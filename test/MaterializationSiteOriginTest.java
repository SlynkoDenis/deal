package deal.semantic;

import deal.ast.Block;
import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.VariableDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.test.SemanticDifferentialHarness;
import deal.types.Type;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0681: the materialization-site origin and the function-row
 * projection on the shared route (design source
 * {@code function-typed-value-materialization-and-dispatch} M8 items 1-5;
 * {@code semantic-ir-construct-coverage-cutover} K11; the corpus pins
 * {@code type-system/dynamic-nonfunction-to-function-e8001} — E8001 with
 * {@code expected = function} at line 8 column 10 — and
 * {@code descriptors/canonical-sig-mismatch-e8010} — E8010 with the two
 * signature texts at line 12 column 10; the task's origin drives).
 *
 * <ol>
 *   <li><b>The declared-annotation origin (both declaration arms).</b>
 *       The annotated-declaration {@code VARIABLE_DECLARATION} boundary
 *       op of the direct arm and of the adapted arm carries the declared
 *       type annotation's own span as its origin (never the declaration's
 *       {@code let} span) and keeps the descriptor-kind policy.</li>
 *   <li><b>The function row on the materialization site.</b> The
 *       function-typed declaration crossing with a non-function value
 *       fails with the pinned function row — E8001, {@code expected
 *       function}, actual the shared actual-kind classification — at the
 *       annotation span in the oracle and on both production artifacts,
 *       with exactly one boundary FAILURE terminal per consumer (the
 *       three-consumer differential verdict passes).</li>
 *   <li><b>The deferred descriptor-kind row.</b> A non-function-typed
 *       declared crossing over a dynamically typed read whose contextual
 *       check defers (a composite read) fails with the descriptor-kind
 *       row at the annotation span; the contextual read child keeps its
 *       own span, is not the failing op, and every consumer emits exactly
 *       one boundary FAILURE terminal at the boundary's own origin.</li>
 *   <li><b>The signature mismatch stays pinned.</b> A differing carried
 *       signature keeps the pinned E8010 with the two canonical signature
 *       texts on the materialization site's own origin.</li>
 *   <li><b>A free boundary outside the declaration arms.</b> A doctored
 *       free boundary of a non-declaration kind (a member of the
 *       validator's free-boundary kind set) carries its own origin and
 *       its single boundary FAILURE terminal in the oracle and both
 *       artifacts — the free-boundary arm is kind-agnostic.</li>
 * </ol>
 *
 * <p>The function-typed declaration crossings are driven with their
 * registration supplied at the unit level (the drive registers the
 * materialized value's allocation identity with the runtime carrier's
 * own binding), because the closed {@code DynamicFunctionValue} producer
 * rule of ISSUE-0622 has not landed in this slice; the end-to-end
 * fixture drive belongs to the joint fixture battery. Nothing else of
 * the one lowering's output is changed.</p>
 */
public class MaterializationSiteOriginTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual), message + " (expected "
            + expected + ", got " + actual + ")");
    }

    private static final ModuleId MODULE = new ModuleId("app");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    // =========================================================================
    // Fixtures
    // =========================================================================

    /**
     * The function-typed declaration crossing with a non-function value —
     * the shape of the corpus fixture
     * {@code type-system/dynamic-nonfunction-to-function-e8001} (the
     * annotation {@code (x: int) => int} starts at column 10 of line 3).
     */
    private static final String FUNCTION_ROW_SOURCE = """
        function boom(): null {
          let t: table = { f: 1 };
          let f: (x: int) => int = t.f;
          return null;
        }

        export function main(): null {
          return boom();
        }
        """;

    /**
     * The non-function-typed declared crossing over a dynamically typed
     * read whose contextual check defers to the declaration crossing (the
     * array-descriptor composite read).
     */
    private static final String DEFERRED_ROW_SOURCE = """
        function boom(): null {
          let t: table = { arr: "x" };
          let a: int[] = t.arr;
          return null;
        }

        export function main(): null {
          return boom();
        }
        """;

    /**
     * The differing carried signature — the shape of the corpus fixture
     * {@code descriptors/canonical-sig-mismatch-e8010} (the annotation
     * starts at column 10 of line 7).
     */
    private static final String SIGNATURE_MISMATCH_SOURCE = """
        function asString(x: int): string {
          return "s";
        }

        function boom(): null {
          let holder: table = { f: asString };
          let f: (x: int) => int = holder.f;
          return null;
        }

        export function main(): null {
          return boom();
        }
        """;

    /** The adapted declaration arm: an arity extension into the annotation. */
    private static final String ADAPTED_ARM_SOURCE = """
        function inc(x: int): int {
          return x + 1;
        }

        function boom(): null {
          let adapted: (a: int, b: int) => int = inc;
          return null;
        }

        export function main(): null {
          return boom();
        }
        """;

    // =========================================================================
    // The checked-project and lowering helpers
    // =========================================================================

    private record CheckedSlice(ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private record Fixture(CheckedProjectInput input, ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           CheckedModuleInput module) {
    }

    private record RawLowering(LoweredModuleUnit unit, StructuredBodyTable table,
                               SemanticLowerer.ModuleLowerer lowerer) {
    }

    /** One drive: the unit, its membership table, and the validated project. */
    private record Drive(LoweredModuleUnit unit, StructuredBodyTable table,
                         ExecutableLoweredProject project) {
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath,
                    String importingModule, Set<String> modulesInProgress)
                    throws ModuleResolver.ModuleNotFoundException {
                Map<String, Map<String, Type>> exports =
                    deal.module.StdlibModuleResolver.stdlibExports(
                        Path.of("std").toAbsolutePath().toString());
                Map<String, Type> moduleExports = exports.get(modulePath);
                if (moduleExports == null) {
                    throw new ModuleResolver.ModuleNotFoundException(
                        "Module not found: " + modulePath);
                }
                return moduleExports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className,
                    String modulePath, String importingModule) {
                return null;
            }
        };
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": checks cleanly: "
            + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    private static List<ExportInterface> exportsOf(ProgramNode program) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ExportDeclaration export
                    && export.declaration() instanceof FunctionDeclaration function) {
                exports.add(new ExportInterface(function.name(), "function"));
            }
        }
        return exports;
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static Fixture fixture(String source, String what) {
        CheckedSlice slice = checkSlice(source, what);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput module = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of("test.deal"), slice.program(), slice.checks(),
            List.<ResolvedImport>of(), exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        List<ModuleFact> facts = List.of(new ModuleFact(SOURCE_ID, MODULE, false, false,
            slice.program(), Map.of(), slice.symbols(), slice.checks(), List.of()));
        CompilerInvocation invocation = invocation();
        CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation, MODULE,
            facts);
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            what + ": the checked project builds: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifestResult = LoweringSupport.computeManifests(
            invocation, built.input(), built.index());
        check(manifestResult != null && manifestResult.diagnostics().isEmpty(),
            what + ": the requirement manifests compute: "
                + (manifestResult == null ? "null" : manifestResult.diagnostics()));
        if (manifestResult == null || !manifestResult.diagnostics().isEmpty()) {
            return null;
        }
        return new Fixture(built.input(), built.index(), manifestResult.manifests(),
            module);
    }

    /** The direct per-module project walk (the produced, pre-gate unit). */
    private static RawLowering rawLower(Fixture fixture, String what) {
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
        ExternalModuleInterface ownInterface = fixture.index().modules().get(MODULE);
        SemanticLowerer.ModuleLowerer lowerer = new SemanticLowerer.ModuleLowerer(
            MODULE, SOURCE_ID, fixture.module().checks(), allocator,
            true, true, true, false, false, false, fixture.module().ast().span(),
            true, true, ownInterface, Map.of());
        lowerer.setModuleImports(fixture.module().imports());
        lowerer.setRegistrationSeeds(ClassRegistrationSeeds.builtinErrorOnly());
        lowerer.setDeclaredConversionIntrinsics(
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT));
        lowerer.setE7Facts(fixture.module().exports(), Map.of(), Map.of(), Set.of());
        try {
            lowerer.lowerProjectModule(fixture.module().ast().statements());
        } catch (RuntimeException defect) {
            check(false, what + ": the walk produces the unit: " + defect);
            return null;
        }
        LoweredModuleUnit unit = lowerer.buildUnit(
            fixture.manifests().get(0).constructCoverage(),
            fixture.module().imports().stream().map(ResolvedImport::resolvedModuleId)
                .toList(),
            fixture.index().interfaceIndexDigest(), REGISTRY_HASH,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        return new RawLowering(unit, lowerer.bodyTable(), lowerer);
    }

    private static ExecutableLoweredProject projectOf(LoweredModuleUnit unit) {
        return new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32,
            new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(MODULE, new ExternalModuleInterface(MODULE,
                    ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
                    InitializationMode.ONCE_AFTER_DEPENDENCIES))),
            Map.of(MODULE, unit), MODULE);
    }

    /** The unit with one extra function-execution binding (the doctor). */
    private static LoweredModuleUnit withRegistration(LoweredModuleUnit unit,
            ValueId identity, FunctionExecutionBinding binding) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> merged =
            new LinkedHashMap<>(unit.functionBindings());
        merged.put(new FunctionAllocationIdentity(identity.id()), binding);
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), merged, unit.ops());
    }

    /**
     * The {@code VARIABLE_DECLARATION} boundary op at the given declared
     * annotation coordinates (the annotation span is unique in the
     * fixture's program).
     */
    private static SemanticOp declarationBoundary(LoweredModuleUnit unit,
            SourceSpan annotation) {
        SemanticOp found = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) op.payload()).kind()
                        == BoundaryKind.VARIABLE_DECLARATION
                    && op.origin().span() != null
                    && op.origin().span().startLine() == annotation.startLine()
                    && op.origin().span().startColumn() == annotation.startColumn()) {
                check(found == null, "exactly one declaration boundary sits at the "
                    + "annotation coordinates (found a second: " + op.opId() + ")");
                found = op;
            }
        }
        check(found != null, "the unit carries the VARIABLE_DECLARATION boundary "
            + "at the annotation coordinates " + annotation.startLine() + ":"
            + annotation.startColumn());
        return found;
    }

    /** The origin text of one op ({@code source:line:column}). */
    private static String originText(SemanticOp op) {
        SourceSpan span = op.origin().span();
        if (span == null) {
            return "-";
        }
        return op.origin().sourceId() + ":" + span.startLine() + ":"
            + span.startColumn();
    }

    /**
     * The declared type annotation's span of the named {@code let}
     * declaration inside the named function body (read from the checked
     * AST — the corpus pin's coordinate, never the lowering's output).
     */
    private static SourceSpan annotationSpan(ProgramNode program, String functionName,
                                             String bindingName) {
        for (StatementNode statement : program.statements()) {
            if (!(statement instanceof FunctionDeclaration function)
                    || !function.name().equals(functionName)) {
                continue;
            }
            for (StatementNode body : function.body().statements()) {
                if (body instanceof VariableDeclaration decl
                        && decl.name().equals(bindingName)
                        && decl.typeAnnotation().isPresent()) {
                    return toSourceSpan(decl.typeAnnotation().get().span());
                }
                if (body instanceof Block block) {
                    for (StatementNode nested : block.statements()) {
                        if (nested instanceof VariableDeclaration decl
                                && decl.name().equals(bindingName)
                                && decl.typeAnnotation().isPresent()) {
                            return toSourceSpan(decl.typeAnnotation().get().span());
                        }
                    }
                }
            }
        }
        check(false, "the checked AST carries the annotated declaration '"
            + bindingName + "' of '" + functionName + "'");
        return null;
    }

    /** One AST span as the IR span (the copied source coordinates). */
    private static SourceSpan toSourceSpan(Span span) {
        return new SourceSpan(span.file(), span.startLine(), span.startColumn(),
            span.endLine(), span.endColumn(), span.startScalarOffset(),
            span.endScalarOffset());
    }

    // =========================================================================
    // The trace-mode and production-artifact runners
    // =========================================================================

    /** One artifact run: the exit code plus the raw trace-protocol lines. */
    private record ArtifactRun(int exitCode, List<String> stdout,
                               List<String> protocol) {
    }

    private static ArtifactRun runLuaTrace(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            Path workspace) throws Exception {
        Files.createDirectories(workspace);
        Path script = workspace.resolve("project.lua");
        Files.writeString(script,
            LuaSemanticEmitter.emitProject(project, Map.of(MODULE, table),
                Map.of(MODULE, registry)),
            StandardCharsets.UTF_8);
        Path stdout = workspace.resolve("lua-out.txt");
        Path stderr = workspace.resolve("lua-err.txt");
        ProcessBuilder builder = new ProcessBuilder("luajit",
            script.toAbsolutePath().toString());
        builder.redirectOutput(stdout.toFile());
        builder.redirectError(stderr.toFile());
        Process process = builder.start();
        int exit = process.waitFor();
        return new ArtifactRun(exit, Files.readAllLines(stdout, StandardCharsets.UTF_8),
            Files.readAllLines(stderr, StandardCharsets.UTF_8));
    }

    /** The absolute classpath of this test process (the artifact compiles resolve it). */
    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static ArtifactRun runJvmTrace(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            Path workspace) throws Exception {
        Files.createDirectories(workspace);
        JvmSemanticEmitter.EmissionResult emission =
            JvmSemanticEmitter.emitProject(project, Map.of(MODULE, table),
                Map.of(MODULE, registry));
        Path source = workspace.resolve(emission.className() + ".java");
        Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
        Path classes = workspace.resolve("classes");
        Files.createDirectories(classes);
        String classpath = absoluteClasspath();
        ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
            "-proc:none", "-cp", classpath, "-d", classes.toString(),
            source.toAbsolutePath().toString());
        javac.redirectErrorStream(true);
        Process compile = javac.start();
        String compileOut = new String(compile.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int compileExit = compile.waitFor();
        if (compileExit != 0) {
            check(false, "the JVM trace artifact compiles: " + compileOut);
            return new ArtifactRun(compileExit, List.of(), List.of());
        }
        Path stdout = workspace.resolve("jvm-out.txt");
        Path stderr = workspace.resolve("jvm-err.txt");
        ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
            classpath + File.pathSeparator + classes, emission.className());
        javaRun.redirectOutput(stdout.toFile());
        javaRun.redirectError(stderr.toFile());
        Process run = javaRun.start();
        int exit = run.waitFor();
        return new ArtifactRun(exit, Files.readAllLines(stdout, StandardCharsets.UTF_8),
            Files.readAllLines(stderr, StandardCharsets.UTF_8));
    }

    /**
     * One trace-protocol line's phase of the given op key, or {@code null}
     * when the op has no such line: the line carries the op key and the
     * phase as its own fields.
     */
    private static List<String> linesOf(List<String> protocol, String opKey,
                                        String phase) {
        List<String> found = new ArrayList<>();
        for (String line : protocol) {
            if (line.contains("|" + opKey + "|" + phase + "|")) {
                found.add(line);
            }
        }
        return found;
    }

    private static void deployRuntime(Path workspace) throws Exception {
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(Path.of("deal", "runtime.lua"), runtimeTarget);
        Path stdTarget = workspace.resolve("std");
        Files.createDirectories(stdTarget);
        try (var listing = Files.list(Path.of("std"))) {
            for (Path file : listing.sorted().toList()) {
                if (file.getFileName().toString().endsWith(".lua")) {
                    Files.copy(file, stdTarget.resolve(file.getFileName()));
                }
            }
        }
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(java.util.Comparator.reverseOrder()).forEach(entry -> {
                        try {
                            Files.deleteIfExists(entry);
                        } catch (java.io.IOException ignored) {
                            // best effort
                        }
                    });
                }
            }
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    /** The LuaJIT production artifact's failure framing under real luajit. */
    private static String luaProductionFailure(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            String what) throws Exception {
        Path workspace = Files.createTempDirectory("origin-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, Map.of(MODULE, table), Map.of(MODULE, registry),
                new HostDeclarationSurface(Map.of())), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                local chunk = dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                      .. tostring(err.o) .. "|" .. tostring(err.e) .. "|"
                      .. tostring(err.a))
                  else
                    print("ERR:" .. tostring(err))
                  end
                  os.exit(0)
                end
                print("OK")
                """.formatted(artifact.toAbsolutePath().toString()),
                StandardCharsets.UTF_8);
            ProcessBuilder builder = new ProcessBuilder("luajit",
                probe.toAbsolutePath().toString());
            builder.directory(workspace.toFile());
            builder.environment().put("DEAL_DEFER_MAIN", "1");
            Path stderrFile = Files.createTempFile(workspace, "stderr", ".txt");
            builder.redirectError(stderrFile.toFile());
            Process process = builder.start();
            String stdout = new String(process.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int exit = process.waitFor();
            String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
            checkEq(0, exit, what + " (luajit): the production chunk executes: "
                + stdout + stderr);
            return stdout.strip();
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM production artifact's failure framing under javac/java. */
    private static String jvmProductionFailure(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            String what) throws Exception {
        Path workspace = Files.createTempDirectory("origin-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project,
                    Map.of(MODULE, table), Map.of(MODULE, registry), className,
                    new HostDeclarationSurface(Map.of()));
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("OriginProbe.java"), """
                final class OriginProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin + "|" + error.expected + "|" + error.actual);
                      return;
                    }
                    System.out.println("OK");
                  }
                }
                """.formatted(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "OriginProbe.java");
            javac.directory(workspace.toFile());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            checkEq(0, compileExit, what + ": the JVM production artifact compiles: "
                + compileOut);
            if (compileExit != 0) {
                return "";
            }
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + File.pathSeparator + classes, "OriginProbe");
            javaRun.directory(workspace.toFile());
            javaRun.redirectErrorStream(false);
            Process run = javaRun.start();
            String stdout = new String(run.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int exit = run.waitFor();
            checkEq(0, exit, what + " (java): the production artifact executes: "
                + stdout);
            return stdout.strip();
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 1. The declared-annotation origin (both declaration arms)
    // =========================================================================

    private static void testDeclarationArmOrigins() {
        System.out.println("-- the declared-annotation origin: the "
            + "VARIABLE_DECLARATION boundary of the direct and the adapted arm "
            + "carries the annotation's own span --");

        // The direct arm.
        Fixture direct = fixture(FUNCTION_ROW_SOURCE, "direct arm origin");
        if (direct == null) {
            return;
        }
        RawLowering directRaw = rawLower(direct, "direct arm origin");
        if (directRaw == null) {
            return;
        }
        SourceSpan directAnnotation = annotationSpan(direct.module().ast(), "boom", "f");
        if (directAnnotation == null) {
            return;
        }
        SemanticOp directBoundary = declarationBoundary(directRaw.unit(), directAnnotation);
        if (directBoundary == null) {
            return;
        }
        check(originText(directBoundary).equals(SOURCE_ID + ":"
                + directAnnotation.startLine() + ":" + directAnnotation.startColumn()),
            "the direct arm's declaration boundary carries the declared type "
                + "annotation's span as its origin: " + originText(directBoundary)
                + " vs annotation " + directAnnotation);
        check(!originText(directBoundary).equals(SOURCE_ID + ":3:3"),
            "the direct arm's boundary origin is not the declaration's let span");
        check(((KindPayload.BoundaryPayload) directBoundary.payload()).descriptor()
                instanceof RuntimeDescriptor.Func
                && directBoundary.failurePolicy() == FailurePolicyId.FUNCTION_SIGNATURE,
            "the function-typed declaration boundary keeps the descriptor-kind "
                + "policy FUNCTION_SIGNATURE: " + directBoundary.failurePolicy());

        // The adapted arm (a FUNCTION_ADAPT value into the annotated target).
        Fixture adapted = fixture(ADAPTED_ARM_SOURCE, "adapted arm origin");
        if (adapted == null) {
            return;
        }
        RawLowering adaptedRaw = rawLower(adapted, "adapted arm origin");
        if (adaptedRaw == null) {
            return;
        }
        boolean adapt = false;
        for (SemanticOp op : adaptedRaw.unit().ops()) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adapt = true;
            }
        }
        check(adapt, "the adapted declaration arm produces its FUNCTION_ADAPT op");
        SourceSpan adaptedAnnotation = annotationSpan(adapted.module().ast(), "boom",
            "adapted");
        if (adaptedAnnotation == null) {
            return;
        }
        SemanticOp adaptedBoundary = declarationBoundary(adaptedRaw.unit(),
            adaptedAnnotation);
        if (adaptedBoundary == null) {
            return;
        }
        check(originText(adaptedBoundary).equals(SOURCE_ID + ":"
                + adaptedAnnotation.startLine() + ":" + adaptedAnnotation.startColumn()),
            "the adapted arm's declaration boundary carries the declared type "
                + "annotation's span as its origin: " + originText(adaptedBoundary)
                + " vs annotation " + adaptedAnnotation);
        check(!originText(adaptedBoundary).equals(SOURCE_ID + ":3:3"),
            "the adapted arm's boundary origin is not the declaration's let span");
        check(adaptedBoundary.failurePolicy() == FailurePolicyId.FUNCTION_SIGNATURE,
            "the adapted arm's boundary keeps the descriptor-kind policy "
                + "FUNCTION_SIGNATURE: " + adaptedBoundary.failurePolicy());
    }

    // =========================================================================
    // 2. The function row on the materialization site (the fixture's shape)
    // =========================================================================

    private static void testFunctionRowDrive() throws Exception {
        System.out.println("-- the function row: the function-typed declaration "
            + "crossing with a non-function value fails E8001 expected function at "
            + "the annotation span in all three consumers --");
        Fixture fixture = fixture(FUNCTION_ROW_SOURCE, "function row");
        if (fixture == null) {
            return;
        }
        SourceSpan annotation = annotationSpan(fixture.module().ast(), "boom", "f");
        if (annotation == null) {
            return;
        }
        String expectedOrigin = SOURCE_ID + ":" + annotation.startLine() + ":"
            + annotation.startColumn();
        RawLowering raw = rawLower(fixture, "function row");
        if (raw == null) {
            return;
        }
        SemanticOp boundary = declarationBoundary(raw.unit(), annotation);
        if (boundary == null) {
            return;
        }
        check(expectedOrigin.equals(originText(boundary)),
            "the crossing's boundary origin is the annotation span: "
                + originText(boundary));
        ValueId materialized = ((KindPayload.BoundaryPayload) boundary.payload())
            .input();
        // The registration supplied at the unit level: the materialized
        // value's allocation identity registered with the runtime carrier's
        // own binding (the producer rule's dynamic record of ISSUE-0675 is
        // replaced by the carrier's class; only the declaration crossing's
        // projection is under test here).
        FunctionExecutionBinding carrier = null;
        for (FunctionExecutionBinding binding : raw.unit().functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.LoweredBody) {
                carrier = binding;
                break;
            }
        }
        check(carrier != null, "the unit carries a runtime carrier binding: " + carrier);
        if (carrier == null) {
            return;
        }
        LoweredModuleUnit doctored = withRegistration(raw.unit(), materialized, carrier);
        ExecutableLoweredProject project = projectOf(doctored);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), "the closed gate accepts the drive project: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return;
        }
        Path workspace = Files.createTempDirectory("function-row-diff");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project,
                    Map.of(MODULE, raw.table()),
                    Map.of(MODULE, new ClassFactoryRegistry(Map.of())),
                    SemanticDifferentialHarness.Expectation.failure("function row",
                        List.of(), "E8001", expectedOrigin), workspace);
            checkEq(3, verdict.runs().size(), "the function-row drive produced the "
                + "three consumers: " + verdict.failures());
            check(verdict.pass(), "the function-row drive's differential verdict "
                + "passes (E8001 at the annotation span, the three traces "
                + "event-for-event): " + verdict.failures());
            for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                int boundaryFailures = 0;
                String failureText = null;
                for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                    if (event.op().equals(boundary.opId())
                            && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                        boundaryFailures++;
                        failureText = event.text();
                    }
                }
                checkEq(1, boundaryFailures, run.consumer() + ": the declaration "
                    + "boundary emits exactly one FAILURE terminal");
                check(failureText != null && failureText.contains(expectedOrigin)
                        && failureText.contains("expected function, got int")
                        && failureText.contains(";function;int;"),
                    run.consumer() + ": the failure carries the pinned function row "
                        + "(E8001, expected function, actual int) at the annotation "
                        + "span: " + failureText);
                check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                        failure && "E8001".equals(failure.error().code())
                        && expectedOrigin.equals(failure.error().origin())
                        && "function".equals(failure.error().expected())
                        && "int".equals(failure.error().actual()),
                    run.consumer() + ": the terminal is E8001 with expected function "
                        + "and actual int at the annotation span: " + run.terminal());
            }
        } finally {
            deleteRecursively(workspace);
        }
        // The production artifacts under the real toolchains.
        String lua = luaProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "function row");
        checkEq("ERR:E8001|expected function, got int|" + expectedOrigin
                + "|function|int", lua,
            "the LuaJIT production artifact pins the function row at the "
                + "annotation span");
        String jvm = jvmProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "function row");
        checkEq("ERR:E8001|expected function, got int|" + expectedOrigin
                + "|function|int", jvm,
            "the JVM production artifact pins the function row at the "
                + "annotation span");
    }

    // =========================================================================
    // 3. The deferred descriptor-kind row
    // =========================================================================

    private static void testDeferredRowDrive() throws Exception {
        System.out.println("-- the deferred descriptor-kind row: a non-function "
            + "declared crossing over a composite read fails at the annotation "
            + "span; the read child keeps its own span and is not the failing op --");
        Fixture fixture = fixture(DEFERRED_ROW_SOURCE, "deferred row");
        if (fixture == null) {
            return;
        }
        SourceSpan annotation = annotationSpan(fixture.module().ast(), "boom", "a");
        if (annotation == null) {
            return;
        }
        String expectedOrigin = SOURCE_ID + ":" + annotation.startLine() + ":"
            + annotation.startColumn();
        RawLowering raw = rawLower(fixture, "deferred row");
        if (raw == null) {
            return;
        }
        SemanticOp boundary = declarationBoundary(raw.unit(), annotation);
        if (boundary == null) {
            return;
        }
        check(expectedOrigin.equals(originText(boundary)),
            "the declaration boundary's origin is the annotation span: "
                + originText(boundary));
        // The contextual read child: its own span, the read's own op.
        SemanticOp readChild = null;
        for (SemanticOp op : raw.unit().ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) op.payload()).kind()
                        == BoundaryKind.CONTEXTUAL_TABLE_READ) {
                readChild = op;
            }
        }
        check(readChild != null, "the composite read carries its contextual "
            + "table-read child");
        if (readChild == null) {
            return;
        }
        check(!originText(readChild).equals(expectedOrigin)
                && originText(readChild).equals(SOURCE_ID + ":3:18"),
            "the contextual read child keeps its own span (the read expression): "
                + originText(readChild));
        ExecutableLoweredProject project = projectOf(raw.unit());
        String readKey = MODULE.path() + "#" + readChild.opId().id();
        String boundaryKey = MODULE.path() + "#" + boundary.opId().id();

        // The oracle.
        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
            project, Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        assertBoundaryTerminal("semantic-oracle", oracle, boundary.opId(), readChild.opId(),
            expectedOrigin, "E8001");
        check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                failure && "[int]".equals(failure.error().expected())
                && "string".equals(failure.error().actual()),
            "the oracle's descriptor-kind row carries the descriptor text and the "
                + "shared actual-kind classification: " + oracle.terminal());

        // The trace-mode artifacts (the per-consumer terminal/origin comparison;
        // the composite read's pass-through atom text differs on the shared JVM
        // runtime, so the drives compare each consumer's own events).
        Path luaWorkspace = Files.createTempDirectory("deferred-row-lua");
        Path jvmWorkspace = Files.createTempDirectory("deferred-row-jvm");
        try {
            ArtifactRun lua = runLuaTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), luaWorkspace);
            checkEq(0, lua.exitCode(), "the shared LuaJIT trace artifact executes: "
                + lua.protocol());
            assertTraceBoundary("shared-luajit", lua.protocol(), boundaryKey, readKey,
                expectedOrigin);
            ArtifactRun jvm = runJvmTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), jvmWorkspace);
            checkEq(0, jvm.exitCode(), "the shared JVM trace artifact executes: "
                + jvm.protocol());
            assertTraceBoundary("shared-jvm", jvm.protocol(), boundaryKey, readKey,
                expectedOrigin);
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
        }

        // The production artifacts under the real toolchains: the boundary's own
        // origin and the descriptor-kind row.
        String lua = luaProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "deferred row");
        check(lua.equals("ERR:E8001|expected array, got string|" + expectedOrigin
                + "|array|string"),
            "the LuaJIT production artifact fails at the annotation span with the "
                + "descriptor-kind row: " + lua);
        String jvm = jvmProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "deferred row");
        check(jvm.equals("ERR:E8001|expected array, got string|" + expectedOrigin
                + "|array|string"),
            "the JVM production artifact fails at the annotation span with the "
                + "descriptor-kind row: " + jvm);
    }

    /** The oracle: one boundary FAILURE at the boundary's own origin; the read child passes. */
    private static void assertBoundaryTerminal(String consumer,
            SemanticRuntimeModel.ConsumerRun run, OpId boundary, OpId readChild,
            String expectedOrigin, String code) {
        int boundaryFailures = 0;
        int readFailures = 0;
        int readSuccesses = 0;
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(boundary)
                    && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                boundaryFailures++;
                check(event.error() != null && code.equals(event.error().code())
                        && expectedOrigin.equals(event.error().origin()),
                    consumer + ": the boundary FAILURE terminal carries " + code
                        + " at its own origin: " + event.text());
            }
            if (event.op().equals(readChild)) {
                if (event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                    readFailures++;
                }
                if (event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                    readSuccesses++;
                }
            }
        }
        checkEq(1, boundaryFailures, consumer + ": exactly one boundary FAILURE "
            + "terminal");
        checkEq(0, readFailures, consumer + ": the contextual read child never fails");
        checkEq(1, readSuccesses, consumer + ": the contextual read child passes");
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                && code.equals(failure.error().code())
                && expectedOrigin.equals(failure.error().origin()),
            consumer + ": the terminal is " + code + " at the boundary's own origin: "
                + run.terminal());
    }

    /** The artifacts: one boundary FAILURE line at the origin; the read child passes. */
    private static void assertTraceBoundary(String consumer, List<String> protocol,
            String boundaryKey, String readKey, String expectedOrigin) {
        List<String> failures = linesOf(protocol, boundaryKey, "FAILURE");
        checkEq(1, failures.size(), consumer + ": exactly one boundary FAILURE "
            + "terminal: " + failures);
        check(!failures.isEmpty() && failures.get(0).contains(expectedOrigin),
            consumer + ": the boundary FAILURE terminal carries the boundary's own "
                + "origin: " + failures);
        checkEq(1, linesOf(protocol, boundaryKey, "START").size(),
            consumer + ": exactly one boundary START");
        checkEq(0, linesOf(protocol, readKey, "FAILURE").size(),
            consumer + ": the contextual read child never fails");
        checkEq(1, linesOf(protocol, readKey, "SUCCESS").size(),
            consumer + ": the contextual read child passes");
    }

    // =========================================================================
    // 4. The differing carried signature stays pinned
    // =========================================================================

    private static void testSignatureMismatchDrive() throws Exception {
        System.out.println("-- the signature mismatch: a differing carried signature "
            + "keeps the pinned E8010 with the two signature texts at the "
            + "annotation span --");
        Fixture fixture = fixture(SIGNATURE_MISMATCH_SOURCE, "signature mismatch");
        if (fixture == null) {
            return;
        }
        SourceSpan annotation = annotationSpan(fixture.module().ast(), "boom", "f");
        if (annotation == null) {
            return;
        }
        String expectedOrigin = SOURCE_ID + ":" + annotation.startLine() + ":"
            + annotation.startColumn();
        RawLowering raw = rawLower(fixture, "signature mismatch");
        if (raw == null) {
            return;
        }
        SemanticOp boundary = declarationBoundary(raw.unit(), annotation);
        if (boundary == null) {
            return;
        }
        check(expectedOrigin.equals(originText(boundary)),
            "the signature-mismatch crossing's origin is the annotation span: "
                + originText(boundary));
        ValueId materialized = ((KindPayload.BoundaryPayload) boundary.payload())
            .input();
        // The runtime carrier of `holder.f` is the `asString` closure; the
        // registration supplied at the unit level is that closure's own
        // LoweredBody (the producer rule's dynamic record is replaced by the
        // stored DEAL body's own class).
        FunctionExecutionBinding carrier = null;
        for (FunctionExecutionBinding binding : raw.unit().functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.LoweredBody body) {
                var function = raw.unit().functions().get(body.functionId());
                if (function != null && "(int)->string"
                        .equals(function.descriptor().canonicalSpecText())) {
                    carrier = binding;
                    break;
                }
            }
        }
        check(carrier != null, "the stored closure's own LoweredBody binding "
            + "resolves: " + carrier);
        if (carrier == null) {
            return;
        }
        LoweredModuleUnit doctored = withRegistration(raw.unit(), materialized, carrier);
        ExecutableLoweredProject project = projectOf(doctored);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), "the closed gate accepts the signature-mismatch drive: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return;
        }
        // The oracle: the pinned E8010 with the two canonical signature texts.
        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
            project, Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                failure && "E8010".equals(failure.error().code())
                && expectedOrigin.equals(failure.error().origin())
                && "function signature mismatch: expected (int)->int, got (int)->string"
                    .equals(failure.error().message())
                && "(int)->int".equals(failure.error().expected())
                && "(int)->string".equals(failure.error().actual()),
            "the oracle keeps the pinned E8010 with the two canonical signature "
                + "texts at the annotation span: " + oracle.terminal());
        int boundaryFailures = 0;
        for (SemanticRuntimeModel.TraceEvent event : oracle.trace()) {
            if (event.op().equals(boundary.opId())
                    && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                boundaryFailures++;
            }
        }
        checkEq(1, boundaryFailures, "the oracle's declaration boundary emits exactly "
            + "one FAILURE terminal");
        // Both artifacts: the same code at the boundary's own origin with one
        // boundary FAILURE terminal. The oracle's row is the pinned canonical
        // pair; the artifacts' carried-signature text spelling on the emitted
        // carriers (the internal `function(int;int)` form) is the pre-existing
        // function-row surface of the shared runtimes, so this drive pins the
        // row's code/stem/origin per consumer and the oracle's canonical texts.
        String boundaryKey = MODULE.path() + "#" + boundary.opId().id();
        Path luaWorkspace = Files.createTempDirectory("sig-mismatch-lua");
        Path jvmWorkspace = Files.createTempDirectory("sig-mismatch-jvm");
        try {
            ArtifactRun lua = runLuaTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), luaWorkspace);
            checkEq(0, lua.exitCode(), "the shared LuaJIT trace artifact executes: "
                + lua.protocol());
            assertSignatureTrace("shared-luajit", lua.protocol(), boundaryKey,
                expectedOrigin);
            ArtifactRun jvm = runJvmTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), jvmWorkspace);
            checkEq(0, jvm.exitCode(), "the shared JVM trace artifact executes: "
                + jvm.protocol());
            assertSignatureTrace("shared-jvm", jvm.protocol(), boundaryKey,
                expectedOrigin);
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
        }
        String lua = luaProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "signature mismatch");
        check(lua.startsWith("ERR:E8010|function signature mismatch:")
                && lua.contains("|" + expectedOrigin + "|"),
            "the LuaJIT production artifact projects E8010 at the annotation span: "
                + lua);
        String jvm = jvmProductionFailure(project, raw.table(),
            new ClassFactoryRegistry(Map.of()), "signature mismatch");
        check(jvm.startsWith("ERR:E8010|function signature mismatch:")
                && jvm.contains("|" + expectedOrigin + "|"),
            "the JVM production artifact projects E8010 at the annotation span: "
                + jvm);
    }

    /** The artifacts: one E8010 boundary FAILURE line at the boundary's own origin. */
    private static void assertSignatureTrace(String consumer, List<String> protocol,
            String boundaryKey, String expectedOrigin) {
        List<String> failures = linesOf(protocol, boundaryKey, "FAILURE");
        checkEq(1, failures.size(), consumer + ": exactly one boundary FAILURE "
            + "terminal: " + failures);
        check(!failures.isEmpty() && failures.get(0).contains("E8010")
                && failures.get(0).contains(expectedOrigin)
                && failures.get(0).contains(
                    "function signature mismatch: expected")
                && failures.get(0).contains(", got "),
            consumer + ": the boundary FAILURE terminal is the E8010 projection with "
                + "the two carried signature texts at the boundary's own origin: "
                + failures);
        checkEq(1, linesOf(protocol, boundaryKey, "START").size(),
            consumer + ": exactly one boundary START");
    }

    // =========================================================================
    // 5. A free boundary outside the declaration arms
    // =========================================================================

    private static void testFreeBoundaryOutsideDeclarationArms() throws Exception {
        System.out.println("-- a free boundary outside the declaration arms: a "
            + "doctored free boundary of a non-declaration kind carries its own "
            + "origin and its single FAILURE terminal in all three consumers --");
        Fixture fixture = fixture(DEFERRED_ROW_SOURCE, "free boundary");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "free boundary");
        if (raw == null) {
            return;
        }
        SourceSpan annotation = annotationSpan(fixture.module().ast(), "boom", "a");
        if (annotation == null) {
            return;
        }
        SemanticOp declaration = declarationBoundary(raw.unit(), annotation);
        if (declaration == null) {
            return;
        }
        // Doctor the produced free boundary: a non-declaration free kind (the
        // validator's closed free-boundary kind set), the same checked input, a
        // primitive descriptor whose row text all three consumers share, and a
        // synthetic origin of the boundary's own.
        SourceSpan synthetic = toSourceSpan(new Span(SOURCE_ID, 42, 9, 42, 9));
        SourceOrigin freeOrigin = new SourceOrigin(SOURCE_ID, synthetic,
            SourceOriginKind.SYNTHETIC, declaration.origin().anchorId(), null);
        KindPayload.BoundaryPayload original =
            (KindPayload.BoundaryPayload) declaration.payload();
        KindPayload.BoundaryPayload freePayload = new KindPayload.BoundaryPayload(
            BoundaryKind.UNTYPED_CLASS_INPUT, RuntimeDescriptor.Int.INSTANCE,
            original.input(), original.realization());
        OpId freeId = new OpId(MODULE, nextOpIdOf(raw.unit()));
        SemanticOp freeBoundary = new SemanticOp(freeId, SemanticOpKind.BOUNDARY,
            freeOrigin, null, null, List.of(), List.of(), freePayload,
            FailurePolicyId.TYPE_DESCRIPTOR, reContract(declaration, freePayload));
        LoweredModuleUnit doctored = withFreeBoundary(raw.unit(), declaration, freeBoundary);
        StructuredBodyTable table = withFreeBoundaryMember(raw.table(), raw.unit(),
            declaration, freeBoundary);
        ExecutableLoweredProject project = projectOf(doctored);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), "the closed gate accepts the doctored free boundary: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return;
        }
        String expectedOrigin = SOURCE_ID + ":42:9";
        String boundaryKey = MODULE.path() + "#" + freeBoundary.opId().id();

        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
            project, Map.of(MODULE, table),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        int oracleFailures = 0;
        for (SemanticRuntimeModel.TraceEvent event : oracle.trace()) {
            if (event.op().equals(freeBoundary.opId())
                    && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                oracleFailures++;
            }
        }
        checkEq(1, oracleFailures, "the oracle emits exactly one FAILURE terminal "
            + "for the free boundary");
        check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                failure && expectedOrigin.equals(failure.error().origin())
                && "E8001".equals(failure.error().code())
                && "expected int, got string".equals(failure.error().message())
                && "int".equals(failure.error().expected())
                && "string".equals(failure.error().actual()),
            "the oracle projects the free boundary's own origin and its "
                + "descriptor-kind row: " + oracle.terminal());

        Path luaWorkspace = Files.createTempDirectory("free-boundary-lua");
        Path jvmWorkspace = Files.createTempDirectory("free-boundary-jvm");
        try {
            ArtifactRun lua = runLuaTrace(project, table,
                new ClassFactoryRegistry(Map.of()), luaWorkspace);
            checkEq(0, lua.exitCode(), "the shared LuaJIT trace artifact executes: "
                + lua.protocol());
            assertFreeBoundaryTrace("shared-luajit", lua.protocol(), boundaryKey,
                expectedOrigin);
            ArtifactRun jvm = runJvmTrace(project, table,
                new ClassFactoryRegistry(Map.of()), jvmWorkspace);
            checkEq(0, jvm.exitCode(), "the shared JVM trace artifact executes: "
                + jvm.protocol());
            assertFreeBoundaryTrace("shared-jvm", jvm.protocol(), boundaryKey,
                expectedOrigin);
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
        }

        String lua = luaProductionFailure(project, table,
            new ClassFactoryRegistry(Map.of()), "free boundary");
        check(lua.equals("ERR:E8001|expected int, got string|" + expectedOrigin
                + "|int|string"),
            "the LuaJIT production artifact projects the free boundary's own origin "
                + "and its descriptor-kind row: " + lua);
        String jvm = jvmProductionFailure(project, table,
            new ClassFactoryRegistry(Map.of()), "free boundary");
        check(jvm.equals("ERR:E8001|expected int, got string|" + expectedOrigin
                + "|int|string"),
            "the JVM production artifact projects the free boundary's own origin and "
                + "its descriptor-kind row: " + jvm);
    }

    private static void assertFreeBoundaryTrace(String consumer, List<String> protocol,
            String boundaryKey, String expectedOrigin) {
        List<String> failures = linesOf(protocol, boundaryKey, "FAILURE");
        checkEq(1, failures.size(), consumer + ": exactly one free-boundary FAILURE "
            + "terminal: " + failures);
        check(!failures.isEmpty() && failures.get(0).contains(expectedOrigin)
                && failures.get(0).contains("expected int, got string"),
            consumer + ": the free-boundary FAILURE terminal carries the boundary's "
                + "own origin and the descriptor-kind row: " + failures);
        checkEq(1, linesOf(protocol, boundaryKey, "START").size(),
            consumer + ": exactly one free-boundary START");
    }

    /** The next free op id of the unit (the doctor's own id). */
    private static long nextOpIdOf(LoweredModuleUnit unit) {
        long max = 0;
        for (SemanticOp op : unit.ops()) {
            max = Math.max(max, op.opId().id());
        }
        return max + 1;
    }

    /** The unit with the declaration boundary replaced by the free boundary. */
    private static LoweredModuleUnit withFreeBoundary(LoweredModuleUnit unit,
            SemanticOp replaced, SemanticOp freeBoundary) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op.opId().equals(replaced.opId()) ? freeBoundary : op);
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    /**
     * The membership table with the free boundary at the doctored boundary's own
     * position (the input value is complete there and the block's transfer has
     * not yet run; the free boundary is not an owned child of any op, so the
     * block walk executes it exactly like every other member).
     */
    private static StructuredBodyTable withFreeBoundaryMember(StructuredBodyTable table,
            LoweredModuleUnit unit, SemanticOp replaced, SemanticOp freeBoundary) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        boolean placed = false;
        for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
            List<OpId> members = new ArrayList<>();
            for (OpId member : entry.getValue()) {
                if (member.equals(replaced.opId())) {
                    members.add(freeBoundary.opId());
                    placed = true;
                    continue;
                }
                members.add(member);
            }
            blockOps.put(entry.getKey(), members);
        }
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>(table.opBlocks());
        BlockId owner = opBlocks.get(replaced.opId());
        if (owner == null) {
            owner = unit.moduleInit().initBlock();
        }
        opBlocks.remove(replaced.opId());
        opBlocks.put(freeBoundary.opId(), owner);
        if (!placed) {
            blockOps.computeIfAbsent(owner, key -> new ArrayList<>())
                .add(freeBoundary.opId());
        }
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /** One op's contract snapshot over a replaced payload (the digest recomputed). */
    private static OperationContractSnapshot reContract(SemanticOp op,
            KindPayload payload) {
        OperationContractSnapshot original = op.contract();
        OperationContractSnapshot draft = new OperationContractSnapshot(
            original.version(), SemanticOpKind.BOUNDARY, original.resultType(),
            original.operandTypes(), original.selector(), payload,
            FailurePolicyId.TYPE_DESCRIPTOR, original.referencedSemanticIds(),
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(draft);
        return new OperationContractSnapshot(original.version(),
            SemanticOpKind.BOUNDARY, original.resultType(), original.operandTypes(),
            original.selector(), payload, FailurePolicyId.TYPE_DESCRIPTOR,
            original.referencedSemanticIds(), digest);
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        testDeclarationArmOrigins();
        testFunctionRowDrive();
        testDeferredRowDrive();
        testSignatureMismatchDrive();
        testFreeBoundaryOutsideDeclarationArms();
        System.out.println();
        System.out.println("Materialization-site origin and function-row projection: "
            + passed + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
