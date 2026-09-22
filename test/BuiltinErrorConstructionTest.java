package deal.test;

import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0619: the builtin {@code Error} construction, field surface, and
 * canonical err carriers ({@code semantic-ir-construct-coverage-cutover}
 * K13 and the K13 contract).
 *
 * <ol>
 *   <li>the vertical drive: an Error literal with provided fields, a
 *       defaulted Error-typed literal (omitted {@code code}), a field read,
 *       a field write observed through an alias, and a catch-and-rethrow
 *       run through the one project lowering, the composed validation
 *       chain, the semantic oracle, and both shared artifacts under the
 *       real {@code luajit} and {@code javac --release 25 -proc:none} plus
 *       {@code java} toolchains — the three traces compared event-for-event
 *       and the terminal pinned to the rethrown {@code Error} value's own
 *       framing;</li>
 *   <li>the structural facts: the literal lowers
 *       {@code CLASS_NEW(BUILTIN_DEFAULTS)} over the compiler-owned builtin
 *       layout for exactly {@code @/Error}, with the null factory ref, the
 *       empty default-op list, the literal-order provided fields, and
 *       exactly one {@code CLASS_LITERAL_FIELD} boundary per provided
 *       field; every listed field is a declared one;</li>
 *   <li>the canonical carriers: the LuaJIT artifact publishes the
 *       {@code {__d = true, code=..., m=...}} err carrier, the JVM artifact
 *       publishes {@code new JvmRuntime.ErrorValue(...)}, and the unit
 *       crosses the value over an {@code @/Error} return boundary and an
 *       {@code @/Error} parameter boundary;</li>
 *   <li>the real production path: the same fixture compiles through the
 *       release-owned production invocation to exactly one project artifact
 *       per target and both artifacts execute under their real toolchains
 *       with the pinned {@code DEAL_ERROR_CODE: E_INNER} terminal;</li>
 *   <li>the named Error corpus fixtures that carry only this slice's
 *       constructs ({@code error-handling/throw-error},
 *       {@code runtime-errors/rethrow-preserves-code}) compile through the
 *       production pipeline on both targets and their observable outcomes
 *       equal the sidecar pins ({@code runtime-ok} and
 *       {@code runtime-error USER_RETHROW});</li>
 *   <li>the negative seeds: a non-builtin class under
 *       {@code BUILTIN_DEFAULTS} fails the composed gate with
 *       {@code CONSTRUCTION_COHERENCE}, and {@code has(e.code)}/
 *       {@code delete e.code} stay the checker's E4005/E4004
 *       rejections.</li>
 * </ol>
 */
public class BuiltinErrorConstructionTest {

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

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static final ModuleId MAIN = new ModuleId("main");
    private static final String SOURCE_ID = "main.deal";
    private static final Path WORKSPACE = Path.of("build/builtin-error-diff");
    private static final Path FIXTURE_ROOT =
        Path.of("test/conformance/backend-runtime");

    /**
     * The vertical fixture: every construct of this slice in one program.
     * The intermediate observations are encoded as distinct failure codes,
     * so the pinned terminal proves the field reads, the write through the
     * alias, the catch reification, and the {@code @/Error} crossings.
     */
    private static final String ERROR_SOURCE = """
        function produceError(): Error {
          try {
            throw { code: "E_INNER", message: "inner" }
          } catch (caught) {
            return caught
          }
          return { code: "E_UNREACHABLE", message: "unreachable" }
        }

        function rethrowFrom(v: Error): null {
          try {
            throw v
          } catch (caught) {
            throw caught
          }
        }

        export function main(): null {
          let e: Error = { code: "E1", message: "m1" }
          let d: Error = { message: "only" }
          if (d.code !== "") {
            throw { code: "FAIL_DEFAULT_CODE", message: "default code" }
          }
          if (d.message !== "only") {
            throw { code: "FAIL_DEFAULT_MESSAGE", message: "default message" }
          }
          if (e.code !== "E1" || e.message !== "m1") {
            throw { code: "FAIL_PROVIDED_FIELDS", message: "provided fields" }
          }
          let alias: Error = e
          e.code = "E2"
          if (alias.code !== "E2") {
            throw { code: "FAIL_ALIAS_WRITE", message: "alias write" }
          }
          if (e.code !== "E2" || e.message !== "m1") {
            throw { code: "FAIL_FIELD_STATE", message: "field state" }
          }
          let carried: Error = produceError()
          if (carried.code !== "E_INNER" || carried.message !== "inner") {
            throw { code: "FAIL_CARRIED", message: "carried value" }
          }
          rethrowFrom(carried)
          return null
        }
        """;

    // =========================================================================
    // The real project harness (the production frontend + the one lowerer)
    // =========================================================================

    private record RealProject(
        Path root,
        CompilationOrchestrator orchestrator,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface) {
    }

    /** The harness-invocation frontend compile of one single-module project. */
    private static RealProject compileProject(String source) throws Exception {
        Path root = Files.createTempDirectory("builtin-error-");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(SOURCE_ID), source);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(SOURCE_ID).toAbsolutePath(), root.resolve("out"), false,
            false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        check(compiled, "the fixture project compiles through the frontend: "
            + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.hasErrors() || built.input() == null
                || built.index() == null || manifests == null
                || manifests.manifests() == null) {
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build");
        }
        return new RealProject(root, orchestrator, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface());
    }

    /** One {@link SemanticLowerer#lowerProject} call over the real project. */
    private static SemanticLowerer.ProjectLoweringResult lower(RealProject project) {
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        return SemanticLowerer.lowerProject(invocation, project.checkedProject(),
            project.index(), project.manifests(), project.surface(), Map.of(),
            Map.of(),
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception ignored) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit,
                                           SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    // =========================================================================
    // 1. The vertical drive
    // =========================================================================

    static void testVerticalDrive() throws Exception {
        System.out.println("-- the builtin Error vertical drive: literals, field "
            + "reads/writes, the alias write, and the catch rethrow through the "
            + "oracle and both real-toolchain artifacts --");

        RealProject project = compileProject(ERROR_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(!result.hasErrors() && result.project() != null,
                "the fixture lowers and validates through the one project entry: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            boolean deferred = false;
            for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                if (diagnostic.message().contains("RETAINED_ABI_DEFERRED")) {
                    deferred = true;
                }
            }
            check(!deferred, "checker-valid builtin Error input reports zero "
                + "RETAINED_ABI_DEFERRED");
            LoweredModuleUnit unit = result.project().modules().get(MAIN);
            check(unit != null, "the entry unit is in the closure");
            if (unit == null) {
                return;
            }
            checkBuiltinClassNewFacts(unit);
            checkErrorBoundaryCrossings(unit);
            checkCarriers(unit, result.tableOf(MAIN));

            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(result.project(),
                    result.tables(), result.registries(),
                    SemanticDifferentialHarness.Expectation.failure(
                        "the builtin Error vertical drive", List.of(),
                        "E_INNER", null),
                    WORKSPACE);
            check(verdict.pass(), "the three-consumer differential drive passes "
                + "(oracle + shared LuaJIT + shared JVM, event-for-event):\n"
                + verdict.report());
            for (deal.semantic.SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                check(!run.trace().isEmpty(), run.consumer()
                    + " produced real events");
                if (run.terminal()
                        instanceof deal.semantic.SemanticRuntimeModel.Terminal.DealFailure
                            failure) {
                    check("E_INNER".equals(failure.error().code())
                            && "inner".equals(failure.error().message()),
                        run.consumer() + " publishes the rethrown Error value's own "
                            + "framing (code E_INNER, message 'inner'); got "
                            + failure.error().code() + " / "
                            + failure.error().message());
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    /** The literal's pinned CLASS_NEW facts (K13 items 1-4). */
    private static void checkBuiltinClassNewFacts(LoweredModuleUnit unit) {
        List<SemanticOp> classNews = ofKind(unit, SemanticOpKind.CLASS_NEW);
        check(classNews.size() >= 2,
            "the fixture constructs the provided-field and the defaulted Error "
                + "literals; got " + classNews.size());
        int fullyProvided = 0;
        int defaulted = 0;        for (SemanticOp classNew : classNews) {
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) classNew.payload();
            checkEq(ClassId.ERROR, payload.classId(),
                "every Error literal's classId is the builtin @/Error");
            checkEq(DefaultOwner.BUILTIN_DEFAULTS, payload.defaultOwner(),
                "every Error literal's defaultOwner is BUILTIN_DEFAULTS");
            check(payload.classFactoryRef() == null,
                "the builtin Error construction carries the null factory ref");
            check(payload.classDefaultOpIds().isEmpty(),
                "the builtin Error construction carries an empty default-op list");
            checkEq(ClassLayout.BUILTIN_ERROR, payload.layout(),
                "the payload's layout is the compiler-owned builtin Error layout");
            checkEq(List.of("code", "message"), payload.layout().fields().stream()
                    .map(ClassLayout.FieldLayout::name).toList(),
                "the builtin layout declares code and message in that order");
            check(payload.layout().fields().stream().allMatch(field ->
                    field.required()
                        && field.defaultOwner() == DefaultOwner.BUILTIN_DEFAULTS
                        && field.descriptor() == RuntimeDescriptor.String.INSTANCE),
                "both builtin fields are required-present strings under "
                    + "BUILTIN_DEFAULTS");
            List<String> provided = payload.providedFields().stream()
                .map(KindPayload.ProvidedField::name).toList();
            List<String> boundaries = payload.fieldBoundaries().stream()
                .map(KindPayload.FieldBoundary::field).toList();
            checkEq(boundaries, provided,
                "the field boundaries name exactly the provided fields");
            check(payload.fieldBoundaries().stream().allMatch(entry ->
                    entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD),
                "every field boundary is a CLASS_LITERAL_FIELD (the builtin "
                    + "defaults are compiler constants, never CLASS_DEFAULT_FIELD)");
            if (provided.size() == 2) {
                fullyProvided++;
                checkEq(List.of("code", "message"), provided,
                    "the fully provided literal keeps its literal order");
            } else if (provided.size() == 1) {
                defaulted++;
                checkEq("message", provided.get(0),
                    "the defaulted literal provides only message (omitted code "
                        + "takes the compiler constant empty string)");
            }
        }
        check(fullyProvided >= 1,
            "at least one literal provides both fields (got " + fullyProvided + ")");
        checkEq(1, defaulted, "one literal omits code (the constant empty string)");
    }

    /** The @/Error boundary crossings and the throw terminators. */
    private static void checkErrorBoundaryCrossings(LoweredModuleUnit unit) {
        RuntimeDescriptor errorDescriptor =
            new RuntimeDescriptor.Class(ClassId.ERROR);
        int crossings = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.BOUNDARY) {
                continue;
            }
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) op.payload();
            if (!errorDescriptor.equals(payload.descriptor())) {
                continue;
            }
            if (payload.kind() == BoundaryKind.FUNCTION_RETURN
                    || payload.kind() == BoundaryKind.FUNCTION_PARAMETER) {
                crossings++;
            }
        }
        check(crossings >= 2,
            "the unit crosses an Error value over an @/Error return boundary and "
                + "an @/Error parameter boundary; got " + crossings);
        List<SemanticOp> throws_ = ofKind(unit, SemanticOpKind.THROW);
        check(throws_.size() >= 4,
            "the unit carries every throw of the fixture (the literals, the "
                + "rethrow, and the guards); got " + throws_.size());
        for (SemanticOp throwOp : throws_) {
            checkEq(FailurePolicyId.THROW_TRANSFER, throwOp.failurePolicy(),
                "every THROW carries THROW_TRANSFER");
        }
    }

    /** The canonical err carriers of both shared artifacts. */
    private static void checkCarriers(LoweredModuleUnit unit,
                                      StructuredBodyTable table) {
        String lua = LuaSemanticEmitter.emitModule(unit, table);
        check(lua.contains("__instT = {__d = true, code = ")
                && lua.contains(", m = "),
            "the LuaJIT artifact publishes the canonical __d err carrier");
        check(lua.contains("__bcheck(\"@/Error\""),
            "the LuaJIT artifact checks the @/Error boundary atom");
        String jvm = JvmSemanticEmitter.emitModule(unit, table).source();
        check(jvm.contains("new JvmRuntime.ErrorValue("),
            "the JVM artifact publishes the canonical ErrorValue carrier");
        check(jvm.contains("JvmRuntime.bcheck(\"@/Error\""),
            "the JVM artifact checks the @/Error boundary atom");
        // The layout participates in layout resolution only: the builtin
        // class is excluded from the generated class carriers and from the
        // JSON plans of both targets.
        check(!lua.contains("__plans[\"@/Error\"]"),
            "the LuaJIT artifact generates no JSON plan for the builtin Error "
                + "class");
        check(!jvm.contains("JvmJson.Plan(\"@/Error\"")
                && !jvm.contains("ID = \"@/Error\";"),
            "the JVM artifact generates no JSON plan and no class carrier for "
                + "the builtin Error class");
    }

    // =========================================================================
    // 2. The real production path
    // =========================================================================

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private record ProjectOutcome(int exitCode, String output) {
    }

    private static ProjectOutcome runProcess(Path directory, String... command)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(directory.toFile());
        builder.redirectErrorStream(true);
        Process process = builder.start();
        String output = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exitCode = process.waitFor();
        return new ProjectOutcome(exitCode, output);
    }

    /**
     * One project compile through the release-owned production invocation.
     */
    private static CompilationOrchestrator productionCompile(Path root, String source,
            Backend backend, String output) throws Exception {
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(SOURCE_ID), source);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(SOURCE_ID).toAbsolutePath(), root.resolve(output), false,
            false, false, false, backend, null,
            List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null,
            productionInvocation());
        orchestrator.compile();
        return orchestrator;
    }

    static void testProductionArtifacts() throws Exception {
        System.out.println("-- the builtin Error fixture through the release-owned "
            + "production invocation on both targets --");

        String buildCp = Path.of("build").toAbsolutePath().normalize().toString();

        Path luaRoot = Files.createTempDirectory("builtin-error-prod-lua-");
        try {
            CompilationOrchestrator lua =
                productionCompile(luaRoot, ERROR_SOURCE, Backend.LUAJIT, "out");
            check(lua.diagnostics().isEmpty(),
                "the LuaJIT production compile succeeds: " + lua.diagnostics());
            check(lua.semanticEmissionCount() == 1
                    && lua.retainedEmissionCount() == 0,
                "the LuaJIT production arm emits exactly one project artifact: "
                    + "semantic=" + lua.semanticEmissionCount() + " retained="
                    + lua.retainedEmissionCount());
            if (lua.semanticEmissionCount() == 1) {
                String artifact = Files.readString(luaRoot.resolve("out/main.lua"));
                check(artifact.contains("{__d = true, code = "),
                    "the production LuaJIT artifact carries the canonical err "
                        + "carrier");
                ProjectOutcome run = runProcess(luaRoot.resolve("out"),
                    "luajit", "main.lua");
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E_INNER"),
                    "the production LuaJIT artifact publishes the rethrown Error's "
                        + "own code: exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(luaRoot);
        }

        Path jvmRoot = Files.createTempDirectory("builtin-error-prod-jvm-");
        try {
            CompilationOrchestrator jvm =
                productionCompile(jvmRoot, ERROR_SOURCE, Backend.JVM, "out");
            check(jvm.diagnostics().isEmpty(),
                "the JVM production compile succeeds: " + jvm.diagnostics());
            check(jvm.semanticEmissionCount() == 1
                    && jvm.retainedEmissionCount() == 0,
                "the JVM production arm emits exactly one project artifact: "
                    + "semantic=" + jvm.semanticEmissionCount() + " retained="
                    + jvm.retainedEmissionCount());
            if (jvm.semanticEmissionCount() == 1) {
                Path out = jvmRoot.resolve("out");
                String artifact = Files.readString(out.resolve("Main.java"));
                check(artifact.contains("new JvmRuntime.ErrorValue("),
                    "the production JVM artifact carries the canonical ErrorValue "
                        + "carrier");
                ProjectOutcome javac = runProcess(jvmRoot, "javac", "--release",
                    "25", "-proc:none", "-cp", buildCp, "-d", out.toString(),
                    out.resolve("Main.java").toString());
                check(javac.exitCode() == 0,
                    "the production JVM artifact compiles: " + javac.output());
                if (javac.exitCode() == 0) {
                    ProjectOutcome run = runProcess(out, "java", "-cp",
                        buildCp + java.io.File.pathSeparator + out, "Main");
                    check(run.exitCode() == 1
                            && run.output().contains("DEAL_ERROR_CODE: E_INNER"),
                        "the production JVM artifact publishes the rethrown Error's "
                            + "own code: exit=" + run.exitCode() + " output="
                            + run.output().replace("\n", "\\n"));
                }
            }
        } finally {
            deleteRecursively(jvmRoot);
        }
    }

    // =========================================================================
    // 3. The named Error corpus fixtures
    // =========================================================================

    /** Strips the fixture metadata header lines (the harness's own rule). */
    private static String fixtureSource(String relative) throws Exception {
        StringBuilder out = new StringBuilder();
        for (String line : Files.readString(FIXTURE_ROOT.resolve(relative))
                .split("\n", -1)) {
            if (line.trim().startsWith("// @")) {
                continue;
            }
            out.append(line).append('\n');
        }
        return out.toString();
    }

    static void testNamedCorpusFixtures() throws Exception {
        System.out.println("-- the named Error corpus fixtures through the "
            + "production pipeline on both targets --");

        // error-handling/throw-error: the sidecar pins runtime-ok with an
        // empty transcript, so the exported test function must execute
        // cleanly (the catch read the thrown Error's code).
        String throwError = fixtureSource("error-handling/throw-error.deal");
        checkExportedFixture("throw-error.deal", throwError,
            "test_throw", null);

        // runtime-errors/rethrow-preserves-code: the sidecar pins
        // runtime-error USER_RETHROW — the caught Error is rethrown and
        // keeps its explicit code.
        String rethrow = fixtureSource("runtime-errors/rethrow-preserves-code.deal");
        checkExportedFixture("rethrow-preserves-code.deal", rethrow,
            "test_rethrow_preserves_code", "USER_RETHROW");

        // rtc-015-error-default-code and error-roundtrip carry later-slice
        // shapes the shared slice does not admit yet (an exported function
        // called from source spans two invocation shapes; a non-null
        // return type without a trailing return needs the non-null implicit
        // return) — they stay fail-closed until their owning children land.
    }

    /**
     * One named corpus fixture through the production pipeline on both
     * targets: the entry module compiles to one project artifact, and the
     * named exported zero-arity function executes through the artifact's
     * published surface. A {@code null} {@code expectedFailureCode} pins
     * the {@code runtime-ok} sidecar, otherwise the pinned runtime-error
     * code.
     */
    private static void checkExportedFixture(String name, String source,
            String exportName, String expectedFailureCode) throws Exception {
        String buildCp = Path.of("build").toAbsolutePath().normalize().toString();

        Path luaRoot = Files.createTempDirectory("builtin-error-fixture-lua-");
        try {
            CompilationOrchestrator lua =
                productionCompile(luaRoot, source, Backend.LUAJIT, "out");
            check(lua.diagnostics().isEmpty(), name
                + ": the LuaJIT production compile succeeds: "
                + lua.diagnostics());
            if (lua.diagnostics().isEmpty()) {
                Path out = luaRoot.resolve("out");
                Files.writeString(out.resolve("fixture_driver.lua"), """
                    local surfaces = dofile("main.lua")
                    local fn = surfaces["%s"]
                    assert(type(fn) == "table" and fn.__kind == "function",
                      "the entry surface publishes the fixture export")
                    local ok, err = pcall(fn.f)
                    if ok then
                      io.write("FIXTURE_OK")
                    else
                      io.write("FIXTURE_FAIL|" .. tostring(err.code))
                    end
                    """.formatted(exportName));
                ProcessBuilder builder = new ProcessBuilder("luajit",
                    "fixture_driver.lua");
                builder.directory(out.toFile());
                builder.redirectErrorStream(true);
                Process process = builder.start();
                String output = new String(process.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8);
                int exitCode = process.waitFor();
                check(exitCode == 0, name + ": the LuaJIT fixture driver runs: exit="
                    + exitCode + " output=" + output.replace("\n", "\\n"));
                checkFixtureOutcome(name + " (LuaJIT)", output, expectedFailureCode);
            }
        } finally {
            deleteRecursively(luaRoot);
        }

        Path jvmRoot = Files.createTempDirectory("builtin-error-fixture-jvm-");
        try {
            CompilationOrchestrator jvm =
                productionCompile(jvmRoot, source, Backend.JVM, "out");
            check(jvm.diagnostics().isEmpty(), name
                + ": the JVM production compile succeeds: " + jvm.diagnostics());
            if (jvm.diagnostics().isEmpty()) {
                Path out = jvmRoot.resolve("out");
                Files.writeString(out.resolve("FixtureDriver.java"), """
                    public final class FixtureDriver {
                      public static void main(String[] args) {
                        Main.main(new String[0]);
                        deal.codegen.jvm.JvmRuntime.FunctionValue fn =
                            (deal.codegen.jvm.JvmRuntime.FunctionValue) Main
                                .EXPORT_SURFACES.get("main").read("%s");
                        try {
                          fn.fn.invoke(new Object[0]);
                          System.out.print("FIXTURE_OK");
                        } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                          System.out.print("FIXTURE_FAIL|" + error.code);
                        }
                      }
                    }
                    """.formatted(exportName));
                String classpath = buildCp;
                ProjectOutcome javac = runProcess(jvmRoot, "javac", "--release",
                    "25", "-proc:none", "-cp", classpath, "-d", out.toString(),
                    out.resolve("Main.java").toString(),
                    out.resolve("FixtureDriver.java").toString());
                check(javac.exitCode() == 0, name
                    + ": the JVM fixture artifact compiles: " + javac.output());
                if (javac.exitCode() == 0) {
                    ProjectOutcome run = runProcess(out, "java", "-cp",
                        classpath + java.io.File.pathSeparator + out,
                        "FixtureDriver");
                    check(run.exitCode() == 0, name
                        + ": the JVM fixture driver runs: exit=" + run.exitCode()
                        + " output=" + run.output().replace("\n", "\\n"));
                    checkFixtureOutcome(name + " (JVM)", run.output(),
                        expectedFailureCode);
                }
            }
        } finally {
            deleteRecursively(jvmRoot);
        }
    }

    private static void checkFixtureOutcome(String name, String output,
            String expectedFailureCode) {
        if (expectedFailureCode == null) {
            check(output.contains("FIXTURE_OK"), name
                + ": the fixture's exported test function executes cleanly "
                + "(the runtime-ok sidecar); got "
                + output.replace("\n", "\\n"));
        } else {
            check(output.contains("FIXTURE_FAIL|" + expectedFailureCode), name
                + ": the fixture's exported test function fails with the sidecar's "
                + "pinned code " + expectedFailureCode + "; got "
                + output.replace("\n", "\\n"));
        }
    }

    // =========================================================================
    // 4. The negative seeds
    // =========================================================================

    static void testNegativeSeeds() throws Exception {
        System.out.println("-- negative seeds: BUILTIN_DEFAULTS on a non-builtin "
            + "class fails the composed gate; has/delete on an Error field stay "
            + "checker rejections --");

        // (a) A user class forged to the builtin-defaults owner: the
        // composed chain rejects the unit with CONSTRUCTION_COHERENCE
        // naming the owner.
        String source = """
            class Point {
              x: int = 0;
            }

            export function main(): null {
              let p: Point = { x: 1 }
              return null
            }
            """;
        RealProject project = compileProject(source);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(!result.hasErrors() && result.project() != null,
                "the user-class fixture lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = result.project().modules().get(MAIN);
            SemanticOp classNew = ofKind(unit, SemanticOpKind.CLASS_NEW).get(0);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) classNew.payload();
            SemanticOp forged = rebuildOp(classNew,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), DefaultOwner.BUILTIN_DEFAULTS,
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    payload.fieldBoundaries()));
            LoweredModuleUnit forgedUnit = withOps(unit, replaced(unit, forged));
            java.util.Optional<CompilerDiagnostic> failure =
                SemanticLowerer.validateProjectUnit(forgedUnit,
                    result.tableOf(MAIN),
                    new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                        project.index().interfaceIndexDigest(),
                        SemanticProfile.DEAL_V1_2_INT32,
                        CapabilityRegistry.releaseRegistry().capabilityRegistryHash()),
                    deal.semantic.BindingsProductionValidator.PinnedWriteFacts.empty(),
                    result.registryOf(MAIN),
                    new deal.semantic.ir.JsonDefaultChildTable(Map.of()),
                    project.index().modules().get(MAIN), Map.of());
            check(failure.isPresent(), "the forged BUILTIN_DEFAULTS owner fails the "
                + "composed gate");
            if (failure.isPresent()) {
                check("E6005".equals(failure.get().code()),
                    "the forged owner returns E6005; got " + failure.get().code());
                check(failure.get().message().contains(
                        deal.semantic.ClassConstructionValidator
                            .CONSTRUCTION_COHERENCE),
                    "the forged owner fails at CONSTRUCTION_COHERENCE; got "
                        + failure.get().message());
                check(failure.get().message().contains("BUILTIN_DEFAULTS"),
                    "the forged owner failure names BUILTIN_DEFAULTS; got "
                        + failure.get().message());
            }
        } finally {
            deleteRecursively(project.root());
        }

        // (b) has()/delete on a builtin Error field: the checker's
        // E4005/E4004 rejections (never a lowered shape).
        checkCheckerCode("""
            export function main(): null {
              let e: Error = { code: "a", message: "b" }
              let present: boolean = has(e.code)
              return null
            }
            """, "E4005", "has(e.code) is the checker's E4005 rejection");
        checkCheckerCode("""
            export function main(): null {
              let e: Error = { code: "a", message: "b" }
              delete e.code
              return null
            }
            """, "E4004", "delete e.code is the checker's E4004 rejection");
    }

    /** Rebuilds one op over a replacement payload (the digest recomputes). */
    private static SemanticOp rebuildOp(SemanticOp original, KindPayload payload) {
        deal.semantic.ir.OperationContractSnapshot placeholder =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, original.kind(),
                original.resultType(), original.operandTypes(), null, payload,
                original.failurePolicy(), List.of(), "placeholder");
        String digest = deal.semantic.ir.ContractSnapshotCanonicalizer.digest(placeholder);
        deal.semantic.ir.OperationContractSnapshot contract =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, original.kind(),
                original.resultType(), original.operandTypes(), null, payload,
                original.failurePolicy(), List.of(), digest);
        return new SemanticOp(original.opId(), original.kind(), original.origin(),
            original.result(), original.resultType(), original.operands(),
            original.operandTypes(), payload, original.failurePolicy(), contract);
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
                                             List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    private static List<SemanticOp> replaced(LoweredModuleUnit unit,
                                             SemanticOp replacement) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op.opId().equals(replacement.opId()) ? replacement : op);
        }
        return ops;
    }

    /** The checker's first diagnostic code of one module source. */
    private static void checkCheckerCode(String source, String expectedCode,
                                         String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": the snippet parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return;
        }
        ModuleResolver resolver = new ModuleResolver() {
            @Override
            public Map<String, deal.types.Type> resolveModule(String modulePath,
                    String importingModule, Set<String> modulesInProgress)
                    throws ModuleResolver.ModuleNotFoundException {
                throw new ModuleResolver.ModuleNotFoundException(
                    "Module not found: " + modulePath);
            }

            @Override
            public deal.checker.Symbol.ClassSymbol resolveClassSymbol(String className,
                    String modulePath, String importingModule) {
                return null;
            }
        };
        NameResolver names = new NameResolver(SOURCE_ID, resolver);
        SymbolTable symbols = names.resolve(parse.program());
        CheckResult checks = TypeChecker.check(SOURCE_ID, symbols, names,
            parse.program());
        boolean found = false;
        for (CompilerDiagnostic diagnostic : checks.diagnostics()) {
            if (expectedCode.equals(diagnostic.code())) {
                found = true;
            }
        }
        check(found, what + ": the diagnostic set carries " + expectedCode + "; got "
            + checks.diagnostics());
    }

    private static <T> void checkEq(T expected, T actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Builtin Error Construction Tests (ISSUE-0619) ===\n");
        testVerticalDrive();
        testProductionArtifacts();
        testNamedCorpusFixtures();
        testNegativeSeeds();
        System.out.println();
        System.out.println("Builtin Error construction: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
