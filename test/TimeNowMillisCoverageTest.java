package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.codegen.Backend;
import deal.checker.SymbolTable;
import deal.ast.MemberAccessExpr;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.StdlibCallRecognition;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0623: {@code time.nowMillis} coverage through the closed
 * {@code std.time}/{@code nowMillis} catalog row
 * ({@code semantic-ir-construct-coverage-cutover} K7, the
 * {@code time.nowMillis} contract, and K9 item 2).
 *
 * <ol>
 *   <li>the structural facts: {@code TIME_NOW_MILLIS} is the 21st closed
 *       {@link StdlibFunctionId} member with an empty
 *       {@code RESERVED_NAMES}, the catalog carries exactly one
 *       {@code std.time} row (zero parameter descriptors, the declared
 *       {@code int} result) as its last row, the recognition predicate
 *       resolves {@code time.nowMillis} to it, and
 *       {@code stdlibPolicy(TIME_NOW_MILLIS) == INT32_RESULT};</li>
 *   <li>the lowering facts: one {@code STDLIB_CALL(TIME_NOW_MILLIS)}
 *       with zero parameter boundaries, exactly one {@code STDLIB_RETURN}
 *       on the declared {@code int}, the {@code INT32_RESULT} terminal at
 *       the call origin, the {@code STDLIB_TIME_NOW_MILLIS} coverage row
 *       recorded (R-COVERAGE applies to it), the
 *       {@code STDLIB_SEMANTICS} claim, and zero
 *       {@code STDLIB_TIME_CONFLICT} claims;</li>
 *   <li>the vertical drive: the fixture runs through the semantic oracle
 *       and both shared artifacts under the real {@code luajit} and
 *       {@code javac --release 25 -proc:none} plus {@code java}
 *       toolchains with the three traces compared event-for-event and the
 *       pinned E8004 {@code int out of safe range} terminal at the call
 *       expression's origin;</li>
 *   <li>the corpus fixture drive: the real
 *       {@code backend-runtime/stdlib-edge/time-now-millis-positive}
 *       fixture compiles through the release-owned production invocation
 *       to exactly one project artifact per target and the artifact's
 *       published export fails with the pinned E8004 snapshot, message,
 *       and call-expression origin;</li>
 *   <li>the negative seed: a unit recording the coverage row with no
 *       produced {@code STDLIB_CALL} fails R-COVERAGE naming the row.</li>
 * </ol>
 */
public class TimeNowMillisCoverageTest {

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
    private static final Path WORKSPACE = Path.of("build/time-now-millis-diff");
    private static final Path FIXTURE = Path.of(
        "test/conformance/backend-runtime/stdlib-edge/time-now-millis-positive.deal");

    /**
     * The vertical fixture: the direct cataloged call in the entry body,
     * so the run terminal is the K7 E8004 projection.
     */
    private static final String TIME_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          time.nowMillis()
          return null
        }
        """;

    // =========================================================================
    // Small helpers
    // =========================================================================

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

    private static String readFixtureSource() throws Exception {
        StringBuilder out = new StringBuilder();
        for (String line : Files.readString(FIXTURE).split("\n", -1)) {
            if (line.trim().startsWith("// @")) {
                continue;
            }
            out.append(line).append('\n');
        }
        return out.toString();
    }

    /**
     * The {@code line:column} of the call expression in the given source
     * (1-based), computed from the text so the assertion pins the real
     * call-expression origin, never a hardcoded guess.
     */
    private static String callSiteOf(String source) {
        int line = 0;
        for (String text : source.split("\n", -1)) {
            line++;
            int column = text.indexOf("time.nowMillis()");
            if (column >= 0) {
                return line + ":" + (column + 1);
            }
        }
        throw new IllegalStateException("the source carries no time.nowMillis() call");
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

    // =========================================================================
    // 1. The closed catalog row (structural)
    // =========================================================================

    static void testClosedCatalogRow() throws Exception {
        System.out.println("-- the closed std.time/nowMillis catalog row --");

        check(StdlibFunctionId.values().length == 21
                && StdlibFunctionId.values()[20] == StdlibFunctionId.TIME_NOW_MILLIS,
            "TIME_NOW_MILLIS is the 21st closed StdlibFunctionId member in the pinned "
                + "order");
        check(StdlibFunctionId.RESERVED_NAMES.isEmpty(),
            "RESERVED_NAMES is empty (the superseded D8 reservation is retired) while "
                + "the reserved-name guard stays");
        Optional<StdlibFunctionCatalog.Entry> row =
            StdlibFunctionCatalog.lookup("std.time", "nowMillis");
        check(row.isPresent()
                && row.get().function() == StdlibFunctionId.TIME_NOW_MILLIS
                && row.get().parameterDescriptors().isEmpty()
                && row.get().returnDescriptor()
                    .equals(DescriptorService.describe(Type.Int.INSTANCE)),
            "the catalog carries std.time/nowMillis -> TIME_NOW_MILLIS with zero "
                + "parameter descriptors and the declared int result: " + row);
        check(StdlibFunctionCatalog.entries().size() == 21
                && StdlibFunctionCatalog.entries().get(20).modulePath().equals("std.time"),
            "the std.time group is the single last row (no existing row moved)");
        check(StdlibFunctionCatalog.lookup("std.time", "nope").isEmpty()
                && StdlibFunctionCatalog.lookup("std/time", "nowMillis").isEmpty(),
            "the catalog lookup is the only authority: an unknown member and the raw "
                + "slash-form specifier are never entries");
        check(SemanticIrValidator.stdlibPolicy(StdlibFunctionId.TIME_NOW_MILLIS)
                == FailurePolicyId.INT32_RESULT,
            "stdlibPolicy(TIME_NOW_MILLIS) == INT32_RESULT (the declared int boundary is "
                + "the single terminal)");

        // The recognition predicate over a real checked project.
        Path root = Files.createTempDirectory("time-now-millis-catalog-");
        try {
            Path src = root.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve(SOURCE_ID), TIME_SOURCE);
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve(SOURCE_ID).toAbsolutePath(), root.resolve("out"), false,
                false, false, false, Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null,
                ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            check(orchestrator.compile(), "the recognition fixture compiles: "
                + orchestrator.diagnostics());
            CheckedModuleInput module = orchestrator.checkedProject().input().modules().get(0);
            MemberAccessExpr call = null;
            for (var statement : module.ast().statements()) {
                if (statement instanceof deal.ast.ExportDeclaration exported
                        && exported.declaration()
                            instanceof deal.ast.FunctionDeclaration function
                        && function.body() != null) {
                    for (var bodyStatement : function.body().statements()) {
                        if (bodyStatement instanceof deal.ast.ExpressionStatement expression
                                && expression.expr() instanceof deal.ast.CallExpr callExpr
                                && callExpr.callee() instanceof MemberAccessExpr member) {
                            call = member;
                        }
                    }
                }
            }
            check(call != null, "the checked fixture carries the time.nowMillis callee");
            if (call != null) {
                Optional<StdlibFunctionCatalog.Entry> recognized =
                    StdlibCallRecognition.recognize(call, module.checks().symbolTable(),
                        module.imports());
                check(recognized.isPresent()
                        && recognized.get().function() == StdlibFunctionId.TIME_NOW_MILLIS,
                    "time.nowMillis is recognized through the closed catalog row: "
                        + (recognized.isEmpty() ? "empty"
                            : recognized.get().function().name()));
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 2. The vertical drive through the oracle and both real toolchains
    // =========================================================================

    private record RealProject(
        Path root,
        CompilationOrchestrator orchestrator,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface) {
    }

    private static RealProject compileProject(String source) throws Exception {
        Path root = Files.createTempDirectory("time-now-millis-");
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

    private static SemanticLowerer.ProjectLoweringResult lower(RealProject project) {
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        return SemanticLowerer.lowerProject(invocation, project.checkedProject(),
            project.index(), project.manifests(), project.surface(), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    static void testVerticalDrive() throws Exception {
        System.out.println("-- the time.nowMillis vertical drive: lowering, the oracle, "
            + "and both real-toolchain artifacts --");

        RealProject project = compileProject(TIME_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(!result.hasErrors() && result.project() != null,
                "the fixture lowers and validates through the one project entry: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            SemanticRequirementManifest manifest = null;
            for (SemanticRequirementManifest candidate : project.manifests()) {
                if (candidate.moduleId().equals(MAIN)) {
                    manifest = candidate;
                }
            }
            check(manifest != null
                    && manifest.capabilities().contains(
                        SemanticCapability.STDLIB_SEMANTICS)
                    && !manifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "the module claims STDLIB_SEMANTICS through the cataloged-call arm and "
                    + "never STDLIB_TIME_CONFLICT: "
                    + (manifest == null ? "no manifest" : manifest.capabilities()));
            check(manifest != null && manifest.constructCoverage()
                    .containsKey(ConstructKind.STDLIB_TIME_NOW_MILLIS),
                "the manifest records the STDLIB_TIME_NOW_MILLIS coverage row");
            LoweredModuleUnit unit = result.project().modules().get(MAIN);
            check(unit != null, "the entry unit is in the closure");
            if (unit == null) {
                return;
            }
            check(unit.constructCoverage()
                    .containsKey(ConstructKind.STDLIB_TIME_NOW_MILLIS),
                "the lowered unit records the STDLIB_TIME_NOW_MILLIS coverage row "
                    + "(R-COVERAGE applies to it)");

            SemanticOp timeCall = null;
            int stdlibCalls = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.STDLIB_CALL) {
                    stdlibCalls++;
                    if (((KindPayload.StdlibCallPayload) op.payload()).function()
                            == StdlibFunctionId.TIME_NOW_MILLIS) {
                        timeCall = op;
                    }
                }
            }
            check(stdlibCalls == 1 && timeCall != null,
                "exactly one STDLIB_CALL(TIME_NOW_MILLIS) is produced; got "
                    + stdlibCalls);
            if (timeCall == null) {
                return;
            }
            check(timeCall.failurePolicy() == FailurePolicyId.INT32_RESULT,
                "the op stamps the INT32_RESULT terminal; got "
                    + timeCall.failurePolicy());
            check(timeCall.operands().isEmpty() && timeCall.operandTypes().isEmpty(),
                "the zero-parameter row produces no parameter operands");
            check(((KindPayload.StdlibCallPayload) timeCall.payload()).effectCapability()
                    == SemanticCapability.STDLIB_SEMANTICS,
                "the op carries effectCapability STDLIB_SEMANTICS");
            int returns = 0;
            int params = 0;
            OpId timeReturnBoundary = null;
            for (SemanticOp child : unit.ops()) {
                if (!timeCall.opId().equals(child.origin().parentOpId())
                        || child.kind() != SemanticOpKind.BOUNDARY) {
                    continue;
                }
                KindPayload.BoundaryPayload boundary =
                    (KindPayload.BoundaryPayload) child.payload();
                if (boundary.kind() == BoundaryKind.STDLIB_RETURN) {
                    returns++;
                    timeReturnBoundary = child.opId();
                    check(boundary.descriptor()
                            .equals(DescriptorService.describe(Type.Int.INSTANCE)),
                        "the STDLIB_RETURN boundary carries the declared int descriptor");
                } else if (boundary.kind() == BoundaryKind.STDLIB_PARAMETER) {
                    params++;
                }
            }
            check(returns == 1 && params == 0,
                "exactly one STDLIB_RETURN and zero STDLIB_PARAMETER children; got "
                    + returns + "/" + params);

            // The oracle terminal: the pinned E8004 at the call-expression origin.
            String expectedSite = SOURCE_ID + ":" + callSiteOf(TIME_SOURCE);
            SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.execute(unit,
                result.tableOf(MAIN));
            check(oracle.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                    && "E8004".equals(failure.error().code())
                    && "int out of safe range".equals(failure.error().message())
                    && failure.error().origin().endsWith(expectedSite),
                "the oracle publishes the pinned E8004 int out of safe range at the "
                    + "call-expression origin " + expectedSite + "; got "
                    + oracle.terminal());

            // The three-consumer drive (oracle, LuaJIT, JVM): every
            // consumer publishes the pinned E8004 terminal at the
            // call-expression origin, and the three traces are equal
            // modulo the clock reading itself — the one event payload
            // that is intrinsically target-specific (the oracle injects
            // its pinned reading; each target reads its own wall clock),
            // which is why the DEAL-visible comparison of this construct
            // is the terminal snapshot the corpus sidecar pins.
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(result.project(), result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.failure(
                        "the time.nowMillis vertical drive", List.of(), "E8004", null),
                    WORKSPACE);
            check(verdict.runs().size() == 3,
                "three real consumers ran the project (oracle, LuaJIT, JVM): "
                    + verdict.report());
            for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                check(run.terminal()
                        instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                        && "E8004".equals(failure.error().code())
                        && "int out of safe range".equals(failure.error().message())
                        && failure.error().origin().endsWith(expectedSite),
                    run.consumer() + " publishes the pinned E8004 int out of safe range "
                        + "terminal at " + expectedSite + "; got " + run.terminal());
            }
            if (verdict.runs().size() == 3) {
                List<String> oracleLines = clockMaskedLines(verdict.runs().get(0),
                    timeReturnBoundary);
                for (int i = 1; i < verdict.runs().size(); i++) {
                    SemanticRuntimeModel.ConsumerRun run = verdict.runs().get(i);
                    List<String> laneLines = clockMaskedLines(run, timeReturnBoundary);
                    boolean equal = laneLines.equals(oracleLines);
                    check(equal, run.consumer() + " trace equals the oracle trace "
                        + "event-for-event modulo the clock reading: "
                        + (equal ? "" : firstDifference(oracleLines, laneLines)));
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    /**
     * The event lines of one run with the clock reading masked: the
     * {@code STDLIB_RETURN} input atom of the time call is replaced by a
     * placeholder (the value is the consumer's own clock reading, so it
     * can never be equal across processes; every other event, including
     * the failing boundary's FAILURE snapshot and the terminal, must
     * match exactly).
     */
    private static List<String> clockMaskedLines(SemanticRuntimeModel.ConsumerRun run,
                                                 OpId clockBoundary) {
        List<String> lines = new java.util.ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (clockBoundary != null && clockBoundary.equals(event.op())) {
                lines.add(event.sequence() + "|" + event.module() + "|"
                    + event.op().module().path() + "#" + event.op().id() + "|"
                    + event.phase() + "|" + event.kind() + "|"
                    + event.contractDigest() + "|"
                    + (event.parentOp() == null ? "-"
                        : event.parentOp().module().path() + "#" + event.parentOp().id())
                    + "|atom:<clock>");
            } else {
                lines.add(event.text());
            }
        }
        return lines;
    }

    private static String firstDifference(List<String> left, List<String> right) {
        int limit = Math.min(left.size(), right.size());
        for (int i = 0; i < limit; i++) {
            if (!left.get(i).equals(right.get(i))) {
                return "event " + i + ": " + left.get(i) + " vs " + right.get(i);
            }
        }
        if (left.size() != right.size()) {
            return "event count " + left.size() + " vs " + right.size();
        }
        return "no difference";
    }

    // =========================================================================
    // 3. The corpus fixture through the release-owned production invocation
    // =========================================================================

    private static CompilationOrchestrator productionCompile(Path root, String source,
            Backend backend) throws Exception {
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(SOURCE_ID), source);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(SOURCE_ID).toAbsolutePath(), root.resolve("out"), false, false,
            false, false, backend, null,
            List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null,
            CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
                ReleaseConfiguration.releaseCapabilityRegistry()));
        orchestrator.compile();
        return orchestrator;
    }

    static void testCorpusFixtureProductionDrive() throws Exception {
        System.out.println("-- the time-now-millis-positive corpus fixture through the "
            + "production pipeline on both targets --");

        String source = readFixtureSource();
        String expectedSite = SOURCE_ID + ":" + callSiteOf(source);
        String buildCp = Path.of("build").toAbsolutePath().normalize().toString();

        Path luaRoot = Files.createTempDirectory("time-now-millis-prod-lua-");
        try {
            CompilationOrchestrator lua = productionCompile(luaRoot, source,
                Backend.LUAJIT);
            check(lua.diagnostics().isEmpty(),
                "the LuaJIT production compile succeeds: " + lua.diagnostics());
            check(lua.semanticEmissionCount() == 1 && lua.retainedEmissionCount() == 0,
                "the LuaJIT production arm emits exactly one project artifact: "
                    + "semantic=" + lua.semanticEmissionCount() + " retained="
                    + lua.retainedEmissionCount());
            if (lua.diagnostics().isEmpty()) {
                Path out = luaRoot.resolve("out");
                Files.writeString(out.resolve("fixture_driver.lua"), """
                    local surfaces = dofile("main.lua")
                    local fn = surfaces["test_time_now_millis_positive"]
                    assert(type(fn) == "table" and fn.__kind == "function",
                      "the entry surface publishes the fixture export")
                    local ok, err = pcall(fn.f)
                    if ok then
                      io.write("FIXTURE_OK")
                    else
                      io.write("FIXTURE_FAIL|" .. tostring(err.code) .. "|"
                        .. tostring(err.m) .. "|" .. tostring(err.o))
                    end
                    """);
                ProjectOutcome run = runProcess(out, "luajit", "fixture_driver.lua");
                check(run.exitCode() == 0, "the LuaJIT fixture driver runs: exit="
                    + run.exitCode() + " output=" + run.output().replace("\n", "\\n"));
                check(run.output().contains("FIXTURE_FAIL|E8004|int out of safe range|")
                        && run.output().contains(expectedSite),
                    "the LuaJIT production artifact fails with the pinned E8004 "
                        + "snapshot, message, and call-expression origin " + expectedSite
                        + "; got " + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(luaRoot);
        }

        Path jvmRoot = Files.createTempDirectory("time-now-millis-prod-jvm-");
        try {
            CompilationOrchestrator jvm = productionCompile(jvmRoot, source, Backend.JVM);
            check(jvm.diagnostics().isEmpty(),
                "the JVM production compile succeeds: " + jvm.diagnostics());
            check(jvm.semanticEmissionCount() == 1 && jvm.retainedEmissionCount() == 0,
                "the JVM production arm emits exactly one project artifact: "
                    + "semantic=" + jvm.semanticEmissionCount() + " retained="
                    + jvm.retainedEmissionCount());
            if (jvm.diagnostics().isEmpty()) {
                Path out = jvmRoot.resolve("out");
                Files.writeString(out.resolve("FixtureDriver.java"), """
                    public final class FixtureDriver {
                      public static void main(String[] args) {
                        Main.main(new String[0]);
                        deal.codegen.jvm.JvmRuntime.FunctionValue fn =
                            (deal.codegen.jvm.JvmRuntime.FunctionValue) Main
                                .EXPORT_SURFACES.get("main")
                                .read("test_time_now_millis_positive");
                        try {
                          fn.fn.invoke(new Object[0]);
                          System.out.print("FIXTURE_OK");
                        } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                          System.out.print("FIXTURE_FAIL|" + error.code + "|"
                            + error.msg + "|" + error.origin);
                        }
                      }
                    }
                    """);
                ProjectOutcome javac = runProcess(jvmRoot, "javac", "--release", "25",
                    "-proc:none", "-cp", buildCp, "-d", out.toString(),
                    out.resolve("Main.java").toString(),
                    out.resolve("FixtureDriver.java").toString());
                check(javac.exitCode() == 0,
                    "the JVM fixture artifact compiles: " + javac.output());
                if (javac.exitCode() == 0) {
                    ProjectOutcome run = runProcess(out, "java", "-cp",
                        buildCp + java.io.File.pathSeparator + out, "FixtureDriver");
                    check(run.exitCode() == 0, "the JVM fixture driver runs: exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
                    check(run.output().contains(
                            "FIXTURE_FAIL|E8004|int out of safe range|")
                            && run.output().contains(expectedSite),
                        "the JVM production artifact fails with the pinned E8004 "
                            + "snapshot, message, and call-expression origin "
                            + expectedSite + "; got "
                            + run.output().replace("\n", "\\n"));
                }
            }
        } finally {
            deleteRecursively(jvmRoot);
        }
    }

    // =========================================================================
    // 4. The negative seed: the coverage row without a produced op
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.a");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(IFACE, SemanticProfile.DEAL_V1_2_INT32,
            REGISTRY);
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    private static int nextOp = 1;
    private static int nextVal = 1;

    private static OpId nextOpId() {
        return new OpId(MOD, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin("test.deal", SourceSpan.synthetic("test.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType,
            List<RuntimeDescriptor> operandTypes, FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy,
            OpId parent) {
        OperationContractSnapshot contract = contractFor(kind, payload, resultType,
            List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(),
            List.of(), payload, policy, contract);
    }

    private static LoweredModuleUnit syntheticUnit(
            Map<ConstructKind, List<SemanticOpKind>> coverage, List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, LCH,
            Set.of(SemanticCapability.STDLIB_SEMANTICS), coverage, Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            ops);
    }

    static void testCoverageRowNegativeSeed() {
        System.out.println("-- negative seed: the coverage row with no produced op fails "
            + "R-COVERAGE --");

        Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(
            ConstructKind.STDLIB_TIME_NOW_MILLIS,
            ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds());

        // Positive control: the row with a produced STDLIB_CALL passes.
        OpId callOp = nextOpId();
        OpId returnBoundary = nextOpId();
        List<SemanticOp> ops = List.of(
            opWith(returnBoundary, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.STDLIB_RETURN,
                    RuntimeDescriptor.Int.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("check")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, callOp),
            opWith(callOp, SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(StdlibFunctionId.TIME_NOW_MILLIS,
                    List.of(), SemanticCapability.STDLIB_SEMANTICS),
                nextValue(), RuntimeDescriptor.Int.INSTANCE,
                FailurePolicyId.INT32_RESULT, null));
        Optional<CompilerDiagnostic> pass =
            SemanticIrValidator.validate(syntheticUnit(coverage, ops), FACTS);
        check(pass.isEmpty(),
            "the std/time.nowMillis row with a produced STDLIB_CALL validates: "
                + (pass.isEmpty() ? "clean" : pass.get().message()));

        // The negative: the row with no produced op of a mapped kind.
        Optional<CompilerDiagnostic> rejected = SemanticIrValidator.validate(
            syntheticUnit(coverage, List.of(opWith(nextOpId(), SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new deal.semantic.ir.ScalarValue.Int(1)),
                nextValue(), RuntimeDescriptor.Int.INSTANCE, FailurePolicyId.NO_DEAL_FAILURE,
                null))), FACTS);
        check(rejected.isPresent()
                && rejected.get().diagnosticCode() == DiagnosticCode.E6005
                && rejected.get().message().contains("R-COVERAGE")
                && rejected.get().message().contains("STDLIB_TIME_NOW_MILLIS"),
            "the coverage row with no produced op fails R-COVERAGE naming the row: "
                + (rejected.isEmpty() ? "no rejection" : rejected.get().message()));
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== time.nowMillis Coverage Tests (ISSUE-0623) ===\n");

        testClosedCatalogRow();
        testVerticalDrive();
        testCorpusFixtureProductionDrive();
        testCoverageRowNegativeSeed();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
