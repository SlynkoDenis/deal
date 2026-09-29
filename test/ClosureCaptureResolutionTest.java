package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.diagnostics.CompilerDiagnostic;
import deal.module.CompilationOrchestrator;
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * ISSUE-0701: the closure capture resolution and the per-iteration
 * incarnations (design source {@code dispatched-corpus-production-realization}
 * R4 item 5, R7, and the capture contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C1/C2/C10).
 *
 * <ol>
 *   <li><b>The five named fixtures.</b> {@code control-flow/for-of-closure},
 *       {@code closures/for-loop-closure-values},
 *       {@code closures/nested-loop-closure-capture},
 *       {@code functions/for-loop-closure}, and
 *       {@code functions/for-loop-closure-array} compile through the
 *       release-owned production invocation on LuaJIT and JVM with zero
 *       E6005 (no {@code CONSTRUCT_UNLOWERED}, no
 *       {@code RETAINED_ABI_DEFERRED}, no {@code SHARED_EMITTER_COVERAGE},
 *       no {@code CAPTURE_RESOLUTION}), publish one project artifact per
 *       target with no retained emission, and execute under the real
 *       toolchains ({@code luajit}; {@code javac --release 25 -proc:none} +
 *       {@code java}) with their pinned sidecar transcripts.</li>
 *   <li><b>The pinned values and the oracle.</b> Each fixture compiles in
 *       the lane layout with a driver entry module that calls the fixture's
 *       exported zero-arity probe and asserts its pinned value
 *       ({@code 123}, {@code 6}, {@code 22}, {@code 12}, {@code 12}); the
 *       one project lowering reports zero diagnostics, the closed schema
 *       and bindings gates accept the closure, and the differential matrix
 *       (semantic oracle + shared LuaJIT + shared JVM) passes
 *       event-for-event.</li>
 *   <li><b>The per-iteration structure.</b> Every closure created inside a
 *       loop iteration captures the <em>creation-site incarnation</em> of
 *       the captured binding (the for-let per-iteration generation 1, the
 *       {@code FOR_EACH} iteration generation), never the loop counter's
 *       generation 0; the emitted artifacts pass the per-iteration cell at
 *       the creation and the emitted factory reads its capture parameter —
 *       never the module-scoped slot.</li>
 *   <li><b>The fail-closed arms.</b> A hand-built closure capture entry
 *       whose generation does not name the creation-site incarnation and a
 *       hand-built detached-body reference with no capture registration
 *       both fail closed with {@code CAPTURE_RESOLUTION}, naming the
 *       binding, the op, and the function.</li>
 *   <li><b>The landed cell discipline.</b> Two closures over one captured
 *       cell observe each other's in-place commit; repeated lowering and
 *       emission of the same input are byte-identical.</li>
 * </ol>
 */
public class ClosureCaptureResolutionTest {

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
        check(Objects.equals(expected, actual), message + " (expected " + expected
            + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static final Path CORPUS =
        Path.of("test", "conformance", "backend-runtime");

    /** The lane's entry-module shape (the corpus entry shim). */
    private static final String CORPUS_ENTRY_SHIM =
        "export function main(): null {\n  return null;\n}\n";

    /** The loop-capture shape one fixture pins. */
    private enum CaptureKind {
        /** The FOR_EACH iteration binding is the captured incarnation. */
        FOR_OF_ITERATION,
        /** The for-let per-iteration generation-1 incarnation is captured. */
        FOR_LET_PER_ITERATION,
        /** A loop-body local (a shared cell allocated inside the loop body). */
        FOR_BODY_LOCAL
    }

    /**
     * One named corpus fixture: its corpus-relative path, its exported
     * zero-arity probe, the probe's pinned runtime value, and the
     * loop-capture shape its closures pin.
     */
    private record Case(String relativePath, String exportName, long value,
                        CaptureKind captureKind) {

        /** The fixture's module identity under the lane layout. */
        String modulePath() {
            return relativePath.replace('/', '.');
        }

        String fixtureFile() {
            return CORPUS.resolve(relativePath + ".deal").toString();
        }

        String sidecarFile() {
            return CORPUS.resolve(relativePath + ".expect.json").toString();
        }
    }

    private static final List<Case> CASES = List.of(
        new Case("control-flow/for-of-closure", "test_closure_capture", 123,
            CaptureKind.FOR_OF_ITERATION),
        new Case("closures/for-loop-closure-values", "test_loop_closure_sum", 6,
            CaptureKind.FOR_LET_PER_ITERATION),
        new Case("closures/nested-loop-closure-capture",
            "test_nested_loop_closure_capture", 22,
            CaptureKind.FOR_BODY_LOCAL),
        new Case("functions/for-loop-closure", "test_for_closure", 12,
            CaptureKind.FOR_LET_PER_ITERATION),
        new Case("functions/for-loop-closure-array", "test_for_closure_array", 12,
            CaptureKind.FOR_LET_PER_ITERATION));

    // =========================================================================
    // The production invocation and the compile helpers
    // =========================================================================

    /** The release-owned production invocation (C8's record). */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** The fixture source with its classification headers stripped, verbatim. */
    private static String fixtureSource(String relativePath) throws Exception {
        return ConformanceHarnessMetadata.stripClassificationHeaders(
            Files.readString(CORPUS.resolve(relativePath + ".deal"),
                StandardCharsets.UTF_8));
    }

    private static CompilationOrchestrator productionCompile(Path moduleRoot, Path entry,
            Backend backend) throws Exception {
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry.toAbsolutePath(), moduleRoot.getParent().resolve("out"), false,
            false, false, false, backend, null, List.of(moduleRoot.toAbsolutePath()),
            null, null, productionInvocation());
        orchestrator.compile();
        return orchestrator;
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return stdout + stderr;
        }
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.redirectErrorStream(false);
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        return new ProcessOutcome(process.waitFor(), stdout, stderr);
    }

    private static String absoluteClasspath() {
        return Path.of("build").toAbsolutePath().normalize().toString();
    }

    private static void writeFile(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
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

    // =========================================================================
    // 1. The corpus inventory and its unchanged pins
    // =========================================================================

    private static void testCorpusInventory() throws Exception {
        System.out.println("-- the five named fixtures and their unchanged sidecar pins --");
        for (Case corpusCase : CASES) {
            Path fixture = Path.of(corpusCase.fixtureFile());
            Path sidecar = Path.of(corpusCase.sidecarFile());
            check(Files.exists(fixture), corpusCase.relativePath()
                + ": the fixture is present");
            check(Files.exists(sidecar), corpusCase.relativePath()
                + ": the sidecar is present");
            String text = Files.readString(sidecar, StandardCharsets.UTF_8);
            check(text.contains("\"mode\": \"runtime-ok\""), corpusCase.relativePath()
                + ": the sidecar pins the runtime-ok mode");
            checkEq(0, sidecarExitCode(text), corpusCase.relativePath()
                + ": the sidecar pins exit code 0");
            checkEq("", sidecarTranscript(text, "stdout"), corpusCase.relativePath()
                + ": the sidecar pins an empty stdout");
            checkEq("", sidecarTranscript(text, "stderr"), corpusCase.relativePath()
                + ": the sidecar pins an empty stderr");
            String source = fixtureSource(corpusCase.relativePath());
            check(source.endsWith(CORPUS_ENTRY_SHIM), corpusCase.relativePath()
                + ": the corpus entry shim is present (the lane's entry shape)");
            check(!source.contains("import "), corpusCase.relativePath()
                + ": the fixture is a single-module compilation set");
        }
    }

    private static int sidecarExitCode(String sidecar) {
        Matcher matcher = Pattern.compile("\"exitCode\":\\s*(-?\\d+)").matcher(sidecar);
        return matcher.find() ? Integer.parseInt(matcher.group(1)) : Integer.MIN_VALUE;
    }

    private static String sidecarTranscript(String sidecar, String channel) {
        Matcher matcher = Pattern.compile("\"" + channel
            + "\":\\s*\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(sidecar);
        if (!matcher.find()) {
            return null;
        }
        return matcher.group(1).replace("\\n", "\n").replace("\\\"", "\"");
    }

    // =========================================================================
    // 2. The production artifacts, the real toolchains, and the sidecars
    // =========================================================================

    private static void testProductionArtifacts() throws Exception {
        System.out.println("-- the fixtures as their own entry module through the "
            + "release-owned production invocation on both targets --");
        for (Case corpusCase : CASES) {
            // LuaJIT.
            Path luaRoot = Files.createTempDirectory("closure-capture-lua-");
            try {
                writeFile(luaRoot, "src/" + corpusCase.relativePath() + ".deal",
                    fixtureSource(corpusCase.relativePath()));
                Path entry = luaRoot.resolve("src")
                    .resolve(corpusCase.relativePath() + ".deal");
                CompilationOrchestrator lua = productionCompile(
                    luaRoot.resolve("src"), entry, Backend.LUAJIT);
                check(lua.diagnostics().isEmpty(), corpusCase.relativePath()
                    + ": the LuaJIT production compile reports zero diagnostics: "
                    + lua.diagnostics());
                check(lua.semanticEmissionCount() == 1
                        && lua.retainedEmissionCount() == 0,
                    corpusCase.relativePath() + ": the LuaJIT production arm emits "
                        + "exactly one project artifact and no retained emission: "
                        + "semantic=" + lua.semanticEmissionCount() + " retained="
                        + lua.retainedEmissionCount());
                Path artifact = luaRoot.resolve("out")
                    .resolve(corpusCase.relativePath() + ".lua");
                check(Files.exists(artifact), corpusCase.relativePath()
                    + ": the LuaJIT artifact is staged at the entry module path");
                if (Files.exists(artifact)) {
                    writeFile(luaRoot.resolve("out"), "closure_capture_driver.lua",
                        luaDriver(corpusCase));
                    ProcessOutcome run = runProcess(List.of("luajit",
                        "closure_capture_driver.lua"), luaRoot.resolve("out"));
                    checkEq(0, run.exitCode(), corpusCase.relativePath()
                        + ": the production LuaJIT artifact executes the exported "
                        + "probe with exit 0: " + run.output());
                    assertSidecarTranscript(corpusCase, "LuaJIT", run);
                }
            } finally {
                deleteRecursively(luaRoot);
            }

            // JVM.
            Path jvmRoot = Files.createTempDirectory("closure-capture-jvm-");
            try {
                writeFile(jvmRoot, "src/" + corpusCase.relativePath() + ".deal",
                    fixtureSource(corpusCase.relativePath()));
                Path entry = jvmRoot.resolve("src")
                    .resolve(corpusCase.relativePath() + ".deal");
                CompilationOrchestrator jvm = productionCompile(
                    jvmRoot.resolve("src"), entry, Backend.JVM);
                check(jvm.diagnostics().isEmpty(), corpusCase.relativePath()
                    + ": the JVM production compile reports zero diagnostics: "
                    + jvm.diagnostics());
                check(jvm.semanticEmissionCount() == 1
                        && jvm.retainedEmissionCount() == 0,
                    corpusCase.relativePath() + ": the JVM production arm emits "
                        + "exactly one project artifact and no retained emission: "
                        + "semantic=" + jvm.semanticEmissionCount() + " retained="
                        + jvm.retainedEmissionCount());
                String className = JvmBackend.classNameFor(corpusCase.relativePath());
                Path artifact = jvmRoot.resolve("out").resolve(className + ".java");
                check(Files.exists(artifact), corpusCase.relativePath()
                    + ": the JVM artifact is the one project class");
                if (Files.exists(artifact)) {
                    Path classes = jvmRoot.resolve("classes");
                    Files.createDirectories(classes);
                    writeFile(jvmRoot, "out/CaptureProbe.java",
                        jvmDriver(className, corpusCase));
                    ProcessOutcome javac = runProcess(List.of("javac", "--release", "25",
                        "-proc:none", "-cp", absoluteClasspath(), "-d", classes.toString(),
                        artifact.toAbsolutePath().toString(),
                        jvmRoot.resolve("out/CaptureProbe.java").toAbsolutePath()
                            .toString()),
                        jvmRoot.resolve("out"));
                    checkEq(0, javac.exitCode(), corpusCase.relativePath()
                        + ": the production JVM artifact compiles: " + javac.output());
                    if (javac.exitCode() == 0) {
                        ProcessOutcome run = runProcess(List.of("java", "-cp",
                            absoluteClasspath() + File.pathSeparator + classes,
                            "CaptureProbe"), jvmRoot.resolve("out"));
                        checkEq(0, run.exitCode(), corpusCase.relativePath()
                            + ": the production JVM artifact executes the exported "
                            + "probe with exit 0: " + run.output());
                        assertSidecarTranscript(corpusCase, "JVM", run);
                    }
                }
            } finally {
                deleteRecursively(jvmRoot);
            }
        }
    }

    /** The runtime-ok sidecar pins the exit code and both empty transcripts. */
    private static void assertSidecarTranscript(Case corpusCase, String target,
            ProcessOutcome run) throws Exception {
        String sidecar = Files.readString(Path.of(corpusCase.sidecarFile()),
            StandardCharsets.UTF_8);
        checkEq(sidecarExitCode(sidecar), run.exitCode(), corpusCase.relativePath()
            + " (" + target + "): the executed fixture's exit code equals the "
            + "sidecar pin");
        checkEq(sidecarTranscript(sidecar, "stdout"), run.stdout(),
            corpusCase.relativePath() + " (" + target
                + "): the executed fixture's stdout equals the sidecar pin");
        checkEq(sidecarTranscript(sidecar, "stderr"), run.stderr(),
            corpusCase.relativePath() + " (" + target
                + "): the executed fixture's stderr equals the sidecar pin");
    }

    /**
     * The LuaJIT driver: the module walk, then the fixture's exported
     * zero-arity probe through the entry surface (the lane's invocation
     * contract — return values are discarded, the probe's own guards are the
     * pinned outcome).
     */
    private static String luaDriver(Case corpusCase) {
        return """
            local surfaces = dofile("%s.lua")
            assert(type(surfaces) == "table",
              "the production chunk returns the entry surface")
            local probe = surfaces["%s"]
            assert(type(probe) == "table" and probe.__kind == "function"
              and type(probe.f) == "function",
              "the entry surface publishes the fixture probe")
            probe.f()
            """.formatted(corpusCase.relativePath(), corpusCase.exportName());
    }

    /**
     * The JVM driver: the module walk, then the fixture's exported zero-arity
     * probe through the entry module's published surface.
     */
    private static String jvmDriver(String className, Case corpusCase) {
        return """
            public final class CaptureProbe {
              public static void main(String[] args) {
                %s.main(new String[0]);
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.EXPORT_SURFACES.get("%s");
                Object probe = surface.read("%s");
                if (!(probe instanceof deal.codegen.jvm.JvmRuntime.FunctionValue fn)) {
                  throw new IllegalStateException(
                      "the entry surface publishes the fixture probe");
                }
                fn.fn.invoke(new Object[0]);
              }
            }
            """.formatted(className, className, corpusCase.modulePath(),
                corpusCase.exportName());
    }

    // =========================================================================
    // 3. The pinned values through the one lowering and the oracle
    // =========================================================================

    /** One lowered fixture project (the driver form). */
    private record Drive(
        Path root,
        ExecutableLoweredProject project,
        Map<ModuleId, StructuredBodyTable> tables,
        Map<ModuleId, ClassFactoryRegistry> registries,
        LoweredModuleUnit unit,
        StructuredBodyTable table) {
    }

    /**
     * Materializes one fixture in the lane layout plus a driver entry module
     * that calls the fixture's exported probe and asserts its pinned value,
     * compiles it through the production invocation, and lowers it through
     * the one project entry.
     */
    private static Drive drive(Case corpusCase) throws Exception {
        Path root = Files.createTempDirectory("closure-capture-drive-");
        String source = fixtureSource(corpusCase.relativePath());
        String fixtureModule = source.substring(0, source.length()
            - CORPUS_ENTRY_SHIM.length());
        writeFile(root, "src/" + corpusCase.relativePath() + ".deal", fixtureModule);
        writeFile(root, "src/app.deal",
            "import * as fx from \"./" + corpusCase.relativePath() + "\"\n\n"
                + "export function main(): null {\n"
                + "  let r: int = fx." + corpusCase.exportName() + "()\n"
                + "  if (r !== " + corpusCase.value() + ") {\n"
                + "    throw { code: \"TEST_FAIL\", message: \""
                + corpusCase.relativePath() + " pinned value\" }\n"
                + "  }\n"
                + "  return null\n"
                + "}\n");
        return lower(root);
    }

    /** The production compile plus the one project lowering of one project root. */
    private static Drive lower(Path root) throws Exception {
        CompilationOrchestrator orchestrator = productionCompile(root.resolve("src"),
            root.resolve("src/app.deal"), Backend.LUAJIT);
        check(orchestrator.diagnostics().isEmpty(),
            "the project compiles through the production invocation: "
                + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            return null;
        }
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(), Map.of(),
            Map.of(), BuiltinErrorDeclaration.synthesized(
                built.input().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null && !result.hasErrors(),
            "the one project lowering reports zero diagnostics (no CONSTRUCT_UNLOWERED, "
                + "no RETAINED_ABI_DEFERRED, no SHARED_EMITTER_COVERAGE, no "
                + "CAPTURE_RESOLUTION): " + result.diagnostics());
        if (result.project() == null) {
            deleteRecursively(root);
            return null;
        }
        LoweredModuleUnit unit = result.project().modules()
            .get(result.project().entryModule());
        StructuredBodyTable table = result.tables().get(result.project().entryModule());
        return new Drive(root, result.project(), result.tables(), result.registries(),
            unit, table);
    }

    private static void testDifferentialMatrix() throws Exception {
        System.out.println("-- the pinned values through the oracle and both shared "
            + "artifacts (the differential matrix) --");
        for (Case corpusCase : CASES) {
            Drive drive = drive(corpusCase);
            if (drive == null) {
                continue;
            }
            try {
                ModuleId fixtureModule = new ModuleId(corpusCase.modulePath());
                LoweredModuleUnit unit = drive.project().modules().get(fixtureModule);
                check(unit != null, corpusCase.relativePath()
                    + ": the fixture module is part of the closure: "
                    + drive.project().modules().keySet());
                if (unit != null) {
                    Optional<CompilerDiagnostic> gate = SemanticIrValidator.validate(
                        drive.project(), new SemanticIrValidator.ComparisonFacts(
                            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                            ReleaseConfiguration.releaseCapabilityRegistry()
                                .capabilityRegistryHash()));
                    check(gate.isEmpty(), corpusCase.relativePath()
                        + ": the closed schema and bindings gates accept the closure: "
                        + gate.map(CompilerDiagnostic::message).orElse("admission"));
                }
                Path workspace = Files.createTempDirectory("closure-capture-matrix-");
                try {
                    SemanticDifferentialHarness.Verdict verdict =
                        SemanticDifferentialHarness.runProject(drive.project(),
                            drive.tables(), drive.registries(),
                            SemanticDifferentialHarness.Expectation.success(
                                corpusCase.relativePath(), List.of(), "null"),
                            workspace);
                    checkEq(3, verdict.runs().size(), corpusCase.relativePath()
                        + ": the drive produced the three consumers: "
                        + verdict.failures());
                    check(verdict.pass(), corpusCase.relativePath()
                        + ": the three-consumer differential verdict passes (the "
                        + "pinned per-iteration value and the traces event-for-event): "
                        + verdict.failures());
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.Success,
                            corpusCase.relativePath() + ": " + run.consumer()
                                + " completes with the driver's pinned-value guard: "
                                + run.terminal());
                    }
                } finally {
                    deleteRecursively(workspace);
                }
            } finally {
                deleteRecursively(drive.root());
            }
        }
    }

    // =========================================================================
    // 4. The per-iteration capture structure
    // =========================================================================

    /**
     * One production compile of one fixture as its own entry module, with
     * the one project lowering over the same inputs and the emitted
     * artifact text of that target.
     */
    private record EntryDrive(Path root, Drive drive, String fixtureModulePath,
            String artifactText) {
    }

    private static EntryDrive entryDrive(Case corpusCase, Backend backend)
            throws Exception {
        Path root = Files.createTempDirectory("closure-capture-entry-");
        String source = fixtureSource(corpusCase.relativePath());
        writeFile(root, "src/" + corpusCase.relativePath() + ".deal", source);
        Path entry = root.resolve("src").resolve(corpusCase.relativePath() + ".deal");
        CompilationOrchestrator orchestrator = productionCompile(root.resolve("src"),
            entry, backend);
        check(orchestrator.diagnostics().isEmpty(), corpusCase.relativePath()
            + ": the " + backend + " production compile reports zero diagnostics: "
            + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            return null;
        }
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(), Map.of(),
            Map.of(), BuiltinErrorDeclaration.synthesized(
                built.input().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null && !result.hasErrors(),
            corpusCase.relativePath() + ": the " + backend + " fixture project lowers "
                + "with zero diagnostics: " + result.diagnostics());
        if (result.project() == null) {
            deleteRecursively(root);
            return null;
        }
        ModuleId module = new ModuleId(corpusCase.modulePath());
        String artifact = backend == Backend.JVM
            ? root.resolve("out").resolve(
                JvmBackend.classNameFor(corpusCase.relativePath()) + ".java").toString()
            : root.resolve("out")
                .resolve(corpusCase.relativePath() + ".lua").toString();
        String text = Files.exists(Path.of(artifact))
            ? Files.readString(Path.of(artifact), StandardCharsets.UTF_8) : null;
        Drive drive = new Drive(root, result.project(), result.tables(),
            result.registries(), result.project().modules().get(module),
            result.tables().get(module));
        return new EntryDrive(root, drive, corpusCase.modulePath(), text);
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

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    /** One binding incarnation's producing allocation. */
    private record Incarnation(BindingId binding, long generation, BlockId scope,
            BindingCellKind kind) {
    }

    private static List<Incarnation> incarnationsOf(LoweredModuleUnit unit) {
        List<Incarnation> incarnations = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc) {
                incarnations.add(new Incarnation(alloc.binding(), alloc.generation(),
                    alloc.scope(), alloc.cellKind()));
            } else if (op.payload() instanceof KindPayload.ForEachPayload forEach) {
                incarnations.add(new Incarnation(forEach.binding(), forEach.generation(),
                    forEach.body(), BindingCellKind.SHARED_CELL));
            }
        }
        return incarnations;
    }

    private static Incarnation incarnation(List<Incarnation> incarnations,
            BindingId binding, long generation) {
        for (Incarnation incarnation : incarnations) {
            if (incarnation.binding().equals(binding)
                    && incarnation.generation() == generation) {
                return incarnation;
            }
        }
        return null;
    }

    /** The blocks of one function-body region (the structured child traversal). */
    private static Set<BlockId> regionBlocks(LoweredModuleUnit unit,
            StructuredBodyTable table, BlockId root) {
        Set<BlockId> blocks = new LinkedHashSet<>();
        Deque<BlockId> queue = new ArrayDeque<>();
        queue.add(root);
        while (!queue.isEmpty()) {
            BlockId block = queue.poll();
            if (block == null || !blocks.add(block)) {
                continue;
            }
            for (OpId opId : table.blockOps().getOrDefault(block, List.of())) {
                SemanticOp op = opOf(unit, opId);
                if (op == null) {
                    continue;
                }
                switch (op.payload()) {
                    case KindPayload.BranchPayload branch -> {
                        addBlock(queue, branch.selectedBlock());
                        addBlock(queue, branch.alternateBlock());
                    }
                    case KindPayload.LoopPayload loop -> {
                        addBlock(queue, loop.initBlock());
                        addBlock(queue, loop.bodyBlock());
                        addBlock(queue, loop.updateBlock());
                    }
                    case KindPayload.ForEachPayload forEach ->
                        addBlock(queue, forEach.body());
                    case KindPayload.TryCatchPayload tryCatch -> {
                        addBlock(queue, tryCatch.tryBlock());
                        addBlock(queue, tryCatch.catchBlock());
                    }
                    default -> {
                        // No structured children.
                    }
                }
            }
        }
        return blocks;
    }

    /** Enqueues one structured child block when the payload carries one. */
    private static void addBlock(Deque<BlockId> queue, BlockId block) {
        if (block != null) {
            queue.add(block);
        }
    }

    /** True iff the function's region reads/stores the capture at its generation. */
    private static boolean bodyReferencesCapture(LoweredModuleUnit unit,
            StructuredBodyTable table, LoweredFunction function,
            BindingGeneration capture) {
        if (function == null || table == null) {
            return false;
        }
        Set<BlockId> region = regionBlocks(unit, table, function.body());
        for (BlockId block : region) {
            for (OpId opId : table.blockOps().getOrDefault(block, List.of())) {
                SemanticOp op = opOf(unit, opId);
                if (op == null) {
                    continue;
                }
                if (op.payload() instanceof KindPayload.BindingLoadPayload load
                        && load.binding().equals(capture.binding())
                        && load.generation() == capture.generation()) {
                    return true;
                }
                if (op.payload() instanceof KindPayload.BindingStorePayload store
                        && store.binding().equals(capture.binding())
                        && store.generation() == capture.generation()) {
                    return true;
                }
            }
        }
        return false;
    }

    private static void testPerIterationStructure() throws Exception {
        System.out.println("-- every closure captures its creation-site incarnation, "
            + "and the emitted factory reads its capture parameter --");
        for (Case corpusCase : CASES) {
            EntryDrive lua = entryDrive(corpusCase, Backend.LUAJIT);
            if (lua == null) {
                continue;
            }
            EntryDrive jvm = null;
            try {
                jvm = entryDrive(corpusCase, Backend.JVM);
                checkStructure(corpusCase, lua, jvm);
            } finally {
                deleteRecursively(lua.root());
                if (jvm != null) {
                    deleteRecursively(jvm.root());
                }
            }
        }
    }

    private static void checkStructure(Case corpusCase, EntryDrive lua, EntryDrive jvm) {
        LoweredModuleUnit unit = lua.drive().unit();
        StructuredBodyTable table = lua.drive().table();
        List<Incarnation> incarnations = incarnationsOf(unit);
        int capturedClosures = 0;
        for (SemanticOp closure : ofKind(unit, SemanticOpKind.CLOSURE_NEW)) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) closure.payload();
            if (payload.captures().isEmpty()) {
                continue;
            }
            capturedClosures++;
            LoweredFunction function = unit.functions().get(payload.function());
            check(function != null && function.captures().equals(payload.captures()),
                corpusCase.relativePath() + ": the LoweredFunction repeats the "
                    + "generation-pinned capture list of " + closure.opId());
            for (BindingGeneration capture : payload.captures()) {
                Incarnation incarnation = incarnation(incarnations,
                    capture.binding(), capture.generation());
                check(incarnation != null, corpusCase.relativePath() + ": the capture "
                    + capture.binding() + "#" + capture.generation() + " of "
                    + closure.opId() + " names a producing allocation of the unit");
                if (incarnation != null) {
                    checkEq(BindingCellKind.SHARED_CELL, incarnation.kind(),
                        corpusCase.relativePath() + ": the captured incarnation "
                            + capture.binding() + "#" + capture.generation() + " of "
                            + closure.opId() + " is a shared cell");
                }
                if (incarnation(incarnations, capture.binding(), 0) != null
                        && incarnation(incarnations, capture.binding(), 1) != null) {
                    checkEq(1L, capture.generation(), corpusCase.relativePath()
                        + ": the capture of the per-iteration binding "
                        + capture.binding() + " in " + closure.opId() + " names the "
                        + "creation-site incarnation, not the counter");
                }
                check(bodyReferencesCapture(unit, table, function, capture),
                    corpusCase.relativePath() + ": the body of " + payload.function()
                        + " reads the captured " + capture.binding() + " at generation "
                        + capture.generation());
            }
            checkEmittedCapture(corpusCase, payload, lua.artifactText(),
                jvm == null ? null : jvm.artifactText());
        }
        check(capturedClosures > 0, corpusCase.relativePath()
            + ": at least one closure of the fixture captures a binding");
        SemanticOp loop = loopOf(unit);
        check(loop != null, corpusCase.relativePath()
            + ": the fixture carries its loop structure");
        if (loop != null) {
            checkLoopCapture(corpusCase, loop, unit, incarnations);
        }
    }

    /** True iff the block sits inside one of the loops the unit carries. */
    private static boolean insideLoopBody(LoweredModuleUnit unit, BlockId block) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.LoopPayload loop
                    && block.equals(loop.bodyBlock())) {
                return true;
            }
            if (op.payload() instanceof KindPayload.ForEachPayload forEach
                    && block.equals(forEach.body())) {
                return true;
            }
        }
        return false;
    }

    /** The fixture's loop op (the LOOP(FOR) or the FOR_EACH). */
    private static SemanticOp loopOf(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.LOOP
                    || op.kind() == SemanticOpKind.FOR_EACH) {
                return op;
            }
        }
        return null;
    }

    /**
     * The loop's own capture clause: the per-iteration incarnation exists
     * beside the counter (for-let) or is the pinned shared iteration cell
     * (for-of), and every closure of the unit that captures the iteration
     * binding names the creation-site incarnation.
     */
    private static void checkLoopCapture(Case corpusCase, SemanticOp loop,
            LoweredModuleUnit unit, List<Incarnation> incarnations) {
        switch (corpusCase.captureKind()) {
            case FOR_OF_ITERATION -> {
                KindPayload.ForEachPayload forEach =
                    (KindPayload.ForEachPayload) loop.payload();
                Incarnation iteration = incarnation(incarnations, forEach.binding(),
                    forEach.generation());
                check(iteration != null
                        && iteration.kind() == BindingCellKind.SHARED_CELL,
                    corpusCase.relativePath() + ": the FOR_EACH iteration binding of "
                        + loop.opId() + " is a shared cell (B2)");
                check(isCapturedAt(unit, forEach.binding(), forEach.generation()),
                    corpusCase.relativePath() + ": a closure captures the FOR_EACH "
                        + "iteration binding at its iteration incarnation");
            }
            case FOR_LET_PER_ITERATION -> {
                KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
                BindingId counterBinding = null;
                for (Incarnation incarnation : incarnations) {
                    if (incarnation.scope().equals(payload.initBlock())
                            && incarnation.generation() == 0) {
                        counterBinding = incarnation.binding();
                    }
                }
                check(counterBinding != null, corpusCase.relativePath()
                    + ": the for-let counter incarnation exists in the init block");
                if (counterBinding == null) {
                    return;
                }
                Incarnation counter = incarnation(incarnations, counterBinding, 0);
                Incarnation perIteration = incarnation(incarnations, counterBinding, 1);
                check(perIteration != null, corpusCase.relativePath()
                    + ": the for-let per-iteration incarnation (generation 1) exists");
                if (perIteration == null) {
                    return;
                }
                checkEq(payload.bodyBlock(), perIteration.scope(),
                    corpusCase.relativePath() + ": the per-iteration incarnation is "
                        + "allocated at the body top");
                checkEq(BindingCellKind.SHARED_CELL, perIteration.kind(),
                    corpusCase.relativePath() + ": the per-iteration incarnation is a "
                        + "shared cell");
                check(counter != null && counter.kind() == BindingCellKind.DIRECT,
                    corpusCase.relativePath() + ": the loop counter stays DIRECT "
                        + "(only the captured incarnation upgrades)");
                checkEq(1L, perIteration.generation(), corpusCase.relativePath()
                    + ": the for-let per-iteration generation is the pinned 1");
                check(isCapturedAt(unit, counterBinding, 1L),
                    corpusCase.relativePath() + ": a closure captures the for-let "
                        + "binding at its per-iteration incarnation");
            }
            case FOR_BODY_LOCAL -> {
                // The captured binding is a loop-body local: its (single)
                // incarnation is a shared cell allocated inside a loop body, so
                // each iteration re-allocates a fresh cell.
                boolean captured = false;
                for (SemanticOp closure : ofKind(unit, SemanticOpKind.CLOSURE_NEW)) {
                    KindPayload.ClosureNewPayload payload =
                        (KindPayload.ClosureNewPayload) closure.payload();
                    for (BindingGeneration capture : payload.captures()) {
                        Incarnation incarnation = incarnation(incarnations,
                            capture.binding(), capture.generation());
                        if (incarnation != null
                                && incarnation.kind() == BindingCellKind.SHARED_CELL
                                && insideLoopBody(unit, incarnation.scope())) {
                            captured = true;
                        }
                    }
                }
                check(captured, corpusCase.relativePath() + ": the fixture captures a "
                    + "loop-body local whose shared cell is allocated per iteration");
            }
        }
    }

    /** True iff one closure of the unit captures the binding at the generation. */
    private static boolean isCapturedAt(LoweredModuleUnit unit, BindingId binding,
            long generation) {
        for (SemanticOp closure : ofKind(unit, SemanticOpKind.CLOSURE_NEW)) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) closure.payload();
            for (BindingGeneration capture : payload.captures()) {
                if (capture.binding().equals(binding)
                        && capture.generation() == generation) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The emitted artifacts pass the creation-site cell and read the parameter. */
    private static void checkEmittedCapture(Case corpusCase,
            KindPayload.ClosureNewPayload payload, String lua, String jvm) {
        if (lua != null) {
            StringBuilder args = new StringBuilder();
            for (BindingGeneration capture : payload.captures()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append("S.b").append(capture.binding().id())
                    .append("g").append(capture.generation());
            }
            check(lua.contains("F" + payload.function().id() + "(" + args + ")"),
                corpusCase.relativePath() + ": the LuaJIT creation of "
                    + payload.function() + " passes the creation-site capture cells ("
                    + args + ")");
            for (BindingGeneration capture : payload.captures()) {
                check(lua.contains("c" + capture.binding().id() + "[1]"),
                    corpusCase.relativePath() + ": the LuaJIT factory of "
                        + payload.function() + " reads its capture parameter c"
                        + capture.binding().id());
            }
        }
        if (jvm != null) {
            StringBuilder jvmArgs = new StringBuilder();
            for (BindingGeneration capture : payload.captures()) {
                if (jvmArgs.length() > 0) {
                    jvmArgs.append(", ");
                }
                jvmArgs.append("b").append(capture.binding().id())
                    .append("g").append(capture.generation());
            }
            check(jvm.contains("F" + payload.function().id() + "(" + jvmArgs + ")"),
                corpusCase.relativePath() + ": the JVM creation of "
                    + payload.function() + " passes the creation-site capture cells ("
                    + jvmArgs + ")");
            for (BindingGeneration capture : payload.captures()) {
                check(jvm.contains("Object c" + capture.binding().id()),
                    corpusCase.relativePath() + ": the JVM factory declares the "
                        + "capture parameter c" + capture.binding().id());
                check(jvm.contains("((Object[]) c" + capture.binding().id() + ")[0]"),
                    corpusCase.relativePath() + ": the JVM factory of "
                        + payload.function() + " reads its capture parameter c"
                        + capture.binding().id());
            }
        }
    }

    // =========================================================================
    // 5. The fail-closed arms
    // =========================================================================

    private static void testCaptureResolutionNegatives() throws Exception {
        System.out.println("-- the fail-closed capture arms: a non-dominating "
            + "incarnation and a missing registration --");
        Case corpusCase = CASES.get(0);
        EntryDrive entry = entryDrive(corpusCase, Backend.LUAJIT);
        if (entry == null) {
            return;
        }
        try {
            LoweredModuleUnit unit = entry.drive().unit();
            StructuredBodyTable table = entry.drive().table();
            SemanticOp closure = null;
            for (SemanticOp candidate : ofKind(unit, SemanticOpKind.CLOSURE_NEW)) {
                if (candidate.payload() instanceof KindPayload.ClosureNewPayload payload
                        && !payload.captures().isEmpty()) {
                    closure = candidate;
                    break;
                }
            }
            check(closure != null, "the for-of fixture carries a capturing closure");
            if (closure == null) {
                return;
            }
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) closure.payload();
            BindingGeneration capture = payload.captures().get(0);

            // (a) The capture entry names a generation the creation site never
            //     resolves: the capture does not name the creating incarnation.
            BindingGeneration wrong = new BindingGeneration(capture.binding(),
                capture.generation() + 7);
            checkFailure(corpusCase.relativePath(),
                doctored(unit, closure, payload,
                    new KindPayload.ClosureNewPayload(payload.function(),
                        payload.signature(), List.of(wrong), payload.binding()),
                    List.of(wrong)),
                table, capture, payload.function(), true);

            // (b) The capture entry is removed: the detached body's reference
            //     stays outside the captures list.
            checkFailure(corpusCase.relativePath(),
                doctored(unit, closure, payload,
                    new KindPayload.ClosureNewPayload(payload.function(),
                        payload.signature(), List.of(), payload.binding()),
                    List.of()),
                table, capture, payload.function(), false);
        } finally {
            deleteRecursively(entry.root());
        }
    }

    /** One unit with the closure payload (and its function record) doctored. */
    private static LoweredModuleUnit doctored(LoweredModuleUnit unit,
            SemanticOp closure,
            KindPayload.ClosureNewPayload original,
            KindPayload.ClosureNewPayload replaced,
            List<BindingGeneration> captures) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (!op.opId().equals(closure.opId())) {
                ops.add(op);
                continue;
            }
            OperationContractSnapshot old = op.contract();
            OperationContractSnapshot rewired = new OperationContractSnapshot(
                old.version(), old.opKind(), old.resultType(), old.operandTypes(),
                old.selector(), replaced, old.failurePolicy(),
                old.referencedSemanticIds(), old.canonicalDigest());
            ops.add(new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
                op.resultType(), op.operands(), op.operandTypes(), replaced,
                op.failurePolicy(), rewired));
        }
        Map<FunctionId, LoweredFunction> functions =
            new LinkedHashMap<>(unit.functions());
        functions.put(original.function(), new LoweredFunction(original.function(),
            original.signature(), captures, original.binding().blockId()));
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            functions, unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    private static void checkFailure(String what, LoweredModuleUnit unit,
            StructuredBodyTable table, BindingGeneration capture, FunctionId function,
            boolean generationMismatch) {
        Optional<CompilerDiagnostic> failure =
            BindingsProductionValidator.validate(unit, table);
        check(failure.isPresent(), what + ": the doctored capture fails closed");
        if (failure.isEmpty()) {
            return;
        }
        String message = failure.get().message();
        check(message.contains(BindingsProductionValidator.CAPTURE_RESOLUTION),
            what + ": the doctored capture carries the landed CAPTURE_RESOLUTION rule: "
                + message);
        check(message.contains(capture.binding().toString()),
            what + ": the CAPTURE_RESOLUTION detail names the binding "
                + capture.binding() + ": " + message);
        check(message.contains(function.toString()),
            what + ": the CAPTURE_RESOLUTION detail names the function " + function
                + ": " + message);
        if (generationMismatch) {
            check(message.contains("does not name the creating incarnation")
                    || message.contains("names generation"),
                what + ": the generation-mismatched capture names the offending "
                    + "generation: " + message);
        } else {
            check(message.contains("outside the captures"),
                what + ": the missing registration is the outside-the-captures "
                    + "defect: " + message);
        }
    }

    // =========================================================================
    // 6. The alias cell discipline
    // =========================================================================

    private static final String ALIAS_SOURCE = """
        export function test(): int {
          let x: int = 1;
          let read: () => int = function(): int { return x; };
          let write: () => int = function(): int { x = x + 1; return x; };
          let total: int = write() + read() + write() + read();
          if (total !== 10) {
            throw { code: "TEST_FAIL", message: "alias cell commit" };
          }
          return total;
        }

        export function main(): null {
          let r: int = test();
          return null;
        }
        """;

    private static void testAliasInPlaceCommit() throws Exception {
        System.out.println("-- an alias of a captured cell observes the in-place "
            + "commit --");
        Path root = Files.createTempDirectory("closure-capture-alias-");
        try {
            writeFile(root, "src/app.deal", ALIAS_SOURCE);
            Drive drive = lower(root);
            if (drive == null) {
                return;
            }
            Path workspace = Files.createTempDirectory("closure-capture-alias-ws-");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(drive.project(),
                        drive.tables(), drive.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "the alias cell drive", List.of(), "null"), workspace);
                check(verdict.pass(), "the alias cell drive passes event-for-event "
                    + "(the write closure's commit is observed by the read closure): "
                    + verdict.failures());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(drive.root());
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 7. The SHARED_CELL adapter inside a per-iteration capturing closure
    // =========================================================================

    /**
     * The review regression: a per-iteration loop-body function binding
     * captured by a detached body, an arity adapter ({@code SHARED_CELL})
     * created inside that body over the captured binding, and three closures
     * created in different iterations whose adapter invocations must observe
     * their own creation-site incarnation. The drive pins the per-iteration
     * values ({@code 0}/{@code 1}/{@code 2}) through the program's own guard,
     * so a regression to the class-scoped slot read for the adapter source
     * fails the guard under the oracle and both real toolchains.
     */
    private static final String ADAPTER_CAPTURE_SOURCE = """
        export function test(): int {
          let fs: (() => int)[] = [function(): int { return -1; }, function(): int { return -1; }, function(): int { return -1; }];
          for (let i: int = 0; i < 3; i = i + 1) {
            let f: (a: int, b: int) => int = function(a: int, b: int): int { return -1; };
            f = function(a: int, b: int): int { return i; };
            fs[i] = function(): int {
              let g: (a: int, b: int, c: int) => int = f;
              return g(0, 0, 0);
            };
          }
          if (fs[0]() !== 0 || fs[1]() !== 1 || fs[2]() !== 2) {
            throw { code: "TEST_FAIL", message: "the per-iteration adapter observes its creation-site incarnation" };
          }
          return fs[0]() + fs[1]() + fs[2]();
        }

        export function main(): null {
          let r: int = test();
          return null;
        }
        """;

    private static void testSharedCellAdapterInsidePerIterationClosure()
            throws Exception {
        System.out.println("-- a SHARED_CELL adapter created inside a per-iteration "
            + "capturing closure reads its capture, never the module-global slot --");
        Path root = Files.createTempDirectory("closure-capture-adapter-");
        try {
            writeFile(root, "src/app.deal", ADAPTER_CAPTURE_SOURCE);

            // The one project lowering through the production invocation: the
            // LuaJIT compile stages the Lua artifact and the Lua toolchain
            // drive runs before the JVM compile (each publication replaces
            // the output root's staged set).
            Drive drive = lower(root);
            if (drive == null) {
                return;
            }
            String luaArtifact = readArtifact(root.resolve("out").resolve("app.lua"));
            check(luaArtifact != null,
                "the adapter drive stages the LuaJIT project artifact");
            if (luaArtifact != null) {
                writeFile(root.resolve("out"), "adapter_driver.lua", """
                    local surfaces = dofile("app.lua")
                    assert(type(surfaces) == "table",
                      "the production chunk returns the entry surface")
                    local probe = surfaces["test"]
                    assert(type(probe) == "table" and probe.__kind == "function"
                      and type(probe.f) == "function",
                      "the entry surface publishes the probe")
                    probe.f()
                    """);
                ProcessOutcome run = runProcess(List.of("luajit", "adapter_driver.lua"),
                    root.resolve("out"));
                checkEq(0, run.exitCode(), "the production LuaJIT artifact executes the "
                    + "per-iteration adapter guard with exit 0: " + run.output());
            }

            // The JVM compile of the identical source, then the JVM toolchain.
            CompilationOrchestrator jvm = productionCompile(root.resolve("src"),
                root.resolve("src/app.deal"), Backend.JVM);
            check(jvm.diagnostics().isEmpty(),
                "the adapter drive compiles on the JVM target with zero diagnostics: "
                    + jvm.diagnostics());
            check(jvm.semanticEmissionCount() == 1 && jvm.retainedEmissionCount() == 0,
                "the adapter drive emits one project artifact and no retained "
                    + "emission: semantic=" + jvm.semanticEmissionCount()
                    + " retained=" + jvm.retainedEmissionCount());
            String jvmArtifact = readArtifact(root.resolve("out")
                .resolve(JvmBackend.classNameFor("app") + ".java"));
            check(jvmArtifact != null,
                "the adapter drive stages the JVM project artifact");
            if (jvmArtifact != null) {
                Path classes = root.resolve("classes");
                Files.createDirectories(classes);
                writeFile(root, "out/AdapterProbe.java", """
                    public final class AdapterProbe {
                      public static void main(String[] args) {
                        %s.main(new String[0]);
                        deal.codegen.jvm.JvmRuntime.Table surface =
                            %s.EXPORT_SURFACES.get("app");
                        Object probe = surface.read("test");
                        if (!(probe instanceof deal.codegen.jvm.JvmRuntime.FunctionValue fn)) {
                          throw new IllegalStateException(
                              "the entry surface publishes the probe");
                        }
                        fn.fn.invoke(new Object[0]);
                      }
                    }
                    """.formatted(JvmBackend.classNameFor("app"),
                    JvmBackend.classNameFor("app")));
                ProcessOutcome javac = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", absoluteClasspath(), "-d", classes.toString(),
                    root.resolve("out").resolve(
                        JvmBackend.classNameFor("app") + ".java").toAbsolutePath()
                        .toString(),
                    root.resolve("out/AdapterProbe.java").toAbsolutePath().toString()),
                    root.resolve("out"));
                checkEq(0, javac.exitCode(), "the production JVM artifact compiles: "
                    + javac.output());
                if (javac.exitCode() == 0) {
                    ProcessOutcome run = runProcess(List.of("java", "-cp",
                        absoluteClasspath() + File.pathSeparator + classes,
                        "AdapterProbe"), root.resolve("out"));
                    checkEq(0, run.exitCode(), "the production JVM artifact executes "
                        + "the per-iteration adapter guard with exit 0: " + run.output());
                }
            }

            List<SemanticOp> adapters = new ArrayList<>();
            for (SemanticOp op : drive.unit().ops()) {
                if (op.payload() instanceof KindPayload.FunctionAdaptPayload payload
                        && payload.mode() == CaptureMode.SHARED_CELL
                        && payload.source() instanceof AdaptSourceRef.SharedCell) {
                    adapters.add(op);
                }
            }
            check(!adapters.isEmpty(), "the drive lowers a SHARED_CELL function "
                + "adapter over a captured binding");

            int insideCapturingFactory = 0;
            for (SemanticOp adapter : adapters) {
                KindPayload.FunctionAdaptPayload payload =
                    (KindPayload.FunctionAdaptPayload) adapter.payload();
                AdaptSourceRef.SharedCell cell =
                    (AdaptSourceRef.SharedCell) payload.source();
                LoweredFunction enclosing = enclosingFunction(drive.unit(),
                    drive.table(), adapter.opId());
                check(enclosing != null, adapter.opId()
                    + ": the adapter sits inside a lowered function body");
                BindingGeneration capture = enclosing == null ? null
                    : enclosing.captureOf(cell.binding());
                check(capture != null, adapter.opId() + ": the enclosing factory "
                    + enclosing + " captures the adapter source " + cell.binding()
                    + " (the factory's capture parameter is the body's source)");
                if (capture == null) {
                    continue;
                }
                insideCapturingFactory++;
                checkEq(cell.generation(), capture.generation(), adapter.opId()
                    + ": the enclosing factory's capture of " + cell.binding()
                    + " names the adapter source's creation-site incarnation");

                // (a) LuaJIT: the adapter creation records the factory's
                //     capture parameter as its cell.
                String luaLine = lineContaining(luaArtifact,
                    "S.v" + valueIdOf(adapter) + " = {__mode = 1,");
                check(luaLine != null && luaLine.contains("__cell = c"
                        + cell.binding().id()), adapter.opId() + ": the LuaJIT "
                    + "adapter creation records the capture parameter c"
                    + cell.binding().id() + " as its cell: " + luaLine);

                // (b) JVM: the adapter creation passes the factory's capture
                //     parameter and never the class-scoped slot.
                String jvmLine = lineContaining(jvmArtifact,
                    "v" + valueIdOf(adapter) + " = new JvmRuntime.AdapterValue(");
                check(jvmLine != null && jvmLine.contains("(Object[]) c"
                        + cell.binding().id()), adapter.opId() + ": the JVM adapter "
                    + "creation passes the capture parameter c" + cell.binding().id()
                    + " as its cell: " + jvmLine);
                check(jvmLine != null && !jvmLine.contains("b" + cell.binding().id()
                        + "g" + cell.generation()), adapter.opId() + ": the JVM "
                    + "adapter creation never reads the class-scoped slot b"
                    + cell.binding().id() + "g" + cell.generation() + ": " + jvmLine);
                check(jvmArtifact != null && jvmArtifact.contains("Object c"
                        + cell.binding().id()), adapter.opId() + ": the JVM "
                    + "factory declares the capture parameter c"
                    + cell.binding().id());
            }
            check(insideCapturingFactory > 0, "at least one SHARED_CELL adapter is "
                + "created inside a factory that captures its source binding");

            // The pinned per-iteration values through the oracle and both
            // shared emitters (the program's own guard is the assertion).
            Path workspace = Files.createTempDirectory("closure-capture-adapter-ws-");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(drive.project(),
                        drive.tables(), drive.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "the per-iteration adapter drive", List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the adapter drive passes event-for-event "
                    + "(the per-iteration adapter observes its own incarnation): "
                    + verdict.failures());
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.Success,
                        run.consumer() + ": the adapter drive completes with the "
                            + "program's per-iteration guard: " + run.terminal());
                }
            } finally {
                deleteRecursively(workspace);
            }

        } finally {
            deleteRecursively(root);
        }
    }

    /** The result value id of an op, or {@code -1} when it produces none. */
    private static long valueIdOf(SemanticOp op) {
        return op.result() instanceof ValueId valueId ? valueId.id() : -1;
    }

    /** The first line of one artifact text containing the needle, or null. */
    private static String lineContaining(String text, String needle) {
        if (text == null) {
            return null;
        }
        for (String line : text.split("\n")) {
            if (line.contains(needle)) {
                return line;
            }
        }
        return null;
    }

    /** The lowered function whose body region owns one op, or null. */
    private static LoweredFunction enclosingFunction(LoweredModuleUnit unit,
            StructuredBodyTable table, OpId opId) {
        BlockId owner = null;
        for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
            if (entry.getValue().contains(opId)) {
                owner = entry.getKey();
                break;
            }
        }
        if (owner == null) {
            return null;
        }
        for (LoweredFunction function : unit.functions().values()) {
            if (regionBlocks(unit, table, function.body()).contains(owner)) {
                return function;
            }
        }
        return null;
    }

    /** The artifact text of one path, or null when the artifact is absent. */
    private static String readArtifact(Path artifact) throws Exception {
        return Files.exists(artifact)
            ? Files.readString(artifact, StandardCharsets.UTF_8) : null;
    }

    // =========================================================================
    // 8. Determinism
    // =========================================================================

    private static void testDeterminism() throws Exception {
        System.out.println("-- repeated lowering and emission are byte-identical --");
        for (Case corpusCase : CASES) {
            // Two compiles of the identical input under one root: the artifact
            // bytes (the embedded source origins included) must be identical.
            Path root = Files.createTempDirectory("closure-capture-determinism-");
            try {
                for (Backend backend : List.of(Backend.LUAJIT, Backend.JVM)) {
                    String first = compileArtifact(root, corpusCase, backend);
                    String second = compileArtifact(root, corpusCase, backend);
                    check(first != null && first.equals(second),
                        corpusCase.relativePath() + ": the repeated " + backend
                            + " emission is byte-identical");
                }
            } finally {
                deleteRecursively(root);
            }
        }
    }

    /** One compile's artifact text (the second compile overwrites the first). */
    private static String compileArtifact(Path root, Case corpusCase, Backend backend)
            throws Exception {
        Path src = root.resolve("src");
        writeFile(root, "src/" + corpusCase.relativePath() + ".deal",
            fixtureSource(corpusCase.relativePath()));
        Path entry = src.resolve(corpusCase.relativePath() + ".deal");
        CompilationOrchestrator orchestrator = productionCompile(src, entry, backend);
        check(orchestrator.diagnostics().isEmpty(), corpusCase.relativePath()
            + ": the " + backend + " determinism compile reports zero diagnostics: "
            + orchestrator.diagnostics());
        Path artifact = backend == Backend.JVM
            ? root.resolve("out").resolve(
                JvmBackend.classNameFor(corpusCase.relativePath()) + ".java")
            : root.resolve("out").resolve(corpusCase.relativePath() + ".lua");
        return Files.exists(artifact)
            ? Files.readString(artifact, StandardCharsets.UTF_8) : null;
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        testCorpusInventory();
        testProductionArtifacts();
        testDifferentialMatrix();
        testPerIterationStructure();
        testCaptureResolutionNegatives();
        testAliasInPlaceCommit();
        testSharedCellAdapterInsidePerIterationClosure();
        testDeterminism();
        System.out.println();
        System.out.println("Closure capture resolution: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
