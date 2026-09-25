package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmRuntime;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SemanticTraceProtocol;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.test.conformance.ErrorSnapshot;
import deal.test.conformance.SidecarExpectations;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;

/**
 * ISSUE-0652: the async host path through the operation handle (design
 * source {@code host-module-load-and-host-call-realization} H4 and the
 * async host start and completion contract;
 * {@code semantic-ir-construct-coverage-cutover} K4;
 * {@code luajit-jvm-single-lowering-production-cutover} C2).
 *
 * <ol>
 *   <li><b>The LuaJIT arm.</b> {@code ASYNC_START(HOST)} invokes the loaded
 *       surface entry through the same host-boundary call shape as the
 *       sync arm ({@code <entry>.f(args..., file, line, column)}): the
 *       loaded wrapper's declared-async shape check realizes the op's
 *       {@code ASYNC_OPERATION_HANDLE} terminal with the pinned E8010 at
 *       the call origin, and the returned operation handle is bound to the
 *       canonical token ({@code __asyncStartHost(tokenId, label,
 *       handle)}). {@code AWAIT} drives a handle-carrying record through
 *       the landed {@code __rt.async_step} machinery — the operation's own
 *       DEAL failure becomes the task's failure identical, a non-DEAL
 *       failure rethrows as infrastructure — while a seam-registered
 *       record keeps the landed {@code __callbacks.__hostCompleteAsync}
 *       path. The production {@code ASYNC_START} site references no
 *       {@code __callbacks.__hostStartAsync}.</li>
 *   <li><b>The JVM arm.</b> The same start invokes the emitted per-export
 *       wrapper with the call origin triple; the wrapper's declared-async
 *       branch runs the shape check (the pinned E8010 at the call origin)
 *       and returns the host operation handle instead of joining it. The
 *       handle is bound through the production
 *       {@code JvmRuntime.startHostTask(tokenId, label, operation)}
 *       registration, and {@code awaitTask} joins that registered
 *       operation (never reading {@code JvmRuntime.HOST_ASYNC}) with the
 *       identical-error discipline.</li>
 *   <li><b>Pinned corpus outcomes.</b> The three admitted async host
 *       fixtures ({@code host-async-ok}, {@code host-async-shape-bad},
 *       {@code host-async-bad}) compile through the production emission
 *       and execute under {@code luajit} and {@code java} with the
 *       sidecar-pinned code, message, origin, expected, and actual: the
 *       completion cell ({@code host-async-bad}) reproduces the pinned
 *       corpus projection {@code expected string} / {@code actual number}
 *       at the await origin on both targets and in the oracle, and the
 *       executed error snapshot equals the sidecar's.</li>
 *   <li><b>A pending operation and the poisoned seams.</b> A host
 *       operation that is still pending when {@code ASYNC_START} returns
 *       (LuaJIT {@code __rt.async_create}; JVM a future completed on
 *       another thread during the {@code AWAIT}) completes with the
 *       declared value while the deterministic seams stay poisoned (the
 *       LuaJIT seam helpers are their raising defaults; a JVM seam that
 *       throws on any completion attempt is installed), and the same run
 *       loads the host module once and runs a sync host call beside the
 *       async one.</li>
 *   <li><b>The single completion boundary.</b> The completion value
 *       crosses the {@code ASYNC_COMPLETION} boundary exactly once at the
 *       await origin; a mismatch is re-originated at that origin and
 *       publishes the boundary's FAILURE beside the await op's, exactly
 *       the oracle's boundary-child pair.</li>
 *   <li><b>Fail-closed seeds.</b> A bad async operation shape (the pinned
 *       E8010 at the call expression), an operation failing with a DEAL
 *       error (the identical error surfaces, its own origin intact), and a
 *       call of an unloaded surface each fail closed.</li>
 *   <li><b>The trace-mode oracle agreement.</b> A combined drive project
 *       (one host load, a sync host call, an async host start and its
 *       await) runs through the oracle and both trace-mode artifacts with
 *       the same events and the same async terminals.</li>
 * </ol>
 */
public class AsyncHostRealizationTest {

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
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    public static void main(String[] args) throws Exception {
        testLuaFixtureSet();
        testJvmFixtureSet();
        testOracleOutcomes();
        testPendingOperationDrive();
        testArtifactTextNoSeam();
        testAwaitTaskProductionBranch();
        testTraceOracleAgreement();
        testFailClosedSeeds();
        System.out.println();
        System.out.println("passes: " + passed + ", failures: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }

    // =========================================================================
    // Fixtures: the corpus async host set
    // =========================================================================

    /** One admitted async host fixture: the corpus path and the host stem. */
    private record AsyncFixture(String name, String hostStem, String hostSpecifier) {

        String corpusFixture() {
            return "test/conformance/backend-runtime/host-abi/" + name + ".deal";
        }

        String corpusHost() {
            return "test/conformance/host-fixtures/" + hostStem;
        }

        String corpusSidecar() {
            return "test/conformance/backend-runtime/host-abi/" + name
                + ".expect.json";
        }
    }

    /**
     * The admitted async host fixture set of this slice: the three fixtures
     * whose declared map, loaded surface, and operation-handle path the async
     * arms realize. The three byte-value fixtures and the value-position read
     * form ({@code host-async-shape-value}) are sibling children's and are not
     * claimed here.
     */
    private static final List<String> ASYNC_FIXTURES = List.of(
        "host-async-ok",
        "host-async-shape-bad",
        "host-async-bad");

    /** The host declaration of one admitted fixture (its own raw specifier). */
    private static AsyncFixture asyncFixture(String name) throws Exception {
        String source = Files.readString(
            Path.of("test/conformance/backend-runtime/host-abi/" + name + ".deal"),
            StandardCharsets.UTF_8);
        int at = source.indexOf("from \"host/");
        if (at < 0) {
            throw new IllegalStateException("the fixture '" + name
                + "' carries no host import");
        }
        int start = at + "from \"".length();
        int end = source.indexOf('"', start);
        String specifier = source.substring(start, end);
        return new AsyncFixture(name, specifier.substring("host/".length()), specifier);
    }

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        String entryPath,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        Map<String, String> externals,
        int headerLinesStripped) {
    }

    private record Outcome(int exitCode, String stdout, String stderr, String value) {
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32,
            deal.semantic.ir.ReleaseState.V1_2_ACTIVE,
            deal.semantic.CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            deal.semantic.ReleaseConfiguration.CURRENT_RELEASE_STATE,
            deal.semantic.ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compile(AsyncFixture fixture) throws Exception {
        return compileWith(fixture.name(), fixture.hostStem(),
            ConformanceHarnessMetadata.stripClassificationHeaders(Files.readString(
                Path.of(fixture.corpusHost() + ".d.deal"), StandardCharsets.UTF_8)),
            Files.readString(Path.of(fixture.corpusFixture()), StandardCharsets.UTF_8));
    }

    /** One synthetic fixture: a host stem, the declaration text, and the app source. */
    private static Fixture compileSource(String name, String hostStem,
            String declarationSource, String appSource) throws Exception {
        return compileWith(name, hostStem, declarationSource, appSource);
    }

    private static Fixture compileWith(String name, String hostStem,
            String declarationSource, String rawApp) throws Exception {
        String hostSpecifier = "host/" + hostStem;
        String appSource = ConformanceHarnessMetadata.stripClassificationHeaders(rawApp);
        int headerLinesStripped = rawApp.split("\n", -1).length
            - appSource.split("\n", -1).length;
        Path root = Files.createTempDirectory("async-host-fixture");
        Path src = root.resolve("src");
        writeFileIn(root, "src/" + hostStem + ".d.deal",
            ConformanceHarnessMetadata.stripClassificationHeaders(declarationSource));
        writeFileIn(root, "src/" + name + ".deal", appSource);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(hostSpecifier, root.resolve("src/" + hostStem + ".d.deal")
            .toAbsolutePath().toString());
        Path entry = src.resolve(name + ".deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, externals,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the async host fixture '" + name
                + "' did not build: " + detail + " / " + orchestrator.diagnostics());
        }
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(hostSpecifier));
        }
        String entryPath = null;
        for (ModuleId module : built.input().modules().stream()
                .map(module -> module.moduleId()).toList()) {
            if (module.path().endsWith(name)) {
                entryPath = module.path();
            }
        }
        if (entryPath == null) {
            throw new IllegalStateException("the entry module path is not derived");
        }
        return new Fixture(root, entryPath, built.input(), built.index(),
            manifests.manifests(), surface, identities, externals,
            headerLinesStripped);
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** The single host import of the lowered project. */
    private static ModuleId hostImportModule(ExecutableLoweredProject project) {
        for (ModuleId module : project.modules().keySet()) {
            for (SemanticOp op : project.modules().get(module).ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT
                        && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                            == ModuleImportKind.HOST) {
                    return ((KindPayload.ModuleImportPayload) op.payload())
                        .resolvedModule();
                }
            }
        }
        throw new IllegalStateException("the fixture carries no host import");
    }

    /** The async EXTERNAL_ENTRY op of one module's export, or null. */
    private static SemanticOp asyncEntryOf(ExecutableLoweredProject project,
            ModuleId module, String exportName) {
        LoweredModuleUnit unit = project.modules().get(module);
        if (unit == null) {
            return null;
        }
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY) {
                KindPayload.ExternalEntryPayload payload =
                    (KindPayload.ExternalEntryPayload) op.payload();
                if (payload.async() && payload.exportName().equals(exportName)) {
                    return op;
                }
            }
        }
        return null;
    }

    // =========================================================================
    // 1. The LuaJIT fixture set under real luajit
    // =========================================================================

    private static void testLuaFixtureSet() throws Exception {
        System.out.println("-- the async host fixture set under luajit (production "
            + "emission, pinned outcomes) --");
        for (String name : ASYNC_FIXTURES) {
            AsyncFixture fixture = asyncFixture(name);
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("async-host-lua");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + name + "' lowers: " + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                Path artifact = workspace.resolve("project.lua");
                Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                    project, result.tables(), result.registries(), compiled.surface()),
                    StandardCharsets.UTF_8);
                deployRuntime(workspace);
                deployHostLua(workspace, fixture);
                Path probe = workspace.resolve("probe.lua");
                Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome outcome = runLua(probe, workspace);
                checkFixtureOutcome(name, outcome, "luajit",
                    compiled.headerLinesStripped());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
    }

    private static void testJvmFixtureSet() throws Exception {
        System.out.println("-- the async host fixture set under javac + java (production "
            + "emission, pinned outcomes) --");
        for (String name : ASYNC_FIXTURES) {
            AsyncFixture fixture = asyncFixture(name);
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("async-host-jvm");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + name + "' lowers: " + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                String className = JvmBackend.classNameFor(project.entryModule().path());
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                        result.registries(), className, compiled.surface());
                Files.writeString(workspace.resolve(className + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("AsyncHostProbe.java"),
                    jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
                String hostSource = Files.readString(
                    Path.of(fixture.corpusHost() + ".java"), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve(
                    JvmBackend.classNameFor(fixture.hostSpecifier()) + ".java"),
                    hostSource, StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java",
                    JvmBackend.classNameFor(fixture.hostSpecifier()) + ".java",
                    "AsyncHostProbe.java"), workspace);
                check(javacRun.exitCode() == 0,
                    "the fixture '" + name + "' compiles under javac: "
                        + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() != 0) {
                    continue;
                }
                Outcome outcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "AsyncHostProbe"),
                    workspace);
                checkFixtureOutcome(name, outcome, "java",
                    compiled.headerLinesStripped());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
    }

    // =========================================================================
    // The sidecar pins
    // =========================================================================

    private record Expectation(String mode, String code, String message, String sourceFile,
                               int line, int column, String expected, String actual) {
    }

    /** The pinned expectation of one corpus sidecar (the authoritative record). */
    private static Expectation expectationOf(String name) throws Exception {
        String json = Files.readString(
            Path.of("test/conformance/backend-runtime/host-abi/" + name + ".expect.json"),
            StandardCharsets.UTF_8);
        String mode = field(json, "\"mode\"");
        String code = field(json, "\"code\"");
        String message = field(json, "\"message\"");
        int errorAt = json.indexOf("\"error\"");
        String errorBlock = errorAt < 0 ? "" : json.substring(errorAt);
        String sourceFile = field(errorBlock, "\"sourceFile\"");
        String expected = field(errorBlock, "\"expected\"");
        String actual = field(errorBlock, "\"actual\"");
        Integer line = number(json, "\"line\"");
        Integer column = number(json, "\"column\"");
        return new Expectation(mode, code, message, sourceFile,
            line == null ? -1 : line, column == null ? -1 : column, expected, actual);
    }

    private static String field(String json, String key) {
        int at = json.indexOf(key);
        if (at < 0) {
            return null;
        }
        int start = json.indexOf('"', json.indexOf(':', at) + 1);
        StringBuilder text = new StringBuilder();
        for (int i = start + 1; i < json.length(); i++) {
            char c = json.charAt(i);
            if (c == '\\' && i + 1 < json.length()) {
                char next = json.charAt(++i);
                switch (next) {
                    case 'n' -> text.append('\n');
                    case '"' -> text.append('"');
                    case '\\' -> text.append('\\');
                    default -> text.append(next);
                }
                continue;
            }
            if (c == '"') {
                break;
            }
            text.append(c);
        }
        return text.toString();
    }

    private static Integer number(String json, String key) {
        int at = json.indexOf(key);
        if (at < 0) {
            return null;
        }
        int start = json.indexOf(':', at) + 1;
        StringBuilder digits = new StringBuilder();
        for (int i = start; i < json.length(); i++) {
            char c = json.charAt(i);
            if (Character.isDigit(c) || (c == '-' && digits.length() == 0)) {
                digits.append(c);
            } else if (digits.length() > 0) {
                break;
            }
        }
        return digits.length() == 0 ? null : Integer.valueOf(digits.toString());
    }

    /**
     * Asserts one fixture run against its sidecar pin: a runtime-ok fixture
     * exits OK with no error; a runtime-error fixture reports every pinned
     * field — the code, the message, the origin line/column, and the
     * expected/actual pair — byte-exact, and the executed error snapshot
     * rendered from those fields equals the sidecar's pinned
     * {@code DEAL_ERROR_SNAPSHOT} transcript (the field set, order, and
     * canonical text; the span's own path is the temp layout's, so only its
     * pinned text is compared).
     */
    private static void checkFixtureOutcome(String name, Outcome outcome,
            String target, int headerLinesStripped) throws Exception {
        Expectation expectation = expectationOf(name);
        if ("runtime-ok".equals(expectation.mode())) {
            check(outcome.exitCode() == 0 && outcome.value().startsWith("OK"),
                "the " + target + " fixture '" + name + "' is runtime-ok: exit="
                    + outcome.exitCode() + " value=" + escaped(outcome.value())
                    + " stderr=" + escaped(outcome.stderr()));
            return;
        }
        check(outcome.value().startsWith("ERR:"),
            "the " + target + " fixture '" + name + "' raises the pinned error: value="
                + escaped(outcome.value()) + " stderr=" + escaped(outcome.stderr()));
        if (!outcome.value().startsWith("ERR:")) {
            return;
        }
        String[] parts = outcome.value().substring(4).split("\\|", -1);
        checkEq(expectation.code(), parts[0], name + " (" + target + ") pinned code");
        checkEq(expectation.message(), parts[1],
            name + " (" + target + ") pinned message");
        String origin = parts[2];
        int lastColon = origin.lastIndexOf(':');
        int prevColon = origin.lastIndexOf(':', lastColon - 1);
        int observedLine = Integer.valueOf(origin.substring(prevColon + 1, lastColon))
            + headerLinesStripped;
        int observedColumn = Integer.valueOf(origin.substring(lastColon + 1));
        checkEq(expectation.line(), observedLine,
            name + " (" + target + ") pinned origin line");
        checkEq(expectation.column(), observedColumn,
            name + " (" + target + ") pinned origin column");
        check(origin.substring(0, prevColon).endsWith(name + ".deal"),
            name + " (" + target + ") pinned origin file: " + origin);
        checkEq(expectation.expected(), "-".equals(parts[3]) ? null : parts[3],
            name + " (" + target + ") pinned expected");
        checkEq(expectation.actual(), "-".equals(parts[4]) ? null : parts[4],
            name + " (" + target + ") pinned actual");
        ARTIFACT_ERRORS.put(name, new String[] {parts[1], parts[4]});

        // The executed transcript equals the sidecar's pinned snapshot: every
        // field, its order, and the canonical rendering are the sidecar's.
        String observedFile = origin.substring(0, prevColon);
        SidecarExpectations.ErrorExpectation observed =
            new SidecarExpectations.ErrorExpectation(parts[0], parts[1], observedFile,
                observedLine, observedColumn,
                Optional.ofNullable("-".equals(parts[3]) ? null : parts[3]),
                Optional.ofNullable("-".equals(parts[4]) ? null : parts[4]),
                Optional.empty(), Optional.empty());
        checkEq(pinnedSnapshotJson(name, expectation.sourceFile(), observedFile),
            ErrorSnapshot.canonicalJson(observed),
            name + " (" + target + ") executed error snapshot equals the pinned "
                + "sidecar snapshot");
    }

    /**
     * The sidecar's pinned {@code DEAL_ERROR_SNAPSHOT} JSON of one fixture,
     * with its pinned source file replaced by the run's own (the temp layout's)
     * source path — every other field, its order, and its canonical rendering
     * stay the sidecar's.
     */
    private static String pinnedSnapshotJson(String name, String pinnedFile,
            String observedFile) throws Exception {
        String stdout = field(Files.readString(
            Path.of("test/conformance/backend-runtime/host-abi/" + name
                + ".expect.json"), StandardCharsets.UTF_8), "\"stdout\"");
        for (String line : stdout.split("\\n", -1)) {
            if (line.startsWith(ErrorSnapshot.SNAPSHOT_LINE_PREFIX)) {
                return line.substring(ErrorSnapshot.SNAPSHOT_LINE_PREFIX.length())
                    .replace("\"sourceFile\":\"" + pinnedFile + "\"",
                        "\"sourceFile\":\"" + observedFile + "\"");
            }
        }
        throw new IllegalStateException("the sidecar of '" + name
            + "' pins no DEAL_ERROR_SNAPSHOT line");
    }

    // =========================================================================
    // 2. The oracle outcomes
    // =========================================================================

    /**
     * The oracle's own realization of the three fixtures: the loaded surface
     * entry's declared-async shape check is the host seam's start terminal
     * (the {@code ASYNC_OPERATION_HANDLE} policy; a scripted bad handle
     * projects {@code async operation mismatch: expected async-operation, got
     * nothing} at the call origin), the completion is the seam's completion
     * terminal, and the single {@code ASYNC_COMPLETION} boundary runs at the
     * await origin. The recorded terminals are compared against both
     * artifacts by the drives below.
     */
    private static void testOracleOutcomes() throws Exception {
        System.out.println("-- the oracle's async host terminals (pinned code and "
            + "origin; the shared completion-cell projection) --");
        for (String name : ASYNC_FIXTURES) {
            AsyncFixture fixture = asyncFixture(name);
            Fixture compiled = compile(fixture);
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the oracle fixture '" + name + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                SemanticOracle.HostResponder responder = responderFor(name,
                    fixture.hostStem());
                SemanticRuntimeModel.ConsumerRun run = SemanticOracle.invokeAsyncEntry(
                    result.project(), result.tables(), responder,
                    result.project().entryModule(),
                    exportNameOf(ConformanceHarnessMetadata.stripClassificationHeaders(
                        Files.readString(Path.of(fixture.corpusFixture()),
                            StandardCharsets.UTF_8))),
                    List.of());
                Expectation expectation = expectationOf(name);
                if ("runtime-ok".equals(expectation.mode())) {
                    check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                        "the oracle fixture '" + name + "' succeeds: "
                            + terminalText(run.terminal()));
                    checkEq("str:fetched", terminalAtom(run.terminal()),
                        name + " (oracle) completion atom");
                    continue;
                }
                check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure,
                    "the oracle fixture '" + name + "' fails: "
                        + terminalText(run.terminal()));
                if (!(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure failure)) {
                    continue;
                }
                SemanticRuntimeModel.ErrorSnapshot error = failure.error();
                checkEq(expectation.code(), error.code(),
                    name + " (oracle) pinned code");
                String origin = error.origin();
                int lastColon = origin.lastIndexOf(':');
                int prevColon = origin.lastIndexOf(':', lastColon - 1);
                checkEq(expectation.line(),
                    Integer.valueOf(origin.substring(prevColon + 1, lastColon))
                        + compiled.headerLinesStripped(),
                    name + " (oracle) pinned origin line");
                checkEq(expectation.column(),
                    Integer.valueOf(origin.substring(lastColon + 1)),
                    name + " (oracle) pinned origin column");
                OpId completionBoundary = completionBoundaryOf(result.project());
                boolean completionStarted = run.trace().stream().anyMatch(event ->
                    event.kind() == SemanticOpKind.BOUNDARY
                        && event.phase() == SemanticRuntimeModel.Phase.START
                        && event.op().equals(completionBoundary));
                boolean completionFailed = run.trace().stream().anyMatch(event ->
                    event.kind() == SemanticOpKind.BOUNDARY
                        && event.phase() == SemanticRuntimeModel.Phase.FAILURE
                        && event.op().equals(completionBoundary));
                if ("host-async-bad".equals(name)) {
                    check(completionStarted && completionFailed,
                        "the oracle's completion cell fails at the await site (the "
                            + "single ASYNC_COMPLETION boundary): "
                            + terminalText(run.terminal()));
                    // The completion cell reproduces the pinned corpus
                    // projection: message "expected string", expected
                    // "string", actual "number" (the completion value is an
                    // integral host number; the cell's numeric carrier is the
                    // single number kind).
                    checkEq(expectation.message(), error.message(),
                        name + " (oracle) pinned message");
                    checkEq(expectation.expected(), error.expected(),
                        name + " (oracle) pinned expected");
                    checkEq(expectation.actual(), error.actual(),
                        name + " (oracle) pinned actual");
                    String[] artifacts = ARTIFACT_ERRORS.get(name);
                    check(artifacts != null,
                        "the " + name + " artifact drives recorded their projection");
                    if (artifacts != null) {
                        checkEq(error.message(), artifacts[0],
                            name + " completion-cell message parity (oracle vs artifacts)");
                        checkEq(error.actual(),
                            "-".equals(artifacts[1]) ? null : artifacts[1],
                            name + " completion-cell actual parity (oracle vs artifacts)");
                    }
                } else {
                    // The declared-async shape check is the start terminal: the
                    // completion boundary is never reached.
                    check(!completionStarted,
                        "the oracle's bad-handle start terminal fails before the "
                            + "completion boundary: " + terminalText(run.terminal()));
                    boolean startFailed = run.trace().stream().anyMatch(event ->
                        event.kind() == SemanticOpKind.ASYNC_START
                            && event.phase() == SemanticRuntimeModel.Phase.FAILURE);
                    check(startFailed,
                        "the oracle's ASYNC_START op publishes the shape-check "
                            + "failure: " + terminalText(run.terminal()));
                }
            } finally {
                deleteRecursively(compiled.root());
            }
        }
    }

    /** The test export name of one app source (its single {@code test_*} function). */
    private static String exportNameOf(String appSource) {
        int at = appSource.indexOf("function test_");
        if (at < 0) {
            throw new IllegalStateException("the drive source carries no test export");
        }
        int nameStart = at + "function ".length();
        return appSource.substring(nameStart, appSource.indexOf('(', nameStart));
    }

    /**
     * The scripted host seam of one fixture: the deployed host's own behavior
     * (a real operation for {@code host-async-ok}, a completion value that
     * violates the declared return for {@code host-async-bad}, a bad handle
     * for {@code host-async-shape-bad}).
     */
    private static SemanticOracle.HostResponder responderFor(String name,
            String hostStem) {
        return new SemanticOracle.HostResponder() {
            @Override
            public String startAsync(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args, String operationLabel) {
                if ("host-async-shape-bad".equals(name)) {
                    return null; // the scripted non-operation handle
                }
                return operationLabel;
            }

            @Override
            public SyncOutcome completeAsync(String operationLabel) {
                if ("host-async-bad".equals(name)) {
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(42));
                }
                return new SyncOutcome.Returned(
                    new SemanticOracle.Value.StrValue("fetched"));
            }
        };
    }

    /** The single ASYNC_COMPLETION boundary op of the closure, or null. */
    private static OpId completionBoundaryOf(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && op.payload() instanceof KindPayload.BoundaryPayload payload
                        && payload.kind() == deal.semantic.ir.BoundaryKind.ASYNC_COMPLETION) {
                    return op.opId();
                }
            }
        }
        return null;
    }

    private static String terminalAtom(SemanticRuntimeModel.Terminal terminal) {
        return terminal instanceof SemanticRuntimeModel.Terminal.Success success
            ? success.resultAtom() : "-";
    }

    private static String terminalText(SemanticRuntimeModel.Terminal terminal) {
        return switch (terminal) {
            case SemanticRuntimeModel.Terminal.Success success ->
                "success:" + success.resultAtom();
            case SemanticRuntimeModel.Terminal.DealFailure failure -> {
                SemanticRuntimeModel.ErrorSnapshot error = failure.error();
                yield "failure:" + error.code() + "|" + error.message() + "|"
                    + error.origin() + "|" + error.expected() + "|" + error.actual();
            }
        };
    }

    // =========================================================================
    // 3. The pending-operation drive (seams poisoned) and the joint load/sync call
    // =========================================================================

    private static final String PENDING_DECLARATION = """
        export function ping(): string;
        export function sum(a: int, b: int): int;
        export async function fetchValue(): string;
        """;

    /**
     * The pending drive project: two aliases of one host module (one load per
     * program), a sync host call, and an async host start whose operation is
     * still pending when {@code ASYNC_START} returns.
     */
    private static final String PENDING_SOURCE = """
        import * as first from "host/pending_op"
        import * as second from "host/pending_op"

        export async function test_pending_op(): string {
          let a: string = first.ping();
          let b: string = second.ping();
          let total: int = first.sum(20, 22);
          let fetched: string = await second.fetchValue();
          if (a !== "pong" || b !== "pong" || total !== 42 || fetched !== "fetched") {
            throw { code: "TEST_FAIL", message: "pending async drive mismatch" };
          }
          return fetched;
        }

        export function main(): null {
          return null;
        }
        """;

    /** The deployed Lua host: the operation is created but not yet stepped. */
    private static final String PENDING_HOST_LUA = """
        local rt = require("deal.runtime")
        _PENDING_LOADS = (_PENDING_LOADS or 0) + 1
        return {
          ping = function() return "pong" end,
          sum = function(a, b) return a + b end,
          fetchValue = function()
            local handle = rt.async_create(function() return "fetched" end)
            io.stderr:write("HOST_PENDING_AT_START="
              .. tostring(handle.__done ~= true) .. "\\n")
            return handle
          end,
        }
        """;

    /** The deployed JVM host: the completion arrives on another thread. */
    private static final String PENDING_HOST_JAVA = """
        final class HostPending_op {
          public static java.lang.String ping() {
            return "pong";
          }

          public static int sum(int a, int b) {
            return a + b;
          }

          public static java.lang.Object fetchValue() {
            java.util.concurrent.CompletableFuture<java.lang.Object> pending =
                new java.util.concurrent.CompletableFuture<>();
            java.lang.System.err.println("HOST_PENDING_AT_START="
                + !pending.isDone());
            java.lang.Thread completer = new java.lang.Thread(() -> {
              try {
                java.lang.Thread.sleep(50L);
              } catch (java.lang.InterruptedException interrupted) {
                java.lang.Thread.currentThread().interrupt();
              }
              pending.complete("fetched");
            });
            completer.setDaemon(true);
            completer.start();
            return pending;
          }
        }
        """;

    private static void testPendingOperationDrive() throws Exception {
        System.out.println("-- the pending-operation drive: one load, a sync host call, "
            + "and an async start still pending at AWAIT, with the seams poisoned --");
        Fixture compiled = compileSource("host-pending-op", "pending_op",
            PENDING_DECLARATION, PENDING_SOURCE);
        Path workspace = Files.createTempDirectory("async-host-pending");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the pending drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();

            // (a) The LuaJIT artifact: the seam helpers keep their raising
            // defaults (never installed) and the load counter is asserted.
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path hostTarget = workspace.resolve("host/pending_op.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.writeString(hostTarget, PENDING_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaPendingDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(probe, workspace);
            check(luaOutcome.exitCode() == 0
                    && luaOutcome.value().startsWith("OK"),
                "the LuaJIT pending drive completes through the operation handle: "
                    + escaped(luaOutcome.value()) + " stderr="
                    + escaped(luaOutcome.stderr()));
            check(luaOutcome.stderr().contains("HOST_PENDING_AT_START=true"),
                "the LuaJIT host operation is still pending when ASYNC_START returns: "
                    + escaped(luaOutcome.stderr()));

            // (b) The JVM artifact: the production registered operation joins
            // while the seam field stays null.
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("AsyncHostProbe.java"),
                jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostPending_op.java"),
                PENDING_HOST_JAVA, StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostPending_op.java", "AsyncHostProbe.java"),
                workspace);
            check(javacRun.exitCode() == 0, "the pending drive compiles under javac: "
                + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "AsyncHostProbe"),
                    workspace);
                check(jvmOutcome.exitCode() == 0 && jvmOutcome.value().startsWith("OK"),
                    "the JVM pending drive completes through the registered operation "
                        + "with HOST_ASYNC null: exit=" + jvmOutcome.exitCode()
                        + " value=" + escaped(jvmOutcome.value()) + " stderr="
                        + escaped(jvmOutcome.stderr()));
                check(jvmOutcome.stderr().contains("HOST_PENDING_AT_START=true"),
                    "the JVM host operation is still pending when ASYNC_START returns: "
                        + escaped(jvmOutcome.stderr()));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** The LuaJIT pending drive: one load, both aliases' calls, the async await. */
    private static String luaPendingDriver(Path artifact, String entryPath) {
        return """
            local chunk = dofile("%s")
            local loads = 0
            local rt = require("deal.runtime")
            local realLoad = rt.load_host
            rt.load_host = function(...)
              loads = loads + 1
              return realLoad(...)
            end
            local ok, err = __dealMain()
            if not ok then print("ERR:INIT|-|-|-|-") os.exit(0) end
            local surface = __exportSurfaces["%s"]
            local ok2, err2 = pcall(surface["test_pending_op"].f)
            if not ok2 then
              if type(err2) == "table" and err2.__d then
                print("ERR:" .. err2.code .. "|" .. tostring(err2.m) .. "|"
                  .. tostring(err2.o) .. "|-|-")
              else
                print("ERR:E9999|" .. tostring(err2) .. "|-|-|-")
              end
              os.exit(0)
            end
            if loads ~= 1 then print("ERR:LOADS|" .. loads .. "|-|-|-") os.exit(0) end
            if (_PENDING_LOADS or 0) ~= 1 then
              print("ERR:HOSTLOADS|" .. tostring(_PENDING_LOADS) .. "|-|-|-") os.exit(0)
            end
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    // =========================================================================
    // 4. The artifact text: no seam on the production path
    // =========================================================================

    private static void testArtifactTextNoSeam() throws Exception {
        System.out.println("-- the production artifact text: the async host sites "
            + "reference the operation handle, never the deterministic seams --");
        AsyncFixture fixture = asyncFixture("host-async-ok");
        Fixture compiled = compile(fixture);
        Path workspace = Files.createTempDirectory("async-host-text");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the artifact-text fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), compiled.surface());
            check(!lua.contains("__callbacks.__hostStartAsync("),
                "the LuaJIT production chunk's async host site never calls the "
                    + "deterministic start seam");
            check(lua.contains("pcall(__rt.async_step, __tA.handle)"),
                "the LuaJIT AWAIT drives a handle-carrying record through "
                    + "__rt.async_step");
            check(lua.contains("if __tA.handle ~= nil then")
                    && lua.indexOf("pcall(__rt.async_step, __tA.handle)")
                        < lua.indexOf("__callbacks.__hostCompleteAsync(__tA.label)"),
                "the LuaJIT seam completion is reachable only by a record without "
                    + "an operation handle (the production path never reaches it)");
            check(lua.contains("__exportSurfaces[\"host.async_ok\"][\"fetchValue\"]).f"),
                "the LuaJIT async host site invokes the loaded surface entry through "
                    + "the host-boundary call shape");
            check(java.util.regex.Pattern.compile(
                    "__asyncStartHost\\(\\d+, \"host\\.async_ok\\.fetchValue\", "
                        + "__resT\\)").matcher(lua).find(),
                "the LuaJIT async host site binds the returned operation handle to the "
                    + "canonical token");

            String className = JvmBackend.classNameFor(project.entryModule().path());
            String java = JvmSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), className, compiled.surface())
                .source();
            check(!java.contains("HOST_ASYNC"),
                "the JVM production artifact never references the deterministic seam "
                    + "field");
            check(java.contains("JvmRuntime.startHostTask(")
                    && java.contains("\"host.async_ok.fetchValue\", __ha_"),
                "the JVM async host site registers the returned operation handle");
            check(!java.contains(".join()"),
                "the JVM artifact joining is the AWAIT's production task join, never "
                    + "a wrapper-side join");
            int wrapperAt = java.indexOf("__host$host$iasync$uok$fetchValue(");
            check(wrapperAt > 0, "the emitted async per-export wrapper exists");
            if (wrapperAt > 0) {
                String wrapperTail = java.substring(wrapperAt);
                check(wrapperTail.contains(
                        "!(__r instanceof java.util.concurrent.CompletableFuture)"),
                    "the emitted wrapper runs the declared-async shape check");
                check(wrapperTail.contains("return __r;"),
                    "the emitted wrapper returns the host operation handle");
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 5. The production host-task registration and the await branch
    // =========================================================================

    /**
     * The {@code JvmRuntime} production branch driven in process: a task
     * registered with a real operation joins that operation with the seam
     * poisoned (a seam that throws on any completion attempt), an operation
     * that failed with a {@code DealError} rethrows that identical error, and
     * a seam-registered task still consults the seam.
     */
    private static void testAwaitTaskProductionBranch() {
        System.out.println("-- JvmRuntime.awaitTask: a production-registered operation "
            + "joins without reading the seam; a seam-registered task keeps its "
            + "seam path --");
        JvmRuntime.HostAsync saved = JvmRuntime.HOST_ASYNC;
        JvmRuntime.HostAsync poisoned = new JvmRuntime.HostAsync() {
            @Override
            public String startAsync(String module, String export, String label,
                    Object[] args) {
                throw new AssertionError("the production path must never start a "
                    + "seam host operation");
            }

            @Override
            public HostCompletion completeAsync(String label) {
                throw new AssertionError("the production path must never complete "
                    + "through the seam");
            }
        };
        try {
            JvmRuntime.HOST_ASYNC = poisoned;
            CompletableFuture<Object> operation = new CompletableFuture<>();
            operation.complete("fetched");
            JvmRuntime.startHostTask(999_001L, "host.pending_op.fetchValue", operation);
            checkEq("fetched", JvmRuntime.awaitTask(999_001L, "await-origin"),
                "a production-registered operation joins while the seam is poisoned");

            // The pending form: the operation completes on another thread while
            // the AWAIT is in flight.
            CompletableFuture<Object> pending = new CompletableFuture<>();
            JvmRuntime.startHostTask(999_002L, "host.pending_op.fetchValue", pending);
            Thread completer = new Thread(() -> {
                try {
                    Thread.sleep(30L);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
                pending.complete("fetched");
            });
            completer.setDaemon(true);
            completer.start();
            checkEq("fetched", JvmRuntime.awaitTask(999_002L, "await-origin"),
                "a pending production operation completes at the AWAIT");

            // The operation's own failure wins with the identical error.
            JvmRuntime.DealError ownError = new JvmRuntime.DealError("E8001",
                "operation failed", "host/fail_op.lua:4:3", null, null, null, null);
            CompletableFuture<Object> failed = new CompletableFuture<>();
            failed.completeExceptionally(ownError);
            JvmRuntime.startHostTask(999_003L, "host.fail_op.failValue", failed);
            JvmRuntime.DealError thrown = null;
            try {
                JvmRuntime.awaitTask(999_003L, "await-origin");
            } catch (JvmRuntime.DealError error) {
                thrown = error;
            }
            check(thrown == ownError, "the operation's own DEAL error is rethrown "
                + "identical (never re-checked, copied, or re-projected)");

            // A seam-registered host task keeps the landed seam path: with no
            // seam installed the completion fails loudly, never silently.
            JvmRuntime.HOST_ASYNC = null;
            JvmRuntime.startHostTask(999_004L, "host.seam_task.fetchValue");
            boolean seamFailed = false;
            try {
                JvmRuntime.awaitTask(999_004L, "await-origin");
            } catch (IllegalStateException expected) {
                seamFailed = expected.getMessage().contains("deterministic host seam");
            }
            check(seamFailed, "a seam-registered host task without a seam fails loudly");
        } finally {
            JvmRuntime.HOST_ASYNC = saved;
        }
    }

    // =========================================================================
    // 6. The trace-mode oracle agreement (the combined host drive)
    // =========================================================================

    private static final String DRIVE_DECLARATION = """
        export function ping(): string;
        export function sum(a: int, b: int): int;
        export async function fetchValue(): string;
        """;

    /**
     * The combined drive project: one host load, a sync host call (a
     * two-argument declared signature), an async host start, and its await.
     */
    private static final String DRIVE_SOURCE = """
        import * as host from "host/async_drive"

        export async function test_async_drive(): string {
          let pinged: string = host.ping();
          let total: int = host.sum(20, 22);
          let fetched: string = await host.fetchValue();
          if (pinged !== "pong" || total !== 42 || fetched !== "fetched") {
            throw { code: "TEST_FAIL", message: "combined async drive mismatch" };
          }
          return fetched;
        }

        export function main(): null {
          return null;
        }
        """;

    private static final String DRIVE_HOST_LUA = """
        local rt = require("deal.runtime")
        return {
          ping = function() return "pong" end,
          sum = function(a, b) return a + b end,
          fetchValue = function()
            return rt.async_start(function() return "fetched" end)
          end,
        }
        """;

    private static final String DRIVE_HOST_JAVA = """
        final class HostAsync_drive {
          public static java.lang.String ping() {
            return "pong";
          }

          public static int sum(int a, int b) {
            return a + b;
          }

          public static java.lang.Object fetchValue() {
            return java.util.concurrent.CompletableFuture.completedFuture("fetched");
          }
        }
        """;

    private record TraceRun(List<String> events, List<String> asyncEffects,
        SemanticRuntimeModel.Terminal terminal) {
    }

    /** The scripted host seam of the combined trace drive (the deployed host). */
    private static SemanticOracle.HostResponder driveResponder() {
        return new SemanticOracle.HostResponder() {
            private final Map<String, SemanticOracle.Value> entries =
                new LinkedHashMap<>();

            @Override
            public SemanticOracle.Value loadedExport(ModuleId module, String export,
                    RuntimeDescriptor descriptor) {
                return entries.computeIfAbsent(module.path() + "." + export,
                    key -> new SemanticOracle.Value.IntrinsicValue("host:" + key));
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                return switch (export) {
                    case "ping" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.StrValue("pong"));
                    case "sum" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(
                            ((SemanticOracle.Value.IntValue) args.get(0)).value()
                                + ((SemanticOracle.Value.IntValue) args.get(1)).value()));
                    default -> throw new IllegalStateException("the drive scripts no "
                        + "sync host call for " + module.path() + "." + export);
                };
            }

            @Override
            public String startAsync(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args, String operationLabel) {
                return operationLabel;
            }

            @Override
            public SyncOutcome completeAsync(String operationLabel) {
                return new SyncOutcome.Returned(
                    new SemanticOracle.Value.StrValue("fetched"));
            }
        };
    }

    private static void testTraceOracleAgreement() throws Exception {
        System.out.println("-- the trace-mode oracle agreement: one load, a sync host "
            + "call, an async host start and its await, event-for-event on all three "
            + "consumers --");
        Fixture compiled = compileSource("host-async-drive", "async_drive",
            DRIVE_DECLARATION, DRIVE_SOURCE);
        Path workspace = Files.createTempDirectory("async-host-trace");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the trace drive fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String export = exportNameOf(DRIVE_SOURCE);
            ModuleId entryModule = project.entryModule();

            // (a) The oracle.
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.invokeAsyncEntry(project, result.tables(),
                    driveResponder(), entryModule, export, List.of());
            List<String> oracleEvents = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : oracleRun.trace()) {
                oracleEvents.add(event.text());
            }
            TraceRun oracle = new TraceRun(List.copyOf(oracleEvents),
                asyncEffectsOf(oracleRun.effects()), oracleRun.terminal());

            // (b) The LuaJIT trace artifact: the seam helpers keep their
            // raising defaults — the production path never reaches them.
            Path luaArtifact = workspace.resolve("project.lua");
            Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(project,
                result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path luaHost = workspace.resolve("host/async_drive.lua");
            Files.createDirectories(luaHost.getParent());
            Files.writeString(luaHost, DRIVE_HOST_LUA, StandardCharsets.UTF_8);
            Path luaProbe = workspace.resolve("trace-probe.lua");
            Files.writeString(luaProbe, luaAsyncEntryDriver(luaArtifact, entryModule,
                export), StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(luaProbe, workspace);
            check(luaOutcome.exitCode() == 0,
                "the LuaJIT trace drive runs: exit=" + luaOutcome.exitCode()
                    + " stderr=" + escaped(luaOutcome.stderr()));
            TraceRun lua = decodeTrace(luaOutcome.stderr());
            checkTraceParity("async-drive", "luajit", oracle, lua);
            checkEq(terminalText(oracle.terminal()), terminalText(lua.terminal()),
                "async-drive (luajit) terminal parity");

            // (c) The JVM trace artifact.
            JvmSemanticEmitter.EmissionResult jvmEmission =
                JvmSemanticEmitter.emitProject(project, result.tables(),
                    result.registries(), compiled.surface());
            String jvmClass = jvmEmission.className();
            SemanticOp entry = asyncEntryOf(project, entryModule, export);
            if (entry == null) {
                fail("the trace drive records no async EXTERNAL_ENTRY for '" + export
                    + "'");
                return;
            }
            Files.writeString(workspace.resolve(jvmClass + ".java"),
                jvmEmission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostAsync_drive.java"),
                DRIVE_HOST_JAVA, StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("AsyncHostTraceDriver.java"),
                jvmAsyncEntryDriver(jvmClass, entry.opId()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmClass + ".java", "HostAsync_drive.java",
                "AsyncHostTraceDriver.java"), workspace);
            check(javacRun.exitCode() == 0,
                "the trace drive compiles under javac with the deployed host: "
                    + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "AsyncHostTraceDriver"), workspace);
                check(jvmOutcome.exitCode() == 0,
                    "the JVM trace drive runs: exit=" + jvmOutcome.exitCode()
                        + " stderr=" + escaped(jvmOutcome.stderr()));
                TraceRun jvm = decodeTrace(jvmOutcome.stderr());
                checkTraceParity("async-drive", "java", oracle, jvm);
                checkEq(terminalText(oracle.terminal()), terminalText(jvm.terminal()),
                    "async-drive (java) terminal parity");
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** The async-terminal effect records of one oracle effects list. */
    private static List<String> asyncEffectsOf(
            List<SemanticRuntimeModel.EffectEvent> effects) {
        List<String> records = new ArrayList<>();
        for (SemanticRuntimeModel.EffectEvent effect : effects) {
            switch (effect.kind()) {
                case ASYNC_START_OP, ASYNC_COMPLETE_RETURN, ASYNC_COMPLETE_THROW ->
                    records.add(effect.kind() + "|" + effect.text());
                default -> {
                }
            }
        }
        return List.copyOf(records);
    }

    /** Decodes one artifact's protocol stream (trace events, async effects, terminal). */
    private static TraceRun decodeTrace(String stderr) {
        List<String> events = new ArrayList<>();
        List<String> asyncEffects = new ArrayList<>();
        SemanticRuntimeModel.Terminal terminal = null;
        for (String line : stderr.split("\n", -1)) {
            if (line.isEmpty()) {
                continue;
            }
            Object decoded;
            try {
                decoded = SemanticTraceProtocol.decode(line);
            } catch (RuntimeException exception) {
                throw new IllegalStateException("the trace protocol does not decode '"
                    + line + "': " + exception.getMessage());
            }
            if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                events.add(event.text());
            } else if (decoded instanceof SemanticRuntimeModel.EffectEvent effect) {
                switch (effect.kind()) {
                    case ASYNC_START_OP, ASYNC_COMPLETE_RETURN, ASYNC_COMPLETE_THROW ->
                        asyncEffects.add(effect.kind() + "|" + effect.text());
                    default -> {
                    }
                }
            } else if (decoded instanceof SemanticRuntimeModel.Terminal term) {
                if (terminal != null) {
                    throw new IllegalStateException("two terminal records: " + line);
                }
                terminal = term;
            }
        }
        if (terminal == null) {
            throw new IllegalStateException("the artifact published no terminal record");
        }
        return new TraceRun(List.copyOf(events), List.copyOf(asyncEffects), terminal);
    }

    private static void checkTraceParity(String name, String target,
            TraceRun oracle, TraceRun artifact) {
        List<String> expected = oracle.events();
        List<String> actual = artifact.events();
        if (expected.equals(actual)) {
            passed++;
        } else {
            failed++;
            int limit = Math.min(expected.size(), actual.size());
            for (int i = 0; i < limit; i++) {
                if (!expected.get(i).equals(actual.get(i))) {
                    System.err.println("FAIL: " + name + " (" + target
                        + ") trace event " + i + " oracle [" + expected.get(i)
                        + "] vs artifact [" + actual.get(i) + "]");
                    break;
                }
            }
            System.err.println("FAIL: " + name + " (" + target + ") trace lengths "
                + expected.size() + " (oracle) vs " + actual.size() + " (artifact)");
        }
        checkEq(oracle.asyncEffects(), artifact.asyncEffects(),
            name + " (" + target + ") async terminal effects");
    }

    /** The LuaJIT async-entry drive: the deferred init walk, then the entry. */
    private static String luaAsyncEntryDriver(Path artifact, ModuleId module,
            String export) {
        return """
            local chunk = dofile("%s")
            local ok, err = __dealMain()
            if not ok then
              io.stderr:write("R|failure|" .. __callbacks.__errtext(err) .. "\\n")
            else
              local okE, resE = pcall(__asyncEntries["%s#%s"], "-", true)
              if okE then
                io.stderr:write("R|success|" .. __callbacks.__hostAtom(resE) .. "\\n")
              else
                io.stderr:write("R|failure|" .. __callbacks.__errtext(resE) .. "\\n")
              end
            end
            io.stderr:flush()
            """.formatted(artifact.toAbsolutePath().toString(), module.path(), export);
    }

    /** The JVM async-entry drive: {@code dealMain} then the entry, one terminal. */
    private static String jvmAsyncEntryDriver(String className, OpId entry) {
        return """
            final class AsyncHostTraceDriver {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                  java.lang.Object result = %s.ae%d("-", true,
                      new java.lang.Object[]{ });
                  System.err.println("R|success|"
                      + deal.codegen.jvm.JvmRuntime.hostAtom(result));
                  System.err.flush();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.err.println("R|failure|"
                      + deal.codegen.jvm.JvmRuntime.errtext(error));
                  System.err.flush();
                }
              }
            }
            """.formatted(className, className, entry.id());
    }

    // =========================================================================
    // 7. Fail-closed seeds
    // =========================================================================

    private static final String FAIL_OP_DECLARATION = """
        export async function failValue(): string;
        """;

    private static final String FAIL_OP_SOURCE = """
        import * as host from "host/fail_op"

        export async function test_fail_op(): string {
          let value: string = await host.failValue();
          return value;
        }

        export function main(): null {
          return null;
        }
        """;

    /** The deployed Lua host whose operation raises the runtime's DEAL error. */
    private static final String FAIL_OP_HOST_LUA = """
        local rt = require("deal.runtime")
        return {
          failValue = function()
            return rt.async_start(function()
              error(rt._err("E8001", "operation failed", "host/fail_op.lua", 4, 3))
            end)
          end,
        }
        """;

    /** The deployed JVM host whose operation fails with a DEAL error. */
    private static final String FAIL_OP_HOST_JAVA = """
        final class HostFail_op {
          public static java.lang.Object failValue() {
            return java.util.concurrent.CompletableFuture.failedFuture(
                new deal.codegen.jvm.JvmRuntime.DealError("E8001",
                    "operation failed", "host/fail_op.java:4:3", null, null, null,
                    null));
          }
        }
        """;

    private static void testFailClosedSeeds() throws Exception {
        System.out.println("-- the fail-closed seeds: the operation's own DEAL error "
            + "surfaces identically, and a call of an unloaded surface fails loudly --");
        // Seed 1: the operation fails with a DEAL error — the identical error
        // (its own code and origin) surfaces at the AWAIT on both targets.
        Fixture compiled = compileSource("host-fail-op", "fail_op",
            FAIL_OP_DECLARATION, FAIL_OP_SOURCE);
        Path workspace = Files.createTempDirectory("async-host-fail");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the fail-op seed lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path hostTarget = workspace.resolve("host/fail_op.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.writeString(hostTarget, FAIL_OP_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(probe, workspace);
            checkEq("ERR:E8001|operation failed|host/fail_op.lua:4:3|-|-",
                luaOutcome.value(),
                "the LuaJIT operation's own DEAL error surfaces identically");

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostFail_op.java"),
                FAIL_OP_HOST_JAVA, StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("AsyncHostProbe.java"),
                jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostFail_op.java", "AsyncHostProbe.java"),
                workspace);
            check(javacRun.exitCode() == 0, "the fail-op seed compiles under javac: "
                + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "AsyncHostProbe"),
                    workspace);
                checkEq("ERR:E8001|operation failed|host/fail_op.java:4:3|-|-",
                    jvmOutcome.value(),
                    "the JVM operation's own DEAL error surfaces identically");
            }

            // Seed 2: the surface load is removed from the emitted chunk, so
            // the async start resolves an unloaded surface: it fails loudly.
            String mutatedText = mutateUnloaded(artifact);
            if (mutatedText == null) {
                fail("the unloaded-surface seed mutates the load");
            } else {
                Path mutatedArtifact = workspace.resolve("project-unloaded.lua");
                Files.writeString(mutatedArtifact, mutatedText, StandardCharsets.UTF_8);
                Path mutatedProbe = workspace.resolve("probe-unloaded.lua");
                Files.writeString(mutatedProbe,
                    luaDriver(mutatedArtifact, compiled.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome seedOutcome = runLua(mutatedProbe, workspace);
                check(seedOutcome.value().startsWith("ERR:")
                        || seedOutcome.exitCode() != 0,
                    "a call of an unloaded surface fails loudly, never silently: "
                        + escaped(seedOutcome.value()) + " stderr="
                        + escaped(seedOutcome.stderr()));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** Removes the host load from one emitted production chunk, or null. */
    private static String mutateUnloaded(Path artifact) throws Exception {
        String lua = Files.readString(artifact, StandardCharsets.UTF_8);
        String mutated = lua.replaceAll(
            "__exportSurfaces\\[\"host\\.fail_op\"\\] = "
                + "__exportSurfaces\\[\"host\\.fail_op\"\\] or "
                + "__rt\\.load_host\\([^\\n]*\\)\\n", "");
        return mutated.equals(lua) ? null : mutated;
    }

    /**
     * The artifact error projections recorded by the fixture-set drives: the
     * shared completion-cell message and actual kind the artifacts produce,
     * asserted equal to the oracle's snapshot by the oracle drive.
     */
    private static final Map<String, String[]> ARTIFACT_ERRORS = new LinkedHashMap<>();

    // =========================================================================
    // The drivers and the process helpers
    // =========================================================================================================================================

    /** The LuaJIT probe: the init walk, then the fixture's test exports. */
    private static String luaDriver(Path artifact, String entryPath) {
        return """
            local function emitError(e)
              if type(e) == "table" and e.__d then
                print("ERR:" .. e.code .. "|" .. tostring(e.m) .. "|" .. tostring(e.o)
                  .. "|" .. tostring(e.e or "-") .. "|" .. tostring(e.a or "-"))
                return
              end
              if type(e) == "table" and e.code ~= nil then
                print("ERR:" .. e.code .. "|" .. tostring(e.message) .. "|"
                  .. tostring(e.file) .. ":" .. tostring(e.line) .. ":"
                  .. tostring(e.column) .. "|" .. tostring(e.expected or "-") .. "|"
                  .. tostring(e.actual or "-"))
                return
              end
              print("ERR:E9999|" .. tostring(e) .. "|-|-|-")
            end
            local chunk = dofile("%s")
            local ok, err = __dealMain()
            if not ok then emitError(err) os.exit(0) end
            local surface = __exportSurfaces["%s"]
            if surface ~= nil then
              local ordered = {}
              for name, candidate in pairs(surface) do ordered[#ordered + 1] = name end
              table.sort(ordered)
              for _, name in ipairs(ordered) do
                if string.sub(name, 1, 5) == "test_" then
                  local ok2, err2 = pcall(surface[name].f)
                  if not ok2 then emitError(err2) os.exit(0) end
                end
              end
            end
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    /** The JVM probe: the init walk, then the fixture's test exports. */
    private static String jvmDriver(String className, String entryPath) {
        return """
            final class AsyncHostProbe {
              public static void main(String[] args) {
                // The deterministic seam stays poisoned: the production path must
                // never reach it.
                deal.codegen.jvm.JvmRuntime.HOST_ASYNC =
                    new deal.codegen.jvm.JvmRuntime.HostAsync() {
                      public String startAsync(java.lang.String module,
                          java.lang.String export, java.lang.String label,
                          java.lang.Object[] arguments) {
                        throw new AssertionError("the production path reached the "
                            + "host-async start seam");
                      }

                      public deal.codegen.jvm.JvmRuntime.HostAsync.HostCompletion
                          completeAsync(java.lang.String label) {
                        throw new AssertionError("the production path reached the "
                            + "host-async completion seam");
                      }
                    };
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  report(error);
                  return;
                }
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.exportSurface(%s);
                for (java.lang.String name : surface.keys) {
                  if (!name.startsWith("test_")) { continue; }
                  try {
                    ((deal.codegen.jvm.JvmRuntime.FunctionValue) surface.read(
                        name)).fn.invoke(new java.lang.Object[]{ });
                  } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                    report(error);
                    return;
                  }
                }
                System.out.println("OK");
              }

              private static void report(deal.codegen.jvm.JvmRuntime.DealError error) {
                System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                    + error.origin + "|" + (error.expected == null ? "-"
                        : error.expected) + "|" + (error.actual == null ? "-"
                        : error.actual));
              }
            }
            """.formatted(className, className, quoted(entryPath));
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

    /** Deploys one corpus host implementation where the raw specifier resolves it. */
    private static void deployHostLua(Path workspace, AsyncFixture fixture)
            throws Exception {
        Path target = workspace.resolve(fixture.hostSpecifier() + ".lua");
        Files.createDirectories(target.getParent());
        Files.copy(Path.of(fixture.corpusHost() + ".lua"), target);
    }

    private static Outcome runLua(Path probe, Path workspace) throws Exception {
        ProcessBuilder builder = new ProcessBuilder("luajit",
            probe.toAbsolutePath().toString());
        builder.directory(workspace.toFile());
        builder.environment().put("DEAL_DEFER_MAIN", "1");
        return run(builder);
    }

    private static Outcome runProcess(List<String> command, Path workDir)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        return run(builder);
    }

    private static Outcome run(ProcessBuilder builder) throws Exception {
        Path stderrFile = Files.createTempFile("async-host-err", ".txt");
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new Outcome(exit, stdout, stderr, stdout.strip());
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(java.io.File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(java.io.File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static String quoted(String text) {
        StringBuilder literal = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> literal.append("\\\"");
                case '\\' -> literal.append("\\\\");
                default -> literal.append(c);
            }
        }
        return literal.append('"').toString();
    }

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) throws Exception {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (var walk = Files.walk(path)) {
            for (Path entry : walk.sorted(java.util.Comparator.reverseOrder()).toList()) {
                Files.deleteIfExists(entry);
            }
        }
    }
}
