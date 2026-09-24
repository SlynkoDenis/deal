package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SemanticTraceProtocol;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
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

/**
 * ISSUE-0655: the cross-module async realization and the external async
 * link ({@code cross-module-call-realization} X2 and the cross-module
 * async call contract; {@code luajit-jvm-single-lowering-production-cutover}
 * C2; {@code semantic-ir-construct-coverage-cutover} K4).
 *
 * <ol>
 *   <li>both emitters emit one async entry per async {@code EXTERNAL_ENTRY}
 *       op of every closure unit (the loops iterate the closure's units),
 *       each entry resolving the entry function and its capture cells
 *       through its own unit; LuaJIT keys
 *       {@code __asyncEntries["<owner>#<export>"]} and the JVM emits the
 *       local {@code ae<entryOpId>} method with the caller referencing it
 *       locally — no {@code SharedM<callee>} reference exists in the one
 *       project artifact;</li>
 *   <li>each entry establishes its own module context around the callee
 *       body and its own events, restoring on every path (LuaJIT
 *       {@code __modStack}; the JVM per-entry module literal plus
 *       {@code JvmRuntime.setModule} with a {@code finally} restore and
 *       event emissions passing that literal);</li>
 *   <li>the caller's {@code ASYNC_START(EXTERNAL)} publishes the alias
 *       token over the callee entry's canonical token (the entry op's id
 *       by construction), the entry creates exactly one canonical task
 *       parented to the caller's op key, and the caller's single
 *       {@code AWAIT} drains and runs the single {@code ASYNC_COMPLETION}
 *       boundary on the declared completion descriptor; the drive flag is
 *       {@code false} for the cross-module caller and {@code true} only
 *       for the top-level scenario drive;</li>
 *   <li>the composed drive executes a sync cross-module call from the
 *       corpus fixture set jointly with the async drive on both targets
 *       (the entry record, the module-context switch, and the artifact
 *       layout are exercised together);</li>
 *   <li>the oracle and the conformance artifacts agree event-for-event
 *       through the differential harness's async-entry matrix, and the
 *       project trace artifact carries the callee module on the callee
 *       entry and body events while the caller's events keep the caller's
 *       module;</li>
 *   <li>the fail-closed seeds (an async start without its link, an entry
 *       reference that resolves to no emitted entry) are rejected by both
 *       production emitters, and the production arm keeps its landed
 *       E6005 {@code SHARED_EMITTER_COVERAGE} outcome with nothing
 *       staged (the guard-replacement slice removes the guard shape; this
 *       slice's drives use the production emitter entry).</li>
 * </ol>
 */
public class CrossModuleAsyncRealizationTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // The focused two-module async fixture
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId APP = new ModuleId("app");
    private static final String PROBE = "test_cross_module_async";

    private static final String LIB_SOURCE = """
        export function double21(): int {
          return 21 * 2;
        }

        export async function getAnswer(): int {
          return 42;
        }

        export async function greet(name: string): string {
          return "Hello, " + name;
        }

        export async function unused(): int {
          return 0;
        }
        """;

    private static final String APP_SOURCE = """
        import * as lib from "./lib"

        export async function test_cross_module_async(): int {
          let s: int = lib.double21();
          let x: int = await lib.getAnswer();
          let t: string = await lib.greet("world");
          if (s !== 42 || x !== 42 || t !== "Hello, world") {
            throw { code: "TEST_FAIL", message: "cross-module async drive" };
          }
          return x;
        }

        export function main(): null {
          return null;
        }
        """;

    /**
     * The async-only variant of the probe: the differential harness's
     * per-unit async-entry drive emits one unit per artifact, and a
     * single-unit session cannot realize a sync cross-module call (its
     * landed arm fails closed for a callee outside the session). The
     * composed fixture (with the sync call) is driven through the project
     * artifacts instead.
     */
    private static final String APP_ASYNC_ONLY_SOURCE = """
        import * as lib from "./lib"

        export async function test_cross_module_async(): int {
          let x: int = await lib.getAnswer();
          let t: string = await lib.greet("world");
          if (x !== 42 || t !== "Hello, world") {
            throw { code: "TEST_FAIL", message: "cross-module async drive" };
          }
          return x;
        }

        export function main(): null {
          return null;
        }
        """;

    private record Fixture(
        Path root,
        Path moduleRoot,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        DistributionHome distributionHome,
        String entryName) {
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** Materializes a source set with the entry module last. */
    private static Fixture materialize(String stamp, Map<String, String> sources,
            String entryName, List<String> companions) throws Exception {
        Path root = Files.createTempDirectory("cross-module-async-" + stamp);
        Path moduleRoot = root.resolve("src");
        Files.createDirectories(moduleRoot);
        writeFileIn(root, "src/" + entryName + ".deal", sources.get(entryName));
        for (String companion : companions) {
            writeFileIn(root, "src/" + companion + ".deal", sources.get(companion));
        }
        Path entry = moduleRoot.resolve(entryName + ".deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(moduleRoot.toAbsolutePath()), null, null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: "
                + detail + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, moduleRoot, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            DistributionHome.forManifestDirectory(moduleRoot.toString()), entryName);
    }

    /** The focused two-module async fixture (the callee is a non-entry module). */
    private static Fixture asyncFixture() throws Exception {
        return materialize("probe", Map.of("lib", LIB_SOURCE, "app", APP_SOURCE),
            "app", List.of("lib"));
    }

    /** The async-only variant used for the per-unit differential matrix. */
    private static Fixture asyncOnlyFixture() throws Exception {
        return materialize("probe-async-only",
            Map.of("lib", LIB_SOURCE, "app", APP_ASYNC_ONLY_SOURCE),
            "app", List.of("lib"));
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), new LinkedHashMap<>(), new LinkedHashMap<>(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            java.util.Set.of());
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

    /** The async starts of one unit targeting the callee module. */
    private static List<SemanticOp> asyncExternalStarts(LoweredModuleUnit unit) {
        List<SemanticOp> starts = new ArrayList<>();
        for (SemanticOp op : ofKind(unit, SemanticOpKind.ASYNC_START)) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            if (payload.callee() instanceof KindPayload.CallCallee.Static callee
                    && callee.binding()
                        instanceof FunctionExecutionBinding.ExternalFunction) {
                starts.add(op);
            }
        }
        return starts;
    }

    /** The async EXTERNAL_ENTRY op of one module's export, or null. */
    private static OpId asyncEntryOf(ExecutableLoweredProject project,
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
                    return op.opId();
                }
            }
        }
        return null;
    }

    // =========================================================================
    // 1. The lowering: one async entry per async export per closure module
    // =========================================================================

    private static void testEntrySetAndTokenLinkage() throws Exception {
        System.out.println("-- one async EXTERNAL_ENTRY per async export of every "
            + "closure module; the caller's alias token over the callee's canonical "
            + "entry token; the single AWAIT and ASYNC_COMPLETION --");
        Fixture fixture = asyncFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null && !result.hasErrors(),
                "the async probe lowers through the one project entry: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            check(libUnit != null && appUnit != null,
                "the closure carries the callee and the caller module");
            if (libUnit == null || appUnit == null) {
                return;
            }

            // The callee unit: one async entry per declared async export
            // (getAnswer, greet) and one sync entry (double21); every async
            // entry names its single FUNCTION_RETURN task cell.
            List<String> libAsyncExports = new ArrayList<>();
            for (SemanticOp op : ofKind(libUnit, SemanticOpKind.EXTERNAL_ENTRY)) {
                KindPayload.ExternalEntryPayload payload =
                    (KindPayload.ExternalEntryPayload) op.payload();
                if (!payload.async()) {
                    continue;
                }
                libAsyncExports.add(payload.exportName());
                SemanticOp boundary = opOf(libUnit, payload.returnBoundaryOpId());
                check(boundary != null
                        && boundary.kind() == SemanticOpKind.BOUNDARY
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp
                        && bp.kind() == BoundaryKind.FUNCTION_RETURN,
                    "the async entry of " + payload.exportName()
                        + " names its single FUNCTION_RETURN task cell");
                if (boundary != null
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp) {
                    checkEq(payload.completionDescriptor(), bp.descriptor(),
                        "the FUNCTION_RETURN cell checks the declared completion "
                            + "descriptor of " + payload.exportName());
                }
            }
            checkEq(List.of("getAnswer", "greet", "unused"), libAsyncExports,
                "the non-entry callee module records one async entry per async "
                    + "export, independent of whether the body executes");

            // The caller unit: one async entry for its own probe export and
            // two ASYNC_START(EXTERNAL) ops whose alias tokens link the
            // callee entries' canonical tokens.
            check(asyncEntryOf(project, APP, PROBE) != null,
                "the entry module records its own async probe entry");
            List<SemanticOp> starts = asyncExternalStarts(appUnit);
            checkEq(2, starts.size(),
                "the caller records one async external start per awaited call");
            for (SemanticOp start : starts) {
                KindPayload.AsyncStartPayload payload =
                    (KindPayload.AsyncStartPayload) start.payload();
                checkEq(AsyncStartSource.EXTERNAL, payload.source(),
                    "the async start records the EXTERNAL source");
                FunctionExecutionBinding.ExternalFunction external =
                    (FunctionExecutionBinding.ExternalFunction)
                        ((KindPayload.CallCallee.Static) payload.callee()).binding();
                checkEq(ExternalExecutionOwner.SHARED_BODY, external.executionOwner(),
                    "the async external resolves the SHARED_BODY execution owner");
                ExternalAsyncLink link = payload.externalAsyncLink();
                check(link != null, "the async external carries its ExternalAsyncLink");
                if (link == null) {
                    return;
                }
                checkEq(LIB, link.calleeModuleId(),
                    "the link names the callee module");
                checkEq(external.exportName(), link.exportName(),
                    "the link names the awaited export");
                checkEq(asyncEntryOf(project, LIB, external.exportName()),
                    new OpId(link.calleeModuleId(), link.calleeTokenId().tokenId()),
                    "the link's canonical token is the callee entry op's id");
                check(start.result() instanceof AsyncTokenId.Alias alias
                        && alias.linkKind() == AsyncLinkKind.EXTERNAL_LINK
                        && alias.referent().equals(link.calleeTokenId()),
                    "the caller's published token is the alias over the callee "
                        + "canonical token: " + start.result());
            }

            // Each AWAIT consumes exactly one alias link and runs exactly one
            // ASYNC_COMPLETION boundary on the declared completion descriptor.
            List<SemanticOp> awaits = ofKind(appUnit, SemanticOpKind.AWAIT);
            checkEq(2, awaits.size(),
                "the caller awaits each started external once");
            for (SemanticOp await : awaits) {
                KindPayload.AwaitPayload payload =
                    (KindPayload.AwaitPayload) await.payload();
                check(payload.token() instanceof AsyncTokenId.Alias alias
                        && alias.linkKind() == AsyncLinkKind.EXTERNAL_LINK,
                    "the await consumes the external alias token");
                SemanticOp boundary = opOf(appUnit, payload.completionBoundaryOpId());
                check(boundary != null
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp
                        && bp.kind() == BoundaryKind.ASYNC_COMPLETION
                        && bp.descriptor().equals(payload.completionDescriptor()),
                    "the await runs the single ASYNC_COMPLETION boundary on the "
                        + "declared descriptor");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The emission surface: the per-closure entry set and the local linkage
    // =========================================================================

    private static void testEmissionSurface() throws Exception {
        System.out.println("-- the LuaJIT chunk carries one __asyncEntries entry per "
            + "async export of every module; the JVM class carries the local "
            + "ae<entryId> methods and no SharedM reference --");
        Fixture fixture = asyncFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the async probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            check(lua.contains("__asyncEntries[\"lib#getAnswer\"] = function("),
                "the LuaJIT chunk defines the non-entry module's async entry "
                    + "(getAnswer)");
            check(lua.contains("__asyncEntries[\"lib#greet\"] = function("),
                "the LuaJIT chunk defines the non-entry module's async entry (greet)");
            check(lua.contains("__asyncEntries[\"app#" + PROBE + "\"] = function("),
                "the LuaJIT chunk defines the entry module's async probe entry");
            check(lua.contains("__asyncEntries[\"lib#unused\"] = function("),
                "the LuaJIT chunk defines an async export whose body no caller "
                    + "drives (the entry set is a closure property)");
            OpId getAnswerEntry = asyncEntryOf(project, LIB, "getAnswer");
            SemanticOp start = asyncExternalStarts(project.modules().get(APP)).get(0);
            check(lua.contains("__asyncEntries[\"lib#getAnswer\"]("
                    + luaString(start.opId().module().path() + "#" + start.opId().id())
                    + ", false, unpack("),
                "the cross-module caller invokes the callee key with the drive flag "
                    + "false");
            check(lua.contains("__modStack[#__modStack + 1] = __module"),
                "the LuaJIT entries establish their own module context");

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            check(emission.source().contains(
                    "public static Object ae" + getAnswerEntry.id() + "("),
                "the JVM class defines the non-entry module's ae<entryId> method");
            check(emission.source().contains("public static Object ae"
                    + asyncEntryOf(project, APP, PROBE).id() + "("),
                "the JVM class defines the entry module's ae<entryId> method");
            check(emission.source().contains("public static Object ae"
                    + asyncEntryOf(project, LIB, "unused").id() + "("),
                "the JVM class defines the never-driven async export's "
                    + "ae<entryId> method");
            check(emission.source().contains("ae" + getAnswerEntry.id() + "(\"app#"
                    + start.opId().id() + "\", false, new Object[]{});"),
                "the cross-module caller invokes the local ae<entryId> method with "
                    + "the drive flag false");
            check(!emission.source().contains("SharedM"),
                "no SharedM<callee> reference exists in the one JVM artifact");
            check(emission.source().contains("MODULE = \"lib\";"),
                "the JVM entry sets the per-entry module literal around the callee "
                    + "body");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The production drives: the composed sync + async execution
    // =========================================================================

    private static void testProductionDrives() throws Exception {
        System.out.println("-- the production artifacts execute on both targets: the "
            + "async probe through the callee entry with the composed sync "
            + "cross-module call, and the corpus sync fixture jointly --");
        driveAsyncProbeProduction();
        driveSyncCorpusFixtureProduction();
    }

    private static void driveAsyncProbeProduction() throws Exception {
        Fixture fixture = asyncFixture();
        Path workspace = Files.createTempDirectory("cross-module-async-drive");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the async probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            // LuaJIT.
            Path luaArtifact = workspace.resolve("project.lua");
            Files.writeString(luaArtifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), fixture.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path luaProbe = workspace.resolve("probe.lua");
            Files.writeString(luaProbe, luaAsyncEntryDriver(luaArtifact, APP, PROBE),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(luaProbe, workspace);
            checkEq(0, luaOutcome.exitCode(),
                "the LuaJIT production async drive exits 0: " + luaOutcome.stderr());
            check(luaOutcome.stderr().contains("R|success|int:42"),
                "the LuaJIT production async drive completes with the pinned value: "
                    + luaOutcome.stderr());

            // JVM.
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            OpId probeEntry = asyncEntryOf(project, APP, PROBE);
            Files.writeString(workspace.resolve("AsyncProbeDriver.java"),
                jvmAsyncEntryDriver("AsyncProbeDriver", className, probeEntry),
                StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                workspace.resolve(className + ".java").toAbsolutePath().toString(),
                workspace.resolve("AsyncProbeDriver.java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, javacRun.exitCode(),
                "the JVM production async artifact compiles: " + javacRun.stdout()
                    + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "AsyncProbeDriver"), workspace);
                checkEq(0, jvmOutcome.exitCode(),
                    "the JVM production async drive exits 0: " + jvmOutcome.stderr());
                check(jvmOutcome.stderr().contains("R|success|int:42"),
                    "the JVM production async drive completes with the pinned "
                        + "value: " + jvmOutcome.stderr());
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The composed-drive half: a corpus {@code modules/*} fixture (a
     * statically resolved sync cross-module call) executes through the same
     * production emitters in the same test run, so the sync entry record
     * realization, the module-context switch, and the artifact layout are
     * exercised jointly with the async realization.
     */
    private static void driveSyncCorpusFixtureProduction() throws Exception {
        Path corpus = Path.of("test", "conformance", "backend-runtime", "modules");
        String name = "imported-recursive-export";
        String probe = "test_imported_recursive_export";
        String entrySource = corpusSource(corpus, name + ".deal");
        String companionSource = corpusSource(corpus, "recursive_export_lib.deal");
        Fixture fixture = materialize("sync-corpus",
            Map.of(name, entrySource, "recursive_export_lib", companionSource),
            name, List.of("recursive_export_lib"));
        Path workspace = Files.createTempDirectory("cross-module-async-sync");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the corpus sync fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path luaArtifact = workspace.resolve(name + ".lua");
            Files.writeString(luaArtifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), fixture.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path luaProbe = workspace.resolve("probe.lua");
            Files.writeString(luaProbe, luaSyncProbeDriver(luaArtifact, name, probe),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runProcess(List.of("luajit",
                luaProbe.toAbsolutePath().toString()), workspace);
            checkEq(0, luaOutcome.exitCode(), name + " (LuaJIT): the sync corpus "
                + "fixture exits 0: " + luaOutcome.stderr());
            checkEq("", luaOutcome.stdout(), name + " (LuaJIT): no stdout");
            checkEq("", luaOutcome.stderr(), name + " (LuaJIT): no stderr");

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("SyncProbe.java"),
                jvmSyncProbeDriver(className, name, probe), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                workspace.resolve(className + ".java").toAbsolutePath().toString(),
                workspace.resolve("SyncProbe.java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, javacRun.exitCode(), name + " (JVM): the sync corpus fixture "
                + "compiles: " + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "SyncProbe"),
                    workspace);
                checkEq(0, jvmOutcome.exitCode(), name + " (JVM): the sync corpus "
                    + "fixture exits 0: " + jvmOutcome.stderr());
                checkEq("", jvmOutcome.stdout(), name + " (JVM): no stdout");
                checkEq("", jvmOutcome.stderr(), name + " (JVM): no stderr");
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The oracle agreement and the callee module attribution
    // =========================================================================

    private static void testDifferentialParityAndModuleContext() throws Exception {
        System.out.println("-- the oracle and both conformance emitters agree "
            + "event-for-event; the entry and body events carry the callee module "
            + "while the caller keeps its own --");
        differentialMatrixParity();
        Fixture fixture = asyncFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the async probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();

            // The project trace artifact (the composed fixture): the callee
            // entry and the callee body events carry the callee module even
            // though the caller runs in another module, and every event of
            // the drive is attributed to one of the closure's modules. The
            // conformance artifacts agree with each other event-for-event
            // and publish the pinned terminal.
            Path workspace = Files.createTempDirectory("cross-module-async-trace");
            try {
                Path luaArtifact = workspace.resolve("project.lua");
                Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(
                    project, result.tables(), result.registries()),
                    StandardCharsets.UTF_8);
                deployRuntime(workspace);
                Path luaProbe = workspace.resolve("trace-probe.lua");
                Files.writeString(luaProbe, luaAsyncEntryDriver(luaArtifact, APP, PROBE),
                    StandardCharsets.UTF_8);
                Outcome luaOutcome = runLua(luaProbe, workspace);
                checkEq(0, luaOutcome.exitCode(),
                    "the LuaJIT trace drive exits 0: " + luaOutcome.stderr());
                check(luaOutcome.stderr().contains("R|success|int:42"),
                    "the LuaJIT trace drive completes with the pinned value");
                TraceRun lua = decodeTrace(luaOutcome.stderr());
                List<String> luaAsync = dropDependencyInitPrefix(lua.events());
                assertModuleContext("luajit", project, luaAsync);
                checkEq("success:int:42", terminalText(lua.terminal()),
                    "the LuaJIT trace drive publishes the pinned terminal");

                String className = JvmBackend.classNameFor(project.entryModule().path());
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitProject(project, result.tables(),
                        result.registries());
                Files.writeString(workspace.resolve(emission.className() + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("AsyncTraceDriver.java"),
                    jvmAsyncEntryDriver("AsyncTraceDriver", emission.className(),
                        asyncEntryOf(project, APP, PROBE)),
                    StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    workspace.resolve(emission.className() + ".java")
                        .toAbsolutePath().toString(),
                    workspace.resolve("AsyncTraceDriver.java")
                        .toAbsolutePath().toString()), workspace);
                checkEq(0, javacRun.exitCode(),
                    "the JVM trace drive compiles: " + javacRun.stdout()
                        + javacRun.stderr());
                if (javacRun.exitCode() == 0) {
                    Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes,
                        "AsyncTraceDriver"), workspace);
                    checkEq(0, jvmOutcome.exitCode(),
                        "the JVM trace drive exits 0: " + jvmOutcome.stderr());
                    TraceRun jvm = decodeTrace(jvmOutcome.stderr());
                    List<String> jvmAsync = dropDependencyInitPrefix(jvm.events());
                    assertModuleContext("java", project, jvmAsync);
                    checkEq(luaAsync, jvmAsync,
                        "the LuaJIT and JVM project traces agree event-for-event");
                    checkEq(terminalText(lua.terminal()), terminalText(jvm.terminal()),
                        "both project trace drives publish the same terminal");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The three-consumer async-entry differential matrix over the async-only
     * variant of the fixture (the differential harness emits one artifact per
     * unit, and a single-unit session cannot realize the sync cross-module
     * call of the composed probe): the oracle's {@code invokeAsyncEntry}
     * surface, the per-unit LuaJIT artifacts, and the per-unit JVM artifacts
     * agree on the oracle's trace event-for-event, and the oracle's callee
     * entry events carry the callee module.
     */
    private static void differentialMatrixParity() throws Exception {
        Fixture fixture = asyncOnlyFixture();
        Path matrix = Files.createTempDirectory("cross-module-async-matrix");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the async-only probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runAsyncEntry(project,
                    result.tables(), PROBE, List.of(),
                    SemanticDifferentialHarness.Expectation.success(
                        "cross-module async entry", List.of(), "int:42"),
                    matrix, null);
            checkEq(3, verdict.runs().size(),
                "the async-entry matrix produced the three consumers: "
                    + verdict.failures());
            if (verdict.runs().size() != 3) {
                return;
            }
            List<String> oracleTrace = traceLines(verdict.runs().get(0));
            check(!oracleTrace.isEmpty(),
                "the oracle produced events for the async entry drive");
            for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                checkEq(oracleTrace, traceLines(consumer),
                    "the " + consumer.consumer()
                        + " per-unit trace equals the oracle's event-for-event");
            }
            // The callee entry's own events carry the callee module.
            java.util.Set<String> libEntryKeys = new java.util.HashSet<>();
            for (String export : List.of("getAnswer", "greet")) {
                OpId entry = asyncEntryOf(project, LIB, export);
                if (entry != null) {
                    libEntryKeys.add(opKeyText(entry));
                }
            }
            long libEntryEvents = 0;
            for (String line : oracleTrace) {
                String[] fields = line.split("\\|", -1);
                if (fields.length >= 5 && libEntryKeys.contains(fields[2])) {
                    checkEq("lib", fields[1],
                        "the oracle's callee entry event carries the callee "
                            + "module: " + line);
                    libEntryEvents++;
                }
            }
            checkEq(4L, libEntryEvents,
                "the oracle emits both callee entries' START/SUCCESS pairs");
        } finally {
            deleteRecursively(matrix);
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The callee-module attribution of one project trace: the callee entry's
     * START/SUCCESS carry {@code lib}, the callee body's ops (its
     * {@code getAnswer}/{@code greet}/{@code double21} entry tasks and their
     * nested ops) carry {@code lib}, and the caller's await completion keeps
     * {@code app}.
     */
    private static void assertModuleContext(String target, ExecutableLoweredProject project,
            List<String> events) {
        LoweredModuleUnit appUnit = project.modules().get(APP);
        OpId getAnswer = asyncEntryOf(project, LIB, "getAnswer");
        OpId greet = asyncEntryOf(project, LIB, "greet");
        OpId probe = asyncEntryOf(project, APP, PROBE);
        java.util.Set<String> callerStartKeys = new java.util.HashSet<>();
        for (SemanticOp start : asyncExternalStarts(appUnit)) {
            callerStartKeys.add(opKeyText(start.opId()));
        }
        long libEntryEvents = 0;
        long libBodyEvents = 0;
        long appEntryEvents = 0;
        long appCompletionEvents = 0;
        for (String line : events) {
            String[] fields = line.split("\\|", -1);
            // Trace text: sequence|module|opKey|phase|kind|digest|parent|inputs|output|error
            if (fields.length < 5) {
                continue;
            }
            String module = fields[1];
            String opKey = fields[2];
            String phase = fields[3];
            String kind = fields[4];
            if (getAnswer != null && opKey.equals(opKeyText(getAnswer))) {
                checkEq("lib", module, target + ": the callee entry event carries the "
                    + "callee module: " + line);
                if (phase.equals("START")) {
                    check(fields.length >= 7
                            && callerStartKeys.contains(fields[6]),
                        target + ": the callee entry parents to the caller's "
                            + "ASYNC_START op key: " + line);
                }
                libEntryEvents++;
            }
            if (greet != null && opKey.equals(opKeyText(greet))) {
                checkEq("lib", module, target + ": the second callee entry event "
                    + "carries the callee module: " + line);
                libEntryEvents++;
            }
            if (probe != null && opKey.equals(opKeyText(probe))) {
                checkEq("app", module, target + ": the entry module's own async probe "
                    + "entry carries its own module: " + line);
                appEntryEvents++;
            }
            if (fields[1].equals("lib") && !kind.equals("MODULE_INIT")) {
                libBodyEvents++;
            }
            if (fields[1].equals("app") && kind.equals("BOUNDARY")) {
                SemanticOp boundary = opOf(appUnit, opIdOf(opKey));
                if (boundary != null
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp
                        && (bp.kind() == BoundaryKind.ASYNC_COMPLETION
                            || bp.kind() == BoundaryKind.EXTERNAL_PARAMETER)) {
                    appCompletionEvents++;
                }
            }
            check(module.equals("lib") || module.equals("app"),
                target + ": every event carries one of the closure's modules: " + line);
        }
        check(libEntryEvents >= 4, target + ": both callee entries emit START/SUCCESS "
            + "under the callee module: " + libEntryEvents);
        check(libBodyEvents > 0, target + ": the callee body events carry the callee "
            + "module: " + libBodyEvents);
        check(appEntryEvents >= 2, target + ": the caller's own probe entry emits "
            + "START/SUCCESS under the caller module: " + appEntryEvents);
        check(appCompletionEvents >= 2, target + ": the caller's await-site "
            + "completions keep the caller module: " + appCompletionEvents);
    }

    // =========================================================================
    // 5. The fail-closed seeds
    // =========================================================================

    private static void testFailClosedSeeds() throws Exception {
        System.out.println("-- the fail-closed seeds: an async start without its link "
            + "and a link resolving to no emitted entry; the production arm keeps its "
            + "landed E6005 outcome with nothing staged --");
        Fixture fixture = asyncFixture();
        Path staged = Files.createTempDirectory("cross-module-async-staged");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the async probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            SemanticOp start = asyncExternalStarts(appUnit).get(0);
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) start.payload();

            // (a) The async start without its ExternalAsyncLink.
            KindPayload.AsyncStartPayload unlinked = new KindPayload.AsyncStartPayload(
                payload.callee(), payload.source(), payload.parameterBoundaryMode(),
                payload.parameterBoundaryOpIds(), payload.completionDescriptor(),
                payload.returnBoundaryOpId(), payload.hostOperationLabel(), null);
            assertEmittersReject("the async start without its ExternalAsyncLink",
                replaceOpPayload(project, appUnit, start, unlinked), result.tables(),
                result.registries(), fixture.surface(), "ExternalAsyncLink");

            // (b) The link's canonical token naming no emitted entry: retarget
            // it at a non-entry op of the callee module (the hand-built
            // inconsistent fact no checker-valid program produces).
            SemanticOp nonEntry = ofKind(project.modules().get(LIB),
                SemanticOpKind.EXPORT_PUBLISH).get(0);
            ExternalAsyncLink dangling = new ExternalAsyncLink(
                payload.externalAsyncLink().calleeModuleId(),
                payload.externalAsyncLink().exportName(),
                new AsyncTokenId.Canonical(nonEntry.opId().id(),
                    deal.semantic.ir.AsyncTokenOwner.DEAL_BODY_TASK));
            KindPayload.AsyncStartPayload danglingLink =
                new KindPayload.AsyncStartPayload(
                    payload.callee(), payload.source(),
                    payload.parameterBoundaryMode(),
                    payload.parameterBoundaryOpIds(), payload.completionDescriptor(),
                    payload.returnBoundaryOpId(), payload.hostOperationLabel(),
                    dangling);
            assertEmittersReject("the entry reference resolving to no emitted entry",
                replaceOpPayload(project, appUnit, start, danglingLink), result.tables(),
                result.registries(), fixture.surface(), "resolves to no emitted");

            // (c) The production arm's landed outcome over the unstaged async
            // closure: E6005 SHARED_EMITTER_COVERAGE and nothing staged (the
            // guard-replacement slice removes the guard shape and retargets
            // this pin; this slice's drives use the emitter entry directly).
            PublicationStager stager = PublicationStager.forRoot(staged);
            ProductionProjectEmission.Result production;
            try {
                production = ProductionProjectEmission.run(productionInvocation(),
                    fixture.checkedProject(), fixture.index(), fixture.manifests(),
                    fixture.surface(), new LinkedHashMap<>(), new LinkedHashMap<>(),
                    BuiltinErrorDeclaration.synthesized(
                        fixture.checkedProject().modules().get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                    java.util.Set.of(), Backend.LUAJIT, false,
                    fixture.distributionHome(), stager);
                check(!production.emitted(),
                    "the production arm keeps the async closure fail-closed");
                check(production.firstDiagnostic() != null
                        && "E6005".equals(production.firstDiagnostic().code())
                        && production.firstDiagnostic().message()
                            .contains("SHARED_EMITTER_COVERAGE"),
                    "the fail-closed outcome is E6005 SHARED_EMITTER_COVERAGE: "
                        + production.firstDiagnostic());
            } finally {
                stager.discard();
            }
            Path outDir = staged.resolve("src").resolve("app.lua");
            check(!Files.exists(staged.resolve("app.lua"))
                    && !Files.exists(outDir),
                "no artifact staged for the fail-closed production run");
        } finally {
            deleteRecursively(staged);
            deleteRecursively(fixture.root());
        }
    }

    /**
     * Replaces one op's payload (the caller unit rebuilt with the replaced
     * payload and its rewired contract snapshot): the hand-built
     * inconsistent fact the fail-closed seeds need (no checker-valid
     * program produces one).
     */
    private static ExecutableLoweredProject replaceOpPayload(
            ExecutableLoweredProject project, LoweredModuleUnit caller,
            SemanticOp op, KindPayload replaced) {
        deal.semantic.ir.OperationContractSnapshot old = op.contract();
        deal.semantic.ir.OperationContractSnapshot rewired =
            new deal.semantic.ir.OperationContractSnapshot(old.version(),
                old.opKind(), old.resultType(), old.operandTypes(), old.selector(),
                replaced, old.failurePolicy(), old.referencedSemanticIds(),
                old.canonicalDigest());
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp candidate : caller.ops()) {
            if (candidate.opId().equals(op.opId())) {
                ops.add(new SemanticOp(candidate.opId(), candidate.kind(),
                    candidate.origin(), candidate.result(), candidate.resultType(),
                    candidate.operands(), candidate.operandTypes(), replaced,
                    candidate.failurePolicy(), rewired));
            } else {
                ops.add(candidate);
            }
        }
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                : project.modules().entrySet()) {
            if (entry.getKey().equals(caller.moduleId())) {
                modules.put(entry.getKey(), withOps(caller, ops));
            } else {
                modules.put(entry.getKey(), entry.getValue());
            }
        }
        return new ExecutableLoweredProject(project.semanticProfile(),
            project.interfaceIndex(), modules, project.entryModule());
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    /** Both production emitters reject the hand-built inconsistent fact. */
    private static void assertEmittersReject(String what,
            ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> registries,
            HostDeclarationSurface surface, String expectedText) {
        try {
            LuaSemanticEmitter.emitProductionProject(project, tables, registries,
                surface);
            fail(what + ": the LuaJIT emitter rejects the inconsistent fact");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && rejection.getMessage().contains(expectedText),
                what + ": the LuaJIT rejection names the defect: "
                    + rejection.getMessage());
        }
        try {
            JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                "Probe", surface);
            fail(what + ": the JVM emitter rejects the inconsistent fact");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && rejection.getMessage().contains(expectedText),
                what + ": the JVM rejection names the defect: "
                    + rejection.getMessage());
        }
    }

    // =========================================================================
    // The drivers, the trace decode, and the process helpers
    // =========================================================================

    private record Outcome(int exitCode, String stdout, String stderr) {
    }

    private record TraceRun(List<String> events, SemanticRuntimeModel.Terminal terminal) {
    }

    private static List<String> traceLines(SemanticRuntimeModel.ConsumerRun run) {
        List<String> lines = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            lines.add(event.text());
        }
        return lines;
    }

    /**
     * Drops the dependency modules' own init-walk prefix from one project
     * trace: the artifact's {@code __dealMain} runs the whole closure's
     * module walks while the oracle's async-entry surface initializes the
     * entry unit only, so the entry module's {@code MODULE_INIT} START is
     * the alignment point (every earlier event belongs to a dependency
     * module's init subtree).
     */
    private static List<String> dropDependencyInitPrefix(List<String> events) {
        for (int i = 0; i < events.size(); i++) {
            String[] fields = events.get(i).split("\\|", -1);
            if (fields.length >= 5 && fields[1].equals(APP.path())
                    && fields[3].equals("START")
                    && fields[4].equals("MODULE_INIT")) {
                return List.copyOf(events.subList(i, events.size()));
            }
        }
        fail("the project trace carries no entry-module MODULE_INIT start");
        return List.copyOf(events);
    }

    /** Decodes one artifact's protocol stream (trace events and terminal). */
    private static TraceRun decodeTrace(String stderr) {
        List<String> events = new ArrayList<>();
        SemanticRuntimeModel.Terminal terminal = null;
        for (String line : stderr.split("\n", -1)) {
            if (line.isEmpty()) {
                continue;
            }
            Object decoded = SemanticTraceProtocol.decode(line);
            if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                events.add(event.text());
            } else if (decoded instanceof SemanticRuntimeModel.EffectEvent) {
                // The async effects stay out of the event comparison (the
                // differential harness compares them; this drive has none).
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
        return new TraceRun(List.copyOf(events), terminal);
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
    private static String jvmAsyncEntryDriver(String driverClass, String className,
            OpId entry) {
        return """
            final class %s {
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
            """.formatted(driverClass, className, className, entry.id());
    }

    /** The LuaJIT sync probe: the walk, then the exported corpus probe. */
    private static String luaSyncProbeDriver(Path artifact, String module,
            String export) {
        return """
            local surfaces = dofile("%s")
            assert(type(surfaces) == "table",
              "the production chunk returns the entry surface")
            local probe = surfaces["%s"]
            assert(type(probe) == "table" and probe.__kind == "function"
              and type(probe.f) == "function",
              "the entry surface publishes the corpus probe")
            probe.f()
            """.formatted(artifact.toAbsolutePath().toString(), export);
    }

    /** The JVM sync probe: the walk, then the exported corpus probe. */
    private static String jvmSyncProbeDriver(String className, String module,
            String export) {
        return """
            public final class SyncProbe {
              public static void main(String[] args) {
                %s.main(new String[0]);
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.EXPORT_SURFACES.get("%s");
                Object probe = surface.read("%s");
                if (!(probe instanceof deal.codegen.jvm.JvmRuntime.FunctionValue fn)) {
                  throw new IllegalStateException(
                      "the entry surface publishes the corpus probe");
                }
                fn.fn.invoke(new Object[0]);
              }
            }
            """.formatted(className, className, module, export);
    }

    private static String opKeyText(OpId opId) {
        return opId.module().path() + "#" + opId.id();
    }

    private static OpId opIdOf(String opKey) {
        int hash = opKey.lastIndexOf('#');
        if (hash < 0) {
            return null;
        }
        return new OpId(new ModuleId(opKey.substring(0, hash)),
            Long.parseLong(opKey.substring(hash + 1)));
    }

    private static String corpusSource(Path corpus, String relative) throws Exception {
        String text = Files.readString(corpus.resolve(relative),
            StandardCharsets.UTF_8);
        StringBuilder stripped = new StringBuilder();
        for (String line : text.split("\n", -1)) {
            if (line.startsWith("// @")) {
                continue;
            }
            stripped.append(line).append('\n');
        }
        return stripped.toString();
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
        Path stderrFile = Files.createTempFile("cross-module-async-err", ".txt");
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new Outcome(exit, stdout, stderr);
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

    private static String luaString(String text) {
        StringBuilder literal = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> literal.append("\\\"");
                case '\\' -> literal.append("\\\\");
                case '\n' -> literal.append("\\n");
                default -> literal.append(c);
            }
        }
        return literal.append('"').toString();
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
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

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Cross-Module Async Realization Tests "
            + "(ISSUE-0655) ===\n");
        testEntrySetAndTokenLinkage();
        testEmissionSurface();
        testProductionDrives();
        testDifferentialParityAndModuleContext();
        testFailClosedSeeds();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Cross-Module Async Realization Tests Passed ===");
    }
}
