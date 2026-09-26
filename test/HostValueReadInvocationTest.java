package deal.test;

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
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
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
import deal.semantic.ir.ValueId;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0653: the host value-position export read invocation (design source
 * {@code host-module-load-and-host-call-realization} H5 and the host
 * value-read invocation contract; {@code semantic-ir-construct-coverage-
 * cutover} K2's exactly-one {@code HostFunction} registration;
 * {@code module-export-reads-and-in-project-class-construction} M1/M5 —
 * read-only).
 *
 * <ol>
 *   <li><b>The lowering of both forms.</b> {@code let f: (…) => … =
 *       host.<export>; f(args)} lowers through the reads child's exactly
 *       one {@code EXPORT_READ} (per source occurrence) plus its exactly
 *       one {@code HostFunction} registration, and the invocation is the
 *       static {@code CALL(INDIRECT)} arm whose {@code CallCallee.Static}
 *       binding is that registration: the closed host cells
 *       ({@code DEAL_TO_HOST}+{@code HOST_PARAMETER} per argument,
 *       {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} on the call), the
 *       same cells, descriptors, policies, and origins the direct
 *       {@code CALL(HOST)} of the same export carries. The async form
 *       ({@code let op: async () => string = host.fetchValue; await op()})
 *       takes the static {@code ASYNC_START(HOST)} arm on the same
 *       binding (the host operation label, the {@code HOST_OPERATION}
 *       token owner, the {@code ASYNC_OPERATION_HANDLE} terminal, zero
 *       return boundaries) with the single {@code AWAIT} +
 *       {@code ASYNC_COMPLETION}. Neither form produces or uses a
 *       {@code CallCallee.Dynamic} shape, and the read is consumed, never
 *       re-produced or re-registered.</li>
 *   <li><b>The sync drive on both targets.</b> The drive project executes
 *       under {@code luajit} and under {@code javac --release 25
 *       -proc:none} + {@code java} through the production emission, with
 *       the host implementation deployed: the read publishes the loaded
 *       surface entry, the invocation resolves that entry by
 *       {@code (hostModuleId, exportName)}, and the host runs once per
 *       call.</li>
 *   <li><b>The async drive on both targets.</b> The passing form
 *       ({@code host/async_ok}'s declared {@code fetchValue} read into an
 *       async-typed binding and awaited through the read) completes with
 *       the declared value; the corpus fixture
 *       {@code host-abi/host-async-shape-value} produces its pinned
 *       call-site E8010 (line 10 column 31) through the same static
 *       route.</li>
 *   <li><b>The oracle.</b> Both drive projects execute through the oracle
 *       with the seamed loaded surface entry and the same terminals, and
 *       the trace-mode artifacts agree event-for-event on both
 *       targets.</li>
 *   <li><b>The loaded host entry's own row (the correction this drive
 *       exposed).</b> The LuaJIT read publishes the loaded surface entry
 *       itself (the host ABI wrapper {@code {__kind = "function", sig,
 *       f}}, the value the direct host call invokes through {@code .f}),
 *       so the function row accepts it by the entry's own declared
 *       canonical signature: every boundary whose descriptor carries a
 *       function position emits the descriptor's canonical spec text
 *       beside the DEAL carrier's internal spelling, non-function checks
 *       keep the three-argument form, and an entry whose declared
 *       signature differs fails with the canonical E8010 projection. The
 *       oracle's closed value model carries the loaded entry
 *       ({@code SemanticOracle.Value.HostEntryValue}), so the read
 *       crosses the same row on all three consumers.</li>
 *   <li><b>The host load and its pinned E8011 checks.</b> The emitted
 *       chunk loads the host module once per program, and a drive whose
 *       loaded table is missing a declared export fails with the pinned
 *       E8011 at the import origin (the load check holds in the
 *       value-position drives too).</li>
 *   <li><b>Fail-closed seeds.</b> A read whose registration names no
 *       loaded module is a producer defect: the emission fails closed
 *       (never a silent call), and the emitted artifact names the module
 *       identity so the unloaded surface cannot be mistaken for a loaded
 *       one.</li>
 * </ol>
 *
 * <p>The reads child's {@code EXPORT_READ} surface is consumed, never
 * forked: the emitted read is the landed
 * {@code __exportHostValue(<module>, <name>)} accessor in both modes, one
 * read per source occurrence, and its exactly-one {@code HostFunction}
 * registration is the binding the invocation consumes — the correction
 * lives in the host surface's own row (the loaded entry and its declared
 * canonical signature), never in a re-produced read.</p>
 */
public class HostValueReadInvocationTest {

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
        testSyncLoweringShape();
        testAsyncLoweringShape();
        testDirectCallParity();
        testHostEntryRowAndMismatchSeed();
        testSyncDrives();
        testAsyncDrives();
        testOracleAgreement();
        testLoadAndFailClosedSeeds();
        System.out.println();
        System.out.println("Passes: " + passed + ", failures: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Host Value-Position Read Invocation Tests Passed ===");
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    private static final String SYNC_DECLARATION = """
        export function greet(name: string): string;
        export function add(a: int, b: int): int;
        """;

    /** The sync value-position form: both declared exports read, then invoked. */
    private static final String SYNC_SOURCE = """
        import * as host from "host/read_sync"

        export function test_read_value_sync(): string {
          let say: (name: string) => string = host.greet;
          let combine: (a: int, b: int) => int = host.add;
          let greeted: string = say("world");
          let total: int = combine(20, 22);
          if (greeted !== "hello world") {
            throw { code: "TEST_FAIL", message: "value-position host read" };
          }
          if (total !== 42) {
            throw { code: "TEST_FAIL", message: "value-position host read (two positions)" };
          }
          return greeted;
        }

        export function main(): null {
          return null;
        }
        """;

    /** The direct-call companion: the same export invoked as a direct host call. */
    private static final String DIRECT_SOURCE = """
        import * as host from "host/read_sync"

        export function test_direct_call(): string {
          let greeted: string = host.greet("world");
          let total: int = host.add(20, 22);
          if (greeted !== "hello world" || total !== 42) {
            throw { code: "TEST_FAIL", message: "direct host call" };
          }
          return greeted;
        }

        export function main(): null {
          return null;
        }
        """;

    /** The trace drive: the reads and invocations run on the entry path. */
    private static final String SYNC_TRACE_SOURCE = """
        import * as host from "host/read_sync"

        export function main(): null {
          let say: (name: string) => string = host.greet;
          let combine: (a: int, b: int) => int = host.add;
          let greeted: string = say("world");
          let total: int = combine(20, 22);
          if (greeted !== "hello world" || total !== 42) {
            throw { code: "TEST_FAIL", message: "trace drive mismatch" };
          }
          return null;
        }
        """;

    /** The deployed LuaJIT host of the sync drive (one load marker). */
    private static final String SYNC_HOST_LUA = """
        _READ_SYNC_LOADS = (_READ_SYNC_LOADS or 0) + 1
        return {
          greet = function(name) return "hello " .. name end,
          add = function(a, b) return a + b end,
        }
        """;

    /** The deployed JVM host of the sync drive. */
    private static final String SYNC_HOST_JAVA = """
        final class HostRead_sync {
          public static java.lang.String greet(java.lang.String name) {
            return "hello " + name;
          }

          public static int add(int a, int b) {
            return a + b;
          }
        }
        """;

    /** The corpus async host declaration used by the passing async drive. */
    private static final String ASYNC_OK_HOST_STEM = "async_ok";

    /** The passing async value-position form over the corpus {@code async_ok} host. */
    private static final String ASYNC_SOURCE = """
        import * as host from "host/async_ok"

        export async function test_read_value_async(): string {
          let op: async () => string = host.fetchValue;
          let fetched: string = await op();
          return fetched;
        }

        export function main(): null {
          return null;
        }
        """;

    /** The corpus async value-position fixture (its sidecar pins the E8010). */
    private static final String ASYNC_SHAPE_VALUE = "host-async-shape-value";

    private static final String ASYNC_SHAPE_HOST_STEM = "async_shape_bad";

    // =========================================================================
    // The compile harness (the landed project lowering entry)
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
        Path root = Files.createTempDirectory("host-value-read-fixture");
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
            throw new IllegalStateException("the fixture '" + name
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
            deal.checker.BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    // =========================================================================
    // The IR readers
    // =========================================================================

    private static LoweredModuleUnit entryUnit(ExecutableLoweredProject project) {
        return project.modules().get(project.entryModule());
    }

    /** The single HOST module import of the entry unit. */
    private static ModuleId hostImportModule(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT
                    && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                        == ModuleImportKind.HOST) {
                return ((KindPayload.ModuleImportPayload) op.payload()).resolvedModule();
            }
        }
        throw new IllegalStateException("the fixture carries no host import");
    }

    private static List<SemanticOp> opsOfKind(LoweredModuleUnit unit,
            SemanticOpKind kind) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                ops.add(op);
            }
        }
        return ops;
    }

    /** The registered binding of one value identity, or null. */
    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit,
            ValueId value) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
    }

    /** The unit's import registrations (HostFunction/ExternalFunction). */
    private static List<FunctionExecutionBinding> importRegistrations(
            LoweredModuleUnit unit) {
        List<FunctionExecutionBinding> imports = new ArrayList<>();
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.HostFunction
                    || binding instanceof FunctionExecutionBinding.ExternalFunction) {
                imports.add(binding);
            }
        }
        return imports;
    }

    /** Whether the closure produces any dynamic callee anywhere. */
    private static boolean carriesDynamicCallee(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                KindPayload payload = op.payload();
                if (payload instanceof KindPayload.CallPayload call
                        && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                    return true;
                }
                if (payload instanceof KindPayload.AsyncStartPayload start
                        && start.callee() instanceof KindPayload.CallCallee.Dynamic) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether the closure registers any host-materialized function value. */
    private static boolean carriesHostFunctionValue(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
                if (binding instanceof FunctionExecutionBinding.HostFunctionValue) {
                    return true;
                }
            }
        }
        return false;
    }

    private static String spanOf(SemanticOp op) {
        return op.origin().span().startLine() + ":" + op.origin().span().startColumn();
    }

    // =========================================================================
    // 1. The sync form's lowering shape
    // =========================================================================

    private static void testSyncLoweringShape() throws Exception {
        System.out.println("-- the sync value-position read: one read per occurrence, "
            + "one HostFunction registration each, the static CALL(INDIRECT) consumes it --");
        Fixture compiled = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the sync value-position form lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            check(!carriesDynamicCallee(project), "the sync value-position drive produces "
                + "no CallCallee.Dynamic shape");
            check(!carriesHostFunctionValue(project), "the sync value-position drive "
                + "registers no HostFunctionValue (the read consumer is the static "
                + "HostFunction registration)");
            LoweredModuleUnit unit = entryUnit(project);
            ModuleId hostModule = hostImportModule(unit);

            List<SemanticOp> reads = opsOfKind(unit, SemanticOpKind.EXPORT_READ);
            checkEq(2, reads.size(), "the sync drive carries exactly one EXPORT_READ per "
                + "read occurrence (two occurrences; an invocation never re-produces a read)");
            List<FunctionExecutionBinding> registrations = importRegistrations(unit);
            checkEq(2, registrations.size(), "the sync drive carries exactly one import "
                + "registration per function-typed read (got " + registrations + ")");

            Map<String, FunctionExecutionBinding> byExport = new LinkedHashMap<>();
            for (SemanticOp read : reads) {
                KindPayload.ExportReadPayload payload =
                    (KindPayload.ExportReadPayload) read.payload();
                checkEq(hostModule, payload.module(),
                    "the read names the loaded host module");
                FunctionExecutionBinding binding = bindingOf(unit, payload.value());
                check(binding instanceof FunctionExecutionBinding.HostFunction host
                        && host.hostModuleId().equals(hostModule)
                        && host.exportName().equals(payload.name())
                        && host.descriptor().equals(payload.descriptor()),
                    "exactly one HostFunction(resolved module, export, descriptor) "
                        + "registration is keyed by the read result's allocation identity "
                        + "for '" + payload.name() + "'; got " + binding);
                byExport.put(payload.name(), binding);
            }
            check(byExport.keySet().equals(Set.of("greet", "add")),
                "the reads name the declared exports (got " + byExport.keySet() + ")");

            // The invocations: static CALL(INDIRECT) on the read registrations
            // with the closed host cells (the entry-delegation CALL of the
            // module's own main body is not a host invocation).
            List<SemanticOp> calls = new ArrayList<>();
            for (SemanticOp op : opsOfKind(unit, SemanticOpKind.CALL)) {
                KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
                if (payload.callee() instanceof KindPayload.CallCallee.Static staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction) {
                    calls.add(op);
                }
            }
            checkEq(2, calls.size(), "the sync drive carries exactly two host CALL ops "
                + "(one per invocation; the reads are not calls)");
            List<FunctionExecutionBinding> consumed = new ArrayList<>();
            for (SemanticOp call : calls) {
                KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
                checkEq(CallMode.INDIRECT, payload.mode(),
                    "the invocation is a CALL(INDIRECT)");
                check(payload.callee() instanceof KindPayload.CallCallee.Static,
                    "the invocation's callee is statically resolved; got "
                        + payload.callee());
                if (!(payload.callee() instanceof KindPayload.CallCallee.Static staticCallee)) {
                    continue;
                }
                FunctionExecutionBinding binding = staticCallee.binding();
                check(binding instanceof FunctionExecutionBinding.HostFunction,
                    "the invocation consumes a HostFunction binding; got " + binding);
                consumed.add(binding);
                checkEq(binding instanceof FunctionExecutionBinding.HostFunction host
                        ? host.descriptor().paramTypes().size() : -1,
                    payload.parameterBoundaryOpIds().size(),
                    "the invocation carries one parameter boundary per declared "
                        + "parameter");
                for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                    SemanticOp boundary = unit.ops().stream()
                        .filter(op -> op.opId().equals(boundaryId)).findFirst()
                        .orElseThrow();
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) boundary.payload();
                    checkEq(BoundaryKind.DEAL_TO_HOST, boundaryPayload.kind(),
                        "the parameter cell is the host DEAL_TO_HOST boundary");
                    checkEq(FailurePolicyId.HOST_PARAMETER, boundary.failurePolicy(),
                        "the parameter cell carries the HOST_PARAMETER policy");
                    checkEq(call.opId(), boundary.origin().parentOpId(),
                        "the parameter cell is parented to the call op");
                }
                SemanticOp returnBoundary = unit.ops().stream()
                    .filter(op -> op.opId().equals(payload.returnBoundaryOpId()))
                    .findFirst().orElse(null);
                check(returnBoundary != null, "the invocation carries its declared "
                    + "return cell");
                if (returnBoundary != null) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) returnBoundary.payload();
                    checkEq(BoundaryKind.HOST_TO_DEAL, boundaryPayload.kind(),
                        "the return cell is the host HOST_TO_DEAL boundary");
                    checkEq(FailurePolicyId.HOST_SYNC_RETURN, returnBoundary.failurePolicy(),
                        "the return cell carries the HOST_SYNC_RETURN policy");
                    checkEq(call.opId(), returnBoundary.origin().parentOpId(),
                        "the return cell is parented to the call op");
                }
            }
            check(consumed.containsAll(byExport.values()) && consumed.size() == 2,
                "the invocations consume exactly the read's registrations (the read is "
                    + "never re-produced or re-registered); reads=" + byExport.values()
                    + " consumed=" + consumed);
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 2. The async form's lowering shape
    // =========================================================================

    private static void testAsyncLoweringShape() throws Exception {
        System.out.println("-- the async value-position read (host-abi/host-async-shape-value): "
            + "the static ASYNC_START(HOST) arm on the read's registration --");
        Fixture compiled = compileWith("host-async-shape-value", ASYNC_SHAPE_HOST_STEM,
            Files.readString(Path.of("test/conformance/host-fixtures/"
                + ASYNC_SHAPE_HOST_STEM + ".d.deal"), StandardCharsets.UTF_8),
            Files.readString(Path.of("test/conformance/backend-runtime/host-abi/"
                + ASYNC_SHAPE_VALUE + ".deal"), StandardCharsets.UTF_8));
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the async value-position fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            check(!carriesDynamicCallee(project), "the async value-position drive "
                + "produces no CallCallee.Dynamic shape");
            check(!carriesHostFunctionValue(project), "the async value-position drive "
                + "registers no HostFunctionValue");
            LoweredModuleUnit unit = entryUnit(project);
            ModuleId hostModule = hostImportModule(unit);

            List<SemanticOp> reads = opsOfKind(unit, SemanticOpKind.EXPORT_READ);
            checkEq(1, reads.size(), "the async drive carries exactly one EXPORT_READ");
            if (reads.size() != 1) {
                return;
            }
            KindPayload.ExportReadPayload read =
                (KindPayload.ExportReadPayload) reads.get(0).payload();
            checkEq("fetchValue", read.name(), "the read names the declared async export");
            FunctionExecutionBinding readBinding = bindingOf(unit, read.value());
            check(readBinding instanceof FunctionExecutionBinding.HostFunction host
                    && host.exportName().equals("fetchValue")
                    && host.descriptor().equals(read.descriptor()),
                "exactly one HostFunction registration is keyed by the read result; got "
                    + readBinding);

            List<SemanticOp> starts = opsOfKind(unit, SemanticOpKind.ASYNC_START);
            checkEq(1, starts.size(), "the async drive carries exactly one ASYNC_START");
            if (starts.size() != 1) {
                return;
            }
            SemanticOp start = starts.get(0);
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) start.payload();
            checkEq(AsyncStartSource.HOST, payload.source(),
                "the async start takes the static HOST source");
            check(payload.callee() instanceof KindPayload.CallCallee.Static staticCallee
                    && staticCallee.binding().equals(readBinding),
                "the async start consumes the read's registration statically; got "
                    + payload.callee());
            checkEq(hostModule.path() + ".fetchValue", payload.hostOperationLabel(),
                "the async start carries the landed host operation label");
            checkEq(FailurePolicyId.ASYNC_OPERATION_HANDLE, start.failurePolicy(),
                "the async start carries the ASYNC_OPERATION_HANDLE terminal");
            checkEq(List.of(), payload.parameterBoundaryOpIds(),
                "the zero-arity host export has no parameter boundaries");
            check(payload.returnBoundaryOpId() == null,
                "a host async start records no return boundary (the shape check is the "
                    + "op's own terminal)");
            check(start.result() instanceof AsyncTokenId.Canonical token
                    && token.owner() == AsyncTokenOwner.HOST_OPERATION,
                "the token is the canonical HOST_OPERATION token; got " + start.result());
            checkEq(10, Integer.valueOf(spanOf(start).split(":")[0])
                    + compiled.headerLinesStripped,
                "the async start carries the call expression's corpus origin line (10)");
            checkEq(31, Integer.valueOf(spanOf(start).split(":")[1]),
                "the async start carries the call expression's origin column (31)");

            List<SemanticOp> awaits = opsOfKind(unit, SemanticOpKind.AWAIT);
            checkEq(1, awaits.size(), "the async drive carries exactly one AWAIT");
            if (awaits.size() == 1) {
                SemanticOp await = awaits.get(0);
                KindPayload.AwaitPayload awaitPayload =
                    (KindPayload.AwaitPayload) await.payload();
                checkEq(start.result(), awaitPayload.token(),
                    "the AWAIT consumes the start's canonical token");
                SemanticOp completion = unit.ops().stream()
                    .filter(op -> op.opId().equals(awaitPayload.completionBoundaryOpId()))
                    .findFirst().orElse(null);
                check(completion != null
                        && ((KindPayload.BoundaryPayload) completion.payload()).kind()
                            == BoundaryKind.ASYNC_COMPLETION,
                    "the AWAIT carries the single ASYNC_COMPLETION boundary");
            }
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 3. The direct-call parity (the same cells, texts, and effects)
    // =========================================================================

    private static void testDirectCallParity() throws Exception {
        System.out.println("-- the indirect host invocation resolves the same surface "
            + "entry with the same cells as the direct CALL(HOST) --");
        Fixture read = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_SOURCE);
        Fixture direct = compileSource("host-direct-sync", "read_sync",
            SYNC_DECLARATION, DIRECT_SOURCE);
        Path readSpace = Files.createTempDirectory("host-read-parity");
        Path directSpace = Files.createTempDirectory("host-direct-parity");
        try {
            SemanticLowerer.ProjectLoweringResult readResult = lower(read);
            SemanticLowerer.ProjectLoweringResult directResult = lower(direct);
            if (readResult.project() == null || directResult.project() == null) {
                fail("the parity fixtures lower: " + readResult.diagnostics() + " / "
                    + directResult.diagnostics());
                return;
            }
            String readLua = LuaSemanticEmitter.emitProductionProject(readResult.project(),
                readResult.tables(), readResult.registries(), read.surface());
            String directLua = LuaSemanticEmitter.emitProductionProject(
                directResult.project(), directResult.tables(), directResult.registries(),
                direct.surface());
            String readJava = JvmSemanticEmitter.emitProductionProject(readResult.project(),
                readResult.tables(), readResult.registries(),
                JvmBackend.classNameFor(readResult.project().entryModule().path()),
                read.surface()).source();
            String directJava = JvmSemanticEmitter.emitProductionProject(
                directResult.project(), directResult.tables(), directResult.registries(),
                JvmBackend.classNameFor(directResult.project().entryModule().path()),
                direct.surface()).source();

            // The LuaJIT arm: both forms invoke the module-keyed surface entry
            // through the loaded wrapper's `.f` convention with the same target.
            checkEq(1, occurrences(readLua,
                "pcall(__exportSurfaces[\"host.read_sync\"][\"greet\"].f"),
                "the read form invokes the loaded surface entry through the host call "
                    + "shape");
            checkEq(1, occurrences(directLua,
                "pcall(__exportSurfaces[\"host.read_sync\"][\"greet\"].f"),
                "the direct form invokes the same loaded surface entry");
            checkEq(occurrences(readLua, "__rt.load_host(\"host/read_sync\""),
                occurrences(directLua, "__rt.load_host(\"host/read_sync\""),
                "both forms emit the same single host load");
            checkEq(1, occurrences(readLua, "__rt.load_host(\"host/read_sync\""),
                "the emitted chunk loads the host module exactly once per program");
            check(readLua.contains("__exportHostValue(\"host.read_sync\", \"greet\")"),
                "the read publishes the loaded surface entry (the HOST read arm)");
            check(occurrences(readLua, "= __intrinsicFn(") <= 2,
                "the read arm emits no intrinsic carrier for the host reads "
                    + "(only the intrinsic seed bindings carry one)");
            for (SemanticOp readOp : opsOfKind(entryUnit(readResult.project()),
                    SemanticOpKind.EXPORT_READ)) {
                KindPayload.ExportReadPayload readPayload =
                    (KindPayload.ExportReadPayload) readOp.payload();
                String readLine = "S.v" + readPayload.value().id()
                    + " = __exportHostValue(\"" + readPayload.module().path()
                    + "\", \"" + readPayload.name() + "\")";
                checkEq(1, occurrences(readLua, readLine),
                    "the read publishes the loaded surface entry: " + readLine);
            }

            // The JVM arm: the same per-export wrapper, the same read surface.
            checkEq(occurrences(directJava, "__host$host$iread$usync$greet("),
                occurrences(readJava, "__host$host$iread$usync$greet("),
                "the read form invokes the emitted per-export wrapper exactly like "
                    + "the direct form");
            check(occurrences(readJava, "__host$host$iread$usync$greet(") >= 2,
                "the emitted per-export wrapper exists and is invoked");
            check(readJava.contains(
                    "exportSurface(\"host.read_sync\").read(\"greet\")"),
                "the read resolves the loaded module's surface entry");
            check(!readJava.contains("HOST_ASYNC"),
                "the read drive's artifact references no deterministic host seam");

            // The IR parity: the same declared cells and policies on both forms.
            LoweredModuleUnit readUnit = entryUnit(readResult.project());
            LoweredModuleUnit directUnit = entryUnit(directResult.project());
            checkEq(cellSignature(directUnit, "greet"), cellSignature(readUnit, "greet"),
                "the read form's host cells match the direct host call's cells "
                    + "(descriptors and policies)");
        } finally {
            deleteRecursively(readSpace);
            deleteRecursively(directSpace);
            deleteRecursively(read.root());
            deleteRecursively(direct.root());
        }
    }

    /** The declared cell descriptors+policies of one export's invocation, in op order. */
    private static List<String> cellSignature(LoweredModuleUnit unit, String exportName) {
        List<String> cells = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.CALL) {
                continue;
            }
            KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
            FunctionExecutionBinding binding = payload.callee()
                instanceof KindPayload.CallCallee.Static staticCallee
                    ? staticCallee.binding() : null;
            if (!(binding instanceof FunctionExecutionBinding.HostFunction host)
                    || !host.exportName().equals(exportName)) {
                continue;
            }
            cells.add("signature=" + payload.signature().canonicalSpecText());
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = unit.ops().stream()
                    .filter(candidate -> candidate.opId().equals(boundaryId)).findFirst()
                    .orElseThrow();
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                cells.add("param " + boundaryPayload.descriptor().canonicalSpecText()
                    + " " + boundaryPayload.kind() + " " + boundary.failurePolicy());
            }
            for (SemanticOp boundary : unit.ops()) {
                if (boundary.opId().equals(payload.returnBoundaryOpId())) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) boundary.payload();
                    cells.add("return " + boundaryPayload.descriptor().canonicalSpecText()
                        + " " + boundaryPayload.kind() + " " + boundary.failurePolicy());
                }
            }
        }
        return cells;
    }

    private static int occurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + needle.length());
        }
        return count;
    }

    // =========================================================================
    // 3b. The loaded host entry's own row (the host ABI wrapper acceptance)
    // =========================================================================

    /**
     * The LuaJIT function row's host-entry arm: the emitted check of a
     * descriptor carrying a function position rides the descriptor's
     * canonical spec text along (the loaded entry's own metadata), every
     * non-function check keeps the three-argument form, and a seeded
     * surface entry whose declared signature differs fails with the
     * canonical E8010 projection — the counterpart of the JVM load's
     * carried {@code signature}/{@code spec} pair. The oracle's loaded
     * entry value crosses the same row (the drives above assert it).
     */
    private static void testHostEntryRowAndMismatchSeed() throws Exception {
        System.out.println("-- the loaded host entry's own row: the canonical signature rides "
            + "along, and a mismatched entry fails with the canonical E8010 --");
        Fixture compiled = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_SOURCE);
        Path workspace = Files.createTempDirectory("host-value-read-row");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the row seed fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String chunk = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), compiled.surface());
            LoweredModuleUnit unit = entryUnit(project);
            List<SemanticOp> reads = opsOfKind(unit, SemanticOpKind.EXPORT_READ);
            checkEq(2, reads.size(), "the row seed carries both reads");
            for (SemanticOp read : reads) {
                KindPayload.ExportReadPayload payload =
                    (KindPayload.ExportReadPayload) read.payload();
                RuntimeDescriptor.Func descriptor =
                    (RuntimeDescriptor.Func) payload.descriptor();
                // The declaration crossing's free-boundary arm runs the check
                // through the prelude pcall form with the boundary's own origin
                // (ISSUE-0681): the canonical trailer rides along unchanged.
                checkEq(1, occurrences(chunk, "pcall(__bcheck, " + luaStringFmt(
                        descriptorTextOf(descriptor)) + ", \"function\", S.v"
                        + payload.value().id() + ", "
                        + luaStringFmt(descriptor.canonicalSpecText()) + ")"),
                    "the emitted function row of '" + payload.name()
                        + "' carries the declared canonical signature beside the "
                        + "host entry's own metadata");
            }
            check(occurrences(chunk, "pcall(__bcheck, \"string\", \"string\", S.v") >= 1
                    || occurrences(chunk, "__bcheck(\"string\", \"string\", S.v") >= 1,
                "the ordinary checks keep the three-argument emitted form");
            check(!java.util.regex.Pattern.compile(
                    "__bcheck[,(] ?\\\"string\\\", \\\"string\\\", [^,)]+, "
                        + "\\\"string\\\"\\)").matcher(chunk).find(),
                "a non-function check emits no canonical trailer");

            // The seeded mismatch: the loaded surface entry carries a
            // different declared signature, so the read's declaration row
            // fails with the canonical projection.
            String seeded = chunk.replaceAll(
                "__exportSurfaces\\[\\\"host\\.read_sync\\\"\\] = "
                    + "__exportSurfaces\\[\\\"host\\.read_sync\\\"\\] or "
                    + "__rt\\.load_host\\([^\\n]*\\)\\n",
                java.util.regex.Matcher.quoteReplacement(SEEDED_SURFACE + "\n"));
            check(!seeded.equals(chunk), "the mismatch seed replaces the host load");
            if (!seeded.equals(chunk) && reads.size() == 2) {
                Path artifact = workspace.resolve("project-seeded.lua");
                Files.writeString(artifact, seeded, StandardCharsets.UTF_8);
                deployRuntime(workspace);
                Path hostTarget = workspace.resolve("host/read_sync.lua");
                Files.createDirectories(hostTarget.getParent());
                Files.writeString(hostTarget, "return {}\n", StandardCharsets.UTF_8);
                Path probe = workspace.resolve("probe-seeded.lua");
                Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome outcome = runLua(probe, workspace);
                // The materialization site's own origin: the `say` declaration's
                // annotation span (line 4, column 12 of the entry source) —
                // ISSUE-0681's declared-annotation origin.
                checkEq("ERR:E8010|function signature mismatch: expected (string)->string, "
                        + "got (int)->int|" + compiled.root()
                            .resolve("src/host-read-sync.deal").toAbsolutePath()
                        + ":4:12|(string)->string|(int)->int",
                    outcome.value(),
                    "a host entry whose declared signature differs fails with the "
                        + "canonical projection at the declared annotation's span "
                        + "(stderr=" + escaped(outcome.stderr()) + ")");
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** The seeded loaded surface: an entry whose declared signature differs. */
    private static final String SEEDED_SURFACE =
        "__exportSurfaces[\"host.read_sync\"] = { greet = {__kind = \"function\", "
            + "sig = \"(int)->int\", f = function() return 1 end}, "
            + "add = {__kind = \"function\", sig = \"(int,int)->int\", "
            + "f = function(a, b) return a + b end} }";

    /** The prelude's internal descriptor text (the boundary check's desc). */
    private static String descriptorTextOf(RuntimeDescriptor descriptor) {
        if (descriptor instanceof RuntimeDescriptor.Func func) {
            StringBuilder params = new StringBuilder();
            for (RuntimeDescriptor param : func.paramTypes()) {
                if (params.length() > 0) {
                    params.append(',');
                }
                params.append(descriptorTextOf(param));
            }
            return "function(" + params + ";" + descriptorTextOf(func.returnType()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable(" + descriptorTextOf(nullable.inner()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Array array) {
            return "array(" + descriptorTextOf(array.element()) + ")";
        }
        return descriptor.canonicalSpecText();
    }

    /** One emitted Lua string literal of one text. */
    private static String luaStringFmt(String text) {
        return "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    // =========================================================================
    // 4. The sync drive under the real toolchains
    // =========================================================================

    private static void testSyncDrives() throws Exception {
        System.out.println("-- the sync value-position read under luajit and javac/java --");
        Fixture compiled = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_SOURCE);
        Path workspace = Files.createTempDirectory("host-value-read-sync");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the sync drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();

            // (a) LuaJIT.
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path hostTarget = workspace.resolve("host/read_sync.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.writeString(hostTarget, SYNC_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(probe, workspace);
            checkEq("OK", luaOutcome.value(),
                "the LuaJIT sync value-position read executes through the loaded surface "
                    + "entry (the deployed host's load marker counted exactly one load); "
                    + "stderr=" + escaped(luaOutcome.stderr()));

            // (b) JVM.
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostRead_sync.java"),
                SYNC_HOST_JAVA, StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("SyncReadProbe.java"),
                jvmDriver("SyncReadProbe", className, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostRead_sync.java", "SyncReadProbe.java"),
                workspace);
            check(javacRun.exitCode() == 0, "the sync drive compiles under javac: "
                + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "SyncReadProbe"),
                    workspace);
                checkEq("OK", jvmOutcome.value(),
                    "the JVM sync value-position read executes through the emitted "
                        + "wrapper; stderr=" + escaped(jvmOutcome.stderr()));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 5. The async drive under the real toolchains
    // =========================================================================

    private static void testAsyncDrives() throws Exception {
        System.out.println("-- the async value-position read under luajit and "
            + "javac/java (the passing form and the pinned corpus shape failure) --");
        // (a) The passing form over the corpus async_ok host.
        String asyncOkDeclaration = Files.readString(
            Path.of("test/conformance/host-fixtures/async_ok.d.deal"),
            StandardCharsets.UTF_8);
        Fixture passing = compileSource("host-read-async", ASYNC_OK_HOST_STEM,
            asyncOkDeclaration, ASYNC_SOURCE);
        Path workspace = Files.createTempDirectory("host-value-read-async");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(passing);
            if (result.project() == null) {
                fail("the passing async drive lowers: " + result.diagnostics());
            } else {
                ExecutableLoweredProject project = result.project();
                Path artifact = workspace.resolve("project.lua");
                Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                    project, result.tables(), result.registries(), passing.surface()),
                    StandardCharsets.UTF_8);
                deployRuntime(workspace);
                Path hostTarget = workspace.resolve("host/async_ok.lua");
                Files.createDirectories(hostTarget.getParent());
                Files.copy(Path.of("test/conformance/host-fixtures/async_ok.lua"),
                    hostTarget);
                Path probe = workspace.resolve("probe.lua");
                Files.writeString(probe, luaDriver(artifact, passing.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome luaOutcome = runLua(probe, workspace);
                checkEq("OK", luaOutcome.value(),
                    "the LuaJIT async value-position read completes through the host "
                        + "operation handle; stderr=" + escaped(luaOutcome.stderr()));

                String className = JvmBackend.classNameFor(project.entryModule().path());
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                        result.registries(), className, passing.surface());
                Files.writeString(workspace.resolve(className + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                check(!emission.source().contains("HOST_ASYNC"),
                    "the JVM async read artifact references no deterministic host seam");
                Files.writeString(workspace.resolve("HostAsync_ok.java"),
                    Files.readString(Path.of(
                        "test/conformance/host-fixtures/async_ok.java")),
                    StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("AsyncReadProbe.java"),
                    jvmDriver("AsyncReadProbe", className, passing.entryPath()),
                    StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java", "HostAsync_ok.java", "AsyncReadProbe.java"),
                    workspace);
                check(javacRun.exitCode() == 0, "the passing async drive compiles under "
                    + "javac: " + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() == 0) {
                    Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes,
                        "AsyncReadProbe"), workspace);
                    checkEq("OK", jvmOutcome.value(),
                        "the JVM async value-position read completes through the "
                            + "registered host operation; stderr="
                            + escaped(jvmOutcome.stderr()));
                }
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(passing.root());
        }

        // (b) The corpus pinned failure through the same static route.
        Fixture pinned = compileWith(ASYNC_SHAPE_VALUE, ASYNC_SHAPE_HOST_STEM,
            Files.readString(Path.of("test/conformance/host-fixtures/"
                + ASYNC_SHAPE_HOST_STEM + ".d.deal"), StandardCharsets.UTF_8),
            Files.readString(Path.of("test/conformance/backend-runtime/host-abi/"
                + ASYNC_SHAPE_VALUE + ".deal"), StandardCharsets.UTF_8));
        Path pinnedSpace = Files.createTempDirectory("host-value-read-pinned");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(pinned);
            if (result.project() == null) {
                fail("the pinned async fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = pinnedSpace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), pinned.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(pinnedSpace);
            Path hostTarget = pinnedSpace.resolve("host/async_shape_bad.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.copy(Path.of("test/conformance/host-fixtures/async_shape_bad.lua"),
                hostTarget);
            Path probe = pinnedSpace.resolve("probe.lua");
            Files.writeString(probe, luaDriver(artifact, pinned.entryPath()),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(probe, pinnedSpace);
            assertPinnedShapeOutcome(luaOutcome, "luajit", pinned.headerLinesStripped());

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, pinned.surface());
            Files.writeString(pinnedSpace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(pinnedSpace.resolve("HostAsync_shape_bad.java"),
                Files.readString(Path.of(
                    "test/conformance/host-fixtures/async_shape_bad.java")),
                StandardCharsets.UTF_8);
            Files.writeString(pinnedSpace.resolve("PinnedReadProbe.java"),
                jvmDriver("PinnedReadProbe", className, pinned.entryPath()),
                StandardCharsets.UTF_8);
            Path classes = pinnedSpace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostAsync_shape_bad.java",
                "PinnedReadProbe.java"), pinnedSpace);
            check(javacRun.exitCode() == 0, "the pinned async fixture compiles under "
                + "javac: " + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "PinnedReadProbe"), pinnedSpace);
                assertPinnedShapeOutcome(jvmOutcome, "java", pinned.headerLinesStripped());
            }
        } finally {
            deleteRecursively(pinnedSpace);
            deleteRecursively(pinned.root());
        }
    }

    /** The corpus sidecar's pinned call-site shape-check outcome. */
    private static void assertPinnedShapeOutcome(Outcome outcome, String target,
            int headerLinesStripped) throws Exception {
        String sidecar = Files.readString(Path.of(
            "test/conformance/backend-runtime/host-abi/" + ASYNC_SHAPE_VALUE
                + ".expect.json"), StandardCharsets.UTF_8);
        checkEq("E8010", sidecarField(sidecar, "\"code\""),
            ASYNC_SHAPE_VALUE + " sidecar code");
        String expectedMessage = sidecarField(sidecar, "\"message\"");
        Integer expectedLine = sidecarNumber(sidecar, "\"line\"");
        Integer expectedColumn = sidecarNumber(sidecar, "\"column\"");
        check(outcome.value().startsWith("ERR:E8010|"),
            "the " + target + " async value-position read fails with the pinned E8010 "
                + "at the call expression: " + escaped(outcome.value()));
        if (!outcome.value().startsWith("ERR:E8010|")) {
            return;
        }
        String[] parts = outcome.value().substring(4).split("\\|", -1);
        checkEq(expectedMessage, parts[1],
            "the " + target + " shape check carries the pinned message");
        String origin = parts[2];
        int lastColon = origin.lastIndexOf(':');
        int prevColon = origin.lastIndexOf(':', lastColon - 1);
        checkEq(expectedLine,
            Integer.valueOf(origin.substring(prevColon + 1, lastColon))
                + headerLinesStripped,
            "the " + target + " pinned call-site origin line (the stripped source's "
                + "origin mapped back to the corpus line)");
        checkEq(expectedColumn, Integer.valueOf(origin.substring(lastColon + 1)),
            "the " + target + " pinned call-site origin column");
        checkEq("async operation", "-".equals(parts[3]) ? null : parts[3],
            "the " + target + " pinned expected descriptor");
        checkEq("number", "-".equals(parts[4]) ? null : parts[4],
            "the " + target + " pinned actual kind");
    }

    private static Integer sidecarNumber(String json, String key) {
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

    private static String sidecarField(String json, String key) {
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

    // =========================================================================
    // 6. The oracle and the trace-mode agreement
    // =========================================================================

    private record TraceRun(List<String> events, List<String> asyncEffects,
        SemanticRuntimeModel.Terminal terminal) {
    }

    /** The sync drive's seamed host: the loaded entry, the calls, the terminals. */
    private static SemanticOracle.HostResponder syncResponder() {
        return new SemanticOracle.HostResponder() {
            private final Map<String, SemanticOracle.Value> entries =
                new LinkedHashMap<>();

            @Override
            public SemanticOracle.Value loadedExport(ModuleId module, String export,
                    RuntimeDescriptor descriptor) {
                return entries.computeIfAbsent(module.path() + "." + export,
                    key -> descriptor instanceof RuntimeDescriptor.Func signature
                        ? new SemanticOracle.Value.HostEntryValue(signature)
                        : new SemanticOracle.Value.IntrinsicValue("host:" + key));
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                return switch (export) {
                    case "greet" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.StrValue(
                            "hello " + ((SemanticOracle.Value.StrValue) args.get(0))
                                .value()));
                    case "add" -> new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(
                            ((SemanticOracle.Value.IntValue) args.get(0)).value()
                                + ((SemanticOracle.Value.IntValue) args.get(1))
                                    .value()));
                    default -> throw new IllegalStateException("the sync drive scripts "
                        + "no host call for " + module.path() + "." + export);
                };
            }
        };
    }

    /** The async drive's seamed host: a real operation with the declared value. */
    private static SemanticOracle.HostResponder asyncResponder(String name) {
        return new SemanticOracle.HostResponder() {
            private final Map<String, SemanticOracle.Value> entries =
                new LinkedHashMap<>();

            @Override
            public SemanticOracle.Value loadedExport(ModuleId module, String export,
                    RuntimeDescriptor descriptor) {
                return entries.computeIfAbsent(module.path() + "." + export,
                    key -> descriptor instanceof RuntimeDescriptor.Func signature
                        ? new SemanticOracle.Value.HostEntryValue(signature)
                        : new SemanticOracle.Value.IntrinsicValue("host:" + key));
            }

            @Override
            public String startAsync(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args, String operationLabel) {
                return ASYNC_SHAPE_VALUE.equals(name) ? null : operationLabel;
            }

            @Override
            public SyncOutcome completeAsync(String operationLabel) {
                return new SyncOutcome.Returned(
                    new SemanticOracle.Value.StrValue("fetched"));
            }
        };
    }

    private static void testOracleAgreement() throws Exception {
        System.out.println("-- the oracle and the trace-mode artifacts agree "
            + "event-for-event on the value-position drives --");
        // (a) The sync drive.
        Fixture compiled = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_TRACE_SOURCE);
        Path workspace = Files.createTempDirectory("host-value-read-trace-sync");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the sync trace drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.executeProjectInits(project, result.tables(),
                    result.registries(), syncResponder());
            TraceRun oracle = traceOf(oracleRun);
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle's sync value-position drive succeeds: "
                    + terminalText(oracle.terminal()));

            Path luaArtifact = workspace.resolve("project.lua");
            Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(project,
                result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path hostTarget = workspace.resolve("host/read_sync.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.writeString(hostTarget, SYNC_HOST_LUA, StandardCharsets.UTF_8);
            Outcome luaOutcome = runProcess(List.of("luajit",
                luaArtifact.toAbsolutePath().toString()), workspace);
            check(luaOutcome.exitCode() == 0,
                "the sync trace drive runs under luajit: " + escaped(luaOutcome.stderr()));
            checkTraceParity("sync value read", "luajit", oracle,
                decodeTrace(luaOutcome.stderr()));

            JvmSemanticEmitter.EmissionResult jvmEmission =
                JvmSemanticEmitter.emitProject(project, result.tables(),
                    result.registries(), compiled.surface());
            String jvmClass = jvmEmission.className();
            Files.writeString(workspace.resolve(jvmClass + ".java"),
                jvmEmission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostRead_sync.java"),
                SYNC_HOST_JAVA, StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmClass + ".java", "HostRead_sync.java"), workspace);
            check(javacRun.exitCode() == 0, "the sync trace drive compiles under javac: "
                + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, jvmClass),
                    workspace);
                check(jvmOutcome.exitCode() == 0,
                    "the sync trace drive runs under java: exit="
                        + jvmOutcome.exitCode() + " " + escaped(jvmOutcome.stderr()));
                checkTraceParity("sync value read", "java", oracle,
                    decodeTrace(jvmOutcome.stderr()));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }

        // (b) The passing async drive.
        String asyncOkDeclaration = Files.readString(
            Path.of("test/conformance/host-fixtures/async_ok.d.deal"),
            StandardCharsets.UTF_8);
        Fixture async = compileSource("host-read-async", ASYNC_OK_HOST_STEM,
            asyncOkDeclaration, ASYNC_SOURCE);
        Path asyncSpace = Files.createTempDirectory("host-value-read-trace-async");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(async);
            if (result.project() == null) {
                fail("the async trace drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String export = exportNameOf(ASYNC_SOURCE);
            ModuleId entryModule = project.entryModule();
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.invokeAsyncEntry(project, result.tables(),
                    asyncResponder("host-async-ok"), entryModule, export, List.of());
            TraceRun oracle = traceOf(oracleRun);
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    && "str:fetched".equals(terminalAtom(oracle.terminal())),
                "the oracle's async value-position drive completes with the declared "
                    + "value: " + terminalText(oracle.terminal()));

            Path luaArtifact = asyncSpace.resolve("project.lua");
            Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(project,
                result.tables(), result.registries(), async.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(asyncSpace);
            Path hostTarget = asyncSpace.resolve("host/async_ok.lua");
            Files.createDirectories(hostTarget.getParent());
            Files.copy(Path.of("test/conformance/host-fixtures/async_ok.lua"),
                hostTarget);
            Path luaProbe = asyncSpace.resolve("trace-probe.lua");
            Files.writeString(luaProbe, luaAsyncEntryDriver(luaArtifact, entryModule,
                export), StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(luaProbe, asyncSpace);
            check(luaOutcome.exitCode() == 0,
                "the async trace drive runs under luajit: exit="
                    + luaOutcome.exitCode() + " stderr=" + escaped(luaOutcome.stderr()));
            checkTraceParity("async value read", "luajit", oracle,
                decodeTrace(luaOutcome.stderr()));

            JvmSemanticEmitter.EmissionResult jvmEmission =
                JvmSemanticEmitter.emitProject(project, result.tables(),
                    result.registries(), async.surface());
            String jvmClass = jvmEmission.className();
            OpId entryOpId = asyncEntryOf(project, entryModule, export);
            if (entryOpId == null) {
                fail("the async drive records no async EXTERNAL_ENTRY for '" + export
                    + "'");
                return;
            }
            Files.writeString(asyncSpace.resolve(jvmClass + ".java"),
                jvmEmission.source(), StandardCharsets.UTF_8);
            Files.writeString(asyncSpace.resolve("HostAsync_ok.java"),
                Files.readString(Path.of(
                    "test/conformance/host-fixtures/async_ok.java")),
                StandardCharsets.UTF_8);
            Files.writeString(asyncSpace.resolve("AsyncReadTraceDriver.java"),
                jvmAsyncEntryDriver(jvmClass, entryOpId), StandardCharsets.UTF_8);
            Path classes = asyncSpace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmClass + ".java", "HostAsync_ok.java",
                "AsyncReadTraceDriver.java"), asyncSpace);
            check(javacRun.exitCode() == 0, "the async trace drive compiles under javac: "
                + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() == 0) {
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "AsyncReadTraceDriver"), asyncSpace);
                check(jvmOutcome.exitCode() == 0,
                    "the async trace drive runs under java: exit="
                        + jvmOutcome.exitCode() + " " + escaped(jvmOutcome.stderr()));
                checkTraceParity("async value read", "java", oracle,
                    decodeTrace(jvmOutcome.stderr()));
            }
        } finally {
            deleteRecursively(asyncSpace);
            deleteRecursively(async.root());
        }
    }

    private static TraceRun traceOf(SemanticRuntimeModel.ConsumerRun run) {
        List<String> events = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            events.add(event.text());
        }
        List<String> asyncEffects = new ArrayList<>();
        for (SemanticRuntimeModel.EffectEvent effect : run.effects()) {
            switch (effect.kind()) {
                case ASYNC_START_OP, ASYNC_COMPLETE_RETURN, ASYNC_COMPLETE_THROW ->
                    asyncEffects.add(effect.kind() + "|" + effect.text());
                default -> {
                }
            }
        }
        return new TraceRun(List.copyOf(events), List.copyOf(asyncEffects),
            run.terminal());
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
        checkEq(terminalText(oracle.terminal()), terminalText(artifact.terminal()),
            name + " (" + target + ") terminal parity");
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
    // 7. The load and the fail-closed seeds
    // =========================================================================

    private static void testLoadAndFailClosedSeeds() throws Exception {
        System.out.println("-- the host load's pinned E8011 check holds in the "
            + "value-position drive, and an unloaded surface fails closed --");
        Fixture compiled = compileSource("host-read-sync", "read_sync",
            SYNC_DECLARATION, SYNC_SOURCE);
        Path workspace = Files.createTempDirectory("host-value-read-seed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the seed drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = workspace.resolve("project.lua");
            String chunk = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), compiled.surface());
            Files.writeString(artifact, chunk, StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path hostTarget = workspace.resolve("host/read_sync.lua");
            Files.createDirectories(hostTarget.getParent());
            // The load check holds: the raw table is missing the declared export.
            Files.writeString(hostTarget,
                "return { add = function(a, b) return a + b end }\n",
                StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome luaOutcome = runLua(probe, workspace);
            check(luaOutcome.value().startsWith("ERR:E8011|"),
                "the value-position drive's host load raises the pinned E8011 for a "
                    + "missing declared export: " + escaped(luaOutcome.value()));
            if (luaOutcome.value().startsWith("ERR:E8011|")) {
                String[] parts = luaOutcome.value().substring(4).split("\\|", -1);
                checkEq("missing host export 'greet' in module 'host/read_sync'",
                    parts[1], "the pinned E8011 text names the export and the module");
                String origin = parts[2];
                int lastColon = origin.lastIndexOf(':');
                int prevColon = origin.lastIndexOf(':', lastColon - 1);
                checkEq(1, Integer.valueOf(origin.substring(prevColon + 1, lastColon)),
                    "the pinned E8011 carries the import statement's line");
                checkEq(1, Integer.valueOf(origin.substring(lastColon + 1)),
                    "the pinned E8011 carries the import statement's column");
            }

            // The unloaded-surface seed: the load is removed from the emitted
            // chunk, so the read's registration names no loaded surface. The
            // emitted read still names the module identity (never a silent
            // call), and the mutated run fails loudly instead of succeeding
            // with a wrong value.
            String mutated = chunk.replaceAll(
                "__exportSurfaces\\[\"host\\.read_sync\"\\] = "
                    + "__exportSurfaces\\[\"host\\.read_sync\"\\] or "
                    + "__rt\\.load_host\\([^\\n]*\\)\\n", "");
            check(!mutated.equals(chunk),
                "the emitted chunk carries the inline load the seed removes");
            if (!mutated.equals(chunk)) {
                Path mutatedArtifact = workspace.resolve("project-unloaded.lua");
                Files.writeString(mutatedArtifact, mutated, StandardCharsets.UTF_8);
                Files.writeString(hostTarget, SYNC_HOST_LUA, StandardCharsets.UTF_8);
                Path mutatedProbe = workspace.resolve("probe-unloaded.lua");
                Files.writeString(mutatedProbe,
                    luaDriver(mutatedArtifact, compiled.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome seedOutcome = runLua(mutatedProbe, workspace);
                check(seedOutcome.value().startsWith("ERR:")
                        || seedOutcome.exitCode() != 0,
                    "a read whose registration names no loaded surface fails loudly, "
                        + "never a silent call: " + escaped(seedOutcome.value())
                        + " stderr=" + escaped(seedOutcome.stderr()));
                check(chunk.contains("__exportSurfaces[\"host.read_sync\"]"),
                    "the emitted read names the module identity the surface registry "
                        + "keys (the unloaded surface is unrepresentable)");
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // The drivers and the process helpers
    // =========================================================================

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
            if (_READ_SYNC_LOADS or 0) > 1 then
              print("ERR:LOADS|" .. _READ_SYNC_LOADS .. "|-|-|-") os.exit(0)
            end
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
    private static String jvmDriver(String probeClass, String className,
            String entryPath) {
        return """
            final class %s {
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
            """.formatted(probeClass, className, className, quoted(entryPath));
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

    /** The async EXTERNAL_ENTRY op id of one module's export, or null. */
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
            final class AsyncReadTraceDriver {
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

    /** Decodes one artifact's protocol stream (trace events, async effects,
     *  terminal). */
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
        Path stderrFile = Files.createTempFile("host-value-read-err", ".txt");
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
