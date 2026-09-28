package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
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
 * ISSUE-0682: the joint dynamic dispatch battery over the assembled epic
 * (design sources {@code function-typed-value-materialization-and-dispatch}
 * M7 items 1-2 and 4-6 with its M5 class table and the dynamic call /
 * dynamic DEAL-body cell contracts, {@code conversion-intrinsic-function-values}
 * J6, and {@code semantic-ir-construct-coverage-cutover} K5/K11/K12).
 *
 * <p>The battery drives, per carrier class, the dispatched invocation
 * through the one lowering and the three consumers (the semantic oracle,
 * the production LuaJIT artifact under real {@code luajit}, and the
 * production JVM artifact under {@code javac --release 25 -proc:none} plus
 * {@code java}), asserting the executed class path, the selected recorded
 * return cell, and the trace events — the sync class drives and the
 * dynamic-await drives for the DEAL-body, adapter, host and external async
 * classes. It then drives the function-typed completion, the dynamic
 * cross-module corpus fixtures, the K12 reference-identity anchor, and the
 * fault battery, and it re-asserts that the closed op-kind, boundary-kind,
 * failure-policy, and payload-record sets are unchanged.</p>
 */
public class DynamicDispatchBatteryTest {

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

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId LIB = new ModuleId("lib");

    // =========================================================================
    // The class drives
    // =========================================================================

    /** The DEAL-body class drive: a parameter callee holding a closure. */
    private static final String DEAL_BODY_SOURCE = """
        function double(x: int): int {
          return x * 2
        }

        function apply(f: (x: int) => int, v: int): int {
          return f(v)
        }

        export function main(): null {
          let r: int = apply(double, 21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "deal body class" };
          }
          return null;
        }
        """;

    /** The adapter class drive: a parameter callee holding an arity extension. */
    private static final String ADAPTER_SOURCE = """
        function one(x: int): int {
          return x
        }

        function apply(f: (x: int, y: int) => int, a: int, b: int): int {
          return f(a, b)
        }

        export function main(): null {
          let takesTwo: (x: int, y: int) => int = one
          let r: int = apply(takesTwo, 10, 20)
          if (r !== 10) {
            throw { code: "TEST_FAIL", message: "adapter class" };
          }
          return null;
        }
        """;

    /** The stdlib-callable class drive: a parameter callee holding console.log. */
    private static final String STDLIB_SOURCE = """
        import * as console from "std/console"

        function invoke(f: (x: string) => null, v: string): null {
          return f(v)
        }

        export function main(): null {
          invoke(console.log, "stdlib-class")
          return null
        }
        """;

    /** The intrinsic-conversion class drive: a parameter callee holding int. */
    private static final String INTRINSIC_SOURCE = """
        function apply(f: (x: number) => int, v: number): int {
          return f(v)
        }

        export function main(): null {
          let r: int = apply(int, 3.0)
          if (r !== 3) {
            throw { code: "TEST_FAIL", message: "intrinsic class" };
          }
          return null;
        }
        """;

    /** The shared-body external drive: the identity-resolved cross-module callee. */
    private static final String EXTERNAL_LIB_SOURCE = """
        export function double(x: int): int {
          return x * 2
        }

        export function main(): null {
          return null
        }
        """;

    private static final String EXTERNAL_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let f: (x: int) => int = lib.double
          let r: int = f(21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "shared body external class" };
          }
          return null;
        }
        """;

    // =========================================================================
    // The dynamic-await class-drive fixtures (M7 item 2)
    // =========================================================================

    /**
     * The DEAL-body async class drive: a function-typed parameter callee
     * holding the {@code async} body {@code value}, awaited on the callee
     * value's own class.
     */
    private static final String DEAL_BODY_ASYNC_SOURCE = """
        async function value(): int {
          return 42
        }

        async function drive(f: async () => int): int {
          let v: int = await f()
          return v
        }

        export async function probe(): int {
          return await drive(value)
        }

        export function main(): null {
          return null
        }
        """;

    /**
     * The adapter async class drive: a function-typed parameter callee
     * whose runtime carrier is an arity-extension adapter over an async
     * DEAL body, awaited on the adapter's own tag.
     */
    private static final String ADAPTER_ASYNC_SOURCE = """
        async function inc(x: int): int {
          return x + 1
        }

        async function drive(f: async (a: int, b: int) => int, x: int, y: int): int {
          let v: int = await f(x, y)
          return v
        }

        export async function probe(): int {
          let adapted: async (a: int, b: int) => int = inc
          return await drive(adapted, 41, 9)
        }

        export function main(): null {
          return null
        }
        """;

    /**
     * The shared-body external async class drive: the identity-resolved
     * callee arm (M4: no value-carried external tag exists), the caller's
     * await running the callee unit's async {@code EXTERNAL_ENTRY} under
     * its own module context.
     */
    private static final String EXTERNAL_ASYNC_LIB_SOURCE = """
        export async function fetch(): int {
          return 40
        }

        export function main(): null {
          return null
        }
        """;

    private static final String EXTERNAL_ASYNC_APP_SOURCE = """
        import * as lib from "./lib"

        export async function probe(): int {
          return await lib.fetch()
        }

        export function main(): null {
          return null
        }
        """;

    /**
     * The host async class drive (M7 item 2): a function-typed parameter
     * callee holding a loaded declared async host export, awaited through
     * the host operation handle.
     */
    private static final String HOST_ASYNC_SOURCE = """
        import * as host from "host/battery_async"

        async function drive(f: async () => int): int {
          let v: int = await f()
          return v
        }

        export async function probe(): int {
          return await drive(host.fetchValue)
        }

        export function main(): null {
          return null
        }
        """;

    private static final String HOST_ASYNC_DECLARATION = """
        export async function fetchValue(): int;
        """;

    private static final String HOST_ASYNC_LUA = """
        local rt = require("deal.runtime")

        return {
          fetchValue = function()
            print("HOST-START")
            return rt.async_start(function() return 42 end)
          end,
        }
        """;

    private static String hostAsyncJava(String hostClass) {
        return """
            import java.util.concurrent.CompletableFuture;

            public final class %s {
              public static Object fetchValue() {
                System.out.println("HOST-START");
                return CompletableFuture.completedFuture(
                    java.lang.Long.valueOf(42L));
              }
            }
            """.formatted(hostClass);
    }

    /**
     * Drives one async project (no host modules) through the three-consumer
     * async-entry matrix (the oracle's {@code invokeAsyncEntry} surface, the
     * shared LuaJIT artifacts' async-entry dispatch, and the shared JVM
     * artifacts' static dispatch entry under the real toolchains) with the
     * pinned {@code probe} export. Returns the drive facts, or null when the
     * drive could not run.
     */
    private static AsyncDrive launchAsyncDrive(String what, Map<String, String> sources,
            String resultAtom) throws Exception {
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return null;
        }
        SemanticLowerer.ProjectLoweringResult result;
        try {
            result = lower(fixture);
        } finally {
            deleteRecursively(fixture.root());
        }
        check(result.project() != null, what + " lowers and passes the closed "
            + "gate: " + result.diagnostics());
        if (result.project() == null) {
            return null;
        }
        Path workspace = Files.createTempDirectory("battery-async");
        SemanticDifferentialHarness.Verdict verdict;
        try {
            verdict = SemanticDifferentialHarness.runAsyncEntry(result.project(),
                result.tables(), "probe", List.of(),
                SemanticDifferentialHarness.Expectation.success(what, List.of(),
                    resultAtom), workspace, null);
        } finally {
            deleteRecursively(workspace);
        }
        checkEq(3, verdict.runs().size(), what + " produced all three consumer runs: "
            + verdict.failures());
        check(verdict.pass(), what + " executes with the pinned outcome on all three "
            + "consumers: " + verdict.report());
        return new AsyncDrive(result.project(), result, verdict);
    }

    /** One launched dynamic-await drive: the project, its lowering facts, the verdict. */
    private record AsyncDrive(ExecutableLoweredProject project,
                              SemanticLowerer.ProjectLoweringResult result,
                              SemanticDifferentialHarness.Verdict verdict) {
    }

    /** Asserts the three async-entry traces equal the oracle's event-for-event. */
    private static void assertAsyncTracesEqual(String what,
            SemanticDifferentialHarness.Verdict verdict) {
        if (verdict.runs().size() != 3) {
            return;
        }
        List<String> oracle = traceLines(verdict.runs().get(0));
        check(!oracle.isEmpty(), what + ": the oracle produced events");
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            checkEq(oracle, traceLines(run), what + ": the " + run.consumer()
                + " async-entry trace equals the oracle's event-for-event");
        }
    }

    /** Asserts one recorded cell runs exactly once per invocation per consumer. */
    private static void assertSingleCellExecution(String what,
            SemanticDifferentialHarness.Verdict verdict, OpId cell, String role) {
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            checkEq(1, eventCount(run, cell, SemanticRuntimeModel.Phase.START),
                what + ": " + run.consumer() + " runs the " + role + " exactly once");
            checkEq(1, eventCount(run, cell, SemanticRuntimeModel.Phase.SUCCESS),
                what + ": " + run.consumer() + " admits the " + role + " value "
                    + "exactly once");
        }
    }

    /**
     * Asserts the resolved body's own cell runs inside the body before the
     * call-owned task cell runs in the caller-side task wrapper (M6: the
     * invocation site executes the call-owned record after the resolved
     * body returns and before the token completes).
     */
    private static void assertTaskCellAfterBodyCell(String what,
            SemanticDifferentialHarness.Verdict verdict, OpId bodyCell, OpId taskCell) {
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            int bodyStart = eventIndex(run, bodyCell, SemanticRuntimeModel.Phase.START);
            int bodySuccess = eventIndex(run, bodyCell, SemanticRuntimeModel.Phase.SUCCESS);
            int taskStart = eventIndex(run, taskCell, SemanticRuntimeModel.Phase.START);
            int taskSuccess = eventIndex(run, taskCell, SemanticRuntimeModel.Phase.SUCCESS);
            check(bodyStart >= 0 && bodySuccess > bodyStart && taskStart > bodySuccess
                    && taskSuccess > taskStart,
                what + ": " + run.consumer() + " runs the resolved body's own cell "
                    + "inside the body before the call-owned task cell runs in the "
                    + "task wrapper (" + bodyStart + " < " + bodySuccess + " < "
                    + taskStart + " < " + taskSuccess + ")");
        }
    }

    /**
     * Drives one sync single-module project (no host modules) through the
     * oracle and both production artifacts, asserting the pinned outcome
     * and effects. Returns the verdict, or null when the drive could not
     * run.
     */
    private static SemanticDifferentialHarness.Verdict driveSyncProject(String what,
            Map<String, String> sources, List<String> effects, String resultAtom,
            java.util.function.Consumer<ExecutableLoweredProject> irAssertions)
            throws Exception {
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return null;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, what + " lowers and passes the closed "
                + "gate: " + result.diagnostics());
            if (result.project() == null) {
                return null;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            if (app == null) {
                fail(what + ": the closure carries no app module");
                return null;
            }
            irAssertions.accept(project);
            Path workspace = Files.createTempDirectory("battery-class");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success(what, effects,
                            resultAtom), workspace);
                reportTraceDiff(verdict.runs());
                check(verdict.pass(), what + " executes on all three consumers: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), what + " produced all three "
                    + "consumer runs");
                return verdict;
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The DEAL-body class drive (M7 item 1). */
    private static void testDealBodyClass() throws Exception {
        System.out.println("-- the DEAL-body class: a function-typed parameter callee "
            + "holding a closure dispatches on the carrier's own tag --");
        SemanticDifferentialHarness.Verdict verdict = driveSyncProject("deal body class",
            Map.of("src/app.deal", DEAL_BODY_SOURCE), List.of(), "null", project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the deal-body drive produces the dynamic callee "
                    + "shape");
                if (call == null) {
                    return;
                }
                KindPayload.CallCallee.Dynamic callee = (KindPayload.CallCallee.Dynamic)
                    ((KindPayload.CallPayload) call.payload()).callee();
                check(registrationOf(app, callee.callee())
                        instanceof FunctionExecutionBinding.DynamicFunctionValue,
                    "the parameter callee registers the producer rule's dynamic "
                        + "materialization");
                FunctionExecutionBinding calleeBinding = carrierRegistration(app, 0);
                check(calleeBinding instanceof FunctionExecutionBinding.LoweredBody,
                    "the passed callee value registers its LoweredBody class: "
                        + calleeBinding);
                OpId dealCell = ((KindPayload.CallPayload) call.payload())
                    .dynamicReturnBoundary().dealBodyBoundaryOpId();
                SemanticOp cell = opOf(app, dealCell);
                check(cell != null, "the dynamic call records its DEAL-body cell");
                if (cell != null && cell.origin().parentOpId() != null) {
                    SemanticOp parent = opOf(app, cell.origin().parentOpId());
                    check(parent != null && parent.kind() == SemanticOpKind.RETURN
                            && parent.payload() instanceof KindPayload.ReturnPayload
                                returned
                            && !app.functions().containsKey(returned.function()),
                        "a runtime-resolved callee records the call-owned form: the "
                            + "recorded cell's parent is the unattached record RETURN "
                            + "naming no lowered body of the unit");
                }
            });
        if (verdict == null || verdict.runs().isEmpty()) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success success
                    && "null".equals(success.resultAtom()),
                "deal body class: " + run.consumer() + " completes runtime-ok: "
                    + run.terminal());
        }
    }

    /** The adapter class drive (M7 item 1). */
    private static void testAdapterClass() throws Exception {
        System.out.println("-- the adapter class: a function-typed parameter callee "
            + "holding an arity extension runs the D15 path --");
        driveSyncProject("adapter class", Map.of("src/app.deal", ADAPTER_SOURCE),
            List.of(), "null", project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the adapter drive produces the dynamic callee "
                    + "shape");
                if (call == null) {
                    return;
                }
                KindPayload.CallCallee.Dynamic callee = (KindPayload.CallCallee.Dynamic)
                    ((KindPayload.CallPayload) call.payload()).callee();
                check(registrationOf(app, callee.callee())
                        instanceof FunctionExecutionBinding.DynamicFunctionValue,
                    "the adapter parameter callee registers the dynamic "
                        + "materialization");
                boolean adapter = false;
                for (FunctionExecutionBinding binding
                        : app.functionBindings().values()) {
                    if (binding instanceof FunctionExecutionBinding.AdapterBinding) {
                        adapter = true;
                    }
                }
                check(adapter, "the arity extension registers its AdapterBinding");
                OpId dealCell = ((KindPayload.CallPayload) call.payload())
                    .dynamicReturnBoundary().dealBodyBoundaryOpId();
                check(opOf(app, dealCell) != null, "the dynamic call records the "
                    + "DEAL-body cell its source class selects");
            });
    }

    /** The stdlib-callable class drive (M7 item 1). */
    private static void testStdlibCallableClass() throws Exception {
        System.out.println("-- the cataloged stdlib callable class: a function-typed "
            + "parameter callee holding console.log runs the catalog row --");
        driveSyncProject("stdlib callable class",
            Map.of("src/app.deal", STDLIB_SOURCE), List.of("stdlib-class"), "null",
            project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the stdlib drive produces the dynamic callee "
                    + "shape");
                if (call == null) {
                    return;
                }
                FunctionExecutionBinding source = carrierRegistration(app, 0);
                check(source instanceof FunctionExecutionBinding.HostFunction host
                        && "std.console".equals(host.hostModuleId().path()),
                    "the carrier's own read registers the cataloged callable's HOST "
                        + "class: " + source);
                OpId hostCell = ((KindPayload.CallPayload) call.payload())
                    .dynamicReturnBoundary().hostBoundaryOpId();
                check(opOf(app, hostCell) != null, "the dynamic call records its "
                    + "host cell");
            });
    }

    /** The intrinsic-conversion class drive (M7 item 1). */
    private static void testIntrinsicConversionClass() throws Exception {
        System.out.println("-- the intrinsic-conversion class: a function-typed "
            + "parameter callee holding int runs the conversion ladder --");
        driveSyncProject("intrinsic conversion class",
            Map.of("src/app.deal", INTRINSIC_SOURCE), List.of(), "null", project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the intrinsic drive produces the dynamic callee "
                    + "shape");
                if (call == null) {
                    return;
                }
                KindPayload.CallCallee.Dynamic callee = (KindPayload.CallCallee.Dynamic)
                    ((KindPayload.CallPayload) call.payload()).callee();
                check(registrationOf(app, callee.callee())
                        instanceof FunctionExecutionBinding.DynamicFunctionValue,
                    "the intrinsic parameter callee registers the dynamic "
                        + "materialization");
                boolean intrinsic = false;
                for (FunctionExecutionBinding binding
                        : app.functionBindings().values()) {
                    if (binding instanceof FunctionExecutionBinding.IntrinsicFunction
                            value && value.kind() == IntrinsicKind.INT_CONVERT) {
                        intrinsic = true;
                    }
                }
                check(intrinsic, "the seeded identity keeps its IntrinsicFunction "
                    + "registration");
                OpId hostCell = ((KindPayload.CallPayload) call.payload())
                    .dynamicReturnBoundary().hostBoundaryOpId();
                check(opOf(app, hostCell) != null, "the dynamic call records the "
                    + "host cell the intrinsic's HOST class selects");
            });
    }

    /** The shared-body external class drive (the identity-resolved callee arm). */
    private static void testSharedBodyExternalClass() throws Exception {
        System.out.println("-- the shared-body external class: the identity-resolved "
            + "cross-module callee runs the callee unit's EXTERNAL_ENTRY --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", EXTERNAL_LIB_SOURCE);
        sources.put("src/app.deal", EXTERNAL_APP_SOURCE);
        SemanticDifferentialHarness.Verdict verdict = driveSyncProject(
            "shared body external class", sources, List.of(), "null", project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = indirectCallOn(app, FunctionExecutionBinding
                    .ExternalFunction.class);
                check(call != null, "the external drive produces the identity-resolved "
                    + "indirect call");
                LoweredModuleUnit lib = project.modules().get(LIB);
                check(lib != null, "the closure carries the callee module");
                if (call == null || lib == null) {
                    return;
                }
                KindPayload.CallPayload payload =
                    (KindPayload.CallPayload) call.payload();
                check(payload.returnBoundaryOpId() == null,
                    "a SHARED_BODY external call records no caller-side return cell");
                check(payload.externalEntryRef() != null,
                    "the call records the callee unit's EXTERNAL_ENTRY");
            });
        if (verdict == null || verdict.runs().isEmpty()) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            check(touchedModule(run, LIB), "shared body external class: "
                + run.consumer() + " executed the callee unit's EXTERNAL_ENTRY");
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success success
                    && "null".equals(success.resultAtom()),
                "shared body external class: " + run.consumer()
                    + " completes runtime-ok: " + run.terminal());
        }
    }

    // =========================================================================
    // The dynamic-await class drives (M7 item 2)
    // =========================================================================

    /**
     * The DEAL-body async class drive (M7 item 2): the awaited parameter
     * callee's runtime carrier is the {@code value} async body, so the
     * dispatch starts that body's task under its module context and the
     * recorded call-owned task cell runs in the caller-side task wrapper
     * exactly once after the resolved body's own RETURN cell.
     */
    private static void testDealBodyAsyncClass() throws Exception {
        System.out.println("-- the DEAL-body class, awaited: a function-typed parameter "
            + "callee holding an async body dispatches on the carrier's own tag and the "
            + "recorded call-owned task cell runs exactly once in the task wrapper --");
        AsyncDrive drive = launchAsyncDrive("deal body async class",
            Map.of("src/app.deal", DEAL_BODY_ASYNC_SOURCE), "int:42");
        if (drive == null) {
            return;
        }
        LoweredModuleUnit app = drive.project().modules().get(APP);
        SemanticOp start = dynamicAsyncStart(app);
        check(start != null, "the deal-body async drive produces the dynamic "
            + "ASYNC_START shape");
        if (start == null) {
            return;
        }
        KindPayload.AsyncStartPayload payload =
            (KindPayload.AsyncStartPayload) start.payload();
        KindPayload.CallCallee.Dynamic callee =
            (KindPayload.CallCallee.Dynamic) payload.callee();
        check(registrationOf(app, callee.callee())
                instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the awaited parameter callee registers the producer rule's dynamic "
                + "materialization");
        FunctionExecutionBinding carrier = carrierRegistration(app, 0);
        check(carrier instanceof FunctionExecutionBinding.LoweredBody,
            "the passed callee value registers its LoweredBody class: " + carrier);
        if (!(carrier instanceof FunctionExecutionBinding.LoweredBody body)) {
            return;
        }
        SemanticOp taskCell = payload.returnBoundaryOpId() == null
            ? null : opOf(app, payload.returnBoundaryOpId());
        check(taskCell != null && callOwnedCell(app, taskCell),
            "a runtime-resolved callee records the call-owned task cell: " + taskCell);
        SemanticOp bodyCell = bodyReturnCell(app, body);
        check(bodyCell != null, "the resolved body carries its own RETURN cell: "
            + bodyCell);
        if (taskCell == null || bodyCell == null) {
            return;
        }
        assertAsyncTracesEqual("deal body async class", drive.verdict());
        assertSingleCellExecution("deal body async class", drive.verdict(),
            taskCell.opId(), "call-owned task cell");
        assertSingleCellExecution("deal body async class", drive.verdict(),
            bodyCell.opId(), "resolved body's own cell");
        assertTaskCellAfterBodyCell("deal body async class", drive.verdict(),
            bodyCell.opId(), taskCell.opId());
    }

    /**
     * The adapter async class drive (M7 item 2): the awaited parameter's
     * runtime carrier is a {@code FUNCTION_ADAPT} value over an async DEAL
     * body, so the D15 source resolution starts the source body's task and
     * the adapter's recorded call-owned task cell runs exactly once in the
     * task wrapper.
     */
    private static void testAdapterAsyncClass() throws Exception {
        System.out.println("-- the adapter class, awaited: the D15 source resolution "
            + "starts the source body task and the recorded call-owned task cell runs "
            + "exactly once in the caller-side task wrapper --");
        AsyncDrive drive = launchAsyncDrive("adapter async class",
            Map.of("src/app.deal", ADAPTER_ASYNC_SOURCE), "int:42");
        if (drive == null) {
            return;
        }
        LoweredModuleUnit app = drive.project().modules().get(APP);
        SemanticOp start = dynamicAsyncStart(app);
        check(start != null, "the adapter async drive produces the dynamic ASYNC_START "
            + "shape");
        if (start == null) {
            return;
        }
        KindPayload.AsyncStartPayload payload =
            (KindPayload.AsyncStartPayload) start.payload();
        KindPayload.CallCallee.Dynamic callee =
            (KindPayload.CallCallee.Dynamic) payload.callee();
        check(registrationOf(app, callee.callee())
                instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the awaited parameter callee registers the producer rule's dynamic "
                + "materialization");
        FunctionExecutionBinding carrier = carrierRegistration(app, 0);
        check(carrier instanceof FunctionExecutionBinding.AdapterBinding adapter
                && adapter.sourceSignature().paramTypes().size() == 1,
            "the passed callee value registers its AdapterBinding with the leading-M "
                + "source arity: " + carrier);
        SemanticOp taskCell = payload.returnBoundaryOpId() == null
            ? null : opOf(app, payload.returnBoundaryOpId());
        check(taskCell != null && callOwnedCell(app, taskCell),
            "a runtime-resolved adapter callee records the call-owned task cell: "
                + taskCell);
        if (taskCell == null) {
            return;
        }
        assertAsyncTracesEqual("adapter async class", drive.verdict());
        assertSingleCellExecution("adapter async class", drive.verdict(),
            taskCell.opId(), "call-owned task cell");
        FunctionExecutionBinding sourceBinding = asyncBodyRegistration(app);
        check(sourceBinding instanceof FunctionExecutionBinding.LoweredBody,
            "the adapter's source body resolves its DEAL-body registration: "
                + sourceBinding);
        if (sourceBinding instanceof FunctionExecutionBinding.LoweredBody sourceBody) {
            SemanticOp sourceCell = bodyReturnCell(app, sourceBody);
            check(sourceCell != null, "the adapter's source body carries its own "
                + "RETURN cell: " + sourceCell);
            if (sourceCell != null) {
                assertSingleCellExecution("adapter async class", drive.verdict(),
                    sourceCell.opId(), "resolved source body's own cell");
            }
        }
    }

    /**
     * The shared-body external async class drive (M7 item 2, the
     * identity-resolved callee arm M4 pins for this class): the caller's
     * await starts the callee unit's async {@code EXTERNAL_ENTRY} task under
     * its own module context, whose single {@code FUNCTION_RETURN} cell runs
     * exactly once per invocation; the caller records zero caller-side
     * return boundaries.
     */
    private static void testSharedBodyExternalAsyncClass() throws Exception {
        System.out.println("-- the shared-body external class, awaited: the "
            + "identity-resolved cross-module await runs the callee unit's async "
            + "EXTERNAL_ENTRY and its FUNCTION_RETURN cell exactly once --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", EXTERNAL_ASYNC_LIB_SOURCE);
        sources.put("src/app.deal", EXTERNAL_ASYNC_APP_SOURCE);
        AsyncDrive drive = launchAsyncDrive("shared body external async class",
            sources, "int:40");
        if (drive == null) {
            return;
        }
        LoweredModuleUnit app = drive.project().modules().get(APP);
        LoweredModuleUnit lib = drive.project().modules().get(LIB);
        check(lib != null, "the external async closure carries the callee module");
        SemanticOp start = null;
        for (SemanticOp op : app.ops()) {
            if (op.payload() instanceof KindPayload.AsyncStartPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Static
                        staticCallee
                    && staticCallee.binding()
                        instanceof FunctionExecutionBinding.ExternalFunction) {
                start = op;
                break;
            }
        }
        check(start != null, "the external async drive produces the identity-resolved "
            + "ASYNC_START shape");
        if (start == null || lib == null) {
            return;
        }
        KindPayload.AsyncStartPayload payload =
            (KindPayload.AsyncStartPayload) start.payload();
        check(payload.externalAsyncLink() != null,
            "the identity-resolved external await records its external async link");
        check(payload.returnBoundaryOpId() == null,
            "an external async resolution records zero caller-side return boundaries");
        OpId entryId = asyncEntryOpId(lib, "fetch");
        check(entryId != null, "the callee unit records its async EXTERNAL_ENTRY");
        if (entryId == null) {
            return;
        }
        SemanticOp entry = opOf(lib, entryId);
        OpId entryCell = ((KindPayload.ExternalEntryPayload) entry.payload())
            .returnBoundaryOpId();
        assertAsyncTracesEqual("shared body external async class", drive.verdict());
        assertSingleCellExecution("shared body external async class", drive.verdict(),
            entryCell, "callee unit's async EXTERNAL_ENTRY return cell");
        for (SemanticRuntimeModel.ConsumerRun run : drive.verdict().runs()) {
            check(touchedModule(run, LIB), "shared body external async class: "
                + run.consumer() + " executed the callee unit's EXTERNAL_ENTRY");
        }
    }

    /** The single indirect call of one unit resolving the given binding shape. */
    private static SemanticOp indirectCallOn(LoweredModuleUnit unit,
            Class<? extends FunctionExecutionBinding> shape) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Static
                        staticCallee
                    && shape.isInstance(staticCallee.binding())) {
                return op;
            }
        }
        return null;
    }

    /**
     * The value-channel registration of one function-typed argument of a
     * unit's first static/indirect call (the passed value's own class).
     */
    private static FunctionExecutionBinding carrierRegistration(LoweredModuleUnit unit,
            int parameterIndex) {
        for (SemanticOp op : unit.ops()) {
            KindPayload.CallCallee callee;
            List<OpId> boundaries;
            if (op.payload() instanceof KindPayload.CallPayload call) {
                callee = call.callee();
                boundaries = call.parameterBoundaryOpIds();
            } else if (op.payload() instanceof KindPayload.AsyncStartPayload start) {
                callee = start.callee();
                boundaries = start.parameterBoundaryOpIds();
            } else {
                continue;
            }
            if (!(callee instanceof KindPayload.CallCallee.Static)) {
                continue;
            }
            if (parameterIndex >= boundaries.size()) {
                continue;
            }
            SemanticOp boundary = opOf(unit, boundaries.get(parameterIndex));
            if (boundary == null
                    || !(boundary.payload() instanceof KindPayload.BoundaryPayload payload)
                    || payload.kind() != deal.semantic.ir.BoundaryKind.FUNCTION_PARAMETER) {
                continue;
            }
            return unit.functionBindings().get(
                new FunctionAllocationIdentity(payload.input().id()));
        }
        return null;
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    /**
     * The function-typed completion drive (M7 item 2): {@code await g(x)}
     * with {@code g: (x: int) => ((y: int) => int)} publishes a
     * function-typed completion (the {@code AWAIT} op's result identity)
     * whose resolved carrier is then called.
     */
    private static final String COMPLETION_SOURCE = """
        function makeAdder(base: int): (x: int) => int {
          return function(x: int): int { return base + x; };
        }

        async function g(x: int): (y: int) => int {
          return makeAdder(x);
        }

        export async function probe(): int {
          let f: (y: int) => int = await g(40)
          return f(2)
        }

        export function main(): null {
          return null
        }
        """;

    /** The driver of `modules/imported-closure-factory.deal`'s test export. */
    private static final String CLOSURE_FACTORY_DRIVER = """
        import * as fix from "./fixture"

        export function main(): null {
          let r: int = fix.test_imported_closure_factory()
          if (r !== 15) {
            throw { code: "TEST_FAIL", message: "imported closure factory driver" };
          }
          return null;
        }
        """;

    /** The driver of `modules/imported-recursive-callback.deal`'s test export. */
    private static final String RECURSIVE_CALLBACK_DRIVER = """
        import * as fix from "./fixture"

        export function main(): null {
          let r: int = fix.test_imported_recursive_callback()
          if (r !== 4) {
            throw { code: "TEST_FAIL", message: "imported recursive callback driver" };
          }
          return null;
        }
        """;

    /**
     * The driver of `closures/closure-returned-from-module.deal`'s test
     * export: the named non-bytes fixture whose cross-module call result
     * flows into a function-typed binding and is then invoked.
     */
    private static final String CLOSURE_RETURNED_DRIVER = """
        import * as fix from "./fixture"

        export function main(): null {
          let r: int = fix.test_closure_returned_from_module()
          if (r !== 12) {
            throw { code: "TEST_FAIL", message: "closure returned from module driver" };
          }
          return null;
        }
        """;

    private record Fixture(Path root, CheckedProjectInput checkedProject,
                           ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           HostDeclarationSurface surface,
                           Map<ModuleId, CanonicalModuleIdentity> identities) {
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** One project compiled through the real orchestrator (stdlib and compiled modules). */
    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        return compileProject(sources, Map.of());
    }

    /** One project compiled through the real orchestrator with host declarations. */
    private static Fixture compileProject(Map<String, String> sources,
                                          Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("dynamic-dispatch-battery");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Path target = root.resolve(source.getKey());
            Files.createDirectories(target.getParent());
            Files.writeString(target, source.getValue(), StandardCharsets.UTF_8);
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            resolvedExternals.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().toString());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT,
            resolvedExternals.isEmpty() ? null : resolvedExternals,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            fail("the fixture project did not build: "
                + (built == null ? "no checked project" : built.diagnostics()) + " / "
                + orchestrator.diagnostics());
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declaration : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declaration,
                new CanonicalModuleIdentity.ExternalModule(declaration.path()));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), identities);
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.identities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    // =========================================================================
    // Op helpers
    // =========================================================================

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp dynamicCall(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload call
                    && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    /** The single dynamic {@code ASYNC_START} op of the unit, or null. */
    private static SemanticOp dynamicAsyncStart(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.AsyncStartPayload start
                    && start.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    /** The async {@code EXTERNAL_ENTRY} op id of one export, or null. */
    private static OpId asyncEntryOpId(LoweredModuleUnit unit, String exportName) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                    && op.payload() instanceof KindPayload.ExternalEntryPayload payload
                    && payload.async() && payload.exportName().equals(exportName)) {
                return op.opId();
            }
        }
        return null;
    }

    /**
     * Whether one recorded cell is the call-owned form (M6): its parent is
     * an unattached record {@code RETURN} naming the invocation — a RETURN
     * whose function resolves to no lowered body of the unit.
     */
    private static boolean callOwnedCell(LoweredModuleUnit unit, SemanticOp cell) {
        OpId parentId = cell.origin().parentOpId();
        SemanticOp parent = parentId == null ? null : opOf(unit, parentId);
        return parent != null
            && parent.kind() == SemanticOpKind.RETURN
            && parent.payload() instanceof KindPayload.ReturnPayload returned
            && !unit.functions().containsKey(returned.function());
    }

    /** The body's own RETURN-recorded return cell of one lowered body, or null. */
    private static SemanticOp bodyReturnCell(LoweredModuleUnit unit,
            FunctionExecutionBinding.LoweredBody body) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload returned
                    && returned.function().equals(body.functionId())
                    && returned.returnBoundaryOpId() != null) {
                return opOf(unit, returned.returnBoundaryOpId());
            }
        }
        return null;
    }

    /** The single async lowered-body registration of the unit, or null. */
    private static FunctionExecutionBinding asyncBodyRegistration(LoweredModuleUnit unit) {
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.LoweredBody body) {
                var function = unit.functions().get(body.functionId());
                if (function != null && function.descriptor().isAsync()) {
                    return binding;
                }
            }
        }
        return null;
    }

    /** The single AWAIT op of the unit, or null. */
    private static SemanticOp awaitOf(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.AWAIT) {
                return op;
            }
        }
        return null;
    }

    /** The first trace position of one op and phase, or -1. */
    private static int eventIndex(SemanticRuntimeModel.ConsumerRun run, OpId op,
                                  SemanticRuntimeModel.Phase phase) {
        int found = -1;
        List<SemanticRuntimeModel.TraceEvent> trace = run.trace();
        for (int i = 0; i < trace.size(); i++) {
            if (trace.get(i).op().equals(op) && trace.get(i).phase() == phase) {
                found = i;
            }
        }
        return found;
    }

    /** The single function-typed {@code AWAIT} op of the unit, or null. */
    private static SemanticOp functionTypedAwait(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.AWAIT
                    && op.payload() instanceof KindPayload.AwaitPayload await
                    && await.completionDescriptor() instanceof RuntimeDescriptor.Func) {
                return op;
            }
        }
        return null;
    }

    private static ValueId resultValueOf(SemanticOp op) {
        return op.result() instanceof ValueId value ? value : null;
    }

    private static FunctionExecutionBinding registrationOf(LoweredModuleUnit unit,
                                                           ValueId value) {
        if (value == null) {
            return null;
        }
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
    }

    /** The number of trace events of one op and phase in a consumer run. */
    private static int eventCount(SemanticRuntimeModel.ConsumerRun run, OpId op,
                                  SemanticRuntimeModel.Phase phase) {
        int count = 0;
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op) && event.phase() == phase) {
                count++;
            }
        }
        return count;
    }

    /** Whether any trace event names an op of the given module. */
    private static boolean touchedModule(SemanticRuntimeModel.ConsumerRun run,
                                         ModuleId module) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().module().equals(module)) {
                return true;
            }
        }
        return false;
    }

    private static List<String> traceLines(SemanticRuntimeModel.ConsumerRun run) {
        List<String> lines = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            lines.add(event.text());
        }
        return lines;
    }

    /** Prints the first trace position where one consumer diverges from the oracle. */
    private static void reportTraceDiff(List<SemanticRuntimeModel.ConsumerRun> runs) {
        if (runs.size() < 2 || !Boolean.getBoolean("battery.traceDebug")) {
            return;
        }
        if (runs.size() < 2) {
            return;
        }
        List<String> oracle = traceLines(runs.get(0));
        for (int c = 1; c < runs.size(); c++) {
            List<String> other = traceLines(runs.get(c));
            int min = Math.min(oracle.size(), other.size());
            for (int i = 0; i < min; i++) {
                if (!oracle.get(i).equals(other.get(i))) {
                    System.out.println("DIFF@" + i + " " + runs.get(c).consumer()
                        + "\n  oracle: " + oracle.get(i)
                        + "\n  other : " + other.get(i));
                    break;
                }
            }
            if (oracle.size() != other.size()) {
                System.out.println(runs.get(c).consumer() + " has " + other.size()
                    + " events, the oracle " + oracle.size());
                for (int i = min; i < Math.max(oracle.size(), other.size()); i++) {
                    System.out.println("  " + (i < oracle.size() ? "oracle: "
                        + oracle.get(i) : "other : " + other.get(i)));
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

    /** Reads one corpus fixture and strips its classification headers. */
    private static String readFixture(String relativePath) throws Exception {
        return ConformanceHarnessMetadata.stripClassificationHeaders(
            Files.readString(Path.of("test/conformance/backend-runtime", relativePath),
                StandardCharsets.UTF_8));
    }

    // =========================================================================
    // 1. The function-typed completion drive
    // =========================================================================

    private static void testFunctionTypedCompletion() throws Exception {
        System.out.println("-- the function-typed completion: exactly one "
            + "DynamicFunctionValue keyed by the AWAIT op's result identity with the "
            + "completion descriptor, and the completion value callable through its "
            + "resolved class path --");
        Fixture fixture = compileProject(Map.of("src/app.deal", COMPLETION_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the completion drive lowers and passes the "
                + "closed gate: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp await = functionTypedAwait(app);
            check(await != null, "the completion drive produces the function-typed "
                + "AWAIT op");
            if (await == null) {
                return;
            }
            ValueId awaited = resultValueOf(await);
            FunctionExecutionBinding registration = registrationOf(app, awaited);
            check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue
                    dynamic
                    && dynamic.materializingOpId().equals(await.opId())
                    && dynamic.descriptor().equals(
                        ((KindPayload.AwaitPayload) await.payload()).completionDescriptor()),
                "the awaited completion registers exactly one DynamicFunctionValue "
                    + "keyed by the AWAIT result identity with the completion "
                    + "descriptor: " + registration);
            SemanticOp call = dynamicCall(app);
            check(call != null, "the completion value is called through the dynamic "
                + "callee shape");
            if (call == null) {
                return;
            }
            KindPayload.CallCallee.Dynamic callee = (KindPayload.CallCallee.Dynamic)
                ((KindPayload.CallPayload) call.payload()).callee();
            check(registrationOf(app, callee.callee())
                    instanceof FunctionExecutionBinding.DynamicFunctionValue,
                "the completion's dynamic call resolves the registered dynamic class");
            OpId dealCell = ((KindPayload.CallPayload) call.payload())
                .dynamicReturnBoundary().dealBodyBoundaryOpId();
            check(opOf(app, dealCell) != null, "the dynamic call records its DEAL-body "
                + "cell: " + dealCell);

            Path workspace = Files.createTempDirectory("battery-completion");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runAsyncEntry(project, result.tables(),
                        "probe", List.of(),
                        SemanticDifferentialHarness.Expectation.success("completion",
                            List.of(), "int:42"),
                        workspace, null);
                check(verdict.pass(), "the three-consumer completion drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(),
                    "the completion drive produced all three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, await.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the AWAIT published the completion value");
                    checkEq(1, eventCount(run, dealCell,
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the recorded call-owned DEAL-body cell "
                            + "ran exactly once");
                    checkEq(1, eventCount(run, dealCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded call-owned DEAL-body cell "
                            + "admitted the closure's returned value");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The dynamic cross-module corpus fixtures
    // =========================================================================

    private static void testCrossModuleFixtures() throws Exception {
        System.out.println("-- the dynamic cross-module corpus fixtures: their pinned "
            + "runtime-ok outcomes through the production artifacts on both targets --");

        // `modules/cross-module-shared-state-closure`: the fixture's own main
        // carries the class/table identity and call-order assertions.
        driveFixtureEntry("modules/cross-module-shared-state-closure.deal",
            Map.of("src/integration_state_lib.deal",
                readFixture("modules/integration_state_lib.deal")),
            List.of(), "null");

        // `equality/reference-identity-composite`: the K12 anchor (the
        // never-called `id`, the never-invoked stored closure `f2`, and the
        // f1/fa identity assertions).
        driveFixtureEntry("equality/reference-identity-composite.deal",
            Map.of(), List.of(), "null");

        // `modules/imported-closure-factory`: a cross-module call result into
        // a function-typed binding, then an invocation.
        driveFixtureDriver("modules/imported-closure-factory.deal",
            CLOSURE_FACTORY_DRIVER,
            Map.of("src/module_extra_lib.deal",
                readFixture("modules/module_extra_lib.deal")),
            "null");

        // `modules/imported-recursive-callback`: an imported recursive
        // function passed as a callback and executed.
        driveFixtureDriver("modules/imported-recursive-callback.deal",
            RECURSIVE_CALLBACK_DRIVER,
            Map.of("src/module_extra_lib.deal",
                readFixture("modules/module_extra_lib.deal")),
            "null", true);

        // `closures/closure-returned-from-module`: a cross-module call
        // result into a function-typed binding, then an invocation of the
        // returned closure (the module-local captured state advances).
        driveFixtureDriver("closures/closure-returned-from-module.deal",
            CLOSURE_RETURNED_DRIVER,
            Map.of("src/closure_batch2_lib.deal",
                readFixture("closures/closure_batch2_lib.deal")),
            "null");
    }

    /** Runs one corpus fixture as the entry module through the three consumers. */
    private static void driveFixtureEntry(String fixturePath,
            Map<String, String> companions, List<String> effects, String resultAtom)
            throws Exception {
        Map<String, String> sources = new LinkedHashMap<>(companions);
        sources.put("src/app.deal", readFixture(fixturePath));
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, fixturePath + " lowers through the one "
                + "project entry: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            Path workspace = Files.createTempDirectory("battery-fixture");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(fixturePath,
                            effects, resultAtom),
                        workspace);
                check(verdict.pass(), fixturePath + " executes with its pinned "
                    + "runtime-ok outcome on all three consumers: " + verdict.report());
                checkEq(3, verdict.runs().size(), fixturePath + " produced all three "
                    + "consumer runs");
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** Runs one corpus fixture as a companion of a driver entry. */
    private static void driveFixtureDriver(String fixturePath, String driver,
            Map<String, String> companions, String resultAtom) throws Exception {
        driveFixtureDriver(fixturePath, driver, companions, resultAtom, false);
    }

    /**
     * Runs one corpus fixture as a companion of a driver entry.
     *
     * @param recursive whether the fixture recurses (a recursive body
     *                  legitimately re-executes its own ops, so the
     *                  harness's one-START-per-op gate is bypassed and the
     *                  three traces are compared directly, exactly like the
     *                  landed cross-module recursive drive)
     */
    private static void driveFixtureDriver(String fixturePath, String driver,
            Map<String, String> companions, String resultAtom, boolean recursive)
            throws Exception {
        Map<String, String> sources = new LinkedHashMap<>(companions);
        sources.put("src/fixture.deal", readFixture(fixturePath));
        sources.put("src/app.deal", driver);
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, fixturePath + " lowers through the one "
                + "project entry: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            Path workspace = Files.createTempDirectory("battery-fixture-driver");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(fixturePath,
                            List.of(), resultAtom),
                        workspace);
                reportTraceDiff(verdict.runs());
                if (recursive) {
                    checkEq(3, verdict.runs().size(), fixturePath + " produced all "
                        + "three consumer runs: " + verdict.failures());
                    if (verdict.runs().size() != 3) {
                        return;
                    }
                    List<String> oracleTrace = traceLines(verdict.runs().get(0));
                    check(!oracleTrace.isEmpty(), fixturePath + ": the oracle "
                        + "produced events");
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        checkEq(oracleTrace, traceLines(run), fixturePath + ": the "
                            + run.consumer() + " trace equals the oracle's "
                            + "event-for-event");
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.Success success
                                && resultAtom.equals(success.resultAtom()),
                            fixturePath + ": " + run.consumer() + " completes with "
                                + "the pinned runtime-ok outcome: " + run.terminal());
                    }
                } else {
                    check(verdict.pass(), fixturePath + " executes with its pinned "
                        + "runtime-ok outcome on all three consumers: "
                        + verdict.report());
                    checkEq(3, verdict.runs().size(), fixturePath + " produced all "
                        + "three consumer runs");
                }
                if (!verdict.runs().isEmpty()) {
                    check(touchedModule(verdict.runs().get(0), new ModuleId("fixture")),
                        fixturePath + ": the oracle executed the fixture module's own "
                            + "ops");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // The host-containing class drives
    // =========================================================================

    private record HostFixture(Fixture compiled, ExecutableLoweredProject project,
                               SemanticLowerer.ProjectLoweringResult result) {
    }

    /**
     * Drives one sync project carrying a host module through the oracle
     * (with the scripted responder) and both production artifacts (with the
     * deployed host implementation). The drive's entry {@code main} throws
     * the pinned TEST_FAIL on any mismatch, so a successful artifact run is
     * the pinned outcome.
     */
    private static void driveHostProject(String what, Map<String, String> sources,
            String hostSpecifier, String hostDeclaration, String hostLuaForRun,
            String hostJavaClassName, String hostJava, HostResponderFactory responder,
            java.util.function.Consumer<ExecutableLoweredProject> irAssertions)
            throws Exception {
        Map<String, String> sourcesWithHost = new LinkedHashMap<>(sources);
        String declarationPath = "src/" + hostDeclarationFileName(hostSpecifier)
            + ".d.deal";
        sourcesWithHost.put(declarationPath, hostDeclaration);
        Fixture fixture = compileProject(sourcesWithHost,
            Map.of(hostSpecifier, declarationPath));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, what + " lowers and passes the closed "
                + "gate: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            irAssertions.accept(project);

            // The oracle with the scripted host seam.
            SemanticRuntimeModel.ConsumerRun oracle;
            try {
                oracle = SemanticOracle.executeProjectInits(project, result.tables(),
                    result.registries(), responder.create());
            } catch (RuntimeException rejected) {
                fail(what + ": the oracle rejects the drive: "
                    + rejected.getClass().getSimpleName() + ": "
                    + rejected.getMessage());
                return;
            }
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                what + ": the oracle completes runtime-ok: " + oracle.terminal()
                    + "\n" + oracle.comparisonReport());

            runHostLua(what, fixture, project, result, hostSpecifier, hostLuaForRun);
            runHostJvm(what, fixture, project, result, hostJavaClassName, hostJava);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The declaration file stem of one host specifier. */
    private static String hostDeclarationFileName(String hostSpecifier) {
        int slash = hostSpecifier.lastIndexOf('/');
        return slash < 0 ? hostSpecifier : hostSpecifier.substring(slash + 1);
    }

    /** Creates the scripted oracle responder of one host drive. */
    private interface HostResponderFactory {
        SemanticOracle.HostResponder create();
    }

    private static void runHostLua(String what, Fixture fixture,
            ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, String hostSpecifier,
            String hostLua) throws Exception {
        Path workspace = Files.createTempDirectory("battery-host-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve(hostSpecifier + ".lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, hostLua, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m))
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
            Path stderrFile = Files.createTempFile(workspace, "stderr", ".txt");
            builder.redirectError(stderrFile.toFile());
            Process process = builder.start();
            String stdout = new String(process.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int exit = process.waitFor();
            String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
            checkEq(0, exit, what + ": the LuaJIT production artifact executes: "
                + stdout + stderr);
            check(stdout.contains("OK"), what + ": the LuaJIT production artifact "
                + "completes runtime-ok: " + stdout.replace("\n", "\\n") + stderr);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void runHostJvm(String what, Fixture fixture,
            ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, String hostJavaClassName,
            String hostJava) throws Exception {
        Path workspace = Files.createTempDirectory("battery-host-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(hostJavaClassName + ".java"),
                hostJava, StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", hostJavaClassName + ".java"), workspace);
            checkEq(0, javac.exitCode(), what + ": the JVM production artifact "
                + "compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, className), workspace);
            checkEq(0, run.exitCode(), what + ": the JVM production artifact "
                + "executes runtime-ok: " + run.output());
        } finally {
            deleteRecursively(workspace);
        }
    }

    private record Outcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
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

    private static Outcome runProcess(List<String> command, Path workDir)
            throws Exception {
        Path stderrFile = Files.createTempFile(workDir, "stderr", ".txt");
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new Outcome(exit, stdout, stderr);
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

    /** The host class drive: a parameter callee holding a loaded host entry. */
    private static final String HOST_SOURCE = """
        import * as host from "host/battery"

        function apply(f: (x: int) => int, v: int): int {
          return f(v)
        }

        export function main(): null {
          let r: int = apply(host.twice, 21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "host class" };
          }
          return null;
        }
        """;

    private static final String HOST_DECLARATION = """
        export function twice(x: int): int;
        """;

    private static final String HOST_LUA = """
        return {
          twice = function(x) return x * 2 end,
        }
        """;

    private static String hostJava(String hostClass) {
        return """
            public final class %s {
              public static Object twice(int x) {
                return java.lang.Integer.valueOf(x * 2);
              }
            }
            """.formatted(hostClass);
    }

    /** The host class drive (M7 item 1). */
    private static void testHostClass() throws Exception {
        System.out.println("-- the host class: a function-typed parameter callee holding a "
            + "loaded host entry runs the host calling convention --");
        String hostClass = JvmBackend.classNameFor("host/battery");
        driveHostProject("host class", Map.of("src/app.deal", HOST_SOURCE),
            "host/battery", HOST_DECLARATION, HOST_LUA, hostClass, hostJava(hostClass),
            () -> new SemanticOracle.HostResponder() {
                @Override
                public SemanticOracle.Value loadedExport(ModuleId module, String export,
                        RuntimeDescriptor descriptor) {
                    return new SemanticOracle.Value.HostEntryValue(
                        (RuntimeDescriptor.Func) descriptor);
                }

                @Override
                public SyncOutcome call(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor,
                        List<SemanticOracle.Value> args) {
                    return new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(42));
                }
            },
            project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the host drive produces the dynamic callee shape");
                if (call == null) {
                    return;
                }
                FunctionExecutionBinding source = carrierRegistration(app, 0);
                check(source instanceof FunctionExecutionBinding.HostFunction host
                        && "host.battery".equals(host.hostModuleId().path())
                        && "twice".equals(host.exportName()),
                    "the host read registers the loaded entry's HOST class: " + source);
                OpId hostCell = ((KindPayload.CallPayload) call.payload())
                    .dynamicReturnBoundary().hostBoundaryOpId();
                check(opOf(app, hostCell) != null, "the dynamic call records its host "
                    + "cell: " + hostCell);
            });
    }

    /** The host-materialized value drive: a host crossing returning a function. */
    private static final String HOST_VALUE_SOURCE = """
        import * as host from "host/battery_fn"

        function apply(f: (x: int) => int, v: int): int {
          return f(v)
        }

        export function main(): null {
          let f: (x: int) => int = host.makeAdder(10)
          let r: int = apply(f, 5)
          if (r !== 15) {
            throw { code: "TEST_FAIL", message: "host-materialized value class" };
          }
          return null;
        }
        """;

    private static final String HOST_VALUE_DECLARATION = """
        export function makeAdder(base: int): (x: int) => int;
        """;

    private static final String HOST_VALUE_LUA = """
        local rt = require("deal.runtime")

        return {
          makeAdder = function(base)
            return rt.function_("(int)->int", function(x) return base + x end)
          end,
        }
        """;

    private static String hostValueJava(String hostClass) {
        return """
            public final class %s {
              public static Object makeAdder(int base) {
                return new $DealRt.Fn1_I_R_I() {
                  @Override
                  int invoke(int x) { return base + x; }
                };
              }
            }
            """.formatted(hostClass);
    }

    /** The host-materialized value class drive (M7 item 1). */
    private static void testHostMaterializedValueClass() throws Exception {
        System.out.println("-- the host-materialized value class: a function-typed host "
            + "crossing publishes a host-materialized carrier --");
        String hostClass = JvmBackend.classNameFor("host/battery_fn");
        driveHostProject("host-materialized value class",
            Map.of("src/app.deal", HOST_VALUE_SOURCE),
            "host/battery_fn", HOST_VALUE_DECLARATION, HOST_VALUE_LUA, hostClass,
            hostValueJava(hostClass),
            () -> new SemanticOracle.HostResponder() {
                @Override
                public SemanticOracle.Value loadedExport(ModuleId module, String export,
                        RuntimeDescriptor descriptor) {
                    return new SemanticOracle.Value.HostEntryValue(
                        (RuntimeDescriptor.Func) descriptor);
                }

                @Override
                public SyncOutcome call(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor,
                        List<SemanticOracle.Value> args) {
                    if (export.startsWith("@value#")) {
                        return new SyncOutcome.Returned(
                            new SemanticOracle.Value.IntValue(15));
                    }
                    return new SyncOutcome.Returned(new SemanticOracle.Value.HostEntryValue(
                        (RuntimeDescriptor.Func) descriptor.returnType()));
                }
            },
            project -> {
                LoweredModuleUnit app = project.modules().get(APP);
                SemanticOp crossing = null;
                for (SemanticOp op : app.ops()) {
                    if (op.payload() instanceof KindPayload.BoundaryPayload boundary
                            && boundary.kind() == deal.semantic.ir.BoundaryKind.HOST_TO_DEAL
                            && boundary.descriptor() instanceof RuntimeDescriptor.Func
                            && op.origin().parentOpId() != null) {
                        SemanticOp parent = opOf(app, op.origin().parentOpId());
                        if (parent != null
                                && parent.kind() == SemanticOpKind.CALL
                                && ((KindPayload.CallPayload) parent.payload()).mode()
                                    == deal.semantic.ir.CallMode.HOST) {
                            crossing = op;
                        }
                    }
                }
                check(crossing != null, "the host-value drive produces the "
                    + "function-typed producing crossing");
                if (crossing == null) {
                    return;
                }
                FunctionExecutionBinding registration = app.functionBindings().get(
                    new FunctionAllocationIdentity(
                        ((KindPayload.BoundaryPayload) crossing.payload()).input().id()));
                check(registration instanceof FunctionExecutionBinding.HostFunctionValue
                        value && value.materializingBoundaryOpId().equals(crossing.opId()),
                    "the crossing registers exactly one HostFunctionValue at the "
                        + "producing crossing: " + registration);
                SemanticOp call = dynamicCall(app);
                check(call != null, "the materialized value is called through the "
                    + "dynamic callee shape");
            });
    }

    // =========================================================================
    // The host async class drive (M7 item 2)
    // =========================================================================

    /**
     * The host async class drive (M7 item 2): a function-typed parameter
     * callee holding a loaded declared async host export, awaited through
     * the host operation handle. The oracle runs the scripted async host
     * seam; both production artifacts run the deployed host implementation
     * under the real toolchains, and the loaded async export records its own
     * invocation so the executed HOST class path is asserted, not inferred.
     */
    private static void testHostAsyncClass() throws Exception {
        System.out.println("-- the host class, awaited: a function-typed parameter "
            + "callee holding a loaded async host export runs the host operation "
            + "handle on the oracle and both production artifacts --");
        String hostClass = JvmBackend.classNameFor("host/battery_async");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/app.deal", HOST_ASYNC_SOURCE);
        String declarationPath = "src/battery_async.d.deal";
        sources.put(declarationPath, HOST_ASYNC_DECLARATION);
        Fixture fixture = compileProject(sources,
            Map.of("host/battery_async", declarationPath));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "host async class lowers and passes the "
                + "closed gate: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp start = dynamicAsyncStart(app);
            check(start != null, "the host async drive produces the dynamic "
                + "ASYNC_START shape");
            if (start == null) {
                return;
            }
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) start.payload();
            KindPayload.CallCallee.Dynamic callee =
                (KindPayload.CallCallee.Dynamic) payload.callee();
            check(registrationOf(app, callee.callee())
                    instanceof FunctionExecutionBinding.DynamicFunctionValue,
                "the awaited parameter callee registers the producer rule's dynamic "
                    + "materialization");
            FunctionExecutionBinding carrier = carrierRegistration(app, 0);
            check(carrier instanceof FunctionExecutionBinding.HostFunction host
                    && "host.battery_async".equals(host.hostModuleId().path())
                    && "fetchValue".equals(host.exportName()),
                "the host read registers the loaded async entry's HostFunction class: "
                    + carrier);
            SemanticOp taskCell = payload.returnBoundaryOpId() == null
                ? null : opOf(app, payload.returnBoundaryOpId());
            check(taskCell != null && callOwnedCell(app, taskCell),
                "the runtime-resolved host callee records the call-owned task cell: "
                    + taskCell);
            SemanticOp await = awaitOf(app);
            check(await != null, "the host async drive records its AWAIT");

            // The oracle with the scripted async host seam.
            SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.invokeAsyncEntry(
                project, result.tables(),
                new SemanticOracle.HostResponder() {
                    @Override
                    public SemanticOracle.Value loadedExport(ModuleId module,
                            String export, RuntimeDescriptor descriptor) {
                        return new SemanticOracle.Value.HostEntryValue(
                            (RuntimeDescriptor.Func) descriptor);
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
                            new SemanticOracle.Value.IntValue(42));
                    }
                },
                project.entryModule(), "probe", List.of());
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success success
                    && "int:42".equals(success.resultAtom()),
                "the host async class completes runtime-ok in the oracle: "
                    + oracle.terminal() + "\n" + oracle.comparisonReport());
            boolean started = false;
            for (SemanticRuntimeModel.EffectEvent effect : oracle.effects()) {
                if (effect.kind() == SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP
                        && effect.text().contains("host.battery_async.fetchValue")) {
                    started = true;
                }
            }
            check(started, "the oracle's dynamic HOST resolution starts the declared "
                + "async export under its operation label");
            if (await != null) {
                OpId completion = ((KindPayload.AwaitPayload) await.payload())
                    .completionBoundaryOpId();
                checkEq(1, eventCount(oracle, completion,
                        SemanticRuntimeModel.Phase.START),
                    "the AWAIT's single ASYNC_COMPLETION boundary admits the host "
                        + "completion exactly once");
            }
            if (taskCell != null) {
                checkEq(0, eventCount(oracle, taskCell.opId(),
                        SemanticRuntimeModel.Phase.START),
                    "a HOST resolution executes zero caller-side recorded task cells");
            }

            runHostAsyncLua(project, result, fixture.surface());
            runHostAsyncJvm(project, result, fixture.surface(), hostClass,
                hostAsyncJava(hostClass));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The LuaJIT production artifact of the host async class drive. */
    private static void runHostAsyncLua(ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, HostDeclarationSurface surface)
            throws Exception {
        Path workspace = Files.createTempDirectory("battery-host-async-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), surface), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve("host/battery_async.lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, HOST_ASYNC_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m))
                  else
                    print("ERR:" .. tostring(err))
                  end
                  os.exit(0)
                end
                local okE, resE = pcall(__asyncEntries["%s#probe"], "-", true)
                if not okE then
                  if type(resE) == "table" and resE.__d then
                    print("ERR:" .. resE.code .. "|" .. tostring(resE.m))
                  else
                    print("ERR:" .. tostring(resE))
                  end
                  os.exit(0)
                end
                print("OK VALUE:" .. tostring(resE))
                """.formatted(artifact.toAbsolutePath().toString(),
                    project.entryModule().path()), StandardCharsets.UTF_8);
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
            checkEq(0, exit, "host async class: the LuaJIT production artifact "
                + "executes: " + stdout + stderr);
            check(stdout.contains("HOST-START"),
                "host async class: the LuaJIT artifact's dynamic HOST class path "
                    + "invoked the loaded async export: "
                    + stdout.replace("\n", "\\n"));
            check(stdout.contains("OK VALUE:42"),
                "host async class: the LuaJIT production artifact completes with the "
                    + "pinned awaited value: " + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM production artifact of the host async class drive. */
    private static void runHostAsyncJvm(ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, HostDeclarationSurface surface,
            String hostClass, String hostJava) throws Exception {
        Path workspace = Files.createTempDirectory("battery-host-async-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, surface);
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(hostClass + ".java"), hostJava,
                StandardCharsets.UTF_8);
            OpId entry = asyncEntryOpId(project.modules().get(project.entryModule()),
                "probe");
            check(entry != null, "host async class: the unit records the async probe "
                + "entry");
            if (entry == null) {
                return;
            }
            Files.writeString(workspace.resolve("AsyncHostProbe.java"), """
                final class AsyncHostProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg);
                      return;
                    }
                    try {
                      java.lang.Object value = %s.ae%s("-", true,
                          new java.lang.Object[]{ });
                      System.out.println("OK VALUE:" + value);
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg);
                    }
                  }
                }
                """.formatted(className, className, entry.id()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", hostClass + ".java", "AsyncHostProbe.java"),
                workspace);
            checkEq(0, javac.exitCode(), "host async class: the JVM production "
                + "artifact compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "AsyncHostProbe"),
                workspace);
            checkEq(0, run.exitCode(), "host async class: the JVM production artifact "
                + "executes: " + run.output());
            check(run.stdout().contains("HOST-START"),
                "host async class: the JVM artifact's dynamic HOST class path invoked "
                    + "the loaded async export: " + run.stdout().replace("\n", "\\n"));
            check(run.stdout().contains("OK VALUE:42"),
                "host async class: the JVM production artifact completes with the "
                    + "pinned awaited value: " + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // The fault drives
    // =========================================================================

    private static final String NONFUNCTION_DRIVER = """
        import * as fix from "./fixture"

        export function main(): null {
          let r: int = fix.test_dynamic_nonfunction_to_function_runtime_error()
          return null;
        }
        """;

    private static final String SIG_MISMATCH_DRIVER = """
        import * as fix from "./fixture"

        export function main(): null {
          let r: int = fix.test_canonical_sig_mismatch()
          return null;
        }
        """;

    /**
     * One materialization-site fault drive: the corpus fixture executes as
     * a companion of a driver that calls its failing export, and the failure
     * row is pinned at the declared type annotation's span on the oracle and
     * both production artifacts. The pinned span is the corpus sidecar's
     * raw-file coordinate.
     */
    private static void driveFixtureDriverFailure(String what, String fixturePath,
            int pinnedLine, int pinnedColumn, String driver, String code,
            String messageStem, String expectedField, String actualField)
            throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/fixture.deal", readFixture(fixturePath));
        sources.put("src/app.deal", driver);
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, what + " lowers and passes the closed "
                + "gate: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit fixtureUnit = result.project().modules().get(
                new ModuleId("fixture"));
            SemanticOp boundary = null;
            for (SemanticOp op : fixtureUnit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && op.payload() instanceof KindPayload.BoundaryPayload payload
                        && payload.kind()
                            == deal.semantic.ir.BoundaryKind.VARIABLE_DECLARATION
                        && payload.descriptor() instanceof RuntimeDescriptor.Func) {
                    boundary = op;
                    break;
                }
            }
            check(boundary != null, what + ": the fixture carries its declaration "
                + "boundary");
            if (boundary == null) {
                return;
            }
            // The corpus pin is the declared type annotation's raw-file span;
            // the harness strips the fixture's classification headers before
            // the lexer, so the lowered source's line is the pinned raw line
            // minus the dropped headers preceding it.
            int dropped = droppedClassificationHeaders(fixturePath, pinnedLine);
            check(boundary.origin().span().startLine() == pinnedLine - dropped
                    && boundary.origin().span().startColumn() == pinnedColumn,
                what + ": the materialization site's origin is the declared type "
                    + "annotation's span — the corpus pin " + pinnedLine + ":"
                    + pinnedColumn + " (raw file) is " + (pinnedLine - dropped) + ":"
                    + pinnedColumn + " of the stripped source, the boundary at "
                    + boundary.origin().span().startLine() + ":"
                    + boundary.origin().span().startColumn());
            String origin = SemanticRuntimeModel.originAtom(boundary.origin().sourceId(),
                boundary.origin().span().startLine(),
                boundary.origin().span().startColumn());
            Path workspace = Files.createTempDirectory("battery-fault");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure(what, List.of(),
                            code, origin),
                        workspace);
                check(verdict.pass(), what + " fails closed with the pinned row at "
                    + "the declared annotation's span on all three consumers: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), what + " produced all three "
                    + "consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    SemanticRuntimeModel.Terminal terminal = run.terminal();
                    check(terminal
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && code.equals(failure.error().code())
                            && origin.equals(failure.error().origin())
                            && (messageStem == null
                                || failure.error().message().contains(messageStem))
                            && (expectedField == null
                                || expectedField.equals(failure.error().expected()))
                            && (actualField == null
                                || actualField.equals(failure.error().actual())),
                        what + ": " + run.consumer() + " projects " + code + " with "
                            + "the pinned fields at the annotation span: "
                            + terminal);
                    checkEq(1, eventCount(run, boundary.opId(),
                            SemanticRuntimeModel.Phase.FAILURE),
                        what + ": " + run.consumer() + " emits exactly one boundary "
                            + "FAILURE terminal");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The number of classification-header lines the harness's stripping
     * drops before one raw-file line (the raw-coordinate to lowered-source
     * line mapping of the corpus pins).
     */
    private static int droppedClassificationHeaders(String fixturePath, int rawLine)
            throws Exception {
        List<String> raw = Files.readAllLines(
            Path.of("test/conformance/backend-runtime", fixturePath),
            StandardCharsets.UTF_8);
        int dropped = 0;
        for (int i = 0; i < rawLine - 1 && i < raw.size(); i++) {
            if (ConformanceHarnessMetadata.isClassificationHeaderLine(raw.get(i))) {
                dropped++;
            }
        }
        return dropped;
    }

    /** One op with a replaced payload and its rewired contract snapshot. */
    private static SemanticOp rebuildOp(SemanticOp op, KindPayload payload) {
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contractOf(op, payload));
    }

    /** The rewired contract snapshot of one rebuilt payload. */
    private static deal.semantic.ir.OperationContractSnapshot contractOf(SemanticOp op,
            KindPayload payload) {
        deal.semantic.ir.OperationContractSnapshot placeholder =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(),
                op.resultType(), op.operandTypes(), null, payload, op.failurePolicy(),
                List.of(), "placeholder");
        String digest =
            deal.semantic.ir.ContractSnapshotCanonicalizer.digest(placeholder);
        return new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(),
            op.resultType(), op.operandTypes(), null, payload, op.failurePolicy(),
            List.of(), digest);
    }

    /** Rebuilds one lowered unit with a replaced op list (the doctoring seam). */
    private static LoweredModuleUnit corrupted(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return corrupted(unit, ops, unit.functionBindings());
    }

    private static LoweredModuleUnit corrupted(LoweredModuleUnit unit,
            List<SemanticOp> ops,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), bindings, ops);
    }

    /**
     * One op rebuilt as a {@code CONST} of a string under the same op id and
     * result identity (the untagged-carrier doctor).
     */
    private static SemanticOp constOp(SemanticOp op, String value) {
        KindPayload payload = new KindPayload.ConstPayload(
            new deal.semantic.ir.ScalarValue.String(value));
        List<RuntimeDescriptor> operandTypes = List.of();
        deal.semantic.ir.OperationContractSnapshot placeholder =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION,
                SemanticOpKind.CONST, RuntimeDescriptor.String.INSTANCE, operandTypes,
                null, payload, deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE,
                List.of(), "placeholder");
        String digest =
            deal.semantic.ir.ContractSnapshotCanonicalizer.digest(placeholder);
        return new SemanticOp(op.opId(), SemanticOpKind.CONST, op.origin(), op.result(),
            RuntimeDescriptor.String.INSTANCE, List.of(), operandTypes, payload,
            deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE,
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION,
                SemanticOpKind.CONST, RuntimeDescriptor.String.INSTANCE, operandTypes,
                null, payload, deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE,
                List.of(), digest));
    }

    /** Replaces one unit of a project closure with a doctored unit. */
    private static ExecutableLoweredProject projectWithUnit(
            ExecutableLoweredProject project, LoweredModuleUnit unit) {
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>(project.modules());
        modules.put(unit.moduleId(), unit);
        return new ExecutableLoweredProject(project.semanticProfile(),
            project.interfaceIndex(), modules, project.entryModule());
    }

    private static String validateUnit(LoweredModuleUnit unit) {
        return SemanticIrValidator.validate(unit, new SemanticIrValidator.ComparisonFacts(
            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
            productionInvocation().capabilityRegistryHash()))
            .map(deal.diagnostics.CompilerDiagnostic::message).orElse(null);
    }

    private static String validateProject(ExecutableLoweredProject project) {
        LoweredModuleUnit entry = project.modules().get(project.entryModule());
        return SemanticIrValidator.validate(project,
            new SemanticIrValidator.ComparisonFacts(entry.interfaceHash(),
                SemanticProfile.DEAL_V1_2_INT32,
                productionInvocation().capabilityRegistryHash()))
            .map(deal.diagnostics.CompilerDiagnostic::message).orElse(null);
    }

    private static void testFaultDrives() throws Exception {
        System.out.println("-- the fault drives: each fails closed with its pinned "
            + "projection and origin --");

        // 1. A non-function carrier at a materialization site: the pinned
        //    E8001 expected-function row at the declared annotation's span
        //    (the sidecar's raw-file pin, line 8 column 10).
        driveFixtureDriverFailure("non-function materialization",
            "type-system/dynamic-nonfunction-to-function-e8001.deal", 8, 10,
            NONFUNCTION_DRIVER, "E8001", "expected function", "function", "int");

        // 2. A differing carried signature: the pinned E8010 row at the
        //    declared annotation's span (the sidecar's raw-file pin, line 12
        //    column 10).
        driveFixtureDriverFailure("carried-signature mismatch",
            "descriptors/canonical-sig-mismatch-e8010.deal", 12, 10,
            SIG_MISMATCH_DRIVER, "E8010", "function signature mismatch",
            "(int)->int", "(int)->string");

        // 3. A swapped recorded cell form: the DEAL-body entry is not the
        //    closed FUNCTION_RETURN cell. The drive pin is the exact rule
        //    name and the exact DEAL-body cell clause.
        Fixture variant = compileProject(Map.of("src/app.deal", DEAL_BODY_SOURCE));
        if (variant != null) {
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(variant);
                check(result.project() != null, "the form-swap drive lowers: "
                    + result.diagnostics());
                if (result.project() != null) {
                    LoweredModuleUnit app = result.project().modules().get(APP);
                    SemanticOp call = dynamicCall(app);
                    OpId dealCell = ((KindPayload.CallPayload) call.payload())
                        .dynamicReturnBoundary().dealBodyBoundaryOpId();
                    List<SemanticOp> ops = new ArrayList<>();
                    for (SemanticOp op : app.ops()) {
                        if (op.opId().equals(dealCell)
                                && op.payload() instanceof KindPayload.BoundaryPayload
                                    payload) {
                            KindPayload.BoundaryPayload swapped =
                                new KindPayload.BoundaryPayload(
                                    deal.semantic.ir.BoundaryKind.HOST_TO_DEAL,
                                    payload.descriptor(), payload.input(),
                                    payload.realization());
                            ops.add(rebuildOp(op, swapped));
                        } else {
                            ops.add(op);
                        }
                    }
                    String verdict = validateUnit(corrupted(app, ops));
                    check(verdict != null
                            && verdict.contains("validatorRule R-BOUNDARY-TRIPLE,")
                            && verdict.contains("the DYNAMIC CALL's DEAL-body return "
                                + "boundary must be FUNCTION_RETURN"),
                        "a swapped recorded cell form fails the closed gate with exactly "
                            + "R-BOUNDARY-TRIPLE and its pinned DEAL-body cell clause: "
                            + verdict);
                }
            } finally {
                deleteRecursively(variant.root());
            }
        }

        // 4a. A DynamicFunctionValue-registered value named inline in a
        //     CallCallee.Static payload: the closed nested shape set rejects
        //     the dynamic shape at the static callee position (R-ENUM).
        Fixture staticCallee = compileProject(Map.of("src/app.deal", DEAL_BODY_SOURCE));
        if (staticCallee != null) {
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(staticCallee);
                check(result.project() != null, "the static-callee drive lowers: "
                    + result.diagnostics());
                if (result.project() != null) {
                    LoweredModuleUnit app = result.project().modules().get(APP);
                    SemanticOp call = dynamicCall(app);
                    KindPayload.CallCallee.Dynamic callee =
                        (KindPayload.CallCallee.Dynamic)
                            ((KindPayload.CallPayload) call.payload()).callee();
                    FunctionExecutionBinding binding =
                        registrationOf(app, callee.callee());
                    check(binding instanceof FunctionExecutionBinding
                            .DynamicFunctionValue,
                        "the static-callee drive names the registered dynamic value: "
                            + binding);
                    if (binding != null) {
                        List<SemanticOp> ops = new ArrayList<>();
                        for (SemanticOp op : app.ops()) {
                            if (op.opId().equals(call.opId())
                                    && op.payload() instanceof KindPayload.CallPayload
                                        payload) {
                                KindPayload.CallPayload replaced =
                                    new KindPayload.CallPayload(payload.mode(),
                                        new KindPayload.CallCallee.Static(binding),
                                        payload.signature(),
                                        payload.parameterBoundaryOpIds(), null, null,
                                        payload.bodyBlock(), payload.externalEntryRef());
                                ops.add(rebuildOp(op, replaced));
                            } else {
                                ops.add(op);
                            }
                        }
                        String verdict = validateUnit(corrupted(app, ops));
                        check(verdict != null
                                && verdict.contains("validatorRule R-ENUM,")
                                && verdict.contains("dynamicFunctionValue")
                                && verdict.contains("in a closed "
                                    + "FunctionExecutionBinding shape position"),
                            "a DynamicFunctionValue-registered value named inline as a "
                                + "static callee fails the closed gate with R-ENUM: "
                                + verdict);
                    }
                }
            } finally {
                deleteRecursively(staticCallee.root());
            }
        }

        // 4b. The same registration reached through an Indirect callee
        //     identity: the re-recorded single return boundary replaces the
        //     dynamic cell set, so the callee-position exclusivity clause is
        //     the failing rule (R-FUNCTION-BINDING).
        Fixture indirectCallee = compileProject(Map.of("src/app.deal", DEAL_BODY_SOURCE));
        if (indirectCallee != null) {
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(indirectCallee);
                check(result.project() != null, "the indirect-callee drive lowers: "
                    + result.diagnostics());
                if (result.project() != null) {
                    LoweredModuleUnit app = result.project().modules().get(APP);
                    SemanticOp call = dynamicCall(app);
                    KindPayload.CallCallee.Dynamic callee =
                        (KindPayload.CallCallee.Dynamic)
                            ((KindPayload.CallPayload) call.payload()).callee();
                    KindPayload.DynamicReturnBoundary dynamic =
                        ((KindPayload.CallPayload) call.payload())
                            .dynamicReturnBoundary();
                    List<SemanticOp> ops = new ArrayList<>();
                    for (SemanticOp op : app.ops()) {
                        if (op.opId().equals(call.opId())
                                && op.payload() instanceof KindPayload.CallPayload
                                    payload) {
                            KindPayload.CallPayload replaced =
                                new KindPayload.CallPayload(
                                    deal.semantic.ir.CallMode.INDIRECT,
                                    new KindPayload.CallCallee.Indirect(callee.callee()),
                                    payload.signature(),
                                    payload.parameterBoundaryOpIds(),
                                    dynamic.dealBodyBoundaryOpId(), null, null, null);
                            ops.add(rebuildOp(op, replaced));
                        } else if (op.opId().equals(dynamic.hostBoundaryOpId())
                                || op.opId().equals(dynamic.externalBoundaryOpId())) {
                            // The re-recorded indirect call carries the single
                            // DEAL-body return boundary; the other two dynamic
                            // cells are no longer part of any invocation shape.
                            continue;
                        } else {
                            ops.add(op);
                        }
                    }
                    String verdict = validateUnit(corrupted(app, ops));
                    check(verdict != null
                            && verdict.contains("validatorRule R-FUNCTION-BINDING,")
                            && verdict.contains("resolves its callee to a "
                                + "DynamicFunctionValue registration"),
                        "a DynamicFunctionValue registration reached through an Indirect "
                            + "callee identity fails the callee-position exclusivity "
                            + "clause (R-FUNCTION-BINDING): " + verdict);
                }
            } finally {
                deleteRecursively(indirectCallee.root());
            }
        }

        // 5. An untagged carrier at a dynamic call: the carrier-producing op
        //    is replaced by a non-function CONST and the registration is
        //    removed, so the dispatch reads no class tag. The oracle fails
        //    closed as a producer defect; the real LuaJIT and javac/java
        //    artifacts project the pinned E8001 expected-function row at the
        //    call origin with the carrier's actual kind and the
        //    expected/actual fields.
        Fixture residue = compileProject(Map.of("src/app.deal", DEAL_BODY_SOURCE));
        if (residue != null) {
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(residue);
                check(result.project() != null, "the residue drive lowers: "
                    + result.diagnostics());
                if (result.project() != null) {
                    LoweredModuleUnit app = result.project().modules().get(APP);
                    SemanticOp call = dynamicCall(app);
                    ValueId calleeValue = ((KindPayload.CallCallee.Dynamic)
                        ((KindPayload.CallPayload) call.payload()).callee()).callee();
                    String origin = SemanticRuntimeModel.originAtom(
                        call.origin().sourceId(), call.origin().span().startLine(),
                        call.origin().span().startColumn());
                    List<SemanticOp> ops = new ArrayList<>();
                    for (SemanticOp op : app.ops()) {
                        if (calleeValue.equals(resultValueOf(op))) {
                            ops.add(constOp(op, "carrier"));
                        } else {
                            ops.add(op);
                        }
                    }
                    Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
                        new LinkedHashMap<>(app.functionBindings());
                    bindings.remove(new FunctionAllocationIdentity(calleeValue.id()));
                    LoweredModuleUnit doctored = corrupted(app, ops, bindings);
                    ExecutableLoweredProject doctoredProject =
                        projectWithUnit(result.project(), doctored);
                    String gate = validateProject(doctoredProject);
                    check(gate == null, "the closed gate accepts the residue drive: "
                        + gate);
                    if (gate == null) {
                        String oracleFailure = null;
                        try {
                            SemanticOracle.executeProjectInits(doctoredProject,
                                result.tables(), result.registries(), null);
                        } catch (RuntimeException rejected) {
                            oracleFailure = rejected.getClass().getSimpleName() + ": "
                                + rejected.getMessage();
                        }
                        check(oracleFailure != null && oracleFailure.contains(
                                "has no registered FunctionExecutionBinding (producer "
                                    + "defect)"),
                            "the oracle fails closed on the unresolvable carrier as a "
                                + "producer defect naming the missing registration: "
                                + oracleFailure);
                        runResidueLua(doctoredProject, result, residue.surface(), origin);
                        runResidueJvm(doctoredProject, result, residue.surface(), origin);
                    }
                }
            } finally {
                deleteRecursively(residue.root());
            }
        }
    }

    /** The real LuaJIT artifact of the untagged-carrier residue drive. */
    private static void runResidueLua(ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, HostDeclarationSurface surface,
            String origin) throws Exception {
        Path workspace = Files.createTempDirectory("battery-residue-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), surface), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if ok then print("OK") os.exit(0) end
                if type(err) == "table" and err.__d then
                  print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                    .. tostring(err.o) .. "|" .. tostring(err.e or "-") .. "|"
                    .. tostring(err.a or "-"))
                else
                  print("ERR:" .. tostring(err))
                end
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
            checkEq(0, exit, "the residue LuaJIT artifact executes: " + stdout + stderr);
            check(stdout.contains("ERR:E8001|expected function, got string|" + origin
                    + "|function|string"),
                "the residue LuaJIT artifact projects the pinned E8001 "
                    + "\"expected function, got string\" row with the expected/actual "
                    + "fields at the call origin: " + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The real javac/java artifact of the untagged-carrier residue drive. */
    private static void runResidueJvm(ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult result, HostDeclarationSurface surface,
            String origin) throws Exception {
        Path workspace = Files.createTempDirectory("battery-residue-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, surface);
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("ResidueProbe.java"), """
                final class ResidueProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                      System.out.println("OK");
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin + "|" + error.expected + "|"
                          + error.actual);
                    }
                  }
                }
                """.formatted(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "ResidueProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the residue JVM artifact compiles: "
                + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "ResidueProbe"),
                workspace);
            checkEq(0, run.exitCode(), "the residue JVM artifact executes: "
                + run.output());
            check(run.stdout().contains("ERR:E8001|expected function, got string|"
                    + origin + "|function|string"),
                "the residue JVM artifact projects the pinned E8001 "
                    + "\"expected function, got string\" row with the expected/actual "
                    + "fields at the call origin: " + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /**
     * The closed-set guard: the extension is additive (a closed binding
     * member), so the closed operation-kind, boundary-kind, failure-policy,
     * and payload-record sets keep their landed members and the drives carry
     * no {@code CONSTRUCT_UNLOWERED}/{@code RETAINED_ABI_DEFERRED} (every
     * drive's project lowers, asserted by the drives themselves).
     */
    private static void testNoExtension() {
        System.out.println("-- no extension: the closed operation-kind, boundary-kind, "
            + "failure-policy, and payload-record sets are unchanged --");
        checkEq(55, SemanticOpKind.values().length,
            "the closed operation-kind set keeps its 55 members");
        checkEq(27, deal.semantic.ir.BoundaryKind.values().length,
            "the closed boundary-kind set keeps its 27 members (the bytes element "
                + "cells of ISSUE-0626)");
        checkEq(27, deal.semantic.ir.FailurePolicyId.values().length,
            "the closed failure-policy set keeps its 27 members (the three bytes "
                + "policies of ISSUE-0626)");
        checkEq(55, KindPayload.class.getPermittedSubclasses().length,
            "the closed payload-record set keeps its 55 landed records");
        checkEq(7, FunctionExecutionBinding.class.getPermittedSubclasses().length,
            "the closed function-execution-binding set keeps its seven landed members "
                + "(the additive DynamicFunctionValue and IntrinsicFunction members "
                + "included)");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Dynamic Dispatch Battery Tests (ISSUE-0682) ===");
        testFunctionTypedCompletion();
        testCrossModuleFixtures();
        testDealBodyClass();
        testDealBodyAsyncClass();
        testAdapterClass();
        testAdapterAsyncClass();
        testStdlibCallableClass();
        testIntrinsicConversionClass();
        testSharedBodyExternalClass();
        testSharedBodyExternalAsyncClass();
        testHostClass();
        testHostMaterializedValueClass();
        testHostAsyncClass();
        testFaultDrives();
        testNoExtension();
        System.out.println();
        if (failed > 0) {
            System.out.println("Dynamic dispatch battery: " + passed + " passed, "
                + failed + " failed");
            System.exit(1);
        }
        System.out.println("Dynamic dispatch battery: " + passed + " passed, 0 failed");
    }
}
