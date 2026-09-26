package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.ClassFactoryRegistry;
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
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.semantic.ir.ExecutableLoweredProject;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0678: the dispatch realization for the cataloged stdlib callable and the
 * asynchronous host class, with the oracle's cross-module callee-body resolution
 * (design sources {@code function-typed-value-materialization-and-dispatch} M5
 * — the class table's HOST sub-classes, the async classes, and the oracle's
 * owning-unit body terminal — and {@code conversion-intrinsic-function-values}
 * J3/J4; read-only: {@code dynamic-call-shape-production-and-emission} Y2/Y5/Y6,
 * {@code semantic-ir-construct-coverage-cutover} K2/K5).
 *
 * <ol>
 *   <li><b>The cataloged-callable class (three consumers).</b> A function-typed
 *       parameter callee whose runtime carrier is the closed catalog row's
 *       memoized callable is classified from the carrier's own tag
 *       ({@code __sid} on LuaJIT, {@code JvmRuntime.StdlibFunctionValue} on the
 *       JVM — never from a checked descriptor or a callee spelling), runs the
 *       catalog row's one invoker with the invoking CALL op's own context (the
 *       console effect and the shared algorithm produce the identical
 *       observables as the direct {@code STDLIB_CALL} arm), and the recorded
 *       {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell executes exactly
 *       once at the call origin. The oracle resolves the same catalog entry and
 *       executes the same shared algorithm — never a host responder. The read's
 *       own registration used as the call callee (the static/indirect arm of
 *       {@code let g: (x: string) => null = console.log; g("…")}) takes the
 *       same catalog row through the host cell family, on all three
 *       consumers.</li>
 *   <li><b>The cataloged-callable failure projection.</b> An algorithm failure
 *       through the dynamically dispatched callable publishes the invoking
 *       <em>CALL</em> op's FAILURE event under its own kind (the row invoker
 *       receives the invoking op's kind label) with the pinned row text at the
 *       call origin, identically on the oracle, the LuaJIT artifact, and the JVM
 *       artifact.</li>
 *   <li><b>The asynchronous host class (oracle and both artifacts).</b> A
 *       function-typed parameter callee whose runtime carrier is a loaded host
 *       surface entry starts the declared async export through the host calling
 *       convention, binds the returned operation handle to the recorded token
 *       under the declared identity's operation label, and completes at the
 *       single {@code AWAIT}; the recorded task cell of a HOST resolution
 *       executes zero times (the oracle's landed dynamic HOST arm).</li>
 *   <li><b>The oracle's owning-unit body terminal.</b> A cross-module callee
 *       value (a call result from another module's exported factory, or the
 *       same awaited) resolves the value-channel class and runs its body through
 *       the unit its function id belongs to — the callee unit's own membership
 *       table and module context — so the callee unit's body-local return cell
 *       executes and the caller's recorded call-owned cell executes exactly
 *       once; all three consumers agree on the events and the terminal.</li>
 *   <li><b>The fail-closed residue.</b> A carrier outside the closed classes
 *       (an untagged value at a dynamic async site) still projects the pinned
 *       E8001 {@code expected function} at the call origin in the oracle and
 *       both artifacts, and the emitted dispatch retains its residue branch.</li>
 * </ol>
 */
public class DynamicClassDispatchTest {

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
    private static final ModuleId HOST = new ModuleId("host.dyn_async");

    // =========================================================================
    // Fixtures
    // =========================================================================

    /** The stdlib-callable drive: a parameter callee holding the catalog callable. */
    private static final String STDLIB_SOURCE = """
        import * as console from "std/console"

        function invoke(f: (x: string) => null): null {
          f("stdlib-value")
          return null
        }

        export function main(): null {
          invoke(console.log)
          return null
        }
        """;

    /** The stdlib-callable indirect drive: the read's own registration as callee. */
    private static final String STDLIB_INDIRECT_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let g: (x: string) => null = console.log
          g("stdlib-indirect")
          return null
        }
        """;

    /** The stdlib failure drive: an algorithm failure through the dynamic callable. */
    private static final String STDLIB_FAILURE_SOURCE = """
        import * as json from "std/json"

        function invoke(f: (s: string) => table): table {
          return f("{")
        }

        export function main(): null {
          let t: table = invoke(json.parse)
          return null
        }
        """;

    /** The cross-module body drive: another unit's factory result into a parameter. */
    private static final String CROSS_LIB_SOURCE = """
        function double(x: int): int {
          return x * 2
        }

        export function pick(): (x: int) => int {
          return double
        }
        """;

    private static final String CROSS_APP_SOURCE = """
        import * as lib from "./lib"

        function apply(f: (x: int) => int, v: int): int {
          return f(v)
        }

        export function main(): null {
          let f: (x: int) => int = lib.pick()
          let r: int = apply(f, 21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "cross-module body" }
          }
          return null
        }
        """;

    /** The awaited cross-module body drive: another unit's async closure. */
    private static final String CROSS_ASYNC_LIB_SOURCE = """
        export function pickAsync(): async (x: int) => int {
          return async function(x: int): int {
            return x * 2
          }
        }
        """;

    private static final String CROSS_ASYNC_APP_SOURCE = """
        import * as lib from "./lib"

        async function invoke(f: async (x: int) => int, v: int): int {
          return await f(v)
        }

        export async function probe(): int {
          let f: async (x: int) => int = lib.pickAsync()
          return await invoke(f, 21)
        }

        export function main(): null {
          return null
        }
        """;

    /** The asynchronous host class drive: a loaded host async export into a parameter. */
    private static final String HOST_DECLARATION = """
        export async function fetchCount(): int;
        """;

    private static final String HOST_APP_SOURCE = """
        import * as host from "host/dyn_async"

        async function drive(f: async () => int): int {
          return await f()
        }

        export async function probe(): int {
          return await drive(host.fetchCount)
        }

        export function main(): null {
          return null
        }
        """;

    private static final String HOST_LUA = """
        local rt = require("deal.runtime")

        return {
          fetchCount = function()
            return rt.async_start(function() return 42 end)
          end,
        }
        """;

    private static String hostJava(String hostClass) {
        return """
            import java.util.concurrent.CompletableFuture;

            public final class %s {
              public static Object fetchCount() {
                return CompletableFuture.completedFuture(
                    java.lang.Long.valueOf(42L));
              }
            }
            """.formatted(hostClass);
    }

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
        Path root = Files.createTempDirectory("dynamic-class-dispatch");
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

    private static SemanticOp dynamicAsyncStart(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.AsyncStartPayload start
                    && start.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    /** The dynamic callee's value channel resolution of one invocation. */
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

    /** The single async EXTERNAL_ENTRY op of one export of one unit. */
    private static OpId asyncEntryOp(LoweredModuleUnit unit, String exportName) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                    && op.payload() instanceof KindPayload.ExternalEntryPayload entry
                    && entry.async() && entry.exportName().equals(exportName)) {
                return op.opId();
            }
        }
        return null;
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

    private static List<SemanticRuntimeModel.TraceEvent> eventsOf(
            SemanticRuntimeModel.ConsumerRun run, OpId op) {
        List<SemanticRuntimeModel.TraceEvent> events = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)) {
                events.add(event);
            }
        }
        return events;
    }

    // =========================================================================
    // The process surface (the real toolchains)
    // =========================================================================

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

    // =========================================================================
    // 1. The cataloged-callable class on all three consumers
    // =========================================================================

    private static void testStdlibCallableClass() throws Exception {
        System.out.println("-- the cataloged stdlib callable: a function-typed parameter "
            + "callee resolves the catalog row on the oracle, the LuaJIT artifact, and "
            + "the JVM artifact --");
        Fixture fixture = compileProject(
            Map.of("src/app.deal", STDLIB_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the stdlib drive lowers through the one "
                + "project entry: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = dynamicCall(app);
            check(call != null, "the stdlib drive produces the dynamic callee shape");
            if (call == null) {
                return;
            }
            KindPayload.CallCallee.Dynamic callee = (KindPayload.CallCallee.Dynamic)
                ((KindPayload.CallPayload) call.payload()).callee();
            FunctionExecutionBinding registration = app.functionBindings().get(
                new FunctionAllocationIdentity(callee.callee().id()));
            check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
                "the producer rule registers the parameter callee's dynamic "
                    + "materialization: " + registration);
            FunctionExecutionBinding source = carrierRegistration(app, 0);
            check(source instanceof FunctionExecutionBinding.HostFunction host
                    && "std.console".equals(host.hostModuleId().path())
                    && "log".equals(host.exportName()),
                "the carrier's own read registers the cataloged callable's HOST class: "
                    + source);
            OpId hostCell = ((KindPayload.CallPayload) call.payload())
                .dynamicReturnBoundary().hostBoundaryOpId();
            check(opOf(app, hostCell) != null, "the dynamic call records its "
                + "HOST_TO_DEAL + HOST_SYNC_RETURN cell: " + hostCell);

            // The emitted dispatch surface: tag-only class resolution and the
            // catalog row invoker with the invoking call's context.
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            String jvm = JvmSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(),
                JvmBackend.classNameFor(project.entryModule().path()),
                fixture.surface()).source();
            check(lua.contains("if v.__sid ~= nil then return \"HOST\" end"),
                "the LuaJIT classification recognizes the cataloged carrier's own tag");
            check(lua.contains("if __dynC.__sid ~= nil then")
                    && lua.contains("__resT = __dynC.__fn(\"CALL\", ")
                    && lua.contains("__stdlibInvoke(kind, sid, opKey, digest, parent, "
                        + "origin, ...)"),
                "the LuaJIT HOST row runs the one row invoker with the invoking call's "
                    + "context and the CALL kind");
            check(jvm.contains("instanceof JvmRuntime.StdlibFunctionValue)"),
                "the JVM classification admits the cataloged callable carrier");
            check(jvm.contains("JvmRuntime.invokeStdlibCallable((JvmRuntime."
                    + "StdlibFunctionValue) "),
                "the JVM HOST row runs the catalog row's invoker with the invoking "
                    + "call's context");

            Path workspace = Files.createTempDirectory("dynamic-stdlib-drive");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success("stdlib class",
                            List.of("stdlib-value"), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer stdlib drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(),
                    "the stdlib drive produced all three consumer runs");
                if (verdict.runs().size() != 3) {
                    return;
                }
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the dynamic CALL started once");
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the dynamic CALL published its checked value");
                    checkEq(1, eventCount(run, hostCell,
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the recorded HOST cell started exactly once");
                    checkEq(1, eventCount(run, hostCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST cell admitted the "
                            + "catalog row's result");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The indirect-arm drive (ISSUE-0678; the task's verification shape): the
     * read's own registration is the call callee, so the static/indirect host
     * arm must run the closed catalog row's invoker with the invoking call's
     * context — the same algorithm, effect, and recorded return cell the direct
     * {@code STDLIB_CALL} arm produces — on the oracle and both artifacts.
     */
    private static void testStdlibCalleeIndirectArm() throws Exception {
        System.out.println("-- the cataloged stdlib callable in the indirect arm: the read's "
            + "own registration as the call callee runs the catalog row on the oracle "
            + "and both artifacts --");
        Fixture fixture = compileProject(
            Map.of("src/app.deal", STDLIB_INDIRECT_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the indirect stdlib drive lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = null;
            for (SemanticOp op : app.ops()) {
                if (op.payload() instanceof KindPayload.CallPayload payload
                        && payload.callee() instanceof KindPayload.CallCallee.Static
                            staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction host
                        && "std.console".equals(host.hostModuleId().path())) {
                    call = op;
                }
            }
            check(call != null, "the indirect stdlib drive produces the host-shaped "
                + "static callee arm");
            if (call == null) {
                return;
            }
            OpId hostCell = ((KindPayload.CallPayload) call.payload())
                .returnBoundaryOpId();
            check(hostCell != null, "the indirect stdlib drive records its "
                + "HOST_TO_DEAL + HOST_SYNC_RETURN cell: " + hostCell);

            String lua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            String jvm = JvmSemanticEmitter.emitProject(project, result.tables(),
                result.registries()).source();
            check(lua.contains(".__sid ~= nil then") && lua.contains(".__fn(\"CALL\""),
                "the LuaJIT host arm dispatches the cataloged carrier through the "
                    + "row invoker with the invoking call's context");
            check(lua.contains("local __rt = require(\"deal.runtime\")"),
                "the LuaJIT chunk of a stdlib-only project binds the host prelude "
                    + "its recorded host cells reference");
            check(jvm.contains("JvmRuntime.invokeStdlibCallable(JvmRuntime.stdlibCallable("),
                "the JVM host arm dispatches the cataloged carrier through the row "
                    + "invoker with the invoking call's context");
            check(jvm.contains("static java.lang.Object __hostParamCheck("),
                "the JVM chunk of a stdlib-only project carries the host seam its "
                    + "recorded host cells reference");

            Path workspace = Files.createTempDirectory("dynamic-stdlib-indirect");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "stdlib indirect arm", List.of("stdlib-indirect"), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer indirect stdlib drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(),
                    "the indirect stdlib drive produced all three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the indirect call published the catalog "
                            + "row's checked result");
                    checkEq(1, eventCount(run, hostCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST cell admitted the "
                            + "catalog row's result");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The cataloged-callable failure projection
    // =========================================================================

    private static void testStdlibCallableFailure() throws Exception {
        System.out.println("-- the cataloged callable's algorithm failure through the "
            + "dynamic call: the invoking CALL op's FAILURE kind and the pinned row "
            + "text at the call origin in all three consumers --");
        Fixture fixture = compileProject(
            Map.of("src/app.deal", STDLIB_FAILURE_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the stdlib failure drive lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = dynamicCall(app);
            if (call == null) {
                fail("the stdlib failure drive produces the dynamic callee shape");
                return;
            }
            String origin = call.origin().sourceId() + ":" + call.origin().span().startLine()
                + ":" + call.origin().span().startColumn();
            Path workspace = Files.createTempDirectory("dynamic-stdlib-failure");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.failure(
                            "stdlib class failure", List.of(),
                            "E8001", origin),
                        workspace);
                check(verdict.pass(), "the three-consumer stdlib failure drive passes "
                    + "(the CALL op's own FAILURE kind): " + verdict.report());
                if (verdict.runs().isEmpty()) {
                    return;
                }
                SemanticRuntimeModel.ConsumerRun oracle = verdict.runs().get(0);
                check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                        failure && "E8001".equals(failure.error().code())
                        && failure.error().message().startsWith(
                            "JSON parse error at position 2: "),
                    "the oracle projects the catalog row's pinned failure text: "
                        + oracle.terminal());
                boolean sawCallFailure = false;
                for (SemanticRuntimeModel.TraceEvent event : eventsOf(oracle, call.opId())) {
                    if (event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                        sawCallFailure = true;
                        checkEq(SemanticOpKind.CALL, event.kind(),
                            "the cataloged callable's failure event carries the "
                                + "invoking CALL op's own kind");
                    }
                }
                check(sawCallFailure, "the oracle publishes the CALL op's FAILURE "
                    + "terminal for the cataloged callable's algorithm failure");
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The oracle's owning-unit body terminal (the cross-module callee value)
    // =========================================================================

    private static void testCrossModuleBody() throws Exception {
        System.out.println("-- the cross-module callee value: the callee unit's body "
            + "runs under its own unit and module context on the oracle and both "
            + "artifacts --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", CROSS_LIB_SOURCE);
        sources.put("src/app.deal", CROSS_APP_SOURCE);
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the cross-module drive lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit lib = project.modules().get(LIB);
            check(lib != null, "the cross-module closure carries the callee module");
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = dynamicCall(app);
            if (call == null) {
                fail("the cross-module drive produces the dynamic callee shape");
                return;
            }
            OpId dealCell = ((KindPayload.CallPayload) call.payload())
                .dynamicReturnBoundary().dealBodyBoundaryOpId();
            Path workspace = Files.createTempDirectory("dynamic-cross-body");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success("cross body",
                            List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer cross-module drive passes: "
                    + verdict.report());
                if (verdict.runs().isEmpty()) {
                    return;
                }
                SemanticRuntimeModel.ConsumerRun oracle = verdict.runs().get(0);
                check(touchedModule(oracle, LIB), "the oracle executed the callee "
                    + "unit's own ops (the resolved body under its owning unit)");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, dealCell,
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the recorded call-owned cell ran exactly "
                            + "once");
                    checkEq(1, eventCount(run, dealCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded call-owned cell admitted the "
                            + "returned value");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testCrossModuleAsyncBody() throws Exception {
        System.out.println("-- the awaited cross-module callee value: the callee unit's "
            + "async body runs under its own unit and the recorded task cell executes "
            + "once on the oracle and both production artifacts --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", CROSS_ASYNC_LIB_SOURCE);
        sources.put("src/app.deal", CROSS_ASYNC_APP_SOURCE);
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the awaited cross-module drive lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp start = dynamicAsyncStart(app);
            if (start == null) {
                fail("the awaited cross-module drive produces the dynamic async shape");
                return;
            }
            OpId taskCell = ((KindPayload.AsyncStartPayload) start.payload())
                .returnBoundaryOpId();
            check(taskCell != null, "the dynamic async start records its single task "
                + "cell");
            // The oracle: the callee unit's async body runs under its own unit
            // (the value-channel LoweredBody of another module's function id),
            // and the caller-side wrapper runs the recorded call-owned task cell
            // exactly once before the token completes.
            SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.invokeAsyncEntry(
                project, result.tables(), null, APP, "probe", List.of());
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    success && "int:42".equals(success.resultAtom()),
                "the oracle completes the awaited cross-module body with the callee "
                    + "unit's own result: " + oracle.comparisonReport());
            check(touchedModule(oracle, LIB), "the oracle executed the callee unit's "
                + "async body under its own unit");
            checkEq(1, eventCount(oracle, taskCell, SemanticRuntimeModel.Phase.START),
                "the oracle ran the recorded task cell exactly once");
            checkEq(1, eventCount(oracle, taskCell, SemanticRuntimeModel.Phase.SUCCESS),
                "the oracle's recorded task cell admitted the completion value");
            runCrossAsyncLua(fixture, project, result.tables(), result.registries());
            runCrossAsyncJvm(fixture, project, result.tables(), result.registries());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void runCrossAsyncLua(Fixture fixture, ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-cross-async-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            if (entry == null) {
                fail("the awaited cross-module drive records the async probe entry");
                return;
            }
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  print("ERR:" .. tostring(err)) os.exit(0)
                end
                local v = __asyncEntries["%s#probe"]("-", true)
                print("OK VALUE:" .. tostring(v))
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
            checkEq(0, exit, "the awaited cross-module LuaJIT artifact executes: "
                + stdout + stderr);
            check(stdout.contains("OK VALUE:42"), "the LuaJIT dynamic await runs the "
                + "cross-module body under its own module context: "
                + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void runCrossAsyncJvm(Fixture fixture, ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-cross-async-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            if (entry == null) {
                fail("the awaited cross-module drive records the JVM async probe entry");
                return;
            }
            Files.writeString(workspace.resolve("CrossAsyncProbe.java"), """
                final class CrossAsyncProbe {
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
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                "CrossAsyncProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the awaited cross-module JVM artifact "
                + "compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "CrossAsyncProbe"),
                workspace);
            checkEq(0, run.exitCode(), "the awaited cross-module JVM artifact executes: "
                + run.output());
            check(run.stdout().contains("OK VALUE:42"), "the JVM dynamic await runs "
                + "the cross-module body under its own module context: "
                + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 4. The asynchronous host class
    // =========================================================================

    private static void testHostAsyncClass() throws Exception {
        System.out.println("-- the asynchronous host class: a loaded host async export "
            + "into a function-typed parameter starts the operation handle on the "
            + "oracle and both production artifacts --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/dyn_async.d.deal", HOST_DECLARATION);
        sources.put("src/app.deal", HOST_APP_SOURCE);
        Fixture fixture = compileProject(sources,
            Map.of("host/dyn_async", "src/dyn_async.d.deal"));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the host async drive lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp start = dynamicAsyncStart(app);
            if (start == null) {
                fail("the host async drive produces the dynamic async shape");
                return;
            }
            check(((KindPayload.AsyncStartPayload) start.payload()).source()
                    == AsyncStartSource.DEAL_BODY,
                "the dynamic async start records the DEAL_BODY source placeholder "
                    + "(the class is runtime-resolved)");
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            String jvm = JvmSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(),
                JvmBackend.classNameFor(project.entryModule().path()),
                fixture.surface()).source();
            check(lua.contains("__surfaceNameOf(__dynC)")
                    && lua.contains("__asyncStartHost(") && lua.contains("__dynLbl"),
                "the LuaJIT async arm realizes the host operation handle class "
                    + "through the carrier's declared identity");
            check(jvm.contains("JvmRuntime.surfaceNameOf(")
                    && jvm.contains("JvmRuntime.startHostTask(")
                    && jvm.contains("JvmRuntime.effect(\"ASYNC_START_OP\""),
                "the JVM async arm realizes the host operation handle class through "
                    + "the carrier's declared identity");

            // The oracle: the loaded entry is the read's own class carrier, so the
            // dynamic HOST resolution runs the declared async export through the
            // seam and the single AWAIT completes it.
            List<String> started = new ArrayList<>();
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public SemanticOracle.Value loadedExport(ModuleId module, String export,
                        RuntimeDescriptor descriptor) {
                    return new SemanticOracle.Value.HostEntryValue(
                        (RuntimeDescriptor.Func) descriptor);
                }

                @Override
                public String startAsync(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor,
                        List<SemanticOracle.Value> args, String operationLabel) {
                    started.add(module.path() + "." + export + "@" + operationLabel);
                    return operationLabel;
                }

                @Override
                public SyncOutcome completeAsync(String operationLabel) {
                    return new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(42L));
                }
            };
            SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.invokeAsyncEntry(
                project, result.tables(), responder, APP, "probe", List.of());
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success success
                    && "int:42".equals(success.resultAtom()),
                "the oracle's dynamic host async start completes with the declared "
                    + "value: " + oracle.comparisonReport());
            checkEq(List.of("host.dyn_async.fetchCount@host.dyn_async.fetchCount"),
                started, "the oracle resolves the loaded host entry's declared "
                    + "identity for the operation label");
            check(!touchedModule(oracle, HOST),
                "the oracle records no host-module op (the async start is an effect)");

            // The production artifacts with the deployed host implementation.
            runHostAsyncLua(fixture, project, result.tables(), result.registries());
            runHostAsyncJvm(fixture, project, result.tables(), result.registries());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void runHostAsyncLua(Fixture fixture, ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-host-async-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve("host/dyn_async.lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, HOST_LUA, StandardCharsets.UTF_8);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            check(entry != null, "the host async drive records the async probe entry");
            if (entry == null) {
                return;
            }
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  print("ERR:" .. tostring(err)) os.exit(0)
                end
                local v = __asyncEntries["%s#probe"]("-", true)
                print("OK VALUE:" .. tostring(v))
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
            checkEq(0, exit, "the host async LuaJIT artifact executes under luajit: "
                + stdout + stderr);
            check(stdout.contains("OK VALUE:42"), "the LuaJIT dynamic host async start "
                + "completes through the operation handle: "
                + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void runHostAsyncJvm(Fixture fixture, ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-host-async-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            String hostClass = JvmBackend.classNameFor("host/dyn_async");
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(hostClass + ".java"),
                hostJava(hostClass), StandardCharsets.UTF_8);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            check(entry != null, "the host async drive records the JVM async probe "
                + "entry");
            if (entry == null) {
                return;
            }
            Files.writeString(workspace.resolve("HostAsyncProbe.java"), """
                final class HostAsyncProbe {
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
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                hostClass + ".java", "HostAsyncProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the host async production artifact compiles "
                + "with the deployed host implementation: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "HostAsyncProbe"),
                workspace);
            checkEq(0, run.exitCode(), "the host async production artifact executes "
                + "under java: " + run.output());
            check(run.stdout().contains("OK VALUE:42"), "the JVM dynamic host async "
                + "start completes through the operation handle: "
                + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 5. The fail-closed residue
    // =========================================================================

    private static void testAsyncResidue() throws Exception {
        System.out.println("-- the async fail-closed residue: an untagged carrier at a "
            + "dynamic async site projects the pinned E8001 at the start origin in the "
            + "oracle and both artifacts --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", CROSS_ASYNC_LIB_SOURCE);
        sources.put("src/app.deal", CROSS_ASYNC_APP_SOURCE);
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the residue drive lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp start = dynamicAsyncStart(app);
            if (start == null) {
                fail("the residue drive produces the dynamic async shape");
                return;
            }
            ValueId callee = ((KindPayload.CallCallee.Dynamic)
                ((KindPayload.AsyncStartPayload) start.payload()).callee()).callee();
            String origin = start.origin().sourceId() + ":"
                + start.origin().span().startLine() + ":"
                + start.origin().span().startColumn();
            // The carrier's producing op is replaced by a CONST of a string
            // result under the same op identity and the identity's registration
            // is dropped: the produced unit carries the identical shape and the
            // runtime value the dispatch reads is not a function carrier.
            List<SemanticOp> ops = new ArrayList<>();
            for (SemanticOp op : app.ops()) {
                if (op.result() instanceof ValueId value && value.equals(callee)) {
                    KindPayload payload = new KindPayload.ConstPayload(
                        new deal.semantic.ir.ScalarValue.String("carrier"));
                    ops.add(new SemanticOp(op.opId(), SemanticOpKind.CONST, op.origin(),
                        op.result(), RuntimeDescriptor.String.INSTANCE, List.of(),
                        List.of(), payload, deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE,
                        contractOf(SemanticOpKind.CONST, payload)));
                } else {
                    ops.add(op);
                }
            }
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
                new LinkedHashMap<>(app.functionBindings());
            bindings.remove(new FunctionAllocationIdentity(callee.id()));
            LoweredModuleUnit doctored = new LoweredModuleUnit(app.formatVersion(),
                app.semanticProfile(), app.moduleId(), app.interfaceHash(),
                app.loweringContextHash(), app.requiredCapabilities(),
                app.constructCoverage(), app.classLayouts(), app.functions(),
                app.moduleInit(), app.exportPlan(), bindings, ops);
            Map<ModuleId, LoweredModuleUnit> doctoredModules =
                new LinkedHashMap<>(project.modules());
            doctoredModules.put(APP, doctored);
            ExecutableLoweredProject doctoredProject = new ExecutableLoweredProject(
                SemanticProfile.DEAL_V1_2_INT32, project.interfaceIndex(),
                doctoredModules, project.entryModule());
            java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
                deal.semantic.ir.SemanticIrValidator.validate(doctoredProject,
                    new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                        doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                        productionInvocation().capabilityRegistryHash()));
            check(gate.isEmpty(), "the closed gate accepts the async residue drive: "
                + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
            if (gate.isPresent()) {
                return;
            }
            Map<ModuleId, StructuredBodyTable> tables = new LinkedHashMap<>();
            tables.put(APP, result.tables().get(APP));
            tables.put(LIB, result.tables().get(LIB));
            String oracleFailure = null;
            try {
                SemanticOracle.invokeAsyncEntry(doctoredProject, tables, null, APP,
                    "probe", List.of());
            } catch (RuntimeException rejected) {
                oracleFailure = rejected.getClass().getSimpleName() + ": "
                    + rejected.getMessage();
            }
            check(oracleFailure != null
                    && oracleFailure.contains("FunctionExecutionBinding"),
                "the oracle fails closed on the untagged async carrier: "
                    + oracleFailure);
            runAsyncResidueLua(fixture, doctoredProject, tables, result.registries(),
                origin);
            runAsyncResidueJvm(fixture, doctoredProject, tables, result.registries(),
                origin);
            check(LuaSemanticEmitter.emitProductionProject(doctoredProject, tables,
                    result.registries(), fixture.surface())
                    .contains("if __dynHN == nil then"),
                "the emitted LuaJIT async arm keeps its fail-closed residue");
            check(JvmSemanticEmitter.emitProductionProject(doctoredProject, tables,
                    result.registries(),
                    JvmBackend.classNameFor(APP.path()), fixture.surface()).source()
                    .contains("JvmRuntime.surfaceNameOf(") ,
                "the emitted JVM async arm keeps its identity gate");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void runAsyncResidueLua(Fixture fixture,
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, String origin)
            throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-async-residue-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  print("ERR:" .. tostring(err)) os.exit(0)
                end
                local okE, errE = pcall(__asyncEntries["%s#probe"], "-", true)
                if okE then
                  print("NO-FAILURE") os.exit(0)
                end
                if type(errE) == "table" and errE.__d then
                  print("ERR:" .. errE.code .. "|" .. tostring(errE.m) .. "|"
                    .. tostring(errE.o))
                else
                  print("ERR:" .. tostring(errE))
                end
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
            checkEq(0, exit, "the async residue LuaJIT artifact executes: " + stdout
                + stderr);
            check(stdout.contains("ERR:E8001|expected function, got string|" + origin),
                "the LuaJIT async residue projects the pinned E8001 at the start "
                    + "origin: " + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void runAsyncResidueJvm(Fixture fixture,
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, String origin)
            throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-async-residue-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            if (entry == null) {
                fail("the async residue drive records the JVM async probe entry");
                return;
            }
            Files.writeString(workspace.resolve("AsyncResidueProbe.java"), """
                final class AsyncResidueProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg);
                      return;
                    }
                    try {
                      %s.ae%s("-", true, new java.lang.Object[]{ });
                      System.out.println("NO-FAILURE");
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin);
                    }
                  }
                }
                """.formatted(className, className, entry.id()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                "AsyncResidueProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the async residue artifact compiles: "
                + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "AsyncResidueProbe"),
                workspace);
            checkEq(0, run.exitCode(), "the async residue artifact executes under java: "
                + run.output());
            check(run.stdout().contains("ERR:E8001|expected function, got string|"
                    + origin),
                "the JVM async residue projects the pinned E8001 at the start origin: "
                    + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The closed contract snapshot of one hand-built op (the validator digest). */
    private static deal.semantic.ir.OperationContractSnapshot contractOf(
            SemanticOpKind kind, KindPayload payload) {
        deal.semantic.ir.OperationContractSnapshot draft =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, kind,
                RuntimeDescriptor.String.INSTANCE, List.of(), null, payload,
                deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder");
        String digest = deal.semantic.ir.ContractSnapshotCanonicalizer.digest(draft);
        return new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, kind,
            RuntimeDescriptor.String.INSTANCE, List.of(), null, payload,
            deal.semantic.ir.FailurePolicyId.NO_DEAL_FAILURE, List.of(), digest);
    }

    // =========================================================================
    // Entry point
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Dynamic Class Dispatch Tests (ISSUE-0678) ===");
        testStdlibCallableClass();
        testStdlibCalleeIndirectArm();
        testStdlibCallableFailure();
        testCrossModuleBody();
        testCrossModuleAsyncBody();
        testHostAsyncClass();
        testAsyncResidue();
        if (failed > 0) {
            System.out.println("\nDynamic class dispatch: " + passed + " passed, "
                + failed + " failed");
            System.exit(1);
        }
        System.out.println("\nDynamic class dispatch: " + passed + " passed, 0 failed");
    }
}
