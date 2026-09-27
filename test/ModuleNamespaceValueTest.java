package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.jvm.JvmBackend;
import deal.ffi.FfiGeneratedModule;
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
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.NamespaceRegistrations;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;
import deal.semantic.SemanticRuntimeModel;
import deal.test.conformance.CorpusFfi;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0627: module namespaces used as values (K15; the module-namespace
 * contract, K9 item 8's payload list, K11's member-read registration, K5's
 * dynamic call shape, K7's cataloged {@code std.time} callable, K2's export
 * surfaces, C1/C2's alias cells and per-module surfaces, and F1/F2's loaded
 * extern-C table).
 *
 * <ol>
 *   <li><b>The four Arm programs</b> (the value-position read, the
 *       table-alias escape, the table-parameter passthrough, and the
 *       cross-module escape/re-export chains) lower and execute through the
 *       one production pipeline on all three consumers — the semantic
 *       oracle, the production LuaJIT artifact under real {@code luajit},
 *       and the production JVM artifact under
 *       {@code javac --release 25 -proc:none} plus {@code java} — with the
 *       pinned E8004 {@code int out of safe range} terminal at the dynamic
 *       call's origin and no {@code STDLIB_TIME_CONFLICT} claim;</li>
 *   <li><b>namespace identity and surfaces</b>: two aliases of one module
 *       read the same value; every alias cell receives the module's
 *       published surface (a compiled module's publication table, a stdlib
 *       module's cataloged callables, a host module's loaded table, an
 *       extern-C module's loaded table);</li>
 *   <li><b>the member read's function row and the dynamic call's executed
 *       class and return cell</b>: exactly one
 *       {@code DynamicFunctionValue} per function-typed member read, the
 *       executed class path and recorded cell in every consumer's trace,
 *       and the read-site E8010/E8001 projections;</li>
 *   <li><b>the completion write</b>: the {@code MODULE_IMPORT} payload's
 *       ordered alias cells are the alias cells' single initializing write,
 *       the emitted artifacts write the module-keyed surface into them, and
 *       a cleared completion fails the namespace-registration gate
 *       closed.</li>
 * </ol>
 */
public class ModuleNamespaceValueTest {

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

    // =========================================================================
    // The Arm sources (the LoweringSupportTest fixtures)
    // =========================================================================

    /** Arm A: the value-position read of a cataloged export. */
    private static final String ARM_A_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let f: () => int = time.nowMillis
          f()
          return null
        }
        """;

    /** Arm B: the table-alias escape. */
    private static final String ARM_B_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let t = time
          let g: () => int = t.nowMillis
          g()
          return null
        }
        """;

    /** Arm B: the table-parameter passthrough. */
    private static final String ARM_PARAM_SOURCE = """
        import * as time from "std/time"

        export function pick(p: table): () => int {
          return p.nowMillis
        }

        export function main(): null {
          let g: () => int = pick(time)
          g()
          return null
        }
        """;

    /** Arm C: the cross-module escape's exporting module. */
    private static final String ARM_C_LIB_SOURCE = """
        import * as time from "std/time"

        export function getTime(): table {
          return time
        }
        """;

    /** Arm C: the cross-module table escape. */
    private static final String ARM_C_SOURCE = """
        import * as a from "./lib"

        export function main(): null {
          let t: table = a.getTime()
          let g: () => int = t.nowMillis
          g()
          return null
        }
        """;

    /** Arm C chain: the re-exporting intermediate module. */
    private static final String ARM_C_CHAIN_MID_SOURCE = """
        import * as a from "./a"

        export function getTime2(): table {
          return a.getTime()
        }
        """;

    /** Arm C chain: the table re-export chain's consumer. */
    private static final String ARM_C_CHAIN_SOURCE = """
        import * as b from "./b"

        export function main(): null {
          let t: table = b.getTime2()
          let g: () => int = t.nowMillis
          g()
          return null
        }
        """;

    /** The two-alias identity program. */
    private static final String TWO_ALIAS_SOURCE = """
        import * as t1 from "std/time"
        import * as t2 from "std/time"

        export function main(): null {
          if (t1 !== t2) {
            throw { code: "TEST_FAIL", message: "namespace identity" }
          }
          return null
        }
        """;

    /** The compiled-namespace library (two exports in declaration order). */
    private static final String COMPILED_LIB_SOURCE = """
        export function double(x: int): int {
          return x * 2
        }

        export function count(): int {
          return 7
        }
        """;

    /** The compiled-module namespace program. */
    private static final String COMPILED_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let m1 = lib
          let m2 = lib
          if (m1 !== m2) {
            throw { code: "TEST_FAIL", message: "namespace identity" }
          }
          let g: (x: int) => int = m1.double
          if (g(21) !== 42) {
            throw { code: "TEST_FAIL", message: "compiled namespace call" }
          }
          let c: () => int = m2.count
          if (c() !== 7) {
            throw { code: "TEST_FAIL", message: "compiled namespace count" }
          }
          return null
        }
        """;

    /** The read-site signature mismatch (a carried {@code ()->int} against {@code (int)->int}). */
    private static final String SIGNATURE_MISMATCH_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let t = time
          let g: (x: int) => int = t.nowMillis
          g(1)
          return null
        }
        """;

    /** The read-site non-function carrier (an int entry read as a function). */
    private static final String NONFUNCTION_SOURCE = """
        export function main(): null {
          let t: table = { count: 1 }
          let g: () => int = t.count
          g()
          return null
        }
        """;

    /** A non-exported member read at a function-typed position (missing). */
    private static final String MISSING_READ_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let t = time
          let g: () => int = t.notPresent
          g()
          return null
        }
        """;

    /** A non-exported member read at a nullable position (language null). */
    private static final String MISSING_NULLABLE_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let t = time
          let g: (() => int) | null = t.notPresent
          if (g !== null) {
            throw { code: "TEST_FAIL", message: "missing read" }
          }
          return null
        }
        """;

    /** The host declaration of the namespace-surface assertion. */
    private static final String HOST_DECLARATION_SOURCE = """
        export class Endpoint {
          path: string;
        }

        export function describe(s: Endpoint): string;
        """;

    /** The host-alias program of the namespace-surface assertion. */
    private static final String HOST_APP_SOURCE = """
        import * as cfg from "host/cfg"

        export function main(): null {
          let t = cfg
          return null
        }
        """;

    /** The extern-C corpus specifier of the namespace-surface assertion. */
    private static final String FFI_SPECIFIER = "candidate/native";

    /** The extern-C alias program of the namespace-surface assertion. */
    private static final String FFI_APP_SOURCE = """
        import * as native from "candidate/native"

        export function main(): null {
            let m = native
            return null
        }
        """;

    // =========================================================================
    // Fixture compile / lower
    // =========================================================================

    private record Fixture(Path root, Path sourceRoot,
                           CheckedProjectInput checkedProject,
                           ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           HostDeclarationSurface surface,
                           Map<ModuleId, CanonicalModuleIdentity> identities,
                           Map<ModuleId, FfiGeneratedModule> externCModules) {
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

    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        return compileProject(sources, Map.of());
    }

    private static Fixture compileProject(Map<String, String> sources,
                                          Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("module-namespace");
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
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            fail("the fixture project did not build: " + detail + " / "
                + orchestrator.diagnostics());
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declaration : orchestrator.hostDeclarationSurface().moduleIds()) {
            // The declaration identity is the raw externals specifier (the
            // extern-C generated plan/class identities are keyed by it), so
            // a slashed specifier never degrades to the dotted module path
            // (the FFI fixture wiring's own rule).
            String specifier = null;
            for (String raw : externals.keySet()) {
                if (raw.replace('/', '.').equals(declaration.path())
                        || raw.equals(declaration.path())) {
                    specifier = raw;
                    break;
                }
            }
            identities.put(declaration,
                new CanonicalModuleIdentity.ExternalModule(specifier == null
                    ? declaration.path() : specifier));
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        return new Fixture(root, src, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(), identities,
            externCModules);
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.identities(), fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    private static SemanticRequirementManifest manifestOf(Fixture fixture, String path) {
        for (SemanticRequirementManifest manifest : fixture.manifests()) {
            if (manifest.moduleId().path().equals(path)) {
                return manifest;
            }
        }
        return null;
    }

    // =========================================================================
    // Op helpers
    // =========================================================================

    private static SemanticOp moduleImportOf(LoweredModuleUnit unit, String modulePath) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT
                    && ((KindPayload.ModuleImportPayload) op.payload()).resolvedModule()
                        .path().equals(modulePath)) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp memberReadOf(LoweredModuleUnit unit, String key) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MEMBER_READ
                    && ((KindPayload.MemberReadPayload) op.payload()).key().equals(key)) {
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

    private static List<SemanticOp> dynamicCalls(LoweredModuleUnit unit) {
        List<SemanticOp> calls = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload call
                    && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                calls.add(op);
            }
        }
        return calls;
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    /** The exactly-one {@code DynamicFunctionValue} keyed by one producing op's result. */
    private static FunctionExecutionBinding registrationOf(LoweredModuleUnit unit,
                                                            SemanticOp producer) {
        if (!(producer.result() instanceof ValueId valueId)) {
            return null;
        }
        return unit.functionBindings().get(new FunctionAllocationIdentity(valueId.id()));
    }

    private static int registrationCount(LoweredModuleUnit unit,
            java.util.function.Predicate<FunctionExecutionBinding> predicate) {
        int count = 0;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (predicate.test(binding)) {
                count++;
            }
        }
        return count;
    }

    // =========================================================================
    // Trace masking and comparison
    // =========================================================================

    /**
     * The event lines of one run with the two target-specific detail classes
     * masked: the recorded stdlib terminal cell's raw clock atom (each
     * consumer reads its own clock; the oracle injects its deterministic
     * reading) and the target-internal reference-allocation ids
     * ({@code ref:<n>}, one counter per consumer). Every other event,
     * including the failing boundary's FAILURE snapshot and the terminal,
     * must match exactly.
     */
    private static List<String> maskedLines(SemanticRuntimeModel.ConsumerRun run,
                                            OpId clockCell) {
        List<String> lines = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            String text = event.text().replaceAll("ref:[0-9]+", "ref:<id>");
            if (clockCell != null && clockCell.equals(event.op())) {
                int last = text.lastIndexOf('|');
                String tail = text.substring(last + 1);
                if (tail.startsWith("num:") || tail.startsWith("int:")) {
                    text = text.substring(0, last) + "|atom:<clock>";
                }
            }
            lines.add(text);
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

    /** Asserts the three-consumer trace equality of one drive under the mask. */
    private static void checkTraceParity(String what,
            SemanticDifferentialHarness.Verdict verdict, OpId clockCell) {
        if (verdict.runs().size() != 3) {
            return;
        }
        List<String> base = maskedLines(verdict.runs().get(0), clockCell);
        for (int i = 1; i < verdict.runs().size(); i++) {
            List<String> other = maskedLines(verdict.runs().get(i), clockCell);
            check(base.equals(other), what + ": " + verdict.runs().get(i).consumer()
                + " trace equals the oracle trace event-for-event under the mask: "
                + firstDifference(base, other));
        }
    }

    /** One event of one consumer run, or null. */
    private static SemanticRuntimeModel.TraceEvent eventOf(
            SemanticRuntimeModel.ConsumerRun run, OpId op,
            SemanticRuntimeModel.Phase phase) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (op.equals(event.op()) && phase == event.phase()) {
                return event;
            }
        }
        return null;
    }

    // =========================================================================
    // 1. The Arm programs: shapes, claims, and the three-consumer drives
    // =========================================================================

    /**
     * Arm A: the value-position read registers the cataloged callable's HOST
     * class statically ({@code HostFunction}) and the invocation is the
     * landed static/indirect arm — no dynamic record is produced.
     */
    private static void testArmAValueRead() throws Exception {
        System.out.println("-- Arm A: the value-position read (static HOST class) --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_A_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "Arm A lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticRequirementManifest manifest = manifestOf(fixture, "app");
            check(manifest != null
                    && !manifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "Arm A claims no STDLIB_TIME_CONFLICT (the marker is inert)");
            SemanticOp read = null;
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.EXPORT_READ) {
                    read = op;
                }
            }
            check(read != null, "Arm A produces the export read");
            if (read != null) {
                check(registrationOf(app, read)
                        instanceof FunctionExecutionBinding.HostFunction host
                        && "std.time".equals(host.hostModuleId().path())
                        && "nowMillis".equals(host.exportName()),
                    "Arm A's read registers the cataloged callable's HOST class: "
                        + registrationOf(app, read));
            }
            check(registrationCount(app, b -> b
                    instanceof FunctionExecutionBinding.DynamicFunctionValue) == 0,
                "Arm A produces no DynamicFunctionValue (the read resolves its class "
                    + "statically)");
            check(dynamicCall(app) == null,
                "Arm A's invocation is the landed static/indirect arm");
            OpId armACell = null;
            for (SemanticOp op : app.ops()) {
                if (op.payload() instanceof KindPayload.CallPayload call
                        && call.callee()
                            instanceof KindPayload.CallCallee.Static staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction
                        && call.returnBoundaryOpId() != null) {
                    armACell = call.returnBoundaryOpId();
                }
            }
            check(armACell != null, "Arm A's static call records its return cell");

            Path workspace = Files.createTempDirectory("module-namespace-arm-a");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure("Arm A",
                            List.of(), "E8004", null), workspace);
                checkEq(3, verdict.runs().size(), "Arm A produced all three consumer "
                    + "runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && "E8004".equals(failure.error().code())
                            && "int out of safe range".equals(failure.error().message())
                            && failure.error().origin().endsWith("app.deal:5:3"),
                        "Arm A (" + run.consumer() + ") publishes the pinned E8004 int "
                            + "out of safe range at the call expression origin; got "
                            + run.terminal());
                }
                checkTraceParity("Arm A", verdict, armACell);
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * Arm B (the table-alias escape): the alias read is the landed
     * {@code BINDING_LOAD} of the alias cell the completion wrote; the member
     * read registers exactly one {@code DynamicFunctionValue}; the invocation
     * is the dynamic call whose recorded HOST cell carries the declared int;
     * the entry's cataloged callable runs and yields the pinned E8004 on all
     * three consumers.
     */
    private static void testArmBTableAlias() throws Exception {
        System.out.println("-- Arm B: the table-alias escape (one dynamic read, one "
            + "dynamic call) --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_B_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "Arm B lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticRequirementManifest manifest = manifestOf(fixture, "app");
            check(manifest != null
                    && !manifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "Arm B claims no STDLIB_TIME_CONFLICT (the retired trigger never "
                    + "fires)");

            SemanticOp importOp = moduleImportOf(app, "std.time");
            check(importOp != null
                    && ((KindPayload.ModuleImportPayload) importOp.payload()).kind()
                        == ModuleImportKind.STDLIB,
                "Arm B records the STDLIB MODULE_IMPORT of std.time");
            List<BindingId> cells = importOp == null ? List.of()
                : ((KindPayload.ModuleImportPayload) importOp.payload()).aliasCells();
            checkEq(1, cells.size(), "the std.time import names its one alias cell");
            for (BindingId cell : cells) {
                int allocs = 0;
                for (SemanticOp op : app.ops()) {
                    if (op.kind() == SemanticOpKind.BINDING_ALLOC
                            && ((KindPayload.BindingAllocPayload) op.payload())
                                .binding().equals(cell)) {
                        allocs++;
                    }
                }
                checkEq(1, allocs, "the alias cell " + cell + " has exactly one "
                    + "BINDING_ALLOC (the hoisted alias)");
                for (SemanticOp op : app.ops()) {
                    if (op.kind() == SemanticOpKind.BINDING_INIT
                            && ((KindPayload.BindingInitPayload) op.payload())
                                .binding().equals(cell)) {
                        fail("the alias cell " + cell + " carries a BINDING_INIT "
                            + "(the MODULE_IMPORT completion is its only write)");
                    }
                }
            }

            SemanticOp read = memberReadOf(app, "nowMillis");
            check(read != null, "Arm B produces the table-member read of nowMillis");
            FunctionExecutionBinding readBinding = read == null ? null
                : registrationOf(app, read);
            check(readBinding
                    instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic
                    && dynamic.materializingOpId().equals(read.opId()),
                "the member read registers exactly one DynamicFunctionValue "
                    + "correlated to its own op: " + readBinding);
            checkEq(1, registrationCount(app, b -> b
                    instanceof FunctionExecutionBinding.DynamicFunctionValue),
                "the unit carries exactly one DynamicFunctionValue");

            SemanticOp call = dynamicCall(app);
            check(call != null, "the invocation lowers the dynamic CALL shape");
            List<SemanticOp> calls = dynamicCalls(app);
            checkEq(1, calls.size(), "exactly one dynamic call is produced");
            if (call != null) {
                KindPayload.CallPayload payload =
                    (KindPayload.CallPayload) call.payload();
                check(payload.callee() instanceof KindPayload.CallCallee.Dynamic,
                    "the call's callee is the Dynamic form");
                KindPayload.DynamicReturnBoundary boundary =
                    payload.dynamicReturnBoundary();
                check(boundary != null && boundary.hostBoundaryOpId() != null
                        && boundary.dealBodyBoundaryOpId() != null
                        && boundary.externalBoundaryOpId() != null,
                    "the dynamic call records the three return cells");
                SemanticOp hostCell = opOf(app, boundary.hostBoundaryOpId());
                check(hostCell != null
                        && ((KindPayload.BoundaryPayload) hostCell.payload())
                            .descriptor()
                            .equals(deal.semantic.DescriptorService.describe(
                                deal.types.Type.Int.INSTANCE)),
                    "the recorded HOST cell carries the declared int terminal");

                Path workspace = Files.createTempDirectory("module-namespace-arm-b");
                try {
                    SemanticDifferentialHarness.Verdict verdict =
                        SemanticDifferentialHarness.runProject(result.project(),
                            result.tables(), result.registries(),
                            SemanticDifferentialHarness.Expectation.failure("Arm B",
                                List.of(), "E8004", null), workspace);
                    checkEq(3, verdict.runs().size(), "Arm B produced all three "
                        + "consumer runs");
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.DealFailure f
                                && "E8004".equals(f.error().code())
                                && "int out of safe range".equals(f.error().message())
                                && f.error().origin().endsWith("app.deal:6:3"),
                            "Arm B (" + run.consumer() + ") publishes the pinned E8004 "
                                + "int out of safe range at the g() call expression; got "
                                + run.terminal());
                        check(eventOf(run, boundary.hostBoundaryOpId(),
                                SemanticRuntimeModel.Phase.START) != null
                                && eventOf(run, boundary.hostBoundaryOpId(),
                                    SemanticRuntimeModel.Phase.FAILURE) != null,
                            "Arm B (" + run.consumer() + ") executes the recorded HOST "
                                + "terminal cell of the dynamic call");
                    }
                    checkTraceParity("Arm B", verdict, boundary.hostBoundaryOpId());
                } finally {
                    deleteRecursively(workspace);
                }
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * Arm B's table-parameter passthrough: the namespace value crosses the
     * {@code table} parameter boundary, the returned function value crosses
     * the {@code ()-&gt;int} return boundary, and the dynamic call yields the
     * pinned E8004.
     */
    private static void testArmParameterPassthrough() throws Exception {
        System.out.println("-- Arm B': the table-parameter passthrough --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_PARAM_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the passthrough fixture lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticRequirementManifest manifest = manifestOf(fixture, "app");
            check(manifest != null
                    && !manifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "the passthrough carries no STDLIB_TIME_CONFLICT claim");

            SemanticOp read = memberReadOf(app, "nowMillis");
            check(read != null
                    && registrationOf(app, read)
                        instanceof FunctionExecutionBinding.DynamicFunctionValue,
                "the parameter member read registers the dynamic materialization");
            SemanticOp call = dynamicCall(app);
            check(call != null, "the g() invocation lowers the dynamic CALL shape");
            if (call != null) {
                KindPayload.DynamicReturnBoundary boundary =
                    ((KindPayload.CallPayload) call.payload()).dynamicReturnBoundary();
                Path workspace = Files.createTempDirectory("module-namespace-arm-param");
                try {
                    SemanticDifferentialHarness.Verdict verdict =
                        SemanticDifferentialHarness.runProject(result.project(),
                            result.tables(), result.registries(),
                            SemanticDifferentialHarness.Expectation.failure(
                                "Arm B'", List.of(), "E8004", null), workspace);
                    checkEq(3, verdict.runs().size(), "the passthrough produced all "
                        + "three consumer runs");
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.DealFailure f
                                && "E8004".equals(f.error().code())
                                && "int out of safe range".equals(f.error().message())
                                && f.error().origin().endsWith("app.deal:9:3"),
                            "the passthrough (" + run.consumer() + ") publishes the "
                                + "pinned E8004 at the g() call expression; got "
                                + run.terminal());
                    }
                    checkTraceParity("Arm B'", verdict, boundary.hostBoundaryOpId());
                } finally {
                    deleteRecursively(workspace);
                }
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * Arm C: the cross-module table escape and the re-export chain. The
     * namespace value crosses the {@code table} return boundary of a compiled
     * module's export and the member read through it resolves the stdlib
     * entry dynamically.
     */
    private static void testArmCrossModuleEscape() throws Exception {
        System.out.println("-- Arm C: the cross-module escape and the re-export chain --");
        driveCrossModuleEscape("Arm C", Map.of(
            "src/lib.deal", ARM_C_LIB_SOURCE,
            "src/app.deal", ARM_C_SOURCE), 6);
        driveCrossModuleEscape("Arm C chain", Map.of(
            "src/a.deal", ARM_C_LIB_SOURCE,
            "src/b.deal", ARM_C_CHAIN_MID_SOURCE,
            "src/app.deal", ARM_C_CHAIN_SOURCE), 6);
    }

    private static void driveCrossModuleEscape(String what,
            Map<String, String> sources, int callLine) throws Exception {
        Fixture fixture = compileProject(sources);
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, what + " lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp call = dynamicCall(app);
            check(call != null, what + " lowers the dynamic CALL shape");
            if (call == null) {
                return;
            }
            KindPayload.DynamicReturnBoundary boundary =
                ((KindPayload.CallPayload) call.payload()).dynamicReturnBoundary();
            Path workspace = Files.createTempDirectory("module-namespace-arm-c");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure(what,
                            List.of(), "E8004", null), workspace);
                checkEq(3, verdict.runs().size(), what + " produced all three "
                    + "consumer runs");
                String site = "app.deal:" + callLine + ":3";
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure f
                            && "E8004".equals(f.error().code())
                            && "int out of safe range".equals(f.error().message())
                            && f.error().origin().endsWith(site),
                        what + " (" + run.consumer() + ") publishes the pinned E8004 at "
                            + site + "; got " + run.terminal());
                }
                checkTraceParity(what, verdict, boundary.hostBoundaryOpId());
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. Namespace identity and surfaces
    // =========================================================================

    /** Two aliases of one module read the identical namespace value. */
    private static void testTwoAliasIdentity() throws Exception {
        System.out.println("-- namespace identity: two aliases of one module read the "
            + "same value --");
        Fixture fixture = compileProject(Map.of("src/app.deal", TWO_ALIAS_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the two-alias fixture lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            Path workspace = Files.createTempDirectory("module-namespace-identity");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "two-alias identity", List.of(), "null"), workspace);
                checkEq(3, verdict.runs().size(), "the identity program produced all "
                    + "three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.Success,
                        "the identity program (" + run.consumer() + ") succeeds "
                            + "(both aliases observe one namespace value); got "
                            + run.terminal());
                }
                checkTraceParity("two-alias identity", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }

            // The emitted artifacts: both alias cells receive the one
            // module-keyed surface expression (never a per-alias copy).
            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            checkEq(2, countOccurrences(lua,
                    "= __exportSurfaces[\"std.time\"]\n"),
                "the Lua artifact writes the one std.time surface into both alias "
                    + "cells");
            String jvmNoSurfaces = null;
            try {
                jvmNoSurfaces = JvmSemanticEmitter.emitProductionProject(result.project(),
                    result.tables(), result.registries(),
                    JvmBackend.classNameFor(result.project().entryModule().path()),
                    fixture.surface()).source();
            } catch (RuntimeException ignored) {
                jvmNoSurfaces = null;
            }
            if (jvmNoSurfaces != null) {
                checkEq(2, countOccurrences(jvmNoSurfaces,
                        "= exportSurface(\"std.time\")"),
                    "the JVM artifact writes the one std.time surface into both alias "
                        + "cells");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The compiled module's namespace value: two aliases read one value, the
     * surface carries the module's published exports in declaration order,
     * and member reads through it dispatch the closures' DEAL-body class and
     * its recorded return cell.
     */
    private static void testCompiledNamespaceSurface() throws Exception {
        System.out.println("-- the compiled module's namespace value and its "
            + "declaration-order entries --");
        Fixture fixture = compileProject(Map.of(
            "src/lib.deal", COMPILED_LIB_SOURCE,
            "src/app.deal", COMPILED_APP_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the compiled-namespace fixture lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            LoweredModuleUnit lib = result.project().modules().get(new ModuleId("lib"));
            check(lib != null, "the closure carries the compiled lib module");
            SemanticOp importOp = moduleImportOf(app, "lib");
            check(importOp != null
                    && ((KindPayload.ModuleImportPayload) importOp.payload()).kind()
                        == ModuleImportKind.COMPILED,
                "the lib import is the COMPILED kind");
            List<SemanticOp> calls = dynamicCalls(app);
            checkEq(2, calls.size(), "both member reads dispatch dynamically");
            if (calls.size() == 2) {
                for (SemanticOp call : calls) {
                    KindPayload.DynamicReturnBoundary boundary =
                        ((KindPayload.CallPayload) call.payload()).dynamicReturnBoundary();
                    check(boundary != null && boundary.dealBodyBoundaryOpId() != null,
                        "the compiled namespace call records the DEAL-body cell");
                }
            }

            // The publication order: the surface entries equal the declared
            // exports in declaration order.
            StringBuilder names = new StringBuilder();
            for (SemanticOp op : lib.ops()) {
                if (op.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                    names.append(((KindPayload.ExportPublishPayload) op.payload()).name())
                        .append(',');
                }
            }
            checkEq("double,count,", names.toString(),
                "the compiled module publishes its exports in declaration order");

            Path workspace = Files.createTempDirectory("module-namespace-compiled");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "compiled namespace", List.of(), "null"), workspace);
                checkEq(3, verdict.runs().size(), "the compiled namespace produced all "
                    + "three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.Success,
                        "the compiled namespace (" + run.consumer() + ") succeeds; got "
                            + run.terminal());
                }
                checkTraceParity("compiled namespace", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }

            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            check(lua.contains("__exportSurfaces[\"lib\"][\"double\"]")
                    && lua.contains("__exportSurfaces[\"lib\"][\"count\"]"),
                "the Lua artifact publishes both compiled exports into the one lib "
                    + "surface");
            checkEq(2, countOccurrences(lua, "= __exportSurfaces[\"lib\"]"),
                "both lib alias cells receive the one lib surface");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The stdlib surface carries the module's cataloged callables. */
    private static void testStdlibSurfaceCallables() throws Exception {
        System.out.println("-- the stdlib surface carries the cataloged callables --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_B_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the stdlib fixture lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            check(lua.contains("__stdlibEntry(\"std.time\", \"nowMillis\", "
                    + "\"TIME_NOW_MILLIS\""),
                "the stdlib surface entry is the cataloged callable of the closed "
                    + "row (one accessor, the same carrier the direct read resolves)");
            check(lua.contains("__exportSurfaces[\"std.time\"] = "
                    + "__exportSurfaces[\"std.time\"] or {}"),
                "the stdlib surface is created idempotently before the module walks");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The host module's namespace value: the completion write stores the
     * loaded {@code load_host} table into the alias cell after the load.
     */
    private static void testHostNamespaceSurface() throws Exception {
        System.out.println("-- the host module's namespace value is the loaded "
            + "load_host table --");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/cfg.d.deal", HOST_DECLARATION_SOURCE);
        sources.put("src/app.deal", HOST_APP_SOURCE);
        Fixture fixture = compileProject(sources, Map.of("host/cfg", "src/cfg.d.deal"));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the host fixture", result)) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp importOp = moduleImportOf(app, "host.cfg");
            check(importOp != null
                    && ((KindPayload.ModuleImportPayload) importOp.payload()).kind()
                        == ModuleImportKind.HOST,
                "the host import is the HOST kind");
            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            int load = lineIndexOf(lua, line -> line.contains(
                "__rt.load_host(\"host/cfg\""));
            int completion = lineIndexOf(lua, line -> line.matches(
                ".*= __exportSurfaces\\[\"host\\.cfg\"]$"));
            check(load >= 0 && completion > load,
                "the host alias completion writes the loaded surface after the "
                    + "load_host call (load line " + load + ", completion line "
                    + completion + ")");
            String jvm = JvmSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(),
                JvmBackend.classNameFor(result.project().entryModule().path()),
                fixture.surface()).source();
            int jvmLoad = lineIndexOf(jvm, line -> line.contains("__hostLoad$")
                && line.contains("(\""));
            int jvmCompletion = lineIndexOf(jvm, line -> line.contains(
                ")[0] = exportSurface(\"host.cfg\");"));
            check(jvmLoad >= 0 && jvmCompletion > jvmLoad,
                "the JVM host alias completion writes the loaded surface after the "
                    + "load entry call (load line " + jvmLoad + ", completion line "
                    + jvmCompletion + ")");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The extern-C module's namespace value: the completion write stores the
     * loaded {@code load_ffi} table into the alias cell after the FFI load
     * (the FFI child's loaded module table).
     */
    private static void testExternCNamespaceSurface() throws Exception {
        System.out.println("-- the extern-C module's namespace value is the loaded "
            + "load_ffi table --");
        Path conformanceRoot = Path.of("test", "conformance");
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(conformanceRoot, FFI_SPECIFIER);
        if (wiring == null) {
            fail("the corpus wiring carries the FFI specifier " + FFI_SPECIFIER);
            return;
        }
        String declaration = ConformanceHarnessMetadata.stripClassificationHeaders(
            Files.readString(conformanceRoot.resolve(CorpusFfi.FFI_DIR)
                .resolve(wiring.declarationCorpusPath()), StandardCharsets.UTF_8));
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/native.d.deal", declaration);
        sources.put("src/app.deal", FFI_APP_SOURCE);
        Fixture fixture = compileProject(sources,
            Map.of(FFI_SPECIFIER, "src/native.d.deal"));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result =
                lowerExternCFixture(fixture);
            if (!checkLowers("the extern-C fixture", result)) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            ModuleId ffiModule = new ModuleId(FFI_SPECIFIER.replace('/', '.'));
            SemanticOp importOp = moduleImportOf(app, ffiModule.path());
            check(importOp != null
                    && ((KindPayload.ModuleImportPayload) importOp.payload()).kind()
                        == ModuleImportKind.HOST,
                "the extern-C import is the host-shaped HOST kind");
            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface(),
                new FfiEmissionInput(fixture.externCModules(),
                    fixture.sourceRoot().toString()));
            int load = lineIndexOf(lua, line -> line.contains("__rt.load_ffi("));
            int completion = lineIndexOf(lua, line -> line.endsWith(
                "= __exportSurfaces[\"" + ffiModule.path() + "\"]"));
            check(load >= 0 && completion > load,
                "the extern-C alias completion writes the loaded load_ffi table "
                    + "after the load (load line " + load + ", completion line "
                    + completion + ")");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** Lowers the extern-C fixture with the compile's own FFI metadata. */
    private static SemanticLowerer.ProjectLoweringResult lowerExternCFixture(
            Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.identities(), fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    private static boolean checkLowers(String what,
            SemanticLowerer.ProjectLoweringResult result) {
        check(result.project() != null, what + " lowers: " + result.diagnostics());
        return result.project() != null;
    }

    // =========================================================================
    // 3. The member read's function row and the read-site projections
    // =========================================================================

    /**
     * The function row at the member read: a carried {@code ()-&gt;int}
     * against the checked {@code (int)-&gt;int} is the pinned E8010 at the
     * read site on all three consumers.
     */
    private static void testReadSiteSignatureMismatch() throws Exception {
        System.out.println("-- the function row at the namespace member read: E8010 "
            + "at the read site --");
        Fixture fixture = compileProject(Map.of("src/app.deal",
            SIGNATURE_MISMATCH_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the signature-mismatch fixture", result)) {
                return;
            }
            Path workspace = Files.createTempDirectory("module-namespace-e8010");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure("E8010",
                            List.of(), "E8010", null), workspace);
                checkEq(3, verdict.runs().size(), "the mismatch produced all three "
                    + "consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure f
                            && "E8010".equals(f.error().code())
                            && f.error().message().contains("function signature mismatch")
                            && f.error().origin().endsWith("app.deal:5:10"),
                        "the mismatch (" + run.consumer() + ") publishes the pinned "
                            + "E8010 at the read site; got " + run.terminal());
                }
                checkTraceParity("E8010 read site", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The function row at the member read: a non-function carrier is the
     * pinned E8001 {@code expected function, got int} at the read site on all
     * three consumers.
     */
    private static void testReadSiteNonFunction() throws Exception {
        System.out.println("-- the function row at the member read: E8001 expected "
            + "function at the read site --");
        Fixture fixture = compileProject(Map.of("src/app.deal", NONFUNCTION_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the non-function fixture", result)) {
                return;
            }
            Path workspace = Files.createTempDirectory("module-namespace-e8001");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure("E8001",
                            List.of(), "E8001", null), workspace);
                checkEq(3, verdict.runs().size(), "the non-function read produced all "
                    + "three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure f
                            && "E8001".equals(f.error().code())
                            && "expected function, got int".equals(f.error().message())
                            && f.error().origin().endsWith("app.deal:3:10"),
                        "the non-function read (" + run.consumer() + ") publishes the "
                            + "pinned E8001 at the read site; got " + run.terminal());
                }
                checkTraceParity("E8001 read site", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * A non-exported member read at a function-typed position: the landed
     * contextual outcome is the pinned E8001 {@code expected function, got
     * missing} at the read site on all three consumers.
     */
    private static void testMissingMemberRead() throws Exception {
        System.out.println("-- the non-exported member read: E8001 expected function, "
            + "got missing at the read site --");
        Fixture fixture = compileProject(Map.of("src/app.deal", MISSING_READ_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the missing-read fixture", result)) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp read = memberReadOf(app, "notPresent");
            check(read != null
                    && registrationOf(app, read)
                        instanceof FunctionExecutionBinding.DynamicFunctionValue,
                "the missing entry's function-typed read registers the dynamic "
                    + "materialization");
            Path workspace = Files.createTempDirectory("module-namespace-missing");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure("missing read",
                            List.of(), "E8001", null), workspace);
                checkEq(3, verdict.runs().size(), "the missing read produced all three "
                    + "consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure f
                            && "E8001".equals(f.error().code())
                            && "expected function, got missing".equals(
                                f.error().message())
                            && f.error().origin().endsWith("app.deal:5:10"),
                        "the missing read (" + run.consumer() + ") publishes the "
                            + "pinned E8001 expected function, got missing at the read "
                            + "site; got " + run.terminal());
                }
                checkTraceParity("missing read", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * A non-exported member read at a nullable position: the landed
     * contextual outcome is the language null (the guarded read never
     * validates the absent entry as a function).
     */
    private static void testMissingMemberReadNullable() throws Exception {
        System.out.println("-- the non-exported member read at a nullable position: "
            + "language null --");
        Fixture fixture = compileProject(Map.of("src/app.deal",
            MISSING_NULLABLE_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the nullable-missing fixture", result)) {
                return;
            }
            Path workspace = Files.createTempDirectory("module-namespace-missing-null");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "nullable missing read", List.of(), "null"), workspace);
                checkEq(3, verdict.runs().size(), "the nullable missing read produced "
                    + "all three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.Success,
                        "the nullable missing read (" + run.consumer() + ") observes "
                            + "the language null; got " + run.terminal());
                }
                checkTraceParity("nullable missing read", verdict, null);
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The completion write's discipline and the fail-closed negative
    // =========================================================================

    /**
     * Every alias cell is named exactly once by its import's completion, the
     * completion payload is the recording surface, and the alias cells are
     * never written by a binding op.
     */
    private static void testCompletionDiscipline() throws Exception {
        System.out.println("-- the completion write is the alias cell's only "
            + "initializing write --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_B_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the discipline fixture", result)) {
                return;
            }
            List<LoweredModuleUnit> units = new ArrayList<>(
                result.project().modules().values());
            NamespaceRegistrations.Assembly assembly =
                NamespaceRegistrations.assemble(units);
            check(!assembly.hasErrors(),
                "the namespace registrations assemble without a defect: "
                    + assembly.diagnostics());
            if (assembly.registrations() != null) {
                checkEq(1, assembly.registrations().registrations().size(),
                    "the closure registers exactly one imported module");
                var registration = assembly.registrations()
                    .registrationFor(new ModuleId("std.time"));
                check(registration != null
                        && registration.kind() == ModuleImportKind.STDLIB
                        && registration.aliasCells().size() == 1,
                    "the std.time registration names its one alias cell: "
                        + registration);
            }
            for (LoweredModuleUnit unit : units) {
                Set<BindingId> aliases = new java.util.LinkedHashSet<>();
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                        aliases.addAll(((KindPayload.ModuleImportPayload) op.payload())
                            .aliasCells());
                    }
                }
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.BINDING_INIT
                            && aliases.contains(((KindPayload.BindingInitPayload)
                                op.payload()).binding())) {
                        fail("alias cell " + op.payload()
                            + " is written by a BINDING_INIT");
                    }
                    if (op.kind() == SemanticOpKind.BINDING_STORE
                            && aliases.contains(((KindPayload.BindingStorePayload)
                                op.payload()).binding())) {
                        fail("alias cell " + op.payload()
                            + " is written by a BINDING_STORE");
                    }
                }
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The fail-closed negative: an import-alias allocation named by no
     * completion fails the namespace-registration gate with exactly the
     * pinned rule (the completion is the alias's pinned initializing write).
     */
    private static void testClearedCompletionFailsClosed() throws Exception {
        System.out.println("-- the negative seed: a cleared completion fails the "
            + "namespace registration gate --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARM_B_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (!checkLowers("the negative-seed fixture", result)) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            List<SemanticOp> ops = new ArrayList<>();
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                    KindPayload.ModuleImportPayload payload =
                        (KindPayload.ModuleImportPayload) op.payload();
                    ops.add(rebuildOp(op, new KindPayload.ModuleImportPayload(
                        payload.rawSpecifier(), payload.resolvedModule(), payload.kind(),
                        List.of())));
                } else {
                    ops.add(op);
                }
            }
            LoweredModuleUnit cleared = corrupted(app, ops);
            NamespaceRegistrations.Assembly assembly =
                NamespaceRegistrations.assemble(List.of(cleared));
            check(assembly.hasErrors()
                    && assembly.diagnostics().size() == 1
                    && assembly.diagnostics().get(0).message().contains(
                        "named by no MODULE_IMPORT completion"),
                "the cleared completion fails the namespace-registration gate: "
                    + assembly.diagnostics());
            check(assembly.registrations() == null,
                "a failed assembly produces no registrations");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Doctoring helpers (the negative seed)
    // =========================================================================

    private static SemanticOp rebuildOp(SemanticOp op, KindPayload payload) {
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contractOf(op, payload));
    }

    private static OperationContractSnapshot contractOf(SemanticOp op,
            KindPayload payload) {
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(), "placeholder");
        String digest =
            deal.semantic.ir.ContractSnapshotCanonicalizer.digest(placeholder);
        return new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(), digest);
    }

    private static LoweredModuleUnit corrupted(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int index = text.indexOf(needle);
        while (index >= 0) {
            count++;
            index = text.indexOf(needle, index + needle.length());
        }
        return count;
    }

    /** The zero-based index of the first line matching the predicate, or -1. */
    private static int lineIndexOf(String text,
            java.util.function.Predicate<String> predicate) {
        String[] lines = text.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (predicate.test(lines[i].trim())) {
                return i;
            }
        }
        return -1;
    }

    private static void deleteRecursively(Path path) {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (var stream = Files.walk(path)) {
            stream.sorted(java.util.Comparator.reverseOrder()).forEach(entry -> {
                try {
                    Files.deleteIfExists(entry);
                } catch (java.io.IOException ignored) {
                    // Best-effort cleanup.
                }
            });
        } catch (java.io.IOException ignored) {
            // Best-effort cleanup.
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Module Namespace Value Tests (ISSUE-0627) ===");
        testArmAValueRead();
        testArmBTableAlias();
        testArmParameterPassthrough();
        testArmCrossModuleEscape();
        testTwoAliasIdentity();
        testCompiledNamespaceSurface();
        testStdlibSurfaceCallables();
        testHostNamespaceSurface();
        testExternCNamespaceSurface();
        testReadSiteSignatureMismatch();
        testReadSiteNonFunction();
        testMissingMemberRead();
        testMissingMemberReadNullable();
        testCompletionDiscipline();
        testClearedCompletionFailsClosed();
        System.out.println();
        if (failed > 0) {
            System.out.println("module namespace values: " + passed + " passed, "
                + failed + " failed");
            System.exit(1);
        }
        System.out.println("module namespace values: " + passed + " passed, 0 failed");
    }
}
