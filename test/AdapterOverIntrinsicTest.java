package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0680: the adapter-over-intrinsic D15 path — the adapter whose recorded
 * source is the seeded intrinsic identity runs the landed D15 protocol in the
 * lowering, both emitters, and the oracle (design source
 * {@code conversion-intrinsic-function-values} J5 and the first-class
 * conversion intrinsic contract; {@code function-typed-value-materialization-
 * and-dispatch} M5's conversion-intrinsic HOST sub-class).
 *
 * <ol>
 *   <li><b>Lowering.</b> The adapted call whose recorded source is the
 *       intrinsic identity records the adapter's xN target-signature
 *       {@code FUNCTION_PARAMETER} cells and the single {@code HOST_TO_DEAL} +
 *       {@code HOST_SYNC_RETURN} return cell (the source class is HOST), and
 *       the adapter creation shape is unchanged: the recorded source stays the
 *       seeded identity with no load and no proof.</li>
 *   <li><b>Execution.</b> The statically resolved and the runtime-resolved
 *       adapter run the landed D15 order in both emitters and the oracle:
 *       the source resolution, the carried canonical spec checked against the
 *       recorded source signature (E8010 at the call origin on a mismatch),
 *       the leading-M projection, the conversion ladder with the invoking
 *       call's context, and the recorded host return cell.</li>
 *   <li><b>Gate.</b> A unit carrying both a value-position intrinsic use and
 *       the adapted declaration over the same seeded identity passes
 *       {@code ADAPTER_SOURCE_SHAPE} and {@code REGISTRY_ONE_TO_ONE}.</li>
 * </ol>
 */
public class AdapterOverIntrinsicTest {

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
    // Fixtures
    // =========================================================================

    /** The corpus fixture's program (intrinsic-arity-extension), verbatim body. */
    private static final String ARITY_SOURCE = """
        export function main(): null {
          let f: (x: number, y: number) => int = int;
          let result: int = f(9.0, 1.0);
          if (result !== 9) {
            throw { code: "TEST_FAIL", message: "intrinsic arity-extension call failed" };
          }
          return null;
        }
        """;

    /**
     * The runtime-resolved drive (ISSUE-0680 criterion 3): the adapted
     * declaration is passed to a function-typed parameter, so the invocation
     * inside {@code apply} is a dynamic callee whose runtime carrier is the
     * adapter over the intrinsic.
     */
    private static final String DYNAMIC_ADAPTER_SOURCE = """
        function apply(f: (x: number, y: number) => int, v: number): int {
          return f(v, 1.0);
        }

        export function main(): null {
          let f: (x: number, y: number) => int = int;
          let result: int = apply(f, 9.0);
          if (result !== 9) {
            throw { code: "TEST_FAIL", message: "dynamic adapter over intrinsic" };
          }
          return null;
        }
        """;

    /**
     * The combined value-position + adapted-declaration drive (ISSUE-0680
     * criterion 4): one unit whose seeded identity carries the
     * identity-preserving load of the value-position declaration and the
     * adapted declaration's producer-less VALUE operand.
     */
    private static final String COMBINED_SOURCE = """
        export function main(): null {
          let f: (x: number, y: number) => int = int;
          let direct: (x: number) => int = int;
          let a: int = f(9.0, 1.0);
          let b: int = direct(3.0);
          if (a !== 9 || b !== 3) {
            throw { code: "TEST_FAIL", message: "combined value and adapter uses" };
          }
          return null;
        }
        """;

    private static final String ENTRY_SHIM = """
        export function main(): null {
          return null;
        }
        """;

    private record Fixture(Path root, CheckedProjectInput checkedProject,
                           ProjectInterfaceIndex index,
                           List<deal.semantic.SemanticRequirementManifest> manifests,
                           HostDeclarationSurface surface,
                           Map<ModuleId, CanonicalModuleIdentity> identities) {
    }

    private record RawLowering(LoweredModuleUnit unit, ExecutableLoweredProject project,
                               Map<ModuleId, deal.semantic.ir.StructuredBodyTable> tables,
                               Map<ModuleId, ClassFactoryRegistry> registries) {
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        Path root = Files.createTempDirectory("adapter-over-intrinsic");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Path target = root.resolve(source.getKey());
            Files.createDirectories(target.getParent());
            Files.writeString(target, source.getValue(), StandardCharsets.UTF_8);
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()), null, null, productionInvocation());
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

    private static RawLowering lower(Fixture fixture, String what) {
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), fixture.checkedProject(), fixture.index(),
            fixture.manifests(), fixture.surface(), fixture.identities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null, what + " lowers through the one project entry: "
            + result.diagnostics());
        if (result.project() == null) {
            return null;
        }
        return new RawLowering(result.project().modules().get(APP), result.project(),
            result.tables(), result.registries());
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

    private static SemanticOp adaptedCall(LoweredModuleUnit unit,
            FunctionExecutionBinding.AdapterBinding adapter) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Static staticCallee
                    && staticCallee.binding() == adapter) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp adaptOp(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                return op;
            }
        }
        return null;
    }

    private static long seedIdentity(LoweredModuleUnit unit, IntrinsicKind kind) {
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic && intrinsic.kind() == kind) {
                return entry.getKey().id();
            }
        }
        return -1;
    }

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

    private static String originText(SemanticOp op) {
        return op.origin().sourceId() + ":" + op.origin().span().startLine() + ":"
            + op.origin().span().startColumn();
    }

    private static SemanticIrValidator.ComparisonFacts facts(LoweredModuleUnit unit) {
        return new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
            SemanticProfile.DEAL_V1_2_INT32,
            ReleaseConfiguration.releaseCapabilityRegistry().capabilityRegistryHash());
    }

    // =========================================================================
    // 1. The lowering: the recorded cells and the unchanged creation shape
    // =========================================================================

    private static void testLoweringShape() throws Exception {
        System.out.println("-- the adapted call's recorded cells and the unchanged "
            + "adapter creation shape --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARITY_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the arity-extension fixture");
            if (raw == null) {
                return;
            }
            LoweredModuleUnit unit = raw.unit();
            long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
            check(seed > 0, "the unit carries the int conversion's seeded identity");
            if (seed < 0) {
                return;
            }

            // The creation shape is unchanged: the recorded source is the
            // seeded identity, no load is emitted, no proof is recorded.
            SemanticOp adapt = adaptOp(unit);
            check(adapt != null, "the adapted declaration produces its FUNCTION_ADAPT");
            if (adapt == null) {
                return;
            }
            KindPayload.FunctionAdaptPayload adaptPayload =
                (KindPayload.FunctionAdaptPayload) adapt.payload();
            check(adaptPayload.source()
                    instanceof deal.semantic.ir.AdaptSourceRef.Value value
                    && value.value().id() == seed,
                "the adapter's recorded source is the seeded intrinsic identity");
            checkEq(deal.semantic.ir.CaptureMode.VALUE, adaptPayload.mode(),
                "the intrinsic source keeps the VALUE capture mode");
            int loads = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BINDING_LOAD
                        && op.result() instanceof deal.semantic.ir.ValueId valueId
                        && valueId.id() == seed) {
                    loads++;
                }
            }
            checkEq(0, loads, "the intrinsic operand emits no function-typed load of "
                + "the intrinsic binding");
            check(adaptPayload.proof() == null, "the intrinsic operand records no proof");

            // The adapted call: xN target-signature FUNCTION_PARAMETER cells
            // plus the single HOST_TO_DEAL + HOST_SYNC_RETURN return cell.
            SemanticOp call = adaptedCall(unit,
                (FunctionExecutionBinding.AdapterBinding) firstAdapter(unit));
            check(call != null, "the adapted call resolves the AdapterBinding");
            if (call == null) {
                return;
            }
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            checkEq(CallMode.INDIRECT, payload.mode(),
                "the adapted call is the INDIRECT call mode");
            checkEq(2, payload.parameterBoundaryOpIds().size(),
                "the adapted call records the two target-signature parameter cells");
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opOf(unit, boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                checkEq(BoundaryKind.FUNCTION_PARAMETER, boundaryPayload.kind(),
                    "the target parameter cell is the FUNCTION_PARAMETER family");
            }
            SemanticOp returnCell = payload.returnBoundaryOpId() == null ? null
                : opOf(unit, payload.returnBoundaryOpId());
            check(returnCell != null, "the adapted call records its single return cell");
            if (returnCell != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnCell.payload();
                checkEq(BoundaryKind.HOST_TO_DEAL, boundaryPayload.kind(),
                    "the adapter host-source return cell is the HOST_TO_DEAL family");
                checkEq(FailurePolicyId.HOST_SYNC_RETURN, returnCell.failurePolicy(),
                    "the return cell carries the pinned HOST_SYNC_RETURN policy");
                checkEq(IntrinsicKind.INT_CONVERT.declaredSignature().returnType(),
                    boundaryPayload.descriptor(),
                    "the return cell checks the declared return descriptor");
            }

            // Both gates admit the unit as produced.
            check(SemanticIrValidator.validate(unit, facts(unit)).isEmpty(),
                "the unit carrying the adapted call passes the closed schema gate");
            check(deal.semantic.BindingsProductionValidator.validate(unit,
                    raw.tables().get(APP)).isEmpty(),
                "the unit carrying the adapted call passes the closed bindings gate");

            // Both artifacts carry the arm (never the removed fail-closed path).
            String lua = LuaSemanticEmitter.emitProject(raw.project(), raw.tables(),
                raw.registries());
            check(lua.contains("__dynS = __adaptSource("),
                "the LuaJIT artifact emits the adapter-over-intrinsic D15 sequence");
            check(lua.contains("__resT = __intConv("),
                "the LuaJIT artifact runs the conversion ladder at the adapted call");
            String jvm = JvmSemanticEmitter.emitProject(raw.project(), raw.tables(),
                raw.registries()).source();
            check(jvm.contains("JvmRuntime.fnCheck(JvmRuntime.adapterSource("),
                "the JVM artifact emits the adapter-over-intrinsic D15 sequence");
            check(jvm.contains("JvmRuntime.intConv("),
                "the JVM artifact runs the conversion ladder at the adapted call");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static FunctionExecutionBinding firstAdapter(LoweredModuleUnit unit) {
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.AdapterBinding) {
                return binding;
            }
        }
        return null;
    }

    // =========================================================================
    // 2. The fixture drive on all three consumers
    // =========================================================================

    private static void testFixtureDrive() throws Exception {
        System.out.println("-- the intrinsic-arity-extension fixture through the "
            + "production artifacts: the adapter converts the first argument, drops "
            + "the second, and the recorded return cell runs once --");
        Path fixtureFile = Path.of("test", "conformance", "backend-runtime",
            "functions", "intrinsic-arity-extension.deal");
        check(Files.exists(fixtureFile), "the corpus fixture is present");
        if (!Files.exists(fixtureFile)) {
            return;
        }
        String raw = Files.readString(fixtureFile, StandardCharsets.UTF_8);
        StringBuilder fixtureBody = new StringBuilder();
        for (String line : raw.lines().toList()) {
            if (line.startsWith("// @")) {
                continue;
            }
            fixtureBody.append(line).append('\n');
        }
        check(fixtureBody.toString().contains(ENTRY_SHIM),
            "the corpus fixture carries the lane's entry shim");
        String librarySource = fixtureBody.toString().replace(ENTRY_SHIM, "");
        String driver = """
            import * as lib from "./lib"

            export function main(): null {
              let r: int = lib.test_intrinsic_arity_extension()
              if (r !== 9) {
                throw { code: "TEST_FAIL", message: "adapter-over-intrinsic fixture" }
              }
              return null
            }
            """;
        Fixture fixture = compileProject(Map.of(
            "src/lib.deal", librarySource, "src/app.deal", driver));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
                productionInvocation(), fixture.checkedProject(), fixture.index(),
                fixture.manifests(), fixture.surface(), fixture.identities(), Map.of(),
                BuiltinErrorDeclaration.synthesized(
                    fixture.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
            check(result.project() != null, "the fixture lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit lib = result.project().modules().get(LIB);
            check(lib != null, "the fixture module is part of the closure");
            if (lib == null) {
                return;
            }
            FunctionExecutionBinding.AdapterBinding adapter =
                (FunctionExecutionBinding.AdapterBinding) firstAdapter(lib);
            check(adapter != null, "the fixture carries the adapter registration");
            if (adapter == null) {
                return;
            }
            SemanticOp call = adaptedCall(lib, adapter);
            if (call == null) {
                fail("the fixture's adapted call is missing");
                return;
            }
            OpId returnCell = ((KindPayload.CallPayload) call.payload())
                .returnBoundaryOpId();
            check(returnCell != null, "the fixture's adapted call records the return "
                + "cell");
            Path workspace = Files.createTempDirectory("adapter-over-intrinsic-drive");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "intrinsic arity extension", List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer fixture drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), "all three consumers produced a run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the adapted call started once");
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the adapted call published the converted "
                            + "value (the driver's result check passed)");
                    checkEq(1, eventCount(run, returnCell,
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell started once");
                    checkEq(1, eventCount(run, returnCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell admitted the "
                            + "converted value");
                    checkEq(0, eventCount(run, returnCell,
                            SemanticRuntimeModel.Phase.FAILURE),
                        run.consumer() + ": the recorded cell raised no failure");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The doctored source-signature mismatch
    // =========================================================================

    private static void testSourceSignatureMismatch() throws Exception {
        System.out.println("-- a doctored adapter source signature projects the pinned "
            + "E8010 at the call origin on all three consumers --");
        Fixture fixture = compileProject(Map.of("src/app.deal", ARITY_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the mismatch drive");
            if (raw == null) {
                return;
            }
            FunctionExecutionBinding.AdapterBinding adapter =
                (FunctionExecutionBinding.AdapterBinding) firstAdapter(raw.unit());
            SemanticOp call = adaptedCall(raw.unit(), adapter);
            if (call == null) {
                fail("the mismatch drive's adapted call is missing");
                return;
            }
            // Doctor the call's recorded source signature: the carrier carries
            // the intrinsic's declared signature, so the check projects the
            // pinned E8010 at the call origin.
            RuntimeDescriptor.Func mismatched =
                IntrinsicKind.NUMBER_CONVERT.declaredSignature();
            check(!mismatched.canonicalSpecText()
                    .equals(adapter.sourceSignature().canonicalSpecText()),
                "the doctored source signature differs from the recorded one");
            FunctionExecutionBinding.AdapterBinding doctored =
                new FunctionExecutionBinding.AdapterBinding(adapter.adaptOpId(),
                    adapter.captureMode(), adapter.sourceRef(), mismatched,
                    adapter.targetSignature());
            KindPayload.CallPayload callPayload = (KindPayload.CallPayload) call.payload();
            KindPayload.CallPayload doctoredPayload = new KindPayload.CallPayload(
                callPayload.mode(), new KindPayload.CallCallee.Static(doctored),
                callPayload.signature(), callPayload.parameterBoundaryOpIds(),
                callPayload.returnBoundaryOpId(), callPayload.dynamicReturnBoundary(),
                callPayload.bodyBlock(), callPayload.externalEntryRef());
            LoweredModuleUnit doctoredUnit = replaceCallPayload(raw.unit(),
                (KindPayload.CallCallee.Static) callPayload.callee(), callPayload,
                doctoredPayload);
            ExecutableLoweredProject doctoredProject = new ExecutableLoweredProject(
                raw.project().semanticProfile(), raw.project().interfaceIndex(),
                Map.of(APP, doctoredUnit), raw.project().entryModule());
            String origin = originText(call);
            Path workspace = Files.createTempDirectory("adapter-over-intrinsic-mismatch");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(doctoredProject, raw.tables(),
                        raw.registries(),
                        SemanticDifferentialHarness.Expectation.failure(
                            "adapter source mismatch", List.of(), "E8010", origin),
                        workspace);
                check(verdict.pass(), "the three-consumer E8010 drive passes: "
                    + verdict.report());
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && "E8010".equals(failure.error().code())
                            && failure.error().message()
                                .startsWith("function signature mismatch")
                            && mismatched.canonicalSpecText()
                                .equals(failure.error().expected())
                            && adapter.sourceSignature().canonicalSpecText()
                                .equals(failure.error().actual())
                            && origin.equals(failure.error().origin()),
                        run.consumer() + ": the pinned E8010 with the two signature "
                            + "texts at the call origin: " + run.terminal());
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.FAILURE),
                        run.consumer() + ": the CALL op publishes its FAILURE terminal");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static LoweredModuleUnit replaceCallPayload(LoweredModuleUnit unit,
            KindPayload.CallCallee.Static callee, KindPayload.CallPayload oldPayload,
            KindPayload.CallPayload newPayload) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() == oldPayload && op.payload() instanceof KindPayload.CallPayload
                    && ((KindPayload.CallPayload) op.payload()).callee() == callee) {
                ops.add(rebuild(op, newPayload, op.resultType()));
            } else {
                ops.add(op);
            }
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    /** One op copy with a replaced payload and a recomputed contract digest. */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload,
            deal.semantic.ir.OpResultType resultType) {
        OperationContractSnapshot contract = contractFor(op.kind(), payload, resultType,
            op.operandTypes(), op.failurePolicy(), "placeholder");
        contract = contractFor(op.kind(), payload, resultType, op.operandTypes(),
            op.failurePolicy(), ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(), resultType,
            op.operands(), op.operandTypes(), payload, op.failurePolicy(), contract);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, deal.semantic.ir.OpResultType resultType,
            List<RuntimeDescriptor> operandTypes, FailurePolicyId policy, String digest) {
        deal.semantic.ir.ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying ? carrying.selector()
                : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(), digest);
    }

    // =========================================================================
    // 3b. The ladder's failure at the adapter call origin
    // =========================================================================

    /** A non-integer argument at the adapted call (the ladder's pinned row). */
    private static final String FRACTION_SOURCE = """
        export function main(): null {
          let f: (x: number, y: number) => int = int;
          let r: int = f(2.5, 1.0);
          return null;
        }
        """;

    private static void testAdapterLadderFailure() throws Exception {
        System.out.println("-- the conversion ladder's failure at the adapted call "
            + "origin, with the invoking CALL op's kind in the FAILURE event --");
        Fixture fixture = compileProject(Map.of("src/app.deal", FRACTION_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the adapter ladder failure drive");
            if (raw == null) {
                return;
            }
            FunctionExecutionBinding.AdapterBinding adapter =
                (FunctionExecutionBinding.AdapterBinding) firstAdapter(raw.unit());
            SemanticOp call = adaptedCall(raw.unit(), adapter);
            if (call == null) {
                fail("the adapter ladder failure drive's call is missing");
                return;
            }
            String origin = originText(call);
            Path workspace = Files.createTempDirectory("adapter-over-intrinsic-ladder");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(raw.project(), raw.tables(),
                        raw.registries(),
                        SemanticDifferentialHarness.Expectation.failure(
                            "adapter ladder failure", List.of(), "E8001", origin),
                        workspace);
                check(verdict.pass(), "the three-consumer ladder failure drive passes: "
                    + verdict.report());
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && "E8001".equals(failure.error().code())
                            && "expected int, got non-integer number"
                                .equals(failure.error().message())
                            && origin.equals(failure.error().origin()),
                        run.consumer() + ": the pinned ladder text at the adapted call "
                            + "origin: " + run.terminal());
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.FAILURE),
                        run.consumer() + ": exactly one CALL FAILURE terminal "
                            + "(never a duplicated event)");
                    boolean callKind = false;
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.op().equals(call.opId())
                                && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                            callKind = event.kind() == SemanticOpKind.CALL;
                        }
                    }
                    check(callKind, run.consumer() + ": the failure event carries the "
                        + "invoking CALL op's own kind");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The runtime-resolved adapter
    // =========================================================================

    private static void testDynamicAdapterDrive() throws Exception {
        System.out.println("-- the runtime adapter branch over an intrinsic carrier: a "
            + "parameter-held adapter runs the same sequence --");
        Fixture fixture = compileProject(Map.of("src/app.deal", DYNAMIC_ADAPTER_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the dynamic adapter drive");
            if (raw == null) {
                return;
            }
            SemanticOp dynamic = null;
            for (SemanticOp op : raw.unit().ops()) {
                if (op.payload() instanceof KindPayload.CallPayload call
                        && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                    dynamic = op;
                }
            }
            check(dynamic != null, "the drive produces the dynamic callee shape");
            if (dynamic == null) {
                return;
            }
            OpId hostCell = ((KindPayload.CallPayload) dynamic.payload())
                .dynamicReturnBoundary().hostBoundaryOpId();
            String lua = LuaSemanticEmitter.emitProject(raw.project(), raw.tables(),
                raw.registries());
            check(lua.contains("if __dynS.__it ~= nil then"),
                "the LuaJIT runtime adapter branch resolves the intrinsic carrier");
            check(lua.contains("__resT = __intConv("),
                "the LuaJIT runtime adapter branch runs the conversion ladder");
            String jvm = JvmSemanticEmitter.emitProject(raw.project(), raw.tables(),
                raw.registries()).source();
            check(jvm.contains("instanceof JvmRuntime.Intrinsic"),
                "the JVM runtime adapter branch resolves the intrinsic carrier");
            check(jvm.contains("JvmRuntime.intConv("),
                "the JVM runtime adapter branch runs the conversion ladder");

            Path workspace = Files.createTempDirectory("adapter-over-intrinsic-dynamic");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(raw.project(), raw.tables(),
                        raw.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "dynamic adapter over intrinsic", List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer dynamic adapter drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), "all three consumers produced a run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, dynamic.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the dynamic call published the converted "
                            + "value");
                    checkEq(1, eventCount(run, hostCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell admitted the "
                            + "converted value");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 5. The combined gate drive (the T2 refinements stay load-bearing)
    // =========================================================================

    private static void testCombinedGateAdmission() throws Exception {
        System.out.println("-- the combined value-position + adapted-declaration unit "
            + "passes ADAPTER_SOURCE_SHAPE and REGISTRY_ONE_TO_ONE --");
        Fixture fixture = compileProject(Map.of("src/app.deal", COMBINED_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the combined gate drive");
            if (raw == null) {
                return;
            }
            LoweredModuleUnit unit = raw.unit();
            long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
            check(seed > 0, "the combined unit carries the int seed registration");
            int adapts = 0;
            boolean valueOperand = false;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                    adapts++;
                    KindPayload.FunctionAdaptPayload payload =
                        (KindPayload.FunctionAdaptPayload) op.payload();
                    if (payload.source() instanceof deal.semantic.ir.AdaptSourceRef.Value
                            value && value.value().id() == seed) {
                        valueOperand = true;
                    }
                }
            }
            checkEq(1, adapts, "the combined unit carries its single adapter (the "
                + "value-position declaration stores directly)");
            check(valueOperand, "the adapter's operand is the seeded intrinsic identity");
            Optional<CompilerDiagnostic> bindings =
                deal.semantic.BindingsProductionValidator.validate(unit,
                    raw.tables().get(APP));
            check(bindings.isEmpty(), "the combined unit passes the closed bindings gate "
                + "(REGISTRY_ONE_TO_ONE and ADAPTER_SOURCE_SHAPE): "
                + bindings.map(CompilerDiagnostic::message).orElse("admission"));
            Optional<CompilerDiagnostic> schema = SemanticIrValidator.validate(unit,
                facts(unit));
            check(schema.isEmpty(), "the combined unit passes the closed schema gate: "
                + schema.map(CompilerDiagnostic::message).orElse("admission"));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 6. The adapter-over-async site (`await` over an adapter over the intrinsic)
    // =========================================================================

    /**
     * The async adaptation drive (ISSUE-0680 criterion 1's adapter-over-async
     * clause): the checker admits no async use of the intrinsic (E3013/E3001 —
     * the design's J3), so the drive doctors the checked async adaptation's
     * lowered shape onto the seeded intrinsic identity — the FUNCTION_ADAPT's
     * VALUE operand, the outer adapter binding's source signature, and the
     * nested source ASYNC_START's callee — and runs the three consumers: the
     * nested source start is the closed DEAL_BODY task running the one
     * conversion ladder with the start's context and completing immediately,
     * and the single AWAIT runs the landed ASYNC_COMPLETION cell on the
     * converted value.
     */
    private static void testAdapterOverAsyncLoweringSite() throws Exception {
        System.out.println("-- the adapter-over-async site over the intrinsic: the nested "
            + "source start converts and the AWAIT completes --");
        String source = """
            async function one(x: int): int { return x; }

            export async function test(): int {
              let g: async (x: int) => int = one;
              let h: async (x: int, y: int) => int = g;
              let r: int = await h(9, 1);
              return r;
            }

            export function main(): null {
              return null;
            }
            """;
        Fixture fixture = compileProject(Map.of("src/app.deal", source));
        if (fixture == null) {
            return;
        }
        try {
            RawLowering raw = lower(fixture, "the adapter-over-async drive");
            if (raw == null) {
                return;
            }
            LoweredModuleUnit unit = raw.unit();
            long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
            check(seed > 0, "the async drive unit carries the int seed identity");
            if (seed < 0) {
                return;
            }
            SemanticOp adapt = adaptOp(unit);
            check(adapt != null, "the async drive carries the adapter creation");
            if (adapt == null) {
                return;
            }
            KindPayload.FunctionAdaptPayload adaptPayload =
                (KindPayload.FunctionAdaptPayload) adapt.payload();
            SemanticOp outer = null;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.ASYNC_START
                        && op.payload() instanceof KindPayload.AsyncStartPayload payload
                        && payload.callee() instanceof KindPayload.CallCallee.Static callee
                        && callee.binding() == firstAdapter(unit)) {
                    outer = op;
                }
            }
            check(outer != null, "the async drive carries the outer adapter start");
            if (outer == null) {
                return;
            }
            SemanticOp nested = null;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.ASYNC_START
                        && outer.opId().equals(op.origin().parentOpId())) {
                    nested = op;
                }
            }
            check(nested != null, "the outer adapter start carries its nested source "
                + "start");
            if (nested == null) {
                return;
            }
            FunctionExecutionBinding.AdapterBinding adapter =
                (FunctionExecutionBinding.AdapterBinding) firstAdapter(unit);
            RuntimeDescriptor.Func declared = IntrinsicKind.INT_CONVERT.declaredSignature();
            FunctionExecutionBinding.AdapterBinding doctored =
                new FunctionExecutionBinding.AdapterBinding(adapter.adaptOpId(),
                    deal.semantic.ir.CaptureMode.VALUE,
                    new deal.semantic.ir.AdaptSourceRef.Value(
                        new deal.semantic.ir.ValueId(seed)),
                    declared, adapter.targetSignature());
            KindPayload.FunctionAdaptPayload doctoredAdapt =
                new KindPayload.FunctionAdaptPayload(declared,
                    adaptPayload.targetSignature(), deal.semantic.ir.CaptureMode.VALUE,
                    new deal.semantic.ir.AdaptSourceRef.Value(
                        new deal.semantic.ir.ValueId(seed)), null);
            KindPayload.AsyncStartPayload outerPayload =
                (KindPayload.AsyncStartPayload) outer.payload();
            KindPayload.AsyncStartPayload doctoredOuter =
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(doctored), outerPayload.source(),
                    outerPayload.parameterBoundaryMode(),
                    outerPayload.parameterBoundaryOpIds(),
                    outerPayload.completionDescriptor(),
                    outerPayload.returnBoundaryOpId(), outerPayload.hostOperationLabel(),
                    outerPayload.externalAsyncLink());
            KindPayload.AsyncStartPayload nestedPayload =
                (KindPayload.AsyncStartPayload) nested.payload();
            checkEq(deal.semantic.ir.ParameterBoundaryMode.ELIDED_BY_ADAPTER,
                nestedPayload.parameterBoundaryMode(),
                "the nested source start elides its parameter boundaries");
            KindPayload.AsyncStartPayload doctoredNested =
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.IntrinsicFunction(
                            IntrinsicKind.INT_CONVERT, declared)),
                    deal.semantic.ir.AsyncStartSource.DEAL_BODY,
                    deal.semantic.ir.ParameterBoundaryMode.ELIDED_BY_ADAPTER, List.of(),
                    declared.returnType(), null, null, null);
            LoweredModuleUnit doctoredUnit = replaceOps(unit,
                Map.of(adapt, rebuildWith(adapt, doctoredAdapt, adapt.resultType(),
                        List.of(new deal.semantic.ir.ValueId(seed))),
                    outer, rebuildWith(outer, doctoredOuter, outer.resultType(),
                        outer.operands()),
                    nested, rebuildWith(nested, doctoredNested, nested.resultType(),
                        nested.operands())));
            ExecutableLoweredProject doctoredProject = new ExecutableLoweredProject(
                raw.project().semanticProfile(), raw.project().interfaceIndex(),
                Map.of(APP, doctoredUnit), raw.project().entryModule());
            String lua = LuaSemanticEmitter.emitProject(doctoredProject, raw.tables(),
                raw.registries());
            check(lua.contains("__intConv(S.__sa") || lua.contains("pcall(__intConv,"),
                "the LuaJIT nested source start runs the conversion inside its task");
            String jvm = JvmSemanticEmitter.emitProject(doctoredProject, raw.tables(),
                raw.registries()).source();
            check(jvm.contains("JvmRuntime.intConv("),
                "the JVM nested source start runs the conversion inside its task");
            Path workspace = Files.createTempDirectory("adapter-over-async-intrinsic");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runAsyncEntry(doctoredProject,
                        raw.tables(), "test", List.of(),
                        new SemanticDifferentialHarness.Expectation(List.of(),
                            new SemanticDifferentialHarness.TerminalExpectation
                                .SuccessWith("int:9"),
                            "adapter over async intrinsic"),
                        workspace, null);
                check(verdict.pass(), "the three-consumer adapter-over-async drive "
                    + "passes: " + verdict.report());
                checkEq(3, verdict.runs().size(), "all three async consumers produced "
                    + "a run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, nested.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the nested source start completed its task");
                    checkEq(1, eventCount(run, outer.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the outer adapter task completed");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** One op copy with a replaced payload, operands, and a recomputed digest. */
    private static SemanticOp rebuildWith(SemanticOp op, KindPayload payload,
            deal.semantic.ir.OpResultType resultType, List<deal.semantic.ir.ValueId> operands) {
        List<RuntimeDescriptor> operandTypes = op.operandTypes();
        if (operands.size() != op.operands().size()) {
            List<RuntimeDescriptor> resized = new ArrayList<>();
            for (int i = 0; i < operands.size(); i++) {
                resized.add(i < operandTypes.size() ? operandTypes.get(i)
                    : op.resultType() instanceof RuntimeDescriptor descriptor ? descriptor
                        : RuntimeDescriptor.Int.INSTANCE);
            }
            operandTypes = List.copyOf(resized);
        }
        OperationContractSnapshot contract = contractFor(op.kind(), payload, resultType,
            operandTypes, op.failurePolicy(), "placeholder");
        contract = contractFor(op.kind(), payload, resultType, operandTypes,
            op.failurePolicy(), ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(), resultType,
            operands, operandTypes, payload, op.failurePolicy(), contract);
    }

    /** One unit copy with the given op copies swapped in by identity. */
    private static LoweredModuleUnit replaceOps(LoweredModuleUnit unit,
            Map<SemanticOp, SemanticOp> replacements) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(replacements.getOrDefault(op, op));
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Adapter-over-Intrinsic D15 Path Tests (ISSUE-0680) ===\n");

        testLoweringShape();
        testFixtureDrive();
        testSourceSignatureMismatch();
        testAdapterLadderFailure();
        testDynamicAdapterDrive();
        testCombinedGateAdmission();
        testAdapterOverAsyncLoweringSite();

        System.out.println("\nAdapter-over-intrinsic: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
