package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DynamicResolutionKind;
import deal.semantic.ir.DynamicReturnBoundaryProtocol;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReturnBoundarySelection;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRuntimeModel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0531 — dynamically resolved function invocations in
 * {@code deal.semantic-ir/1}: the closed {@code CallCallee.Dynamic}
 * callee shape, the dynamic return-boundary set of {@code CALL}
 * (DEAL body, host, retained-ABI external; {@code SHARED_BODY} records no
 * caller-side cell), the {@code ASYNC_START} dynamic projection (source
 * {@code DEAL_BODY} + the single {@code FUNCTION_RETURN} task cell), the
 * runtime selection protocol
 * ({@link DynamicReturnBoundaryProtocol}), and the
 * callback-delivered/host-response {@code HostFunctionValue}
 * registration closure (R-FUNCTION-BINDING) with the
 * {@code materializingBoundaryOpId} correlation carried on both
 * validator surfaces.
 *
 * <p>Corpus:</p>
 * <ol>
 *   <li>Closed construction: the {@code Dynamic} callee, the
 *       {@code DynamicReturnBoundary} record, the
 *       {@code CallPayload}/{@code AsyncStartPayload} exclusivity
 *       rejections, and the {@code ReturnBoundarySelection} closed
 *       kinds.</li>
 *   <li>The protocol: {@code kindOf} for every direct binding shape and
 *       the adapter fail-closed arm; {@code select} for all four
 *       resolution classes with the pinned cell/kind/owner.</li>
 *   <li>Validator positives: a unit-level dynamic CALL (all three
 *       recorded cells + a parameter boundary), a project-level dynamic
 *       CALL with the DEAL-body cell living in the callee unit, and a
 *       dynamic ASYNC_START — each through the typed and the text
 *       surface.</li>
 *   <li>Validator negatives: wrong mode, missing/extra record,
 *       exclusive single return id, per-class cell violations,
 *       unresolvable/non-BOUNDARY entries, the ASYNC_START source and
 *       missing-return violations, the closed per-class cell checks
 *       (kind/policy/descriptor, mutual distinctness, and the
 *       RETURN-parentage of the DEAL-body and ASYNC task cells), the
 *       malformed-record exclusivity, and the open callee type
 *       (R-ENUM).</li>
 *   <li>The HostFunctionValue crossing closure: the positive
 *       registration, and the negatives (missing registration, dangling
 *       correlation id, descriptor/key mismatches, null correlation id
 *       through the text surface).</li>
 *   <li>Canonical rendering and the text round-trip.</li>
 *   <li>Oracle execution of a dynamically resolved {@code ASYNC_START} for
 *       every runtime resolution class — DEAL_BODY (the task body's
 *       {@code RETURN} runs exactly the recorded {@code FUNCTION_RETURN}
 *       task cell), HOST (start/complete with the derived operation
 *       label; zero caller-side return cells), and EXTERNAL/SHARED_BODY
 *       (the callee async {@code EXTERNAL_ENTRY} owns the canonical
 *       token and the caller {@code AWAIT} completes through the
 *       execution-bound referent).</li>
 *   <li>Oracle execution of adapter-resolved dynamic {@code CALL} and
 *       {@code ASYNC_START} — the D15 source resolution fixes the class
 *       per source binding (LoweredBody, HostFunction, HostFunctionValue,
 *       retained-ABI external, SHARED_BODY external) and each class
 *       executes exactly the selected recorded cell with the pinned
 *       kind and owner.</li>
 * </ol>
 */
public class DynamicResolutionIrTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Shared synthetic fixtures
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.a");
    private static final ModuleId MOD_B = new ModuleId("mod.b");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(IFACE, SemanticProfile.DEAL_V1_2_INT32, REGISTRY);
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor STR = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor.Func SIG = new RuntimeDescriptor.Func(List.of(INT), INT);

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

    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            List.of(), selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, nextValue(),
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    private static SemanticOp boundaryWithInput(OpId id, BoundaryKind kind,
            RuntimeDescriptor descriptor, FailurePolicyId policy, OpId parent, ValueId input) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    private static LoweredModuleUnit unit(ModuleId module,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return unit(module, Map.of(), bindings, ops);
    }

    private static LoweredModuleUnit unit(ModuleId module,
            Map<FunctionId, LoweredFunction> functions,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, module, IFACE, LCH, Set.of(), Map.of(), Map.of(),
            functions, new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            bindings, ops);
    }

    private static LoweredModuleUnit unit(
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return unit(MOD, bindings, ops);
    }

    private static void assertPass(Optional<CompilerDiagnostic> diagnostic, String what) {
        check(diagnostic.isEmpty(), what + " passes validation"
            + (diagnostic.isPresent() ? ": " + diagnostic.get().message() : ""));
    }

    private static void assertE6005(Optional<CompilerDiagnostic> diagnostic, String rule,
            String... contains) {
        check(diagnostic.isPresent(), rule + " is rejected with E6005");
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()), rule + " diagnostic code is E6005");
        check(d.diagnosticCode() == DiagnosticCode.E6005, rule + " diagnosticCode is E6005");
        String message = d.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            rule + " is named as the validator rule (exactly one rule per fixture); got \""
                + message + "\"");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \""
                + message + "\"");
        }
    }

    private static void negative(String what, LoweredModuleUnit unit, String rule,
            String... contains) {
        assertE6005(SemanticIrValidator.validate(unit, FACTS), rule, contains);
    }

    private static void negativeText(String what, String text, String rule, String... contains) {
        assertE6005(SemanticIrValidator.validateText(text, FACTS), rule, contains);
    }

    private static boolean throwsIllegalArgument(Runnable action) {
        try {
            action.run();
            return false;
        } catch (RuntimeException e) {
            return true;
        }
    }

    // =========================================================================
    // 1. Closed construction
    // =========================================================================

    private static void testConstruction() {
        System.out.println("-- Closed construction: Dynamic callee, DynamicReturnBoundary, "
            + "payload exclusivity --");

        ValueId callee = new ValueId(7);
        KindPayload.CallCallee.Dynamic dynamic = new KindPayload.CallCallee.Dynamic(callee);
        check(dynamic.callee().equals(callee), "the Dynamic callee records its ValueId");
        check(throwsIllegalArgument(() -> new KindPayload.CallCallee.Dynamic(null)),
            "Dynamic rejects a null callee");

        OpId deal = nextOpId();
        OpId host = nextOpId();
        OpId external = nextOpId();
        KindPayload.DynamicReturnBoundary record =
            new KindPayload.DynamicReturnBoundary(deal, host, external);
        check(record.dealBodyBoundaryOpId().equals(deal)
                && record.hostBoundaryOpId().equals(host)
                && record.externalBoundaryOpId().equals(external),
            "the record carries the three pinned entries");
        check(throwsIllegalArgument(() -> new KindPayload.DynamicReturnBoundary(null, host,
                external)),
            "the record rejects a null DEAL-body entry");
        check(throwsIllegalArgument(() -> new KindPayload.DynamicReturnBoundary(deal, null,
                external)),
            "the record rejects a null host entry");
        check(throwsIllegalArgument(() -> new KindPayload.DynamicReturnBoundary(deal, host,
                null)),
            "the record rejects a null external entry");

        // CallPayload exclusivity (construction-checked).
        new KindPayload.CallPayload(CallMode.INDIRECT, dynamic, SIG, List.of(), null, record,
            null, null);
        check(true, "a Dynamic callee + INDIRECT + the record constructs");
        check(throwsIllegalArgument(() -> new KindPayload.CallPayload(CallMode.DIRECT, dynamic,
                SIG, List.of(), null, record, null, null)),
            "a Dynamic callee under DIRECT is rejected at construction");
        check(throwsIllegalArgument(() -> new KindPayload.CallPayload(CallMode.INDIRECT, dynamic,
                SIG, List.of(), null, null, null, null)),
            "a Dynamic callee without the record is rejected at construction");
        check(throwsIllegalArgument(() -> new KindPayload.CallPayload(CallMode.INDIRECT, dynamic,
                SIG, List.of(), deal, record, null, null)),
            "a Dynamic callee with the single return id set is rejected at construction");
        check(throwsIllegalArgument(() -> new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Indirect(callee), SIG, List.of(), null, record, null,
                null)),
            "a non-Dynamic callee with the record is rejected at construction");

        // AsyncStartPayload exclusivity.
        new KindPayload.AsyncStartPayload(dynamic, AsyncStartSource.DEAL_BODY,
            ParameterBoundaryMode.RUN, List.of(), INT, deal, null, null);
        check(true, "a Dynamic ASYNC_START with source DEAL_BODY constructs");
        check(throwsIllegalArgument(() -> new KindPayload.AsyncStartPayload(dynamic,
                AsyncStartSource.HOST, ParameterBoundaryMode.RUN, List.of(), INT, deal, null,
                null)),
            "a Dynamic ASYNC_START with source HOST is rejected at construction");

        // ReturnBoundarySelection closed kinds.
        new ReturnBoundarySelection.CalleeReturn(deal);
        new ReturnBoundarySelection.CallTerminal(host, BoundaryKind.HOST_TO_DEAL);
        new ReturnBoundarySelection.CallTerminal(external, BoundaryKind.EXTERNAL_RETURN);
        check(true, "the two call-terminal kinds construct");
        check(throwsIllegalArgument(() -> new ReturnBoundarySelection.CallTerminal(host,
                BoundaryKind.FUNCTION_RETURN)),
            "CallTerminal rejects a non-call-terminal kind");
        check(ReturnBoundarySelection.None.INSTANCE != null, "the None selection exists");
    }

    // =========================================================================
    // 2. Runtime selection protocol
    // =========================================================================

    private static void testProtocol() {
        System.out.println("-- Runtime selection protocol: kindOf + select --");

        check(DynamicReturnBoundaryProtocol.kindOf(new FunctionExecutionBinding.LoweredBody(
                new FunctionId(1), new BlockId(1))) == DynamicResolutionKind.DEAL_BODY,
            "a LoweredBody resolves DEAL_BODY");
        check(DynamicReturnBoundaryProtocol.kindOf(new FunctionExecutionBinding.HostFunction(
                MOD, "f", SIG)) == DynamicResolutionKind.HOST,
            "a HostFunction resolves HOST");
        check(DynamicReturnBoundaryProtocol.kindOf(new FunctionExecutionBinding.HostFunctionValue(
                MOD, nextOpId(), SIG)) == DynamicResolutionKind.HOST,
            "a HostFunctionValue resolves HOST");
        check(DynamicReturnBoundaryProtocol.kindOf(new FunctionExecutionBinding.ExternalFunction(
                MOD, "f", SIG, ExternalExecutionOwner.RETAINED_ABI)) == DynamicResolutionKind.EXTERNAL,
            "a RETAINED_ABI external resolves EXTERNAL");
        check(DynamicReturnBoundaryProtocol.kindOf(new FunctionExecutionBinding.ExternalFunction(
                MOD, "f", SIG, ExternalExecutionOwner.SHARED_BODY)) == DynamicResolutionKind.SHARED_BODY,
            "a SHARED_BODY external resolves SHARED_BODY");
        check(throwsIllegalArgument(() -> DynamicReturnBoundaryProtocol.kindOf(
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(3), 0), SIG, SIG))),
            "an AdapterBinding fails closed (its class derives from the D15-resolved source "
                + "binding)");
        check(throwsIllegalArgument(() -> DynamicReturnBoundaryProtocol.kindOf(
                new FunctionExecutionBinding.DynamicFunctionValue(nextOpId(), SIG))),
            "a DynamicFunctionValue fails closed (the record names no execution class; the "
                + "class is the runtime value's producing registration)");

        OpId deal = nextOpId();
        OpId host = nextOpId();
        OpId external = nextOpId();
        KindPayload.DynamicReturnBoundary record =
            new KindPayload.DynamicReturnBoundary(deal, host, external);
        ReturnBoundarySelection dealSel =
            DynamicReturnBoundaryProtocol.select(record, DynamicResolutionKind.DEAL_BODY);
        check(dealSel instanceof ReturnBoundarySelection.CalleeReturn calleeReturn
                && calleeReturn.boundaryOpId().equals(deal),
            "DEAL_BODY selects the recorded DEAL-body cell owned by the callee RETURN");
        ReturnBoundarySelection hostSel =
            DynamicReturnBoundaryProtocol.select(record, DynamicResolutionKind.HOST);
        check(hostSel instanceof ReturnBoundarySelection.CallTerminal hostTerminal
                && hostTerminal.boundaryOpId().equals(host)
                && hostTerminal.kind() == BoundaryKind.HOST_TO_DEAL,
            "HOST selects the recorded host cell (HOST_TO_DEAL) owned by the call op");
        ReturnBoundarySelection externalSel =
            DynamicReturnBoundaryProtocol.select(record, DynamicResolutionKind.EXTERNAL);
        check(externalSel instanceof ReturnBoundarySelection.CallTerminal externalTerminal
                && externalTerminal.boundaryOpId().equals(external)
                && externalTerminal.kind() == BoundaryKind.EXTERNAL_RETURN,
            "EXTERNAL selects the recorded retained-ABI cell (EXTERNAL_RETURN) owned by the "
                + "call op");
        check(DynamicReturnBoundaryProtocol.select(record, DynamicResolutionKind.SHARED_BODY)
                == ReturnBoundarySelection.None.INSTANCE,
            "SHARED_BODY selects zero caller-side return boundaries (the callee RETURN under "
                + "EXTERNAL_ENTRY runs the single EXTERNAL_RETURN)");
    }

    // =========================================================================
    // 3. Validator positives
    // =========================================================================

    /**
     * One unit-level dynamic CALL: the three recorded return cells plus
     * one parameter boundary. The DEAL-body cell is parented to a RETURN
     * naming the CALL (the callee-side ownership shape); the host and
     * retained-ABI cells are parented to the CALL (call-op ownership).
     */
    private static LoweredModuleUnit dynamicCallUnit(OpId dealBoundaryId,
            BoundaryKind dealKind, RuntimeDescriptor dealDescriptor,
            FailurePolicyId dealPolicy, OpId hostBoundaryId, BoundaryKind hostKind,
            FailurePolicyId hostPolicy, OpId externalBoundaryId, BoundaryKind externalKind,
            FailurePolicyId externalPolicy) {
        OpId callOp = nextOpId();
        OpId paramBoundary = nextOpId();
        OpId returnOp = nextOpId();
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp));
        ops.add(boundaryWith(dealBoundaryId, dealKind, dealDescriptor, dealPolicy, returnOp));
        ops.add(boundaryWith(hostBoundaryId, hostKind, INT, hostPolicy, callOp));
        ops.add(boundaryWith(externalBoundaryId, externalKind, INT, externalPolicy, callOp));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), callOp, dealBoundaryId),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, callOp));
        ops.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                SIG, List.of(paramBoundary), null,
                new KindPayload.DynamicReturnBoundary(dealBoundaryId, hostBoundaryId,
                    externalBoundaryId),
                null, null),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return unit(Map.of(), ops);
    }

    private static void testDynamicCallPositive() {
        System.out.println("-- Validator positive: unit-level dynamic CALL --");

        OpId deal = nextOpId();
        OpId host = nextOpId();
        OpId external = nextOpId();
        LoweredModuleUnit unit = dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, host, BoundaryKind.HOST_TO_DEAL,
            FailurePolicyId.HOST_SYNC_RETURN, external, BoundaryKind.EXTERNAL_RETURN,
            FailurePolicyId.TYPE_DESCRIPTOR);
        assertPass(SemanticIrValidator.validate(unit, FACTS),
            "the dynamic CALL records valid return boundaries (typed)");
        String text = SemanticIrValidator.toUnitText(unit);
        assertPass(SemanticIrValidator.validateText(text, FACTS),
            "the dynamic CALL records valid return boundaries (text)");
        check(text.contains("\"type\":\"dynamic\"") && text.contains("\"dealBodyBoundaryOpId\"")
                && text.contains("\"hostBoundaryOpId\"")
                && text.contains("\"externalBoundaryOpId\""),
            "the dynamic callee and its three entries render in the canonical text");

        // The same unit re-validates after the text round-trip through the
        // single parser (parse → re-serialize → validate).
        CanonicalJson.Value parsed = CanonicalJson.parse(text);
        String reserialized = CanonicalJson.serializeText(parsed);
        assertPass(SemanticIrValidator.validateText(reserialized, FACTS),
            "the dynamic CALL round-trips through the single canonical parser");
    }

    private static void testDynamicCallPositiveProject() {
        System.out.println("-- Validator positive: project-level dynamic CALL (callee-side "
            + "DEAL-body cell) --");

        OpId callOp = nextOpId();
        OpId paramBoundary = nextOpId();
        OpId hostBoundary = nextOpId();
        OpId externalBoundary = nextOpId();
        OpId dealBoundary = new OpId(MOD_B, 7);
        OpId calleeReturn = new OpId(MOD_B, 8);
        List<SemanticOp> callerOps = new ArrayList<>();
        callerOps.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp));
        callerOps.add(boundaryWith(hostBoundary, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.HOST_SYNC_RETURN, callOp));
        callerOps.add(boundaryWith(externalBoundary, BoundaryKind.EXTERNAL_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp));
        callerOps.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                SIG, List.of(paramBoundary), null,
                new KindPayload.DynamicReturnBoundary(dealBoundary, hostBoundary,
                    externalBoundary),
                null, null),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        LoweredModuleUnit caller = unit(MOD, Map.of(), callerOps);

        List<SemanticOp> calleeOps = new ArrayList<>();
        calleeOps.add(boundaryWith(dealBoundary, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, calleeReturn));
        calleeOps.add(opWith(calleeReturn, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(nextValue(), new FunctionId(2), callOp, dealBoundary),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        LoweredModuleUnit callee = unit(MOD_B, Map.of(), calleeOps);

        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        modules.put(MOD_B, callee);
        modules.put(MOD, caller);
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(
                MOD_B, new ExternalModuleInterface(MOD_B, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                MOD, new ExternalModuleInterface(MOD, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, index, modules, MOD);
        assertPass(SemanticIrValidator.validate(project, FACTS),
            "the cross-unit dynamic CALL validates at project level (typed)");
        assertPass(SemanticIrValidator.validateText(SemanticIrValidator.toProjectText(project),
                FACTS),
            "the cross-unit dynamic CALL validates at project level (text)");
    }

    private static void testDynamicAsyncPositive() {
        System.out.println("-- Validator positive: dynamic ASYNC_START --");

        OpId startOp = nextOpId();
        OpId paramBoundary = nextOpId();
        OpId returnBoundary = nextOpId();
        OpId returnOp = nextOpId();
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, startOp));
        ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), startOp,
                returnBoundary),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, startOp));
        ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
            new KindPayload.AsyncStartPayload(
                new KindPayload.CallCallee.Dynamic(new ValueId(88)),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                List.of(paramBoundary), INT, returnBoundary, null, null),
            new AsyncTokenId.Canonical(5, AsyncTokenOwner.DEAL_BODY_TASK),
            InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
        LoweredModuleUnit unit = unit(Map.of(), ops);
        assertPass(SemanticIrValidator.validate(unit, FACTS),
            "the dynamic ASYNC_START records the DEAL_BODY task return boundary (typed)");
        assertPass(SemanticIrValidator.validateText(SemanticIrValidator.toUnitText(unit), FACTS),
            "the dynamic ASYNC_START records the DEAL_BODY task return boundary (text)");
    }

    // =========================================================================
    // 4. Validator negatives
    // =========================================================================

    private static void testDynamicCallNegatives() {
        System.out.println("-- Validator negatives: dynamic CALL cells and records --");

        OpId deal = nextOpId();
        OpId host = nextOpId();
        OpId external = nextOpId();

        // Per-class cell violations (typed).
        negative("dynamic.dealBody.wrongKind",
            dynamicCallUnit(deal, BoundaryKind.HOST_TO_DEAL, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.HOST_TO_DEAL, FailurePolicyId.HOST_SYNC_RETURN, external,
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's DEAL-body return boundary must be FUNCTION_RETURN");
        negative("dynamic.dealBody.wrongDescriptor",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, STR, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.HOST_TO_DEAL, FailurePolicyId.HOST_SYNC_RETURN, external,
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's DEAL-body FUNCTION_RETURN boundary must check the declared "
                + "return descriptor");
        negative("dynamic.host.wrongKind",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.FUNCTION_RETURN, FailurePolicyId.HOST_SYNC_RETURN, external,
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's host return boundary must be HOST_TO_DEAL + HOST_SYNC_RETURN");
        negative("dynamic.host.wrongPolicy",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.HOST_TO_DEAL, FailurePolicyId.TYPE_DESCRIPTOR, external,
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's host return boundary must be HOST_TO_DEAL + HOST_SYNC_RETURN");
        negative("dynamic.external.wrongKind",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.HOST_TO_DEAL, FailurePolicyId.HOST_SYNC_RETURN, external,
                BoundaryKind.FUNCTION_RETURN, FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's retained-ABI return boundary must be EXTERNAL_RETURN");
        negative("dynamic.external.wrongPolicy",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                host, BoundaryKind.HOST_TO_DEAL, FailurePolicyId.HOST_SYNC_RETURN, external,
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.HOST_SYNC_RETURN),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's retained-ABI return boundary must be EXTERNAL_RETURN under the "
                + "descriptor-kind rule");
        // Unresolvable / non-BOUNDARY entries (typed).
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId hostOk = nextOpId();
            OpId externalOk = nextOpId();
            OpId ghost = nextOpId(); // no op carries this id
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(hostOk, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(boundaryWith(externalOk, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                    SIG, List.of(paramBoundary), null,
                    new KindPayload.DynamicReturnBoundary(ghost, hostOk, externalOk),
                    null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("dynamic.entry.unresolved", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "dynamic return boundary " + ghost + " does not resolve");
        }
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId hostOk = nextOpId();
            OpId externalOk = nextOpId();
            OpId nonBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(hostOk, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(boundaryWith(externalOk, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(nonBoundary, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                    SIG, List.of(paramBoundary), null,
                    new KindPayload.DynamicReturnBoundary(nonBoundary, hostOk, externalOk),
                    null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("dynamic.entry.notABoundary", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "dynamic return boundary " + nonBoundary + " is not a BOUNDARY op");
        }

        // Per-class cell checks close on the invocation side (direction
        // (b)): a recorded cell of the wrong class must be rejected even
        // when its direction-(a) cell never consults the invocation.
        negative("dynamic.hostExternal.wrongCellKind",
            dynamicCallUnit(deal, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, host, BoundaryKind.VARIABLE_DECLARATION,
                FailurePolicyId.TYPE_DESCRIPTOR, external, BoundaryKind.VARIABLE_DECLARATION,
                FailurePolicyId.TYPE_DESCRIPTOR),
            SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "the DYNAMIC CALL's host return boundary must be HOST_TO_DEAL + "
                + "HOST_SYNC_RETURN on the declared return descriptor");

        // All three entries aliasing one FUNCTION_RETURN cell.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId aliased = nextOpId();
            OpId returnOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(aliased, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), callOp,
                    aliased),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                    SIG, List.of(paramBoundary), null,
                    new KindPayload.DynamicReturnBoundary(aliased, aliased, aliased),
                    null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("dynamic.entries.aliased", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC CALL's three dynamic return-boundary entries must be "
                    + "mutually distinct");
        }

        // The DEAL-body cell owned by another CALL's RETURN: the recorded
        // cell must be parented to a RETURN naming THIS call.
        {
            OpId otherCall = nextOpId();
            OpId otherParam = nextOpId();
            OpId otherRet = nextOpId();
            OpId otherReturn = nextOpId();
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(otherParam, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, otherCall));
            ops.add(boundaryWith(otherRet, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, otherReturn));
            ops.add(opWith(otherReturn, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), otherCall,
                    otherRet),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, otherCall));
            ops.add(opWith(otherCall, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    SIG, List.of(otherParam), otherRet, null, new BlockId(1), null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(hostCell, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(boundaryWith(externalCell, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                    SIG, List.of(paramBoundary), null,
                    new KindPayload.DynamicReturnBoundary(otherRet, hostCell, externalCell),
                    null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("dynamic.deal.misOwned", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC CALL's DEAL-body return boundary must be parented to a "
                    + "RETURN naming the CALL");
        }

        // The DEAL-body cell class is closed on the text surface as well
        // (direction (b)): a kind whose direction-(a) cell never consults
        // the invocation cannot bypass the per-class check.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealBoundary = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId returnOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(dealBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(boundaryWith(hostCell, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(boundaryWith(externalCell, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), callOp,
                    dealBoundary),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(new ValueId(77)),
                    SIG, List.of(paramBoundary), null,
                    new KindPayload.DynamicReturnBoundary(dealBoundary, hostCell,
                        externalCell),
                    null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit unit = unit(Map.of(), ops);
            String wrongKind = substituteBoundaryKind(SemanticIrValidator.toUnitText(unit),
                dealBoundary, "VARIABLE_DECLARATION");
            negativeText("dynamic.deal.wrongKindText", wrongKind,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC CALL's DEAL-body return boundary must be FUNCTION_RETURN");
        }

        // Text-surface record violations (one leaf + digest recompute).
        {
            LoweredModuleUnit base = dynamicCallUnit(nextOpId(), BoundaryKind.FUNCTION_RETURN,
                INT, FailurePolicyId.TYPE_DESCRIPTOR, nextOpId(), BoundaryKind.HOST_TO_DEAL,
                FailurePolicyId.HOST_SYNC_RETURN, nextOpId(), BoundaryKind.EXTERNAL_RETURN,
                FailurePolicyId.TYPE_DESCRIPTOR);
            String text = SemanticIrValidator.toUnitText(base);
            String missingRecord = dropPayloadLeaf(text, SemanticOpKind.CALL,
                "dynamicReturnBoundary");
            negativeText("dynamic.missingRecord", missingRecord,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "a DYNAMIC callee must record its dynamic return-boundary set");
            String singleReturn = setCallReturnBoundary(text);
            negativeText("dynamic.singleReturnSet", singleReturn,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "a DYNAMIC CALL records no single returnBoundaryOpId");
            String wrongMode = substitutePayloadLeaf(text, SemanticOpKind.CALL, "mode",
                "DIRECT");
            negativeText("dynamic.wrongModeText", wrongMode,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "a DYNAMIC callee is admissible only under CallMode INDIRECT");
            String openCallee = substituteCalleeType(text, "openCallee");
            negativeText("dynamic.openCalleeType", openCallee, SemanticIrValidator.R_ENUM,
                "open value \"openCallee\" in a closed CallCallee position");
        }

        // A static callee carrying the dynamic record (text-injected).
        {
            LoweredModuleUnit base = dynamicCallUnit(nextOpId(), BoundaryKind.FUNCTION_RETURN,
                INT, FailurePolicyId.TYPE_DESCRIPTOR, nextOpId(), BoundaryKind.HOST_TO_DEAL,
                FailurePolicyId.HOST_SYNC_RETURN, nextOpId(), BoundaryKind.EXTERNAL_RETURN,
                FailurePolicyId.TYPE_DESCRIPTOR);
            String text = SemanticIrValidator.toUnitText(base);
            String record =
                "{\"dealBodyBoundaryOpId\":{\"id\":1,\"modulePath\":\"mod.a\",\"type\":\"op\"},"
                    + "\"externalBoundaryOpId\":{\"id\":1,\"modulePath\":\"mod.a\",\"type\":\"op\"},"
                    + "\"hostBoundaryOpId\":{\"id\":1,\"modulePath\":\"mod.a\",\"type\":\"op\"}}";
            String staticCallee = substituteCalleeType(text, "static");
            String withRecord = setPayloadLeaf(staticCallee, SemanticOpKind.CALL,
                "dynamicReturnBoundary", parseJson(record));
            negativeText("static.withRecord", withRecord,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "only a DYNAMIC callee records the dynamic return-boundary set");
        }

        // A non-Dynamic callee carrying a malformed record object: the
        // exclusivity fires on the key's presence, not on parse success
        // (the record is silently unparseable, yet its presence alone is
        // the pinned violation). The baseline DIRECT CALL validates, and
        // only the injected malformed record trips the rule.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId retBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(retBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    SIG, List.of(paramBoundary), retBoundary, null, new BlockId(1), null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit base = unit(Map.of(), ops);
            assertPass(SemanticIrValidator.validate(base, FACTS),
                "the plain DIRECT CALL baseline validates");
            String text = SemanticIrValidator.toUnitText(base);
            String withMalformedRecord = setPayloadLeaf(text, SemanticOpKind.CALL,
                "dynamicReturnBoundary", parseJson("{\"bogus\":1}"));
            negativeText("direct.malformedRecord", withMalformedRecord,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "only a DYNAMIC callee records the dynamic return-boundary set");
        }
    }

    private static void testDynamicAsyncNegatives() {
        System.out.println("-- Validator negatives: dynamic ASYNC_START records --");

        // Missing task return boundary (text-injected).
        {
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            OpId returnOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), startOp,
                    returnBoundary),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Dynamic(new ValueId(88)),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, returnBoundary, null, null),
                new AsyncTokenId.Canonical(5, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit unit = unit(Map.of(), ops);
            String text = SemanticIrValidator.toUnitText(unit);
            String missing = dropPayloadLeaf(text, SemanticOpKind.ASYNC_START,
                "returnBoundaryOpId");
            negativeText("async.dynamic.missingReturn", missing,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "a DYNAMIC ASYNC_START must record its DEAL_BODY task return boundary");
            String wrongSource = substitutePayloadLeaf(text, SemanticOpKind.ASYNC_START,
                "source", "HOST");
            negativeText("async.dynamic.wrongSource", wrongSource,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "a DYNAMIC ASYNC_START records source DEAL_BODY");
            String badCell = substituteBoundaryKind(text, returnBoundary,
                "HOST_TO_DEAL");
            negativeText("async.dynamic.badCell", badCell,
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC ASYNC_START's recorded task return boundary must be "
                    + "FUNCTION_RETURN");
        }

        // The recorded task cell of the wrong class (a kind whose
        // direction-(a) cell never consults the invocation).
        {
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId declParent = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(taskCell, BoundaryKind.VARIABLE_DECLARATION, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, declParent));
            ops.add(opWith(declParent, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Dynamic(new ValueId(88)),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, taskCell, null, null),
                new AsyncTokenId.Canonical(6, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("async.dynamic.wrongCellKind", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC ASYNC_START's recorded task return boundary must be "
                    + "FUNCTION_RETURN under the descriptor-kind rule on the completion "
                    + "descriptor");
        }

        // The recorded task cell not parented to a RETURN naming the
        // ASYNC_START (a well-formed FUNCTION_RETURN parented directly to
        // the ASYNC_START op).
        {
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(taskCell, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Dynamic(new ValueId(88)),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, taskCell, null, null),
                new AsyncTokenId.Canonical(6, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("async.dynamic.misOwnedCell", unit(Map.of(), ops),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the DYNAMIC ASYNC_START's recorded task return boundary must be "
                    + "parented to a RETURN naming the ASYNC_START");
        }
    }

    // =========================================================================
    // 5. HostFunctionValue crossing closure (R-FUNCTION-BINDING)
    // =========================================================================

    /** The pinned crossing op id of {@link #crossingUnit} (identity 40's correlation). */
    private static final OpId CROSSING_OP = new OpId(MOD, 900);

    /** A callback-argument host crossing materializing a function value (identity 40). */
    private static LoweredModuleUnit crossingUnit(
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings) {
        OpId callbackOp = nextOpId();
        OpId crossing = CROSSING_OP;
        OpId ret = nextOpId();
        RuntimeDescriptor.Func callbackSig =
            new RuntimeDescriptor.Func(List.of(SIG), INT);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWithInput(crossing, BoundaryKind.HOST_TO_DEAL, SIG,
            FailurePolicyId.FUNCTION_SIGNATURE, callbackOp, new ValueId(40)));
        ops.add(boundaryWith(ret, BoundaryKind.DEAL_TO_HOST, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
            new KindPayload.CallbackInvokePayload(new ValueId(9), callbackSig,
                List.of(crossing), ret),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return unit(bindings, ops);
    }

    private static void testHostFunctionValueClosure() {
        System.out.println("-- HostFunctionValue crossing closure (callback-delivered "
            + "identities) --");

        Map<FunctionAllocationIdentity, FunctionExecutionBinding> positive = Map.of(
            new FunctionAllocationIdentity(40),
            new FunctionExecutionBinding.HostFunctionValue(MOD, CROSSING_OP, SIG));
        LoweredModuleUnit positiveUnit = crossingUnit(positive);
        assertPass(SemanticIrValidator.validate(positiveUnit, FACTS),
            "the function-typed HOST_TO_DEAL crossing with its matching registration "
                + "(typed)");
        String text = SemanticIrValidator.toUnitText(positiveUnit);
        assertPass(SemanticIrValidator.validateText(text, FACTS),
            "the function-typed HOST_TO_DEAL crossing with its matching registration "
                + "(text)");
        check(text.contains("\"materializingBoundaryOpId\":{\"id\":"),
            "the text protocol carries the hostFunctionValue correlation id");

        // Negatives (typed): missing registration, dangling id, wrong key.
        negative("crossing.missingRegistration", crossingUnit(Map.of()),
            SemanticIrValidator.R_FUNCTION_BINDING,
            "no matching HostFunctionValue registration");
        OpId dangling = nextOpId();
        negative("crossing.danglingCorrelation",
            crossingUnit(Map.of(new FunctionAllocationIdentity(40),
                new FunctionExecutionBinding.HostFunctionValue(MOD, dangling, SIG))),
            SemanticIrValidator.R_FUNCTION_BINDING,
            "does not resolve to a HOST_TO_DEAL boundary op of the unit");
        negative("crossing.wrongKey",
            crossingUnit(Map.of(new FunctionAllocationIdentity(41),
                new FunctionExecutionBinding.HostFunctionValue(MOD, CROSSING_OP, SIG))),
            SemanticIrValidator.R_FUNCTION_BINDING,
            "does not carry the registered allocation identity as its input");

        // A HostFunctionValue registration whose materializing op is a
        // boundary of another kind.
        {
            OpId otherBoundary = nextOpId();
            OpId otherParent = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(otherBoundary, BoundaryKind.VARIABLE_DECLARATION, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, otherParent));
            ops.add(opWith(otherParent, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit unit = unit(Map.of(
                    new FunctionAllocationIdentity(55),
                    new FunctionExecutionBinding.HostFunctionValue(MOD, otherBoundary, SIG)),
                ops);
            negative("registration.wrongCrossingKind", unit,
                SemanticIrValidator.R_FUNCTION_BINDING,
                "does not resolve to a HOST_TO_DEAL boundary op of the unit");
        }

        // Null correlation id (text-injected into the functionBindings entry).
        {
            String nulled = nullMaterializingBoundary(text);
            negativeText("registration.nullCorrelation", nulled,
                SemanticIrValidator.R_FUNCTION_BINDING,
                "carries no materializingBoundaryOpId");
        }
    }

    // =========================================================================
    // 6. Canonical rendering details
    // =========================================================================

    private static void testCanonicalRendering() {
        System.out.println("-- Canonical rendering: callee, record, correlation id --");

        ValueId callee = new ValueId(7);
        KindPayload.CallCallee.Dynamic dynamic = new KindPayload.CallCallee.Dynamic(callee);
        CanonicalJson.Value calleeJson = ContractSnapshotCanonicalizer.calleeJson(dynamic);
        check(calleeJson instanceof CanonicalJson.Obj calleeObj
                && "dynamic".equals(strAt(calleeObj, "type"))
                && at(calleeObj, "callee") instanceof CanonicalJson.Obj,
            "the dynamic callee renders as the pinned {\"callee\", \"type\":\"dynamic\"} object");

        OpId deal = nextOpId();
        OpId host = nextOpId();
        OpId external = nextOpId();
        CanonicalJson.Value recordJson = ContractSnapshotCanonicalizer.dynamicReturnBoundaryJson(
            new KindPayload.DynamicReturnBoundary(deal, host, external));
        check(recordJson instanceof CanonicalJson.Obj recordObj
                && at(recordObj, "dealBodyBoundaryOpId") instanceof CanonicalJson.Obj
                && at(recordObj, "hostBoundaryOpId") instanceof CanonicalJson.Obj
                && at(recordObj, "externalBoundaryOpId") instanceof CanonicalJson.Obj,
            "the dynamic return-boundary set renders its three op-id entries");

        CanonicalJson.Value bindingJson = ContractSnapshotCanonicalizer.bindingJson(
            new FunctionExecutionBinding.HostFunctionValue(MOD, external, SIG));
        check(bindingJson instanceof CanonicalJson.Obj bindingObj
                && at(bindingObj, "materializingBoundaryOpId") instanceof CanonicalJson.Obj,
            "the hostFunctionValue binding renders its materializingBoundaryOpId");
    }

    // =========================================================================
    // Text-surface mutation helpers (one leaf + digest recompute)
    // =========================================================================

    private static CanonicalJson.Value at(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }

    private static String strAt(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = at(obj, key);
        return value instanceof CanonicalJson.Str str ? str.value() : null;
    }

    private static CanonicalJson.Obj withEntry(CanonicalJson.Obj obj, String key,
            CanonicalJson.Value value) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            entries.add(entry.key().equals(key) ? CanonicalJson.e(key, value) : entry);
        }
        return CanonicalJson.obj(entries);
    }

    private static CanonicalJson.Obj withoutEntry(CanonicalJson.Obj obj, String key) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (!entry.key().equals(key)) {
                entries.add(entry);
            }
        }
        return CanonicalJson.obj(entries);
    }

    private static CanonicalJson.Obj parseJson(String text) {
        return (CanonicalJson.Obj) CanonicalJson.parse(text);
    }

    private static String recomputeContractDigest(CanonicalJson.Obj contract) {
        List<CanonicalJson.Entry> eight = new ArrayList<>();
        for (CanonicalJson.Entry entry : contract.entries()) {
            if (!"canonicalDigest".equals(entry.key())) {
                eight.add(entry);
            }
        }
        return CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(CanonicalJson.obj(eight)));
    }

    private static CanonicalJson.Obj contractWith(CanonicalJson.Obj contract, String key,
            CanonicalJson.Value value) {
        CanonicalJson.Obj updated = withEntry(contract, key, value);
        String digest = recomputeContractDigest(updated);
        return withEntry(updated, "canonicalDigest", CanonicalJson.str(digest));
    }

    private static CanonicalJson.Obj firstOpOfKind(CanonicalJson.Obj root, String kind) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        for (CanonicalJson.Value item : ops.items()) {
            CanonicalJson.Obj op = (CanonicalJson.Obj) item;
            if (kind.equals(strAt(op, "kind"))) {
                return op;
            }
        }
        throw new IllegalArgumentException("no op of kind " + kind);
    }

    private static CanonicalJson.Obj opById(CanonicalJson.Obj root, long id) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        for (CanonicalJson.Value item : ops.items()) {
            CanonicalJson.Obj op = (CanonicalJson.Obj) item;
            CanonicalJson.Obj opId = (CanonicalJson.Obj) at(op, "opId");
            CanonicalJson.Value idValue = at(opId, "id");
            if (idValue instanceof CanonicalJson.Int i && i.value() == id) {
                return op;
            }
        }
        throw new IllegalArgumentException("no op with id " + id);
    }

    private static CanonicalJson.Obj withOp(CanonicalJson.Obj root, CanonicalJson.Obj updated) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        CanonicalJson.Obj updatedOpId = (CanonicalJson.Obj) at(updated, "opId");
        int target = ((CanonicalJson.Int) at(updatedOpId, "id")).value();
        List<CanonicalJson.Value> items = new ArrayList<>();
        for (CanonicalJson.Value item : ops.items()) {
            CanonicalJson.Obj op = (CanonicalJson.Obj) item;
            CanonicalJson.Obj opId = (CanonicalJson.Obj) at(op, "opId");
            int id = ((CanonicalJson.Int) at(opId, "id")).value();
            items.add(id == target ? updated : item);
        }
        return withEntry(root, "ops", CanonicalJson.arr(items));
    }

    /** Substitutes one payload leaf of the first op of the given kind (digest recomputed). */
    private static String substitutePayloadLeaf(String text, SemanticOpKind kind, String key,
            String to) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = firstOpOfKind(root, kind.name());
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, key, CanonicalJson.str(to));
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Sets one payload leaf of the first op of the given kind to an arbitrary value. */
    private static String setPayloadLeaf(String text, SemanticOpKind kind, String key,
            CanonicalJson.Value value) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = firstOpOfKind(root, kind.name());
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, key, value);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Drops one payload leaf of the first op of the given kind (digest recomputed). */
    private static String dropPayloadLeaf(String text, SemanticOpKind kind, String key) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = firstOpOfKind(root, kind.name());
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withoutEntry(payload, key);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Substitutes the callee's closed type tag of the first CALL op. */
    private static String substituteCalleeType(String text, String to) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = firstOpOfKind(root, "CALL");
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj callee = (CanonicalJson.Obj) at(payload, "callee");
        CanonicalJson.Obj callee2 = withEntry(callee, "type", CanonicalJson.str(to));
        CanonicalJson.Obj payload2 = withEntry(payload, "callee", callee2);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Sets the single returnBoundaryOpId of the first CALL op to the host cell entry. */
    private static String setCallReturnBoundary(String text) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = firstOpOfKind(root, "CALL");
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj record = (CanonicalJson.Obj) at(payload, "dynamicReturnBoundary");
        CanonicalJson.Value hostEntry = at(record, "hostBoundaryOpId");
        CanonicalJson.Obj payload2 = withEntry(payload, "returnBoundaryOpId", hostEntry);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Substitutes one boundary op's kind leaf (digest recomputed). */
    private static String substituteBoundaryKind(String text, OpId boundaryId, String to) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Obj op = opById(root, boundaryId.id());
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, "kind", CanonicalJson.str(to));
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return CanonicalJson.serializeText(withOp(root, op2));
    }

    /** Renders the hostFunctionValue binding entry with a null correlation id. */
    private static String nullMaterializingBoundary(String text) {
        CanonicalJson.Obj root = parseJson(text);
        CanonicalJson.Arr bindings = (CanonicalJson.Arr) at(root, "functionBindings");
        List<CanonicalJson.Value> items = new ArrayList<>();
        for (CanonicalJson.Value item : bindings.items()) {
            CanonicalJson.Obj entry = (CanonicalJson.Obj) item;
            CanonicalJson.Obj binding = (CanonicalJson.Obj) at(entry, "binding");
            if ("hostFunctionValue".equals(strAt(binding, "type"))) {
                CanonicalJson.Obj nulled = withEntry(binding, "materializingBoundaryOpId",
                    CanonicalJson.nullValue());
                entry = withEntry(entry, "binding", nulled);
            }
            items.add(entry);
        }
        return CanonicalJson.serializeText(withEntry(root, "functionBindings",
            CanonicalJson.arr(items)));
    }

    // =========================================================================
    // 6. Oracle execution — the runtime resolution reconciliation
    // =========================================================================

    /**
     * The oracle-execution fixture for one dynamically resolved CALL: the
     * module-init block runs one CONST (the argument value 7) and the
     * dynamic CALL; the recorded three return cells (DEAL-body
     * {@code FUNCTION_RETURN} parented to the callee RETURN, call-op-owned
     * {@code HOST_TO_DEAL} and {@code EXTERNAL_RETURN}) plus one
     * {@code FUNCTION_PARAMETER} boundary; the DEAL-body resolution's
     * body block (one leading parameter ALLOC + the RETURN).
     */
    private static LoweredModuleUnit dynamicOracleCaller(
            FunctionExecutionBinding binding, ValueId calleeId, OpId constOp,
            OpId paramBoundary, OpId dealCell, OpId hostCell, OpId externalCell,
            OpId allocOp, OpId returnOp, OpId callOp, ValueId argValue,
            ValueId callResult, BlockId bodyBlock) {
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(constOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(7)), argValue, INT,
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWithInput(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp, argValue));
        ops.add(boundaryWith(dealCell, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(boundaryWith(hostCell, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.HOST_SYNC_RETURN, callOp));
        ops.add(boundaryWith(externalCell, BoundaryKind.EXTERNAL_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(1), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(1), callOp, dealCell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, callOp));
        ops.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Dynamic(calleeId),
                SIG, List.of(paramBoundary), null,
                new KindPayload.DynamicReturnBoundary(dealCell, hostCell, externalCell),
                null, null),
            callResult, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        Map<FunctionId, LoweredFunction> functions = Map.of(
            new FunctionId(1),
            new LoweredFunction(new FunctionId(1), SIG, List.of(), bodyBlock));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
            new FunctionAllocationIdentity(calleeId.id()), binding);
        return unit(MOD, functions, bindings, ops);
    }

    /** The block-membership table of one dynamic-CALL caller unit. */
    private static StructuredBodyTable dynamicOracleTable(BlockId bodyBlock, OpId constOp,
            OpId callOp, OpId allocOp, OpId returnOp) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        blockOps.put(new BlockId(0), List.of(constOp, callOp));
        blockOps.put(bodyBlock, List.of(allocOp, returnOp));
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        opBlocks.put(constOp, new BlockId(0));
        opBlocks.put(callOp, new BlockId(0));
        opBlocks.put(allocOp, bodyBlock);
        opBlocks.put(returnOp, bodyBlock);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /** One op's SUCCESS event with the exact output atom. */
    private static boolean oracleSucceeded(SemanticRuntimeModel.ConsumerRun run, OpId op,
            String output) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op) && event.phase() == SemanticRuntimeModel.Phase.SUCCESS
                    && output.equals(event.output())) {
                return true;
            }
        }
        return false;
    }

    /** Whether the run emitted any event for the op. */
    private static boolean oracleTouched(SemanticRuntimeModel.ConsumerRun run, OpId op) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)) {
                return true;
            }
        }
        return false;
    }

    /** The count of SUCCESS events of one boundary kind within one unit's op set. */
    private static long oracleBoundarySuccesses(SemanticRuntimeModel.ConsumerRun run,
            LoweredModuleUnit unit, BoundaryKind kind) {
        long count = 0;
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.phase() == SemanticRuntimeModel.Phase.SUCCESS
                    && event.kind() == SemanticOpKind.BOUNDARY) {
                for (SemanticOp op : unit.ops()) {
                    if (op.opId().equals(event.op())
                            && ((KindPayload.BoundaryPayload) op.payload()).kind() == kind) {
                        count++;
                    }
                }
            }
        }
        return count;
    }

    /** Whether the run recorded the exact ordered effect. */
    private static boolean oracleEffect(SemanticRuntimeModel.ConsumerRun run,
            SemanticRuntimeModel.EffectEvent.Kind kind, String text) {
        return run.effects().contains(new SemanticRuntimeModel.EffectEvent(kind, text));
    }

    /**
     * The oracle-execution fixture for one dynamically resolved
     * {@code ASYNC_START}: the module-init block runs one CONST (the
     * argument value 7), the dynamic {@code ASYNC_START} (recorded source
     * {@code DEAL_BODY} — the single recorded caller-side cell is the
     * {@code FUNCTION_RETURN} task cell parented to the task body's
     * {@code RETURN}), and the consuming {@code AWAIT}; the task body
     * block holds one leading parameter ALLOC + the RETURN.
     */
    private static LoweredModuleUnit dynamicOracleAsyncCaller(
            FunctionExecutionBinding binding, AsyncTokenId token, ValueId calleeId,
            OpId constOp, OpId paramBoundary, OpId taskCell, OpId allocOp, OpId returnOp,
            OpId startOp, OpId completionBoundary, OpId awaitOp, ValueId argValue,
            ValueId awaitResult, BlockId bodyBlock) {
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(constOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(7)), argValue, INT,
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWithInput(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, startOp, argValue));
        ops.add(boundaryWith(taskCell, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(9), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(1), startOp, taskCell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, startOp));
        ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
            new KindPayload.AsyncStartPayload(
                new KindPayload.CallCallee.Dynamic(calleeId),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                List.of(paramBoundary), INT, taskCell, null, null),
            token, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
            FailurePolicyId.ASYNC_COMPLETION, awaitOp));
        ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
            new KindPayload.AwaitPayload(token, INT, completionBoundary),
            awaitResult, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        Map<FunctionId, LoweredFunction> functions = Map.of(
            new FunctionId(1),
            new LoweredFunction(new FunctionId(1), SIG, List.of(), bodyBlock));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
            new FunctionAllocationIdentity(calleeId.id()), binding);
        return unit(MOD, functions, bindings, ops);
    }

    /** The block-membership table of one dynamic-ASYNC_START caller unit. */
    private static StructuredBodyTable dynamicOracleAsyncTable(BlockId bodyBlock,
            OpId constOp, OpId startOp, OpId awaitOp, OpId allocOp, OpId returnOp) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        blockOps.put(new BlockId(0), List.of(constOp, startOp, awaitOp));
        blockOps.put(bodyBlock, List.of(allocOp, returnOp));
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        opBlocks.put(constOp, new BlockId(0));
        opBlocks.put(startOp, new BlockId(0));
        opBlocks.put(awaitOp, new BlockId(0));
        opBlocks.put(allocOp, bodyBlock);
        opBlocks.put(returnOp, bodyBlock);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /**
     * One {@code MOD_B} async callee unit for a dynamic
     * {@code ASYNC_START(EXTERNAL/SHARED_BODY)} fixture: the async
     * {@code EXTERNAL_ENTRY} owns the canonical token, and the entry task
     * body's {@code RETURN} runs the single callee-unit
     * {@code FUNCTION_RETURN}.
     */
    private static LoweredModuleUnit dynamicOracleAsyncCallee(OpId entry, OpId cell,
            OpId allocOp, OpId returnOp, ValueId argValue, BlockId bodyBlock) {
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(cell, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(8), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(2), entry, cell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, entry));
        ops.add(opWith(entry, SemanticOpKind.EXTERNAL_ENTRY,
            new KindPayload.ExternalEntryPayload("f", new FunctionId(2), SIG, true, cell,
                INT),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return unit(MOD_B, Map.of(new FunctionId(2),
                new LoweredFunction(new FunctionId(2), SIG, List.of(), bodyBlock)),
            Map.of(), ops);
    }

    /** The block-membership table of one async callee unit. */
    private static StructuredBodyTable dynamicOracleAsyncCalleeTable(BlockId bodyBlock,
            OpId allocOp, OpId returnOp) {
        return new StructuredBodyTable(
            Map.of(bodyBlock, List.of(allocOp, returnOp), new BlockId(0), List.of()),
            Map.of(allocOp, bodyBlock, returnOp, bodyBlock));
    }

    /**
     * One {@code MOD_B} sync callee unit for a dynamic
     * {@code CALL(SHARED_BODY)} fixture: the sync {@code EXTERNAL_ENTRY}
     * body's {@code RETURN} runs the single {@code EXTERNAL_RETURN}.
     */
    private static LoweredModuleUnit dynamicOracleSyncCallee(OpId entry, OpId cell,
            OpId allocOp, OpId returnOp, ValueId argValue, BlockId bodyBlock) {
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(cell, BoundaryKind.EXTERNAL_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(8), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(2), entry, cell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, entry));
        ops.add(opWith(entry, SemanticOpKind.EXTERNAL_ENTRY,
            new KindPayload.ExternalEntryPayload("f", new FunctionId(2), SIG, false, cell,
                null),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return unit(MOD_B, Map.of(new FunctionId(2),
                new LoweredFunction(new FunctionId(2), SIG, List.of(), bodyBlock)),
            Map.of(), ops);
    }

    /** One executable project over the caller (MOD) and callee (MOD_B) units. */
    private static ExecutableLoweredProject dynamicOracleProject(LoweredModuleUnit callee,
            LoweredModuleUnit caller) {
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        modules.put(MOD_B, callee);
        modules.put(MOD, caller);
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(
                MOD_B, new ExternalModuleInterface(MOD_B, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                MOD, new ExternalModuleInterface(MOD, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        return new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, index, modules, MOD);
    }

    /**
     * The oracle-execution fixture for one adapter-resolved dynamic
     * {@code CALL}: the module-init block runs one CONST (argument value
     * 7), one {@code CLOSURE_NEW} producing the source function value
     * (its producing identity registers the source binding), one
     * {@code FUNCTION_ADAPT} producing the adapter (the D15 source value
     * retention), and the dynamic {@code CALL} whose callee resolves to
     * the {@code AdapterBinding}; the recorded three return cells plus
     * one {@code FUNCTION_PARAMETER} boundary; the DEAL-body resolution's
     * body block (one leading parameter ALLOC + the RETURN).
     */
    private static LoweredModuleUnit dynamicOracleAdapterCaller(
            FunctionExecutionBinding sourceBinding, RuntimeDescriptor.Func sourceSignature,
            RuntimeDescriptor.Func targetSignature, ValueId closureResult, ValueId adaptResult,
            ValueId calleeId, OpId constOp, OpId closureOp, OpId adaptOp, OpId paramBoundary,
            OpId dealCell, OpId hostCell, OpId externalCell, OpId allocOp, OpId returnOp,
            OpId callOp, ValueId argValue, ValueId callResult, BlockId bodyBlock) {
        FunctionExecutionBinding.AdapterBinding adapter =
            new FunctionExecutionBinding.AdapterBinding(adaptOp, CaptureMode.VALUE,
                new AdaptSourceRef.Value(closureResult), sourceSignature, targetSignature);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(constOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(7)), argValue, INT,
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(closureOp, SemanticOpKind.CLOSURE_NEW,
            new KindPayload.ClosureNewPayload(new FunctionId(2), sourceSignature, List.of(),
                new FunctionExecutionBinding.LoweredBody(new FunctionId(2), bodyBlock)),
            closureResult, sourceSignature, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(adaptOp, SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(sourceSignature, targetSignature,
                CaptureMode.VALUE, new AdaptSourceRef.Value(closureResult), null),
            adaptResult, targetSignature, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWithInput(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp, argValue));
        ops.add(boundaryWith(dealCell, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(boundaryWith(hostCell, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.HOST_SYNC_RETURN, callOp));
        ops.add(boundaryWith(externalCell, BoundaryKind.EXTERNAL_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(4), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(2), callOp, dealCell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, callOp));
        ops.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Dynamic(calleeId),
                targetSignature, List.of(paramBoundary), null,
                new KindPayload.DynamicReturnBoundary(dealCell, hostCell, externalCell),
                null, null),
            callResult, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        Map<FunctionId, LoweredFunction> functions = Map.of(
            new FunctionId(2),
            new LoweredFunction(new FunctionId(2), sourceSignature, List.of(), bodyBlock));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>();
        bindings.put(new FunctionAllocationIdentity(closureResult.id()), sourceBinding);
        bindings.put(new FunctionAllocationIdentity(adaptResult.id()), adapter);
        bindings.put(new FunctionAllocationIdentity(calleeId.id()), adapter);
        return unit(MOD, functions, bindings, ops);
    }

    /** The block-membership table of one adapter-resolved dynamic-CALL unit. */
    private static StructuredBodyTable dynamicOracleAdapterCallTable(BlockId bodyBlock,
            OpId constOp, OpId closureOp, OpId adaptOp, OpId callOp, OpId allocOp,
            OpId returnOp) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        blockOps.put(new BlockId(0), List.of(constOp, closureOp, adaptOp, callOp));
        blockOps.put(bodyBlock, List.of(allocOp, returnOp));
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        opBlocks.put(constOp, new BlockId(0));
        opBlocks.put(closureOp, new BlockId(0));
        opBlocks.put(adaptOp, new BlockId(0));
        opBlocks.put(callOp, new BlockId(0));
        opBlocks.put(allocOp, bodyBlock);
        opBlocks.put(returnOp, bodyBlock);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /**
     * The oracle-execution fixture for one adapter-resolved dynamic
     * {@code ASYNC_START}: the same D15 setup as the adapter CALL
     * (CONST + CLOSURE_NEW + FUNCTION_ADAPT), then the dynamic
     * {@code ASYNC_START} (recorded source {@code DEAL_BODY} with the
     * single {@code FUNCTION_RETURN} task cell) and the consuming
     * {@code AWAIT}; the task body block (one leading parameter ALLOC +
     * the RETURN) is the DEAL-body resolution's body.
     */
    private static LoweredModuleUnit dynamicOracleAdapterAsyncCaller(
            FunctionExecutionBinding sourceBinding, RuntimeDescriptor.Func sourceSignature,
            RuntimeDescriptor.Func targetSignature, AsyncTokenId token, ValueId closureResult,
            ValueId adaptResult, ValueId calleeId, OpId constOp, OpId closureOp, OpId adaptOp,
            OpId paramBoundary, OpId taskCell, OpId allocOp, OpId returnOp, OpId startOp,
            OpId completionBoundary, OpId awaitOp, ValueId argValue, ValueId awaitResult,
            BlockId bodyBlock) {
        FunctionExecutionBinding.AdapterBinding adapter =
            new FunctionExecutionBinding.AdapterBinding(adaptOp, CaptureMode.VALUE,
                new AdaptSourceRef.Value(closureResult), sourceSignature, targetSignature);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(opWith(constOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(7)), argValue, INT,
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(closureOp, SemanticOpKind.CLOSURE_NEW,
            new KindPayload.ClosureNewPayload(new FunctionId(2), sourceSignature, List.of(),
                new FunctionExecutionBinding.LoweredBody(new FunctionId(2), bodyBlock)),
            closureResult, sourceSignature, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(adaptOp, SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(sourceSignature, targetSignature,
                CaptureMode.VALUE, new AdaptSourceRef.Value(closureResult), null),
            adaptResult, targetSignature, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWithInput(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, startOp, argValue));
        ops.add(boundaryWith(taskCell, BoundaryKind.FUNCTION_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
        ops.add(opWith(allocOp, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(14), bodyBlock, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(returnOp, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(argValue, new FunctionId(2), startOp, taskCell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, startOp));
        ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
            new KindPayload.AsyncStartPayload(
                new KindPayload.CallCallee.Dynamic(calleeId),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                List.of(paramBoundary), INT, taskCell, null, null),
            token, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
            FailurePolicyId.ASYNC_COMPLETION, awaitOp));
        ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
            new KindPayload.AwaitPayload(token, INT, completionBoundary),
            awaitResult, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        Map<FunctionId, LoweredFunction> functions = Map.of(
            new FunctionId(2),
            new LoweredFunction(new FunctionId(2), sourceSignature, List.of(), bodyBlock));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>();
        bindings.put(new FunctionAllocationIdentity(closureResult.id()), sourceBinding);
        bindings.put(new FunctionAllocationIdentity(adaptResult.id()), adapter);
        bindings.put(new FunctionAllocationIdentity(calleeId.id()), adapter);
        return unit(MOD, functions, bindings, ops);
    }

    /** The block-membership table of one adapter-resolved dynamic-ASYNC_START unit. */
    private static StructuredBodyTable dynamicOracleAdapterAsyncTable(BlockId bodyBlock,
            OpId constOp, OpId closureOp, OpId adaptOp, OpId startOp, OpId awaitOp,
            OpId allocOp, OpId returnOp) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        blockOps.put(new BlockId(0), List.of(constOp, closureOp, adaptOp, startOp, awaitOp));
        blockOps.put(bodyBlock, List.of(allocOp, returnOp));
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        opBlocks.put(constOp, new BlockId(0));
        opBlocks.put(closureOp, new BlockId(0));
        opBlocks.put(adaptOp, new BlockId(0));
        opBlocks.put(startOp, new BlockId(0));
        opBlocks.put(awaitOp, new BlockId(0));
        opBlocks.put(allocOp, bodyBlock);
        opBlocks.put(returnOp, bodyBlock);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    private static void testDynamicOracleExecution() {
        System.out.println("-- Oracle execution: dynamic CALL per runtime resolution class --");

        ValueId callee = new ValueId(77);
        OpId constOp = nextOpId();
        OpId paramBoundary = nextOpId();
        OpId dealCell = nextOpId();
        OpId hostCell = nextOpId();
        OpId externalCell = nextOpId();
        OpId allocOp = nextOpId();
        OpId returnOp = nextOpId();
        OpId callOp = nextOpId();
        ValueId argValue = nextValue();
        ValueId callResult = nextValue();
        BlockId bodyBlock = new BlockId(1);

        // DEAL_BODY: the callee RETURN executes the recorded FUNCTION_RETURN cell.
        LoweredModuleUnit dealUnit = dynamicOracleCaller(
            new FunctionExecutionBinding.LoweredBody(new FunctionId(1), bodyBlock),
            callee, constOp, paramBoundary, dealCell, hostCell, externalCell, allocOp,
            returnOp, callOp, argValue, callResult, bodyBlock);
        StructuredBodyTable dealTable = dynamicOracleTable(bodyBlock, constOp, callOp,
            allocOp, returnOp);
        SemanticRuntimeModel.ConsumerRun dealRun = SemanticOracle.execute(dealUnit, dealTable);
        check(dealRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the DEAL-body dynamic CALL run succeeds");
        check(oracleSucceeded(dealRun, dealCell, "int:7"),
            "the DEAL-body resolution executes the recorded FUNCTION_RETURN cell (int:7)");
        check(oracleSucceeded(dealRun, callOp, "int:7"),
            "the DEAL-body CALL terminal records the checked value");
        check(!oracleTouched(dealRun, hostCell) && !oracleTouched(dealRun, externalCell),
            "the DEAL-body resolution executes exactly the selected cell");

        // HOST: the call op executes the recorded HOST_TO_DEAL cell.
        SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
                check("f".equals(export) && args.size() == 1
                        && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7,
                    "the host call receives the checked argument");
                return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
            }
        };
        LoweredModuleUnit hostUnit = dynamicOracleCaller(
            new FunctionExecutionBinding.HostFunction(MOD, "f", SIG),
            callee, constOp, paramBoundary, dealCell, hostCell, externalCell, allocOp,
            returnOp, callOp, argValue, callResult, bodyBlock);
        StructuredBodyTable hostTable = dynamicOracleTable(bodyBlock, constOp, callOp,
            allocOp, returnOp);
        SemanticRuntimeModel.ConsumerRun hostRun = SemanticOracle.execute(hostUnit, hostTable,
            responder);
        check(hostRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the HOST dynamic CALL run succeeds");
        check(oracleSucceeded(hostRun, hostCell, "int:9"),
            "the HOST resolution executes the recorded HOST_TO_DEAL cell (int:9)");
        check(oracleSucceeded(hostRun, callOp, "int:9"),
            "the HOST CALL terminal records the checked value");
        check(!oracleTouched(hostRun, dealCell) && !oracleTouched(hostRun, externalCell),
            "the HOST resolution executes exactly the selected cell");
        check(hostRun.effects().contains(new SemanticRuntimeModel.EffectEvent(
                SemanticRuntimeModel.EffectEvent.Kind.HOST_CALL, "mod.a.f"))
                && hostRun.effects().contains(new SemanticRuntimeModel.EffectEvent(
                    SemanticRuntimeModel.EffectEvent.Kind.HOST_RETURN, "mod.a.f=int:9")),
            "the HOST resolution records the ordered host effects");

        // EXTERNAL (retained-ABI): the call op executes the recorded EXTERNAL_RETURN cell.
        LoweredModuleUnit externalUnit = dynamicOracleCaller(
            new FunctionExecutionBinding.ExternalFunction(MOD, "f", SIG,
                ExternalExecutionOwner.RETAINED_ABI),
            callee, constOp, paramBoundary, dealCell, hostCell, externalCell, allocOp,
            returnOp, callOp, argValue, callResult, bodyBlock);
        StructuredBodyTable externalTable = dynamicOracleTable(bodyBlock, constOp, callOp,
            allocOp, returnOp);
        SemanticRuntimeModel.ConsumerRun externalRun = SemanticOracle.execute(externalUnit,
            externalTable, responder);
        check(externalRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the retained-ABI EXTERNAL dynamic CALL run succeeds");
        check(oracleSucceeded(externalRun, externalCell, "int:9"),
            "the EXTERNAL resolution executes the recorded EXTERNAL_RETURN cell (int:9)");
        check(oracleSucceeded(externalRun, callOp, "int:9"),
            "the EXTERNAL CALL terminal records the checked value");
        check(!oracleTouched(externalRun, dealCell) && !oracleTouched(externalRun, hostCell),
            "the EXTERNAL resolution executes exactly the selected cell");

        // SHARED_BODY: zero caller-side boundaries — the callee unit's RETURN
        // under its EXTERNAL_ENTRY runs the single EXTERNAL_RETURN cell.
        OpId calleeEntry = new OpId(MOD_B, 1);
        OpId calleeCell = new OpId(MOD_B, 2);
        OpId calleeAlloc = new OpId(MOD_B, 3);
        OpId calleeLoad = new OpId(MOD_B, 4);
        OpId calleeReturn = new OpId(MOD_B, 5);
        ValueId calleeLoaded = new ValueId(500);
        BlockId calleeBody = new BlockId(1);
        List<SemanticOp> calleeOps = new ArrayList<>();
        calleeOps.add(boundaryWith(calleeCell, BoundaryKind.EXTERNAL_RETURN, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, calleeReturn));
        calleeOps.add(opWith(calleeAlloc, SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(new BindingId(2), calleeBody, false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        calleeOps.add(opWith(calleeLoad, SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(new BindingId(2), 0),
            calleeLoaded, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        calleeOps.add(opWith(calleeReturn, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(calleeLoaded, new FunctionId(2), calleeEntry,
                calleeCell),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, calleeEntry));
        calleeOps.add(opWith(calleeEntry, SemanticOpKind.EXTERNAL_ENTRY,
            new KindPayload.ExternalEntryPayload("f", new FunctionId(2), SIG, false,
                calleeCell, null),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        LoweredModuleUnit calleeUnit = unit(MOD_B,
            Map.of(new FunctionId(2),
                new LoweredFunction(new FunctionId(2), SIG, List.of(), calleeBody)),
            Map.of(), calleeOps);
        StructuredBodyTable calleeTable = new StructuredBodyTable(
            Map.of(calleeBody, List.of(calleeAlloc, calleeLoad, calleeReturn),
                new BlockId(0), List.of()),
            Map.of(calleeAlloc, calleeBody, calleeLoad, calleeBody,
                calleeReturn, calleeBody));

        LoweredModuleUnit sharedCaller = dynamicOracleCaller(
            new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG,
                ExternalExecutionOwner.SHARED_BODY),
            callee, constOp, paramBoundary, dealCell, hostCell, externalCell, allocOp,
            returnOp, callOp, argValue, callResult, bodyBlock);
        StructuredBodyTable sharedTable = dynamicOracleTable(bodyBlock, constOp, callOp,
            allocOp, returnOp);
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        modules.put(MOD_B, calleeUnit);
        modules.put(MOD, sharedCaller);
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(
                MOD_B, new ExternalModuleInterface(MOD_B, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                MOD, new ExternalModuleInterface(MOD, ExternalModuleKind.IMPLEMENTATION,
                    List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, index, modules, MOD);
        Map<ModuleId, StructuredBodyTable> tables = Map.of(MOD, sharedTable, MOD_B,
            calleeTable);
        SemanticRuntimeModel.ConsumerRun sharedRun = SemanticOracle.execute(project, tables,
            null);
        check(sharedRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the SHARED_BODY dynamic CALL run succeeds");
        check(oracleSucceeded(sharedRun, calleeCell, "int:7"),
            "the SHARED_BODY resolution runs the callee RETURN's EXTERNAL_RETURN cell "
                + "(int:7)");
        check(oracleSucceeded(sharedRun, callOp, "int:7"),
            "the SHARED_BODY CALL terminal records the value without re-checking");
        check(!oracleTouched(sharedRun, dealCell) && !oracleTouched(sharedRun, hostCell)
                && !oracleTouched(sharedRun, externalCell),
            "the SHARED_BODY resolution executes zero caller-side return boundaries");
    }

    private static void testDynamicAsyncOracleExecution() {
        System.out.println("-- Oracle execution: dynamic ASYNC_START per runtime resolution class --");

        // DEAL_BODY: the task body's RETURN executes the recorded FUNCTION_RETURN
        // task cell — exactly that cell, nothing else.
        {
            ValueId callee = new ValueId(88);
            AsyncTokenId token = new AsyncTokenId.Canonical(901,
                AsyncTokenOwner.DEAL_BODY_TASK);
            OpId constOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(2);
            LoweredModuleUnit unit = dynamicOracleAsyncCaller(
                new FunctionExecutionBinding.LoweredBody(new FunctionId(1), bodyBlock),
                token, callee, constOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAsyncTable(bodyBlock, constOp, startOp,
                awaitOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the DEAL-body dynamic ASYNC_START run succeeds");
            check(oracleSucceeded(run, startOp, "tok:901:DEAL_BODY_TASK"),
                "the DEAL-body ASYNC_START publishes its canonical token");
            check(oracleSucceeded(run, paramBoundary, "int:7"),
                "the DEAL-body resolution checks the argument through the parameter boundary");
            check(oracleSucceeded(run, taskCell, "int:7"),
                "the DEAL-body resolution executes the recorded FUNCTION_RETURN task cell "
                    + "(int:7)");
            check(oracleBoundarySuccesses(run, unit, BoundaryKind.FUNCTION_RETURN) == 1,
                "the DEAL-body resolution executes exactly the recorded task cell");
            check(oracleBoundarySuccesses(run, unit, BoundaryKind.ASYNC_COMPLETION) == 1,
                "the AWAIT runs exactly one ASYNC_COMPLETION boundary");
            check(oracleSucceeded(run, awaitOp, "int:7"),
                "the DEAL-body AWAIT completes through the recorded task cell (int:7)");
        }

        // HOST: startAsync/completeAsync with the derived operation label; zero
        // caller-side return cells execute.
        {
            ValueId callee = new ValueId(88);
            AsyncTokenId token = new AsyncTokenId.Canonical(902,
                AsyncTokenOwner.HOST_OPERATION);
            OpId constOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(3);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public String startAsync(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args,
                        String operationLabel) {
                    check(MOD.equals(module) && "f".equals(export) && SIG.equals(descriptor)
                            && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7
                            && "mod.a.f".equals(operationLabel),
                        "the HOST resolution derives the operation label mod.a.f and "
                            + "starts with the checked argument");
                    return operationLabel;
                }

                @Override
                public SyncOutcome completeAsync(String operationLabel) {
                    check("mod.a.f".equals(operationLabel),
                        "the AWAIT completes the derived operation label");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAsyncCaller(
                new FunctionExecutionBinding.HostFunction(MOD, "f", SIG),
                token, callee, constOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAsyncTable(bodyBlock, constOp, startOp,
                awaitOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the HOST dynamic ASYNC_START run succeeds");
            check(oracleSucceeded(run, startOp, "tok:902:HOST_OPERATION"),
                "the HOST ASYNC_START publishes its canonical token");
            check(oracleSucceeded(run, awaitOp, "int:9"),
                "the HOST AWAIT completes the host operation (int:9)");
            check(!oracleTouched(run, taskCell)
                    && oracleBoundarySuccesses(run, unit, BoundaryKind.FUNCTION_RETURN) == 0,
                "the HOST resolution executes zero caller-side return cells");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP,
                    "mod.a.f")
                    && oracleEffect(run,
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_COMPLETE_RETURN,
                        "mod.a.f=int:9"),
                "the HOST resolution records the ordered async host effects");
        }

        // EXTERNAL and SHARED_BODY: the callee unit's async EXTERNAL_ENTRY owns the
        // canonical token; the caller token links through the execution-bound
        // dynamicReferents map and the caller AWAIT completes through it.
        for (ExternalExecutionOwner owner : List.of(ExternalExecutionOwner.RETAINED_ABI,
                ExternalExecutionOwner.SHARED_BODY)) {
            String label = owner == ExternalExecutionOwner.RETAINED_ABI
                ? "EXTERNAL (retained-ABI)" : "SHARED_BODY";
            long callerToken = owner == ExternalExecutionOwner.RETAINED_ABI ? 903 : 904;
            ValueId callee = new ValueId(88);
            OpId constOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(4);
            OpId calleeEntry = new OpId(MOD_B, 11);
            OpId calleeCell = new OpId(MOD_B, 12);
            OpId calleeAlloc = new OpId(MOD_B, 13);
            OpId calleeReturn = new OpId(MOD_B, 14);
            BlockId calleeBody = new BlockId(1);
            LoweredModuleUnit calleeUnit = dynamicOracleAsyncCallee(calleeEntry, calleeCell,
                calleeAlloc, calleeReturn, argValue, calleeBody);
            StructuredBodyTable calleeTable = dynamicOracleAsyncCalleeTable(calleeBody,
                calleeAlloc, calleeReturn);
            LoweredModuleUnit caller = dynamicOracleAsyncCaller(
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG, owner),
                new AsyncTokenId.Canonical(callerToken, AsyncTokenOwner.DEAL_BODY_TASK),
                callee, constOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable callerTable = dynamicOracleAsyncTable(bodyBlock, constOp,
                startOp, awaitOp, allocOp, returnOp);
            ExecutableLoweredProject project = dynamicOracleProject(calleeUnit, caller);
            Map<ModuleId, StructuredBodyTable> tables = Map.of(MOD, callerTable, MOD_B,
                calleeTable);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(project, tables,
                null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the " + label + " dynamic ASYNC_START run succeeds");
            check(oracleSucceeded(run, startOp, "tok:" + callerToken + ":DEAL_BODY_TASK"),
                "the " + label + " ASYNC_START publishes its caller token");
            check(oracleSucceeded(run, calleeEntry, "tok:11:DEAL_BODY_TASK"),
                "the " + label + " callee async entry publishes its canonical token");
            check(oracleSucceeded(run, calleeCell, "int:7"),
                "the " + label + " callee task runs the callee-unit FUNCTION_RETURN (int:7)");
            check(!oracleTouched(run, taskCell)
                    && oracleBoundarySuccesses(run, caller, BoundaryKind.FUNCTION_RETURN) == 0,
                "the " + label + " resolution executes zero caller-side return cells");
            check(oracleBoundarySuccesses(run, calleeUnit, BoundaryKind.FUNCTION_RETURN) == 1
                    && oracleBoundarySuccesses(run, caller,
                        BoundaryKind.ASYNC_COMPLETION) == 1,
                "the " + label + " run executes one callee FUNCTION_RETURN and one caller "
                    + "ASYNC_COMPLETION");
            check(oracleSucceeded(run, awaitOp, "int:7"),
                "the " + label + " AWAIT completes through the canonical referent (int:7)");
        }
    }

    private static void testDynamicAdapterOracleExecution() {
        System.out.println("-- Oracle execution: adapter-resolved dynamic CALL and ASYNC_START --");

        // CALL — the D15 source resolution fixes the execution class per the
        // source binding; each class executes exactly the selected recorded cell.
        {
            // LoweredBody source → DEAL_BODY: the source body's RETURN executes the
            // recorded FUNCTION_RETURN cell.
            ValueId closureResult = new ValueId(61);
            ValueId adaptResult = new ValueId(62);
            ValueId callee = new ValueId(63);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealCell = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId callOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId callResult = nextValue();
            BlockId bodyBlock = new BlockId(5);
            LoweredModuleUnit unit = dynamicOracleAdapterCaller(
                new FunctionExecutionBinding.LoweredBody(new FunctionId(2), bodyBlock),
                SIG, SIG, closureResult, adaptResult, callee, constOp, closureOp, adaptOp,
                paramBoundary, dealCell, hostCell, externalCell, allocOp, returnOp, callOp,
                argValue, callResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterCallTable(bodyBlock, constOp,
                closureOp, adaptOp, callOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter CALL with a LoweredBody source run succeeds");
            check(oracleTouched(run, closureOp) && oracleTouched(run, adaptOp),
                "the D15 setup runs CLOSURE_NEW then FUNCTION_ADAPT before the call");
            check(oracleSucceeded(run, dealCell, "int:7"),
                "the adapter DEAL-body resolution executes the recorded FUNCTION_RETURN "
                    + "cell (int:7)");
            check(oracleSucceeded(run, callOp, "int:7"),
                "the adapter DEAL-body CALL terminal records the checked value");
            check(!oracleTouched(run, hostCell) && !oracleTouched(run, externalCell),
                "the adapter DEAL-body resolution executes exactly the selected cell");
        }
        {
            // HostFunction source → HOST: the call op executes the recorded
            // HOST_TO_DEAL cell.
            ValueId closureResult = new ValueId(64);
            ValueId adaptResult = new ValueId(65);
            ValueId callee = new ValueId(66);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealCell = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId callOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId callResult = nextValue();
            BlockId bodyBlock = new BlockId(6);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public SyncOutcome call(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
                    check(MOD.equals(module) && "f".equals(export)
                            && SIG.equals(descriptor) && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7,
                        "the adapter HOST resolution forwards the host call with the "
                            + "leading source argument");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAdapterCaller(
                new FunctionExecutionBinding.HostFunction(MOD, "f", SIG),
                SIG, SIG, closureResult, adaptResult, callee, constOp, closureOp, adaptOp,
                paramBoundary, dealCell, hostCell, externalCell, allocOp, returnOp, callOp,
                argValue, callResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterCallTable(bodyBlock, constOp,
                closureOp, adaptOp, callOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter CALL with a HostFunction source run succeeds");
            check(oracleSucceeded(run, hostCell, "int:9"),
                "the adapter HOST resolution executes the recorded HOST_TO_DEAL cell "
                    + "(int:9)");
            check(oracleSucceeded(run, callOp, "int:9"),
                "the adapter HOST CALL terminal records the checked value");
            check(!oracleTouched(run, dealCell) && !oracleTouched(run, externalCell),
                "the adapter HOST resolution executes exactly the selected cell");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.HOST_CALL,
                    "mod.a.f")
                    && oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.HOST_RETURN,
                        "mod.a.f=int:9"),
                "the adapter HOST resolution records the ordered host effects");
        }
        {
            // HostFunctionValue source → HOST: the materializing-boundary
            // correlation names the host export.
            ValueId closureResult = new ValueId(67);
            ValueId adaptResult = new ValueId(68);
            ValueId callee = new ValueId(69);
            OpId materializing = new OpId(MOD, 700);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealCell = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId callOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId callResult = nextValue();
            BlockId bodyBlock = new BlockId(7);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public SyncOutcome call(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
                    check(MOD.equals(module) && "@value#700".equals(export)
                            && SIG.equals(descriptor) && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7,
                        "the adapter HostFunctionValue resolution forwards the host call "
                            + "under the materializing-boundary correlation export");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAdapterCaller(
                new FunctionExecutionBinding.HostFunctionValue(MOD, materializing, SIG),
                SIG, SIG, closureResult, adaptResult, callee, constOp, closureOp, adaptOp,
                paramBoundary, dealCell, hostCell, externalCell, allocOp, returnOp, callOp,
                argValue, callResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterCallTable(bodyBlock, constOp,
                closureOp, adaptOp, callOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter CALL with a HostFunctionValue source run succeeds");
            check(oracleSucceeded(run, hostCell, "int:9"),
                "the adapter HostFunctionValue resolution executes the recorded "
                    + "HOST_TO_DEAL cell (int:9)");
            check(oracleSucceeded(run, callOp, "int:9"),
                "the adapter HostFunctionValue CALL terminal records the checked value");
            check(!oracleTouched(run, dealCell) && !oracleTouched(run, externalCell),
                "the adapter HostFunctionValue resolution executes exactly the selected "
                    + "cell");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.HOST_CALL,
                    "mod.a.@value#700"),
                "the adapter HostFunctionValue resolution records the correlation export "
                    + "effect");
        }
        {
            // ExternalFunction (RETAINED_ABI) source → EXTERNAL: the call op executes
            // the recorded EXTERNAL_RETURN cell.
            ValueId closureResult = new ValueId(70);
            ValueId adaptResult = new ValueId(71);
            ValueId callee = new ValueId(72);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealCell = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId callOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId callResult = nextValue();
            BlockId bodyBlock = new BlockId(8);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public SyncOutcome call(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
                    check(MOD_B.equals(module) && "f".equals(export)
                            && SIG.equals(descriptor) && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7,
                        "the adapter EXTERNAL resolution forwards the retained-ABI host "
                            + "call with the leading source argument");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAdapterCaller(
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG,
                    ExternalExecutionOwner.RETAINED_ABI),
                SIG, SIG, closureResult, adaptResult, callee, constOp, closureOp, adaptOp,
                paramBoundary, dealCell, hostCell, externalCell, allocOp, returnOp, callOp,
                argValue, callResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterCallTable(bodyBlock, constOp,
                closureOp, adaptOp, callOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter CALL with a retained-ABI ExternalFunction source run succeeds");
            check(oracleSucceeded(run, externalCell, "int:9"),
                "the adapter EXTERNAL resolution executes the recorded EXTERNAL_RETURN "
                    + "cell (int:9)");
            check(oracleSucceeded(run, callOp, "int:9"),
                "the adapter EXTERNAL CALL terminal records the checked value");
            check(!oracleTouched(run, dealCell) && !oracleTouched(run, hostCell),
                "the adapter EXTERNAL resolution executes exactly the selected cell");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.HOST_CALL,
                    "mod.b.f"),
                "the adapter EXTERNAL resolution records the retained-ABI host effect");
        }
        {
            // ExternalFunction (SHARED_BODY) source → SHARED_BODY: zero caller-side
            // cells; the callee unit's sync EXTERNAL_ENTRY runs its EXTERNAL_RETURN.
            ValueId closureResult = new ValueId(73);
            ValueId adaptResult = new ValueId(74);
            ValueId callee = new ValueId(75);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId dealCell = nextOpId();
            OpId hostCell = nextOpId();
            OpId externalCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId callOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId callResult = nextValue();
            BlockId bodyBlock = new BlockId(9);
            OpId calleeEntry = new OpId(MOD_B, 21);
            OpId calleeCell = new OpId(MOD_B, 22);
            OpId calleeAlloc = new OpId(MOD_B, 23);
            OpId calleeReturn = new OpId(MOD_B, 24);
            BlockId calleeBody = new BlockId(1);
            LoweredModuleUnit calleeUnit = dynamicOracleSyncCallee(calleeEntry, calleeCell,
                calleeAlloc, calleeReturn, argValue, calleeBody);
            StructuredBodyTable calleeTable = dynamicOracleAsyncCalleeTable(calleeBody,
                calleeAlloc, calleeReturn);
            LoweredModuleUnit caller = dynamicOracleAdapterCaller(
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG,
                    ExternalExecutionOwner.SHARED_BODY),
                SIG, SIG, closureResult, adaptResult, callee, constOp, closureOp, adaptOp,
                paramBoundary, dealCell, hostCell, externalCell, allocOp, returnOp, callOp,
                argValue, callResult, bodyBlock);
            StructuredBodyTable callerTable = dynamicOracleAdapterCallTable(bodyBlock,
                constOp, closureOp, adaptOp, callOp, allocOp, returnOp);
            ExecutableLoweredProject project = dynamicOracleProject(calleeUnit, caller);
            Map<ModuleId, StructuredBodyTable> tables = Map.of(MOD, callerTable, MOD_B,
                calleeTable);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(project, tables,
                null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter CALL with a SHARED_BODY ExternalFunction source run succeeds");
            check(oracleSucceeded(run, calleeCell, "int:7"),
                "the adapter SHARED_BODY resolution runs the callee EXTERNAL_RETURN "
                    + "(int:7)");
            check(oracleSucceeded(run, callOp, "int:7"),
                "the adapter SHARED_BODY CALL terminal records the value without "
                    + "re-checking");
            check(!oracleTouched(run, dealCell) && !oracleTouched(run, hostCell)
                    && !oracleTouched(run, externalCell),
                "the adapter SHARED_BODY resolution executes zero caller-side return "
                    + "cells");
        }

        // ASYNC_START — the same D15 setup; each source class executes its own
        // terminal with zero caller-side return cells outside the DEAL-body
        // resolution's recorded task cell.
        {
            // LoweredBody source → DEAL_BODY: the task body's RETURN executes the
            // recorded FUNCTION_RETURN task cell.
            ValueId closureResult = new ValueId(76);
            ValueId adaptResult = new ValueId(77);
            ValueId callee = new ValueId(78);
            AsyncTokenId token = new AsyncTokenId.Canonical(911,
                AsyncTokenOwner.DEAL_BODY_TASK);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(10);
            LoweredModuleUnit unit = dynamicOracleAdapterAsyncCaller(
                new FunctionExecutionBinding.LoweredBody(new FunctionId(2), bodyBlock),
                SIG, SIG, token, closureResult, adaptResult, callee, constOp, closureOp,
                adaptOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterAsyncTable(bodyBlock, constOp,
                closureOp, adaptOp, startOp, awaitOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter ASYNC_START with a LoweredBody source run succeeds");
            check(oracleSucceeded(run, startOp, "tok:911:DEAL_BODY_TASK"),
                "the adapter DEAL-body ASYNC_START publishes its canonical token");
            check(oracleSucceeded(run, taskCell, "int:7"),
                "the adapter DEAL-body resolution executes the recorded FUNCTION_RETURN "
                    + "task cell (int:7)");
            check(oracleBoundarySuccesses(run, unit, BoundaryKind.FUNCTION_RETURN) == 1
                    && oracleBoundarySuccesses(run, unit,
                        BoundaryKind.ASYNC_COMPLETION) == 1,
                "the adapter DEAL-body resolution executes exactly the recorded task cell "
                    + "plus one ASYNC_COMPLETION");
            check(oracleSucceeded(run, awaitOp, "int:7"),
                "the adapter DEAL-body AWAIT completes through the recorded task cell "
                    + "(int:7)");
        }
        {
            // HostFunction source → HOST: startAsync/completeAsync with the derived
            // label; zero caller-side return cells.
            ValueId closureResult = new ValueId(79);
            ValueId adaptResult = new ValueId(80);
            ValueId callee = new ValueId(81);
            AsyncTokenId token = new AsyncTokenId.Canonical(912,
                AsyncTokenOwner.HOST_OPERATION);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(11);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public String startAsync(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args,
                        String operationLabel) {
                    check(MOD.equals(module) && "f".equals(export) && SIG.equals(descriptor)
                            && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7
                            && "mod.a.f".equals(operationLabel),
                        "the adapter HOST resolution derives the operation label mod.a.f "
                            + "and starts with the leading source argument");
                    return operationLabel;
                }

                @Override
                public SyncOutcome completeAsync(String operationLabel) {
                    check("mod.a.f".equals(operationLabel),
                        "the adapter HOST AWAIT completes the derived operation label");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAdapterAsyncCaller(
                new FunctionExecutionBinding.HostFunction(MOD, "f", SIG),
                SIG, SIG, token, closureResult, adaptResult, callee, constOp, closureOp,
                adaptOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterAsyncTable(bodyBlock, constOp,
                closureOp, adaptOp, startOp, awaitOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter ASYNC_START with a HostFunction source run succeeds");
            check(oracleSucceeded(run, startOp, "tok:912:HOST_OPERATION"),
                "the adapter HOST ASYNC_START publishes its canonical token");
            check(oracleSucceeded(run, awaitOp, "int:9"),
                "the adapter HOST AWAIT completes the host operation (int:9)");
            check(!oracleTouched(run, taskCell)
                    && oracleBoundarySuccesses(run, unit, BoundaryKind.FUNCTION_RETURN) == 0,
                "the adapter HOST resolution executes zero caller-side return cells");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP,
                    "mod.a.f")
                    && oracleEffect(run,
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_COMPLETE_RETURN,
                        "mod.a.f=int:9"),
                "the adapter HOST resolution records the ordered async host effects");
        }
        {
            // HostFunctionValue source → HOST: the derived label collapses the
            // materializing-boundary correlation.
            ValueId closureResult = new ValueId(82);
            ValueId adaptResult = new ValueId(83);
            ValueId callee = new ValueId(84);
            OpId materializing = new OpId(MOD, 701);
            AsyncTokenId token = new AsyncTokenId.Canonical(913,
                AsyncTokenOwner.HOST_OPERATION);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(12);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public String startAsync(ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args,
                        String operationLabel) {
                    check(MOD.equals(module) && "@value#701".equals(export)
                            && SIG.equals(descriptor) && args.size() == 1
                            && ((SemanticOracle.Value.IntValue) args.get(0)).value() == 7
                            && "mod.a.@value".equals(operationLabel),
                        "the adapter HostFunctionValue resolution derives the operation "
                            + "label mod.a.@value and starts under the correlation export");
                    return operationLabel;
                }

                @Override
                public SyncOutcome completeAsync(String operationLabel) {
                    check("mod.a.@value".equals(operationLabel),
                        "the adapter HostFunctionValue AWAIT completes the derived "
                            + "operation label");
                    return new SyncOutcome.Returned(new SemanticOracle.Value.IntValue(9));
                }
            };
            LoweredModuleUnit unit = dynamicOracleAdapterAsyncCaller(
                new FunctionExecutionBinding.HostFunctionValue(MOD, materializing, SIG),
                SIG, SIG, token, closureResult, adaptResult, callee, constOp, closureOp,
                adaptOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable table = dynamicOracleAdapterAsyncTable(bodyBlock, constOp,
                closureOp, adaptOp, startOp, awaitOp, allocOp, returnOp);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(unit, table,
                responder);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter ASYNC_START with a HostFunctionValue source run succeeds");
            check(oracleSucceeded(run, startOp, "tok:913:HOST_OPERATION"),
                "the adapter HostFunctionValue ASYNC_START publishes its canonical token");
            check(oracleSucceeded(run, awaitOp, "int:9"),
                "the adapter HostFunctionValue AWAIT completes the host operation (int:9)");
            check(!oracleTouched(run, taskCell)
                    && oracleBoundarySuccesses(run, unit, BoundaryKind.FUNCTION_RETURN) == 0,
                "the adapter HostFunctionValue resolution executes zero caller-side "
                    + "return cells");
            check(oracleEffect(run, SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP,
                    "mod.a.@value"),
                "the adapter HostFunctionValue resolution records the derived label effect");
        }
        for (ExternalExecutionOwner owner : List.of(ExternalExecutionOwner.RETAINED_ABI,
                ExternalExecutionOwner.SHARED_BODY)) {
            // ExternalFunction source → EXTERNAL/SHARED_BODY: the callee unit's async
            // EXTERNAL_ENTRY owns the canonical token; the caller AWAIT completes
            // through the dynamicReferents linkage.
            String label = owner == ExternalExecutionOwner.RETAINED_ABI
                ? "EXTERNAL (retained-ABI)" : "SHARED_BODY";
            long callerToken = owner == ExternalExecutionOwner.RETAINED_ABI ? 914 : 915;
            ValueId closureResult = new ValueId(85);
            ValueId adaptResult = new ValueId(86);
            ValueId callee = new ValueId(87);
            AsyncTokenId token = new AsyncTokenId.Canonical(callerToken,
                AsyncTokenOwner.DEAL_BODY_TASK);
            OpId constOp = nextOpId();
            OpId closureOp = nextOpId();
            OpId adaptOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId taskCell = nextOpId();
            OpId allocOp = nextOpId();
            OpId returnOp = nextOpId();
            OpId startOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId awaitOp = nextOpId();
            ValueId argValue = nextValue();
            ValueId awaitResult = nextValue();
            BlockId bodyBlock = new BlockId(13);
            OpId calleeEntry = new OpId(MOD_B, 11);
            OpId calleeCell = new OpId(MOD_B, 12);
            OpId calleeAlloc = new OpId(MOD_B, 13);
            OpId calleeReturn = new OpId(MOD_B, 14);
            BlockId calleeBody = new BlockId(1);
            LoweredModuleUnit calleeUnit = dynamicOracleAsyncCallee(calleeEntry, calleeCell,
                calleeAlloc, calleeReturn, argValue, calleeBody);
            StructuredBodyTable calleeTable = dynamicOracleAsyncCalleeTable(calleeBody,
                calleeAlloc, calleeReturn);
            LoweredModuleUnit caller = dynamicOracleAdapterAsyncCaller(
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG, owner),
                SIG, SIG, token, closureResult, adaptResult, callee, constOp, closureOp,
                adaptOp, paramBoundary, taskCell, allocOp, returnOp, startOp,
                completionBoundary, awaitOp, argValue, awaitResult, bodyBlock);
            StructuredBodyTable callerTable = dynamicOracleAdapterAsyncTable(bodyBlock,
                constOp, closureOp, adaptOp, startOp, awaitOp, allocOp, returnOp);
            ExecutableLoweredProject project = dynamicOracleProject(calleeUnit, caller);
            Map<ModuleId, StructuredBodyTable> tables = Map.of(MOD, callerTable, MOD_B,
                calleeTable);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(project, tables,
                null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the adapter ASYNC_START with a " + label + " ExternalFunction source "
                    + "run succeeds");
            check(oracleSucceeded(run, startOp, "tok:" + callerToken + ":DEAL_BODY_TASK"),
                "the adapter " + label + " ASYNC_START publishes its caller token");
            check(oracleSucceeded(run, calleeEntry, "tok:11:DEAL_BODY_TASK"),
                "the adapter " + label + " callee async entry publishes its canonical "
                    + "token");
            check(oracleSucceeded(run, calleeCell, "int:7"),
                "the adapter " + label + " callee task runs the callee-unit "
                    + "FUNCTION_RETURN (int:7)");
            check(!oracleTouched(run, taskCell)
                    && oracleBoundarySuccesses(run, caller, BoundaryKind.FUNCTION_RETURN) == 0,
                "the adapter " + label + " resolution executes zero caller-side return "
                    + "cells");
            check(oracleSucceeded(run, awaitOp, "int:7"),
                "the adapter " + label + " AWAIT completes through the canonical referent "
                    + "(int:7)");
        }
    }

    // =========================================================================
    // Entry point
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Dynamic Resolution IR Test (ISSUE-0531) ===\n");

        testConstruction();
        testProtocol();
        testCanonicalRendering();
        testDynamicCallPositive();
        testDynamicCallPositiveProject();
        testDynamicAsyncPositive();
        testDynamicCallNegatives();
        testDynamicAsyncNegatives();
        testHostFunctionValueClosure();
        testDynamicOracleExecution();
        testDynamicAsyncOracleExecution();
        testDynamicAdapterOracleExecution();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
