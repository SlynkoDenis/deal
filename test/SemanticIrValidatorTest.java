package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.CapabilityRequirementCatalog;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.DeleteTargetKind;
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
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.NullableSide;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
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
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Verifies the ISSUE-0286 closed 14-condition {@link SemanticIrValidator}
 * on both surfaces — the typed record surface
 * ({@link SemanticIrValidator#validate(LoweredModuleUnit,
 * SemanticIrValidator.ComparisonFacts)} /
 * {@link SemanticIrValidator#validate(ExecutableLoweredProject,
 * SemanticIrValidator.ComparisonFacts)}) and the canonical-JSON text
 * surface ({@link SemanticIrValidator#validateText(String,
 * SemanticIrValidator.ComparisonFacts)}, the pinned invalid-IR injection
 * route).
 *
 * <p>Corpus:</p>
 * <ol>
 *   <li>The pinned 14-rule enumeration order and the E6005 surface (code,
 *       phase, registry-instantiated message carrying the detail).</li>
 *   <li>The positive corpus: one passing synthetic unit per
 *       {@link SemanticOpKind} (55), every closed enum value in a passing
 *       unit (3 unary selectors, 42 binary selectors, 4 call modes,
 *       3 async sources, 2 parameter boundary modes, 4 index modes,
 *       2 iteration modes, 6 control selectors, 3 capture modes,
 *       2 realization forms, 25 boundary kinds, 24 policy names,
 *       21 stdlib ids), and each of the 23 construct rows carrying a
 *       required common form recorded in a passing unit's
 *       {@code constructCoverage} with at least one produced op of a
 *       mapped kind.</li>
 *   <li>Typed/text equivalence: the same validation result through both
 *       surfaces for the corpus units and for typed negatives.</li>
 *   <li>The negative corpus: each of the 14 rules asserted exactly once
 *       per defect class through T5's E6005 payload — the raw-name
 *       negatives (R-ENUM open policy, R-ENUM reserved boundary name,
 *       R-PRIVATE-STEP op kind, the out-of-set R-ENUM selector fixture,
 *       R-PROFILE's profile-string fixture and the cross-unit
 *       project-level profile fixture) via {@code validateText} over the
 *       text produced by the validator's serializer with exactly one leaf
 *       value substituted and the contract digest recomputed through T3,
 *       the remainder via typed construction.</li>
 *   <li>Deterministic first-failure order (the S6 rule enumeration order
 *       across independent defects) and repeated-run determinism.</li>
 *   <li>Lock pins (ISSUE-0368, retargeted by K7): {@code TIME_NOW_MILLIS}
 *       is the 21st closed {@link StdlibFunctionId} member
 *       ({@code RESERVED_NAMES} empty; an out-of-set selector name is
 *       R-ENUM), and a unit claiming {@code STDLIB_TIME_CONFLICT}
 *       — the empty-evidence routing marker — fails R-CAPABILITY
 *       on both the typed and the text surface, so no common-lowering
 *       path admits it.</li>
 * </ol>
 */
public class SemanticIrValidatorTest {

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
    private static final RuntimeDescriptor BOOL = RuntimeDescriptor.Boolean.INSTANCE;
    private static final RuntimeDescriptor STR = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor TBL = RuntimeDescriptor.Table.INSTANCE;
    private static final RuntimeDescriptor.Func SIG_II = new RuntimeDescriptor.Func(List.of(INT), INT);
    private static final RuntimeDescriptor.Func SIG_II_ASYNC =
        new RuntimeDescriptor.Func(List.of(INT), INT, true);
    private static final RuntimeDescriptor.Func SIG_FF =
        new RuntimeDescriptor.Func(List.of(SIG_II), SIG_II);

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
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        return opWith(nextOpId(), kind, payload, result, resultType, policy, parent);
    }

    private static SemanticOp boundary(BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent) {
        return boundaryWith(nextOpId(), kind, descriptor, policy, parent);
    }

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, nextValue(),
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    private static LoweredModuleUnit unit(String module, Set<SemanticCapability> caps,
            Map<ConstructKind, List<SemanticOpKind>> coverage,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, new ModuleId(module), IFACE, LCH, caps, coverage,
            Map.of(), Map.of(), new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            bindings, ops);
    }

    private static LoweredModuleUnit unit(Set<SemanticCapability> caps,
            Map<ConstructKind, List<SemanticOpKind>> coverage,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return unit("mod.a", caps, coverage, bindings, ops);
    }

    private static LoweredModuleUnit unit(List<SemanticOp> ops) {
        return unit(Set.of(), Map.of(), Map.of(), ops);
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
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            rule + " phase is BACKEND_LOWERING");
        check("error".equals(d.severity()), rule + " severity is error");
        String message = d.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            rule + " is named as the validator rule (exactly one rule per fixture); got \""
                + message + "\"");
        check(message.contains("deal.semantic-ir/1") && message.contains("mod"),
            rule + " message carries the detail fields");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \"" + message + "\"");
        }
    }

    private static void track(Set<String> tracker, String name) {
        tracker.add(name);
    }

    // =========================================================================
    // 1. Pinned rule set and E6005 surface
    // =========================================================================

    private static void testRuleSet() {
        System.out.println("-- Pinned 14-condition rule set --");

        check(SemanticIrValidator.RULES.equals(List.of(
                "R-COVERAGE", "R-ENUM", "R-CAPABILITY", "R-POLICY-KIND", "R-BOUNDARY-TRIPLE",
                "R-ELIDED-PLACEMENT", "R-FUNCTION-BINDING", "R-EXTERNAL-ENTRY", "R-ALIAS-CYCLE",
                "R-TOKEN-REUSE", "R-PRIVATE-STEP", "R-RESERVED-NAME", "R-DIGEST", "R-PROFILE")),
            "RULES is exactly the closed 14-condition list in the S6 enumeration order; got "
                + SemanticIrValidator.RULES);
        check(SemanticIrValidator.RULES.size() == 14,
            "exactly 14 rules (nothing more, nothing less)");
        check(SemanticIrValidator.RULES.equals(List.of(
                SemanticIrValidator.R_COVERAGE, SemanticIrValidator.R_ENUM,
                SemanticIrValidator.R_CAPABILITY, SemanticIrValidator.R_POLICY_KIND,
                SemanticIrValidator.R_BOUNDARY_TRIPLE, SemanticIrValidator.R_ELIDED_PLACEMENT,
                SemanticIrValidator.R_FUNCTION_BINDING, SemanticIrValidator.R_EXTERNAL_ENTRY,
                SemanticIrValidator.R_ALIAS_CYCLE, SemanticIrValidator.R_TOKEN_REUSE,
                SemanticIrValidator.R_PRIVATE_STEP, SemanticIrValidator.R_RESERVED_NAME,
                SemanticIrValidator.R_DIGEST, SemanticIrValidator.R_PROFILE)),
            "the rule constants match the enumeration order");

        // The E6005 surface: a failing validation returns exactly one
        // registry-constructed diagnostic carrying the detail.
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validate(
            unit(Set.of(SemanticCapability.CALLS), Map.of(), Map.of(),
                List.of(constOp())), FACTS);
        assertE6005(failure, "R-CAPABILITY", "CALLS", "SemanticIrValidator");
        check(failure.get().message().contains("validatorRule R-CAPABILITY"),
            "the payload names the failing rule through T5's detail construction");
    }

    private static SemanticOp constOp() {
        return op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    // =========================================================================
    // 2. Positive corpus: 55 op-kind units + enum sweep + construct rows
    // =========================================================================

    private static void testPositiveKindCorpus() {
        System.out.println("-- Positive corpus: one passing unit per SemanticOpKind (55) --");

        Map<String, LoweredModuleUnit> units = buildKindUnits();
        check(units.size() == 55, "exactly 55 kind units built; got " + units.size());
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            LoweredModuleUnit unit = units.get(kind.name());
            check(unit != null, "a unit exists for kind " + kind.name());
            if (unit != null) {
                assertPass(SemanticIrValidator.validate(unit, FACTS),
                    "kind unit " + kind.name());
                assertPass(SemanticIrValidator.validateText(
                        SemanticIrValidator.toUnitText(unit), FACTS),
                    "kind unit " + kind.name() + " through the text surface");
            }
        }
    }

    private static Map<String, LoweredModuleUnit> buildKindUnits() {
        Map<String, LoweredModuleUnit> units = new LinkedHashMap<>();

        // CONST
        units.put("CONST", unit(List.of(constOp())));

        // UNARY
        units.put("UNARY", unit(List.of(
            op(SemanticOpKind.UNARY, new KindPayload.UnaryPayload(UnarySelector.BOOL_NOT),
                nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // BINARY
        units.put("BINARY", unit(List.of(
            op(SemanticOpKind.BINARY,
                new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null))));

        // STRING_CONCAT
        units.put("STRING_CONCAT", unit(List.of(
            op(SemanticOpKind.STRING_CONCAT,
                new KindPayload.StringConcatPayload(List.of(nextValue())),
                nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // ARRAY_NEW (with its ARRAY_LITERAL_ELEMENT boundary child)
        {
            OpId arrayOp = nextOpId();
            OpId elementBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
                FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, arrayOp));
            ops.add(opWith(arrayOp, SemanticOpKind.ARRAY_NEW,
                new KindPayload.ArrayNewPayload(INT, List.of(nextValue()),
                    List.of(elementBoundary)),
                nextValue(), new RuntimeDescriptor.Array(INT),
                FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("ARRAY_NEW", unit(ops));
        }

        // TABLE_NEW
        units.put("TABLE_NEW", unit(List.of(
            op(SemanticOpKind.TABLE_NEW,
                new KindPayload.TableNewPayload(
                    List.of(new KindPayload.TableEntry("k", nextValue()))),
                nextValue(), TBL, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // ARRAY_LENGTH
        units.put("ARRAY_LENGTH", unit(List.of(
            op(SemanticOpKind.ARRAY_LENGTH, new KindPayload.ArrayLengthPayload(nextValue()),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // MEMBER_READ / MEMBER_WRITE / MEMBER_DELETE
        units.put("MEMBER_READ", unit(List.of(
            op(SemanticOpKind.MEMBER_READ, new KindPayload.MemberReadPayload(nextValue(), "k"),
                nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("MEMBER_WRITE", unit(List.of(
            op(SemanticOpKind.MEMBER_WRITE,
                new KindPayload.MemberWritePayload(nextValue(), "k", nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("MEMBER_DELETE", unit(List.of(
            op(SemanticOpKind.MEMBER_DELETE,
                new KindPayload.MemberDeletePayload(nextValue(), "k"),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // INDEX_NORMALIZE
        units.put("INDEX_NORMALIZE", unit(List.of(
            op(SemanticOpKind.INDEX_NORMALIZE,
                new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_READ, nextValue(),
                    nextValue()),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // INDEX_READ (with its ARRAY_ELEMENT_READ boundary child)
        {
            OpId indexReadOp = nextOpId();
            OpId elementBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_ELEMENT_READ, INT,
                FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, indexReadOp));
            ops.add(opWith(indexReadOp, SemanticOpKind.INDEX_READ,
                new KindPayload.IndexReadPayload(nextValue(), nextValue(), elementBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("INDEX_READ", unit(ops));
        }

        // INDEX_WRITE / INDEX_DELETE
        units.put("INDEX_WRITE", unit(List.of(
            op(SemanticOpKind.INDEX_WRITE,
                new KindPayload.IndexWritePayload(nextValue(), nextValue(), nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("INDEX_DELETE", unit(List.of(
            op(SemanticOpKind.INDEX_DELETE,
                new KindPayload.IndexDeletePayload(nextValue(), nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // OPTIONAL_READ
        units.put("OPTIONAL_READ", unit(List.of(
            op(SemanticOpKind.OPTIONAL_READ,
                new KindPayload.OptionalReadPayload(nextValue(), true, INT),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // HAS_FIELD
        units.put("HAS_FIELD", unit(List.of(
            op(SemanticOpKind.HAS_FIELD, new KindPayload.HasFieldPayload(nextValue(), "k"),
                nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // BOUNDARY (core descriptor-kind-rule cell)
        units.put("BOUNDARY", unit(List.of(
            boundary(BoundaryKind.VARIABLE_DECLARATION, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                null))));

        // BINDING_ALLOC / BINDING_INIT / BINDING_LOAD / BINDING_STORE
        units.put("BINDING_ALLOC", unit(List.of(
            op(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(new BindingId(1), new BlockId(0), false,
                    BindingCellKind.DIRECT, 0),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("BINDING_INIT", unit(List.of(
            op(SemanticOpKind.BINDING_INIT,
                new KindPayload.BindingInitPayload(new BindingId(1), 0, nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("BINDING_LOAD", unit(List.of(
            op(SemanticOpKind.BINDING_LOAD,
                new KindPayload.BindingLoadPayload(new BindingId(1), 0),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("BINDING_STORE", unit(List.of(
            op(SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(1), 0, nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // RECURSIVE_GROUP_INIT
        units.put("RECURSIVE_GROUP_INIT", unit(List.of(
            op(SemanticOpKind.RECURSIVE_GROUP_INIT,
                new KindPayload.RecursiveGroupInitPayload(List.of(new BindingId(1)),
                    List.of(new FunctionId(1))),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // CLOSURE_NEW (function-typed result with its registered binding)
        {
            FunctionId function = new FunctionId(1);
            FunctionExecutionBinding.LoweredBody binding =
                new FunctionExecutionBinding.LoweredBody(function, new BlockId(1));
            ValueId result = new ValueId(2300);
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
                new FunctionAllocationIdentity(2300), binding);
            units.put("CLOSURE_NEW", unit(Set.of(), Map.of(), bindings, List.of(
                op(SemanticOpKind.CLOSURE_NEW,
                    new KindPayload.ClosureNewPayload(function, SIG_II, List.of(), binding),
                    result, SIG_II, FailurePolicyId.NO_DEAL_FAILURE, null))));
        }

        // FUNCTION_ADAPT (function-typed result with its registered binding)
        {
            OpId adaptOp = nextOpId();
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(adaptOp, CaptureMode.VALUE,
                    new AdaptSourceRef.Value(new ValueId(9)), SIG_II, SIG_II);
            ValueId result = new ValueId(2400);
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
                new FunctionAllocationIdentity(2400), binding);
            units.put("FUNCTION_ADAPT", unit(Set.of(), Map.of(), bindings, List.of(
                op(SemanticOpKind.FUNCTION_ADAPT,
                    new KindPayload.FunctionAdaptPayload(SIG_II, SIG_II, CaptureMode.VALUE,
                        new AdaptSourceRef.Value(new ValueId(9)), null),
                    result, SIG_II, FailurePolicyId.NO_DEAL_FAILURE, null))));
        }

        // ASSIGN / DELETE (address chains without boundary children)
        units.put("ASSIGN", unit(List.of(
            op(SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(deal.semantic.ir.AssignTargetKind.VARIABLE,
                    List.of(nextOpId(), nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("DELETE", unit(List.of(
            op(SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                    List.of(nextOpId(), nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // CALL (DIRECT with parameter/return boundaries)
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, new BlockId(1), null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("CALL", unit(ops));
        }

        // EXTERNAL_ENTRY (sync)
        {
            OpId entryOp = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(returnBoundary, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), SIG_II, false,
                    returnBoundary, null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("EXTERNAL_ENTRY", unit(ops));
        }

        // CALLBACK_INVOKE
        {
            OpId callbackOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(new ValueId(9), SIG_II,
                    List.of(paramBoundary), returnBoundary),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("CALLBACK_INVOKE", unit(ops));
        }

        // INTRINSIC_CALL
        units.put("INTRINSIC_CALL", unit(List.of(
            op(SemanticOpKind.INTRINSIC_CALL,
                new KindPayload.IntrinsicCallPayload(IntrinsicKind.INT_CONVERT, nextValue()),
                nextValue(), INT, FailurePolicyId.INT_CONVERSION, null))));

        // STDLIB_CALL
        units.put("STDLIB_CALL", unit(List.of(
            op(SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(StdlibFunctionId.CONSOLE_LOG, List.of(),
                    SemanticCapability.STDLIB_SEMANTICS),
                nextValue(), RuntimeDescriptor.Null.INSTANCE,
                FailurePolicyId.INFRASTRUCTURE_ONLY, null))));

        // ASYNC_START (DEAL_BODY with parameter/return boundaries)
        {
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, returnBoundary, null, null),
                new AsyncTokenId.Canonical(1, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("ASYNC_START", unit(ops));
        }

        // AWAIT (with its ASYNC_COMPLETION boundary child)
        {
            OpId awaitOp = nextOpId();
            OpId completionBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitOp));
            ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(new AsyncTokenId.Canonical(1,
                    AsyncTokenOwner.DEAL_BODY_TASK), INT, completionBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            units.put("AWAIT", unit(ops));
        }

        // BRANCH / LOOP
        units.put("BRANCH", unit(List.of(
            op(SemanticOpKind.BRANCH,
                new KindPayload.BranchPayload(ControlSelector.IF, nextValue(), new BlockId(1),
                    new BlockId(2)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("LOOP", unit(List.of(
            op(SemanticOpKind.LOOP,
                new KindPayload.LoopPayload(ControlSelector.WHILE, null, nextValue(),
                    new BlockId(1), null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // FOR_EACH
        units.put("FOR_EACH", unit(List.of(
            op(SemanticOpKind.FOR_EACH,
                new KindPayload.ForEachPayload(IterationMode.ARRAY_VALUES, nextValue(),
                    new BindingId(1), 0, new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // TRY_CATCH / THROW
        units.put("TRY_CATCH", unit(List.of(
            op(SemanticOpKind.TRY_CATCH,
                new KindPayload.TryCatchPayload(new BlockId(1), new BindingId(1),
                    new BlockId(2)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("THROW", unit(List.of(
            op(SemanticOpKind.THROW, new KindPayload.ThrowPayload(nextValue()),
                null, null, FailurePolicyId.THROW_TRANSFER, null))));

        // RETURN
        units.put("RETURN", unit(List.of(
            op(SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, new FunctionId(1), nextOpId(), nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // BREAK / CONTINUE
        units.put("BREAK", unit(List.of(
            op(SemanticOpKind.BREAK, new KindPayload.BreakPayload(nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("CONTINUE", unit(List.of(
            op(SemanticOpKind.CONTINUE, new KindPayload.ContinuePayload(nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // DISCARD
        units.put("DISCARD", unit(List.of(
            op(SemanticOpKind.DISCARD, new KindPayload.DiscardPayload(nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // CLASS_DEFAULT
        units.put("CLASS_DEFAULT", unit(List.of(
            op(SemanticOpKind.CLASS_DEFAULT,
                new KindPayload.ClassDefaultPayload(new ClassId("mod.a", "C"), "f",
                    new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // CLASS_NEW (with a CLASS_LITERAL_FIELD boundary child)
        {
            ClassId classId = new ClassId("mod.a", "C");
            ClassLayout layout = new ClassLayout(classId,
                List.of(new ClassLayout.FieldLayout("f", INT, true, DefaultOwner.LOCAL)));
            OpId classNewOp = nextOpId();
            OpId fieldBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(fieldBoundary, BoundaryKind.CLASS_LITERAL_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(opWith(classNewOp, SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(classId, layout,
                    List.of(new KindPayload.ProvidedField("f", nextValue())),
                    DefaultOwner.LOCAL, List.of(), null,
                    List.of(new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_LITERAL_FIELD,
                        fieldBoundary))),
                nextValue(), new RuntimeDescriptor.Class(classId),
                FailurePolicyId.CLASS_CONSTRUCTION, null));
            units.put("CLASS_NEW", unit(ops));
        }

        // CLASS_FACTORY
        units.put("CLASS_FACTORY", unit(List.of(
            op(SemanticOpKind.CLASS_FACTORY,
                new KindPayload.ClassFactoryPayload(new ClassId("mod.a", "C"), List.of(),
                    nextOpId()),
                null, null, FailurePolicyId.CLASS_CONSTRUCTION, null))));

        // FIELD_READ / FIELD_WRITE / FIELD_DELETE
        units.put("FIELD_READ", unit(List.of(
            op(SemanticOpKind.FIELD_READ,
                new KindPayload.FieldReadPayload(nextValue(), new ClassId("mod.a", "C"), "f"),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("FIELD_WRITE", unit(List.of(
            op(SemanticOpKind.FIELD_WRITE,
                new KindPayload.FieldWritePayload(nextValue(), new ClassId("mod.a", "C"), "f",
                    nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("FIELD_DELETE", unit(List.of(
            op(SemanticOpKind.FIELD_DELETE,
                new KindPayload.FieldDeletePayload(nextValue(), new ClassId("mod.a", "C"), "f"),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // JSON_FROM_CLASS / JSON_TO_CLASS
        {
            ClassId classId = new ClassId("mod.a", "C");
            ClassLayout layout = new ClassLayout(classId, List.of());
            units.put("JSON_FROM_CLASS", unit(List.of(
                op(SemanticOpKind.JSON_FROM_CLASS,
                    new KindPayload.JsonFromClassPayload(layout, nextValue()),
                    nextValue(), RuntimeDescriptor.Null.INSTANCE,
                    FailurePolicyId.JSON_FROM_NULL, null))));
            units.put("JSON_TO_CLASS", unit(List.of(
                op(SemanticOpKind.JSON_TO_CLASS,
                    new KindPayload.JsonToClassPayload(nextValue(), layout),
                    nextValue(), STR, FailurePolicyId.JSON_TO_ERROR, null))));
        }

        // MODULE_INIT / MODULE_IMPORT
        units.put("MODULE_INIT", unit(List.of(
            op(SemanticOpKind.MODULE_INIT,
                new KindPayload.ModuleInitPayload(MOD, List.of(new ModuleId("dep")),
                    new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("MODULE_IMPORT", unit(List.of(
            op(SemanticOpKind.MODULE_IMPORT,
                new KindPayload.ModuleImportPayload("dep", new ModuleId("dep"),
                    ModuleImportKind.COMPILED),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // EXPORT_READ / EXPORT_PUBLISH
        units.put("EXPORT_READ", unit(List.of(
            op(SemanticOpKind.EXPORT_READ,
                new KindPayload.ExportReadPayload(new ModuleId("dep"), "x", INT, nextValue()),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))));
        units.put("EXPORT_PUBLISH", unit(List.of(
            op(SemanticOpKind.EXPORT_PUBLISH,
                new KindPayload.ExportPublishPayload(new ModuleId("dep"), "x", INT, nextValue()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        // ENTRY_INVOKE
        units.put("ENTRY_INVOKE", unit(List.of(
            op(SemanticOpKind.ENTRY_INVOKE,
                new KindPayload.EntryInvokePayload(new ModuleId("entry"), new FunctionId(0)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null))));

        return units;
    }

    // =========================================================================
    // Enum sweep: every closed enum value appears in a passing unit
    // =========================================================================

    private static void testEnumSweep() {
        System.out.println("-- Enum sweep: every closed value in a passing unit --");

        Set<String> unary = new LinkedHashSet<>();
        Set<String> binary = new LinkedHashSet<>();
        Set<String> callModes = new LinkedHashSet<>();
        Set<String> asyncSources = new LinkedHashSet<>();
        Set<String> paramModes = new LinkedHashSet<>();
        Set<String> indexModes = new LinkedHashSet<>();
        Set<String> iterationModes = new LinkedHashSet<>();
        Set<String> controlSelectors = new LinkedHashSet<>();
        Set<String> captureModes = new LinkedHashSet<>();
        Set<String> realizations = new LinkedHashSet<>();
        Set<String> boundaryKinds = new LinkedHashSet<>();
        Set<String> policies = new LinkedHashSet<>();
        Set<String> stdlibIds = new LinkedHashSet<>();

        // The 55 kind units already cover: BOOL_NOT, INT32_ADD, DIRECT,
        // DEAL_BODY, RUN, ARRAY_READ, ARRAY_VALUES, IF, WHILE, VALUE,
        // runtimeValidation, VARIABLE_DECLARATION, CLASS_LITERAL_FIELD,
        // FUNCTION_PARAMETER, FUNCTION_RETURN, ASYNC_COMPLETION,
        // ARRAY_LITERAL_ELEMENT, ARRAY_ELEMENT_READ, EXTERNAL_RETURN,
        // HOST_TO_DEAL, DEAL_TO_HOST, NO_DEAL_FAILURE, TYPE_DESCRIPTOR,
        // INT32_RESULT, INT_CONVERSION, INFRASTRUCTURE_ONLY,
        // ARRAY_ELEMENT_DESCRIPTOR, ARRAY_READ_INDEX_THEN_DESCRIPTOR,
        // THROW_TRANSFER, CLASS_CONSTRUCTION, JSON_FROM_NULL, JSON_TO_ERROR,
        // CONSOLE_LOG.
        track(unary, "BOOL_NOT");
        track(binary, "INT32_ADD");
        track(callModes, "DIRECT");
        track(asyncSources, "DEAL_BODY");
        track(paramModes, "RUN");
        track(indexModes, "ARRAY_READ");
        track(iterationModes, "ARRAY_VALUES");
        track(controlSelectors, "IF");
        track(controlSelectors, "WHILE");
        track(captureModes, "VALUE");
        track(realizations, "runtimeValidation");
        track(boundaryKinds, "VARIABLE_DECLARATION");
        track(boundaryKinds, "CLASS_LITERAL_FIELD");
        track(boundaryKinds, "FUNCTION_PARAMETER");
        track(boundaryKinds, "FUNCTION_RETURN");
        track(boundaryKinds, "ASYNC_COMPLETION");
        track(boundaryKinds, "ARRAY_LITERAL_ELEMENT");
        track(boundaryKinds, "ARRAY_ELEMENT_READ");
        track(boundaryKinds, "EXTERNAL_RETURN");
        track(boundaryKinds, "HOST_TO_DEAL");
        track(boundaryKinds, "DEAL_TO_HOST");
        track(policies, "ASYNC_COMPLETION");
        track(policies, "NO_DEAL_FAILURE");
        track(policies, "TYPE_DESCRIPTOR");
        track(policies, "INT32_RESULT");
        track(policies, "INT_CONVERSION");
        track(policies, "INFRASTRUCTURE_ONLY");
        track(policies, "ARRAY_ELEMENT_DESCRIPTOR");
        track(policies, "ARRAY_READ_INDEX_THEN_DESCRIPTOR");
        track(policies, "THROW_TRANSFER");
        track(policies, "CLASS_CONSTRUCTION");
        track(policies, "JSON_FROM_NULL");
        track(policies, "JSON_TO_ERROR");
        track(stdlibIds, "CONSOLE_LOG");

        // Unary selectors: INT32_NEG, NUMBER_NEG.
        passingSweep("unary INT32_NEG", List.of(
            op(SemanticOpKind.UNARY, new KindPayload.UnaryPayload(UnarySelector.INT32_NEG),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null)), unary, "INT32_NEG");
        passingSweep("unary NUMBER_NEG", List.of(
            op(SemanticOpKind.UNARY, new KindPayload.UnaryPayload(UnarySelector.NUMBER_NEG),
                nextValue(), RuntimeDescriptor.Number.INSTANCE, FailurePolicyId.NO_DEAL_FAILURE,
                null)), unary, "NUMBER_NEG");

        // Binary selectors: all 42 with their pinned selector policies.
        for (BinarySelector selector : BinarySelector.values()) {
            NullableSide side = selector.name().startsWith("NULLABLE") ? NullableSide.BOTH : null;
            RuntimeDescriptor inner = selector.name().startsWith("NULLABLE") ? INT : null;
            passingSweep("binary " + selector.name(), List.of(
                op(SemanticOpKind.BINARY,
                    new KindPayload.BinaryPayload(selector, inner, side),
                    nextValue(), INT, binaryPolicy(selector), null)), binary, selector.name());
            track(policies, binaryPolicy(selector).name());
        }

        // Call modes: INDIRECT, HOST, EXTERNAL (SHARED_BODY + RETAINED_ABI).
        {
            // INDIRECT → LoweredBody through functionBindings.
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings = Map.of(
                new FunctionAllocationIdentity(9),
                new FunctionExecutionBinding.LoweredBody(new FunctionId(1), new BlockId(1)));
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(9)),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("call mode INDIRECT", ops, bindings, callModes, "INDIRECT");
        }
        {
            // HOST.
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.HOST,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.HostFunction(
                        new ModuleId("host.a"), "f", SIG_II)),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("call mode HOST", ops, callModes, "HOST");
            track(policies, "HOST_PARAMETER");
            track(policies, "HOST_SYNC_RETURN");
        }
        {
            // EXTERNAL SHARED_BODY: callee-side EXTERNAL_ENTRY + caller-side
            // EXTERNAL_PARAMETER boundaries, no caller-side return boundary.
            OpId entryOp = nextOpId();
            OpId entryReturn = nextOpId();
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(entryReturn, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), SIG_II, false,
                    entryReturn, null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(boundaryWith(paramBoundary, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.ExternalFunction(MOD, "f", SIG_II,
                            ExternalExecutionOwner.SHARED_BODY)),
                    SIG_II, List.of(paramBoundary), null, null, null, entryOp),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("call mode EXTERNAL SHARED_BODY", ops, callModes, "EXTERNAL");
            track(boundaryKinds, "EXTERNAL_PARAMETER");
        }
        {
            // EXTERNAL RETAINED_ABI: caller-side return boundary.
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.ExternalFunction(MOD, "f", SIG_II,
                            ExternalExecutionOwner.RETAINED_ABI)),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("call mode EXTERNAL RETAINED_ABI", ops, Set.of(), null);
        }

        // Async sources: HOST and EXTERNAL.
        {
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.HostFunction(
                        new ModuleId("host.a"), "f", SIG_II_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, null, "op-label", null),
                new AsyncTokenId.Canonical(2, AsyncTokenOwner.HOST_OPERATION),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.ASYNC_OPERATION_HANDLE, null));
            passingSweep("async source HOST", ops, asyncSources, "HOST");
            track(policies, "ASYNC_OPERATION_HANDLE");
        }
        {
            OpId entryOp = nextOpId();
            OpId entryReturn = nextOpId();
            OpId startOp = nextOpId();
            OpId paramBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(entryReturn, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), SIG_II_ASYNC, true,
                    entryReturn, INT),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(boundaryWith(paramBoundary, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.ExternalFunction(MOD, "f", SIG_II_ASYNC,
                            ExternalExecutionOwner.SHARED_BODY)),
                    AsyncStartSource.EXTERNAL, ParameterBoundaryMode.RUN,
                    List.of(paramBoundary), INT, null, null, null),
                new AsyncTokenId.Canonical(3, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("async source EXTERNAL", ops, asyncSources, "EXTERNAL");
        }

        // Parameter boundary modes: ELIDED_BY_ADAPTER on the nested source
        // op of an adapter-over-async task.
        {
            OpId outerOp = nextOpId();
            OpId outerParam = nextOpId();
            OpId nestedOp = nextOpId();
            OpId nestedReturn = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(outerParam, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(nestedReturn, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, nestedOp));
            ops.add(opWith(outerOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.AdapterBinding(
                        nextOpId(), CaptureMode.SHARED_CELL,
                        new AdaptSourceRef.SharedCell(new BindingId(1), 0),
                        SIG_II_ASYNC, SIG_II)),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(outerParam), INT, null, null, null),
                new AsyncTokenId.Canonical(4, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(nestedOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.ELIDED_BY_ADAPTER,
                    List.of(), INT, nestedReturn, null, null),
                new AsyncTokenId.Canonical(5, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, outerOp));
            passingSweep("parameter boundary mode ELIDED_BY_ADAPTER", ops, paramModes,
                "ELIDED_BY_ADAPTER");
            track(captureModes, "SHARED_CELL");
        }

        // Index modes: ARRAY_WRITE, TABLE_READ, TABLE_WRITE.
        for (IndexMode mode : List.of(IndexMode.ARRAY_WRITE, IndexMode.TABLE_READ,
                IndexMode.TABLE_WRITE)) {
            passingSweep("index mode " + mode.name(), List.of(
                op(SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(mode, nextValue(), nextValue()),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null)),
                indexModes, mode.name());
        }

        // Iteration modes: STRING_SCALARS.
        passingSweep("iteration mode STRING_SCALARS", List.of(
            op(SemanticOpKind.FOR_EACH,
                new KindPayload.ForEachPayload(IterationMode.STRING_SCALARS, nextValue(),
                    new BindingId(1), 0, new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null)),
            iterationModes, "STRING_SCALARS");

        // Control selectors: LOGICAL_AND, LOGICAL_OR, TRY_CATCH on BRANCH;
        // FOR on LOOP.
        for (ControlSelector selector : List.of(ControlSelector.LOGICAL_AND,
                ControlSelector.LOGICAL_OR, ControlSelector.TRY_CATCH)) {
            passingSweep("control selector " + selector.name(), List.of(
                op(SemanticOpKind.BRANCH,
                    new KindPayload.BranchPayload(selector, nextValue(), new BlockId(1),
                        new BlockId(2)),
                    null, null, FailurePolicyId.NO_DEAL_FAILURE, null)),
                controlSelectors, selector.name());
        }
        passingSweep("control selector FOR", List.of(
            op(SemanticOpKind.LOOP,
                new KindPayload.LoopPayload(ControlSelector.FOR, new BlockId(1), nextValue(),
                    new BlockId(2), new BlockId(3)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null)),
            controlSelectors, "FOR");

        // Capture modes: REEVALUATE_THUNK (with a registered adapter binding
        // for the function-typed result).
        {
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(),
                    CaptureMode.REEVALUATE_THUNK,
                    new AdaptSourceRef.Thunk(new BlockId(1), List.of()),
                    SIG_II, SIG_II);
            ValueId result = new ValueId(2500);
            passingSweep("capture mode REEVALUATE_THUNK", List.of(
                op(SemanticOpKind.FUNCTION_ADAPT,
                    new KindPayload.FunctionAdaptPayload(SIG_II, SIG_II,
                        CaptureMode.REEVALUATE_THUNK,
                        new AdaptSourceRef.Thunk(new BlockId(1), List.of()), null),
                    result, SIG_II, FailurePolicyId.NO_DEAL_FAILURE, null)),
                Map.of(new FunctionAllocationIdentity(2500), binding),
                captureModes, "REEVALUATE_THUNK");
        }

        // Realization forms: RepresentationProof.
        passingSweep("realization RepresentationProof", List.of(
            op(SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                    nextValue(), new BoundaryRealization.RepresentationProof("jvm-int-proof")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, null)),
            realizations, "representationProof");
        track(boundaryKinds, "VARIABLE_ASSIGNMENT");

        // The 25 boundary kinds, each in a passing unit with its closed cell.
        passingSweep("boundary kinds (25 cells)", buildBoundaryKindUnit(), Set.of(), null);
        boundaryKinds.addAll(boundaryKindsTest);
        policies.addAll(policiesSweep);

        // Stdlib ids: all 21 with their pinned algorithm policies.
        for (StdlibFunctionId function : StdlibFunctionId.values()) {
            passingSweep("stdlib " + function.name(), List.of(
                op(SemanticOpKind.STDLIB_CALL,
                    new KindPayload.StdlibCallPayload(function, List.of(),
                        SemanticCapability.STDLIB_SEMANTICS),
                    nextValue(), RuntimeDescriptor.Null.INSTANCE, stdlibPolicy(function), null)),
                stdlibIds, function.name());
            track(policies, stdlibPolicy(function).name());
        }

        // FUNCTION_SIGNATURE: a function-descriptor boundary under the
        // descriptor-kind rule; HOST_LOAD: a host module import.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, SIG_II,
                FailurePolicyId.FUNCTION_SIGNATURE, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, SIG_II,
                FailurePolicyId.FUNCTION_SIGNATURE, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    SIG_FF, List.of(paramBoundary), returnBoundary, null, new BlockId(1), null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            passingSweep("policy FUNCTION_SIGNATURE", ops, policies, "FUNCTION_SIGNATURE");
        }
        passingSweep("policy HOST_LOAD", List.of(
            op(SemanticOpKind.MODULE_IMPORT,
                new KindPayload.ModuleImportPayload("host.a", new ModuleId("host.a"),
                    ModuleImportKind.HOST),
                null, null, FailurePolicyId.HOST_LOAD, null)),
            policies, "HOST_LOAD");
        passingSweep("intrinsic NUMBER_CONVERT", List.of(
            op(SemanticOpKind.INTRINSIC_CALL,
                new KindPayload.IntrinsicCallPayload(IntrinsicKind.NUMBER_CONVERT, nextValue()),
                nextValue(), RuntimeDescriptor.Number.INSTANCE,
                FailurePolicyId.NUMBER_CONVERSION, null)),
            policies, "NUMBER_CONVERSION");

        // Assert complete enumeration coverage.
        check(unary.size() == 3, "all 3 unary selectors appear in passing units; got " + unary);
        check(binary.size() == 42, "all 42 binary selectors appear in passing units; got " + binary.size());
        check(callModes.size() == 4, "all 4 call modes appear in passing units; got " + callModes);
        check(asyncSources.size() == 3, "all 3 async sources appear in passing units; got " + asyncSources);
        check(paramModes.size() == 2, "both parameter boundary modes appear in passing units; got " + paramModes);
        check(indexModes.size() == 4, "all 4 index modes appear in passing units; got " + indexModes);
        check(iterationModes.size() == 2, "both iteration modes appear in passing units; got " + iterationModes);
        check(controlSelectors.size() == 6, "all 6 control selectors appear in passing units; got " + controlSelectors);
        check(captureModes.size() == 3, "all 3 capture modes appear in passing units; got " + captureModes);
        check(realizations.size() == 2, "both realization forms appear in passing units; got " + realizations);
        check(boundaryKinds.size() == 25, "all 25 boundary kinds appear in passing units; got " + boundaryKinds);
        check(policies.size() == 24, "all 24 policy names appear in passing units; got " + policies);
        check(stdlibIds.size() == 21, "all 21 stdlib ids appear in passing units; got " + stdlibIds.size());
    }

    private static FailurePolicyId binaryPolicy(BinarySelector selector) {
        return switch (selector) {
            case INT32_ADD, INT32_SUB, INT32_MUL -> FailurePolicyId.INT32_RESULT;
            case INT32_DIV_TRUNC, INT32_MOD_TRUNC -> FailurePolicyId.INT32_DIVISOR_THEN_RESULT;
            case INT32_POW -> FailurePolicyId.INT32_EXPONENT_THEN_RESULT;
            default -> FailurePolicyId.NO_DEAL_FAILURE;
        };
    }

    private static FailurePolicyId stdlibPolicy(StdlibFunctionId function) {
        return switch (function) {
            case CONSOLE_LOG, CONSOLE_ERROR -> FailurePolicyId.INFRASTRUCTURE_ONLY;
            case STRING_LENGTH, TIME_NOW_MILLIS -> FailurePolicyId.INT32_RESULT;
            case JSON_PARSE -> FailurePolicyId.JSON_PARSE_SYNTAX;
            case JSON_STRINGIFY -> FailurePolicyId.JSON_TO_ERROR;
            case MATH_SQRT -> FailurePolicyId.SQRT_NEGATIVE;
            case MATH_ABS_INT -> FailurePolicyId.INT32_RESULT;
            default -> FailurePolicyId.NO_DEAL_FAILURE;
        };
    }

    private static void passingSweep(String what, List<SemanticOp> ops, Set<String> tracker,
            String tracked) {
        passingSweep(what, ops, Map.of(), tracker, tracked);
    }

    private static void passingSweep(String what, List<SemanticOp> ops,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            Set<String> tracker, String tracked) {
        LoweredModuleUnit unit = unit(Set.of(), Map.of(), bindings, ops);
        assertPass(SemanticIrValidator.validate(unit, FACTS), what);
        assertPass(SemanticIrValidator.validateText(SemanticIrValidator.toUnitText(unit), FACTS),
            what + " through the text surface");
        if (tracker != null && tracked != null) {
            track(tracker, tracked);
        }
    }

    /** One unit carrying a passing boundary op for each of the 25 closed boundary kinds. */
    private static List<SemanticOp> buildBoundaryKindUnit() {
        List<SemanticOp> ops = new ArrayList<>();

        // Core descriptor-kind-rule cells (any placement).
        ops.add(boundary(BoundaryKind.VARIABLE_DECLARATION, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.CLASS_FIELD_ASSIGNMENT, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.UNTYPED_CLASS_INPUT, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.OPTIONAL_FIELD_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.CONTEXTUAL_TABLE_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.IMPORTED_MEMBER_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        ops.add(boundary(BoundaryKind.MODULE_EXPORT, INT, FailurePolicyId.TYPE_DESCRIPTOR, null));
        track(boundaryKindsTest, "VARIABLE_DECLARATION");
        track(boundaryKindsTest, "CLASS_FIELD_ASSIGNMENT");
        track(boundaryKindsTest, "UNTYPED_CLASS_INPUT");
        track(boundaryKindsTest, "OPTIONAL_FIELD_READ");
        track(boundaryKindsTest, "CONTEXTUAL_TABLE_READ");
        track(boundaryKindsTest, "IMPORTED_MEMBER_READ");
        track(boundaryKindsTest, "MODULE_EXPORT");

        // ARRAY_NEW + its ARRAY_LITERAL_ELEMENT boundary.
        OpId arrayOp = nextOpId();
        OpId elementBoundary = nextOpId();
        ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, arrayOp));
        ops.add(opWith(arrayOp, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(nextValue()), List.of(elementBoundary)),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null));
        track(boundaryKindsTest, "ARRAY_LITERAL_ELEMENT");

        // INDEX_READ + ARRAY_ELEMENT_READ boundary.
        OpId indexReadOp = nextOpId();
        OpId readBoundary = nextOpId();
        ops.add(boundaryWith(readBoundary, BoundaryKind.ARRAY_ELEMENT_READ, INT,
            FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, indexReadOp));
        ops.add(opWith(indexReadOp, SemanticOpKind.INDEX_READ,
            new KindPayload.IndexReadPayload(nextValue(), nextValue(), readBoundary),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        track(boundaryKindsTest, "ARRAY_ELEMENT_READ");

        // ASSIGN ARRAY_SLOT + ARRAY_ELEMENT_ASSIGNMENT boundary.
        OpId assignOp = nextOpId();
        OpId assignBoundary = nextOpId();
        ops.add(boundaryWith(assignBoundary, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
            FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, assignOp));
        ops.add(opWith(assignOp, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(deal.semantic.ir.AssignTargetKind.ARRAY_SLOT,
                List.of(nextOpId(), nextOpId(), nextOpId(), assignBoundary, nextOpId())),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        track(boundaryKindsTest, "ARRAY_ELEMENT_ASSIGNMENT");
        track(policiesSweep, "ARRAY_WRITE_BOUNDS_THEN_ELEMENT");

        // DELETE ARRAY_SLOT + ARRAY_ELEMENT_DELETE boundary.
        OpId deleteOp = nextOpId();
        OpId deleteBoundary = nextOpId();
        ops.add(boundaryWith(deleteBoundary, BoundaryKind.ARRAY_ELEMENT_DELETE, INT,
            FailurePolicyId.ARRAY_DELETE_BOUNDS, deleteOp));
        ops.add(opWith(deleteOp, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                List.of(nextOpId(), nextOpId(), deleteBoundary, nextOpId())),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        track(boundaryKindsTest, "ARRAY_ELEMENT_DELETE");
        track(policiesSweep, "ARRAY_DELETE_BOUNDS");

        // JSON field boundaries.
        ops.add(boundary(BoundaryKind.JSON_FROM_FIELD, INT, FailurePolicyId.JSON_FROM_NULL, null));
        ops.add(boundary(BoundaryKind.JSON_TO_FIELD, INT, FailurePolicyId.JSON_TO_ERROR, null));
        track(boundaryKindsTest, "JSON_FROM_FIELD");
        track(boundaryKindsTest, "JSON_TO_FIELD");

        // AWAIT + ASYNC_COMPLETION boundary (the single completion position).
        OpId awaitOp = nextOpId();
        OpId completionBoundary = nextOpId();
        ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
            FailurePolicyId.ASYNC_COMPLETION, awaitOp));
        ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
            new KindPayload.AwaitPayload(new AsyncTokenId.Canonical(6, AsyncTokenOwner.DEAL_BODY_TASK),
                INT, completionBoundary),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        track(boundaryKindsTest, "ASYNC_COMPLETION");

        // CLASS_NEW + CLASS_LITERAL_FIELD / CLASS_DEFAULT_FIELD boundaries.
        {
            ClassId classId = new ClassId("mod.a", "C");
            ClassLayout layout = new ClassLayout(classId,
                List.of(new ClassLayout.FieldLayout("f", INT, true, DefaultOwner.LOCAL)));
            OpId classNewOp = nextOpId();
            OpId literalBoundary = nextOpId();
            OpId defaultBoundary = nextOpId();
            ops.add(boundaryWith(literalBoundary, BoundaryKind.CLASS_LITERAL_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(boundaryWith(defaultBoundary, BoundaryKind.CLASS_DEFAULT_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(opWith(classNewOp, SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(classId, layout,
                    List.of(new KindPayload.ProvidedField("f", nextValue())),
                    DefaultOwner.LOCAL, List.of(), null,
                    List.of(new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_LITERAL_FIELD,
                            literalBoundary),
                        new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_DEFAULT_FIELD,
                            defaultBoundary))),
                nextValue(), new RuntimeDescriptor.Class(classId),
                FailurePolicyId.CLASS_CONSTRUCTION, null));
            track(boundaryKindsTest, "CLASS_LITERAL_FIELD");
            track(boundaryKindsTest, "CLASS_DEFAULT_FIELD");
        }

        // CALL DIRECT + FUNCTION_PARAMETER / FUNCTION_RETURN boundaries.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, new BlockId(1), null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        }

        // STDLIB_CALL + STDLIB_PARAMETER / STDLIB_RETURN boundaries.
        {
            OpId stdlibOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.STDLIB_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, stdlibOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.STDLIB_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, stdlibOp));
            ops.add(opWith(stdlibOp, SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(StdlibFunctionId.MATH_ABS_INT,
                    List.of(nextValue()), SemanticCapability.STDLIB_SEMANTICS),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null));
            track(boundaryKindsTest, "STDLIB_PARAMETER");
            track(boundaryKindsTest, "STDLIB_RETURN");
        }

        // CALL EXTERNAL RETAINED_ABI + EXTERNAL_PARAMETER / EXTERNAL_RETURN boundaries.
        {
            OpId callOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.ExternalFunction(MOD, "f", SIG_II,
                            ExternalExecutionOwner.RETAINED_ABI)),
                    SIG_II, List.of(paramBoundary), returnBoundary, null, null, null),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            track(boundaryKindsTest, "EXTERNAL_PARAMETER");
            track(boundaryKindsTest, "EXTERNAL_RETURN");
        }

        // CALLBACK_INVOKE + HOST_TO_DEAL / DEAL_TO_HOST boundaries.
        {
            OpId callbackOp = nextOpId();
            OpId paramBoundary = nextOpId();
            OpId returnBoundary = nextOpId();
            ops.add(boundaryWith(paramBoundary, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(boundaryWith(returnBoundary, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(new ValueId(9), SIG_II,
                    List.of(paramBoundary), returnBoundary),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            track(boundaryKindsTest, "HOST_TO_DEAL");
            track(boundaryKindsTest, "DEAL_TO_HOST");
        }

        return ops;
    }

    private static final Set<String> boundaryKindsTest = new LinkedHashSet<>();
    private static final Set<String> policiesSweep = new LinkedHashSet<>();

    // =========================================================================
    // 23 construct rows recorded in passing units with a produced mapped op
    // =========================================================================

    private static void testConstructRows() {
        System.out.println("-- 23 construct rows recorded in passing units --");

        Map<ConstructKind, SemanticOpKind> producing = new EnumMap<>(ConstructKind.class);
        producing.put(ConstructKind.SCALAR_LITERAL, SemanticOpKind.CONST);
        producing.put(ConstructKind.IDENTIFIER, SemanticOpKind.BINDING_LOAD);
        producing.put(ConstructKind.UNARY_ARITHMETIC_COMPARISON, SemanticOpKind.UNARY);
        producing.put(ConstructKind.STRING_CONCAT_TEMPLATE, SemanticOpKind.STRING_CONCAT);
        producing.put(ConstructKind.CALL, SemanticOpKind.CALL);
        producing.put(ConstructKind.CROSS_MODULE_CALL, SemanticOpKind.EXTERNAL_ENTRY);
        producing.put(ConstructKind.MEMBER_ACCESS, SemanticOpKind.MEMBER_READ);
        producing.put(ConstructKind.INDEX_ACCESS, SemanticOpKind.INDEX_READ);
        producing.put(ConstructKind.ARRAY_OBJECT_LITERAL, SemanticOpKind.ARRAY_NEW);
        producing.put(ConstructKind.CLASS_OBJECT_LITERAL, SemanticOpKind.CLASS_NEW);
        producing.put(ConstructKind.FUNCTION_DECLARATION_EXPRESSION, SemanticOpKind.CLOSURE_NEW);
        producing.put(ConstructKind.ASSIGNMENT, SemanticOpKind.ASSIGN);
        producing.put(ConstructKind.DELETE, SemanticOpKind.DELETE);
        producing.put(ConstructKind.HAS, SemanticOpKind.HAS_FIELD);
        producing.put(ConstructKind.AWAIT_ASYNC_CALL, SemanticOpKind.AWAIT);
        producing.put(ConstructKind.VARIABLE_DECLARATION, SemanticOpKind.BINDING_ALLOC);
        producing.put(ConstructKind.RETURN_EXPRESSION_STATEMENT, SemanticOpKind.RETURN);
        producing.put(ConstructKind.IF_WHILE_FOR_FOR_OF, SemanticOpKind.BRANCH);
        producing.put(ConstructKind.BREAK_CONTINUE, SemanticOpKind.BREAK);
        producing.put(ConstructKind.TRY_CATCH_THROW, SemanticOpKind.TRY_CATCH);
        producing.put(ConstructKind.CLASS_DECLARATION, SemanticOpKind.CLASS_DEFAULT);
        producing.put(ConstructKind.IMPORT_EXPORT_ENTRY, SemanticOpKind.MODULE_INIT);
        producing.put(ConstructKind.STDLIB_TIME_NOW_MILLIS, SemanticOpKind.STDLIB_CALL);

        int withForm = 0;
        for (ConstructKind kind : ConstructKind.values()) {
            check(kind.requiredCommonForm() != null,
                "every row carries a required common form (the K7 std.time row included)");
            withForm++;
            Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(kind,
                kind.mappedOpKinds());
            List<SemanticOp> produced = buildProducingOps(producing.get(kind));
            LoweredModuleUnit unit = unit(Set.of(), coverage, Map.of(),
                produced == null ? List.of() : produced);
            assertPass(SemanticIrValidator.validate(unit, FACTS),
                "construct row " + kind.name() + " with a produced op of a mapped kind");
            assertPass(SemanticIrValidator.validateText(SemanticIrValidator.toUnitText(unit), FACTS),
                "construct row " + kind.name() + " through the text surface");
        }
        check(withForm == 23, "23 rows carry a required common form; got " + withForm);

        // The pinned exemplars: the call, unary/arithmetic/comparison, and
        // function declaration/expression rows prove CALL / UNARY / BINARY /
        // CLOSURE_NEW each have a producing construct.
        check(producing.get(ConstructKind.CALL) == SemanticOpKind.CALL
                && producing.get(ConstructKind.UNARY_ARITHMETIC_COMPARISON) == SemanticOpKind.UNARY
                && producing.get(ConstructKind.FUNCTION_DECLARATION_EXPRESSION)
                    == SemanticOpKind.CLOSURE_NEW,
            "the call/unary/function-declaration rows produce CALL/UNARY/CLOSURE_NEW");
        check(ConstructKind.CALL.mappedOpKinds().contains(SemanticOpKind.CALL)
                && ConstructKind.UNARY_ARITHMETIC_COMPARISON.mappedOpKinds()
                    .containsAll(List.of(SemanticOpKind.UNARY, SemanticOpKind.BINARY))
                && ConstructKind.FUNCTION_DECLARATION_EXPRESSION.mappedOpKinds()
                    .contains(SemanticOpKind.CLOSURE_NEW),
            "the pinned detector rows map those producing kinds");

        // The K7 std.time row is an ordinary constructCoverage key: a unit
        // that records it with a produced STDLIB_CALL passes, and a unit
        // that records it with no produced op of a mapped kind fails
        // R-COVERAGE like every other row.
        LoweredModuleUnit timeCovered = new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, LCH, Set.of(),
            Map.of(ConstructKind.STDLIB_TIME_NOW_MILLIS,
                ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds()),
            Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            buildProducingOps(SemanticOpKind.STDLIB_CALL));
        assertPass(SemanticIrValidator.validate(timeCovered, FACTS),
            "the std/time.nowMillis row with a produced STDLIB_CALL");
        assertE6005(SemanticIrValidator.validate(
                unit(Set.of(), Map.of(ConstructKind.STDLIB_TIME_NOW_MILLIS,
                        ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds()),
                    Map.of(), List.of(constOp())), FACTS),
            "R-COVERAGE", "STDLIB_TIME_NOW_MILLIS");
    }

    private static List<SemanticOp> buildProducingOps(SemanticOpKind kind) {
        return switch (kind) {
            case CONST -> List.of(constOp());
            case UNARY -> List.of(op(SemanticOpKind.UNARY,
                new KindPayload.UnaryPayload(UnarySelector.BOOL_NOT),
                nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null));
            case BINARY -> List.of(op(SemanticOpKind.BINARY,
                new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null));
            case CLOSURE_NEW -> List.of(op(SemanticOpKind.CLOSURE_NEW,
                new KindPayload.ClosureNewPayload(new FunctionId(1), SIG_II, List.of(),
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(1), new BlockId(1))),
                nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null));
            case CALL -> {
                OpId callOp = nextOpId();
                OpId paramBoundary = nextOpId();
                OpId returnBoundary = nextOpId();
                List<SemanticOp> ops = new ArrayList<>();
                ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                    FailurePolicyId.TYPE_DESCRIPTOR, callOp));
                ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                    FailurePolicyId.TYPE_DESCRIPTOR, callOp));
                ops.add(opWith(callOp, SemanticOpKind.CALL,
                    new KindPayload.CallPayload(CallMode.DIRECT,
                        new KindPayload.CallCallee.Static(
                            new FunctionExecutionBinding.LoweredBody(
                                new FunctionId(1), new BlockId(1))),
                        SIG_II, List.of(paramBoundary), returnBoundary, null, new BlockId(1), null),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
                yield ops;
            }
            case EXTERNAL_ENTRY -> {
                OpId entryOp = nextOpId();
                OpId returnBoundary = nextOpId();
                List<SemanticOp> ops = new ArrayList<>();
                ops.add(boundaryWith(returnBoundary, BoundaryKind.EXTERNAL_RETURN, INT,
                    FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
                ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                    new KindPayload.ExternalEntryPayload("f", new FunctionId(1), SIG_II, false,
                        returnBoundary, null),
                    null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
                yield ops;
            }
            case ARRAY_NEW -> List.of(op(SemanticOpKind.ARRAY_NEW,
                new KindPayload.ArrayNewPayload(INT, List.of(), List.of()),
                nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE,
                null));
            case CLASS_NEW -> List.of(op(SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(new ClassId("mod.a", "C"),
                    new ClassLayout(new ClassId("mod.a", "C"), List.of()), List.of(),
                    DefaultOwner.LOCAL, List.of(), null, List.of()),
                nextValue(), new RuntimeDescriptor.Class(new ClassId("mod.a", "C")),
                FailurePolicyId.CLASS_CONSTRUCTION, null));
            case AWAIT -> {
                OpId awaitOp = nextOpId();
                OpId completionBoundary = nextOpId();
                List<SemanticOp> ops = new ArrayList<>();
                ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                    FailurePolicyId.ASYNC_COMPLETION, awaitOp));
                ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
                    new KindPayload.AwaitPayload(new AsyncTokenId.Canonical(7,
                        AsyncTokenOwner.DEAL_BODY_TASK), INT, completionBoundary),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
                yield ops;
            }
            case STRING_CONCAT -> List.of(op(SemanticOpKind.STRING_CONCAT,
                new KindPayload.StringConcatPayload(List.of(nextValue())),
                nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null));
            case MEMBER_READ -> List.of(op(SemanticOpKind.MEMBER_READ,
                new KindPayload.MemberReadPayload(nextValue(), "k"),
                nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null));
            case INDEX_READ -> {
                OpId indexReadOp = nextOpId();
                OpId elementBoundary = nextOpId();
                List<SemanticOp> ops = new ArrayList<>();
                ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_ELEMENT_READ, INT,
                    FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, indexReadOp));
                ops.add(opWith(indexReadOp, SemanticOpKind.INDEX_READ,
                    new KindPayload.IndexReadPayload(nextValue(), nextValue(), elementBoundary),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
                yield ops;
            }
            case ASSIGN -> List.of(op(SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(deal.semantic.ir.AssignTargetKind.VARIABLE,
                    List.of(nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case DELETE -> List.of(op(SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT, List.of(nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case HAS_FIELD -> List.of(op(SemanticOpKind.HAS_FIELD,
                new KindPayload.HasFieldPayload(nextValue(), "k"),
                nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null));
            case BINDING_LOAD -> List.of(op(SemanticOpKind.BINDING_LOAD,
                new KindPayload.BindingLoadPayload(new BindingId(1), 0),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            case BINDING_ALLOC -> List.of(op(SemanticOpKind.BINDING_ALLOC,
                new KindPayload.BindingAllocPayload(new BindingId(1), new BlockId(0), false,
                    BindingCellKind.DIRECT, 0),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case RETURN -> List.of(op(SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, new FunctionId(1), nextOpId(), nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case BRANCH -> List.of(op(SemanticOpKind.BRANCH,
                new KindPayload.BranchPayload(ControlSelector.IF, nextValue(), new BlockId(1),
                    new BlockId(2)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case BREAK -> List.of(op(SemanticOpKind.BREAK,
                new KindPayload.BreakPayload(nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case TRY_CATCH -> List.of(op(SemanticOpKind.TRY_CATCH,
                new KindPayload.TryCatchPayload(new BlockId(1), new BindingId(1),
                    new BlockId(2)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case CLASS_DEFAULT -> List.of(op(SemanticOpKind.CLASS_DEFAULT,
                new KindPayload.ClassDefaultPayload(new ClassId("mod.a", "C"), "f",
                    new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case MODULE_INIT -> List.of(op(SemanticOpKind.MODULE_INIT,
                new KindPayload.ModuleInitPayload(MOD, List.of(new ModuleId("dep")),
                    new BlockId(1)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            case STDLIB_CALL -> {
                OpId callOp = nextOpId();
                OpId returnBoundary = nextOpId();
                ValueId result = nextValue();
                List<SemanticOp> ops = new ArrayList<>();
                ops.add(boundaryWith(returnBoundary, BoundaryKind.STDLIB_RETURN, INT,
                    FailurePolicyId.TYPE_DESCRIPTOR, callOp));
                ops.add(opWith(callOp, SemanticOpKind.STDLIB_CALL,
                    new KindPayload.StdlibCallPayload(
                        StdlibFunctionId.TIME_NOW_MILLIS, List.of(),
                        SemanticCapability.STDLIB_SEMANTICS),
                    result, INT, FailurePolicyId.INT32_RESULT, null));
                yield ops;
            }
            default -> null;
        };
    }

    // =========================================================================
    // 3. Negative corpus: each of the 14 rules asserted exactly once per class
    // =========================================================================

    private static void testNegatives() {
        System.out.println("-- Negative corpus (typed construction) --");

        // R-COVERAGE: the call row recorded, no produced op of any mapped kind.
        Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(ConstructKind.CALL,
            ConstructKind.CALL.mappedOpKinds());
        assertE6005(SemanticIrValidator.validate(
                unit(Set.of(), coverage, Map.of(), List.of(constOp())), FACTS),
            "R-COVERAGE", "construct CALL");

        // R-CAPABILITY: a claimed capability without a required operation.
        assertE6005(SemanticIrValidator.validate(
                unit(Set.of(SemanticCapability.CALLS), Map.of(), Map.of(), List.of(constOp())),
                FACTS),
            "R-CAPABILITY", "CALLS");

        // R-POLICY-KIND: a policy not allowed for its selector.
        assertE6005(SemanticIrValidator.validate(unit(List.of(
                op(SemanticOpKind.BINARY,
                    new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                    nextValue(), INT, FailurePolicyId.JSON_PARSE_SYNTAX, null))), FACTS),
            "R-POLICY-KIND", "JSON_PARSE_SYNTAX", "INT32_ADD");

        // R-BOUNDARY-TRIPLE: an invocation-kind boundary outside any invocation.
        assertE6005(SemanticIrValidator.validate(unit(List.of(
                boundary(BoundaryKind.FUNCTION_PARAMETER, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                    null))), FACTS),
            "R-BOUNDARY-TRIPLE", "FUNCTION_PARAMETER");

        // R-ELIDED-PLACEMENT: ELIDED_BY_ADAPTER with no parent op.
        {
            OpId startOp = nextOpId();
            OpId returnBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(returnBoundary, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                        new FunctionId(1), new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.ELIDED_BY_ADAPTER,
                    List.of(), INT, returnBoundary, null, null),
                new AsyncTokenId.Canonical(8, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(SemanticIrValidator.validate(unit(ops), FACTS),
                "R-ELIDED-PLACEMENT", "ELIDED_BY_ADAPTER");
        }

        // R-FUNCTION-BINDING: a function-typed result without a binding.
        assertE6005(SemanticIrValidator.validate(unit(List.of(
                op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    new ValueId(7), SIG_II, FailurePolicyId.NO_DEAL_FAILURE, null))), FACTS),
            "R-FUNCTION-BINDING", "ValueId 7");

        // R-EXTERNAL-ENTRY: a SHARED_BODY ExternalFunction without a recorded
        // EXTERNAL_ENTRY in the callee unit (project-level cross-unit check).
        {
            LoweredModuleUnit caller = unit("mod.a", Set.of(), Map.of(),
                Map.of(new FunctionAllocationIdentity(1),
                    new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", SIG_II,
                        ExternalExecutionOwner.SHARED_BODY)),
                List.of(constOp()));
            LoweredModuleUnit callee = unit("mod.b", Set.of(), Map.of(), Map.of(), List.of());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(MOD, new ExternalModuleInterface(MOD, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                    MOD_B, new ExternalModuleInterface(MOD_B, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
            ExecutableLoweredProject project = new ExecutableLoweredProject(
                SemanticProfile.DEAL_V1_2_INT32, index,
                new LinkedHashMap<>() {{
                    put(MOD, caller);
                    put(MOD_B, callee);
                }}, MOD);
            assertE6005(SemanticIrValidator.validate(project, FACTS),
                "R-EXTERNAL-ENTRY", "SHARED_BODY", "\"f\"");
        }

        // R-ALIAS-CYCLE: an alias referent chain revisiting a token identity.
        {
            AsyncTokenId canonical = new AsyncTokenId.Canonical(9, AsyncTokenOwner.DEAL_BODY_TASK);
            AsyncTokenId aliasB = new AsyncTokenId.Alias(1, canonical, deal.semantic.ir.AsyncLinkKind.EXTERNAL_LINK);
            AsyncTokenId aliasA = new AsyncTokenId.Alias(1, aliasB, deal.semantic.ir.AsyncLinkKind.EXTERNAL_LINK);
            OpId awaitOp = nextOpId();
            OpId completionBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitOp));
            ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(aliasA, INT, completionBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(SemanticIrValidator.validate(unit(ops), FACTS),
                "R-ALIAS-CYCLE", "alias token cycle");
        }

        // R-TOKEN-REUSE: the same token consumed by two AWAITs.
        {
            AsyncTokenId token = new AsyncTokenId.Alias(2,
                new AsyncTokenId.Canonical(10, AsyncTokenOwner.DEAL_BODY_TASK),
                deal.semantic.ir.AsyncLinkKind.EXTERNAL_LINK);
            OpId awaitOne = nextOpId();
            OpId completionOne = nextOpId();
            OpId awaitTwo = nextOpId();
            OpId completionTwo = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(completionOne, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitOne));
            ops.add(opWith(awaitOne, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(token, INT, completionOne),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(boundaryWith(completionTwo, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitTwo));
            ops.add(opWith(awaitTwo, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(token, INT, completionTwo),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(SemanticIrValidator.validate(unit(ops), FACTS),
                "R-TOKEN-REUSE", "consumed twice");
        }

        // R-DIGEST: a wrong (stale) contract digest — T3's recomputation disagrees.
        {
            KindPayload payload = new KindPayload.ConstPayload(new ScalarValue.Int(1));
            OperationContractSnapshot stale = contractFor(SemanticOpKind.CONST, payload, INT,
                List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                "0000000000000000000000000000000000000000000000000000000000000000");
            String recomputed = ContractSnapshotCanonicalizer.digest(stale);
            check(!recomputed.equals(stale.canonicalDigest()),
                "the stale digest differs from T3's recomputation (R-DIGEST precondition)");
            SemanticOp staleOp = new SemanticOp(nextOpId(), SemanticOpKind.CONST, origin(null),
                nextValue(), INT, List.of(), List.of(), payload, FailurePolicyId.NO_DEAL_FAILURE,
                stale);
            Optional<CompilerDiagnostic> diagnostic =
                SemanticIrValidator.validate(unit(List.of(staleOp)), FACTS);
            assertE6005(diagnostic, "R-DIGEST", recomputed);
        }

        // R-PROFILE: interfaceHash mismatch.
        assertE6005(SemanticIrValidator.validate(
                new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
                    SemanticProfile.DEAL_V1_2_INT32, MOD, "wrong-interface-digest", LCH, Set.of(),
                    Map.of(), Map.of(), Map.of(),
                    new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
                    List.of(constOp())), FACTS),
            "R-PROFILE", "interfaceHash");

        // R-PROFILE: loweringContextHash computed by T3's helper for a
        // different profile/registry-hash pair.
        {
            String wrongHash = LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                "different-registry-hash");
            check(!wrongHash.equals(LCH), "the foreign-pair hash differs (T3 precondition)");
            assertE6005(SemanticIrValidator.validate(
                    new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
                        SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, wrongHash, Set.of(),
                        Map.of(), Map.of(), Map.of(),
                        new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
                        Map.of(), List.of(constOp())), FACTS),
                "R-PROFILE", "loweringContextHash");
        }
    }

    // =========================================================================
    // 4. Text-surface negatives: the pinned invalid-IR injection route
    // =========================================================================

    private static void testTextNegatives() {
        System.out.println("-- Negative corpus (canonical-JSON text surface) --");

        // R-ENUM: an open, non-reserved FailurePolicyId value in both mirror
        // positions (op + contract), digest recomputed through T3.
        {
            LoweredModuleUnit base = unit(List.of(
                op(SemanticOpKind.BINARY,
                    new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                    nextValue(), INT, FailurePolicyId.INT32_RESULT, null)));
            assertPass(SemanticIrValidator.validate(base, FACTS), "binary injection base");
            String text = substitutePolicy(SemanticIrValidator.toUnitText(base),
                "INT32_RESULT", "NOT_A_POLICY");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-ENUM", "NOT_A_POLICY");
        }

        // R-ENUM: a reserved boundary name in BoundaryKind position (the
        // three reserved names are R-ENUM values per S6's negative list).
        {
            LoweredModuleUnit base = unit(List.of(
                boundary(BoundaryKind.VARIABLE_DECLARATION, INT, FailurePolicyId.TYPE_DESCRIPTOR,
                    null)));
            assertPass(SemanticIrValidator.validate(base, FACTS), "boundary injection base");
            String text = substitutePayloadLeaf(SemanticIrValidator.toUnitText(base),
                "kind", "VARIABLE_DECLARATION", "DEAL_TO_C_FFI");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-ENUM", "DEAL_TO_C_FFI");
        }

        // R-PRIVATE-STEP: an out-of-set op-kind string.
        {
            LoweredModuleUnit base = unit(List.of(constOp()));
            assertPass(SemanticIrValidator.validate(base, FACTS), "const injection base");
            String text = substituteOpKind(SemanticIrValidator.toUnitText(base),
                "CONST", "PRIVATE_STEP_X");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-PRIVATE-STEP", "PRIVATE_STEP_X");
        }

        // R-ENUM: an open stdlib selector name in the StdlibFunctionId
        // position (the closed-set rule; TIME_NOW_MILLIS is a member
        // since K7 and its typed form is validated by the construct-row
        // battery).
        {
            LoweredModuleUnit base = unit(List.of(
                op(SemanticOpKind.STDLIB_CALL,
                    new KindPayload.StdlibCallPayload(StdlibFunctionId.CONSOLE_LOG, List.of(),
                        SemanticCapability.STDLIB_SEMANTICS),
                    nextValue(), RuntimeDescriptor.Null.INSTANCE,
                    FailurePolicyId.INFRASTRUCTURE_ONLY, null)));
            assertPass(SemanticIrValidator.validate(base, FACTS), "stdlib injection base");
            String text = substituteStdlibFunction(SemanticIrValidator.toUnitText(base),
                "CONSOLE_LOG", "NOT_A_STDLIB_ID");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-ENUM", "NOT_A_STDLIB_ID");
        }

        // R-RESERVED-NAME: each of the four reserved policy names in
        // FailurePolicyId position.
        for (String reserved : FailurePolicyId.RESERVED_NAMES) {
            LoweredModuleUnit base = unit(List.of(
                op(SemanticOpKind.BINARY,
                    new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                    nextValue(), INT, FailurePolicyId.INT32_RESULT, null)));
            String text = substitutePolicy(SemanticIrValidator.toUnitText(base),
                "INT32_RESULT", reserved);
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-RESERVED-NAME", reserved);
        }

        // R-PROFILE: the semanticProfile string LEGACY_SAFE_INT in a unit
        // otherwise identical to a valid one.
        {
            LoweredModuleUnit base = unit(List.of(constOp()));
            String text = substituteUnitLeaf(SemanticIrValidator.toUnitText(base),
                "semanticProfile", "DEAL_V1_2_INT32", "LEGACY_SAFE_INT");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-PROFILE", "LEGACY_SAFE_INT");
        }

        // R-PROFILE: cross-unit profile mismatch through project-level
        // canonical-JSON injection.
        {
            LoweredModuleUnit unitA = unit("mod.a", Set.of(), Map.of(), Map.of(),
                List.of(constOp()));
            LoweredModuleUnit unitB = unit("mod.b", Set.of(), Map.of(), Map.of(),
                List.of(constOp()));
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(MOD, new ExternalModuleInterface(MOD, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES),
                    MOD_B, new ExternalModuleInterface(MOD_B, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)));
            ExecutableLoweredProject project = new ExecutableLoweredProject(
                SemanticProfile.DEAL_V1_2_INT32, index,
                new LinkedHashMap<>() {{
                    put(MOD, unitA);
                    put(MOD_B, unitB);
                }}, MOD);
            assertPass(SemanticIrValidator.validate(project, FACTS), "project injection base");
            String text = substituteProjectUnitLeaf(SemanticIrValidator.toProjectText(project),
                1, "semanticProfile", "DEAL_V1_2_INT32", "LEGACY_SAFE_INT");
            assertE6005(SemanticIrValidator.validateText(text, FACTS),
                "R-PROFILE", "LEGACY_SAFE_INT");
        }

        // Transport-level decode failures are never E6005 and never a rule.
        try {
            SemanticIrValidator.validateText("{not json", FACTS);
            fail("malformed JSON must raise SemanticIrTextDecodeException");
        } catch (deal.semantic.ir.SemanticIrTextDecodeException expected) {
            check(true, "malformed JSON is a transport-level decode failure (never E6005)");
        }
    }

    // ---- text-surface substitution helpers (one leaf + digest recompute) ----

    private static CanonicalJson.Obj parseObj(String text) {
        return (CanonicalJson.Obj) CanonicalJson.parse(text);
    }

    private static CanonicalJson.Value at(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }

    private static CanonicalJson.Obj withEntry(CanonicalJson.Obj obj, String key,
            CanonicalJson.Value value) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            entries.add(entry.key().equals(key)
                ? CanonicalJson.e(key, value) : entry);
        }
        return CanonicalJson.obj(entries);
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

    private static String substitutePolicy(String text, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "failurePolicy", CanonicalJson.str(to));
        CanonicalJson.Obj op2 = withEntry(op, "failurePolicy", CanonicalJson.str(to));
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    private static String substitutePayloadLeaf(String text, String key, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, key, CanonicalJson.str(to));
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    private static String substituteOpKind(String text, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "opKind", CanonicalJson.str(to));
        CanonicalJson.Obj op2 = withEntry(op, "kind", CanonicalJson.str(to));
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    private static String substituteStdlibFunction(String text, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, "function", CanonicalJson.str(to));
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        contract2 = contractWith(contract2, "selector", CanonicalJson.str(to));
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    private static String substituteUnitLeaf(String text, String key, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        return serialize(withEntry(root, key, CanonicalJson.str(to)));
    }

    private static String substituteProjectUnitLeaf(String text, int unitIndex, String key,
            String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Arr modules = (CanonicalJson.Arr) at(root, "modules");
        List<CanonicalJson.Value> items = new ArrayList<>(modules.items());
        CanonicalJson.Obj unit = (CanonicalJson.Obj) items.get(unitIndex);
        items.set(unitIndex, withEntry(unit, key, CanonicalJson.str(to)));
        return serialize(withEntry(root, "modules", CanonicalJson.arr(items)));
    }

    private static CanonicalJson.Obj firstOp(CanonicalJson.Obj root) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        return (CanonicalJson.Obj) ops.items().get(0);
    }

    private static CanonicalJson.Obj withOps(CanonicalJson.Obj root, CanonicalJson.Obj op) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        List<CanonicalJson.Value> items = new ArrayList<>(ops.items());
        items.set(0, op);
        return withEntry(root, "ops", CanonicalJson.arr(items));
    }

    private static String serialize(CanonicalJson.Value value) {
        return CanonicalJson.serializeText(value);
    }

    // =========================================================================
    // 5. Determinism and multi-defect first-failure order
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- Deterministic first-failure order --");

        // Two independent defects in one unit: the S6 enumeration order
        // decides — R-COVERAGE (rule 1) before R-DIGEST (rule 13).
        {
            KindPayload payload = new KindPayload.ConstPayload(new ScalarValue.Int(1));
            OperationContractSnapshot stale = contractFor(SemanticOpKind.CONST, payload, INT,
                List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
            SemanticOp staleOp = new SemanticOp(nextOpId(), SemanticOpKind.CONST, origin(null),
                nextValue(), INT, List.of(), List.of(), payload, FailurePolicyId.NO_DEAL_FAILURE,
                stale);
            Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(ConstructKind.CALL,
                ConstructKind.CALL.mappedOpKinds());
            LoweredModuleUnit unit = unit(Set.of(), coverage, Map.of(), List.of(staleOp));
            Optional<CompilerDiagnostic> first = SemanticIrValidator.validate(unit, FACTS);
            assertE6005(first, "R-COVERAGE", "construct CALL");
            // Repeated runs are byte-identical diagnostics.
            check(first.get().message().equals(
                    SemanticIrValidator.validate(unit, FACTS).get().message()),
                "repeated validation produces the identical first failure");
        }

        // Repeated text-surface runs are deterministic too.
        {
            LoweredModuleUnit base = unit(List.of(constOp()));
            String text = substituteUnitLeaf(SemanticIrValidator.toUnitText(base),
                "semanticProfile", "DEAL_V1_2_INT32", "LEGACY_SAFE_INT");
            Optional<CompilerDiagnostic> first = SemanticIrValidator.validateText(text, FACTS);
            Optional<CompilerDiagnostic> second = SemanticIrValidator.validateText(text, FACTS);
            check(first.isPresent() && first.get().message().equals(second.get().message()),
                "repeated text-surface validation produces the identical first failure");
        }

        // Typed/text equivalence for a typed negative: the same rule fires on
        // both surfaces.
        {
            LoweredModuleUnit negative = unit(Set.of(SemanticCapability.CALLS), Map.of(),
                Map.of(), List.of(constOp()));
            Optional<CompilerDiagnostic> typed = SemanticIrValidator.validate(negative, FACTS);
            Optional<CompilerDiagnostic> text = SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(negative), FACTS);
            assertE6005(typed, "R-CAPABILITY", "CALLS");
            assertE6005(text, "R-CAPABILITY", "CALLS");
            check(typed.get().message().equals(text.get().message()),
                "both surfaces report the identical E6005 for the same defect");
        }
    }

    // =========================================================================
    // 6. Lock pins (ISSUE-0368, retargeted by K7): TIME_NOW_MILLIS is the
    //    21st closed member; the STDLIB_TIME_CONFLICT routing marker stays inert
    // =========================================================================

    private static boolean enumMember(Class<? extends Enum<?>> closed, String name) {
        for (Enum<?> value : closed.getEnumConstants()) {
            if (value.name().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private static void testLockPins() {
        System.out.println("-- Lock pins (ISSUE-0368, K7): TIME_NOW_MILLIS is the 21st "
            + "member; STDLIB_TIME_CONFLICT never valid IR --");

        // Fact 1 — the K7 selector member: TIME_NOW_MILLIS is the 21st enum
        // member, RESERVED_NAMES is empty, and the reserved-name guard stays
        // (deny-by-default over the closed set).
        check(enumMember(StdlibFunctionId.class, "TIME_NOW_MILLIS"),
            "TIME_NOW_MILLIS is a StdlibFunctionId enum member (the 21st value)");
        check(StdlibFunctionId.RESERVED_NAMES.isEmpty()
                && !StdlibFunctionId.RESERVED_NAMES.contains("TIME_NOW_MILLIS"),
            "RESERVED_NAMES is empty — the superseded D8 reservation is retired");
        check(!StdlibFunctionId.isReservedName("TIME_NOW_MILLIS")
                && !StdlibFunctionId.isReservedName("NOT_A_STDLIB_ID"),
            "neither TIME_NOW_MILLIS nor an unknown name is a reserved selector name");

        // Fact 1 — the closed-set surface: an out-of-set stdlib selector
        // name is R-ENUM (the only remaining selector-family rejection),
        // while the typed member validates through the construct-row
        // battery.
        {
            LoweredModuleUnit base = unit(List.of(
                op(SemanticOpKind.STDLIB_CALL,
                    new KindPayload.StdlibCallPayload(StdlibFunctionId.CONSOLE_LOG, List.of(),
                        SemanticCapability.STDLIB_SEMANTICS),
                    nextValue(), RuntimeDescriptor.Null.INSTANCE,
                    FailurePolicyId.INFRASTRUCTURE_ONLY, null)));
            assertPass(SemanticIrValidator.validate(base, FACTS),
                "stdlib injection base (typed surface)");
            String unknown = substituteStdlibFunction(SemanticIrValidator.toUnitText(base),
                "CONSOLE_LOG", "NOT_A_STDLIB_ID");
            Optional<CompilerDiagnostic> unknownDiagnostic =
                SemanticIrValidator.validateText(unknown, FACTS);
            assertE6005(unknownDiagnostic, "R-ENUM", "NOT_A_STDLIB_ID");
            System.out.println("    observed out-of-set selector rejection: "
                + unknownDiagnostic.get().message());

            // The dispatch contrast: the same raw-string route now accepts
            // the closed TIME_NOW_MILLIS name syntactically, so the
            // rejection is the closed-set rule for a truly unknown name.
            String timeName = substituteStdlibFunction(SemanticIrValidator.toUnitText(base),
                "CONSOLE_LOG", "TIME_NOW_MILLIS");
            Optional<CompilerDiagnostic> timeDiagnostic =
                SemanticIrValidator.validateText(timeName, FACTS);
            check(timeDiagnostic.isPresent()
                    && timeDiagnostic.get().message().contains("R-POLICY-KIND"),
                "the raw TIME_NOW_MILLIS name is a closed member: the substitution fails "
                    + "the algorithm→policy pin (R-POLICY-KIND), never R-RESERVED-NAME: "
                    + (timeDiagnostic.isEmpty() ? "no diagnostic"
                        : timeDiagnostic.get().message()));
            System.out.println("    observed TIME_NOW_MILLIS rejection: "
                + (timeDiagnostic.isEmpty() ? "none" : timeDiagnostic.get().message()));
        }

        // Fact 2 — the routing-marker lock: the S4 evidence set of
        // STDLIB_TIME_CONFLICT is empty (never valid IR).
        check(CapabilityRequirementCatalog.requiredOperations(
                SemanticCapability.STDLIB_TIME_CONFLICT).isEmpty(),
            "STDLIB_TIME_CONFLICT maps to {} (empty required-operation evidence — a "
                + "routing marker only, never valid IR)");

        // Fact 2 — a unit claiming STDLIB_TIME_CONFLICT fails R-CAPABILITY
        // on the typed surface and the text surface (the validator is the
        // admission gate of every common-lowering path).
        {
            LoweredModuleUnit forged = unit("mod.a",
                Set.of(SemanticCapability.STDLIB_TIME_CONFLICT),
                Map.of(), Map.of(), List.of());
            Optional<CompilerDiagnostic> typed = SemanticIrValidator.validate(forged, FACTS);
            assertE6005(typed, "R-CAPABILITY", "STDLIB_TIME_CONFLICT");
            System.out.println("    observed STDLIB_TIME_CONFLICT rejection (typed): "
                + typed.get().message());
            Optional<CompilerDiagnostic> text = SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(forged), FACTS);
            assertE6005(text, "R-CAPABILITY", "STDLIB_TIME_CONFLICT");
            check(typed.get().message().equals(text.get().message()),
                "both surfaces report the identical R-CAPABILITY rejection for the forged "
                    + "STDLIB_TIME_CONFLICT claim");
        }

        // Fact 2 — no produced op set can satisfy the claim: a unit that
        // fully satisfies its other claims still fails on the
        // empty-evidence claim, so no lowering path admits a
        // conflict-claiming module.
        {
            LoweredModuleUnit forged = unit("mod.a",
                Set.of(SemanticCapability.FOUNDATION_VALUES,
                    SemanticCapability.STDLIB_TIME_CONFLICT),
                Map.of(), Map.of(), List.of(
                    constOp(),
                    op(SemanticOpKind.UNARY,
                        new KindPayload.UnaryPayload(UnarySelector.BOOL_NOT),
                        nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null),
                    op(SemanticOpKind.BINARY,
                        new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                        nextValue(), INT, FailurePolicyId.INT32_RESULT, null),
                    op(SemanticOpKind.STRING_CONCAT,
                        new KindPayload.StringConcatPayload(List.of(nextValue())),
                        nextValue(), STR, FailurePolicyId.NO_DEAL_FAILURE, null)));
            assertE6005(SemanticIrValidator.validate(forged, FACTS),
                "R-CAPABILITY", "STDLIB_TIME_CONFLICT");
            assertE6005(SemanticIrValidator.validateText(
                    SemanticIrValidator.toUnitText(forged), FACTS),
                "R-CAPABILITY", "STDLIB_TIME_CONFLICT");
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Semantic IR Validator Test (ISSUE-0286) ===\n");

        testRuleSet();
        testPositiveKindCorpus();
        testEnumSweep();
        testConstructRows();
        testNegatives();
        testTextNegatives();
        testDeterminism();
        testLockPins();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
