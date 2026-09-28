package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.NormalizedSlot;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
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
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Verifies the ISSUE-0234 A-D1/A-D3/A-D9 surface: {@link AddressChainProtocol}
 * as the closed address-chain shape authority of {@code deal.semantic-ir/1}
 * and {@link NormalizedSlot} as the closed {@code INDEX_NORMALIZE} slot
 * computation.
 *
 * <p>Corpus:</p>
 * <ol>
 *   <li>NormalizedSlot: the ARRAY_READ present/absent decisions, the
 *       ARRAY_WRITE append decision exactly at {@code index ==
 *       currentLength}, total representation of negative/out-of-range
 *       indices (never a failure), table-slot key identity with no
 *       coercion, the table-mode computation ignoring {@code currentLength}
 *       (the surface takes none), the pinned result types, the closed
 *       sealed shapes, and the fail-closed mode dispatch.</li>
 *   <li>Positives: one unit per closed A-D9 shape — the plain and
 *       adapter VARIABLE chains, TABLE_SLOT member/index writes,
 *       ARRAY_SLOT write (with its ARRAY_LENGTH lengthOp), CLASS_FIELD
 *       write, TABLE_SLOT member/index deletes, ARRAY_SLOT delete,
 *       CLASS_FIELD delete — plus a nested chain (an inner ASSIGN as the
 *       valueOp of an outer chain), a multi-chain unit with no shared
 *       children, a vacuous unit without chain ops, and an
 *       INDEX_NORMALIZE-only unit (non-chain ops are outside the
 *       protocol's domain).</li>
 *   <li>Negatives, each rejected with exactly one E6005 through
 *       {@code FailureContractRegistry} naming module, capability
 *       {@code EVALUATION_ORDER}, the pinned rule, profile
 *       {@code DEAL_V1_2_INT32}, IR version {@code deal.semantic-ir/1},
 *       and the offending op origin: wrong child order, wrong child kind,
 *       wrong boundary kind, wrong boundary policy, wrong normalize mode,
 *       missing lengthOp on an array chain, commit not last, boundary
 *       after the commit, missing VARIABLE_ASSIGNMENT boundary
 *       ({@code ADDRESS_CHAIN_SHAPE}); a producing child referenced by
 *       two chains and a duplicated producing child op
 *       ({@code SINGLE_EVALUATION}).</li>
 *   <li>Foundation regression: {@code INDEX_NORMALIZE → NO_DEAL_FAILURE}
 *       stays pinned by the foundation validator (R-POLICY-KIND) and the
 *       closed 14-condition rule set is unchanged — the protocol adds no
 *       {@code SemanticIrValidator} rule.</li>
 *   <li>Determinism: repeated validation is byte-identical.</li>
 * </ol>
 */
public class AddressChainProtocolTest {

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

    private static final ModuleId MOD = new ModuleId("mod.chain");
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, "capability-registry-hash-1");

    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor STR = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor TBL = RuntimeDescriptor.Table.INSTANCE;
    private static final RuntimeDescriptor ARR = new RuntimeDescriptor.Array(INT);
    private static final RuntimeDescriptor CLS = new RuntimeDescriptor.Class(new ClassId("mod.chain", "C"));
    private static final RuntimeDescriptor.Func SIG_II = new RuntimeDescriptor.Func(List.of(INT), INT);
    private static final RuntimeDescriptor.Func SIG_II_I =
        new RuntimeDescriptor.Func(List.of(INT, INT), INT);

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

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent, ValueId input) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    /** A CONST signed32 producer with a pinned result identity. */
    private static SemanticOp constInt(OpId id, OpId parent, ValueId result, int value) {
        return opWith(id, SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(value)),
            result, INT, FailurePolicyId.NO_DEAL_FAILURE, parent);
    }

    /** A CONST string producer with a pinned result identity. */
    private static SemanticOp constString(OpId id, OpId parent, ValueId result, String value) {
        return opWith(id, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.String(value)),
            result, STR, FailurePolicyId.NO_DEAL_FAILURE, parent);
    }

    private static LoweredModuleUnit unit(List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, "interface-digest-1", LCH, Set.of(),
            Map.of(), Map.of(), Map.of(), new ModuleInitPlan(List.of(), new BlockId(0)),
            ExportPlan.empty(), Map.of(), ops);
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
        check(message.contains("module 'mod.chain'"), rule + " message names the module");
        check(message.contains("capability EVALUATION_ORDER"),
            rule + " message names capability EVALUATION_ORDER");
        check(message.contains("validatorRule " + rule + ","),
            rule + " is named as the validator rule (exactly one rule per fixture); got \""
                + message + "\"");
        check(message.contains("semanticProfile DEAL_V1_2_INT32"),
            rule + " message names the semantic profile");
        check(message.contains("irVersion deal.semantic-ir/1"),
            rule + " message names the IR version");
        check(message.contains("AddressChainProtocol " + rule),
            rule + " message names the producing component");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \""
                + message + "\"");
        }
    }

    private static void expectIllegalArgument(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected IllegalArgumentException for " + what + ", but no exception was raised");
        } catch (IllegalArgumentException expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected IllegalArgumentException for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    // =========================================================================
    // Closed A-D9 chain fixtures (children first, then the chain op)
    // =========================================================================

    /** ASSIGN VARIABLE: [valueOp, VARIABLE_ASSIGNMENT boundaryOp, BINDING_STORE commitOp]. */
    private static List<SemanticOp> variableAssignPlain() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId value = nextValue();
        OpId valueOp = nextOpId();
        OpId boundaryOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(constInt(valueOp, chainId, value, 7));
        ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, chainId, value));
        ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
            new KindPayload.BindingStorePayload(new BindingId(1), 1, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                List.of(valueOp, boundaryOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** ASSIGN VARIABLE adapter: [valueOp, FUNCTION_ADAPT, VARIABLE_ASSIGNMENT, BINDING_STORE]. */
    private static List<SemanticOp> variableAssignAdapter() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId sourceValue = nextValue();
        ValueId adapterValue = nextValue();
        OpId valueOp = nextOpId();
        OpId adapterOp = nextOpId();
        OpId boundaryOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(constInt(valueOp, chainId, sourceValue, 7));
        ops.add(opWith(adapterOp, SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(SIG_II, SIG_II_I, CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(new BindingId(2), 0), null),
            adapterValue, SIG_II_I, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, SIG_II_I,
            FailurePolicyId.FUNCTION_SIGNATURE, chainId, adapterValue));
        ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
            new KindPayload.BindingStorePayload(new BindingId(3), 1, adapterValue),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                List.of(valueOp, adapterOp, boundaryOp, commitOp)),
            adapterValue, SIG_II_I, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** ASSIGN TABLE_SLOT member write: [containerOp, valueOp, MEMBER_WRITE]. */
    private static List<SemanticOp> tableMemberAssign() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId value = nextValue();
        OpId containerOp = nextOpId();
        OpId valueOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, TBL,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constInt(valueOp, chainId, value, 9));
        ops.add(opWith(commitOp, SemanticOpKind.MEMBER_WRITE,
            new KindPayload.MemberWritePayload(container, "k", value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                List.of(containerOp, valueOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** ASSIGN TABLE_SLOT index write: [containerOp, keyOp, valueOp, normalizeOp(TABLE_WRITE), INDEX_WRITE]. */
    private static List<SemanticOp> tableIndexAssign() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId key = nextValue();
        ValueId value = nextValue();
        ValueId slot = nextValue();
        OpId containerOp = nextOpId();
        OpId keyOp = nextOpId();
        OpId valueOp = nextOpId();
        OpId normalizeOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, TBL,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constString(keyOp, chainId, key, "0"));
        ops.add(constInt(valueOp, chainId, value, 9));
        ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
            new KindPayload.IndexNormalizePayload(IndexMode.TABLE_WRITE, key, key),
            slot, STR, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(commitOp, SemanticOpKind.INDEX_WRITE,
            new KindPayload.IndexWritePayload(container, slot, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                List.of(containerOp, keyOp, valueOp, normalizeOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /**
     * ASSIGN ARRAY_SLOT write:
     * [containerOp, keyOp, valueOp, lengthOp, normalizeOp(ARRAY_WRITE),
     * boundaryOp(ARRAY_ELEMENT_ASSIGNMENT + ARRAY_WRITE_BOUNDS_THEN_ELEMENT), INDEX_WRITE].
     */
    private static List<SemanticOp> arrayAssign() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId key = nextValue();
        ValueId value = nextValue();
        ValueId length = nextValue();
        ValueId slot = nextValue();
        OpId containerOp = nextOpId();
        OpId keyOp = nextOpId();
        OpId valueOp = nextOpId();
        OpId lengthOp = nextOpId();
        OpId normalizeOp = nextOpId();
        OpId boundaryOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, ARR,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constInt(keyOp, chainId, key, 0));
        ops.add(constInt(valueOp, chainId, value, 9));
        ops.add(opWith(lengthOp, SemanticOpKind.ARRAY_LENGTH,
            new KindPayload.ArrayLengthPayload(container), length, INT,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
            new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_WRITE, key, length),
            slot, INT, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(boundaryWith(boundaryOp, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
            FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, chainId, value));
        ops.add(opWith(commitOp, SemanticOpKind.INDEX_WRITE,
            new KindPayload.IndexWritePayload(container, slot, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.ARRAY_SLOT,
                List.of(containerOp, keyOp, valueOp, lengthOp, normalizeOp, boundaryOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** ASSIGN CLASS_FIELD write: [containerOp, valueOp, FIELD_WRITE]. */
    private static List<SemanticOp> classFieldAssign() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId value = nextValue();
        OpId containerOp = nextOpId();
        OpId valueOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, CLS,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constInt(valueOp, chainId, value, 9));
        ops.add(opWith(commitOp, SemanticOpKind.FIELD_WRITE,
            new KindPayload.FieldWritePayload(container, new ClassId("mod.chain", "C"), "f", value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.CLASS_FIELD,
                List.of(containerOp, valueOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** DELETE TABLE_SLOT member delete: [containerOp, MEMBER_DELETE]. */
    private static List<SemanticOp> tableMemberDelete() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        OpId containerOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, TBL,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(commitOp, SemanticOpKind.MEMBER_DELETE,
            new KindPayload.MemberDeletePayload(container, "k"),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                List.of(containerOp, commitOp)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** DELETE TABLE_SLOT index delete: [containerOp, keyOp, normalizeOp(TABLE_WRITE), INDEX_DELETE]. */
    private static List<SemanticOp> tableIndexDelete() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId key = nextValue();
        ValueId slot = nextValue();
        OpId containerOp = nextOpId();
        OpId keyOp = nextOpId();
        OpId normalizeOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, TBL,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constString(keyOp, chainId, key, "0"));
        ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
            new KindPayload.IndexNormalizePayload(IndexMode.TABLE_WRITE, key, key),
            slot, STR, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(commitOp, SemanticOpKind.INDEX_DELETE,
            new KindPayload.IndexDeletePayload(container, slot),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                List.of(containerOp, keyOp, normalizeOp, commitOp)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** DELETE CLASS_FIELD delete: [containerOp, FIELD_DELETE]. */
    private static List<SemanticOp> classFieldDelete() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        OpId containerOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, CLS,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(commitOp, SemanticOpKind.FIELD_DELETE,
            new KindPayload.FieldDeletePayload(container, new ClassId("mod.chain", "C"), "f"),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.CLASS_FIELD,
                List.of(containerOp, commitOp)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /**
     * DELETE ARRAY_SLOT delete:
     * [containerOp, keyOp, lengthOp, normalizeOp(ARRAY_WRITE),
     * boundaryOp(ARRAY_ELEMENT_DELETE + ARRAY_DELETE_BOUNDS), INDEX_DELETE].
     */
    private static List<SemanticOp> arrayDelete() {
        List<SemanticOp> ops = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId container = nextValue();
        ValueId key = nextValue();
        ValueId length = nextValue();
        ValueId slot = nextValue();
        OpId containerOp = nextOpId();
        OpId keyOp = nextOpId();
        OpId lengthOp = nextOpId();
        OpId normalizeOp = nextOpId();
        OpId boundaryOp = nextOpId();
        OpId commitOp = nextOpId();
        ops.add(opWith(containerOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, ARR,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(constInt(keyOp, chainId, key, 2));
        ops.add(opWith(lengthOp, SemanticOpKind.ARRAY_LENGTH,
            new KindPayload.ArrayLengthPayload(container), length, INT,
            FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
            new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_WRITE, key, length),
            slot, INT, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(boundaryWith(boundaryOp, BoundaryKind.ARRAY_ELEMENT_DELETE, INT,
            FailurePolicyId.ARRAY_DELETE_BOUNDS, chainId, slot));
        ops.add(opWith(commitOp, SemanticOpKind.INDEX_DELETE,
            new KindPayload.IndexDeletePayload(container, slot),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        ops.add(opWith(chainId, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                List.of(containerOp, keyOp, lengthOp, normalizeOp, boundaryOp, commitOp)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    // =========================================================================
    // 1. NormalizedSlot (A-D3)
    // =========================================================================

    private static void testNormalizedSlot() {
        System.out.println("-- NormalizedSlot: the closed INDEX_NORMALIZE slot computation --");

        // Closed sealed family: exactly the three shapes (the bytes slot is
        // the closed third member, K6 item 5).
        Class<?>[] permitted = NormalizedSlot.class.getPermittedSubclasses();
        check(permitted != null && permitted.length == 3
                && Set.of(NormalizedSlot.ArraySlot.class, NormalizedSlot.TableSlot.class,
                    NormalizedSlot.BytesSlot.class).equals(Set.of(permitted)),
            "NormalizedSlot is sealed over exactly ArraySlot, TableSlot, and BytesSlot");

        // ARRAY_READ: present = index < currentLength; append is always false.
        NormalizedSlot.ArraySlot in = NormalizedSlot.arraySlot(IndexMode.ARRAY_READ, 2, 3);
        check(in.index() == 2 && in.present() && !in.append(),
            "ARRAY_READ index 2 of length 3 is present (index < currentLength) with no append");
        NormalizedSlot.ArraySlot atEnd = NormalizedSlot.arraySlot(IndexMode.ARRAY_READ, 3, 3);
        check(atEnd.index() == 3 && !atEnd.present() && !atEnd.append(),
            "ARRAY_READ index == currentLength is absent with no append");
        NormalizedSlot.ArraySlot beyond = NormalizedSlot.arraySlot(IndexMode.ARRAY_READ, 5, 3);
        check(beyond.index() == 5 && !beyond.present() && !beyond.append(),
            "ARRAY_READ index > currentLength is absent with no append");
        NormalizedSlot.ArraySlot negative = NormalizedSlot.arraySlot(IndexMode.ARRAY_READ, -1, 3);
        check(negative.index() == -1 && negative.present() && !negative.append(),
            "a negative index is represented exactly per the pinned formula (present = "
                + "index < currentLength) — the computation never fails and never enforces "
                + "bounds; the negative index raises E8002 in the read boundary before the "
                + "present decision is ever consulted");

        // ARRAY_WRITE: append exactly at index == currentLength; present stays index < currentLength.
        NormalizedSlot.ArraySlot append = NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE, 3, 3);
        check(append.index() == 3 && append.append() && !append.present(),
            "ARRAY_WRITE index == currentLength is an append (the xs[xs.length] = v idiom)");
        NormalizedSlot.ArraySlot overwrite = NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE, 2, 3);
        check(overwrite.index() == 2 && !overwrite.append() && overwrite.present(),
            "ARRAY_WRITE index < currentLength overwrites in place (append=false, present=true)");
        NormalizedSlot.ArraySlot gap = NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE, 4, 3);
        check(gap.index() == 4 && !gap.append() && !gap.present(),
            "ARRAY_WRITE index > currentLength is a gap (append=false, present=false) — "
                + "bounds enforcement is the boundary policy's, never the normalize's");
        NormalizedSlot.ArraySlot negativeWrite =
            NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE, -1, 0);
        check(negativeWrite.index() == -1 && !negativeWrite.append() && negativeWrite.present(),
            "ARRAY_WRITE with a negative index and length 0 stays a pure computation "
                + "(append = index == currentLength stays false); bounds enforcement is the "
                + "boundary policy's, never the normalize's");

        // Table modes: key identity preserved exactly, no coercion.
        NormalizedSlot.TableSlot zeroKey = NormalizedSlot.tableSlot(IndexMode.TABLE_WRITE, "0");
        check("0".equals(zeroKey.key()), "TABLE_WRITE key \"0\" is preserved exactly (no "
            + "coercion to an int key)");
        NormalizedSlot.TableSlot namedKey = NormalizedSlot.tableSlot(IndexMode.TABLE_READ, "k");
        check("k".equals(namedKey.key()), "TABLE_READ key \"k\" is preserved exactly");
        check(new NormalizedSlot.TableSlot("0").equals(zeroKey),
            "TableSlot equality is the key string (record equality)");

        // Pinned result types (A-D3): int for array modes, string for table modes.
        check(in.resultType() == RuntimeDescriptor.Int.INSTANCE
                && append.resultType() == RuntimeDescriptor.Int.INSTANCE,
            "ArraySlot pins resultType int (the slot's index value)");
        check(zeroKey.resultType() == RuntimeDescriptor.String.INSTANCE
                && namedKey.resultType() == RuntimeDescriptor.String.INSTANCE,
            "TableSlot pins resultType string (the slot's key value)");

        // Determinism and structural equality.
        check(in.equals(NormalizedSlot.arraySlot(IndexMode.ARRAY_READ, 2, 3)),
            "repeated ARRAY_READ computation is structurally identical");
        check(zeroKey.equals(NormalizedSlot.tableSlot(IndexMode.TABLE_WRITE, "0")),
            "repeated TABLE_WRITE computation is structurally identical");
        check(!in.equals(append), "different decisions produce different slots");

        // Fail-closed mode dispatch: a table mode in the array computation and
        // vice versa are internal producer errors, never a DEAL projection.
        expectIllegalArgument(() -> NormalizedSlot.arraySlot(IndexMode.TABLE_READ, 1, 1),
            "arraySlot(TABLE_READ)");
        expectIllegalArgument(() -> NormalizedSlot.tableSlot(IndexMode.ARRAY_WRITE, "k"),
            "tableSlot(ARRAY_WRITE)");
        try {
            NormalizedSlot.tableSlot(IndexMode.TABLE_WRITE, null);
            fail("expected NullPointerException for a null table key");
        } catch (NullPointerException expected) {
            passed++;
        }
    }

    // =========================================================================
    // 2. Positive corpus: the closed A-D9 shapes
    // =========================================================================

    private static void testPositiveShapes() {
        System.out.println("-- Positive corpus: one unit per closed A-D9 shape --");

        assertPass(AddressChainProtocol.validate(unit(variableAssignPlain())),
            "ASSIGN VARIABLE [valueOp, VARIABLE_ASSIGNMENT boundaryOp, BINDING_STORE commitOp]");
        assertPass(AddressChainProtocol.validate(unit(variableAssignAdapter())),
            "ASSIGN VARIABLE [valueOp, FUNCTION_ADAPT adapterOp, VARIABLE_ASSIGNMENT "
                + "boundaryOp, BINDING_STORE commitOp]");
        assertPass(AddressChainProtocol.validate(unit(tableMemberAssign())),
            "ASSIGN TABLE_SLOT [containerOp, valueOp, MEMBER_WRITE] (literal member key)");
        assertPass(AddressChainProtocol.validate(unit(tableIndexAssign())),
            "ASSIGN TABLE_SLOT [containerOp, keyOp, valueOp, INDEX_NORMALIZE(TABLE_WRITE), "
                + "INDEX_WRITE]");
        assertPass(AddressChainProtocol.validate(unit(arrayAssign())),
            "ASSIGN ARRAY_SLOT [containerOp, keyOp, valueOp, lengthOp(ARRAY_LENGTH), "
                + "INDEX_NORMALIZE(ARRAY_WRITE), ARRAY_ELEMENT_ASSIGNMENT boundaryOp, "
                + "INDEX_WRITE]");
        assertPass(AddressChainProtocol.validate(unit(classFieldAssign())),
            "ASSIGN CLASS_FIELD [containerOp, valueOp, FIELD_WRITE]");
        assertPass(AddressChainProtocol.validate(unit(tableMemberDelete())),
            "DELETE TABLE_SLOT [containerOp, MEMBER_DELETE]");
        assertPass(AddressChainProtocol.validate(unit(tableIndexDelete())),
            "DELETE TABLE_SLOT [containerOp, keyOp, INDEX_NORMALIZE(TABLE_WRITE), INDEX_DELETE]");
        assertPass(AddressChainProtocol.validate(unit(classFieldDelete())),
            "DELETE CLASS_FIELD [containerOp, FIELD_DELETE]");
        assertPass(AddressChainProtocol.validate(unit(arrayDelete())),
            "DELETE ARRAY_SLOT [containerOp, keyOp, lengthOp(ARRAY_LENGTH), "
                + "INDEX_NORMALIZE(ARRAY_WRITE), ARRAY_ELEMENT_DELETE boundaryOp, INDEX_DELETE]");
    }

    private static void testPositiveComposition() {
        System.out.println("-- Positive composition: nesting, multi-chain units, non-chains --");

        // Nested chains: an inner ASSIGN is the outer VARIABLE chain's valueOp
        // (assignment is an expression in the grammar).
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId outerChain = nextOpId();
            OpId innerChain = nextOpId();
            ValueId innerValue = nextValue();
            ValueId outerValue = nextValue();

            // Inner chain: VARIABLE [value, boundary, commit].
            OpId innerValueOp = nextOpId();
            OpId innerBoundaryOp = nextOpId();
            OpId innerCommitOp = nextOpId();
            ops.add(constInt(innerValueOp, innerChain, innerValue, 1));
            ops.add(boundaryWith(innerBoundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, innerChain, innerValue));
            ops.add(opWith(innerCommitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(4), 1, innerValue),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, innerChain));
            ops.add(opWith(innerChain, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(innerValueOp, innerBoundaryOp, innerCommitOp)),
                innerValue, INT, FailurePolicyId.NO_DEAL_FAILURE, outerChain));

            // Outer chain: VARIABLE [innerChain, boundary, commit].
            OpId outerBoundaryOp = nextOpId();
            OpId outerCommitOp = nextOpId();
            ops.add(boundaryWith(outerBoundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerChain, innerValue));
            ops.add(opWith(outerCommitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(5), 1, innerValue),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, outerChain));
            ops.add(opWith(outerChain, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(innerChain, outerBoundaryOp, outerCommitOp)),
                outerValue, INT, FailurePolicyId.NO_DEAL_FAILURE, null));

            assertPass(AddressChainProtocol.validate(unit(ops)),
                "a nested ASSIGN valueOp (inner chain parented to the outer chain)");
        }

        // A multi-chain unit with no shared children (children may appear in
        // any order in the op list — resolution is by identity).
        {
            List<SemanticOp> plain = variableAssignPlain();
            List<SemanticOp> member = tableMemberAssign();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(member.get(member.size() - 1)); // chain op first
            ops.addAll(member.subList(0, member.size() - 1));
            ops.addAll(plain);
            assertPass(AddressChainProtocol.validate(unit(ops)),
                "a multi-chain unit with no shared children and out-of-source-order ops");
        }

        // Vacuous and non-chain units are outside the protocol's domain.
        assertPass(AddressChainProtocol.validate(unit(List.of())),
            "a unit without chain ops passes vacuously");
        assertPass(AddressChainProtocol.validate(unit(List.of(
                constInt(nextOpId(), null, nextValue(), 1)))),
            "a unit with only non-chain ops passes (the protocol owns chains only)");
    }

    // =========================================================================
    // 3. Negative controls: ADDRESS_CHAIN_SHAPE
    // =========================================================================

    private static void testNegativeShapeControls() {
        System.out.println("-- Negative controls: ADDRESS_CHAIN_SHAPE E6005 per defect class --");

        // Wrong child order: the receiver op sits at the value position and
        // vice versa, so the commit's resolved-receiver wiring mismatches the
        // pinned receiver position.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId receiverResult = nextValue();
            ValueId valueResult = nextValue();
            OpId receiverOp = nextOpId();
            OpId valueOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(constInt(valueOp, chainId, valueResult, 9));
            ops.add(constInt(receiverOp, chainId, receiverResult, 1));
            ops.add(opWith(commitOp, SemanticOpKind.MEMBER_WRITE,
                new KindPayload.MemberWritePayload(receiverResult, "k", valueResult),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                    List.of(valueOp, receiverOp, commitOp)),
                valueResult, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "resolved table reference", "MEMBER_WRITE");
        }

        // Wrong child kind: a result-less op at the value position.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId container = nextValue();
            OpId containerOp = nextOpId();
            OpId wrongOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(opWith(containerOp, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, TBL,
                FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(wrongOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(6), 0, null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(commitOp, SemanticOpKind.MEMBER_WRITE,
                new KindPayload.MemberWritePayload(container, "k", container),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.TABLE_SLOT,
                    List.of(containerOp, wrongOp, commitOp)),
                container, TBL, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "value child", "BINDING_STORE", "ValueId result");
        }

        // Wrong boundary kind: VARIABLE_DECLARATION in the VARIABLE boundary slot.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId valueOp = nextOpId();
            OpId boundaryOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_DECLARATION, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainId, value));
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(7), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, boundaryOp, commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "VARIABLE_ASSIGNMENT", "VARIABLE_DECLARATION");
        }

        // Wrong boundary policy: the descriptor-kind rule is violated.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId valueOp = nextOpId();
            OpId boundaryOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.ARRAY_DELETE_BOUNDS, chainId, value));
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(8), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, boundaryOp, commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "descriptor-kind policy", "TYPE_DESCRIPTOR", "ARRAY_DELETE_BOUNDS");
        }

        // Wrong normalize mode: ARRAY_READ on an ARRAY_SLOT write chain.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId container = nextValue();
            ValueId key = nextValue();
            ValueId value = nextValue();
            ValueId length = nextValue();
            ValueId slot = nextValue();
            OpId containerOp = nextOpId();
            OpId keyOp = nextOpId();
            OpId valueOp = nextOpId();
            OpId lengthOp = nextOpId();
            OpId normalizeOp = nextOpId();
            OpId boundaryOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(opWith(containerOp, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, ARR,
                FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(constInt(keyOp, chainId, key, 0));
            ops.add(constInt(valueOp, chainId, value, 9));
            ops.add(opWith(lengthOp, SemanticOpKind.ARRAY_LENGTH,
                new KindPayload.ArrayLengthPayload(container), length, INT,
                FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
                new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_READ, key, length),
                slot, INT, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, chainId, value));
            ops.add(opWith(commitOp, SemanticOpKind.INDEX_WRITE,
                new KindPayload.IndexWritePayload(container, slot, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.ARRAY_SLOT,
                    List.of(containerOp, keyOp, valueOp, lengthOp, normalizeOp, boundaryOp,
                        commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "ARRAY_WRITE", "ARRAY_READ");
        }

        // Missing lengthOp: an ARRAY_SLOT write chain without the ARRAY_LENGTH read.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId container = nextValue();
            ValueId key = nextValue();
            ValueId value = nextValue();
            ValueId slot = nextValue();
            OpId containerOp = nextOpId();
            OpId keyOp = nextOpId();
            OpId valueOp = nextOpId();
            OpId normalizeOp = nextOpId();
            OpId boundaryOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(opWith(containerOp, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)), container, ARR,
                FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(constInt(keyOp, chainId, key, 0));
            ops.add(constInt(valueOp, chainId, value, 9));
            ops.add(opWith(normalizeOp, SemanticOpKind.INDEX_NORMALIZE,
                new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_WRITE, key, key),
                slot, INT, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, chainId, value));
            ops.add(opWith(commitOp, SemanticOpKind.INDEX_WRITE,
                new KindPayload.IndexWritePayload(container, slot, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.ARRAY_SLOT,
                    List.of(containerOp, keyOp, valueOp, normalizeOp, boundaryOp, commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "lengthOp", "ARRAY_LENGTH", "6 children");
        }

        // Commit not last: the BINDING_STORE at the value position.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId commitOp = nextOpId();
            OpId valueOp = nextOpId();
            OpId boundaryOp = nextOpId();
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(9), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainId, value));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(commitOp, valueOp, boundaryOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "value child", "BINDING_STORE");
        }

        // Boundary after the commit: [valueOp, BINDING_STORE, BOUNDARY] —
        // the commit occupies the boundary position and the boundary is last.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId valueOp = nextOpId();
            OpId commitOp = nextOpId();
            OpId boundaryOp = nextOpId();
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(10), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainId, value));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, commitOp, boundaryOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "VARIABLE_ASSIGNMENT", "BINDING_STORE");
        }

        // Missing VARIABLE_ASSIGNMENT boundary: [valueOp, BINDING_STORE] only.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId valueOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(11), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_ADDRESS_CHAIN_SHAPE,
                "VARIABLE_ASSIGNMENT", "2 children");
        }
    }

    // =========================================================================
    // 4. Negative controls: SINGLE_EVALUATION
    // =========================================================================

    private static void testNegativeSingleEvaluationControls() {
        System.out.println("-- Negative controls: SINGLE_EVALUATION E6005 per defect class --");

        // A producing child referenced by two chains (both chains otherwise
        // well-formed VARIABLE shapes).
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainA = nextOpId();
            OpId chainB = nextOpId();
            ValueId shared = nextValue();
            OpId sharedValueOp = nextOpId();
            ops.add(constInt(sharedValueOp, chainA, shared, 7));

            OpId boundaryA = nextOpId();
            OpId commitA = nextOpId();
            ops.add(boundaryWith(boundaryA, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainA, shared));
            ops.add(opWith(commitA, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(12), 1, shared),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainA));
            ops.add(opWith(chainA, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(sharedValueOp, boundaryA, commitA)),
                shared, INT, FailurePolicyId.NO_DEAL_FAILURE, null));

            OpId boundaryB = nextOpId();
            OpId commitB = nextOpId();
            ops.add(boundaryWith(boundaryB, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainB, shared));
            ops.add(opWith(commitB, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(13), 1, shared),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainB));
            ops.add(opWith(chainB, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(sharedValueOp, boundaryB, commitB)),
                shared, INT, FailurePolicyId.NO_DEAL_FAILURE, null));

            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_SINGLE_EVALUATION,
                "referenced by more than one chain", "OpId(");
        }

        // A duplicated producing child op: the same OpId appears twice in the
        // unit's op list.
        {
            List<SemanticOp> ops = new ArrayList<>();
            OpId chainId = nextOpId();
            ValueId value = nextValue();
            OpId valueOp = nextOpId();
            OpId boundaryOp = nextOpId();
            OpId commitOp = nextOpId();
            ops.add(constInt(valueOp, chainId, value, 7));
            ops.add(boundaryWith(boundaryOp, BoundaryKind.VARIABLE_ASSIGNMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, chainId, value));
            ops.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
                new KindPayload.BindingStorePayload(new BindingId(14), 1, value),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
            ops.add(opWith(chainId, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                    List.of(valueOp, boundaryOp, commitOp)),
                value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            // The duplicated producing entry: same OpId, evaluated twice.
            ops.add(constInt(valueOp, null, value, 7));
            assertE6005(AddressChainProtocol.validate(unit(ops)),
                AddressChainProtocol.RULE_SINGLE_EVALUATION,
                "appears more than once", "OpId(");
        }
    }

    // =========================================================================
    // 5. Foundation regression (R-POLICY-KIND pin; the closed set is unchanged)
    // =========================================================================

    private static void testFoundationUnchanged() {
        System.out.println("-- Foundation regression: INDEX_NORMALIZE purity pin and the "
            + "closed 14-condition rule set --");

        // The closed 14-condition rule set is unchanged — the protocol adds no
        // SemanticIrValidator rule.
        check(SemanticIrValidator.RULES.equals(List.of(
                "R-COVERAGE", "R-ENUM", "R-CAPABILITY", "R-POLICY-KIND", "R-BOUNDARY-TRIPLE",
                "R-ELIDED-PLACEMENT", "R-FUNCTION-BINDING", "R-EXTERNAL-ENTRY", "R-ALIAS-CYCLE",
                "R-TOKEN-REUSE", "R-PRIVATE-STEP", "R-RESERVED-NAME", "R-DIGEST", "R-PROFILE"))
                && SemanticIrValidator.RULES.size() == 14,
            "the foundation validator's closed 14-condition rule set is unchanged "
                + "(ADDRESS_CHAIN_SHAPE/SINGLE_EVALUATION are production-time rules, not "
                + "validator rules); got " + SemanticIrValidator.RULES);

        SemanticIrValidator.ComparisonFacts facts =
            new SemanticIrValidator.ComparisonFacts("interface-digest-1",
                SemanticProfile.DEAL_V1_2_INT32, "capability-registry-hash-1");

        // INDEX_NORMALIZE → NO_DEAL_FAILURE stays validator-pinned.
        Optional<CompilerDiagnostic> pass = SemanticIrValidator.validate(unit(List.of(
                opWith(nextOpId(), SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_READ, nextValue(),
                        nextValue()),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null))), facts);
        check(pass.isEmpty(), "INDEX_NORMALIZE with NO_DEAL_FAILURE passes the foundation "
            + "validator (the R-POLICY-KIND pin is unchanged)");

        Optional<CompilerDiagnostic> wrongPolicy = SemanticIrValidator.validate(unit(List.of(
                opWith(nextOpId(), SemanticOpKind.INDEX_NORMALIZE,
                    new KindPayload.IndexNormalizePayload(IndexMode.ARRAY_READ, nextValue(),
                        nextValue()),
                    nextValue(), INT, FailurePolicyId.TYPE_DESCRIPTOR, null))), facts);
        check(wrongPolicy.isPresent() && wrongPolicy.get().message().contains("R-POLICY-KIND"),
            "INDEX_NORMALIZE with a non-NO_DEAL_FAILURE policy still fails R-POLICY-KIND");
    }

    // =========================================================================
    // 6. Determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- Determinism: repeated validation is byte-identical --");

        List<SemanticOp> positive = arrayAssign();
        Optional<CompilerDiagnostic> firstPass = AddressChainProtocol.validate(unit(positive));
        Optional<CompilerDiagnostic> secondPass = AddressChainProtocol.validate(unit(positive));
        check(firstPass.isEmpty() && secondPass.isEmpty(),
            "the positive ARRAY_SLOT chain validates identically across runs");

        List<SemanticOp> negative = new ArrayList<>();
        OpId chainId = nextOpId();
        ValueId value = nextValue();
        OpId valueOp = nextOpId();
        OpId commitOp = nextOpId();
        negative.add(constInt(valueOp, chainId, value, 7));
        negative.add(opWith(commitOp, SemanticOpKind.BINDING_STORE,
            new KindPayload.BindingStorePayload(new BindingId(15), 1, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, chainId));
        negative.add(opWith(chainId, SemanticOpKind.ASSIGN,
            new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                List.of(valueOp, commitOp)),
            value, INT, FailurePolicyId.NO_DEAL_FAILURE, null));
        Optional<CompilerDiagnostic> first = AddressChainProtocol.validate(unit(negative));
        Optional<CompilerDiagnostic> second = AddressChainProtocol.validate(unit(negative));
        check(first.isPresent() && second.isPresent()
                && first.get().message().equals(second.get().message()),
            "the negative E6005 diagnostic is byte-identical across runs; got \""
                + (first.isPresent() ? first.get().message() : "") + "\" vs \""
                + (second.isPresent() ? second.get().message() : "") + "\"");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Address Chain Protocol Test (ISSUE-0234 A-D1/A-D3/A-D9) ===\n");

        testNormalizedSlot();
        testPositiveShapes();
        testPositiveComposition();
        testNegativeShapeControls();
        testNegativeSingleEvaluationControls();
        testFoundationUnchanged();
        testDeterminism();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
