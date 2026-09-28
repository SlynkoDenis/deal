package deal.semantic.ir;

import deal.diagnostics.CompilerDiagnostic;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * The closed address-chain shape authority of {@code deal.semantic-ir/1}
 * (assignment-delete-address-chains A-D1/A-D3/A-D9; parent
 * common-semantic-lowering-layer D14): a static, pure, deterministic
 * production-time validation of every {@code ASSIGN}/{@code DELETE} op of
 * a lowered unit against the closed per-target chain shapes.
 *
 * <p><b>Closed shapes (A-D9, exact).</b> {@code ASSIGN}:
 * {@code VARIABLE} = {@code [valueOp, (adapterChild)?,
 * boundaryOp(VARIABLE_ASSIGNMENT), commitOp(BINDING_STORE)]};
 * {@code TABLE_SLOT} member write = {@code [containerOp, valueOp,
 * commitOp(MEMBER_WRITE)]} (the member key is a literal string — no
 * keyOp); {@code TABLE_SLOT} index write = {@code [containerOp, keyOp,
 * valueOp, normalizeOp(TABLE_WRITE), commitOp(INDEX_WRITE)]};
 * {@code ARRAY_SLOT} write = {@code [containerOp, keyOp, valueOp,
 * lengthOp, normalizeOp(ARRAY_WRITE), boundaryOp, commitOp(INDEX_WRITE)]}
 * with the lengthOp an {@code ARRAY_LENGTH} read of the resolved
 * receiver; {@code BYTES_SLOT} write (K6 item 4) = the array shape's
 * exact mirror with the lengthOp an {@code ARRAY_LENGTH} read of the
 * resolved byte receiver, the normalize mode {@code BYTES_WRITE}, and
 * the {@code BYTE_ELEMENT_ASSIGNMENT} + {@code BYTES_WRITE} boundary;
 * {@code CLASS_FIELD} write = {@code [containerOp, valueOp,
 * commitOp(FIELD_WRITE)]}. {@code DELETE}: {@code TABLE_SLOT} member =
 * {@code [containerOp, commitOp(MEMBER_DELETE)]}; {@code TABLE_SLOT}
 * index = {@code [containerOp, keyOp, normalizeOp(TABLE_WRITE),
 * commitOp(INDEX_DELETE)]}; {@code CLASS_FIELD} = {@code [containerOp,
 * commitOp(FIELD_DELETE)]}; {@code ARRAY_SLOT} = {@code [containerOp,
 * keyOp, lengthOp, normalizeOp(ARRAY_WRITE), boundaryOp,
 * commitOp(INDEX_DELETE)]}. Delete chains carry no RHS and use the
 * write-mode normalize ({@code ARRAY_WRITE}/{@code TABLE_WRITE}) — delete
 * is a mutation context and the closed {@link IndexMode} set is not
 * extended.</p>
 *
 * <p><b>Boundary children (A-D4, closed).</b> The {@code ARRAY_SLOT}
 * write boundary must carry kind {@code ARRAY_ELEMENT_ASSIGNMENT} with
 * policy {@code ARRAY_WRITE_BOUNDS_THEN_ELEMENT} and input = the checked
 * RHS value ({@code valueOp}'s result); the {@code ARRAY_SLOT} delete
 * boundary must carry kind {@code ARRAY_ELEMENT_DELETE} with policy
 * {@code ARRAY_DELETE_BOUNDS} and input = the normalized index
 * ({@code normalizeOp}'s result); the {@code BYTES_SLOT} write boundary
 * must carry kind {@code BYTE_ELEMENT_ASSIGNMENT} with policy
 * {@code BYTES_WRITE} and input = the checked RHS value. A {@code VARIABLE} chain's single
 * boundary must carry kind {@code VARIABLE_ASSIGNMENT} with the
 * descriptor-kind policy — {@code TYPE_DESCRIPTOR} for non-function
 * descriptors, {@code FUNCTION_SIGNATURE} for function descriptors — and
 * input = the committed value (the {@code valueOp} result, or the
 * {@code FUNCTION_ADAPT} adapter child's result for adapter chains). The
 * boundary's descriptor is the declared target descriptor by construction
 * (the chain-lowering task produces it from the checked target type
 * through the DescriptorService; this protocol produces no descriptors and
 * validates the closed kind/policy pairing over the declared descriptor
 * the boundary carries). {@code TABLE_SLOT} and {@code CLASS_FIELD}
 * chains carry zero write-check boundaries.</p>
 *
 * <p><b>Normalize and commit (A-D3/A-D5).</b> The normalize child is
 * {@code INDEX_NORMALIZE} with policy {@code NO_DEAL_FAILURE} (purity —
 * it never raises E8002 and never enforces bounds) and the closed mode:
 * {@code ARRAY_WRITE} on {@code ARRAY_SLOT} chains, {@code BYTES_WRITE}
 * on {@code BYTES_SLOT} chains, {@code TABLE_WRITE}
 * on {@code TABLE_SLOT} index chains. For array chains the normalize's
 * {@code rawKey} references the key child's result and its
 * {@code currentLength} references the length child's result (the length
 * read pins at normalize time, after key and RHS); for table chains
 * {@code rawKey} and the unused {@code currentLength} both reference the
 * key child's result (no length read occurs for table targets). The
 * commit child is always last, exactly one per chain, and its payload
 * references only the resolved receiver/key/slot/value results produced
 * by the chain's own children — it never re-evaluates a source
 * expression. Every child records the chain op as its
 * {@code parentOpId} (A-D2).</p>
 *
 * <p><b>Single evaluation (A-D1/A-D8).</b> Each producing child appears
 * exactly once in the unit's op list and is referenced by exactly one
 * chain; a duplicated op entry or a child shared by two chains would
 * execute a source expression more than once and is rejected.</p>
 *
 * <p><b>Reporting.</b> A violation is E6005 through
 * {@link FailureContractRegistry} with a {@link LoweringFailureDetail}
 * naming the module, capability {@code EVALUATION_ORDER}, the pinned rule
 * {@link #RULE_ADDRESS_CHAIN_SHAPE} or {@link #RULE_SINGLE_EVALUATION},
 * profile {@code DEAL_V1_2_INT32}, IR version
 * {@code deal.semantic-ir/1}, and the offending op origin. The foundation
 * validator's closed 14-condition rule set is unchanged: chain-shape
 * validation is a production-time check in exactly the slot the foundation
 * reserved ({@code SemanticIrValidator} javadoc — ownership cycles, bad
 * dominance, invalid exits, … are the construct epics' production-time
 * checks), never new {@code SemanticIrValidator} rules.</p>
 *
 * <p><b>Order and purity.</b> Deterministic first-failure order: the
 * single-evaluation pass first (the unit's op list in op order, then the
 * chains' child lists in op order), then the chain-shape pass over the
 * {@code ASSIGN}/{@code DELETE} ops in op order with positional checks in
 * child-list order. The single-evaluation pass runs first because a child
 * shared by two chains can otherwise only surface as a parentage mismatch
 * on the second chain — the pinned {@code SINGLE_EVALUATION} rule owns
 * multiplicity defects. Validation is linear in chain length, mutates
 * nothing, and interprets only the validated unit and the closed shapes;
 * no host code executes.</p>
 */
public final class AddressChainProtocol {

    /** The ADDRESS_CHAIN_SHAPE rule: a chain violating the closed A-D9 shapes. */
    public static final String RULE_ADDRESS_CHAIN_SHAPE = "ADDRESS_CHAIN_SHAPE";

    /** The SINGLE_EVALUATION rule: a producing child evaluated more than once. */
    public static final String RULE_SINGLE_EVALUATION = "SINGLE_EVALUATION";

    private AddressChainProtocol() {
        // Static surface only; pure and stateless.
    }

    // =========================================================================
    // Public surface
    // =========================================================================

    /**
     * Validates every {@code ASSIGN}/{@code DELETE} op of the unit against
     * the closed A-D9 chain shapes and the single-evaluation invariants.
     * Returns empty on pass and exactly one E6005 diagnostic naming the
     * first failing rule on failure. Pure, deterministic, no mutation; a
     * unit without chain ops passes vacuously (non-chain ops are outside
     * this authority's domain).
     *
     * @param unit the lowered unit; non-null
     * @return empty on pass, otherwise the first E6005
     * @throws NullPointerException if {@code unit} is null
     */
    public static Optional<CompilerDiagnostic> validate(LoweredModuleUnit unit) {
        Objects.requireNonNull(unit, "unit must not be null");

        // Pass 1 — single evaluation (the pinned order: multiplicity
        // defects are this rule's regardless of any shape defect).
        Optional<CompilerDiagnostic> singleEvaluation = checkSingleEvaluation(unit);
        if (singleEvaluation.isPresent()) {
            return singleEvaluation;
        }

        // Pass 2 — chain shape, chains in op order, positions in order.
        Map<OpId, SemanticOp> ops = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            ops.put(op.opId(), op);
        }
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.ASSIGN || op.kind() == SemanticOpKind.DELETE) {
                Optional<CompilerDiagnostic> shape = checkChainShape(unit, op, ops);
                if (shape.isPresent()) {
                    return shape;
                }
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // Single evaluation (A-D1/A-D8)
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkSingleEvaluation(LoweredModuleUnit unit) {
        // (a) Each op appears exactly once in the unit's op list: a
        // duplicated entry would execute the op — and its source
        // expression — more than once.
        Map<OpId, SemanticOp> seen = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            if (seen.put(op.opId(), op) != null) {
                return fail(unit, RULE_SINGLE_EVALUATION, op,
                    "the op " + op.opId() + " appears more than once in the unit's op list "
                        + "(a duplicated op would evaluate its source expression more than "
                        + "once)");
            }
        }
        // (b) Each chain child is referenced by exactly one chain, once:
        // a child shared by two chains (or listed twice in one chain)
        // would be evaluated more than once.
        Map<OpId, OpId> owner = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            List<OpId> children = childOps(op);
            for (OpId child : children) {
                OpId previous = owner.putIfAbsent(child, op.opId());
                if (previous != null) {
                    return fail(unit, RULE_SINGLE_EVALUATION, op,
                        "the producing child " + child + " is referenced by more than one "
                            + "chain"
                            + (previous.equals(op.opId())
                                ? " (listed more than once in chain " + op.opId() + ")"
                                : " (by chain " + previous + " and by chain " + op.opId()
                                    + ")"));
                }
            }
        }
        return Optional.empty();
    }

    private static List<OpId> childOps(SemanticOp op) {
        if (op.payload() instanceof KindPayload.AssignPayload assign) {
            return assign.childOps();
        }
        if (op.payload() instanceof KindPayload.DeletePayload delete) {
            return delete.childOps();
        }
        return List.of();
    }

    // =========================================================================
    // Chain shape (A-D1/A-D9)
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkChainShape(LoweredModuleUnit unit,
                                                                SemanticOp chain,
                                                                Map<OpId, SemanticOp> ops) {
        List<OpId> children = childOps(chain);
        for (OpId child : children) {
            if (chain.opId().equals(child)) {
                return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                    "the chain lists itself as a child (op " + chain.opId() + ")");
            }
        }
        return switch (chain.kind()) {
            case ASSIGN -> {
                KindPayload.AssignPayload payload =
                    (KindPayload.AssignPayload) chain.payload();
                yield switch (payload.targetKind()) {
                    case VARIABLE -> checkVariableAssign(unit, chain, payload.childOps(), ops);
                    case TABLE_SLOT -> checkTableAssign(unit, chain, payload.childOps(), ops);
                    case ARRAY_SLOT -> checkArrayAssign(unit, chain, payload.childOps(), ops);
                    case BYTES_SLOT -> checkBytesAssign(unit, chain, payload.childOps(), ops);
                    case CLASS_FIELD -> checkClassFieldAssign(unit, chain, payload.childOps(),
                        ops);
                };
            }
            case DELETE -> {
                KindPayload.DeletePayload payload =
                    (KindPayload.DeletePayload) chain.payload();
                yield switch (payload.targetKind()) {
                    case TABLE_SLOT -> checkTableDelete(unit, chain, payload.childOps(), ops);
                    case ARRAY_SLOT -> checkArrayDelete(unit, chain, payload.childOps(), ops);
                    case CLASS_FIELD -> checkClassFieldDelete(unit, chain, payload.childOps(),
                        ops);
                };
            }
            default -> Optional.empty();
        };
    }

    // -- ASSIGN VARIABLE -------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkVariableAssign(LoweredModuleUnit unit,
                                                                    SemanticOp chain,
                                                                    List<OpId> children,
                                                                    Map<OpId, SemanticOp> ops) {
        if (children.size() != 3 && children.size() != 4) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed ASSIGN VARIABLE chain shape with " + children.size() + " children; "
                    + "the closed shapes are [valueOp, VARIABLE_ASSIGNMENT boundaryOp, "
                    + "BINDING_STORE commitOp] and [valueOp, FUNCTION_ADAPT adapterOp, "
                    + "VARIABLE_ASSIGNMENT boundaryOp, BINDING_STORE commitOp]");
        }
        boolean adapter = children.size() == 4;
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        int boundaryPos = adapter ? 2 : 1;
        int commitPos = adapter ? 3 : 2;

        // valueOp — the committed value's producer.
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "value");
        if (failure.isPresent()) {
            return failure;
        }
        ValueId committed = (ValueId) c[0].result();

        // adapterChild (E6's reserved slot; FUNCTION_ADAPT only).
        if (adapter) {
            failure = requireParentage(unit, chain, c[1], 1);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireKind(unit, chain, c[1], SemanticOpKind.FUNCTION_ADAPT, 1,
                "adapter");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[1], 1, "adapter");
            if (failure.isPresent()) {
                return failure;
            }
            committed = (ValueId) c[1].result();
        }

        // boundaryOp — exactly one VARIABLE_ASSIGNMENT under the
        // descriptor-kind rule, input = the committed value.
        failure = requireParentage(unit, chain, c[boundaryPos], boundaryPos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[boundaryPos], SemanticOpKind.BOUNDARY,
            boundaryPos, "VARIABLE_ASSIGNMENT boundary");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.BoundaryPayload boundary =
            (KindPayload.BoundaryPayload) c[boundaryPos].payload();
        if (boundary.kind() != BoundaryKind.VARIABLE_ASSIGNMENT) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the VARIABLE chain boundary at position " + boundaryPos + " must carry "
                    + "kind VARIABLE_ASSIGNMENT, got " + boundary.kind());
        }
        FailurePolicyId expectedPolicy = descriptorKindPolicy(boundary.descriptor());
        if (c[boundaryPos].failurePolicy() != expectedPolicy) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the VARIABLE_ASSIGNMENT boundary at position " + boundaryPos + " must carry "
                    + "the descriptor-kind policy " + expectedPolicy.name()
                    + " for the declared descriptor " + boundary.descriptor().canonicalSpecText()
                    + ", got " + c[boundaryPos].failurePolicy().name());
        }
        failure = requireEqual(unit, chain, boundary.input(), committed,
            "the VARIABLE_ASSIGNMENT boundary's input (the committed value)");
        if (failure.isPresent()) {
            return failure;
        }

        // commitOp — exactly one BINDING_STORE, last, storing the
        // committed value.
        failure = requireParentage(unit, chain, c[commitPos], commitPos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[commitPos], SemanticOpKind.BINDING_STORE,
            commitPos, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.BindingStorePayload store =
            (KindPayload.BindingStorePayload) c[commitPos].payload();
        return requireEqual(unit, chain, store.value(), committed,
            "the BINDING_STORE commit's stored value");
    }

    // -- ASSIGN TABLE_SLOT -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkTableAssign(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 List<OpId> children,
                                                                 Map<OpId, SemanticOp> ops) {
        if (children.size() == 3) {
            // Member write: [containerOp, valueOp, MEMBER_WRITE].
            CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
            SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
            if (childFailure[0] != null) {
                return Optional.of(childFailure[0]);
            }
            Optional<CompilerDiagnostic> failure;
            failure = requireParentage(unit, chain, c[0], 0);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[0], 0, "receiver");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[1], 1);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[1], 1, "value");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[2], 2);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireKind(unit, chain, c[2], SemanticOpKind.MEMBER_WRITE, 2, "commit");
            if (failure.isPresent()) {
                return failure;
            }
            KindPayload.MemberWritePayload write =
                (KindPayload.MemberWritePayload) c[2].payload();
            failure = requireEqual(unit, chain, write.table(), (ValueId) c[0].result(),
                "the MEMBER_WRITE commit's resolved table reference");
            if (failure.isPresent()) {
                return failure;
            }
            return requireEqual(unit, chain, write.value(), (ValueId) c[1].result(),
                "the MEMBER_WRITE commit's stored value");
        }
        if (children.size() == 5) {
            // Index write: [containerOp, keyOp, valueOp,
            // normalizeOp(TABLE_WRITE), INDEX_WRITE].
            CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
            SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
            if (childFailure[0] != null) {
                return Optional.of(childFailure[0]);
            }
            Optional<CompilerDiagnostic> failure;
            failure = requireParentage(unit, chain, c[0], 0);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[0], 0, "receiver");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[1], 1);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[1], 1, "key");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireResultType(unit, chain, c[1],
                RuntimeDescriptor.String.INSTANCE,
                "the table key child at position 1");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[2], 2);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[2], 2, "value");
            if (failure.isPresent()) {
                return failure;
            }
            failure = checkTableNormalize(unit, chain, c, 3);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[4], 4);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireKind(unit, chain, c[4], SemanticOpKind.INDEX_WRITE, 4, "commit");
            if (failure.isPresent()) {
                return failure;
            }
            KindPayload.IndexWritePayload write =
                (KindPayload.IndexWritePayload) c[4].payload();
            failure = requireEqual(unit, chain, write.container(), (ValueId) c[0].result(),
                "the INDEX_WRITE commit's resolved container reference");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireEqual(unit, chain, write.slot(), (ValueId) c[3].result(),
                "the INDEX_WRITE commit's resolved slot reference");
            if (failure.isPresent()) {
                return failure;
            }
            return requireEqual(unit, chain, write.value(), (ValueId) c[2].result(),
                "the INDEX_WRITE commit's stored value");
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            "no closed ASSIGN TABLE_SLOT chain shape with " + children.size() + " children; "
                + "the closed shapes are [containerOp, valueOp, MEMBER_WRITE commitOp] "
                + "(member, literal string key) and [containerOp, keyOp, valueOp, "
                + "INDEX_NORMALIZE(TABLE_WRITE), INDEX_WRITE commitOp] (index)");
    }

    /** The shared TABLE_WRITE normalize of a table index chain (write or delete). */
    private static Optional<CompilerDiagnostic> checkTableNormalize(LoweredModuleUnit unit,
                                                                    SemanticOp chain,
                                                                    SemanticOp[] c,
                                                                    int normalizePos) {
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[normalizePos], normalizePos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[normalizePos], SemanticOpKind.INDEX_NORMALIZE,
            normalizePos, "normalize");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.IndexNormalizePayload normalize =
            (KindPayload.IndexNormalizePayload) c[normalizePos].payload();
        if (normalize.mode() != IndexMode.TABLE_WRITE) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the table chain normalize at position " + normalizePos + " must carry mode "
                    + "TABLE_WRITE (delete is a mutation context; the closed IndexMode set is "
                    + "not extended), got " + normalize.mode());
        }
        failure = requirePolicy(unit, chain, c[normalizePos], FailurePolicyId.NO_DEAL_FAILURE,
            "the INDEX_NORMALIZE child (purity: it never raises a DEAL failure)");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[normalizePos], normalizePos, "normalize");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[normalizePos],
            RuntimeDescriptor.String.INSTANCE,
            "the INDEX_NORMALIZE child at position " + normalizePos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireEqual(unit, chain, normalize.rawKey(), (ValueId) c[1].result(),
            "the INDEX_NORMALIZE child's rawKey");
        if (failure.isPresent()) {
            return failure;
        }
        // The closed payload's required currentLength operand references
        // the raw key identity and is unused — no length read occurs for
        // table targets (A-D3).
        return requireEqual(unit, chain, normalize.currentLength(), (ValueId) c[1].result(),
            "the INDEX_NORMALIZE child's currentLength (unused for table targets; it must "
                + "reference the raw key identity)");
    }

    // -- ASSIGN ARRAY_SLOT -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkArrayAssign(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 List<OpId> children,
                                                                 Map<OpId, SemanticOp> ops) {
        if (children.size() != 7) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed ASSIGN ARRAY_SLOT chain shape with " + children.size() + " children; "
                    + "the closed shape is [containerOp, keyOp, valueOp, "
                    + "lengthOp(ARRAY_LENGTH), normalizeOp(INDEX_NORMALIZE ARRAY_WRITE), "
                    + "boundaryOp(ARRAY_ELEMENT_ASSIGNMENT + ARRAY_WRITE_BOUNDS_THEN_ELEMENT), "
                    + "commitOp(INDEX_WRITE)]");
        }
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "receiver");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[1], 1);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[1], 1, "key");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[1], RuntimeDescriptor.Int.INSTANCE,
            "the array key child at position 1");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[2], 2);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[2], 2, "value");
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkArrayLengthAndNormalize(unit, chain, c, 3, 4, 5);
        if (failure.isPresent()) {
            return failure;
        }
        // boundaryOp — ARRAY_ELEMENT_ASSIGNMENT + ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
        // input = the checked RHS value.
        failure = requireParentage(unit, chain, c[5], 5);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[5], SemanticOpKind.BOUNDARY, 5,
            "ARRAY_ELEMENT_ASSIGNMENT boundary");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.BoundaryPayload boundary = (KindPayload.BoundaryPayload) c[5].payload();
        if (boundary.kind() != BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the ARRAY_SLOT write boundary at position 5 must carry kind "
                    + "ARRAY_ELEMENT_ASSIGNMENT, got " + boundary.kind());
        }
        if (c[5].failurePolicy() != FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the ARRAY_ELEMENT_ASSIGNMENT boundary at position 5 must carry policy "
                    + "ARRAY_WRITE_BOUNDS_THEN_ELEMENT, got " + c[5].failurePolicy().name());
        }
        failure = requireEqual(unit, chain, boundary.input(), (ValueId) c[2].result(),
            "the ARRAY_ELEMENT_ASSIGNMENT boundary's input (the checked RHS value)");
        if (failure.isPresent()) {
            return failure;
        }
        // commitOp — INDEX_WRITE, last.
        failure = requireParentage(unit, chain, c[6], 6);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[6], SemanticOpKind.INDEX_WRITE, 6, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.IndexWritePayload write = (KindPayload.IndexWritePayload) c[6].payload();
        failure = requireEqual(unit, chain, write.container(), (ValueId) c[0].result(),
            "the INDEX_WRITE commit's resolved container reference");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireEqual(unit, chain, write.slot(), (ValueId) c[4].result(),
            "the INDEX_WRITE commit's resolved slot reference");
        if (failure.isPresent()) {
            return failure;
        }
        return requireEqual(unit, chain, write.value(), (ValueId) c[2].result(),
            "the INDEX_WRITE commit's stored value");
    }

    /**
     * ASSIGN BYTES_SLOT write — the array chain's exact mirror (K6 item
     * 4): {@code [containerOp, keyOp, valueOp,
     * lengthOp(ARRAY_LENGTH over the byte receiver),
     * normalizeOp(INDEX_NORMALIZE BYTES_WRITE),
     * boundaryOp(BYTE_ELEMENT_ASSIGNMENT + BYTES_WRITE),
     * commitOp(INDEX_WRITE)]}. The boundary enforces the pinned E8012
     * bounds ({@code index < 0} or {@code index >= b.length}) with input =
     * the checked RHS value; the commit enforces the E8013 value range
     * (0..255) before the single mutation. There is no bytes delete shape
     * ({@code delete b[i]} is the checker's E3007 rejection).
     */
    private static Optional<CompilerDiagnostic> checkBytesAssign(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 List<OpId> children,
                                                                 Map<OpId, SemanticOp> ops) {
        if (children.size() != 7) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed ASSIGN BYTES_SLOT chain shape with " + children.size()
                    + " children; the closed shape is [containerOp, keyOp, valueOp, "
                    + "lengthOp(ARRAY_LENGTH), normalizeOp(INDEX_NORMALIZE BYTES_WRITE), "
                    + "boundaryOp(BYTE_ELEMENT_ASSIGNMENT + BYTES_WRITE), "
                    + "commitOp(INDEX_WRITE)]");
        }
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "receiver");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[1], 1);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[1], 1, "key");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[1], RuntimeDescriptor.Int.INSTANCE,
            "the bytes key child at position 1");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[2], 2);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[2], 2, "value");
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkIndexLengthAndNormalize(unit, chain, c, 3, 4, IndexMode.BYTES_WRITE);
        if (failure.isPresent()) {
            return failure;
        }
        // boundaryOp — BYTE_ELEMENT_ASSIGNMENT + BYTES_WRITE,
        // input = the checked RHS value.
        failure = requireParentage(unit, chain, c[5], 5);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[5], SemanticOpKind.BOUNDARY, 5,
            "BYTE_ELEMENT_ASSIGNMENT boundary");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.BoundaryPayload boundary = (KindPayload.BoundaryPayload) c[5].payload();
        if (boundary.kind() != BoundaryKind.BYTE_ELEMENT_ASSIGNMENT) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the BYTES_SLOT write boundary at position 5 must carry kind "
                    + "BYTE_ELEMENT_ASSIGNMENT, got " + boundary.kind());
        }
        if (c[5].failurePolicy() != FailurePolicyId.BYTES_WRITE) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the BYTE_ELEMENT_ASSIGNMENT boundary at position 5 must carry policy "
                    + "BYTES_WRITE, got " + c[5].failurePolicy().name());
        }
        failure = requireEqual(unit, chain, boundary.input(), (ValueId) c[2].result(),
            "the BYTE_ELEMENT_ASSIGNMENT boundary's input (the checked RHS value)");
        if (failure.isPresent()) {
            return failure;
        }
        // commitOp — INDEX_WRITE, last.
        failure = requireParentage(unit, chain, c[6], 6);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[6], SemanticOpKind.INDEX_WRITE, 6, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.IndexWritePayload write = (KindPayload.IndexWritePayload) c[6].payload();
        failure = requireEqual(unit, chain, write.container(), (ValueId) c[0].result(),
            "the INDEX_WRITE commit's resolved container reference");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireEqual(unit, chain, write.slot(), (ValueId) c[4].result(),
            "the INDEX_WRITE commit's resolved slot reference");
        if (failure.isPresent()) {
            return failure;
        }
        return requireEqual(unit, chain, write.value(), (ValueId) c[2].result(),
            "the INDEX_WRITE commit's stored value");
    }

    /**
     * The shared length read + ARRAY_WRITE normalize of an array chain
     * (write or delete): positions {@code lengthPos} (ARRAY_LENGTH of the
     * resolved receiver) and {@code normalizePos} (INDEX_NORMALIZE
     * ARRAY_WRITE of the key result against the read length).
     */
    private static Optional<CompilerDiagnostic> checkArrayLengthAndNormalize(
            LoweredModuleUnit unit, SemanticOp chain, SemanticOp[] c, int lengthPos,
            int normalizePos, int boundaryPos) {
        return checkIndexLengthAndNormalize(unit, chain, c, lengthPos, normalizePos,
            IndexMode.ARRAY_WRITE);
    }

    /**
     * The shared length read + write normalize of an index chain (array or
     * bytes; K6 item 4): positions {@code lengthPos} (ARRAY_LENGTH of the
     * resolved receiver) and {@code normalizePos} (INDEX_NORMALIZE of the
     * key result against the read length) under the expected write mode.
     */
    private static Optional<CompilerDiagnostic> checkIndexLengthAndNormalize(
            LoweredModuleUnit unit, SemanticOp chain, SemanticOp[] c, int lengthPos,
            int normalizePos, IndexMode expectedMode) {
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[lengthPos], lengthPos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[lengthPos], SemanticOpKind.ARRAY_LENGTH,
            lengthPos, "length");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[lengthPos], lengthPos, "length");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[lengthPos], RuntimeDescriptor.Int.INSTANCE,
            "the ARRAY_LENGTH child at position " + lengthPos);
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.ArrayLengthPayload length =
            (KindPayload.ArrayLengthPayload) c[lengthPos].payload();
        failure = requireEqual(unit, chain, length.arrayValue(), (ValueId) c[0].result(),
            "the ARRAY_LENGTH child's array reference (the resolved receiver)");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[normalizePos], normalizePos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[normalizePos], SemanticOpKind.INDEX_NORMALIZE,
            normalizePos, "normalize");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.IndexNormalizePayload normalize =
            (KindPayload.IndexNormalizePayload) c[normalizePos].payload();
        if (normalize.mode() != expectedMode) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the chain normalize at position " + normalizePos + " must carry mode "
                    + expectedMode + " (delete is a mutation context; the closed IndexMode "
                    + "set is not extended), got " + normalize.mode());
        }
        failure = requirePolicy(unit, chain, c[normalizePos], FailurePolicyId.NO_DEAL_FAILURE,
            "the INDEX_NORMALIZE child (purity: it never raises a DEAL failure, never E8002)");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[normalizePos], normalizePos, "normalize");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[normalizePos], RuntimeDescriptor.Int.INSTANCE,
            "the INDEX_NORMALIZE child at position " + normalizePos);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireEqual(unit, chain, normalize.rawKey(), (ValueId) c[1].result(),
            "the INDEX_NORMALIZE child's rawKey");
        if (failure.isPresent()) {
            return failure;
        }
        // The length read pins at normalize time (after key and RHS): the
        // normalize's currentLength must be the length child's result.
        return requireEqual(unit, chain, normalize.currentLength(), (ValueId) c[lengthPos].result(),
            "the INDEX_NORMALIZE child's currentLength (the length read at normalize time)");
    }

    // -- ASSIGN CLASS_FIELD ----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkClassFieldAssign(LoweredModuleUnit unit,
                                                                      SemanticOp chain,
                                                                      List<OpId> children,
                                                                      Map<OpId, SemanticOp> ops) {
        if (children.size() != 3) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed ASSIGN CLASS_FIELD chain shape with " + children.size()
                    + " children; the closed shape is [containerOp, valueOp, FIELD_WRITE "
                    + "commitOp]");
        }
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "receiver");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[1], 1);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[1], 1, "value");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[2], 2);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[2], SemanticOpKind.FIELD_WRITE, 2, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.FieldWritePayload write = (KindPayload.FieldWritePayload) c[2].payload();
        failure = requireEqual(unit, chain, write.classValue(), (ValueId) c[0].result(),
            "the FIELD_WRITE commit's resolved class value reference");
        if (failure.isPresent()) {
            return failure;
        }
        return requireEqual(unit, chain, write.value(), (ValueId) c[1].result(),
            "the FIELD_WRITE commit's stored value");
    }

    // -- DELETE TABLE_SLOT -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkTableDelete(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 List<OpId> children,
                                                                 Map<OpId, SemanticOp> ops) {
        if (children.size() == 2) {
            // Member delete: [containerOp, MEMBER_DELETE].
            CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
            SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
            if (childFailure[0] != null) {
                return Optional.of(childFailure[0]);
            }
            Optional<CompilerDiagnostic> failure;
            failure = requireParentage(unit, chain, c[0], 0);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[0], 0, "receiver");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[1], 1);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireKind(unit, chain, c[1], SemanticOpKind.MEMBER_DELETE, 1, "commit");
            if (failure.isPresent()) {
                return failure;
            }
            KindPayload.MemberDeletePayload delete =
                (KindPayload.MemberDeletePayload) c[1].payload();
            return requireEqual(unit, chain, delete.table(), (ValueId) c[0].result(),
                "the MEMBER_DELETE commit's resolved table reference");
        }
        if (children.size() == 4) {
            // Index delete: [containerOp, keyOp, normalizeOp(TABLE_WRITE),
            // INDEX_DELETE].
            CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
            SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
            if (childFailure[0] != null) {
                return Optional.of(childFailure[0]);
            }
            Optional<CompilerDiagnostic> failure;
            failure = requireParentage(unit, chain, c[0], 0);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[0], 0, "receiver");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[1], 1);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireValueResult(unit, chain, c[1], 1, "key");
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireResultType(unit, chain, c[1],
                RuntimeDescriptor.String.INSTANCE,
                "the table key child at position 1");
            if (failure.isPresent()) {
                return failure;
            }
            failure = checkTableNormalize(unit, chain, c, 2);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireParentage(unit, chain, c[3], 3);
            if (failure.isPresent()) {
                return failure;
            }
            failure = requireKind(unit, chain, c[3], SemanticOpKind.INDEX_DELETE, 3, "commit");
            if (failure.isPresent()) {
                return failure;
            }
            KindPayload.IndexDeletePayload delete =
                (KindPayload.IndexDeletePayload) c[3].payload();
            failure = requireEqual(unit, chain, delete.container(), (ValueId) c[0].result(),
                "the INDEX_DELETE commit's resolved container reference");
            if (failure.isPresent()) {
                return failure;
            }
            return requireEqual(unit, chain, delete.slot(), (ValueId) c[2].result(),
                "the INDEX_DELETE commit's resolved slot reference");
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            "no closed DELETE TABLE_SLOT chain shape with " + children.size() + " children; "
                + "the closed shapes are [containerOp, MEMBER_DELETE commitOp] (member, "
                + "literal string key) and [containerOp, keyOp, "
                + "INDEX_NORMALIZE(TABLE_WRITE), INDEX_DELETE commitOp] (index)");
    }

    // -- DELETE ARRAY_SLOT -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkArrayDelete(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 List<OpId> children,
                                                                 Map<OpId, SemanticOp> ops) {
        if (children.size() != 6) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed DELETE ARRAY_SLOT chain shape with " + children.size() + " children; "
                    + "the closed shape is [containerOp, keyOp, lengthOp(ARRAY_LENGTH), "
                    + "normalizeOp(INDEX_NORMALIZE ARRAY_WRITE), "
                    + "boundaryOp(ARRAY_ELEMENT_DELETE + ARRAY_DELETE_BOUNDS), "
                    + "commitOp(INDEX_DELETE)]");
        }
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "receiver");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[1], 1);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[1], 1, "key");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireResultType(unit, chain, c[1], RuntimeDescriptor.Int.INSTANCE,
            "the array key child at position 1");
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkArrayLengthAndNormalize(unit, chain, c, 2, 3, 4);
        if (failure.isPresent()) {
            return failure;
        }
        // boundaryOp — ARRAY_ELEMENT_DELETE + ARRAY_DELETE_BOUNDS,
        // input = the normalized index.
        failure = requireParentage(unit, chain, c[4], 4);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[4], SemanticOpKind.BOUNDARY, 4,
            "ARRAY_ELEMENT_DELETE boundary");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.BoundaryPayload boundary = (KindPayload.BoundaryPayload) c[4].payload();
        if (boundary.kind() != BoundaryKind.ARRAY_ELEMENT_DELETE) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the ARRAY_SLOT delete boundary at position 4 must carry kind "
                    + "ARRAY_ELEMENT_DELETE, got " + boundary.kind());
        }
        if (c[4].failurePolicy() != FailurePolicyId.ARRAY_DELETE_BOUNDS) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "the ARRAY_ELEMENT_DELETE boundary at position 4 must carry policy "
                    + "ARRAY_DELETE_BOUNDS, got " + c[4].failurePolicy().name());
        }
        failure = requireEqual(unit, chain, boundary.input(), (ValueId) c[3].result(),
            "the ARRAY_ELEMENT_DELETE boundary's input (the normalized index)");
        if (failure.isPresent()) {
            return failure;
        }
        // commitOp — INDEX_DELETE, last.
        failure = requireParentage(unit, chain, c[5], 5);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[5], SemanticOpKind.INDEX_DELETE, 5, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.IndexDeletePayload delete = (KindPayload.IndexDeletePayload) c[5].payload();
        failure = requireEqual(unit, chain, delete.container(), (ValueId) c[0].result(),
            "the INDEX_DELETE commit's resolved container reference");
        if (failure.isPresent()) {
            return failure;
        }
        return requireEqual(unit, chain, delete.slot(), (ValueId) c[3].result(),
            "the INDEX_DELETE commit's resolved slot reference");
    }

    // -- DELETE CLASS_FIELD ----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkClassFieldDelete(LoweredModuleUnit unit,
                                                                      SemanticOp chain,
                                                                      List<OpId> children,
                                                                      Map<OpId, SemanticOp> ops) {
        if (children.size() != 2) {
            return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                "no closed DELETE CLASS_FIELD chain shape with " + children.size()
                    + " children; the closed shape is [containerOp, FIELD_DELETE commitOp]");
        }
        CompilerDiagnostic[] childFailure = new CompilerDiagnostic[1];
        SemanticOp[] c = resolveChildren(unit, chain, children, ops, childFailure);
        if (childFailure[0] != null) {
            return Optional.of(childFailure[0]);
        }
        Optional<CompilerDiagnostic> failure;
        failure = requireParentage(unit, chain, c[0], 0);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireValueResult(unit, chain, c[0], 0, "receiver");
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireParentage(unit, chain, c[1], 1);
        if (failure.isPresent()) {
            return failure;
        }
        failure = requireKind(unit, chain, c[1], SemanticOpKind.FIELD_DELETE, 1, "commit");
        if (failure.isPresent()) {
            return failure;
        }
        KindPayload.FieldDeletePayload delete = (KindPayload.FieldDeletePayload) c[1].payload();
        return requireEqual(unit, chain, delete.classValue(), (ValueId) c[0].result(),
            "the FIELD_DELETE commit's resolved class value reference");
    }

    // =========================================================================
    // Shared checks
    // =========================================================================

    /**
     * Resolves every child of the chain in position order. On the first
     * unresolvable child the failure is reported through
     * {@code failureOut} (the caller returns it) and the returned array
     * is partial; a fully resolvable child list fills the array and leaves
     * {@code failureOut} untouched.
     */
    private static SemanticOp[] resolveChildren(LoweredModuleUnit unit, SemanticOp chain,
                                                List<OpId> children,
                                                Map<OpId, SemanticOp> ops,
                                                CompilerDiagnostic[] failureOut) {
        SemanticOp[] resolved = new SemanticOp[children.size()];
        for (int i = 0; i < children.size(); i++) {
            SemanticOp child = ops.get(children.get(i));
            if (child == null) {
                failureOut[0] = fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
                    "the child at position " + i + " (" + children.get(i)
                        + ") does not resolve to an op of this unit").get();
                return resolved;
            }
            resolved[i] = child;
        }
        return resolved;
    }

    private static Optional<CompilerDiagnostic> requireKind(LoweredModuleUnit unit,
                                                            SemanticOp chain, SemanticOp child,
                                                            SemanticOpKind expected, int position,
                                                            String role) {
        if (child.kind() == expected) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            "the " + role + " child at position " + position + " must be " + expected
                + ", got " + child.kind());
    }

    private static Optional<CompilerDiagnostic> requireValueResult(LoweredModuleUnit unit,
                                                                   SemanticOp chain,
                                                                   SemanticOp child,
                                                                   int position, String role) {
        if (child.result() instanceof ValueId) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            "the " + role + " child at position " + position + " (" + child.kind()
                + ") must publish a ValueId result");
    }

    private static Optional<CompilerDiagnostic> requireParentage(LoweredModuleUnit unit,
                                                                 SemanticOp chain,
                                                                 SemanticOp child,
                                                                 int position) {
        if (chain.opId().equals(child.origin().parentOpId())) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            "the child at position " + position + " (" + child.opId() + ") must record the "
                + "chain op as its parentOpId, got " + child.origin().parentOpId());
    }

    private static Optional<CompilerDiagnostic> requireEqual(LoweredModuleUnit unit,
                                                             SemanticOp chain, ValueId actual,
                                                             ValueId expected, String what) {
        if (expected.equals(actual)) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            what + " must reference the resolved value " + expected + ", got " + actual);
    }

    private static Optional<CompilerDiagnostic> requirePolicy(LoweredModuleUnit unit,
                                                              SemanticOp chain, SemanticOp child,
                                                              FailurePolicyId expected,
                                                              String what) {
        if (child.failurePolicy() == expected) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            what + " must carry policy " + expected.name() + ", got "
                + child.failurePolicy().name());
    }

    private static Optional<CompilerDiagnostic> requireResultType(LoweredModuleUnit unit,
                                                                  SemanticOp chain,
                                                                  SemanticOp child,
                                                                  RuntimeDescriptor expected,
                                                                  String what) {
        if (expected.equals(child.resultType())) {
            return Optional.empty();
        }
        return fail(unit, RULE_ADDRESS_CHAIN_SHAPE, chain,
            what + " must carry resultType " + expected.canonicalSpecText() + ", got "
                + (child.resultType() == null ? "none" : child.resultType()));
    }

    /** The descriptor-kind rule: FUNCTION_SIGNATURE for function descriptors, TYPE_DESCRIPTOR otherwise. */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    // =========================================================================
    // E6005 construction (registry-owned; the protocol never hand-crafts a message)
    // =========================================================================

    private static Optional<CompilerDiagnostic> fail(LoweredModuleUnit unit, String rule,
                                                     SemanticOp op, String reason) {
        LoweringFailureDetail detail = new LoweringFailureDetail(
            unit.moduleId().path(),
            SemanticCapability.EVALUATION_ORDER,
            rule,
            unit.semanticProfile(),
            unit.formatVersion(),
            "AddressChainProtocol " + rule + " (op " + op.opId() + " at "
                + op.origin().span() + ": " + reason + ")");
        return Optional.of(FailureContractRegistry.e6005(detail));
    }
}
