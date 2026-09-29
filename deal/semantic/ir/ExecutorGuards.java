package deal.semantic.ir;

import java.util.Objects;

/**
 * The shared fail-closed shape guards of the op-level executors
 * ({@link ClassOpsExecutor}, {@link ContainerOpsExecutor}): the pinned op
 * shape, the named boundary-child resolution, and the child-shape checks.
 * The guards build the defect message only; the caller throws its own
 * {@code Defect} type so the executors keep their distinct public
 * failure surface.
 */
final class ExecutorGuards {

    private ExecutorGuards() {
    }

    /**
     * The pinned-op-shape defect message: exactly {@code kind} and exactly
     * {@code policy}, or {@code null} when the op conforms. A different
     * kind is not the op the caller executes, and a non-pinned policy
     * would silently change the contract.
     */
    static String opShapeDefect(SemanticOp op, SemanticOpKind kind,
                                FailurePolicyId policy) {
        Objects.requireNonNull(op, "op must not be null");
        if (op.kind() != kind) {
            return "expected a " + kind + " op, got " + op.kind() + " "
                + op.opId() + ": the executor interprets validated op shapes only — a "
                + "wrong kind is a producer defect, never executed";
        }
        if (op.failurePolicy() != policy) {
            return kind + " " + op.opId() + " carries failure policy "
                + op.failurePolicy() + ": the pinned policy is " + policy
                + " — a non-pinned policy is a producer defect, never executed";
        }
        return null;
    }

    /** The unresolved-boundary-child defect message (the lookup miss). */
    static String missingBoundaryChildDefect(SemanticOp owner, OpId childId) {
        return owner.kind() + " " + owner.opId() + " names boundary child "
            + childId + " which the boundary lookup does not resolve — a producer "
            + "defect, never executed";
    }

    /**
     * The child-shape defect message of a resolved boundary child: a
     * {@code BOUNDARY} op of the given boundary kind whose origin
     * {@code parentOpId} is the owning op, or {@code null} when the child
     * conforms.
     */
    static String childShapeDefect(SemanticOp child, SemanticOp owner,
                                   BoundaryKind pinnedKind) {
        if (child.kind() != SemanticOpKind.BOUNDARY) {
            return owner.kind() + " " + owner.opId() + " names child "
                + child.opId() + " of kind " + child.kind()
                + ": the pinned child kind is BOUNDARY — a producer defect, never executed";
        }
        if (!owner.opId().equals(child.origin().parentOpId())) {
            return owner.kind() + " " + owner.opId() + " names boundary child "
                + child.opId() + " whose origin parentOpId is "
                + child.origin().parentOpId()
                + ": the validator pins the child's parentOpId to the owning op — a "
                + "mismatch is a producer defect, never executed";
        }
        KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) child.payload();
        if (payload.kind() != pinnedKind) {
            return owner.kind() + " " + owner.opId() + " names boundary child "
                + child.opId() + " of boundary kind " + payload.kind()
                + ": the pinned child boundary kind is " + pinnedKind
                + " — a producer defect, never executed";
        }
        return null;
    }
}
