package deal.semantic.ir;

import deal.diagnostics.DiagnosticCode;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The single execution form of the closed boundary-assignment table at the
 * {@code BOUNDARY}-op level (ISSUE-0233 design D3): a static, pure,
 * deterministic projection engine over the closed value view.
 *
 * <p><b>Closed 13-policy subset.</b> A {@code BOUNDARY} op can carry
 * exactly these policies and the executor has a projection for exactly
 * these:
 *
 * <pre>{@code
 * TYPE_DESCRIPTOR, FUNCTION_SIGNATURE, HOST_PARAMETER, HOST_SYNC_RETURN,
 * ASYNC_COMPLETION, ARRAY_ELEMENT_DESCRIPTOR, ARRAY_READ_INDEX_THEN_DESCRIPTOR,
 * ARRAY_WRITE_BOUNDS_THEN_ELEMENT, ARRAY_DELETE_BOUNDS, BYTES_READ, BYTES_WRITE,
 * JSON_FROM_NULL, JSON_TO_ERROR
 * }</pre>
 *
 * Any other policy is never a {@code BOUNDARY} policy — the validator's
 * closed table rejects it — and {@link #check} rejects it fail closed as a
 * producer {@link Defect} (never a DEAL projection). Totality is exactly
 * the validator-accepted cells (the D5 tie): every validator-accepted
 * cell has a defined projection here and no other cell does.</p>
 *
 * <p><b>Projections (normative, D3).</b> The descriptor-kind rule: a
 * non-function descriptor check projects wrong kinds as E8001
 * {@code expected {expected}, got {actual}} with the canonical
 * {@link ActualKind} token; the {@code int} path follows the pinned order
 * (kind → NaN → infinity → non-integer → E8004 {@code int out of safe range});
 * a string view classified {@code invalid-unicode} projects the pinned
 * {@code expected string, got invalid Unicode scalar encoding}; a class
 * descriptor requires the tagged atom text byte-equal; an array descriptor
 * checks elements in increasing index order and projects the first
 * failure as E8003 {@code array element {oneBasedIndex} type mismatch}
 * with the element descriptor as expected, the leaf actual kind as
 * actual, and the leaf failure as cause; a nullable descriptor passes
 * language null and propagates the inner failure unchanged. A function
 * descriptor check projects a differing carried signature as E8010
 * {@code function signature mismatch: expected {expected}, got {actual}}
 * (actual = the carried signature's canonical text) and a non-function
 * value as E8001. {@code HOST_PARAMETER} projects every failure through
 * the single pinned E8010
 * {@code parameter {index} type mismatch: expected {expected}, got {actual}};
 * {@code HOST_SYNC_RETURN} through
 * {@code return value 1 type mismatch: expected {expected}, got nothing}
 * (no value) or {@code … got {actual}} (wrong value);
 * {@code ASYNC_COMPLETION} mismatches as E8001
 * {@code expected {expected}} with the cell's actual kind (a numeric
 * completion carrier is the single {@code number} kind — the pinned corpus
 * completion-cell transcript; operation-failure precedence
 * is the {@code AWAIT} machine's — ISSUE-0236 — never this op's). The
 * array cells enforce {@code negative array index} (read),
 * {@code array index out of bounds} (write/delete, index {@code < 0} or
 * {@code > length}) before any element check, and the executor never
 * commits a mutation. The bytes cells (K6) enforce the pinned E8012
 * bounds ({@code index < 0} or {@code index >= length}) before the
 * element check; the write's E8013 value range and its single mutation
 * are the enclosing commit's (this executor commits nothing). {@code JSON_FROM_NULL} swallows every failure into
 * language null (never a DEAL failure); {@code JSON_TO_ERROR} projects the
 * first unsupported/wrong-identity/missing/nonfinite value as E8001
 * {@code value at {fieldPath} is not JSON serializable: {actual}}.
 * Messages are instantiated from the registry rows
 * ({@code FailureContractRegistry.row(policy)}) — the executor never
 * selects message text.</p>
 *
 * <p><b>Missing.</b> A {@code missing} view against a nullable descriptor
 * maps to language null and passes — the {@code OPTIONAL_FIELD_READ} and
 * {@code CONTEXTUAL_TABLE_READ} cells' pinned missing→null mapping
 * (the optional read additionally pre-maps missing to null at the op, so
 * its boundary sees null; a non-nullable optional field therefore
 * projects {@code expected {expected}, got null} after the pre-mapping).
 * A {@code missing} view against a non-nullable descriptor projects
 * {@code expected {expected}, got missing} — the
 * {@code CONTEXTUAL_TABLE_READ} non-nullable decision and every other
 * cell's classification. In validator-accepted IR a {@code missing} view
 * reaches a nullable descriptor only at the two named cells, so the rule
 * is exact over the table's cells.</p>
 *
 * <p><b>Realization independence.</b> {@link #check} never consults the
 * realization: a {@code RuntimeValidation} boundary runs the check. A
 * {@code RepresentationProof} boundary is not executed —
 * {@link #execute} returns {@code Pass} with the value unchanged and
 * never enters check logic on that path (the D4 proof-eligibility rule
 * makes a failing proved boundary unreachable for admissible cells).</p>
 *
 * <p><b>Purity and bounds.</b> No mutation, no retry, no target
 * mechanics; recursion is bounded by descriptor length plus element
 * count. The component depends only on the schema itself (descriptors,
 * actual kinds, policies, the closed view) — no {@code deal.types}
 * dependency. The executor implements no oracle value model, no
 * shared-emitter adapters, no invocation state machine (context fields
 * are inputs), and no address-chain ordering — those are
 * ISSUE-0240/0239/0236/0234's.</p>
 */
public final class BoundaryExecutor {

    private BoundaryExecutor() {
        // Static surface only; pure and stateless.
    }

    /**
     * An executor producer defect: a policy outside the closed 11-policy
     * subset, a cell executed without its required context, a broken
     * descriptor/policy pairing, or an uninstantiable projection template.
     * Internal control flow — fail closed, never a DEAL projection and
     * never a crash.
     */
    public static final class Defect extends RuntimeException {

        private static final long serialVersionUID = 1L;

        public Defect(String message) {
            super(message);
        }
    }

    /** The closed 13-policy subset a {@code BOUNDARY} op can carry (D3, exact). */
    private static final Set<FailurePolicyId> EXECUTABLE_POLICIES = Set.of(
        FailurePolicyId.TYPE_DESCRIPTOR,
        FailurePolicyId.FUNCTION_SIGNATURE,
        FailurePolicyId.HOST_PARAMETER,
        FailurePolicyId.HOST_SYNC_RETURN,
        FailurePolicyId.ASYNC_COMPLETION,
        FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
        FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
        FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
        FailurePolicyId.ARRAY_DELETE_BOUNDS,
        FailurePolicyId.BYTES_READ,
        FailurePolicyId.BYTES_WRITE,
        FailurePolicyId.JSON_FROM_NULL,
        FailurePolicyId.JSON_TO_ERROR
    );

    // =========================================================================
    // check — the closed projection engine (RuntimeValidation cells)
    // =========================================================================

    /**
     * Executes the closed projection of one validated {@code BOUNDARY} op
     * cell: {@code Pass} with the same semantic value (or the named
     * missing→null mapping), or {@code Fail} with the registry row's
     * pinned, instantiated projection.
     *
     * @param policy     the boundary's failure policy; must be a member of
     *                   the closed 11-policy subset
     * @param descriptor the boundary's checked descriptor; non-null
     * @param view       the completed input operand's closed value view;
     *                   non-null
     * @param context    the minimal context the cell names; non-null
     * @return {@code Pass} or {@code Fail}, deterministic
     * @throws Defect               if {@code policy} is outside the closed
     *                              11-policy subset, if a context-bearing
     *                              cell lacks its required context field, or
     *                              if a descriptor/policy pairing is not a
     *                              validator-accepted cell
     * @throws NullPointerException if any argument is null
     */
    public static BoundaryOutcome check(FailurePolicyId policy, RuntimeDescriptor descriptor,
                                        BoundaryValueView view, BoundaryContext context) {
        Objects.requireNonNull(policy, "policy must not be null");
        Objects.requireNonNull(descriptor, "descriptor must not be null");
        Objects.requireNonNull(view, "view must not be null");
        Objects.requireNonNull(context, "context must not be null");
        if (!EXECUTABLE_POLICIES.contains(policy)) {
            throw new Defect("policy " + policy.name() + " is outside the closed 13-policy "
                + "BOUNDARY subset: the validator's closed table rejects it as a BOUNDARY "
                + "policy and the executor has no projection for it");
        }
        return switch (policy) {
            case TYPE_DESCRIPTOR -> checkTypeDescriptor(descriptor, view);
            case FUNCTION_SIGNATURE -> checkFunctionSignature(descriptor, view);
            case HOST_PARAMETER -> checkHostParameter(descriptor, view, context);
            case HOST_SYNC_RETURN -> checkHostSyncReturn(descriptor, view);
            case ASYNC_COMPLETION -> checkAsyncCompletion(descriptor, view);
            case ARRAY_ELEMENT_DESCRIPTOR -> checkArrayElement(descriptor, view, context);
            case ARRAY_READ_INDEX_THEN_DESCRIPTOR -> checkArrayRead(view, context);
            case ARRAY_WRITE_BOUNDS_THEN_ELEMENT ->
                checkArrayWrite(descriptor, view, context);
            case ARRAY_DELETE_BOUNDS -> checkArrayDelete(view, context);
            case BYTES_READ -> checkBytesRead(descriptor, view, context);
            case BYTES_WRITE -> checkBytesWrite(descriptor, view, context);
            case JSON_FROM_NULL -> checkJsonFromNull(descriptor, view);
            case JSON_TO_ERROR -> checkJsonToError(descriptor, view, context);
            default -> throw new Defect(
                "policy " + policy.name() + " has no executor projection");
        };
    }

    // =========================================================================
    // execute — the BOUNDARY-op-level dispatch on the realization
    // =========================================================================

    /**
     * The {@code BOUNDARY}-op-level terminal dispatch: a
     * {@link BoundaryRealization.RepresentationProof} boundary is not
     * executed — its terminal is always {@code Pass} with the value
     * unchanged and no check logic runs on this path; a
     * {@link BoundaryRealization.RuntimeValidation} boundary runs
     * {@link #check}. The check logic itself never consults the
     * realization.
     *
     * @param policy      the boundary's failure policy; must be a member of
     *                    the closed 11-policy subset
     * @param descriptor  the boundary's checked descriptor; non-null
     * @param view        the completed input operand's closed value view;
     *                    non-null
     * @param context     the minimal context the cell names; non-null
     * @param realization the op payload's realization; non-null
     * @return {@code Pass} for a proved boundary (value unchanged), or the
     *         {@code check} outcome for a runtime validation
     * @throws Defect               if {@code policy} is outside the closed
     *                              11-policy subset
     * @throws NullPointerException if any argument is null
     */
    public static BoundaryOutcome execute(FailurePolicyId policy, RuntimeDescriptor descriptor,
                                          BoundaryValueView view, BoundaryContext context,
                                          BoundaryRealization realization) {
        Objects.requireNonNull(policy, "policy must not be null");
        Objects.requireNonNull(descriptor, "descriptor must not be null");
        Objects.requireNonNull(view, "view must not be null");
        Objects.requireNonNull(context, "context must not be null");
        Objects.requireNonNull(realization, "realization must not be null");
        if (!EXECUTABLE_POLICIES.contains(policy)) {
            throw new Defect("policy " + policy.name() + " is outside the closed 13-policy "
                + "BOUNDARY subset: the validator's closed table rejects it as a BOUNDARY "
                + "policy and the executor has no projection for it");
        }
        if (realization instanceof BoundaryRealization.RepresentationProof) {
            // A proved boundary is not executed: its terminal is always
            // SUCCESS with the value unchanged. No check logic runs here.
            return new BoundaryOutcome.Pass(view);
        }
        return check(policy, descriptor, view, context);
    }

    // =========================================================================
    // Policy handlers
    // =========================================================================

    /** TYPE_DESCRIPTOR: the descriptor-kind rule for non-function descriptors. */
    private static BoundaryOutcome checkTypeDescriptor(RuntimeDescriptor descriptor,
                                                       BoundaryValueView view) {
        if (descriptor instanceof RuntimeDescriptor.Func) {
            throw new Defect("TYPE_DESCRIPTOR with a function descriptor: the closed "
                + "descriptor-kind rule assigns function descriptors to FUNCTION_SIGNATURE "
                + "(validator cell)");
        }
        return descriptorKindOutcome(tdProjection(), core(descriptor, view));
    }

    /** FUNCTION_SIGNATURE: function descriptors; E8010 for a differing signature. */
    private static BoundaryOutcome checkFunctionSignature(RuntimeDescriptor descriptor,
                                                          BoundaryValueView view) {
        if (!(descriptor instanceof RuntimeDescriptor.Func)) {
            throw new Defect("FUNCTION_SIGNATURE with a non-function descriptor: the closed "
                + "descriptor-kind rule assigns non-function descriptors to TYPE_DESCRIPTOR "
                + "(validator cell)");
        }
        return descriptorKindOutcome(signatureProjection(), core(descriptor, view));
    }

    /** HOST_PARAMETER: every failure through the single pinned E8010 template. */
    private static BoundaryOutcome checkHostParameter(RuntimeDescriptor descriptor,
                                                      BoundaryValueView view,
                                                      BoundaryContext context) {
        Integer parameterIndex = requireContextField(context.parameterIndex(),
            "parameterIndex", "HOST_PARAMETER");
        if (parameterIndex < 1) {
            throw new Defect("HOST_PARAMETER names a one-based parameterIndex; got "
                + parameterIndex);
        }
        CoreResult result = core(descriptor, view);
        return switch (result) {
            case CorePass pass -> new BoundaryOutcome.Pass(pass.value());
            case CoreFail fail -> new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.HOST_PARAMETER), 0,
                descriptor.canonicalSpecText(), hostActual(view, fail),
                metadataOf("index", Integer.toString(parameterIndex)), null));
        };
    }

    /** HOST_SYNC_RETURN: no value first, then the descriptor-kind check. */
    private static BoundaryOutcome checkHostSyncReturn(RuntimeDescriptor descriptor,
                                                       BoundaryValueView view) {
        if (view.kind() == ActualKind.NOTHING) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.HOST_SYNC_RETURN), 0,
                descriptor.canonicalSpecText(), "nothing", new LinkedHashMap<>(), null));
        }
        CoreResult result = core(descriptor, view);
        return switch (result) {
            case CorePass pass -> new BoundaryOutcome.Pass(pass.value());
            case CoreFail fail -> new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.HOST_SYNC_RETURN), 1,
                descriptor.canonicalSpecText(), hostActual(view, fail),
                new LinkedHashMap<>(), null));
        };
    }

    /**
     * ASYNC_COMPLETION: mismatches through the row's pinned E8001 template.
     * The cell's actual-kind token is the pinned corpus projection: a
     * completion value's numeric carrier has the single {@code number} kind
     * (the corpus completion-cell pin {@code expected string} /
     * {@code number} for an integral host completion), while every other
     * kind keeps the shared token.
     */
    private static BoundaryOutcome checkAsyncCompletion(RuntimeDescriptor descriptor,
                                                        BoundaryValueView view) {
        return descriptorKindOutcome(asyncProjection(),
            completionActual(core(descriptor, view), view));
    }

    /** The completion cell's numeric actual token ({@link #checkAsyncCompletion}). */
    private static CoreResult completionActual(CoreResult result, BoundaryValueView view) {
        if (result instanceof CoreFail fail
                && fail.caseKind() == FailureCase.KIND_MISMATCH
                && view.kind() == ActualKind.INT) {
            return new CoreFail(fail.caseKind(), fail.expected(),
                ActualKind.NUMBER.token(), 0, null);
        }
        return result;
    }

    /** ARRAY_ELEMENT_DESCRIPTOR: element check; E8003 with the leaf cause. */
    private static BoundaryOutcome checkArrayElement(RuntimeDescriptor descriptor,
                                                     BoundaryValueView view,
                                                     BoundaryContext context) {
        Integer elementIndex = requireContextField(context.elementIndex(),
            "elementIndex", "ARRAY_ELEMENT_DESCRIPTOR");
        if (elementIndex < 1) {
            throw new Defect("ARRAY_ELEMENT_DESCRIPTOR names a one-based elementIndex; got "
                + elementIndex);
        }
        CoreResult result = core(descriptor, view);
        return switch (result) {
            case CorePass pass -> new BoundaryOutcome.Pass(pass.value());
            case CoreFail fail -> {
                CoreFail leaf = fail.caseKind() == FailureCase.ELEMENT ? fail.cause() : fail;
                yield new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                    FailureContractRegistry.row(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR), 0,
                    descriptor.canonicalSpecText(),
                    ActualKind.canonicalToken(view.kind(), view.classId()),
                    metadataOf("oneBasedIndex", Integer.toString(elementIndex)),
                    project(tdProjection(), leaf)));
            }
        };
    }

    /** ARRAY_READ_INDEX_THEN_DESCRIPTOR: negative index first, otherwise pass through. */
    private static BoundaryOutcome checkArrayRead(BoundaryValueView view,
                                                  BoundaryContext context) {
        Integer index = requireContextField(context.index(), "index",
            "ARRAY_READ_INDEX_THEN_DESCRIPTOR");
        if (index < 0) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(
                    FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR),
                0, null, null, new LinkedHashMap<>(), null));
        }
        // The read's value/missing decision is the contextual boundary's,
        // not this cell's; the executor commits nothing.
        return new BoundaryOutcome.Pass(view);
    }

    /** ARRAY_WRITE_BOUNDS_THEN_ELEMENT: bounds first, then the element check. */
    private static BoundaryOutcome checkArrayWrite(RuntimeDescriptor descriptor,
                                                   BoundaryValueView view,
                                                   BoundaryContext context) {
        Integer index = requireContextField(context.index(), "index",
            "ARRAY_WRITE_BOUNDS_THEN_ELEMENT");
        Integer length = requireContextField(context.length(), "length",
            "ARRAY_WRITE_BOUNDS_THEN_ELEMENT");
        if (length < 0) {
            throw new Defect("ARRAY_WRITE_BOUNDS_THEN_ELEMENT names a non-negative array "
                + "length; got " + length);
        }
        if (index < 0 || index > length) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(
                    FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT),
                0, null, null, new LinkedHashMap<>(), null));
        }
        // The mutation is the enclosing commit op's, after this boundary;
        // the executor commits nothing.
        return descriptorKindOutcome(tdProjection(), core(descriptor, view));
    }

    /**
     * BYTES_READ: the pinned E8012 bounds check first
     * ({@code index < 0} or {@code index >= b.length}), then the element
     * descriptor-kind check on the already-read byte (K6 item 3). The
     * context carries {@code {index, length}}.
     */
    private static BoundaryOutcome checkBytesRead(RuntimeDescriptor descriptor,
                                                  BoundaryValueView view,
                                                  BoundaryContext context) {
        Integer index = requireContextField(context.index(), "index", "BYTES_READ");
        Integer length = requireContextField(context.length(), "length", "BYTES_READ");
        if (length < 0) {
            throw new Defect("BYTES_READ names a non-negative bytes length; got " + length);
        }
        if (index < 0 || index >= length) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.BYTES_READ),
                0, null, null, new LinkedHashMap<>(), null));
        }
        return descriptorKindOutcome(tdProjection(), core(descriptor, view));
    }

    /**
     * BYTES_WRITE: the pinned E8012 bounds check first
     * ({@code index < 0} or {@code index >= b.length}), then the element
     * descriptor-kind check on the checked RHS value; the value-range
     * check (E8013, {@code 0..255}) and the single mutation are the
     * enclosing commit's, after this boundary (K6 items 3/4).
     */
    private static BoundaryOutcome checkBytesWrite(RuntimeDescriptor descriptor,
                                                   BoundaryValueView view,
                                                   BoundaryContext context) {
        Integer index = requireContextField(context.index(), "index", "BYTES_WRITE");
        Integer length = requireContextField(context.length(), "length", "BYTES_WRITE");
        if (length < 0) {
            throw new Defect("BYTES_WRITE names a non-negative bytes length; got " + length);
        }
        if (index < 0 || index >= length) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.BYTES_WRITE),
                0, null, null, new LinkedHashMap<>(), null));
        }
        return descriptorKindOutcome(tdProjection(), core(descriptor, view));
    }

    /**
     * The write's value-range projection (E8013
     * {@code bytes value out of range}): the pinned second template of the
     * {@code BYTES_WRITE} row, committed by the chain's
     * {@code INDEX_WRITE} child at the assignment-expression origin.
     */
    public static BoundaryFailure bytesWriteRangeFailure() {
        return BoundaryFailure.fromRowWithCode(
            FailureContractRegistry.row(FailurePolicyId.BYTES_WRITE), 1,
            DiagnosticCode.E8013, null, null, new LinkedHashMap<>(), null);
    }

    /** ARRAY_DELETE_BOUNDS: index < 0 or > length; otherwise pass. */
    private static BoundaryOutcome checkArrayDelete(BoundaryValueView view,
                                                    BoundaryContext context) {
        Integer index = requireContextField(context.index(), "index",
            "ARRAY_DELETE_BOUNDS");
        Integer length = requireContextField(context.length(), "length",
            "ARRAY_DELETE_BOUNDS");
        if (length < 0) {
            throw new Defect("ARRAY_DELETE_BOUNDS names a non-negative array length; got "
                + length);
        }
        if (index < 0 || index > length) {
            return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.ARRAY_DELETE_BOUNDS),
                0, null, null, new LinkedHashMap<>(), null));
        }
        // The commit's nil write runs after the boundary.
        return new BoundaryOutcome.Pass(view);
    }

    /** JSON_FROM_NULL: any failure swallows into language null; never a DEAL failure. */
    private static BoundaryOutcome checkJsonFromNull(RuntimeDescriptor descriptor,
                                                     BoundaryValueView view) {
        CoreResult result = core(descriptor, view);
        return switch (result) {
            case CorePass pass -> new BoundaryOutcome.Pass(pass.value());
            case CoreFail ignored -> new BoundaryOutcome.Pass(BoundaryValueView.nullView());
        };
    }

    /** JSON_TO_ERROR: the first declaration-order unsupported value projects E8001. */
    private static BoundaryOutcome checkJsonToError(RuntimeDescriptor descriptor,
                                                    BoundaryValueView view,
                                                    BoundaryContext context) {
        String fieldPath = requireContextField(context.fieldPath(), "fieldPath",
            "JSON_TO_ERROR");
        String failing = jsonFailure(descriptor, view);
        if (failing == null) {
            return new BoundaryOutcome.Pass(view);
        }
        return new BoundaryOutcome.Fail(BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.JSON_TO_ERROR), 0,
            null, failing, metadataOf("fieldPath", fieldPath), null));
    }

    // =========================================================================
    // The descriptor-kind core: classification only, projected per policy
    // =========================================================================

    /** The core's failure cases: the pinned check order of the closed table. */
    private enum FailureCase {
        /** A wrong-kind value; projected as E8001 with the canonical actual token. */
        KIND_MISMATCH,
        /** A string view classified invalid-unicode. */
        INVALID_UNICODE,
        /** The int path's NaN / infinity / non-integer number refinement. */
        INT_REFINEMENT,
        /** The int path's signed32 range failure (E8004). */
        INT_OUT_OF_RANGE,
        /** A function value with a differing carried signature (E8010). */
        SIG_MISMATCH,
        /**
         * A non-bytes value at a bytes descriptor: the canonical v1.2
         * {@code expected bytes} projection (the bytes carrier's own
         * pinned text, with the expected/actual metadata beside it).
         */
        BYTES_KIND_MISMATCH,
        /** A failing array element in increasing index order (E8003 + cause). */
        ELEMENT
    }

    private sealed interface CoreResult permits CorePass, CoreFail {
    }

    private record CorePass(BoundaryValueView value) implements CoreResult {
    }

    private record CoreFail(FailureCase caseKind, String expected, String actual,
                            int elementIndex, CoreFail cause) implements CoreResult {
    }

    private static CoreResult pass(BoundaryValueView view) {
        return new CorePass(view);
    }

    /**
     * The bytes descriptor's kind-mismatch projection: the pinned
     * {@code expected bytes} text (the corpus's canonical v1.2 projection
     * for a non-bytes value at a bytes descriptor) with the expected
     * {@code bytes} and the value's canonical actual kind.
     */
    private static CoreResult bytesKindFail(BoundaryValueView view) {
        return new CoreFail(FailureCase.BYTES_KIND_MISMATCH, "bytes",
            ActualKind.canonicalToken(view.kind(), view.classId()), 0, null);
    }

    private static CoreResult kindFail(RuntimeDescriptor descriptor, BoundaryValueView view) {
        return new CoreFail(FailureCase.KIND_MISMATCH, kindExpected(descriptor),
            ActualKind.canonicalToken(view.kind(), view.classId()), 0, null);
    }

    /**
     * The kind-mismatch expected token of one descriptor: an array keeps
     * the fixed {@code array} token the unchanged reference runtime and
     * every shared producer print ({@code expected array, got table}) —
     * the descriptor's canonical {@code [D]} text is the E8003 element
     * projection's spelling, never the array kind row's — while every
     * other descriptor projects its canonical text.
     */
    private static String kindExpected(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Array
            ? "array" : descriptor.canonicalSpecText();
    }

    /**
     * The closed descriptor-kind check (D3): kind match for
     * null/boolean/number/string/table (number accepts an int carrier);
     * the int path in normative order (kind → NaN → infinity →
     * non-integer → E8004 signed32 range); the pinned invalid-unicode
     * classification; class atom byte-equality; array elements in
     * increasing index order with the first failure and its leaf cause;
     * nullable passes language null (and maps missing → null) and
     * propagates the inner failure unchanged; function values check the
     * carried signature structurally.
     */
    private static CoreResult core(RuntimeDescriptor descriptor, BoundaryValueView view) {
        if (view.kind() == ActualKind.MISSING
                && descriptor instanceof RuntimeDescriptor.Nullable) {
            // The named missing→null mapping (OPTIONAL_FIELD_READ /
            // CONTEXTUAL_TABLE_READ with a nullable descriptor).
            return pass(BoundaryValueView.nullView());
        }
        return switch (descriptor) {
            case RuntimeDescriptor.Null ignored ->
                view.kind() == ActualKind.NULL ? pass(view) : kindFail(descriptor, view);
            case RuntimeDescriptor.Boolean ignored ->
                view.kind() == ActualKind.BOOLEAN ? pass(view) : kindFail(descriptor, view);
            case RuntimeDescriptor.Int ignored -> coreInt(view);
            case RuntimeDescriptor.Number ignored ->
                view.kind() == ActualKind.NUMBER || view.kind() == ActualKind.INT
                    ? pass(view) : kindFail(descriptor, view);
            case RuntimeDescriptor.String ignored ->
                view.kind() == ActualKind.STRING ? pass(view)
                    : view.kind() == ActualKind.INVALID_UNICODE
                        ? new CoreFail(FailureCase.INVALID_UNICODE, "string",
                            "invalid-unicode", 0, null)
                        : kindFail(descriptor, view);
            case RuntimeDescriptor.Table ignored ->
                view.kind() == ActualKind.TABLE ? pass(view) : kindFail(descriptor, view);
            case RuntimeDescriptor.Bytes ignored ->
                // K6 item 11: the bytes descriptor's boundary projection is
                // the kind check — a bytes view passes, every other view
                // projects the bytes carrier's pinned v1.2 text
                // ({@code expected bytes} with the expected/actual metadata,
                // the canonical projection every backend produces).
                view.kind() == ActualKind.BYTES ? pass(view)
                    : bytesKindFail(view);
            case RuntimeDescriptor.Class cls -> coreClass(cls, view);
            case RuntimeDescriptor.Array array -> coreArray(array, view);
            case RuntimeDescriptor.Nullable nullable -> coreNullable(nullable, view);
            case RuntimeDescriptor.Func func -> coreFunc(func, view);
        };
    }

    /** The int path in the pinned normative order (spec v1.2 check_int order). */
    private static CoreResult coreInt(BoundaryValueView view) {
        return switch (view.kind()) {
            case INT -> pass(view);
            case NUMBER -> {
                double value = view.numberValue();
                if (Double.isNaN(value)) {
                    yield new CoreFail(FailureCase.INT_REFINEMENT, "int", "NaN", 0, null);
                }
                if (Double.isInfinite(value)) {
                    yield new CoreFail(FailureCase.INT_REFINEMENT, "int", "infinity", 0, null);
                }
                if (value != Math.rint(value)) {
                    yield new CoreFail(FailureCase.INT_REFINEMENT, "int",
                        "non-integer number", 0, null);
                }
                if (value < -2147483648d || value > 2147483647d) {
                    yield new CoreFail(FailureCase.INT_OUT_OF_RANGE, "int", "number", 0, null);
                }
                yield pass(view);
            }
            default -> kindFail(RuntimeDescriptor.Int.INSTANCE, view);
        };
    }

    /** Class atom identity: byte-equal to the descriptor's pinned atom text. */
    private static CoreResult coreClass(RuntimeDescriptor.Class descriptor,
                                        BoundaryValueView view) {
        if (view.kind() == ActualKind.CLASS
                && descriptor.classId().text().equals(view.classId())) {
            return pass(view);
        }
        return kindFail(descriptor, view);
    }

    /** Array elements in increasing index order; first failure wins with its leaf cause. */
    private static CoreResult coreArray(RuntimeDescriptor.Array descriptor,
                                        BoundaryValueView view) {
        if (view.kind() != ActualKind.ARRAY) {
            return kindFail(descriptor, view);
        }
        List<BoundaryValueView> elements = view.elements();
        for (int i = 0; i < elements.size(); i++) {
            BoundaryValueView element = elements.get(i);
            CoreResult elementResult = core(descriptor.element(), element);
            if (elementResult instanceof CoreFail elementFail) {
                CoreFail leaf = elementFail.caseKind() == FailureCase.ELEMENT
                    ? elementFail.cause() : elementFail;
                return new CoreFail(FailureCase.ELEMENT,
                    descriptor.element().canonicalSpecText(),
                    ActualKind.canonicalToken(element.kind(), element.classId()),
                    i + 1, leaf);
            }
        }
        return pass(view);
    }

    /** Nullable: language null passes; the inner failure propagates unchanged. */
    private static CoreResult coreNullable(RuntimeDescriptor.Nullable descriptor,
                                           BoundaryValueView view) {
        if (view.kind() == ActualKind.NULL) {
            return pass(view);
        }
        return core(descriptor.inner(), view);
    }

    /**
     * Function values: the carried signature must be structurally equal. A
     * non-function value projects the pinned function row — the shared
     * actual-kind classification with the fixed {@code function} expected
     * token both target runtimes project (never the descriptor text) —
     * while a differing carried signature keeps the canonical signature
     * texts.
     */
    private static CoreResult coreFunc(RuntimeDescriptor.Func descriptor,
                                       BoundaryValueView view) {
        if (view.kind() == ActualKind.FUNCTION) {
            RuntimeDescriptor.Func carried = view.functionSignature();
            return descriptor.equals(carried) ? pass(view)
                : new CoreFail(FailureCase.SIG_MISMATCH, descriptor.canonicalSpecText(),
                    carried.canonicalSpecText(), 0, null);
        }
        return new CoreFail(FailureCase.KIND_MISMATCH, "function",
            ActualKind.canonicalToken(view.kind(), view.classId()), 0, null);
    }

    // =========================================================================
    // Projection: core failures instantiate the registry rows' pinned templates
    // =========================================================================

    /** The pinned template selection of one descriptor-kind projection set. */
    private record Projection(FailurePolicyRow kindRow, int kindTemplate,
                              int refinementTemplate, int unicodeTemplate,
                              FailurePolicyRow sigRow, int bytesTemplate) {
    }

    /** TYPE_DESCRIPTOR: kind mismatches, the pinned invalid-unicode variant, E8010 signatures. */
    private static Projection tdProjection() {
        return new Projection(FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR),
            0, -1, 1, FailureContractRegistry.row(FailurePolicyId.FUNCTION_SIGNATURE), 2);
    }

    /** FUNCTION_SIGNATURE: non-functions project the E8001 kind template. */
    private static Projection signatureProjection() {
        return new Projection(FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR),
            0, -1, -1, FailureContractRegistry.row(FailurePolicyId.FUNCTION_SIGNATURE), -1);
    }

    /**
     * ASYNC_COMPLETION: kind mismatches through the row's corpus-aligned
     * {@code expected {expected}} template, the int ladder's pinned refinement
     * texts through the row's second template.
     */
    private static Projection asyncProjection() {
        return new Projection(FailureContractRegistry.row(FailurePolicyId.ASYNC_COMPLETION),
            0, 1, 1, null, -1);
    }

    /** The descriptor-kind outcome: Pass keeps the value; a failure projects per the set. */
    private static BoundaryOutcome descriptorKindOutcome(Projection projection,
                                                         CoreResult result) {
        return switch (result) {
            case CorePass pass -> new BoundaryOutcome.Pass(pass.value());
            case CoreFail fail -> new BoundaryOutcome.Fail(project(projection, fail));
        };
    }

    /**
     * Projects a core failure through one projection set: the row, the
     * template index, the metadata, and the E8003 leaf cause all come
     * from the closed registry rows — the executor never selects message
     * text.
     */
    private static BoundaryFailure project(Projection projection, CoreFail fail) {
        record Selected(FailurePolicyRow row, int templateIndex) {
        }
        Selected selected = switch (fail.caseKind()) {
            case KIND_MISMATCH ->
                new Selected(projection.kindRow(), projection.kindTemplate());
            case INT_REFINEMENT -> new Selected(projection.kindRow(),
                projection.refinementTemplate() >= 0
                    ? projection.refinementTemplate() : projection.kindTemplate());
            case INVALID_UNICODE -> new Selected(projection.kindRow(),
                projection.unicodeTemplate() >= 0
                    ? projection.unicodeTemplate() : projection.kindTemplate());
            case INT_OUT_OF_RANGE -> new Selected(
                FailureContractRegistry.row(FailurePolicyId.INT32_RESULT), 0);
            case SIG_MISMATCH -> new Selected(
                projection.sigRow() != null ? projection.sigRow() : projection.kindRow(), 0);
            case BYTES_KIND_MISMATCH -> new Selected(projection.kindRow(),
                projection.bytesTemplate() >= 0
                    ? projection.bytesTemplate() : projection.kindTemplate());
            case ELEMENT -> new Selected(
                FailureContractRegistry.row(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR), 0);
        };
        Map<String, String> metadata = fail.caseKind() == FailureCase.ELEMENT
            ? metadataOf("oneBasedIndex", Integer.toString(fail.elementIndex()))
            : new LinkedHashMap<>();
        BoundaryFailure cause = fail.caseKind() == FailureCase.ELEMENT
            ? project(projection, fail.cause()) : null;
        return BoundaryFailure.fromRow(selected.row(), selected.templateIndex(),
            fail.expected(), fail.actual(), metadata, cause);
    }

    /**
     * The host-wrap actual: the canonical token of the whole value for an
     * element failure (the parameter/return is the array), otherwise the
     * core failure's pinned classification.
     */
    private static String hostActual(BoundaryValueView view, CoreFail fail) {
        return fail.caseKind() == FailureCase.ELEMENT
            ? ActualKind.canonicalToken(view.kind(), view.classId()) : fail.actual();
    }

    // =========================================================================
    // JSON serializability (JSON_TO_ERROR): first declaration-order failure
    // =========================================================================

    /**
     * Returns the canonical actual-kind token of the first
     * unsupported/wrong-identity/missing/nonfinite value against the
     * declared descriptor, or {@code null} when the value is JSON
     * serializable. Unsupported values are functions, async-operation
     * handles, and invalid Unicode scalar sequences; nonfinite numbers
     * fail regardless of the declared numeric descriptor; class values
     * must carry the declared atom identity; arrays check elements in
     * increasing index order (the first failure wins); nullables pass
     * language null. A cycle cannot be expressed in the closed tree view
     * (no identity edges), so cycle detection is the machine's fact.
     */
    private static String jsonFailure(RuntimeDescriptor descriptor, BoundaryValueView view) {
        return switch (view.kind()) {
            case MISSING -> "missing";
            case FUNCTION -> "function";
            case ASYNC_OPERATION -> "async-operation";
            case INVALID_UNICODE -> "invalid-unicode";
            case NUMBER -> {
                double value = view.numberValue();
                yield Double.isNaN(value) || Double.isInfinite(value)
                    ? "number" : jsonShape(descriptor, view);
            }
            default -> jsonShape(descriptor, view);
        };
    }

    private static String jsonShape(RuntimeDescriptor descriptor, BoundaryValueView view) {
        return switch (descriptor) {
            case RuntimeDescriptor.Class cls ->
                view.kind() == ActualKind.CLASS
                        && cls.classId().text().equals(view.classId())
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.Nullable nullable ->
                view.kind() == ActualKind.NULL ? null : jsonFailure(nullable.inner(), view);
            case RuntimeDescriptor.Array array -> {
                if (view.kind() != ActualKind.ARRAY) {
                    yield ActualKind.canonicalToken(view.kind(), view.classId());
                }
                String first = null;
                for (BoundaryValueView element : view.elements()) {
                    first = jsonFailure(array.element(), element);
                    if (first != null) {
                        break;
                    }
                }
                yield first;
            }
            case RuntimeDescriptor.Int ignored -> switch (view.kind()) {
                case INT -> null;
                case NUMBER -> {
                    double value = view.numberValue();
                    yield Double.isNaN(value) || Double.isInfinite(value)
                            || value != Math.rint(value)
                            || value < -2147483648d || value > 2147483647d
                        ? "number" : null;
                }
                default -> ActualKind.canonicalToken(view.kind(), view.classId());
            };
            case RuntimeDescriptor.Number ignored ->
                view.kind() == ActualKind.NUMBER || view.kind() == ActualKind.INT
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.Null ignored ->
                view.kind() == ActualKind.NULL
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.Boolean ignored ->
                view.kind() == ActualKind.BOOLEAN
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.String ignored ->
                view.kind() == ActualKind.STRING
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.Table ignored ->
                view.kind() == ActualKind.TABLE
                    ? null : ActualKind.canonicalToken(view.kind(), view.classId());
            case RuntimeDescriptor.Bytes ignored -> throw new Defect(
                "a bytes descriptor reached the closed JSON-serializability projection: "
                    + "the closed boundary-assignment table has no bytes-descriptor JSON "
                    + "cell (bytes are non-jsonable and a bytes-typed @jsonable field is "
                    + "the checker's E4007 rejection) — never a BOUNDARY op");
            case RuntimeDescriptor.Func ignored ->
                ActualKind.canonicalToken(view.kind(), view.classId());
        };
    }

    // =========================================================================
    // Shared helpers
    // =========================================================================

    /** A deterministic single-entry metadata map (pinned placeholder order). */
    private static Map<String, String> metadataOf(String key, String value) {
        Map<String, String> metadata = new LinkedHashMap<>();
        metadata.put(key, value);
        return metadata;
    }

    /** A context-bearing cell executed without its named context is a producer defect. */
    private static <T> T requireContextField(T field, String fieldName, String cell) {
        if (field == null) {
            throw new Defect("the " + cell + " cell names context field '" + fieldName
                + "'; executing it without its required context is a producer defect, "
                + "never a DEAL projection");
        }
        return field;
    }
}
