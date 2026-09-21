package deal.semantic.ir;

import java.util.Objects;

/**
 * The runtime binding-resolution protocol of a dynamically resolved
 * {@code CALL}/{@code ASYNC_START} site (ISSUE-0531): a static, pure,
 * deterministic selection of the execution class and of the recorded
 * return-boundary cell for a callee whose binding kind is unknown until
 * execution.
 *
 * <p>{@link #kindOf(FunctionExecutionBinding)} classifies a resolved
 * {@code FunctionExecutionBinding} into the closed
 * {@link DynamicResolutionKind} set. An {@code AdapterBinding} carries no
 * source kind of its own; the D15 invocation protocol resolves the
 * adapter's source value to its own binding, and the class is derived
 * from that source binding ({@code kindOf(sourceBinding)}) — this method
 * fails closed on an adapter input rather than guessing. An
 * {@code IntrinsicFunction} is a boundary-shaped callable: the call op
 * computes the conversion result and runs the recorded
 * {@code HOST_TO_DEAL}/{@code HOST_SYNC_RETURN} cell, so its resolution
 * class is {@code HOST} (the intrinsic carrier's realization and its
 * invocation belong to the function-typed-value child).</p>
 *
 * <p>{@link #select(KindPayload.DynamicReturnBoundary, DynamicResolutionKind)}
 * selects the single recorded return-boundary cell the runtime executes
 * for the resolved class, with its closed kind and owner
 * ({@link ReturnBoundarySelection}): {@code DEAL_BODY} → the
 * {@code FUNCTION_RETURN} cell executed by the callee's source
 * {@code RETURN}; {@code HOST} → the {@code HOST_TO_DEAL} +
 * {@code HOST_SYNC_RETURN} cell executed by the call op; {@code EXTERNAL}
 * → the {@code EXTERNAL_RETURN} cell executed by the call op;
 * {@code SHARED_BODY} → {@link ReturnBoundarySelection.None} (the
 * callee's {@code RETURN} under its {@code EXTERNAL_ENTRY} runs the
 * single {@code EXTERNAL_RETURN} in the callee unit). The recorded cell
 * op ids resolve to {@code BOUNDARY} ops and carry their class's closed
 * cell (validator R-BOUNDARY-TRIPLE, the dynamic CALL arm); this protocol
 * never invents or synthesizes a boundary — it selects exactly one
 * recorded cell per resolution.
 */
public final class DynamicReturnBoundaryProtocol {

    private DynamicReturnBoundaryProtocol() {
        // Static surface; no instances.
    }

    /**
     * Classifies a resolved execution binding into the closed runtime
     * resolution class.
     *
     * @param binding the runtime-resolved binding; non-null
     * @return the closed resolution class of the binding
     * @throws IllegalArgumentException on an {@code AdapterBinding} input
     *         (the adapter's class derives from its D15-resolved source
     *         binding — the adapter carries no source kind of its own)
     */
    public static DynamicResolutionKind kindOf(FunctionExecutionBinding binding) {
        Objects.requireNonNull(binding, "binding must not be null");
        return switch (binding) {
            case FunctionExecutionBinding.LoweredBody ignored -> DynamicResolutionKind.DEAL_BODY;
            case FunctionExecutionBinding.HostFunction ignored -> DynamicResolutionKind.HOST;
            case FunctionExecutionBinding.HostFunctionValue ignored -> DynamicResolutionKind.HOST;
            case FunctionExecutionBinding.ExternalFunction external ->
                external.executionOwner() == ExternalExecutionOwner.SHARED_BODY
                    ? DynamicResolutionKind.SHARED_BODY
                    : DynamicResolutionKind.EXTERNAL;
            case FunctionExecutionBinding.IntrinsicFunction ignored ->
                DynamicResolutionKind.HOST;
            case FunctionExecutionBinding.AdapterBinding ignored ->
                throw new IllegalArgumentException("an AdapterBinding resolution derives its "
                    + "class from the D15-resolved source binding (kindOf(sourceBinding)); "
                    + "the adapter carries no source kind of its own");
        };
    }

    /**
     * Selects the single recorded return-boundary cell the runtime
     * executes for the resolved class.
     *
     * @param boundary the recorded dynamic return-boundary set of the
     *                 CALL; non-null
     * @param kind     the runtime-resolved execution class; non-null
     * @return the selected cell with its closed kind and owner
     */
    public static ReturnBoundarySelection select(KindPayload.DynamicReturnBoundary boundary,
                                                 DynamicResolutionKind kind) {
        Objects.requireNonNull(boundary, "boundary must not be null");
        Objects.requireNonNull(kind, "kind must not be null");
        return switch (kind) {
            case DEAL_BODY -> new ReturnBoundarySelection.CalleeReturn(
                boundary.dealBodyBoundaryOpId());
            case HOST -> new ReturnBoundarySelection.CallTerminal(
                boundary.hostBoundaryOpId(), BoundaryKind.HOST_TO_DEAL);
            case EXTERNAL -> new ReturnBoundarySelection.CallTerminal(
                boundary.externalBoundaryOpId(), BoundaryKind.EXTERNAL_RETURN);
            case SHARED_BODY -> ReturnBoundarySelection.None.INSTANCE;
        };
    }
}
