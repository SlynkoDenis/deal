package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * A lowered function record of a {@link LoweredModuleUnit} (parent source-
 * construct coverage: "function declaration/expression covers
 * {@code CLOSURE_NEW}/{@code RECURSIVE_GROUP_INIT} and a
 * {@code LoweredFunction}"). The unit's {@code functions} map records one
 * entry per lowered function; execution semantics of the body are owned by
 * the construct epics (ISSUE-0234..0239) — this is the immutable schema
 * shape only.
 *
 * @param functionId the function identity; non-null
 * @param descriptor the exact function signature descriptor; non-null
 * @param captures   the ordered captured binding generations (closures
 *                   capture bindings, not values; each entry names the
 *                   creation-site incarnation of the captured binding —
 *                   the same generation-pinned entries as the
 *                   {@code CLOSURE_NEW} payload, so the factory's capture
 *                   parameter is the body's binding source); non-null
 * @param body       the body block identity; non-null
 */
public record LoweredFunction(
    FunctionId functionId,
    RuntimeDescriptor.Func descriptor,
    List<BindingGeneration> captures,
    BlockId body
) {

    public LoweredFunction(FunctionId functionId, RuntimeDescriptor.Func descriptor,
                           List<BindingGeneration> captures, BlockId body) {
        this.functionId = Objects.requireNonNull(functionId, "functionId must not be null");
        this.descriptor = Objects.requireNonNull(descriptor, "descriptor must not be null");
        this.captures = List.copyOf(captures);
        this.body = Objects.requireNonNull(body, "body must not be null");
    }

    /** The captured binding identities in capture order (the op payload's keys). */
    public List<BindingId> captureBindings() {
        return captures.stream().map(BindingGeneration::binding).toList();
    }

    /** The generation-pinned capture of one binding, or {@code null}. */
    public BindingGeneration captureOf(BindingId binding) {
        for (BindingGeneration capture : captures) {
            if (capture.binding().equals(binding)) {
                return capture;
            }
        }
        return null;
    }
}
