package deal.semantic.ir;

import java.util.List;

/**
 * The closed intrinsic-conversion set of {@code deal.semantic-ir/1}
 * (parent closed operation table; schema S3): the two conversion
 * intrinsics {@code int} and {@code number} usable as first-class function
 * values.
 *
 * <p>Closed set — exactly {@link #INT_CONVERT} and
 * {@link #NUMBER_CONVERT}; no open or unknown fallback member and no
 * external extension point exist. {@code INTRINSIC_CALL} has zero
 * {@code BOUNDARY} child ops of any kind: its single input operand
 * completes before START and the conversion policy
 * ({@code INT_CONVERSION}/{@code NUMBER_CONVERSION}) is its only terminal
 * check. The conversions are payload fields, not snapshot selectors.</p>
 *
 * <p>Each kind carries its pinned declared signature — the checker's
 * root {@code Symbol.IntrinsicSymbol} function type
 * ({@code deal/checker/NameResolver.seedIntrinsics}): {@code INT_CONVERT}
 * is {@code (number) -> int} and {@code NUMBER_CONVERT} is
 * {@code (int) -> number}. The signature is the closed descriptor
 * position of the {@code FunctionExecutionBinding.IntrinsicFunction}
 * shape ({@link #declaredSignature()}); a binding carrying any other
 * {@code (kind, descriptor)} pair fails the closed gate.</p>
 */
public enum IntrinsicKind {

    /** The {@code int} conversion intrinsic. */
    INT_CONVERT,

    /** The {@code number} conversion intrinsic. */
    NUMBER_CONVERT;

    /**
     * The pinned declared signature of this conversion intrinsic: the
     * intrinsic's declared function type as the compilation's single
     * {@code deal.semantic.DescriptorService} descriptor producer renders it —
     * {@code INT_CONVERT} is {@code (number)->int} and
     * {@code NUMBER_CONVERT} is {@code (int)->number}. It is the only
     * descriptor admissible in a {@code FunctionExecutionBinding
     * .IntrinsicFunction} shape of this kind.
     *
     * @return the intrinsic's declared signature descriptor; non-null
     */
    public RuntimeDescriptor.Func declaredSignature() {
        return switch (this) {
            case INT_CONVERT -> new RuntimeDescriptor.Func(
                List.of(RuntimeDescriptor.Number.INSTANCE),
                RuntimeDescriptor.Int.INSTANCE);
            case NUMBER_CONVERT -> new RuntimeDescriptor.Func(
                List.of(RuntimeDescriptor.Int.INSTANCE),
                RuntimeDescriptor.Number.INSTANCE);
        };
    }
}
