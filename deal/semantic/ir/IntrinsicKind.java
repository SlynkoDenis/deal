package deal.semantic.ir;

import java.util.List;

/**
 * The closed intrinsic-conversion set of {@code deal.semantic-ir/1}
 * (parent closed operation table; schema S3): the two conversion
 * intrinsics {@code int} and {@code number} usable as first-class function
 * values, plus the {@code bytes} allocation intrinsic.
 *
 * <p>Closed set — exactly {@link #INT_CONVERT},
 * {@link #NUMBER_CONVERT}, and {@link #BYTES_NEW}; no open or unknown
 * fallback member and no external extension point exist.
 * {@code INTRINSIC_CALL} has zero {@code BOUNDARY} child ops of any kind:
 * its single input operand completes before START and the intrinsic
 * policy ({@code INT_CONVERSION}/{@code NUMBER_CONVERSION} for the
 * conversions, {@code BYTES_ALLOCATE} for the allocation) is its only
 * terminal check. The kinds are payload fields, not snapshot
 * selectors.</p>
 *
 * <p>Each kind carries its pinned declared signature — the checker's
 * root {@code Symbol.IntrinsicSymbol} function type
 * ({@code deal/checker/NameResolver.seedIntrinsics}): {@code INT_CONVERT}
 * is {@code (number) -> int}, {@code NUMBER_CONVERT} is
 * {@code (int) -> number}, and {@code BYTES_NEW} is
 * {@code (int) -> bytes}. For the two conversions the signature is the
 * closed descriptor position of the
 * {@code FunctionExecutionBinding.IntrinsicFunction} shape
 * ({@link #declaredSignature()}); a binding carrying any other
 * {@code (kind, descriptor)} pair fails the closed gate. The bytes
 * allocation intrinsic is never a first-class function value (its
 * {@code INTRINSIC_CALL} carries the pinned {@code int} input descriptor
 * and the {@code bytes} result descriptor), so no
 * {@code IntrinsicFunction} binding is ever registered for it.</p>
 */
public enum IntrinsicKind {

    /** The {@code int} conversion intrinsic. */
    INT_CONVERT,

    /** The {@code number} conversion intrinsic. */
    NUMBER_CONVERT,

    /**
     * The {@code bytes} allocation intrinsic ({@code bytes(length)}): one
     * {@code INTRINSIC_CALL} with the pinned {@code int} input descriptor,
     * the {@code bytes} result descriptor, and the {@code BYTES_ALLOCATE}
     * terminal policy (E8012 {@code bytes length must be non-negative} at
     * the call expression).
     */
    BYTES_NEW;

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
            case BYTES_NEW -> new RuntimeDescriptor.Func(
                List.of(RuntimeDescriptor.Int.INSTANCE),
                RuntimeDescriptor.Bytes.INSTANCE);
        };
    }
}
