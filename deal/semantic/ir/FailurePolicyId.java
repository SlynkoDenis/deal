package deal.semantic.ir;

import java.util.List;

/**
 * The closed failure-policy set of {@code deal.semantic-ir/1} (parent
 * "Closed failure policies and canonical visible errors"; schema S3).
 *
 * <p>Closed set — exactly the 27 values below in the pinned order; no open
 * or unknown fallback member and no external extension point exist. The
 * {@code FailureContractRegistry} maps every policy to exactly one row
 * (code, template, metadata, origin, cause, frame, precedence); consumers
 * receive the resolved record in the operation snapshot and never select
 * messages. Unknown or reserved policies fail validation
 * (R-ENUM/R-RESERVED-NAME).</p>
 *
 * <p>Reserved policy names — invalid as {@code FailurePolicyId} in version 1
 * (validator R-RESERVED-NAME): {@code EXTERNAL_PARAMETER},
 * {@code EXTERNAL_RETURN}, {@code STDLIB_PARAMETER},
 * {@code STDLIB_RETURN} ({@link #RESERVED_NAMES}). The same names remain
 * valid {@link BoundaryKind} values for external and stdlib positions,
 * whose policies are selected by the descriptor-kind rule of the closed
 * boundary-assignment table — so they are reserved here exactly because
 * their policy is derived, never selected.</p>
 */
public enum FailurePolicyId {

    NO_DEAL_FAILURE,
    TYPE_DESCRIPTOR,
    INT32_RESULT,
    INT32_DIVISOR_THEN_RESULT,
    INT32_EXPONENT_THEN_RESULT,
    INT_CONVERSION,
    NUMBER_CONVERSION,
    ARRAY_ELEMENT_DESCRIPTOR,
    ARRAY_READ_INDEX_THEN_DESCRIPTOR,
    ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
    ARRAY_DELETE_BOUNDS,
    BYTES_ALLOCATE,
    BYTES_READ,
    BYTES_WRITE,
    FUNCTION_SIGNATURE,
    HOST_PARAMETER,
    HOST_SYNC_RETURN,
    ASYNC_COMPLETION,
    ASYNC_OPERATION_HANDLE,
    HOST_LOAD,
    CLASS_CONSTRUCTION,
    JSON_PARSE_SYNTAX,
    JSON_FROM_NULL,
    JSON_TO_ERROR,
    SQRT_NEGATIVE,
    THROW_TRANSFER,
    INFRASTRUCTURE_ONLY;

    /**
     * The reserved policy names, invalid as {@code FailurePolicyId} values
     * in {@code deal.semantic-ir/1}. They are not enum members.
     */
    public static final List<String> RESERVED_NAMES = List.of(
        "EXTERNAL_PARAMETER",
        "EXTERNAL_RETURN",
        "STDLIB_PARAMETER",
        "STDLIB_RETURN"
    );

    /** Returns true iff {@code name} is a reserved (invalid) policy name. */
    public static boolean isReservedName(String name) {
        return RESERVED_NAMES.contains(name);
    }
}
