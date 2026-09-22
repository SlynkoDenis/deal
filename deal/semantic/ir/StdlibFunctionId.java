package deal.semantic.ir;

import java.util.List;

/**
 * The closed standard-library function set of {@code deal.semantic-ir/1}
 * (parent D8, "Standard-library operation table"; schema S3).
 *
 * <p>Closed set — exactly the 21 values below in the pinned order; no open
 * or unknown fallback member and no external extension point exist. Each
 * id names one {@code STDLIB_CALL} whose algorithm, effect, result,
 * ordering, and failure policy are fixed by the parent's stdlib table;
 * consumers may invoke target helpers only after equivalence to that
 * operation is verified. {@code TIME_NOW_MILLIS} is the 21st member
 * ({@code semantic-ir-construct-coverage-cutover} K7): the declared API
 * {@code nowMillis(): int} cannot represent contemporary epoch
 * milliseconds under signed32, so the operation reads the target clock
 * and its single terminal is the declared {@code int} boundary — the
 * pinned E8004 {@code int out of safe range} (
 * {@link FailurePolicyId#INT32_RESULT}). A module referencing it claims
 * {@code STDLIB_SEMANTICS} through the landed cataloged-call arm, exactly
 * like every other cataloged id.</p>
 */
public enum StdlibFunctionId implements ClosedSelector {

    CONSOLE_LOG,
    CONSOLE_ERROR,
    STRING_LENGTH,
    STRING_SUBSTRING,
    STRING_CONTAINS,
    STRING_STARTS_WITH,
    STRING_ENDS_WITH,
    STRING_REPLACE,
    STRING_SPLIT,
    STRING_TRIM,
    TABLE_KEYS,
    JSON_PARSE,
    JSON_STRINGIFY,
    MATH_FLOOR,
    MATH_CEIL,
    MATH_SQRT,
    MATH_ABS_INT,
    MATH_ABS_NUMBER,
    MATH_MIN_INT,
    MATH_MAX_INT,
    TIME_NOW_MILLIS;

    /**
     * The reserved stdlib selector names, invalid as
     * {@code StdlibFunctionId} values in {@code deal.semantic-ir/1}. They
     * are not enum members. The list is empty since
     * {@code TIME_NOW_MILLIS} became the 21st member (K7); the guard
     * (deny-by-default: no reserved name is ever a valid selector) stays
     * as the closed-set machinery, exercised by the reserved
     * {@link FailurePolicyId} names.
     */
    public static final List<String> RESERVED_NAMES = List.of();

    /** Returns true iff {@code name} is a reserved (invalid) stdlib selector name. */
    public static boolean isReservedName(String name) {
        return RESERVED_NAMES.contains(name);
    }
}
