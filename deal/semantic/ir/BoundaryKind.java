package deal.semantic.ir;

import java.util.List;

/**
 * The closed boundary-kind set of {@code deal.semantic-ir/1} (parent
 * "Closed boundary-assignment table (normative)"; schema S3).
 *
 * <p>Closed set — exactly the 27 values below in the pinned order; no open
 * or unknown fallback member and no external extension point exist. Every
 * reachable typed boundary is one {@code BOUNDARY} op whose
 * {@code (kind, descriptor, policy)} triple comes from the closed
 * boundary-assignment table; a triple outside the table is invalid IR
 * (validator R-BOUNDARY-TRIPLE).</p>
 *
 * <p>Reserved names — invalid in version 1 (validator R-ENUM/R-RESERVED-NAME):
 * {@code C_FFI_TO_DEAL}, {@code DEAL_TO_C_FFI} ({@link #RESERVED_NAMES}).
 * The C FFI crossings are host-shaped (the extern-C import's loaded module
 * table carries them), so those boundaries cannot reach this seam.</p>
 */
public enum BoundaryKind {

    VARIABLE_DECLARATION,
    VARIABLE_ASSIGNMENT,
    CLASS_FIELD_ASSIGNMENT,
    ARRAY_ELEMENT_ASSIGNMENT,
    /** The bytes element write's bounds cell ({@code BYTES_WRITE}). */
    BYTE_ELEMENT_ASSIGNMENT,
    ARRAY_ELEMENT_READ,
    /** The bytes element read's bounds cell ({@code BYTES_READ}). */
    BYTE_ELEMENT_READ,
    ARRAY_ELEMENT_DELETE,
    ARRAY_LITERAL_ELEMENT,
    FUNCTION_PARAMETER,
    FUNCTION_RETURN,
    ASYNC_COMPLETION,
    CLASS_LITERAL_FIELD,
    CLASS_DEFAULT_FIELD,
    UNTYPED_CLASS_INPUT,
    OPTIONAL_FIELD_READ,
    CONTEXTUAL_TABLE_READ,
    IMPORTED_MEMBER_READ,
    MODULE_EXPORT,
    HOST_TO_DEAL,
    DEAL_TO_HOST,
    STDLIB_PARAMETER,
    STDLIB_RETURN,
    EXTERNAL_PARAMETER,
    EXTERNAL_RETURN,
    JSON_FROM_FIELD,
    JSON_TO_FIELD;

    /**
     * The reserved boundary names, invalid as {@code BoundaryKind} values
     * in {@code deal.semantic-ir/1}. They are not enum members.
     */
    public static final List<String> RESERVED_NAMES = List.of(
        "C_FFI_TO_DEAL",
        "DEAL_TO_C_FFI"
    );

    /** Returns true iff {@code name} is a reserved (invalid) boundary name. */
    public static boolean isReservedName(String name) {
        return RESERVED_NAMES.contains(name);
    }
}
