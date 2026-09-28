package deal.semantic.ir;

import java.util.Objects;

/**
 * The closed canonical actual-kind tokens of the parent's "Closed failure
 * policies and canonical visible errors" section, owned by the failure
 * contract registry (schema S5): exactly the 14 pinned values
 *
 * <pre>{@code
 * null, missing, boolean, int, number, string, bytes, table, array, function,
 * class:<ClassId>, async-operation, nothing, invalid-unicode
 * }</pre>
 *
 * <p>in the pinned order; no open or unknown fallback member exists.
 * Actual-kind tokens appear in {@code {actual}} placeholder positions of
 * failure-policy templates (e.g. {@code TYPE_DESCRIPTOR} E8001
 * {@code expected {expected}, got {actual}}). Target class names never
 * appear: {@link #CLASS} is the only kind that renders with an identity,
 * as {@code class:<ClassId>}, and {@link #canonicalToken(ActualKind,
 * String)} fails closed for every other combination — a non-class kind
 * carrying a class name, a missing class id, or an empty class id is a
 * contract defect, never a renderable token.</p>
 */
public enum ActualKind {

    /** Language null. */
    NULL("null"),
    /** Internal missing (e.g. absent optional/template slot). */
    MISSING("missing"),
    /** Boolean. */
    BOOLEAN("boolean"),
    /** Signed-32-bit int. */
    INT("int"),
    /** IEEE-754 number. */
    NUMBER("number"),
    /** Unicode scalar string. */
    STRING("string"),
    /** Bytes buffer (the v1.2 fixed-length byte sequence). */
    BYTES("bytes"),
    /** Table. */
    TABLE("table"),
    /** Array. */
    ARRAY("array"),
    /** Function value. */
    FUNCTION("function"),
    /** Class instance; renders {@code class:<ClassId>} — never a target class name. */
    CLASS(null),
    /** Backend async operation handle. */
    ASYNC_OPERATION("async-operation"),
    /** No value produced. */
    NOTHING("nothing"),
    /** A string scalar sequence that is not valid Unicode. */
    INVALID_UNICODE("invalid-unicode");

    private final String token;

    ActualKind(String token) {
        this.token = token;
    }

    /**
     * The fixed canonical token of this kind, or {@code null} for
     * {@link #CLASS}, whose token requires a class id
     * ({@code class:<ClassId>}).
     */
    public String token() {
        return token;
    }

    /**
     * Renders the canonical actual-kind token with the fail-closed rule:
     * {@code CLASS} renders {@code class:<ClassId>} and requires a
     * non-empty class id; every other kind renders its fixed token and
     * never accepts a class name (target class names never appear).
     *
     * @param kind    the actual kind; must not be null
     * @param classId the class id for {@link #CLASS}, otherwise {@code null}
     * @return the canonical token text
     * @throws NullPointerException     if {@code kind} is null, or if
     *                                  {@code kind == CLASS} and
     *                                  {@code classId} is null
     * @throws IllegalArgumentException if {@code kind == CLASS} and
     *                                  {@code classId} is empty, or if
     *                                  {@code kind != CLASS} and
     *                                  {@code classId} is non-null
     */
    public static String canonicalToken(ActualKind kind, String classId) {
        Objects.requireNonNull(kind, "kind must not be null");
        if (kind == CLASS) {
            Objects.requireNonNull(classId,
                "CLASS renders as class:<ClassId> and requires the class id");
            if (classId.isEmpty()) {
                throw new IllegalArgumentException(
                    "CLASS renders as class:<ClassId> and requires a non-empty class id");
            }
            return "class:" + classId;
        }
        if (classId != null) {
            throw new IllegalArgumentException(
                "a non-class actual kind never carries a class name (kind " + kind + ")");
        }
        return kind.token;
    }
}
