package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * The closed canonical value view a {@code BOUNDARY} op's executor
 * consumes (ISSUE-0233 design D3): pure classification data, never a
 * target representation.
 *
 * <p>Shape (D3, exact):
 * {@code {kind: ActualKind, classId?, numberValue?, functionSignature?,
 * elements:[BoundaryValueView]?}}. The {@code kind} is one of the closed
 * 14 canonical actual kinds ({@link ActualKind}); the payload fields are
 * present exactly when the kind names them:
 * {@code classId} for {@code CLASS} (the canonical {@code @modulePath/Name}
 * atom text), {@code numberValue} for {@code NUMBER} (any IEEE-754 double,
 * NaN/infinity included) and optionally for {@code INT} (an in-range
 * signed32 integral carrier), {@code functionSignature} for
 * {@code FUNCTION} (the carried signature), and {@code elements} for
 * {@code ARRAY} (the element views in index order). Every other field is
 * {@code null} for a kind that does not carry it, and construction fails
 * closed for an inconsistent shape.</p>
 *
 * <p>The view is realized by the oracle's value model and the shared
 * emitters' adapter layers; the executor interprets classifications only
 * (no representation unification, no {@code deal.types} dependency). The
 * view carries no identity edges, so a cycle cannot be expressed in it;
 * cycle detection for JSON serialization is the machine's fact.</p>
 */
public record BoundaryValueView(
    ActualKind kind,
    String classId,
    Double numberValue,
    RuntimeDescriptor.Func functionSignature,
    List<BoundaryValueView> elements
) {

    public BoundaryValueView {
        Objects.requireNonNull(kind, "kind must not be null");
        switch (kind) {
            case CLASS -> {
                if (classId == null || classId.isEmpty()) {
                    throw new IllegalArgumentException(
                        "a CLASS view carries the canonical class-id atom text "
                            + "(@modulePath/ClassName); classId must be non-null and non-empty");
                }
            }
            case NUMBER -> {
                if (numberValue == null) {
                    throw new IllegalArgumentException(
                        "a NUMBER view must carry its IEEE-754 value in numberValue");
                }
            }
            case INT -> {
                if (numberValue != null) {
                    if (!Double.isFinite(numberValue)
                            || numberValue != Math.rint(numberValue)
                            || numberValue < -2147483648d || numberValue > 2147483647d) {
                        throw new IllegalArgumentException(
                            "an INT view value must be a signed32 integral carrier, got "
                                + numberValue);
                    }
                }
            }
            case FUNCTION -> {
                if (functionSignature == null) {
                    throw new IllegalArgumentException(
                        "a FUNCTION view must carry its signature in functionSignature");
                }
            }
            case ARRAY -> {
                if (elements == null) {
                    throw new IllegalArgumentException(
                        "an ARRAY view must carry its element views in elements");
                }
            }
            default -> {
                // NULL, MISSING, BOOLEAN, STRING, BYTES, TABLE,
                // ASYNC_OPERATION, NOTHING, INVALID_UNICODE: no payload
                // field (a BYTES view is classification-only: it carries
                // no contents, K6 item 11).
            }
        }
        if (kind != ActualKind.CLASS && classId != null) {
            throw new IllegalArgumentException(
                "only a CLASS view carries a class id (a non-class actual kind never "
                    + "carries a class name)");
        }
        if (kind != ActualKind.NUMBER && kind != ActualKind.INT && numberValue != null) {
            throw new IllegalArgumentException(
                "only a NUMBER or INT view carries a numeric value");
        }
        if (kind != ActualKind.FUNCTION && functionSignature != null) {
            throw new IllegalArgumentException(
                "only a FUNCTION view carries a function signature");
        }
        if (kind != ActualKind.ARRAY && elements != null) {
            throw new IllegalArgumentException("only an ARRAY view carries element views");
        }
        if (elements != null) {
            elements = List.copyOf(elements);
        }
    }

    /** A payload-free view for {@code NULL}, {@code MISSING}, {@code BOOLEAN},
     *  {@code INT}, {@code STRING}, {@code BYTES}, {@code TABLE},
     *  {@code ASYNC_OPERATION}, {@code NOTHING}, and {@code INVALID_UNICODE}. */
    public static BoundaryValueView of(ActualKind kind) {
        Objects.requireNonNull(kind, "kind must not be null");
        return switch (kind) {
            case NULL, MISSING, BOOLEAN, INT, STRING, BYTES, TABLE, ASYNC_OPERATION,
                 NOTHING, INVALID_UNICODE ->
                new BoundaryValueView(kind, null, null, null, null);
            case CLASS, NUMBER, FUNCTION, ARRAY ->
                throw new IllegalArgumentException(kind
                    + " carries a payload; use the payload-bearing factory");
        };
    }

    /** An {@code INT} view carrying its exact signed32 value. */
    public static BoundaryValueView ofInt(long value) {
        if (value < -2147483648L || value > 2147483647L) {
            throw new IllegalArgumentException(
                "an INT view value must be signed32, got " + value);
        }
        return new BoundaryValueView(ActualKind.INT, null, (double) value, null, null);
    }

    /** A {@code NUMBER} view carrying its IEEE-754 value (NaN/infinity included). */
    public static BoundaryValueView ofNumber(double value) {
        return new BoundaryValueView(ActualKind.NUMBER, null, value, null, null);
    }

    /** A {@code CLASS} view carrying the canonical {@code @modulePath/ClassName} atom text. */
    public static BoundaryValueView ofClass(String classId) {
        Objects.requireNonNull(classId, "classId must not be null");
        if (classId.isEmpty()) {
            throw new IllegalArgumentException("classId must not be empty");
        }
        return new BoundaryValueView(ActualKind.CLASS, classId, null, null, null);
    }

    /** A {@code FUNCTION} view carrying the value's actual signature. */
    public static BoundaryValueView ofFunction(RuntimeDescriptor.Func signature) {
        Objects.requireNonNull(signature, "signature must not be null");
        return new BoundaryValueView(ActualKind.FUNCTION, null, null, signature, null);
    }

    /** An {@code ARRAY} view carrying its element views in index order. */
    public static BoundaryValueView ofArray(BoundaryValueView... elements) {
        Objects.requireNonNull(elements, "elements must not be null");
        return ofArray(List.of(elements));
    }

    /** An {@code ARRAY} view carrying its element views in index order. */
    public static BoundaryValueView ofArray(List<BoundaryValueView> elements) {
        Objects.requireNonNull(elements, "elements must not be null");
        return new BoundaryValueView(ActualKind.ARRAY, null, null, null,
            List.copyOf(elements));
    }

    /** The language-null view ({@code ActualKind.NULL}). */
    public static BoundaryValueView nullView() {
        return of(ActualKind.NULL);
    }
}
