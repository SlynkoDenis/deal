package deal.semantic.ir;

import java.util.Objects;

/**
 * The minimal execution context a boundary cell names (ISSUE-0233 design
 * D3): exactly {@code {parameterIndex?, index?, length?, elementIndex?,
 * fieldPath?}} — one field per context-bearing cell of the closed
 * 13-policy subset, all optional because every field is named by at most
 * one cell.
 *
 * <ul>
 *   <li>{@code parameterIndex} — the {@code HOST_PARAMETER} boundary's
 *       one-based position among the invocation's parameter boundaries
 *       (the invocation machine's fact; retained pin
 *       {@code deal/runtime.lua:593-605}).</li>
 *   <li>{@code index} — the array index for the
 *       {@code ARRAY_READ_INDEX_THEN_DESCRIPTOR},
 *       {@code ARRAY_WRITE_BOUNDS_THEN_ELEMENT}, and
 *       {@code ARRAY_DELETE_BOUNDS} cells, and the bytes index for the
 *       {@code BYTES_READ}/{@code BYTES_WRITE} cells.</li>
 *   <li>{@code length} — the array length at check time for the write and
 *       delete bounds cells, and the bytes length for the
 *       {@code BYTES_READ}/{@code BYTES_WRITE} cells.</li>
 *   <li>{@code elementIndex} — the {@code ARRAY_ELEMENT_DESCRIPTOR}
 *       boundary's one-based element position ({@code {oneBasedIndex}}).</li>
 *   <li>{@code fieldPath} — the {@code JSON_TO_ERROR} boundary's
 *       {@code {fieldPath}}.</li>
 * </ul>
 *
 * <p>The executor validates required-ness and ranges fail closed: a
 * context-bearing cell executed without its required context is a
 * producer defect ({@link BoundaryExecutor.Defect}), never a DEAL
 * projection. The context carries no invocation state — fields are
 * machine-supplied inputs, never derived here (ISSUE-0236 owns the
 * invocation state machine).</p>
 */
public record BoundaryContext(
    Integer parameterIndex,
    Integer index,
    Integer length,
    Integer elementIndex,
    String fieldPath
) {

    /** The empty context: no cell names a field. */
    public static BoundaryContext none() {
        return new BoundaryContext(null, null, null, null, null);
    }

    /** The {@code HOST_PARAMETER} context: one-based parameter position. */
    public static BoundaryContext parameter(int oneBasedParameterIndex) {
        if (oneBasedParameterIndex < 1) {
            throw new IllegalArgumentException(
                "parameterIndex is one-based, got " + oneBasedParameterIndex);
        }
        return new BoundaryContext(oneBasedParameterIndex, null, null, null, null);
    }

    /** The {@code ARRAY_READ_INDEX_THEN_DESCRIPTOR} context: the read index. */
    public static BoundaryContext arrayIndex(int index) {
        return new BoundaryContext(null, index, null, null, null);
    }

    /** The {@code ARRAY_WRITE_BOUNDS_THEN_ELEMENT}/{@code ARRAY_DELETE_BOUNDS}
     *  context: the index and the array length at check time. */
    public static BoundaryContext writeBounds(int index, int length) {
        if (length < 0) {
            throw new IllegalArgumentException("length must be >= 0, got " + length);
        }
        return new BoundaryContext(null, index, length, null, null);
    }

    /**
     * The bytes cells' context (K6 item 3): the bytes index and the
     * receiver's length at check time — the read's own length read for
     * {@code BYTES_READ}, the chain's length child for
     * {@code BYTES_WRITE}.
     */
    public static BoundaryContext bytesBounds(int index, int length) {
        if (length < 0) {
            throw new IllegalArgumentException("length must be >= 0, got " + length);
        }
        return new BoundaryContext(null, index, length, null, null);
    }

    /** The {@code ARRAY_ELEMENT_DESCRIPTOR} context: one-based element position. */
    public static BoundaryContext element(int oneBasedElementIndex) {
        if (oneBasedElementIndex < 1) {
            throw new IllegalArgumentException(
                "elementIndex is one-based, got " + oneBasedElementIndex);
        }
        return new BoundaryContext(null, null, null, oneBasedElementIndex, null);
    }

    /** The {@code JSON_TO_ERROR} context: the field path of the failing value. */
    public static BoundaryContext jsonField(String fieldPath) {
        Objects.requireNonNull(fieldPath, "fieldPath must not be null");
        return new BoundaryContext(null, null, null, null, fieldPath);
    }
}
