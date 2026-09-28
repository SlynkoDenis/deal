package deal.semantic.ir;

import java.util.Objects;

/**
 * The closed normalized slot of {@code INDEX_NORMALIZE}
 * (assignment-delete-address-chains A-D3; parent common-semantic-lowering-layer
 * D14): the sealed two-shape record computed from the normalize payload's
 * {@code {mode, rawKey, currentLength}} triple.
 *
 * <p><b>Closed shapes (A-D3).</b></p>
 *
 * <ul>
 *   <li>Array modes → {@link ArraySlot} — {@code {index: signed32,
 *       present: index < currentLength, append: index == currentLength
 *       (ARRAY_WRITE only)}}. {@code present} is the {@code ARRAY_READ}
 *       decision; {@code append} is the {@code ARRAY_WRITE} decision (the
 *       append idiom {@code xs[xs.length] = v} normalizes to
 *       {@code append = true}). Negative and out-of-range indices are
 *       represented exactly — the computation never fails and never
 *       enforces bounds: negative/out-of-range enforcement happens only in
 *       the named boundary policies ({@code ARRAY_READ_INDEX_THEN_DESCRIPTOR},
 *       {@code ARRAY_WRITE_BOUNDS_THEN_ELEMENT},
 *       {@code ARRAY_DELETE_BOUNDS}), never in the normalize.</li>
 *   <li>Table modes → {@link TableSlot} — {@code {key: string}}. The key is
 *       total over lowering-reachable targets: A-D10's E3018 checker gate
 *       pins every table index write/delete key to static type
 *       {@code string} before lowering, so the computation performs no
 *       coercion and key identity is preserved exactly ({@code t["0"]}
 *       stays distinct from any other key). For table modes the closed
 *       payload's required {@code currentLength} operand references the raw
 *       key identity and is unused by the computation — no length read
 *       occurs for table targets.</li>
 *   <li>Bytes modes → {@link BytesSlot} — {@code {index: signed32,
 *       present: index < currentLength}} (K6 item 5). There is no append
 *       decision: a bytes buffer is fixed-length and an index equal to the
 *       length is the boundary's pinned E8012, never an append. Negative
 *       and out-of-range indices are represented exactly — the computation
 *       never fails and never enforces bounds.</li>
 * </ul>
 *
 * <p><b>Purity.</b> {@code INDEX_NORMALIZE} remains pure: policy
 * {@code NO_DEAL_FAILURE} (validator-pinned, R-POLICY-KIND), never raises
 * a DEAL failure, never raises E8002, and touches no storage beyond its
 * completed operands. The computation here is total and deterministic over
 * the closed mode set; a mode outside the computation's shape fails closed
 * with {@link IllegalArgumentException} (an internal producer error, never
 * a DEAL projection). The commit consumes the normalize-computed
 * {@code append} decision; observably this equals a commit-time length
 * comparison because no chain step between normalize and commit mutates
 * storage.</p>
 *
 * <p><b>Result type (A-D3).</b> The normalize op's result {@code ValueId}
 * carries the slot's index/key value with
 * {@link ArraySlot#resultType()} = {@code int},
 * {@link BytesSlot#resultType()} = {@code int}, and
 * {@link TableSlot#resultType()} = {@code string}.</p>
 *
 * <p>This record is computation-only: the {@code INDEX_NORMALIZE} op's
 * result wiring is the chain-lowering task's production; the closed
 * payload shapes and the schema-owned records are unchanged.</p>
 */
public sealed interface NormalizedSlot
    permits NormalizedSlot.ArraySlot, NormalizedSlot.BytesSlot, NormalizedSlot.TableSlot {

    /**
     * The closed array slot: the signed32 index plus the {@code present}
     * and {@code append} decisions ({@code present = index <
     * currentLength}; {@code append = index == currentLength} for
     * {@code ARRAY_WRITE}, always {@code false} for {@code ARRAY_READ}).
     *
     * @param index   the raw array index, signed 32-bit exactly (a Java
     *                {@code int}; no safe-range representation exists)
     * @param present {@code index < currentLength} — the {@code ARRAY_READ}
     *                decision (present/absent)
     * @param append  {@code index == currentLength} — the
     *                {@code ARRAY_WRITE} append decision
     */
    record ArraySlot(int index, boolean present, boolean append) implements NormalizedSlot {

        @Override
        public RuntimeDescriptor resultType() {
            return RuntimeDescriptor.Int.INSTANCE;
        }
    }

    /**
     * The closed bytes slot ({@code BYTES_READ}/{@code BYTES_WRITE}): the
     * signed32 index plus the {@code present} decision
     * ({@code present = index < currentLength}). No append decision exists
     * — a bytes buffer is fixed-length and {@code index == currentLength}
     * is the boundary's pinned E8012; negative and out-of-range indices
     * are represented exactly (the computation never enforces bounds).
     *
     * @param index   the raw bytes index, signed 32-bit exactly (a Java
     *                {@code int}; no safe-range representation exists)
     * @param present {@code index < currentLength} — the
     *                {@code BYTES_READ}/{@code BYTES_WRITE} bounds decision
     */
    record BytesSlot(int index, boolean present) implements NormalizedSlot {

        @Override
        public RuntimeDescriptor resultType() {
            return RuntimeDescriptor.Int.INSTANCE;
        }
    }

    /**
     * The closed table slot: the raw string key with identity preserved
     * exactly (no coercion; {@code "0"} stays distinct from every other
     * key). Total over lowering-reachable targets by A-D10's E3018
     * static-string gate.
     *
     * @param key the raw string key; non-null
     */
    record TableSlot(String key) implements NormalizedSlot {

        public TableSlot {
            Objects.requireNonNull(key, "key must not be null");
        }

        @Override
        public RuntimeDescriptor resultType() {
            return RuntimeDescriptor.String.INSTANCE;
        }
    }

    /**
     * The {@code INDEX_NORMALIZE} result type this slot pins (A-D3):
     * {@code int} for array modes, {@code string} for table modes.
     *
     * @return the pinned result-type descriptor
     */
    RuntimeDescriptor resultType();

    /**
     * Computes the closed array slot from the raw index and the current
     * length (A-D3). Pure, total, deterministic: no bounds enforcement, no
     * failure, and negative/out-of-range indices are represented exactly —
     * enforcement happens only in the named boundary policies.
     *
     * <ul>
     *   <li>{@code ARRAY_READ}: {@code present = index < currentLength},
     *       {@code append = false}.</li>
     *   <li>{@code ARRAY_WRITE}: {@code present = index < currentLength},
     *       {@code append = index == currentLength} (the append idiom
     *       {@code xs[xs.length] = v} normalizes to
     *       {@code append = true}).</li>
     * </ul>
     *
     * @param mode          the normalize mode; must be {@code ARRAY_READ}
     *                      or {@code ARRAY_WRITE}
     * @param index         the raw array index (signed32)
     * @param currentLength the array length read at normalize time
     * @return the computed {@link ArraySlot}
     * @throws IllegalArgumentException if {@code mode} is a table mode (an
     *         internal producer error — the closed table-mode computation
     *         is {@link #tableSlot(IndexMode, String)})
     */
    static ArraySlot arraySlot(IndexMode mode, int index, int currentLength) {
        Objects.requireNonNull(mode, "mode must not be null");
        return switch (mode) {
            case ARRAY_READ -> new ArraySlot(index, index < currentLength, false);
            case ARRAY_WRITE -> new ArraySlot(index, index < currentLength,
                index == currentLength);
            default -> throw new IllegalArgumentException(
                "arraySlot computes ARRAY_READ/ARRAY_WRITE slots only, got " + mode
                    + " (the closed table-mode computation is tableSlot)");
        };
    }

    /**
     * Computes the closed bytes slot from the raw index and the current
     * length (K6 item 5): {@code present = index < currentLength} for both
     * bytes modes; no append decision exists. Pure, total, deterministic:
     * no bounds enforcement, no failure, and negative/out-of-range indices
     * are represented exactly — enforcement happens only in the named
     * boundary policies ({@code BYTES_READ}/{@code BYTES_WRITE}).
     *
     * @param mode          the normalize mode; must be {@code BYTES_READ}
     *                      or {@code BYTES_WRITE}
     * @param index         the raw bytes index (signed32)
     * @param currentLength the bytes length read at normalize time
     * @return the computed {@link BytesSlot}
     * @throws IllegalArgumentException if {@code mode} is not a bytes mode
     *         (an internal producer error — the closed array/table
     *         computations are {@link #arraySlot(IndexMode, int, int)} and
     *         {@link #tableSlot(IndexMode, String)})
     */
    static BytesSlot bytesSlot(IndexMode mode, int index, int currentLength) {
        Objects.requireNonNull(mode, "mode must not be null");
        return switch (mode) {
            case BYTES_READ, BYTES_WRITE -> new BytesSlot(index, index < currentLength);
            default -> throw new IllegalArgumentException(
                "bytesSlot computes BYTES_READ/BYTES_WRITE slots only, got " + mode
                    + " (the closed array/table computations are arraySlot/tableSlot)");
        };
    }

    /**
     * Computes the closed table slot from the raw string key (A-D3). No
     * coercion is performed and key identity is preserved exactly; the
     * closed payload's required {@code currentLength} operand is unused by
     * the computation (no length read occurs for table targets) and is
     * therefore absent from this surface.
     *
     * @param mode the normalize mode; must be {@code TABLE_READ} or
     *             {@code TABLE_WRITE}
     * @param key  the raw string key; non-null
     * @return the computed {@link TableSlot} carrying the identical key
     * @throws NullPointerException     if {@code mode} or {@code key} is null
     * @throws IllegalArgumentException if {@code mode} is an array mode (an
     *         internal producer error — the closed array-mode computation
     *         is {@link #arraySlot(IndexMode, int, int)})
     */
    static TableSlot tableSlot(IndexMode mode, String key) {
        Objects.requireNonNull(mode, "mode must not be null");
        Objects.requireNonNull(key, "key must not be null");
        return switch (mode) {
            case TABLE_READ, TABLE_WRITE -> new TableSlot(key);
            default -> throw new IllegalArgumentException(
                "tableSlot computes TABLE_READ/TABLE_WRITE slots only, got " + mode
                    + " (the closed array-mode computation is arraySlot)");
        };
    }
}
