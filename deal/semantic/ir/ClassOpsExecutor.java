package deal.semantic.ir;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.Map;
import java.util.Objects;
import java.util.function.Supplier;

/**
 * The single op-level execution form of the class-construction operations
 * of {@code deal.semantic-ir/1} (class-construction-jsonable-operations
 * K-D4/K-D11; ISSUE-0512; parent D16 and the normative construction
 * section, the closed {@code CLASS_NEW}/{@code CLASS_DEFAULT} operation
 * rows, and the {@code CLASS_CONSTRUCTION} E8007 policy row): a static,
 * pure, deterministic, stateless executor over the closed value view —
 * extended with the class variant
 * {@code Class {classId, fields: [Present(Value) | Missing]}} preserving
 * missing versus null — plus the value lookup for payload-referenced
 * provided-field prior steps. The sequencing item 2 child (ISSUE-0512)
 * introduced the executor with the
 * {@code CLASS_DEFAULT}/{@code CLASS_NEW(LOCAL)} surface and the pinned
 * delegate seams; this child (sequencing item 3, ISSUE-0513) completes
 * the field-operation surface — {@code FIELD_READ}/{@code FIELD_WRITE}/
 * {@code FIELD_DELETE} with the nominal receiver boundary first and the
 * presence-aware read/commit/idempotent-delete semantics (K-D6) and
 * {@code HAS_FIELD} with the presence boolean (K-D7). The sequencing
 * item 4 child (ISSUE-0514) completes the cross-unit default filling —
 * {@code CLASS_FACTORY} with the K-D5 execution contract (the
 * {@code CLASS_NEW(SHARED_FACTORY)} trigger, the skip-provided rule,
 * the untagged internal transfer, the executed cross-unit
 * {@code parentOpId} pin) and {@code CLASS_NEW(SHARED_FACTORY)} with
 * the K-D4 transfer order, the overlay reorder pin, the
 * {@code CLASS_DEFAULT_FIELD} extraction rule, and the tag-last
 * publication. The {@code JSON_*} surfaces complete the assembled
 * executor in this child (sequencing item 5, ISSUE-0515): the
 * {@code JSON_FROM_CLASS} walk (K-D8/K-D9 — the parse seam, the
 * top-level gate with the {@code {}}/{@code []} collapse, the
 * document-order extra-key gate, the declaration-order provided
 * decode, the per-site {@code CLASS_DEFAULT} children of the
 * {@code JsonDefaultChildTable} record, the nested-class
 * {@code CLASS_FACTORY} trigger, the final validation, the tag, and
 * the {@code JSON_MAX_DEPTH} bound) and the {@code JSON_TO_CLASS}
 * walk (K-D10 — the root identity check, the declaration-order
 * serialization with the pinned fieldPath convention, the
 * path-local cycle set, the call-origin {@code JSON_TO_ERROR}
 * projection, and deterministic RFC-8259 text) over the JSON
 * algorithm delegate seam (K-D11 — E8's
 * {@code SharedStdlibSemantics} is the production delegate). The
 * extern-C C-struct surface ({@link #executeClassNewFfiPlan};
 * ISSUE-0667) executes the runtime entry's four phases over the
 * closed plan projection: the provided fields' boundary children,
 * the provided-source-order extra-key guard, the omitted
 * required-present fields' deferred defaults exactly once per
 * attempt in class source order, the per-field descriptor
 * validation, and the declaration-order publication — with no
 * generated evaluator content and no native code.
 *
 * <p><b>Interpretation surface.</b> The executor interprets only
 * validated op shapes ({@link SemanticOp} records whose kind/payload
 * pairing the {@code SemanticOp} constructor has already enforced) and
 * the closed {@link Value} view — never AST nodes, never target
 * representations, never host code, never identity-keyed checker state.
 * A shape outside the pinned contracts — a wrong op kind, a non-pinned
 * failure policy, a non-{@code LOCAL} default owner, an unresolvable
 * lookup value, a wrong-kind value, a boundary child of the wrong kind
 * or parentage, a child-count mismatch, or an input-wiring mismatch —
 * fails closed as a producer {@link Defect}, never as a DEAL projection
 * and never as a crash (the same fail-closed discipline as
 * {@link ContainerOpsExecutor} and {@link BoundaryExecutor}).</p>
 *
 * <p><b>Value lookup.</b> Every payload-referenced provided-field prior
 * step resolves through the caller-supplied {@code Map<ValueId, Value>}
 * in literal order before the op's behavior runs (K-D4 step 1). A
 * referenced prior step the lookup does not resolve is a producer defect
 * (prior steps complete before operation START in the validated machine,
 * so the oracle's lookup always resolves). A provided value resolving to
 * the internal {@link Value.Missing} is a producer defect — a provided
 * field always carries a present value, and the missing state exists
 * only for absent slots of the constructed instance.</p>
 *
 * <p><b>Layout resolution.</b> The payload carries the layout; the
 * caller-supplied {@code Map<ClassId, ClassLayout>} is the
 * layout-resolution context (K-D11: the unit's {@code classLayouts} plus
 * the project interface index). The executor resolves the payload's
 * {@code classId} against the context and requires the resolved layout
 * to be exactly the payload's layout — an unresolvable or mismatched
 * layout is a producer defect (the payload is never interpreted against
 * a foreign layout).</p>
 *
 * <p><b>Boundary orchestration (K-D4 step 5, pinned).</b> The executor
 * creates no boundary projection: every field boundary is driven through
 * the {@link BoundaryCheckRunner} delegate seam
 * ({@code (BoundaryPayload, Value) → Pass | Fail}) strictly in payload
 * (declaration) order; the first failing child fails the op with that
 * child's failure and no instance is published (the tag never runs). The
 * delegate is E4's {@link BoundaryExecutor} in production; this epic's
 * unit tests use pass-through/fail-first fixtures. The pinned child
 * wiring is checked fail closed before each run: kind
 * {@code CLASS_LITERAL_FIELD}/{@code CLASS_DEFAULT_FIELD} matching the
 * payload entry, {@code parentOpId} = the {@code CLASS_NEW} op, the
 * field's declared descriptor, the descriptor-kind policy
 * ({@code TYPE_DESCRIPTOR} for non-function descriptors,
 * {@code FUNCTION_SIGNATURE} for function descriptors), and the input —
 * the field's {@code valueOpId} for provided fields, the field's
 * {@code CLASS_DEFAULT} op result {@code ValueId} for defaulted fields
 * (K-D4 input wiring).</p>
 *
 * <p><b>Default application (K-D4 step 2, pinned).</b>
 * {@code CLASS_DEFAULT} children execute in declaration order through
 * the {@link BodyRunner} seam — the block runs exactly once per
 * triggering construction attempt and the callback returns the produced
 * default value; the op carries no boundary of its own and its policy is
 * {@code NO_DEAL_FAILURE}. A child whose field is provided is skipped —
 * a provided field's default never runs. {@code CLASS_DEFAULT} ops are
 * detached structural ops (K-D12: their nesting owner is recorded by the
 * {@code CLASS_NEW} payload's {@code classDefaultOpIds}, not by a static
 * {@code parentOpId}), so the executor checks payload membership and
 * {@code classId} coherence instead of parentage. Per-construction
 * freshness is produced by block re-execution: each triggering attempt
 * invokes the body runner again, so a literal-typed default allocates
 * freshly per attempt (the oracle's machine re-executes the block; this
 * executor pins the per-trigger invocation protocol).</p>
 *
 * <p><b>The closed K-D4 order of {@code CLASS_NEW(LOCAL)}.</b>
 * (1) provided values resolve in literal order; (2) default application
 * for omitted required-present fields with declared defaults in
 * declaration order, skipping provided fields; (3) extra-key rejection
 * first in provided-source order — the first provided name not in the
 * layout fails {@code CLASS_CONSTRUCTION} with the registry row's pinned
 * E8007 {@code extra field '{field}' in class '{classId}'} at the op
 * origin, after default application and before any provided-field
 * application or field validation; (4) provided-field application in
 * declaration order (the overlay onto the default-filled instance — the
 * {@code jvm-xmod-class-construction-defaults} reorder pin); (5) field
 * validation in declaration order through the
 * {@link BoundaryCheckRunner} seam per {@code fieldBoundaries} entry;
 * (6) the fresh instance is tagged with {@code classId} and SUCCESS
 * publishes it. A failure at any step publishes no partial instance (the
 * tag never runs); completed children's effects remain observable.
 * {@code CLASS_NEW} runs zero return boundaries and the executor never
 * drives a {@code FUNCTION_RETURN} child.</p>
 *
 * <p><b>Failure rows.</b> The E8007 projection is instantiated from the
 * pinned {@link FailureContractRegistry} {@code CLASS_CONSTRUCTION} row
 * through {@link BoundaryFailure#fromRow} with the row's metadata
 * ({@code field}, {@code classId}) — the executor never selects message
 * text, and consumers never select messages. {@link OpFailure} pairs the
 * structured projection with the executed op's origin (the operation
 * origin of the closed table's rule).</p>
 *
 * <p><b>Purity and bounds.</b> No mutation of the unit, no randomness,
 * no I/O, no host code, no retry, no {@code deal.types} dependency; the
 * executor is linear in the provided-field count, the default count, the
 * boundary count, and the layout's field count, and delegates
 * descriptor-depth work to the boundary delegate (this component
 * recurses over no descriptor). Fresh instances carry fresh identities
 * (the model's allocation rule); repeated executions with equal inputs
 * produce equal results.</p>
 */
public final class ClassOpsExecutor {

    private ClassOpsExecutor() {
        // Static surface only; pure and stateless.
    }

    // =========================================================================
    // Producer defects (fail closed, never a DEAL projection)
    // =========================================================================

    /**
     * An executor producer defect: a shape outside the pinned contracts
     * reached the executor — a wrong op kind, a non-pinned failure
     * policy, a non-{@code LOCAL} default owner or a non-null factory
     * ref, an unresolvable or mismatched layout, an unresolvable
     * provided-field prior step, a wrong-kind value, a boundary child of
     * the wrong kind or parentage, a child-count/order mismatch, an
     * input-wiring mismatch, a {@code CLASS_DEFAULT} child of the wrong
     * kind/policy/class, or a duplicate default child. Internal control
     * flow — fail closed, never a DEAL projection and never a crash (the
     * validated-shapes-only discipline).
     */
    public static final class Defect extends RuntimeException {

        private static final long serialVersionUID = 1L;

        public Defect(String message) {
            super(message);
        }
    }

    // =========================================================================
    // The closed value view, extended with the class variant
    // =========================================================================

    /**
     * The closed value view the executor consumes and produces over the
     * semantic value model: the {@link ContainerOpsExecutor} view
     * extended with the class variant (K-D4: the construction result)
     * — language null, boolean, signed32 int, IEEE-754 number, string
     * (carrying the closed {@link UnicodeScalars.ScalarString}
     * classification), table ({@link SemanticTable}), array
     * ({@link SemanticArray}), bytes ({@link Value.Bytes}, K6 items
     * 10/11), class ({@link Value.Class}), function
     * (carrying the closed signature for the descriptor-kind rule's
     * {@code FUNCTION_SIGNATURE} cells), and the internal
     * {@code missing} (the schema's {@link ActualKind#MISSING}, never a
     * Java null reference). Async-operation values are never produced or
     * consumed by construction, so the view does not carry them.
     *
     * <p>A class value carries the canonical {@code classId} tag and its
     * fields in declaration order as {@link FieldState}
     * {@code Present(Value) | Missing} — present null (the explicit
     * {@link Null} variant) is {@code Present} and is distinguishable
     * from {@code Missing}, so the three presence states (missing,
     * present null, present value) are preserved exactly (K-D6's
     * storage discipline). A {@code Present} field never carries the
     * internal {@code Missing} view (fail closed).</p>
     *
     * <p>Every variant renders its canonical actual kind
     * ({@link ActualKind}): a {@link String} view renders
     * {@code STRING} for a {@code Valid} scalar sequence and
     * {@code INVALID_UNICODE} for an {@code Invalid} one; a
     * {@link Class} view renders {@code CLASS} with the canonical
     * {@code class:<ClassId>} atom text. Null references never appear:
     * language null is the explicit {@link Null} variant, and absent
     * fields are the explicit {@link Missing} state.</p>
     */
    public sealed interface Value
        permits Value.Null, Value.Bool, Value.Int, Value.Number, Value.String,
                Value.Table, Value.Array, Value.Bytes, Value.Class, Value.Function,
                Value.Missing {

        /** The canonical actual kind this value renders as. */
        ActualKind actualKind();

        /** A string view carrying the validated classification of {@code carrier}. */
        static Value string(java.lang.String carrier) {
            return new String(UnicodeScalars.validate(carrier));
        }

        /** Language null (the explicit {@code ActualKind#NULL}). */
        enum Null implements Value {
            INSTANCE;

            @Override
            public ActualKind actualKind() {
                return ActualKind.NULL;
            }
        }

        /** A boolean value. */
        record Bool(boolean value) implements Value {

            @Override
            public ActualKind actualKind() {
                return ActualKind.BOOLEAN;
            }
        }

        /** A signed32 integer value. */
        record Int(int value) implements Value {

            @Override
            public ActualKind actualKind() {
                return ActualKind.INT;
            }
        }

        /** An IEEE-754 number value (NaN and infinity included). */
        record Number(double value) implements Value {

            @Override
            public ActualKind actualKind() {
                return ActualKind.NUMBER;
            }
        }

        /**
         * A string value carrying the closed scalar classification
         * ({@link UnicodeScalars.ScalarString}): {@code Valid} renders
         * {@link ActualKind#STRING}, {@code Invalid} renders
         * {@link ActualKind#INVALID_UNICODE}. The classification is
         * never normalized away.
         */
        record String(UnicodeScalars.ScalarString scalar) implements Value {

            public String {
                Objects.requireNonNull(scalar, "scalar must not be null");
            }

            @Override
            public ActualKind actualKind() {
                return scalar.actualKind();
            }
        }

        /** A table value carrying its first-insertion-order model. */
        record Table(SemanticTable<Value> table) implements Value {

            public Table {
                Objects.requireNonNull(table, "table must not be null");
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.TABLE;
            }
        }


        /**
         * A bytes buffer view (K6 item 10): the same mutable storage as the
         * oracle's bytes value, shared by every alias, so an element write
         * through one view is observed through every other. The logical
         * length is fixed at allocation and never changes; the view is
         * classification-only for boundary projection (K6 item 11).
         */
        record Bytes(byte[] storage, int length) implements Value {

            public Bytes {
                Objects.requireNonNull(storage, "storage must not be null");
                if (length < 0 || length > storage.length) {
                    throw new Defect("a bytes view's logical length " + length
                        + " is outside its storage of " + storage.length
                        + " byte(s)");
                }
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.BYTES;
            }
        }

        /** An array value carrying its ordered element list. */
        record Array(SemanticArray<Value> array) implements Value {

            public Array {
                Objects.requireNonNull(array, "array must not be null");
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.ARRAY;
            }
        }

        /**
         * A class instance: the canonical {@code classId} tag plus its
         * fields in declaration order as {@link FieldState}
         * {@code Present(Value) | Missing}. Present null (the explicit
         * {@link Null} variant) stays {@code Present} and is
         * distinguishable from {@code Missing}; a {@code Present} field
         * never carries the internal {@code Missing} view (fail closed).
         */
        record Class(ClassId classId, List<FieldState> fields) implements Value {

            public Class {
                Objects.requireNonNull(classId, "classId must not be null");
                Objects.requireNonNull(fields, "fields must not be null");
                fields = List.copyOf(fields);
                for (FieldState field : fields) {
                    if (field instanceof FieldState.Present present
                            && present.value() instanceof Missing) {
                        throw new Defect("a present class field never carries the internal "
                            + "Missing view — a field value is language null (Null), a "
                            + "value, or the field is absent (the Missing field state): "
                            + "a shape outside the pinned contracts, never executed");
                    }
                }
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.CLASS;
            }
        }

        /** A function value carrying its closed signature (descriptor-kind rule). */
        record Function(RuntimeDescriptor.Func signature) implements Value {

            public Function {
                Objects.requireNonNull(signature, "signature must not be null");
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.FUNCTION;
            }
        }

        /** The internal missing (an absent class field; never Java null). */
        enum Missing implements Value {
            INSTANCE;

            @Override
            public ActualKind actualKind() {
                return ActualKind.MISSING;
            }
        }
    }

    /**
     * One class-field state of the closed value view:
     * {@code Present(Value) | Missing}. Present null (the explicit
     * {@link Value.Null} variant) is {@code Present} — the three presence
     * states (missing, present null, present value) are distinct and are
     * never conflated.
     */
    public sealed interface FieldState permits FieldState.Present, FieldState.Missing {

        /** The field is present; {@code value} is its value (never the internal Missing). */
        record Present(Value value) implements FieldState {

            public Present {
                Objects.requireNonNull(value, "value must not be null");
                if (value instanceof Value.Missing) {
                    throw new Defect("a present class field never carries the internal "
                        + "Missing view — a present field holds language null (Null) or a "
                        + "value; absence is the Missing field state, never a field value");
                }
            }
        }

        /** The field is absent (the schema's internal missing). */
        enum Missing implements FieldState {
            INSTANCE;
        }
    }

    // =========================================================================
    // Op-level failure and outcome
    // =========================================================================

    /**
     * One op-level failure: the structured registry-row projection
     * (built with {@link BoundaryFailure#fromRow}) paired with the
     * executed op's origin — the operation origin of the closed table's
     * rule (for {@code CLASS_NEW} the extra-key scan reports at the op
     * origin; for a field-boundary child failure the parent op's origin —
     * the child's own origin stays observable through the unit's ops).
     */
    public record OpFailure(BoundaryFailure failure, SourceOrigin origin) {

        public OpFailure {
            Objects.requireNonNull(failure, "failure must not be null");
            Objects.requireNonNull(origin, "origin must not be null");
        }
    }

    /**
     * The closed terminal of one executor call:
     * {@code Success(value) | Failure(OpFailure)}. A {@code Failure} is
     * exactly one pinned projection — never a partial value and never a
     * retry. A failed {@code CLASS_NEW} publishes no partial instance:
     * the {@code Value.Class} exists only on the success path, so the
     * tag never runs on a failure (K-D4 step 6).
     *
     * @param <V> the success value type of the op (the produced default
     *            value or the fresh tagged instance)
     */
    public sealed interface Outcome<V> permits Outcome.Success, Outcome.Failure {

        /** The op succeeded; {@code value} is the published result. */
        record Success<V>(V value) implements Outcome<V> {

            public Success {
                Objects.requireNonNull(value, "value must not be null");
            }
        }

        /** The op failed; {@code failure} is the registry-row projection. */
        record Failure<V>(OpFailure failure) implements Outcome<V> {

            public Failure {
                Objects.requireNonNull(failure, "failure must not be null");
            }
        }
    }

    // =========================================================================
    // Boundary-check delegate seam (K-D11)
    // =========================================================================

    /**
     * The boundary-check delegate seam (K-D11): exactly
     * {@code (BoundaryPayload, Value) → Pass | Fail} — the closed value
     * view of the checked field input in, the published checked value or
     * the boundary's own failure out. E4's {@link BoundaryExecutor} is
     * the production delegate; this epic's unit tests use
     * pass-through/fail-first fixtures. The delegate owns every boundary
     * projection (the descriptor-kind rule's E8001/E8010); the executor
     * pins only the orchestration (declaration order, the first failure
     * fails the op, tag only after all validation).
     */
    @FunctionalInterface
    public interface BoundaryCheckRunner {

        /**
         * Runs one field-boundary check of the construction.
         *
         * @param boundary the child's pinned {@code BOUNDARY} payload
         *                 (kind, descriptor, input, realization)
         * @param input    the closed value view the child checks — the
         *                 provided value ({@code CLASS_LITERAL_FIELD})
         *                 or the default block's produced value
         *                 ({@code CLASS_DEFAULT_FIELD})
         * @return {@code Pass} with the published checked value, or
         *         {@code Fail} with the boundary's own failure
         */
        BoundaryResult run(KindPayload.BoundaryPayload boundary, Value input);
    }

    /**
     * The delegate's terminal: {@code Pass(value) | Fail(failure)}. The
     * first {@code Fail} of the field-boundary run fails the op with
     * that child's failure — no instance is published (the tag never
     * runs), and the later children never run.
     */
    public sealed interface BoundaryResult permits BoundaryResult.Pass, BoundaryResult.Fail {

        /**
         * The boundary passed; {@code value} is the delegate-published
         * checked value (a passing boundary never copies or converts).
         */
        record Pass(Value value) implements BoundaryResult {

            public Pass {
                Objects.requireNonNull(value, "value must not be null");
            }
        }

        /** The boundary failed; {@code failure} is its registry-row projection. */
        record Fail(BoundaryFailure failure) implements BoundaryResult {

            public Fail {
                Objects.requireNonNull(failure, "failure must not be null");
            }
        }
    }

    // =========================================================================
    // Body-runner seam (K-D11)
    // =========================================================================

    /**
     * The body-runner delegate seam (K-D11): executes one
     * {@code CLASS_DEFAULT} default block (the detached per-construction
     * block of the op's payload) exactly once for the current triggering
     * construction attempt and returns the block's produced default
     * value — the {@code CLASS_DEFAULT} op's result. E5's block machinery
     * is the production delegate; this epic's unit tests use scripted
     * fixtures recording every invocation (the invocation log proves the
     * declaration order and the skip-provided rule). Per-construction
     * freshness is realized by re-invocation: the executor calls the
     * runner again on every triggering attempt, so literal-typed defaults
     * allocate freshly per attempt. A default-block failure propagates as
     * the callback's own throw (the oracle's machine owns it), never as a
     * synthesized projection here.
     */
    @FunctionalInterface
    public interface BodyRunner {

        /**
         * Executes one {@code CLASS_DEFAULT} default block.
         *
         * @param defaultOp the validated {@code CLASS_DEFAULT} op whose
         *                  {@link KindPayload.ClassDefaultPayload#defaultBlock()}
         *                  is the block to run; non-null
         * @return the block's produced default value (the op's result);
         *         never the internal {@link Value.Missing} (a default
         *         block always produces a present value — fail closed)
         */
        Value runDefault(SemanticOp defaultOp);
    }

    // =========================================================================
    // CLASS_DEFAULT
    // =========================================================================

    /**
     * Executes one validated {@code CLASS_DEFAULT} op (K-D3/K-D4 step 2):
     * the default block runs exactly once for the current triggering
     * construction attempt through the {@link BodyRunner} seam and the
     * op publishes the produced default value. The op carries no boundary
     * of its own and its policy is {@code NO_DEAL_FAILURE}; it exists
     * only as a child of a triggering construction ({@code CLASS_NEW} or
     * {@code CLASS_FACTORY}), and its detached block is re-run on every
     * triggering attempt — per-construction freshness is produced by
     * block re-execution, never by deep copies.
     *
     * @param op         the validated {@code CLASS_DEFAULT} op; non-null
     * @param bodyRunner the default-block callback; non-null
     * @return {@code Success} with the block's produced default value
     * @throws Defect               if the op is not a
     *                              {@code CLASS_DEFAULT} carrying
     *                              {@code NO_DEAL_FAILURE}, or if the
     *                              produced value is the internal
     *                              {@link Value.Missing} (a default block
     *                              always produces a present value)
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeClassDefault(SemanticOp op, BodyRunner bodyRunner) {
        requireOp(op, SemanticOpKind.CLASS_DEFAULT, FailurePolicyId.NO_DEAL_FAILURE);
        Objects.requireNonNull(bodyRunner, "bodyRunner must not be null");
        Value produced = bodyRunner.runDefault(op);
        if (produced instanceof Value.Missing) {
            throw new Defect("CLASS_DEFAULT " + op.opId() + " produced the internal Missing "
                + "view: a default block always produces a present value (language null is "
                + "the explicit Null variant) — a wrong-kind value is a producer defect, "
                + "never executed");
        }
        return new Outcome.Success<Value>(produced);
    }

    // =========================================================================
    // CLASS_NEW(LOCAL)
    // =========================================================================

    /**
     * Executes one validated {@code CLASS_NEW} op with
     * {@code defaultOwner: LOCAL} in the closed K-D4/D16 order:
     *
     * <ol>
     *   <li>provided values resolve from the lookup in literal order
     *       ({@code providedFields} payload order);</li>
     *   <li>default application for omitted required-present fields with
     *       declared defaults — the {@code classDefaultOpIds}
     *       {@code CLASS_DEFAULT} children in declaration order through
     *       the {@link BodyRunner} seam, skipping any child whose field
     *       is provided (a provided field's default never runs);</li>
     *   <li>extra-key rejection first in provided-source order: the
     *       first provided name not in the layout fails
     *       {@code CLASS_CONSTRUCTION} — E8007
     *       {@code extra field '{field}' in class '{classId}'} at the op
     *       origin — after default application and before any
     *       provided-field application or field validation (the default
     *       side effects have completed, no provided field is applied,
     *       and no boundary runs after the scan fails);</li>
     *   <li>provided-field application in declaration order (the overlay
     *       onto the default-filled instance — the
     *       {@code jvm-xmod-class-construction-defaults} reorder pin;
     *       duplicate provided names keep the last provided value, the
     *       checker's literal-map rule);</li>
     *   <li>field validation in declaration order through the
     *       {@link BoundaryCheckRunner} seam per {@code fieldBoundaries}
     *       entry ({@code CLASS_LITERAL_FIELD} for provided fields,
     *       {@code CLASS_DEFAULT_FIELD} for defaulted fields; the pinned
     *       input wiring, declared descriptor, descriptor-kind policy,
     *       and {@code parentOpId} are checked fail closed before each
     *       run); omitted optional fields get no boundary and stay
     *       missing;</li>
     *   <li>the fresh instance is tagged with {@code classId}
     *       ({@code class:<ClassId>} canonical identity) and SUCCESS
     *       publishes it.</li>
     * </ol>
     *
     * A failure at any step publishes no partial instance (the
     * {@link Value.Class} exists only on the success path, so the tag
     * never runs); completed children's effects remain observable.
     * {@code CLASS_NEW} runs zero return boundaries — the executor never
     * drives a {@code FUNCTION_RETURN} child.
     *
     * @param op          the validated {@code CLASS_NEW} op carrying
     *                    {@code CLASS_CONSTRUCTION}; non-null
     * @param priorValues the resolved provided-field prior-step values;
     *                    non-null, no null entries
     * @param defaultOps  the unit's {@code CLASS_DEFAULT} ops by
     *                    {@link OpId}; every id of
     *                    {@code classDefaultOpIds} must resolve to a
     *                    {@code CLASS_DEFAULT} op of this classId
     *                    carrying {@code NO_DEAL_FAILURE}; non-null
     * @param boundaryOps the unit's boundary ops by {@link OpId}; every
     *                    {@code fieldBoundaries} id must resolve to a
     *                    {@code BOUNDARY} op parented to this op; non-null
     * @param layouts     the layout-resolution context
     *                    {@code ClassId → ClassLayout} (K-D11); the
     *                    payload's classId must resolve to exactly the
     *                    payload's layout; non-null
     * @param checkRunner the boundary-check delegate; non-null
     * @param bodyRunner  the default-block callback; non-null
     * @return {@code Success} with the fresh tagged instance after every
     *         field boundary passed, or {@code Failure} with the E8007
     *         extra-key projection or the first failing boundary's
     *         failure
     * @throws Defect               if the op is not a {@code CLASS_NEW}
     *                              carrying {@code CLASS_CONSTRUCTION},
     *                              if its default owner is not
     *                              {@code LOCAL} or its factory ref is
     *                              non-null, if the layout resolution
     *                              fails or mismatches, if a provided
     *                              value does not resolve or resolves to
     *                              the internal {@code Missing}, if a
     *                              default child or boundary child
     *                              violates the pinned shape, if the
     *                              field-boundary entries mismatch the
     *                              pinned declaration-order
     *                              count/kinds, or if an input-wiring
     *                              mismatch appears
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeClassNewLocal(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<OpId, SemanticOp> defaultOps,
            Map<OpId, SemanticOp> boundaryOps,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner,
            BodyRunner bodyRunner) {
        requireOp(op, SemanticOpKind.CLASS_NEW, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(defaultOps, "defaultOps must not be null");
        Objects.requireNonNull(boundaryOps, "boundaryOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        Objects.requireNonNull(bodyRunner, "bodyRunner must not be null");
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();
        // This child's surface: LOCAL execution only. SHARED_FACTORY
        // execution is executeClassNewSharedFactory's; the host
        // declaration class construction is
        // executeClassNewHostDefaults's; the builtin Error construction is
        // executeClassNewBuiltinDefaults's; RETAINED_ABI is E10's and the
        // extern-C FFI_PLAN owner is executeClassNewFfiPlan's — all fail
        // closed here, never silently executed as LOCAL.
        if (payload.defaultOwner() != DefaultOwner.LOCAL) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner "
                + payload.defaultOwner() + ": this executor surface is LOCAL "
                + "execution — SHARED_FACTORY transfer is "
                + "executeClassNewSharedFactory's, RETAINED_ABI transfer is E10's, "
                + "the host construction is executeClassNewHostDefaults's, the "
                + "builtin Error construction is executeClassNewBuiltinDefaults's, "
                + "and the extern-C FFI_PLAN construction is "
                + "executeClassNewFfiPlan's; "
                + "a non-LOCAL owner reaching executeClassNewLocal is a producer "
                + "defect, never executed");
        }
        if (payload.classFactoryRef() != null) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a non-null classFactoryRef "
                + payload.classFactoryRef() + ": the pinned LOCAL shape carries "
                + "classFactoryRef null (the factory ref exists only for "
                + "SHARED_FACTORY/RETAINED_ABI owners) — a producer defect, never "
                + "executed");
        }

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " does not resolve in the layout-resolution context: every "
                + "payload-referenced class resolves through the unit's classLayouts "
                + "(plus the project interface index) — an unresolvable layout is a "
                + "producer defect, never executed");
        }
        if (!layout.equals(payload.layout())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a layout that differs "
                + "from the resolution context's layout of " + payload.classId()
                + ": the payload's layout must be exactly the resolved layout — a "
                + "mismatch is a producer defect, never executed");
        }

        // K-D4 step 1: provided values resolve in literal order.
        LinkedHashMap<String, Value> providedValues = new LinkedHashMap<>();
        LinkedHashMap<String, ValueId> providedValueIds = new LinkedHashMap<>();
        resolveProvidedFields(op, payload, priorValues, null, providedValues,
            providedValueIds);

        // K-D4 step 2: default application in declaration order for omitted
        // required-present fields — skipping any child whose field is
        // provided (a provided field's default never runs).
        LinkedHashMap<String, Value> defaultValues = new LinkedHashMap<>();
        LinkedHashMap<String, SemanticOp> defaultOpsByField = applyClassDefaults(
            op, payload.classId(), payload.classDefaultOpIds(), defaultOps, layout,
            providedValues.keySet(),
            "default application runs for omitted required-present fields only — an"
                + " optional field's default never runs at construction (the field stays"
                + " missing), so a listed optional default is a producer defect, never"
                + " executed",
            bodyRunner, defaultValues);

        // K-D4 step 3: extra-key rejection first in provided-source order —
        // after default application, before any provided-field application
        // or field validation.
        Outcome.Failure<Value> extraKeyFailure =
            undeclaredProvidedFieldFailure(op, payload, layout);
        if (extraKeyFailure != null) {
            return extraKeyFailure;
        }

        // The pinned field-boundary coverage (K-D4 step 5 shape): exactly
        // one entry per provided field (CLASS_LITERAL_FIELD) and per
        // defaulted field (CLASS_DEFAULT_FIELD) in declaration order;
        // omitted optional fields get no boundary and stay missing. A
        // count, order, or kind deviation is a producer defect.
        List<KindPayload.FieldBoundary> boundaries = payload.fieldBoundaries();
        requireBoundaryShape(op, payload, layout, providedValues, boundaries,
            defaultValues::containsKey);

        // K-D4 step 4: provided-field application in declaration order (the
        // overlay onto the default-filled instance; duplicate names keep the
        // last provided value).
        LinkedHashMap<java.lang.String, Value> instanceFields = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value provided = providedValues.get(fieldLayout.name());
            Value defaultValue = defaultValues.get(fieldLayout.name());
            if (provided != null) {
                instanceFields.put(fieldLayout.name(), provided);
            } else if (defaultValue != null) {
                instanceFields.put(fieldLayout.name(), defaultValue);
            }
        }

        // K-D4 step 5: field validation in declaration order through the
        // BoundaryCheckRunner seam; the first failing child fails the op
        // and no instance is published.
        LinkedHashMap<String, Value> checkedValues = new LinkedHashMap<>();
        OpFailure fieldFailure = applyFieldBoundaries(op, payload, layout, boundaries,
            providedValues, providedValueIds, boundaryOps, checkRunner, checkedValues,
            (child, entry, boundaryPayload) -> {
                SemanticOp defaultOp = defaultOpsByField.get(entry.field());
                if (defaultOp == null) {
                    throw new Defect("CLASS_NEW " + op.opId() + " carries a "
                        + "CLASS_DEFAULT_FIELD boundary for field '" + entry.field()
                        + "' without a default child: the pinned kind names omitted "
                        + "required-present defaulted fields only — a producer defect, "
                        + "never executed");
                }
                if (!(defaultOp.result() instanceof ValueId resultId)) {
                    throw new Defect("CLASS_NEW " + op.opId() + " CLASS_DEFAULT child "
                        + defaultOp.opId() + " publishes a non-ValueId result "
                        + defaultOp.result() + ": the pinned CLASS_DEFAULT_FIELD input is "
                        + "the CLASS_DEFAULT op's result ValueId (K-D4 input wiring) — a "
                        + "producer defect, never executed");
                }
                if (!boundaryPayload.input().equals(resultId)) {
                    throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                        + child.opId() + " carries input " + boundaryPayload.input()
                        + ": the pinned CLASS_DEFAULT_FIELD input is the field's "
                        + "CLASS_DEFAULT op result " + resultId + " (K-D4 input wiring) — "
                        + "a mismatch is a producer defect, never executed");
                }
                return defaultValues.get(entry.field());
            });
        if (fieldFailure != null) {
            return new Outcome.Failure<Value>(fieldFailure);
        }
        instanceFields.putAll(checkedValues);

        // K-D4 step 6: tag the fresh instance with classId and SUCCESS
        // publishes it (declaration-order field states; omitted optionals
        // stay missing; present null stays present null).
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value value = instanceFields.get(fieldLayout.name());
            states.add(value == null ? FieldState.Missing.INSTANCE
                : new FieldState.Present(value));
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    // =========================================================================
    // CLASS_NEW (BUILTIN_DEFAULTS, the builtin Error construction)
    // =========================================================================

    /**
     * Executes one validated {@code CLASS_NEW} op carrying
     * {@code defaultOwner: BUILTIN_DEFAULTS} (ISSUE-0619;
     * {@code semantic-ir-construct-coverage-cutover} K13 items 2-4): the
     * builtin {@code Error} construction. The shape is the compiler-owned
     * one:
     *
     * <ol>
     *   <li>the op is a {@code CLASS_NEW} carrying
     *       {@code CLASS_CONSTRUCTION} for exactly {@link ClassId#ERROR}
     *       over exactly {@link ClassLayout#BUILTIN_ERROR}, with a null
     *       {@code classFactoryRef} and an empty
     *       {@code classDefaultOpIds} (there is no factory and no default
     *       block — the omitted fields take the compiler constant empty
     *       string at the construction site);</li>
     *   <li>the provided values resolve in literal order (K-D4 step 1); an
     *       undeclared provided name is a producer defect (the checker's
     *       E4002 rejects it before lowering);</li>
     *   <li>the field boundaries run in payload order through the
     *       {@link BoundaryCheckRunner} seam (K-D4 step 5) — exactly one
     *       {@code CLASS_LITERAL_FIELD} child per provided field with the
     *       field's declared descriptor and the provided value as its
     *       pinned input; the first failing child fails the op and no
     *       instance is published;</li>
     *   <li>the instance carries the two declared fields in declaration
     *       order, both present: the boundary-published provided value or
     *       the compiler constant empty string.</li>
     * </ol>
     *
     * <p>No default child runs: the builtin defaults are compiler
     * constants, never an evaluated default block or a factory transfer;
     * and no extra-key projection runs (the closed declared field set and
     * the checker's E4002 make an unknown provided name unreachable).</p>
     *
     * @param op          the validated {@code CLASS_NEW} op carrying
     *                    {@code CLASS_CONSTRUCTION} with
     *                    {@code defaultOwner: BUILTIN_DEFAULTS}; non-null
     * @param priorValues the resolved provided-field prior-step values;
     *                    non-null, no null entries
     * @param boundaryOps the unit's boundary ops by {@link OpId}; every
     *                    {@code fieldBoundaries} id must resolve to a
     *                    {@code BOUNDARY} op parented to this op; non-null
     * @param layouts     the layout-resolution context
     *                    {@code ClassId → ClassLayout}; the builtin class
     *                    must resolve to exactly
     *                    {@link ClassLayout#BUILTIN_ERROR}; non-null
     * @param checkRunner the boundary-check delegate; non-null
     * @return {@code Success} with the builtin Error instance (both fields
     *         present in declaration order) after every provided field
     *         boundary passed, or {@code Failure} with the first failing
     *         boundary's failure
     * @throws Defect               on a shape outside the pinned contract —
     *                              a wrong op kind/policy/owner, a
     *                              non-builtin class, a foreign layout, a
     *                              non-null factory ref, a non-empty default
     *                              child list, an unresolvable provided
     *                              value, an undeclared provided name, a
     *                              boundary child or entry outside the pinned
     *                              shape, or an input-wiring mismatch
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeClassNewBuiltinDefaults(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<OpId, SemanticOp> boundaryOps,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner) {
        requireOp(op, SemanticOpKind.CLASS_NEW, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(boundaryOps, "boundaryOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();

        // This child's surface: BUILTIN_DEFAULTS execution only. The host
        // declaration class construction (HOST_DEFAULTS) is
        // executeClassNewHostDefaults's and the extern-C FFI_PLAN
        // construction is executeClassNewFfiPlan's; a foreign owner
        // reaching this surface is a producer defect, never silently
        // executed.
        if (payload.defaultOwner() != DefaultOwner.BUILTIN_DEFAULTS) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner "
                + payload.defaultOwner() + ": this executor surface is the builtin"
                + " Error construction (BUILTIN_DEFAULTS) — LOCAL is"
                + " executeClassNewLocal's, SHARED_FACTORY transfer is"
                + " executeClassNewSharedFactory's, the host declaration class"
                + " construction is executeClassNewHostDefaults's, RETAINED_ABI"
                + " transfer is E10's, and the extern-C FFI_PLAN construction is"
                + " executeClassNewFfiPlan's; a foreign owner reaching"
                + " executeClassNewBuiltinDefaults"
                + " is a producer defect, never executed");
        }
        if (!ClassId.ERROR.equals(payload.classId())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner"
                + " BUILTIN_DEFAULTS for class " + payload.classId() + ": the"
                + " builtin-defaults owner is admissible only for the builtin Error"
                + " class " + ClassId.ERROR.text() + " — a non-builtin class under"
                + " BUILTIN_DEFAULTS is a producer defect, never executed");
        }
        if (payload.classFactoryRef() != null) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a non-null"
                + " classFactoryRef " + payload.classFactoryRef() + " under"
                + " BUILTIN_DEFAULTS: the builtin Error construction carries a null"
                + " factory ref (the builtin defaults are compiler constants, never a"
                + " factory transfer) — a producer defect, never executed");
        }
        if (!payload.classDefaultOpIds().isEmpty()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries "
                + payload.classDefaultOpIds() + " under BUILTIN_DEFAULTS: the builtin"
                + " Error construction carries an empty child list (the omitted fields"
                + " take the compiler constant empty string at the construction site)"
                + " — a producer defect, never executed");
        }

        // Layout resolution (K-D11): the builtin class resolves through the
        // compiler-owned layout entry, and the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null || !layout.equals(ClassLayout.BUILTIN_ERROR)) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId "
                + payload.classId() + " does not resolve to the compiler-owned"
                + " builtin Error layout in the layout-resolution context: the"
                + " builtin class is a compiler constant layout — an unresolvable or"
                + " foreign entry is a producer defect, never executed");
        }
        if (!layout.equals(payload.layout())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a layout that"
                + " differs from the compiler-owned builtin Error layout: the"
                + " payload's layout must be exactly the resolved layout — a mismatch"
                + " is a producer defect, never executed");
        }

        // Provided values resolve in literal order (K-D4 step 1); an
        // undeclared provided name is unreachable from the checker (E4002)
        // and stays fail closed.
        LinkedHashMap<String, Value> providedValues = new LinkedHashMap<>();
        LinkedHashMap<String, ValueId> providedValueIds = new LinkedHashMap<>();
        resolveProvidedFields(op, payload, priorValues, layout, providedValues,
            providedValueIds);

        // The pinned field-boundary coverage (K-D4 step 5 shape): exactly
        // one entry per provided field (CLASS_LITERAL_FIELD) in declaration
        // order — an omitted field gets no boundary (it takes the compiler
        // constant empty string).
        LinkedHashMap<String, Value> checkedValues = new LinkedHashMap<>();
        OpFailure fieldFailure = applyLiteralFieldBoundaries(op, payload, layout,
            providedValues, providedValueIds, payload.fieldBoundaries(), boundaryOps,
            checkRunner, checkedValues, "builtin Error shape");
        if (fieldFailure != null) {
            return new Outcome.Failure<Value>(fieldFailure);
        }

        // The instance: the declaration-order field states (both fields
        // present) — the boundary-published provided values and the compiler
        // constant empty string for the omitted fields.
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value value = checkedValues.get(fieldLayout.name());
            if (value == null) {
                value = Value.string("");
            }
            states.add(new FieldState.Present(value));
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    /**
     * The loaded host class defaults projection of one declared host
     * class (ISSUE-0624; {@code semantic-ir-construct-coverage-cutover}
     * K10 and the K10 contract): the oracle-side analog of the loaded
     * module's {@code <C>_defaults} entry — one entry per field name the
     * host's mandatory defaults table carries, an absent optional field
     * as the miss sentinel ({@link Value#MISSING}-equivalent
     * {@code null}/absent entry), and a class the seam supplies no
     * projection for as {@code null} (a fail-closed producer defect,
     * never an invented default). The executor consumes the projection as
     * data: it evaluates no host code and mutates no host state.
     */
    @FunctionalInterface
    public interface HostDefaultsProjection {

        /**
         * The loaded defaults of one declared host class, or {@code null}
         * when the seam supplies none.
         *
         * @param classId the declared host class's canonical identity;
         *                non-null
         * @return the field-name &#8594; value projection in the host's
         *         declaration order, or {@code null}
         */
        Map<String, Value> defaultsOf(ClassId classId);
    }

    /**
     * Executes one validated {@code CLASS_NEW} op carrying
     * {@code defaultOwner: HOST_DEFAULTS} (ISSUE-0624;
     * {@code semantic-ir-construct-coverage-cutover} K10 and the K10
     * contract): the pinned host construction phases over the loaded
     * host module's {@code <C>_defaults} entry —
     *
     * <ol>
     *   <li>provided values resolve in literal order (they completed
     *       before the op);</li>
     *   <li>the loaded defaults projection is consumed as data (the
     *       construction's per-attempt instance is fresh, so one attempt
     *       never mutates the next);</li>
     *   <li>extra-key rejection first in provided-source order: the first
     *       provided name the loaded defaults projection does not carry
     *       fails {@code CLASS_CONSTRUCTION} — E8007
     *       {@code extra field '{field}' in class '{classId}'} at the op
     *       origin — before any field validation;</li>
     *   <li>provided-field validation in declaration order through the
     *       {@link BoundaryCheckRunner} seam per {@code fieldBoundaries}
     *       entry (the pinned {@code CLASS_LITERAL_FIELD} coverage);</li>
     *   <li>the instance: provided fields present with their
     *       boundary-published values, an omitted required-present field
     *       present with the loaded default (an omitted field whose
     *       loaded default is absent or the miss sentinel is absent, the
     *       deployed {@code class_} construction's own behavior), an
     *       omitted optional field absent; the canonical class identity
     *       tags the instance.</li>
     * </ol>
     *
     * <p>A failure at any step publishes no partial instance; the class
     * factory ref is null and no {@code CLASS_DEFAULT} child runs (the
     * loaded defaults are data, never in-project default
     * expressions).</p>
     *
     * @param op              the validated {@code CLASS_NEW} op carrying
     *                        {@code CLASS_CONSTRUCTION} and
     *                        {@code HOST_DEFAULTS}; non-null
     * @param priorValues     the resolved operand values; every provided
     *                        value of the payload must resolve; non-null
     * @param boundaryOps     the unit's boundary ops by {@link OpId};
     *                        every {@code fieldBoundaries} id must resolve
     *                        to a {@code BOUNDARY} op parented to this op;
     *                        non-null
     * @param layouts         the layout-resolution context
     *                        {@code ClassId → ClassLayout}; the payload's
     *                        classId must resolve to exactly the payload's
     *                        layout; non-null
     * @param checkRunner     the boundary-check delegate; non-null
     * @param hostDefaults    the loaded {@code <C>_defaults} projection of
     *                        the payload's class (the seam's data); null
     *                        is a fail-closed producer defect
     * @return {@code Success} with the fresh tagged instance after every
     *         provided-field boundary passed, or {@code Failure} with the
     *         E8007 extra-key projection or the first failing boundary's
     *         failure
     * @throws Defect               on a shape outside the pinned contract —
     *                              a wrong op kind/policy/owner, a non-null
     *                              factory ref, a non-empty default child
     *                              list, an unresolvable value or layout, a
     *                              boundary child or entry outside the pinned
     *                              shape, an input-wiring mismatch, or a
     *                              missing defaults projection
     * @throws NullPointerException if any argument but {@code hostDefaults}
     *                              is null
     */
    public static Outcome<Value> executeClassNewHostDefaults(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<OpId, SemanticOp> boundaryOps,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner,
            Map<String, Value> hostDefaults) {
        requireOp(op, SemanticOpKind.CLASS_NEW, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(boundaryOps, "boundaryOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();

        if (payload.defaultOwner() != DefaultOwner.HOST_DEFAULTS) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner "
                + payload.defaultOwner() + ": this executor surface is the host"
                + " declaration class construction (HOST_DEFAULTS) — LOCAL is"
                + " executeClassNewLocal's, SHARED_FACTORY transfer is"
                + " executeClassNewSharedFactory's, the builtin Error construction is"
                + " executeClassNewBuiltinDefaults's, RETAINED_ABI transfer is E10's,"
                + " and the extern-C FFI_PLAN construction is executeClassNewFfiPlan's;"
                + " a foreign owner reaching executeClassNewHostDefaults is a producer"
                + " defect,"
                + " never executed");
        }
        if (payload.classFactoryRef() != null) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a non-null"
                + " classFactoryRef " + payload.classFactoryRef() + " under"
                + " HOST_DEFAULTS: the host construction carries a null factory ref"
                + " (the loaded defaults are data, never a factory transfer) — a"
                + " producer defect, never executed");
        }
        if (!payload.classDefaultOpIds().isEmpty()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries "
                + payload.classDefaultOpIds() + " under HOST_DEFAULTS: the host"
                + " construction carries an empty child list (the omitted fields'"
                + " values come from the loaded defaults entry — no in-project"
                + " default expression is evaluated) — a producer defect, never"
                + " executed");
        }
        if (hostDefaults == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " reaches the host construction without the loaded defaults"
                + " projection: the host seam supplies the module's <C>_defaults"
                + " entry — an absent projection is a producer defect, never an"
                + " invented default");
        }

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " does not resolve in the layout-resolution context: a declaration"
                + " class resolves through the project's registered declaration"
                + " layouts — an unresolvable layout is a producer defect, never"
                + " executed");
        }
        if (!layout.equals(payload.layout())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a layout that differs"
                + " from the resolution context's layout of " + payload.classId()
                + ": the payload's layout must be exactly the registered declaration"
                + " layout — a mismatch is a producer defect, never executed");
        }

        // Phase 1: provided values resolve in literal order; an undeclared
        // provided name is unreachable from the checker (E4002) and stays
        // fail closed.
        LinkedHashMap<String, Value> providedValues = new LinkedHashMap<>();
        LinkedHashMap<String, ValueId> providedValueIds = new LinkedHashMap<>();
        resolveProvidedFields(op, payload, priorValues, layout, providedValues,
            providedValueIds);

        // Phase 3: extra-key rejection first in provided-source order — the
        // loaded defaults projection is the accepted-key authority (the
        // deployed construction entry's own rule), before any field
        // validation.
        for (KindPayload.ProvidedField field : payload.providedFields()) {
            if (!hostDefaults.containsKey(field.name())) {
                BoundaryFailure failure = BoundaryFailure.fromRow(
                    FailureContractRegistry.row(FailurePolicyId.CLASS_CONSTRUCTION), 0,
                    null, null,
                    metadataOf("field", field.name(), "classId", payload.classId().text()),
                    null);
                return new Outcome.Failure<Value>(new OpFailure(failure, op.origin()));
            }
        }

        // Phase 4: exactly one CLASS_LITERAL_FIELD boundary per provided
        // field in declaration order; each runs through the delegate.
        LinkedHashMap<String, Value> checkedValues = new LinkedHashMap<>();
        OpFailure fieldFailure = applyLiteralFieldBoundaries(op, payload, layout,
            providedValues, providedValueIds, payload.fieldBoundaries(), boundaryOps,
            checkRunner, checkedValues, "host construction");
        if (fieldFailure != null) {
            return new Outcome.Failure<Value>(fieldFailure);
        }

        // Phase 5: the declaration-order field states — the provided fields
        // with their boundary-published values, an omitted required-present
        // field with the loaded default (absent when the loaded projection
        // carries no present entry, exactly like the deployed class_
        // construction), and an omitted optional field absent.
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value provided = checkedValues.get(fieldLayout.name());
            if (provided != null) {
                states.add(new FieldState.Present(provided));
                continue;
            }
            if (fieldLayout.required()) {
                Value loaded = hostDefaults.get(fieldLayout.name());
                if (loaded != null && !(loaded instanceof Value.Missing)) {
                    states.add(new FieldState.Present(loaded));
                    continue;
                }
            }
            states.add(FieldState.Missing.INSTANCE);
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    // =========================================================================
    // The extern-C C-struct construction surface (ISSUE-0667)
    // =========================================================================

    /**
     * One ordered entry of the loaded {@code <C>_plan} projection
     * ({@code luajit-ffi-struct-plan-construction-and-oracle-projection}
     * F4 and the oracle plan-projection contract; ISSUE-0667): the field
     * name, the field's canonical descriptor, the plan's optional flag,
     * and the deferred default — the plan's generated evaluator, supplied
     * by the seam as a fresh per-attempt value. An entry without a
     * deferred default carries a null supplier; an extern-C struct
     * declares every field required with a default, so a null supplier on
     * a required entry is a producer defect at the construction, never an
     * absent field.
     *
     * @param name             the field name in class source order; non-null
     * @param descriptor       the field's canonical descriptor; non-null
     * @param optional         the plan's optional flag (always false for an
     *                         extern-C struct field)
     * @param defaultEvaluator the deferred default supplier, or {@code null}
     *                         when the entry carries no evaluator
     */
    public record FfiPlanEntry(String name, RuntimeDescriptor descriptor,
                               boolean optional, Supplier<Value> defaultEvaluator) {

        public FfiPlanEntry {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }

    /**
     * The FFI-plan field-check delegate seam (struct-plan F4; ISSUE-0667):
     * one field check of the C-struct construction. A provided field's
     * phase-1 run passes the field's pinned
     * {@code CLASS_LITERAL_FIELD} boundary child payload (the delegate
     * runs the child and publishes its checked value/events); the phase-3
     * descriptor check of one present field passes a {@code null} boundary
     * (no boundary op exists for a plan-supplied field). The delegate owns
     * every descriptor projection (the descriptor-kind rule's
     * E8001/E8004/E8010 cells); the executor pins only the orchestration
     * (the provided-source guard, the plan source order, the single
     * per-attempt evaluation, and the tag only after all validation).
     */
    @FunctionalInterface
    public interface FfiPlanCheckRunner {

        /**
         * Runs one field check of the C-struct construction.
         *
         * @param boundary   the field's pinned {@code CLASS_LITERAL_FIELD}
         *                   child payload for a provided field's phase-1
         *                   boundary run, or {@code null} for the phase-3
         *                   descriptor check of one present field
         * @param descriptor the checked field's descriptor (the boundary
         *                   child's descriptor, or the plan entry's);
         *                   non-null
         * @param input      the present field value; non-null
         * @return {@code Pass} with the checked value, or {@code Fail} with
         *         the pinned registry-row projection
         */
        BoundaryResult run(KindPayload.BoundaryPayload boundary,
                           RuntimeDescriptor descriptor, Value input);
    }

    /**
     * Executes one validated {@code CLASS_NEW(FFI_PLAN)} op (ISSUE-0667;
     * {@code luajit-ffi-struct-plan-construction-and-oracle-projection} F4
     * and the oracle plan-projection contract): the extern-C C-struct
     * construction over the loaded {@code <exportName>_plan} projection —
     * the oracle-side twin of the runtime's
     * {@code __rt.class_plan_(identity, plan, provided, file, line,
     * column)} four phases.
     *
     * <ol>
     *   <li>the provided values resolve in literal order; each provided
     *       field's {@code CLASS_LITERAL_FIELD} boundary child runs in
     *       declaration order through the {@link FfiPlanCheckRunner} seam
     *       and the checked value is the provided copy;</li>
     *   <li>the extra-key guard in provided-source order — a provided name
     *       absent from the projection raises E8007 at the op (literal)
     *       origin before any default runs (the artifact's deterministic
     *       authority, kept because the runtime's phase-1 pair iteration is
     *       order-free);</li>
     *   <li>each omitted required-present entry's deferred default is
     *       invoked exactly once per attempt in class source order
     *       (optional omissions stay absent) and the supplied value is the
     *       field's value;</li>
     *   <li>every present field validates against its plan entry's
     *       descriptor in class source order through the same seam (the
     *       runtime's canonical-matcher projections, at the literal
     *       origin);</li>
     *   <li>the instance publishes as the declaration-order
     *       {@link Value.Class} with every declared field present (the
     *       extern-C struct shape is required-present throughout).</li>
     * </ol>
     *
     * <p>A failure publishes no partial instance. No generated evaluator
     * content and no native code runs here: the projection's deferred
     * defaults are the seam's values, invoked once per attempt, never
     * memoized across attempts.</p>
     *
     * @param op          the validated construction op carrying
     *                    {@code CLASS_CONSTRUCTION} and
     *                    {@code defaultOwner FFI_PLAN}; non-null
     * @param priorValues the provided-field value lookup (literal-order
     *                    prior steps); non-null
     * @param boundaryOps the unit's {@code BOUNDARY} ops by {@link OpId};
     *                    non-null
     * @param layouts     the layout-resolution context
     *                    {@code ClassId → ClassLayout} (the unit's layouts
     *                    plus the project's registered declaration
     *                    layouts); non-null
     * @param projection  the loaded plan's ordered entries as the closed
     *                    plan-projection terminal supplies them; a
     *                    {@code null} projection is a fail-closed producer
     *                    defect (never an invented empty plan)
     * @param checkRunner the field-check delegate; non-null
     * @return the declaration-order instance or the pinned projection
     * @throws Defect if the op shape, the resolved layout, the projection
     *                agreement, a boundary child, or a plan entry deviates
     *                from the pinned construction contract, or if a
     *                declared field would stay absent at publication
     * @throws NullPointerException if any argument but {@code projection}
     *                              and the op payload's legally absent
     *                              members is null
     */
    public static Outcome<Value> executeClassNewFfiPlan(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<OpId, SemanticOp> boundaryOps,
            Map<ClassId, ClassLayout> layouts,
            List<FfiPlanEntry> projection,
            FfiPlanCheckRunner checkRunner) {
        requireOp(op, SemanticOpKind.CLASS_NEW, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(boundaryOps, "boundaryOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();

        if (payload.defaultOwner() != DefaultOwner.FFI_PLAN) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner "
                + payload.defaultOwner() + ": this executor surface is the extern-C"
                + " C-struct construction (FFI_PLAN) — LOCAL is"
                + " executeClassNewLocal's, SHARED_FACTORY transfer is"
                + " executeClassNewSharedFactory's, the host declaration class"
                + " construction is executeClassNewHostDefaults's, the builtin Error"
                + " construction is executeClassNewBuiltinDefaults's, and RETAINED_ABI"
                + " transfer is E10's; a foreign owner reaching"
                + " executeClassNewFfiPlan is a producer defect, never executed");
        }
        if (payload.classFactoryRef() != null) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a non-null"
                + " classFactoryRef " + payload.classFactoryRef() + " under FFI_PLAN:"
                + " the C-struct construction carries a null factory ref (the loaded"
                + " plan is the single default authority, never a factory transfer) —"
                + " a producer defect, never executed");
        }
        if (!payload.classDefaultOpIds().isEmpty()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries "
                + payload.classDefaultOpIds() + " under FFI_PLAN: the C-struct"
                + " construction carries an empty default-op list (the omitted"
                + " fields' evaluators are the loaded plan's — no in-project default"
                + " expression is evaluated) — a producer defect, never executed");
        }
        if (projection == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " reaches the C-struct construction without the loaded plan"
                + " projection: the closed plan-projection terminal supplies the"
                + " loaded <exportName>_plan entries — an absent projection is a"
                + " fail-closed producer defect, never an invented empty plan");
        }

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout. The declaration-class layouts join the
        // resolution context through the caller's declaration-layout input.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " does not resolve in the layout-resolution context: an extern-C"
                + " C-struct class resolves through the project's registered"
                + " declaration layouts — an unresolvable layout is a producer"
                + " defect, never executed");
        }
        if (!layout.equals(payload.layout())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a layout that"
                + " differs from the resolution context's layout of "
                + payload.classId() + ": the payload's layout must be exactly the"
                + " registered C-struct layout — a mismatch is a producer defect,"
                + " never executed");
        }

        // The projection agreement (struct-plan F4): the loaded plan's
        // entries must equal the class's seed layout in order, names, and
        // descriptors — a producer defect raised before any phase runs.
        if (projection.size() != layout.fields().size()) {
            throw new Defect("CLASS_NEW " + op.opId() + " projects "
                + projection.size() + " plan entries for the seed layout of "
                + payload.classId() + " with " + layout.fields().size() + " fields:"
                + " the loaded plan's ordered entries must equal the"
                + " compiler-validated seed layout — a fail-closed producer defect,"
                + " raised before any phase");
        }
        for (int i = 0; i < projection.size(); i++) {
            FfiPlanEntry entry = projection.get(i);
            ClassLayout.FieldLayout field = layout.fields().get(i);
            if (!entry.name().equals(field.name())
                    || !entry.descriptor().equals(field.descriptor())) {
                throw new Defect("CLASS_NEW " + op.opId() + " plan entry " + i
                    + " ('" + entry.name() + "': "
                    + entry.descriptor().canonicalSpecText() + ") differs from the"
                    + " seed layout's field '" + field.name() + "': "
                    + field.descriptor().canonicalSpecText() + " — the loaded plan's"
                    + " order, names, and descriptors must equal the class's seed"
                    + " layout (a fail-closed producer defect, raised before any"
                    + " phase)");
            }
        }

        // Phase 1: the provided values resolve in literal order (they
        // completed before the op) and each provided field's
        // CLASS_LITERAL_FIELD boundary child runs in declaration order; the
        // checked value is the construction's provided copy.
        LinkedHashMap<String, Value> providedValues = new LinkedHashMap<>();
        LinkedHashMap<String, ValueId> providedValueIds = new LinkedHashMap<>();
        resolveProvidedFields(op, payload, priorValues, null, providedValues,
            providedValueIds);
        LinkedHashMap<String, Value> checkedValues = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
            Value provided = providedValues.get(entry.field());
            ValueId providedId = providedValueIds.get(entry.field());
            if (entry.kind() != BoundaryKind.CLASS_LITERAL_FIELD || provided == null
                    || providedId == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " carries boundary entry"
                    + " for field '" + entry.field() + "' of kind " + entry.kind()
                    + ": the C-struct construction carries exactly one"
                    + " CLASS_LITERAL_FIELD boundary per provided field and no"
                    + " CLASS_DEFAULT_FIELD — a shape deviation is a producer defect,"
                    + " never executed");
            }
            ClassLayout.FieldLayout fieldLayout = fieldOf(layout, entry.field());
            if (fieldLayout == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " field-boundary entry"
                    + " names field '" + entry.field() + "' which is not a declared"
                    + " field of " + payload.classId() + " — a producer defect, never"
                    + " executed");
            }
            SemanticOp child = requireBoundaryChild(boundaryOps, entry.boundaryOpId(), op,
                entry.kind());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) child.payload();
            if (!boundaryPayload.descriptor().equals(fieldLayout.descriptor())) {
                throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                    + child.opId() + " carries descriptor "
                    + boundaryPayload.descriptor().canonicalSpecText() + ": the pinned"
                    + " child descriptor is the field's declared descriptor "
                    + fieldLayout.descriptor().canonicalSpecText() + " — a mismatch"
                    + " is a producer defect, never executed");
            }
            requireDescriptorKindPolicy(child, boundaryPayload.descriptor());
            if (!boundaryPayload.input().equals(providedId)) {
                throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                    + child.opId() + " carries input " + boundaryPayload.input()
                    + ": the pinned CLASS_LITERAL_FIELD input is the field's provided"
                    + " value op " + providedId + " (K-D4 input wiring) — a mismatch"
                    + " is a producer defect, never executed");
            }
            BoundaryResult result = checkRunner.run(boundaryPayload,
                boundaryPayload.descriptor(), provided);
            if (result instanceof BoundaryResult.Fail fail) {
                return new Outcome.Failure<Value>(new OpFailure(fail.failure(),
                    op.origin()));
            }
            checkedValues.put(entry.field(), ((BoundaryResult.Pass) result).value());
        }

        // Phase 1b: the extra-key guard in provided-source order — a
        // provided name absent from the projection raises E8007 at the
        // literal origin before any default runs (the artifact's
        // deterministic authority; the runtime entry's phase-1 pairs()
        // iteration is order-free).
        Outcome.Failure<Value> extraKeyFailure =
            undeclaredProvidedFieldFailure(op, payload, layout);
        if (extraKeyFailure != null) {
            return extraKeyFailure;
        }
        // After the guard admits every provided name: every provided field
        // carries exactly one boundary child (a declared provided field
        // without one is a producer defect).
        if (payload.fieldBoundaries().size() != payload.providedFields().size()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries "
                + payload.fieldBoundaries().size() + " field-boundary entries for "
                + payload.providedFields().size() + " provided fields: the C-struct"
                + " construction carries exactly one CLASS_LITERAL_FIELD boundary per"
                + " provided field — a child-count mismatch is a producer defect,"
                + " never executed");
        }

        // Phase 2: omitted required-present defaults invoke their deferred
        // evaluator exactly once per attempt in class source order; optional
        // omissions stay absent.
        LinkedHashMap<String, Value> slots = new LinkedHashMap<>(checkedValues);
        for (FfiPlanEntry entry : projection) {
            if (slots.containsKey(entry.name()) || entry.optional()) {
                continue;
            }
            if (entry.defaultEvaluator() == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " plan entry '"
                    + entry.name() + "' is required-present without a deferred"
                    + " default: an extern-C struct field is declared required with a"
                    + " default (the loaded plan's evaluator is the only default"
                    + " authority) — a supplier-less required entry is a producer"
                    + " defect, never an absent field");
            }
            Value supplied = entry.defaultEvaluator().get();
            if (supplied == null || supplied instanceof Value.Missing) {
                throw new Defect("CLASS_NEW " + op.opId() + " plan entry '"
                    + entry.name() + "' deferred default produced the absent value:"
                    + " a required-present extern-C struct field's evaluator returns"
                    + " a present value — a producer defect, never an absent field");
            }
            slots.put(entry.name(), supplied);
        }

        // Phase 3: every present field validates against its plan entry's
        // descriptor in class source order (the same E8001/E8004/E8010
        // projections, at the literal origin). A provided field's phase-1
        // boundary child already ran; the entry-descriptor check re-runs
        // event-free — the runtime's canonical matcher validates every
        // present field.
        for (FfiPlanEntry entry : projection) {
            Value present = slots.get(entry.name());
            if (present == null) {
                continue;
            }
            BoundaryResult result = checkRunner.run(null, entry.descriptor(), present);
            if (result instanceof BoundaryResult.Fail fail) {
                return new Outcome.Failure<Value>(new OpFailure(fail.failure(),
                    op.origin()));
            }
            slots.put(entry.name(), ((BoundaryResult.Pass) result).value());
        }

        // Phase 4: the declaration-order field states; every declared field
        // of the C-struct is present (the seed layout's required-present
        // rule).
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value present = slots.get(fieldLayout.name());
            if (present == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " publishes an absent"
                    + " field '" + fieldLayout.name() + "' of " + payload.classId()
                    + ": every declared extern-C C-struct field is required-present"
                    + " (the seed layout) — an absent field at publication is a"
                    + " producer defect, never a partial instance");
            }
            states.add(new FieldState.Present(present));
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    /**
     * Executes one validated {@code CLASS_FACTORY} op (K-D5): the
     * declaring module's default-application op, one per exported class,
     * triggered by a caller's {@code CLASS_NEW} with
     * {@code defaultOwner: SHARED_FACTORY} or by a
     * {@code JSON_FROM_CLASS} nested-class decode (K-D8 step 6, K-D5
     * trigger (b) — the JSON child's trigger of the same closed
     * trigger set). The factory runs
     * its {@code CLASS_DEFAULT} children in declaration order through
     * the {@link BodyRunner} seam — defaults evaluate per construction
     * in the declaring module's scope (the owner-side body runner
     * executes the owner unit's detached default blocks; mutable default
     * arrays/tables/nested classes allocate freshly per execution by
     * block re-execution) — skipping any child whose field the
     * triggering context records as provided (the caller's static
     * {@code providedFields}); fills an internal default-filled instance
     * (the untagged transfer — never published by the factory, never
     * passed through any boundary) and returns it as its result. The
     * factory runs zero boundaries and zero return boundaries; its
     * failure policy is {@code CLASS_CONSTRUCTION}; a failing default
     * child fails the triggering caller's op (the body runner's throw
     * propagates out of the caller's transfer — no caller instance is
     * published and the completed children's effects remain). The
     * executed {@code parentOpId} the trace records is the triggering
     * caller op's id (K-D12, cross-unit): {@code triggeringCaller} is
     * the caller op this execution parents to, and the factory never
     * constructs directly and never checks a return.
     *
     * <p>The factory's children are the detached structural
     * {@code CLASS_DEFAULT} ops named by the payload's
     * {@code classDefaultOpIds} (K-D12: the payload membership records
     * their nesting, not a static {@code parentOpId}); each is
     * shape-checked fail closed before its block runs (kind, policy,
     * classId coherence, a declared required-present field, no
     * duplicates). The payload's {@code callerOpRef} is the
     * deterministic pre-allocated execution-wiring slot (K-D2): the
     * executed parent is the triggering caller op this API pins, and a
     * non-{@code CLASS_NEW} caller reaching this child's surface is a
     * producer defect.</p>
     *
     * @param op              the validated owner-side {@code CLASS_FACTORY}
     *                        op carrying {@code CLASS_CONSTRUCTION};
     *                        non-null
     * @param triggeringCaller the triggering caller {@code CLASS_NEW} op
     *                        whose id is the factory's executed
     *                        {@code parentOpId} (cross-unit); non-null,
     *                        never the factory op itself
     * @param defaultOps      the owner unit's {@code CLASS_DEFAULT} ops
     *                        by {@link OpId}; every id of
     *                        {@code classDefaultOpIds} must resolve to a
     *                        {@code CLASS_DEFAULT} op of this classId
     *                        carrying {@code NO_DEAL_FAILURE}; non-null
     * @param layouts         the layout-resolution context
     *                        {@code ClassId → ClassLayout} (the owner's
     *                        {@code classLayouts} plus the project
     *                        interface facts); the payload's classId must
     *                        resolve; non-null
     * @param providedFields  the triggering context's provided-field name
     *                        set (a {@code CLASS_NEW}'s static
     *                        {@code providedFields} names) — every child
     *                        whose field is provided is skipped (a
     *                        provided field's default never runs); non-null
     * @param bodyRunner      the owner-side default-block callback
     *                        (defaults evaluate in the declaring module's
     *                        scope); non-null
     * @return {@code Success} with the internal default-filled transfer
     *         instance (untagged — declaration-order states, defaulted
     *         fields present, every other field missing)
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy, a
     *                              trigger outside the closed trigger set
     *                              ({@code CLASS_NEW} or
     *                              {@code JSON_FROM_CLASS}), a
     *                              self-trigger, an unresolvable layout, a
     *                              default child of the wrong
     *                              kind/policy/class, a defaulted field
     *                              outside the layout or optional, or a
     *                              duplicate default child
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeClassFactory(
            SemanticOp op,
            SemanticOp triggeringCaller,
            Map<OpId, SemanticOp> defaultOps,
            Map<ClassId, ClassLayout> layouts,
            Set<String> providedFields,
            BodyRunner bodyRunner) {
        requireOp(op, SemanticOpKind.CLASS_FACTORY, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(triggeringCaller, "triggeringCaller must not be null");
        Objects.requireNonNull(defaultOps, "defaultOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(providedFields, "providedFields must not be null");
        Objects.requireNonNull(bodyRunner, "bodyRunner must not be null");
        // The executed parentOpId pin (K-D5/K-D12): the factory's events
        // parent to the triggering caller op — a caller CLASS_NEW for this
        // child's surface (the JSON_FROM_CLASS nested-decode trigger is
        // the later JSON child's). The factory never parents to itself.
        if (triggeringCaller.kind() != SemanticOpKind.CLASS_NEW
                && triggeringCaller.kind() != SemanticOpKind.JSON_FROM_CLASS) {
            throw new Defect("CLASS_FACTORY " + op.opId() + " triggered by an op of kind "
                + triggeringCaller.kind() + ": the closed trigger set is {CLASS_NEW (the "
                + "SHARED_FACTORY construction trigger), JSON_FROM_CLASS (the "
                + "nested-class decode trigger, K-D8 step 6/K-D5 trigger (b))} and the "
                + "factory's executed parentOpId is the triggering caller op's id "
                + "(K-D5/K-D12) — an op outside the closed trigger set reaching "
                + "execution is a producer defect, never executed");
        }
        if (triggeringCaller.opId().equals(op.opId())) {
            throw new Defect("CLASS_FACTORY " + op.opId() + " triggered by itself: the "
                + "factory is the declaring module's default-application op and its "
                + "executed parentOpId is the triggering caller op (cross-unit) — a "
                + "factory as its own caller is a producer defect, never executed");
        }
        KindPayload.ClassFactoryPayload payload =
            (KindPayload.ClassFactoryPayload) op.payload();

        // Layout resolution (K-D11): the factory fills the declared
        // layout of its own classId, never a foreign layout.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null) {
            throw new Defect("CLASS_FACTORY " + op.opId() + " classId " + payload.classId()
                + " does not resolve in the layout-resolution context: the factory fills "
                + "its class's declared layout (the owner unit's classLayouts) — an "
                + "unresolvable layout is a producer defect, never executed");
        }

        // Declaration-order default application (K-D5): the CLASS_DEFAULT
        // children in declaration order, skipping any child whose field
        // the triggering context records as provided (a provided field's
        // default never runs); defaults evaluate per construction in the
        // declaring module's scope through the owner-side body runner.
        LinkedHashMap<String, Value> filled = new LinkedHashMap<>();
        applyClassDefaults(op, payload.classId(), payload.classDefaultOpIds(), defaultOps,
            layout, providedFields,
            "the factory payload lists required-present defaulted fields only (an"
                + " optional-with-default field's default never runs and its op id never"
                + " enters the payload) — a listed optional default is a producer defect,"
                + " never executed",
            bodyRunner, filled);

        // The internal default-filled transfer instance (K-D5, untagged):
        // declaration-order states — the defaulted fields present, every
        // other field missing. The factory never publishes this instance:
        // the caller's CLASS_NEW overlays provided fields, validates, and
        // tags its own fresh published instance.
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value value = filled.get(fieldLayout.name());
            states.add(value == null ? FieldState.Missing.INSTANCE
                : new FieldState.Present(value));
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    // =========================================================================
    // CLASS_NEW(SHARED_FACTORY)
    // =========================================================================

    /**
     * Executes one validated {@code CLASS_NEW} op with
     * {@code defaultOwner: SHARED_FACTORY} in the closed K-D4/D16 order
     * with the K-D5 cross-unit transfer:
     *
     * <ol>
     *   <li>provided values resolve from the lookup in literal order in
     *       the caller before the transfer (the
     *       {@code jvm-xmod-class-construction-eval-order} pin — the
     *       provided-field evaluation crosses the module boundary in
     *       literal order);</li>
     *   <li>default application transfers to the owner unit's
     *       {@code CLASS_FACTORY} op — resolved by the payload's
     *       {@code classFactoryRef} {@link ClassFactoryId} through the
     *       caller-supplied {@link ClassFactoryRegistry} (K-D5) — which
     *       fills the omitted required-present fields' defaults in the
     *       declaring module's scope (skipping provided fields) and
     *       returns the default-filled transfer instance;</li>
     *   <li>extra-key rejection first in provided-source order: the
     *       first provided name not in the layout fails
     *       {@code CLASS_CONSTRUCTION} — E8007
     *       {@code extra field '{field}' in class '{classId}'} at the op
     *       origin — after the transfer (the default side effects have
     *       completed) and before any provided-field application or
     *       field validation;</li>
     *   <li>provided-field application in declaration order: the overlay
     *       of the provided values onto the transferred instance (the
     *       {@code jvm-xmod-class-construction-defaults} reorder pin);</li>
     *   <li>field validation in declaration order through the
     *       {@link BoundaryCheckRunner} seam per {@code fieldBoundaries}
     *       entry — {@code CLASS_LITERAL_FIELD} for provided fields with
     *       input = the field's provided value; {@code CLASS_DEFAULT_FIELD}
     *       for omitted required-present defaulted fields with the pinned
     *       input wiring = the owner {@code CLASS_FACTORY} op's result
     *       {@link ValueId} (the K-D4 cross-unit D4-global reference) and
     *       the extraction rule — the executor reads the named field
     *       from the transferred instance before running the boundary
     *       (the checked value is the transferred instance's field);</li>
     *   <li>the fresh caller-side instance is tagged with {@code classId}
     *       ({@code class:<ClassId>} canonical identity) and SUCCESS
     *       publishes it — a fresh instance record distinct from the
     *       internal transfer instance.</li>
     * </ol>
     *
     * A failure at any step publishes no partial instance (the
     * {@link Value.Class} exists only on the success path, so the tag
     * never runs); completed children's effects remain. A failing
     * default child propagates as the owner body runner's own throw —
     * the triggering caller's op fails and no caller instance exists.
     * {@code CLASS_NEW} runs zero return boundaries — the executor never
     * drives a {@code FUNCTION_RETURN} child.
     *
     * @param op              the validated caller-side {@code CLASS_NEW}
     *                        op carrying {@code CLASS_CONSTRUCTION} with
     *                        {@code defaultOwner: SHARED_FACTORY},
     *                        non-null {@code classFactoryRef}, and empty
     *                        {@code classDefaultOpIds}; non-null
     * @param priorValues     the resolved provided-field prior-step values
     *                        (the caller's); non-null, no null entries
     * @param factories       the owner's {@link ClassFactoryRegistry} —
     *                        the {@code classFactoryRef} must resolve to
     *                        the owner {@code CLASS_FACTORY} op id
     *                        (K-D5); non-null
     * @param ownerOps        the owner unit's ops by {@link OpId} (the
     *                        factory op, its result, and the owner's
     *                        {@code CLASS_DEFAULT} ops); non-null
     * @param boundaryOps     the caller unit's boundary ops by
     *                        {@link OpId}; every {@code fieldBoundaries}
     *                        id must resolve to a {@code BOUNDARY} op
     *                        parented to this op; non-null
     * @param layouts         the layout-resolution context
     *                        {@code ClassId → ClassLayout} (the caller's
     *                        {@code classLayouts} plus the owner unit's);
     *                        the payload's classId must resolve to exactly
     *                        the payload's layout; non-null
     * @param checkRunner     the boundary-check delegate; non-null
     * @param ownerBodyRunner the owner-side default-block callback
     *                        (defaults evaluate in the declaring module's
     *                        scope); non-null
     * @return {@code Success} with the fresh tagged caller-side instance
     *         after every field boundary passed, or {@code Failure} with
     *         the E8007 extra-key projection or the first failing
     *         boundary's failure
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy, a
     *                              non-{@code SHARED_FACTORY} owner, a
     *                              null factory ref or non-empty
     *                              {@code classDefaultOpIds}, a layout
     *                              resolution failure, an unresolvable
     *                              factory binding or factory op, a
     *                              factory of the wrong kind/policy/class,
     *                              a non-{@link ValueId} factory result,
     *                              a provided value that does not resolve
     *                              or resolves to {@code Missing}, a
     *                              boundary child or field-boundary entry
     *                              outside the pinned shape, an
     *                              input-wiring mismatch (including the
     *                              {@code CLASS_DEFAULT_FIELD} input not
     *                              naming the factory result), or a
     *                              transferred instance missing a field
     *                              the boundary list names
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeClassNewSharedFactory(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            ClassFactoryRegistry factories,
            Map<OpId, SemanticOp> ownerOps,
            Map<OpId, SemanticOp> boundaryOps,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner,
            BodyRunner ownerBodyRunner) {
        requireOp(op, SemanticOpKind.CLASS_NEW, FailurePolicyId.CLASS_CONSTRUCTION);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(factories, "factories must not be null");
        Objects.requireNonNull(ownerOps, "ownerOps must not be null");
        Objects.requireNonNull(boundaryOps, "boundaryOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        Objects.requireNonNull(ownerBodyRunner, "ownerBodyRunner must not be null");
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();

        // This child's surface: SHARED_FACTORY execution. LOCAL execution
        // is {@link #executeClassNewLocal}'s; the host declaration class
        // construction is {@link #executeClassNewHostDefaults}'s; the
        // builtin Error construction is
        // {@link #executeClassNewBuiltinDefaults}'s; RETAINED_ABI is E10's
        // and the extern-C FFI_PLAN construction is
        // {@link #executeClassNewFfiPlan}'s — a
        // non-SHARED_FACTORY owner reaching this surface is a producer
        // defect, never silently executed as a transfer.
        if (payload.defaultOwner() != DefaultOwner.SHARED_FACTORY) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries defaultOwner "
                + payload.defaultOwner() + ": this child's executor surface is "
                + "SHARED_FACTORY transfer (executeClassNewLocal is the LOCAL surface, "
                + "executeClassNewHostDefaults is the host declaration class surface, "
                + "executeClassNewBuiltinDefaults is the builtin Error surface, "
                + "RETAINED_ABI transfer is E10's, and the extern-C FFI_PLAN"
                + " construction is executeClassNewFfiPlan's) — a"
                + " non-SHARED_FACTORY owner reaching "
                + "executeClassNewSharedFactory is a producer defect, never executed");
        }
        if (payload.classFactoryRef() == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a null classFactoryRef: "
                + "the pinned SHARED_FACTORY shape carries classFactoryRef = the "
                + "interface's pre-allocated constructionEntry — a null factory ref is a "
                + "producer defect, never executed");
        }
        if (!payload.classDefaultOpIds().isEmpty()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries " + payload.classDefaultOpIds()
                + ": the pinned SHARED_FACTORY shape carries classDefaultOpIds empty (the "
                + "owner's CLASS_FACTORY carries the CLASS_DEFAULT child list) — a "
                + "non-empty list is a producer defect, never executed");
        }

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.classId());
        if (layout == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classId " + payload.classId()
                + " does not resolve in the layout-resolution context: every "
                + "payload-referenced class resolves through the unit's classLayouts "
                + "(plus the project interface index) — an unresolvable layout is a "
                + "producer defect, never executed");
        }
        if (!layout.equals(payload.layout())) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries a layout that differs "
                + "from the resolution context's layout of " + payload.classId()
                + ": the payload's layout must be exactly the resolved layout — a "
                + "mismatch is a producer defect, never executed");
        }

        // K-D4 step 1: provided values resolve in literal order in the
        // caller before the transfer (the eval-order pin).
        LinkedHashMap<String, Value> providedValues = new LinkedHashMap<>();
        LinkedHashMap<String, ValueId> providedValueIds = new LinkedHashMap<>();
        resolveProvidedFields(op, payload, priorValues, null, providedValues,
            providedValueIds);

        // The factory resolution by ClassFactoryId (K-D5): the payload's
        // classFactoryRef names the owner's CLASS_FACTORY op through the
        // registry — a missing binding means an owner not on the shared
        // route (its construction defers at lowering, RETAINED_ABI is
        // E10's) and is never executed here.
        OpId factoryOpId = factories.factoryFor(payload.classFactoryRef());
        if (factoryOpId == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " classFactoryRef "
                + payload.classFactoryRef() + " does not resolve in the owner's "
                + "ClassFactoryRegistry: a SHARED_FACTORY op reaching execution without "
                + "a registered factory is a producer defect (an owner on a retained "
                + "route defers at lowering — RETAINED_ABI is E10's), never executed");
        }
        SemanticOp factoryOp = ownerOps.get(factoryOpId);
        if (factoryOp == null) {
            throw new Defect("CLASS_NEW " + op.opId() + " factory op id " + factoryOpId
                + " does not resolve in the owner unit's op lookup: the registry binding "
                + "names the owner unit's CLASS_FACTORY op — an unresolvable factory op "
                + "is a producer defect, never executed");
        }
        requireOp(factoryOp, SemanticOpKind.CLASS_FACTORY,
            FailurePolicyId.CLASS_CONSTRUCTION);
        KindPayload.ClassFactoryPayload factoryPayload =
            (KindPayload.ClassFactoryPayload) factoryOp.payload();
        if (!factoryPayload.classId().equals(payload.classId())) {
            throw new Defect("CLASS_NEW " + op.opId() + " resolves factory op "
                + factoryOp.opId() + " of class " + factoryPayload.classId()
                + ": the pinned factory fills the constructed class's defaults ("
                + payload.classId() + ") — a classId mismatch is a producer defect, "
                + "never executed");
        }
        if (!(factoryOp.result() instanceof ValueId factoryResult)) {
            throw new Defect("CLASS_NEW " + op.opId() + " factory op " + factoryOp.opId()
                + " publishes a non-ValueId result " + factoryOp.result()
                + ": the pinned CLASS_DEFAULT_FIELD input is the CLASS_FACTORY op's "
                + "result ValueId (K-D4 input wiring) — a producer defect, never "
                + "executed");
        }

        // The owner-side CLASS_DEFAULT lookup (defaults evaluate in the
        // declaring module's scope through the owner's ops).
        Map<OpId, SemanticOp> ownerDefaultOps = new LinkedHashMap<>();
        for (Map.Entry<OpId, SemanticOp> entry : ownerOps.entrySet()) {
            if (entry.getValue().kind() == SemanticOpKind.CLASS_DEFAULT) {
                ownerDefaultOps.put(entry.getKey(), entry.getValue());
            }
        }

        // K-D4 step 2: the transfer to the owner's CLASS_FACTORY — the
        // factory skips the caller's provided fields and returns the
        // default-filled transfer instance (untagged). A failing default
        // child propagates as the owner body runner's throw (the caller's
        // op fails; no instance published; completed effects remain).
        Set<String> providedNames = new LinkedHashSet<>(providedValues.keySet());
        Outcome<Value> transferred = executeClassFactory(factoryOp, op, ownerDefaultOps,
            layouts, providedNames, ownerBodyRunner);
        if (!(transferred instanceof Outcome.Success<Value> transferSuccess
                && transferSuccess.value() instanceof Value.Class transferredInstance)) {
            throw new Defect("CLASS_NEW " + op.opId() + " factory transfer produced "
                + transferred + ": the pinned factory returns exactly its internal "
                + "default-filled transfer instance — a wrong outcome is a producer "
                + "defect, never executed");
        }
        if (!transferredInstance.classId().equals(payload.classId())
                || transferredInstance.fields().size() != layout.fields().size()) {
            throw new Defect("CLASS_NEW " + op.opId() + " factory transfer produced an "
                + "instance of " + transferredInstance.classId() + " with "
                + transferredInstance.fields().size() + " field states: the pinned "
                + "transfer carries the constructed class's declaration-order states ("
                + payload.classId() + ", " + layout.fields().size() + " fields) — a "
                + "mismatch is a producer defect, never executed");
        }

        // K-D4 step 3: extra-key rejection first in provided-source order —
        // after the transfer, before any provided-field application or
        // field validation (the completed default effects are observable).
        Outcome.Failure<Value> extraKeyFailure =
            undeclaredProvidedFieldFailure(op, payload, layout);
        if (extraKeyFailure != null) {
            return extraKeyFailure;
        }

        // The pinned field-boundary coverage (K-D4 step 5 shape): exactly
        // one entry per provided field (CLASS_LITERAL_FIELD) and per
        // defaulted field (CLASS_DEFAULT_FIELD) in declaration order;
        // omitted optional fields get no boundary and stay missing.
        List<KindPayload.FieldBoundary> boundaries = payload.fieldBoundaries();
        requireBoundaryShape(op, payload, layout, providedValues, boundaries,
            name -> defaultValueOf(transferredInstance, layout, name) != null);

        // K-D4 step 4: provided-field application in declaration order (the
        // overlay onto the transferred instance; duplicate names keep the
        // last provided value).
        LinkedHashMap<String, Value> instanceFields = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value provided = providedValues.get(fieldLayout.name());
            Value defaultValue = defaultValueOf(transferredInstance, layout, fieldLayout.name());
            if (provided != null) {
                instanceFields.put(fieldLayout.name(), provided);
            } else if (defaultValue != null) {
                instanceFields.put(fieldLayout.name(), defaultValue);
            }
        }

        // K-D4 step 5: field validation in declaration order through the
        // BoundaryCheckRunner seam; the first failing child fails the op
        // and no instance is published.
        LinkedHashMap<String, Value> checkedValues = new LinkedHashMap<>();
        OpFailure fieldFailure = applyFieldBoundaries(op, payload, layout, boundaries,
            providedValues, providedValueIds, boundaryOps, checkRunner, checkedValues,
            (child, entry, boundaryPayload) -> {
                // The K-D4 extraction rule: the boundary's input naming
                // the owner CLASS_FACTORY op's result ValueId is the
                // wiring (the cross-unit D4-global reference); the checked
                // value is the transferred instance's named field — the
                // factory fills exactly the defaulted fields this list
                // names, so the field must be present.
                if (!boundaryPayload.input().equals(factoryResult)) {
                    throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                        + child.opId() + " carries input " + boundaryPayload.input()
                        + ": the pinned CLASS_DEFAULT_FIELD input of a SHARED_FACTORY "
                        + "CLASS_NEW is the owner CLASS_FACTORY op's result ValueId "
                        + factoryResult + " (K-D4 input wiring, the cross-unit D4-global "
                        + "reference) — a mismatch is a producer defect, never executed");
                }
                Value extracted = defaultValueOf(transferredInstance, layout, entry.field());
                if (extracted == null) {
                    throw new Defect("CLASS_NEW " + op.opId() + " carries a "
                        + "CLASS_DEFAULT_FIELD boundary for field '" + entry.field()
                        + "' whose transferred instance field is missing: the factory "
                        + "fills exactly the omitted required-present defaulted fields "
                        + "the boundary list names (the extraction rule reads the "
                        + "transferred instance's named field) — a missing field is a "
                        + "producer defect, never executed");
                }
                return extracted;
            });
        if (fieldFailure != null) {
            return new Outcome.Failure<Value>(fieldFailure);
        }
        instanceFields.putAll(checkedValues);

        // K-D4 step 6: tag the fresh caller-side instance with classId and
        // SUCCESS publishes it — a fresh instance record distinct from the
        // internal transfer instance (declaration-order field states;
        // omitted optionals stay missing; present null stays present
        // null).
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value value = instanceFields.get(fieldLayout.name());
            states.add(value == null ? FieldState.Missing.INSTANCE
                : new FieldState.Present(value));
        }
        return new Outcome.Success<Value>(
            new Value.Class(payload.classId(), List.copyOf(states)));
    }

    /**
     * The present value of the named declaration-order field of one class
     * instance, or {@code null} when the field is missing (never a
     * conflated state — present null is the explicit {@link Value.Null}
     * variant and returns non-null). The instance's states parallel its
     * layout's declaration order (checked fail closed by the callers).
     */
    private static Value defaultValueOf(Value.Class instance, ClassLayout layout,
                                        String fieldName) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(fieldName)) {
                FieldState state = instance.fields().get(i);
                return state instanceof FieldState.Present present ? present.value() : null;
            }
        }
        return null;
    }

    // =========================================================================
    // FIELD_READ
    // =========================================================================

    /**
     * Executes one validated {@code FIELD_READ} op (K-D6): the nominal
     * receiver boundary runs first — the {@code UNTYPED_CLASS_INPUT}
     * child with descriptor {@code class:<ClassId>} and input = the
     * payload's resolved receiver (a null receiver fails E8001
     * {@code expected {@module/C}, got null} and a wrong identity fails
     * with actual {@code class:<other>} — the canonical descriptor-kind
     * projections of the child's own delegate); then the presence-aware
     * read: a missing field pre-maps to language null before the
     * {@code OPTIONAL_FIELD_READ} boundary (present null passes a
     * nullable descriptor; a missing value against a non-nullable
     * descriptor — a required field of a defective instance — fails
     * E8001 {@code expected {T}, got null}); SUCCESS publishes the
     * boundary-checked value. The receiver resolves from the value
     * lookup exactly once (never re-evaluated) and the key is the
     * static payload field name (never evaluated).
     *
     * <p>The children are supplied as explicit ops (the payload records
     * no boundary ids — the K-D12 parentage pin is the owner relation)
     * and are shape-checked fail closed before each run: the pinned
     * kind, {@code parentOpId} = the {@code FIELD_READ} op, a
     * {@code RuntimeValidation} realization, the pinned descriptor
     * ({@code class:<ClassId>} for the receiver boundary; the read's
     * checked result descriptor for the field boundary — the field's
     * declared descriptor, nullable-wrapped for an optional non-nullable
     * field, the checker's optional-read wrap), the pinned input
     * (the payload's {@code classValue} / the op's own result
     * {@code ValueId}), and the descriptor-kind policy.</p>
     *
     * @param op               the validated {@code FIELD_READ} op
     *                         carrying {@code NO_DEAL_FAILURE}; non-null
     * @param priorValues      the resolved prior-step values (the
     *                         receiver); non-null, no null entries
     * @param receiverBoundary the op's first child — the
     *                         {@code UNTYPED_CLASS_INPUT} boundary;
     *                         non-null
     * @param fieldBoundary    the op's second child — the
     *                         {@code OPTIONAL_FIELD_READ} boundary;
     *                         non-null
     * @param layouts          the layout-resolution context
     *                         {@code ClassId → ClassLayout}; the
     *                         payload's classId must resolve; non-null
     * @param checkRunner      the boundary-check delegate; non-null
     * @return {@code Success} with the boundary-checked field value, or
     *         {@code Failure} with the first failing boundary's failure
     *         at the op origin
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy, a
     *                              non-{@code ValueId} result, a child of
     *                              the wrong kind/parentage/realization/
     *                              descriptor/policy/input, an
     *                              unresolvable or mismatched layout, a
     *                              field not declared in the layout, an
     *                              instance of the wrong class or field
     *                              count, or a receiver the pinned
     *                              receiver boundary could not pass
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeFieldRead(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            SemanticOp receiverBoundary,
            SemanticOp fieldBoundary,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner) {
        requireOp(op, SemanticOpKind.FIELD_READ, FailurePolicyId.NO_DEAL_FAILURE);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(receiverBoundary, "receiverBoundary must not be null");
        Objects.requireNonNull(fieldBoundary, "fieldBoundary must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.FieldReadPayload payload = (KindPayload.FieldReadPayload) op.payload();

        // The receiver resolves exactly once (never re-evaluated).
        Value receiver = resolve(priorValues, payload.classValue());

        // The nominal receiver boundary first (K-D6): the pinned child
        // shape, then the delegate run with the resolved receiver.
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(payload.classId());
        requireFieldBoundaryChild(receiverBoundary, op, BoundaryKind.UNTYPED_CLASS_INPUT,
            classDescriptor, payload.classValue());
        BoundaryResult receiverResult =
            runReceiverBoundary(op, receiverBoundary, receiver, checkRunner);
        if (receiverResult instanceof BoundaryResult.Fail fail) {
            return new Outcome.Failure<Value>(new OpFailure(fail.failure(), op.origin()));
        }

        // After the receiver boundary passes, the receiver is the pinned
        // class instance (the production delegate can only pass an
        // instance of class:<ClassId>; a pass-through fixture passing
        // anything else is a producer defect).
        Value receiverValue = ((BoundaryResult.Pass) receiverResult).value();
        ClassLayout layout = requireInstance(op, payload.classId(), receiverValue, layouts);

        // The presence-aware read: Present(value) reads the value;
        // Missing pre-maps to language null before the field boundary
        // (K-D6) — present null stays present null, missing stays
        // distinguishable through the pre-map.
        int fieldIndex = fieldIndexOf(op, layout, payload.field());
        FieldState state = ((Value.Class) receiverValue).fields().get(fieldIndex);
        Value readValue;
        if (state instanceof FieldState.Present present) {
            readValue = present.value();
        } else {
            readValue = Value.Null.INSTANCE;
        }

        // The field boundary's pinned result descriptor (the checker's
        // optional-read wrap: the field's declared descriptor,
        // nullable-wrapped for an optional non-nullable field).
        ClassLayout.FieldLayout fieldLayout = layout.fields().get(fieldIndex);
        RuntimeDescriptor resultDescriptor = readResultDescriptorOf(fieldLayout);
        if (!(op.result() instanceof ValueId readResult)) {
            throw new Defect("FIELD_READ " + op.opId() + " publishes a non-ValueId result "
                + op.result() + ": the pinned OPTIONAL_FIELD_READ input is the op's own "
                + "result ValueId — a producer defect, never executed");
        }
        requireFieldBoundaryChild(fieldBoundary, op, BoundaryKind.OPTIONAL_FIELD_READ,
            resultDescriptor, readResult);
        BoundaryResult fieldResult = checkRunner.run(
            (KindPayload.BoundaryPayload) fieldBoundary.payload(), readValue);
        return switch (fieldResult) {
            case BoundaryResult.Pass pass -> new Outcome.Success<Value>(pass.value());
            case BoundaryResult.Fail fail -> new Outcome.Failure<Value>(
                new OpFailure(fail.failure(), op.origin()));
        };
    }

    // =========================================================================
    // FIELD_WRITE
    // =========================================================================

    /**
     * Executes one validated {@code FIELD_WRITE} commit op (K-D6): the
     * nominal receiver boundary runs first (the
     * {@code UNTYPED_CLASS_INPUT} child with descriptor
     * {@code class:<ClassId>} and input = the payload's resolved
     * receiver), then the field boundary (the
     * {@code CLASS_FIELD_ASSIGNMENT} child with the field's declared
     * descriptor and input = the payload's resolved stored value), and
     * the store commits immediately before SUCCESS — the published
     * instance carries the boundary-published value in the named field
     * with every other field state unchanged (a fresh updated instance;
     * the caller rebinds the receiver's reference to it). A failed
     * boundary commits nothing: the outcome is {@code Failure} and no
     * updated instance exists. The receiver and the stored value each
     * resolve from the value lookup exactly once (never re-evaluated);
     * the key is the static payload field name (never evaluated).
     *
     * <p>The children are supplied as explicit ops and are shape-checked
     * fail closed before each run exactly like {@link #executeFieldRead}'s
     * (pinned kind, {@code parentOpId} = the {@code FIELD_WRITE} op, a
     * {@code RuntimeValidation} realization, the pinned descriptor and
     * input, the descriptor-kind policy).</p>
     *
     * @param op               the validated {@code FIELD_WRITE} op
     *                         carrying {@code NO_DEAL_FAILURE}; non-null
     * @param priorValues      the resolved prior-step values (the
     *                         receiver and the stored value); non-null,
     *                         no null entries
     * @param receiverBoundary the op's first child — the
     *                         {@code UNTYPED_CLASS_INPUT} boundary;
     *                         non-null
     * @param fieldBoundary    the op's second child — the
     *                         {@code CLASS_FIELD_ASSIGNMENT} boundary;
     *                         non-null
     * @param layouts          the layout-resolution context
     *                         {@code ClassId → ClassLayout}; the
     *                         payload's classId must resolve; non-null
     * @param checkRunner      the boundary-check delegate; non-null
     * @return {@code Success} with the updated instance (the store
     *         committed), or {@code Failure} with the first failing
     *         boundary's failure at the op origin (nothing committed)
     * @throws Defect               on a shape outside the pinned
     *                              contracts (the
     *                              {@link #executeFieldRead} set)
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeFieldWrite(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            SemanticOp receiverBoundary,
            SemanticOp fieldBoundary,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner) {
        requireOp(op, SemanticOpKind.FIELD_WRITE, FailurePolicyId.NO_DEAL_FAILURE);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(receiverBoundary, "receiverBoundary must not be null");
        Objects.requireNonNull(fieldBoundary, "fieldBoundary must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.FieldWritePayload payload = (KindPayload.FieldWritePayload) op.payload();

        // The receiver and the stored value each resolve exactly once.
        Value receiver = resolve(priorValues, payload.classValue());
        Value stored = resolve(priorValues, payload.value());

        // The nominal receiver boundary first (K-D6).
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(payload.classId());
        requireFieldBoundaryChild(receiverBoundary, op, BoundaryKind.UNTYPED_CLASS_INPUT,
            classDescriptor, payload.classValue());
        BoundaryResult receiverResult =
            runReceiverBoundary(op, receiverBoundary, receiver, checkRunner);
        if (receiverResult instanceof BoundaryResult.Fail fail) {
            return new Outcome.Failure<Value>(new OpFailure(fail.failure(), op.origin()));
        }
        Value receiverValue = ((BoundaryResult.Pass) receiverResult).value();
        ClassLayout layout = requireInstance(op, payload.classId(), receiverValue, layouts);
        int fieldIndex = fieldIndexOf(op, layout, payload.field());
        ClassLayout.FieldLayout fieldLayout = layout.fields().get(fieldIndex);

        // The field boundary with the stored value and the field's
        // declared descriptor (K-D6); the store commits only after both
        // pass — a failed boundary commits nothing.
        requireFieldBoundaryChild(fieldBoundary, op, BoundaryKind.CLASS_FIELD_ASSIGNMENT,
            fieldLayout.descriptor(), payload.value());
        BoundaryResult fieldResult = checkRunner.run(
            (KindPayload.BoundaryPayload) fieldBoundary.payload(), stored);
        if (fieldResult instanceof BoundaryResult.Fail fail) {
            return new Outcome.Failure<Value>(new OpFailure(fail.failure(), op.origin()));
        }

        // The store commits immediately before SUCCESS: the published
        // instance carries the boundary-published value in the named
        // field; every other field state is unchanged.
        Value committed = ((BoundaryResult.Pass) fieldResult).value();
        return new Outcome.Success<Value>(updatedInstance((Value.Class) receiverValue,
            fieldIndex, new FieldState.Present(committed)));
    }

    // =========================================================================
    // FIELD_DELETE
    // =========================================================================

    /**
     * Executes one validated {@code FIELD_DELETE} commit op (K-D6): the
     * nominal receiver boundary runs (the {@code UNTYPED_CLASS_INPUT}
     * child with descriptor {@code class:<ClassId>} and input = the
     * payload's resolved receiver), then the field is set missing — the
     * published instance carries {@code Missing} in the named field with
     * every other field state unchanged. Deleting an already-missing
     * field is a no-op SUCCESS (the published instance equals the
     * receiver's state). The receiver resolves from the value lookup
     * exactly once; the key is the static payload field name (never
     * evaluated).
     *
     * <p>The child is supplied as an explicit op and is shape-checked
     * fail closed before the run exactly like {@link #executeFieldRead}'s
     * children (pinned kind, {@code parentOpId} = the
     * {@code FIELD_DELETE} op, a {@code RuntimeValidation} realization,
     * the pinned descriptor and input, the descriptor-kind policy).</p>
     *
     * @param op               the validated {@code FIELD_DELETE} op
     *                         carrying {@code NO_DEAL_FAILURE}; non-null
     * @param priorValues      the resolved prior-step values (the
     *                         receiver); non-null, no null entries
     * @param receiverBoundary the op's only child — the
     *                         {@code UNTYPED_CLASS_INPUT} boundary;
     *                         non-null
     * @param layouts          the layout-resolution context
     *                         {@code ClassId → ClassLayout}; the
     *                         payload's classId must resolve; non-null
     * @param checkRunner      the boundary-check delegate; non-null
     * @return {@code Success} with the updated instance (the field
     *         missing), or {@code Failure} with the failing boundary's
     *         failure at the op origin
     * @throws Defect               on a shape outside the pinned
     *                              contracts (the
     *                              {@link #executeFieldRead} set)
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeFieldDelete(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            SemanticOp receiverBoundary,
            Map<ClassId, ClassLayout> layouts,
            BoundaryCheckRunner checkRunner) {
        requireOp(op, SemanticOpKind.FIELD_DELETE, FailurePolicyId.NO_DEAL_FAILURE);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(receiverBoundary, "receiverBoundary must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(checkRunner, "checkRunner must not be null");
        KindPayload.FieldDeletePayload payload = (KindPayload.FieldDeletePayload) op.payload();

        // The receiver resolves exactly once (never re-evaluated).
        Value receiver = resolve(priorValues, payload.classValue());

        // The nominal receiver boundary (K-D6).
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(payload.classId());
        requireFieldBoundaryChild(receiverBoundary, op, BoundaryKind.UNTYPED_CLASS_INPUT,
            classDescriptor, payload.classValue());
        BoundaryResult receiverResult =
            runReceiverBoundary(op, receiverBoundary, receiver, checkRunner);
        if (receiverResult instanceof BoundaryResult.Fail fail) {
            return new Outcome.Failure<Value>(new OpFailure(fail.failure(), op.origin()));
        }
        Value receiverValue = ((BoundaryResult.Pass) receiverResult).value();
        ClassLayout layout = requireInstance(op, payload.classId(), receiverValue, layouts);
        int fieldIndex = fieldIndexOf(op, layout, payload.field());

        // Set the field missing; deleting an already-missing field is a
        // no-op SUCCESS (the produced instance equals the receiver's
        // state).
        return new Outcome.Success<Value>(updatedInstance((Value.Class) receiverValue,
            fieldIndex, FieldState.Missing.INSTANCE));
    }

    // =========================================================================
    // HAS_FIELD
    // =========================================================================

    /**
     * Executes one validated {@code HAS_FIELD} op (K-D7): the receiver
     * resolves from the value lookup exactly once (the key is the static
     * payload field name — never evaluated) and the op publishes the
     * presence boolean: present (present null included) → {@code true},
     * missing → {@code false}. The op runs no boundary children of any
     * kind and its policy is {@code NO_DEAL_FAILURE} — a valid shape
     * never fails, so the success terminal always carries the presence
     * boolean.
     *
     * <p>The presence states stay distinct in the class value view:
     * {@code Present(null)} is present, {@code Missing} is missing —
     * never conflated.</p>
     *
     * @param op          the validated {@code HAS_FIELD} op carrying
     *                    {@code NO_DEAL_FAILURE}; non-null
     * @param priorValues the resolved prior-step values (the receiver);
     *                    non-null, no null entries
     * @param layouts     the layout-resolution context
     *                    {@code ClassId → ClassLayout}; the instance's
     *                    own classId must resolve; non-null
     * @return {@code Success} with the presence boolean
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy, a
     *                              receiver that does not resolve to a
     *                              class, an unresolvable layout, a key
     *                              not declared in the layout, or an
     *                              instance field-count mismatch
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeHasField(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<ClassId, ClassLayout> layouts) {
        requireOp(op, SemanticOpKind.HAS_FIELD, FailurePolicyId.NO_DEAL_FAILURE);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        KindPayload.HasFieldPayload payload = (KindPayload.HasFieldPayload) op.payload();

        // The receiver resolves exactly once; the key is never evaluated.
        Value receiver = resolve(priorValues, payload.receiver());
        if (!(receiver instanceof Value.Class instance)) {
            throw new Defect("HAS_FIELD " + op.opId() + " receiver " + payload.receiver()
                + " resolves to " + receiver.actualKind()
                + ": the pinned receiver is a class instance (the checker admits class "
                + "receivers only) — a producer defect, never a projection");
        }
        ClassLayout layout = layouts.get(instance.classId());
        if (layout == null) {
            throw new Defect("HAS_FIELD " + op.opId() + " instance classId "
                + instance.classId() + " does not resolve in the layout-resolution "
                + "context: the presence read maps the static key through the instance's "
                + "own layout — an unresolvable layout is a producer defect, never "
                + "executed");
        }
        if (layout.fields().size() != instance.fields().size()) {
            throw new Defect("HAS_FIELD " + op.opId() + " instance of "
                + instance.classId() + " carries " + instance.fields().size()
                + " field states for a layout of " + layout.fields().size()
                + " fields: the pinned instance shape matches its layout's declaration "
                + "order — a count mismatch is a producer defect, never executed");
        }
        int fieldIndex = fieldIndexOf(op, layout, payload.key());
        FieldState state = instance.fields().get(fieldIndex);
        return new Outcome.Success<Value>(new Value.Bool(
            state instanceof FieldState.Present));
    }

    // =========================================================================
    // Field-op fail-closed helpers
    // =========================================================================

    /**
     * Requires one field-op boundary child's pinned shape fail closed:
     * a {@code BOUNDARY} op of the pinned kind whose origin
     * {@code parentOpId} is the owning field op, a
     * {@code RuntimeValidation} realization (proof is inadmissible on
     * these cells, K-D6), the pinned descriptor, the pinned input, and
     * the descriptor-kind policy.
     */
    private static void requireFieldBoundaryChild(SemanticOp child, SemanticOp owner,
                                                  BoundaryKind pinnedKind,
                                                  RuntimeDescriptor pinnedDescriptor,
                                                  ValueId pinnedInput) {
        requireChildOf(child, owner, pinnedKind);
        KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) child.payload();
        if (!(payload.realization() instanceof BoundaryRealization.RuntimeValidation)) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names boundary child "
                + child.opId() + " carrying realization " + payload.realization()
                + ": the pinned field-op boundary cells are RuntimeValidation only "
                + "(representation proof is inadmissible on UNTYPED_CLASS_INPUT, "
                + "OPTIONAL_FIELD_READ, and CLASS_FIELD_ASSIGNMENT) — a producer defect, "
                + "never executed");
        }
        if (!payload.descriptor().equals(pinnedDescriptor)) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names boundary child "
                + child.opId() + " carrying descriptor "
                + payload.descriptor().canonicalSpecText() + ": the pinned child "
                + "descriptor is " + pinnedDescriptor.canonicalSpecText()
                + " — a mismatch is a producer defect, never executed");
        }
        if (!payload.input().equals(pinnedInput)) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names boundary child "
                + child.opId() + " carrying input " + payload.input()
                + ": the pinned input is " + pinnedInput + " (K-D6 input wiring) — a "
                + "mismatch is a producer defect, never executed");
        }
        requireDescriptorKindPolicy(child, pinnedDescriptor);
    }

    /**
     * Runs the nominal receiver boundary of one field op with the
     * resolved receiver and returns the delegate's terminal. The child's
     * pinned shape has already been checked by the caller
     * ({@link #requireFieldBoundaryChild}); the descriptor-kind policy
     * projection is the delegate's (the production
     * {@link BoundaryExecutor}'s canonical E8001/E8010 projections).
     */
    private static BoundaryResult runReceiverBoundary(SemanticOp op, SemanticOp receiverBoundary,
                                                      Value receiver,
                                                      BoundaryCheckRunner checkRunner) {
        return checkRunner.run((KindPayload.BoundaryPayload) receiverBoundary.payload(),
            receiver);
    }

    /**
     * Requires the post-boundary receiver of one field op: a
     * {@link Value.Class} instance of the payload's classId whose field
     * count matches the resolved layout's declaration order. The pinned
     * receiver boundary on a class descriptor can only pass such an
     * instance (the production delegate's canonical identity check), so
     * any other shape reaching the read/write/delete is a producer
     * defect — never a projection and never a silent read.
     */
    private static ClassLayout requireInstance(SemanticOp op, ClassId classId, Value receiver,
                                               Map<ClassId, ClassLayout> layouts) {
        if (!(receiver instanceof Value.Class instance)) {
            throw new Defect(op.kind() + " " + op.opId() + " receiver boundary passed value "
                + receiver.actualKind() + ": the pinned UNTYPED_CLASS_INPUT boundary on "
                + "descriptor class:" + classId.text() + " can only pass an instance of "
                + classId + " — a wrong-kind value after a passing receiver boundary is a "
                + "producer defect, never executed");
        }
        if (!instance.classId().equals(classId)) {
            throw new Defect(op.kind() + " " + op.opId() + " receiver boundary passed an "
                + "instance of " + instance.classId() + ": the pinned receiver is "
                + classId + " (the canonical nominal identity check) — a wrong-identity "
                + "value after a passing receiver boundary is a producer defect, never "
                + "executed");
        }
        ClassLayout layout = layouts.get(classId);
        if (layout == null) {
            throw new Defect(op.kind() + " " + op.opId() + " classId " + classId
                + " does not resolve in the layout-resolution context: the field "
                + "read/write/delete maps the static field name through the class's "
                + "layout — an unresolvable layout is a producer defect, never executed");
        }
        if (layout.fields().size() != instance.fields().size()) {
            throw new Defect(op.kind() + " " + op.opId() + " instance of " + classId
                + " carries " + instance.fields().size() + " field states for a layout of "
                + layout.fields().size() + " fields: the pinned instance shape matches its "
                + "layout's declaration order — a count mismatch is a producer defect, "
                + "never executed");
        }
        return layout;
    }

    /** The declaration-order index of {@code field} in {@code layout}, fail closed. */
    private static int fieldIndexOf(SemanticOp op, ClassLayout layout, java.lang.String field) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(field)) {
                return i;
            }
        }
        throw new Defect(op.kind() + " " + op.opId() + " names field '" + field
            + "' which is not a declared field of " + layout.classId()
            + ": the pinned payload names declared fields only — a producer defect, "
            + "never executed");
    }

    /**
     * The pinned {@code OPTIONAL_FIELD_READ} result descriptor of one
     * layout field (the checker's optional-read wrap): the field's
     * declared descriptor, nullable-wrapped for an optional non-nullable
     * field.
     */
    private static RuntimeDescriptor readResultDescriptorOf(ClassLayout.FieldLayout field) {
        RuntimeDescriptor declared = field.descriptor();
        if (!field.required() && !(declared instanceof RuntimeDescriptor.Nullable)) {
            return new RuntimeDescriptor.Nullable(declared);
        }
        return declared;
    }

    /**
     * Produces the updated instance of one field commit: the named
     * declaration-order field state replaced with the committed state
     * ({@code Present(committed)} for a write, {@code Missing} for a
     * delete); every other field state is unchanged. The model is
     * immutable, so the commit is the fresh updated instance the caller
     * rebinds the receiver's reference to — a failed boundary produces
     * no updated instance at all (nothing commits).
     */
    private static Value updatedInstance(Value.Class instance, int fieldIndex,
                                         FieldState committed) {
        List<FieldState> states = new ArrayList<>(instance.fields());
        states.set(fieldIndex, committed);
        return new Value.Class(instance.classId(), List.copyOf(states));
    }

    // =========================================================================
    // The JSON algorithm delegate seam (K-D8/K-D10/K-D11)
    // =========================================================================

    /**
     * The pinned parse terminal of the JSON algorithm delegate seam
     * (K-D11): exactly {@code Success(value) | SyntaxFailure}. The
     * seam's parse contract is the E8 {@code JSON_PARSE} row — an
     * RFC-8259 scalar-valid parse of the (already scalar-valid) input;
     * object order follows text; duplicate keys keep the last value and
     * the first position; a signed32 <em>integer lexical form</em>
     * becomes {@link Value.Int} and every other numeric form becomes
     * {@link Value.Number}; a syntax defect is a {@link SyntaxFailure}
     * (the walk swallows it into language null — policy
     * {@code JSON_FROM_NULL} has no visible failure). E8's
     * {@code SharedStdlibSemantics} is the production delegate; the
     * walker tests use a fixture delegate implementing exactly the
     * pinned rows. The executor defines no second production JSON
     * algorithm.
     */
    public sealed interface JsonParse permits JsonParse.Success, JsonParse.SyntaxFailure {

        /**
         * The parse succeeded: {@code value} is the closed parsed-JSON
         * value model of the input — exactly the JSON-shaped subset of
         * the executor's {@link Value} view: {@code Null}, {@code Bool},
         * {@code Int} (signed32 integer lexical forms only),
         * {@code Number}, {@code String} (valid scalar carriers),
         * {@code Table} (objects with ordered entries), and
         * {@code Array}. A value outside that set is a seam-contract
         * violation and fails closed as a producer {@link Defect}.
         */
        record Success(Value value) implements JsonParse {

            public Success {
                Objects.requireNonNull(value, "value must not be null");
            }
        }

        /** The input is not RFC-8259 scalar-valid JSON text. */
        record SyntaxFailure() implements JsonParse {
        }
    }

    /**
     * The pinned stringify terminal of the JSON algorithm delegate seam
     * (K-D11): exactly {@code Success(text) | Failure(fieldPath,
     * actual)}. The seam's stringify contract is the E8
     * {@code JSON_STRINGIFY} row over the executor's JSON-shape view —
     * finite acyclic JSON-shaped data (string-keyed objects, arrays,
     * and null/boolean/int/number/string leaves); object fields in
     * first-insertion order, arrays in index order; RFC-8259 escaping;
     * shortest round-trippable decimal number formatting
     * ({@code Double.toString}); the first failure in declaration order
     * fails with the pinned {@code JSON_TO_CLASS} segment convention —
     * a table key {@code k} appends {@code ".k"}, an array element
     * {@code i} appends {@code "[i]"}, and the root value itself has
     * the empty relative path — prefixed with the caller-supplied field
     * path, so the executor projects the exact
     * {@code value at {fieldPath} is not JSON serializable: {actual}}
     * template (K-D10). Unsupported values, cycles, and nonfinite
     * numbers fail here; acyclic finite data never fails. E8's
     * {@code SharedStdlibSemantics} is the production delegate; the
     * walker tests use a fixture delegate implementing exactly the
     * pinned rows.
     */
    public sealed interface JsonStringify permits JsonStringify.Success, JsonStringify.Failure {

        /** The exact RFC-8259 text of the JSON-shaped value. */
        record Success(UnicodeScalars.Valid text) implements JsonStringify {

            public Success {
                Objects.requireNonNull(text, "text must not be null");
            }
        }

        /**
         * The first declaration-order failure: {@code fieldPath} is the
         * full pinned-convention path (the caller's prefix plus the
         * seam's relative segments), {@code actual} is the offending
         * value's canonical actual-kind token.
         */
        record Failure(String fieldPath, String actual) implements JsonStringify {

            public Failure {
                Objects.requireNonNull(fieldPath, "fieldPath must not be null");
                Objects.requireNonNull(actual, "actual must not be null");
            }
        }
    }

    /**
     * The parse arm of the JSON algorithm delegate seam (K-D11):
     * {@code (UnicodeScalars.Valid) → JsonParse}. The executor calls it
     * once per {@code JSON_FROM_CLASS} execution with the resolved
     * scalar-valid input text; an invalid scalar carrier never reaches
     * the seam (the walk returns language null first — the input is
     * not RFC-8259 text).
     */
    @FunctionalInterface
    public interface JsonParser {

        /**
         * Parses one scalar-valid JSON text per the E8 {@code JSON_PARSE}
         * row.
         *
         * @param text the scalar-valid input text; non-null
         * @return the pinned parse terminal
         */
        JsonParse parse(UnicodeScalars.Valid text);
    }

    /**
     * The stringify arm of the JSON algorithm delegate seam (K-D11):
     * {@code (Value, fieldPathPrefix) → JsonStringify} over the
     * executor's JSON-shape view. The executor delegates every leaf,
     * table, and non-class array element encoding of the
     * {@code JSON_TO_CLASS} walk to this seam — the walk itself owns
     * the declared-field selection/order, presence, identity checks,
     * class recursion, paths, and depth; the seam owns the exact
     * RFC-8259 text and the finite-acyclic JSON-shape discipline.
     */
    @FunctionalInterface
    public interface JsonStringifier {

        /**
         * Stringifies one JSON-shaped value per the E8
         * {@code JSON_STRINGIFY} row.
         *
         * @param jsonShaped      the JSON-shaped value (null, boolean,
         *                        int, number, valid string, table, or
         *                        array); non-null. Nested unsupported
         *                        carriers inside a table or an array —
         *                        a class instance, a function, the
         *                        internal missing view, or an
         *                        invalid-scalar string — are projected
         *                        by the seam's pinned
         *                        {@code Failure(fieldPath, actual)}
         *                        terminal, never thrown by the delegate
         * @param fieldPathPrefix the caller's pinned-convention field
         *                        path prefix the seam appends its
         *                        relative failure path to; non-null
         * @return the pinned stringify terminal
         */
        JsonStringify stringify(Value jsonShaped, String fieldPathPrefix);
    }

    /**
     * The nested-defaults seam of the {@code JSON_FROM_CLASS} walk
     * (K-D8 step 6; K-D5 trigger (b)): fills the omitted
     * required-present defaults of one nested class for the runtime
     * provided-field set by resolving and executing the nested class's
     * {@code CLASS_FACTORY} in the nested declaring module's scope, and
     * returns the default-filled untagged transfer instance. The
     * production caller resolves the factory op through the
     * layout-resolution context (the nested
     * {@link ClassInterface#constructionEntry()} plus the owner unit's
     * {@link ClassFactoryRegistry}) and drives
     * {@link #executeClassFactory} with the triggering
     * {@code JSON_FROM_CLASS} op as the factory's executed
     * {@code parentOpId} (K-D12, cross-unit) — a nested class whose
     * factory does not resolve is a producer defect, never executed and
     * never silently skipped. A failing default child throws (the walk
     * swallows it into language null); the returned instance must carry
     * the nested classId with the nested layout's declaration-order
     * field count (fail closed otherwise).
     */
    @FunctionalInterface
    public interface NestedClassFactory {

        /**
         * Fills the nested class's omitted required-present defaults.
         *
         * @param classId         the nested class identity; non-null
         * @param providedFields  the runtime provided-field name set of
         *                        the nested document (the factory's
         *                        skip-provided rule); non-null
         * @return the default-filled untagged transfer instance (a
         *         {@link Value.Class} of {@code classId})
         */
        Value fillDefaults(ClassId classId, Set<String> providedFields);
    }

    // =========================================================================
    // JSON_FROM_CLASS (the generated C$fromJson walk, K-D8/K-D9)
    // =========================================================================

    /**
     * The pinned bounded walk depth of the two JSON walkers (K-D8/K-D10):
     * {@code 512} — the retained bound of the runtime's JSON plans
     * ({@code deal/runtime.lua} {@code __rt._JSON_MAX_DEPTH = 512}).
     * Nesting deeper than 512 levels fails: the
     * {@code JSON_FROM_CLASS} walk returns language null and the
     * {@code JSON_TO_CLASS} walk fails {@code JSON_TO_ERROR} at the
     * exceeding position.
     */
    public static final int JSON_MAX_DEPTH = 512;

    /**
     * Executes one validated {@code JSON_FROM_CLASS} op (K-D8, the
     * generated {@code C$fromJson} walk), policy
     * {@code JSON_FROM_NULL}:
     *
     * <ol>
     *   <li>the {@code jsonString} operand resolves exactly once; an
     *       invalid scalar carrier is a syntax defect (RFC-8259 text is
     *       scalar-valid) and returns language null;</li>
     *   <li>parse through the {@link JsonParser} seam (the E8
     *       {@code JSON_PARSE} algorithm — signed32 integer lexical
     *       mapping, duplicate keys keep last value and first position,
     *       document order preserved); a syntax defect returns language
     *       null (no DEAL failure);</li>
     *   <li>the top-level gate (K-D8 step 2): a JSON null returns
     *       language null; a JSON object walks; an empty array
     *       {@code []} decodes as the defaulted instance (the pinned
     *       {@code {}}/{@code []} collapse); a non-empty array or
     *       scalar returns language null;</li>
     *   <li>the extra-key gate in document order (K-D8 step 3): the
     *       first parsed key that is not a declared field returns
     *       language null before any field decode or default runs;</li>
     *   <li>provided-field decode in declaration order (K-D8 step 4):
     *       per the field's declared descriptor — int fields accept
     *       only {@code Int} carriers from the parse's signed32 lexical
     *       mapping (out-of-range, fractional, or {@code Number}
     *       carriers fail); nullable fields accept JSON null; a JSON
     *       null on a non-nullable field fails; {@code table} fields
     *       accept only a JSON object or the empty-array collapse (a
     *       non-empty array-shaped value fails — the retained pins);
     *       {@code array} fields decode element-wise; class fields
     *       recurse into the nested walk with an identity check and the
     *       same phase order. A decode failure returns language null
     *       immediately and no defaults run (parent D5);</li>
     *   <li>default application in declaration order (K-D8 step 5):
     *       the op's per-site {@code CLASS_DEFAULT} children (the
     *       {@code JsonDefaultChildTable} record's declaration-order
     *       list resolved through {@code defaultChildIds}/
     *       {@code defaultOps}) run exactly once each for omitted
     *       required-present fields, skipping fields present in the
     *       document; an absent required-present field without a
     *       declared default is a field failure returning language null
     *       (K-D9 — no per-type reference defaults are invented); a
     *       failing child returns language null with the completed
     *       children's effects remaining;</li>
     *   <li>nested-class defaults (K-D8 step 6): a nested class decode
     *       triggers the nested class's {@code CLASS_FACTORY} through
     *       the {@link NestedClassFactory} seam (K-D5 trigger (b)),
     *       which fills the nested defaults in the nested declaring
     *       module's scope; the decoded provided fields overlay; nested
     *       validation; nested tag; a nested failure returns language
     *       null end-to-end;</li>
     *   <li>final validation in declaration order (K-D8 step 7): every
     *       present field (decoded or defaulted) validates against its
     *       declared descriptor through the executor's internal
     *       descriptor checks with the {@code JSON_FROM_NULL}
     *       projection — never {@code BOUNDARY} children
     *       (walk-internal values have no IR {@code ValueId}s);</li>
     *   <li>the fresh instance is tagged with the classId and published
     *       (K-D8 step 8); omitted optionals stay missing and present
     *       null stays present null (the three-state roundtrip).</li>
     * </ol>
     *
     * Every listed failure publishes language null and no partial
     * instance is visible; the walk is bounded by
     * {@link #JSON_MAX_DEPTH} over class/array recursion and
     * table-field contents (exceeding it returns language null). The
     * op runs zero boundary children and zero return boundaries — the
     * executor never drives a {@code BOUNDARY} child.
     *
     * @param op               the validated {@code JSON_FROM_CLASS} op
     *                         carrying {@code JSON_FROM_NULL}; non-null
     * @param priorValues      the resolved prior-step values (the
     *                         {@code jsonString} operand); non-null, no
     *                         null entries
     * @param defaultChildIds  the op's per-site {@code CLASS_DEFAULT}
     *                         child op ids in declaration order (the
     *                         unit's {@code JsonDefaultChildTable}
     *                         entry); non-null
     * @param defaultOps       the unit's {@code CLASS_DEFAULT} ops by
     *                         {@link OpId}; every id of
     *                         {@code defaultChildIds} must resolve to a
     *                         {@code CLASS_DEFAULT} op of the layout's
     *                         classId carrying
     *                         {@code NO_DEAL_FAILURE}; non-null
     * @param layouts          the layout-resolution context
     *                         {@code ClassId → ClassLayout} (the unit's
     *                         {@code classLayouts} plus the project
     *                         interface index); the payload's layout
     *                         must resolve to exactly the payload's
     *                         layout and every nested class must resolve;
     *                         non-null
     * @param parser           the parse arm of the JSON algorithm seam;
     *                         non-null
     * @param nestedFactory    the nested-class default-filling seam
     *                         (K-D5 trigger (b)); non-null
     * @param bodyRunner       the default-block callback for the op's
     *                         own {@code CLASS_DEFAULT} children; non-null
     * @return the tagged fresh instance, or language null
     *         ({@link Value.Null}) on every listed failure — never a
     *         partial instance
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy,
     *                              an unresolvable or mismatched layout,
     *                              an unresolvable or wrong-kind operand,
     *                              a default child of the wrong
     *                              kind/policy/class/field, a duplicate
     *                              default child, a nested factory
     *                              producing a wrong-kind or
     *                              wrong-shaped instance, an
     *                              unresolvable nested layout, a
     *                              non-JSON-shaped seam result, or a
     *                              producer Defect thrown by the
     *                              default-block runner or the nested
     *                              factory seam (fail closed, never the
     *                              walk's language-null carrier)
     * @throws NullPointerException if any argument is null
     */
    public static Value executeJsonFromClass(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            List<OpId> defaultChildIds,
            Map<OpId, SemanticOp> defaultOps,
            Map<ClassId, ClassLayout> layouts,
            JsonParser parser,
            NestedClassFactory nestedFactory,
            BodyRunner bodyRunner) {
        requireOp(op, SemanticOpKind.JSON_FROM_CLASS, FailurePolicyId.JSON_FROM_NULL);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(defaultChildIds, "defaultChildIds must not be null");
        Objects.requireNonNull(defaultOps, "defaultOps must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(parser, "parser must not be null");
        Objects.requireNonNull(nestedFactory, "nestedFactory must not be null");
        Objects.requireNonNull(bodyRunner, "bodyRunner must not be null");
        KindPayload.JsonFromClassPayload payload =
            (KindPayload.JsonFromClassPayload) op.payload();

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.layout().classId());
        if (layout == null || !layout.equals(payload.layout())) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " layout of "
                + payload.layout().classId() + " does not resolve to exactly the "
                + "payload's layout in the layout-resolution context: the payload's "
                + "layout must be exactly the resolved layout — an unresolvable or "
                + "mismatched layout is a producer defect, never executed");
        }

        // The JSON string operand resolves exactly once (never
        // re-evaluated); an invalid scalar carrier is a syntax defect of
        // the walk's input — RFC-8259 text is scalar-valid, so the walk
        // returns language null before any parse or default runs.
        Value operand = resolve(priorValues, payload.jsonString());
        if (!(operand instanceof Value.String string)) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " jsonString operand "
                + payload.jsonString() + " resolves to " + operand.actualKind()
                + ": the pinned operand is a string value (the generated body's "
                + "parameter load) — a wrong-kind operand is a producer defect, never "
                + "executed");
        }
        if (!(string.scalar() instanceof UnicodeScalars.Valid valid)) {
            return Value.Null.INSTANCE;
        }

        // Parse through the seam (the E8 JSON_PARSE algorithm); a syntax
        // defect returns language null — no DEAL failure.
        JsonParse parsed = parser.parse(valid);
        if (parsed instanceof JsonParse.SyntaxFailure) {
            return Value.Null.INSTANCE;
        }
        Value document = ((JsonParse.Success) parsed).value();
        requireJsonShape(op, document);

        // The top-level gate (K-D8 step 2): a JSON null → null; a JSON
        // object → the walk; an empty array [] → the defaulted instance
        // (the pinned {}/[] collapse); a non-empty array or scalar → null.
        if (document instanceof Value.Null) {
            return Value.Null.INSTANCE;
        }
        if (document instanceof Value.Array empty && empty.array().size() == 0) {
            document = emptyTable();
        }
        if (!(document instanceof Value.Table table)) {
            return Value.Null.INSTANCE;
        }
        try {
            return decodeFromJson(op, layout, (Value.Table) table, defaultChildIds,
                defaultOps, layouts, nestedFactory, bodyRunner, 0);
        } catch (JsonFromFailure failure) {
            // Every listed walk failure publishes language null and no
            // partial instance is visible; completed default-block
            // effects remain (the walk never rolls back a runner).
            return Value.Null.INSTANCE;
        }
    }

    // =========================================================================
    // JSON_TO_CLASS (the generated C$toJson walk, K-D10)
    // =========================================================================

    /**
     * Executes one validated {@code JSON_TO_CLASS} op (K-D10, the
     * generated {@code C$toJson} walk), policy {@code JSON_TO_ERROR}:
     *
     * <ol>
     *   <li>the {@code classValue} operand resolves exactly once; the
     *       root identity check requires an instance of exactly the
     *       layout's classId — otherwise the op fails
     *       {@code JSON_TO_ERROR} — E8001
     *       {@code value at {fieldPath} is not JSON serializable: {actual}}
     *       with fieldPath {@code ""} (the root) and {@code actual} the
     *       offending value's canonical actual-kind token
     *       ({@code class:<other>} for a wrong identity);</li>
     *   <li>each declared field serializes in declaration order: an
     *       omitted optional field is skipped; a missing required field
     *       fails (the "missing required value" arm, {@code actual}
     *       {@code missing}); present null serializes as JSON null;
     *       primitives encode per JSON kind (nonfinite numbers fail);
     *       class fields recurse with a nested identity check; array
     *       fields encode element-wise; {@code table} fields run the
     *       seam's finite-acyclic JSON-shape walk (functions, class
     *       instances, NaN/Infinity, and cyclic containers inside a
     *       table fail);</li>
     *   <li>cycle detection is path-local (a seen set over entered
     *       class instances); re-entry fails at the re-entering
     *       position; the walk is bounded by {@link #JSON_MAX_DEPTH}
     *       over class/array recursion and table-field contents
     *       (exceeding it fails at the exceeding position);</li>
     *   <li>the first failure wins in declaration order; the pinned
     *       fieldPath convention — root {@code ""}, a declared field
     *       {@code f} = {@code "f"}, a nested class field under
     *       {@code f} = {@code "f.g"}, an array element =
     *       {@code "f[0]"} (0-based), a table object key =
     *       {@code "f.k"};</li>
     *   <li>the failure origin is the call origin — the origin of the
     *       call invoking the generated {@code C$toJson} ({@code
     *       callOrigin}, resolved through the active call executing the
     *       op; the generated body's synthetic anchor is never used);
     *       frames are the active DEAL calls; no cause;</li>
     *   <li>success emits deterministic RFC-8259 text — declared
     *       fields in declaration order, table entries in
     *       first-insertion order, arrays in index order, shortest
     *       round-trippable number formatting (the E8 stringify
     *       algorithm).</li>
     * </ol>
     *
     * The op runs zero boundary children and zero return boundaries —
     * the executor never drives a {@code BOUNDARY} child.
     *
     * @param op           the validated {@code JSON_TO_CLASS} op
     *                     carrying {@code JSON_TO_ERROR}; non-null
     * @param priorValues  the resolved prior-step values (the
     *                     {@code classValue} operand); non-null, no null
     *                     entries
     * @param layouts      the layout-resolution context
     *                     {@code ClassId → ClassLayout}; the payload's
     *                     layout must resolve to exactly the payload's
     *                     layout and every nested class must resolve;
     *                     non-null
     * @param stringifier  the stringify arm of the JSON algorithm seam;
     *                     non-null
     * @param callOrigin   the call origin of the call invoking the
     *                     generated {@code C$toJson} — the
     *                     {@code JSON_TO_ERROR} projection origin (the
     *                     generated body's synthetic anchor is never
     *                     used); non-null
     * @return {@code Success} with the deterministic JSON text, or
     *         {@code Failure} with the first declaration-order
     *         {@code JSON_TO_ERROR} projection at the call origin
     * @throws Defect               on a shape outside the pinned
     *                              contracts — a wrong op kind/policy,
     *                              an unresolvable or mismatched layout,
     *                              an unresolvable operand, an
     *                              unresolvable nested layout, or a
     *                              function-typed field descriptor
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> executeJsonToClass(
            SemanticOp op,
            Map<ValueId, Value> priorValues,
            Map<ClassId, ClassLayout> layouts,
            JsonStringifier stringifier,
            SourceOrigin callOrigin) {
        requireOp(op, SemanticOpKind.JSON_TO_CLASS, FailurePolicyId.JSON_TO_ERROR);
        Objects.requireNonNull(priorValues, "priorValues must not be null");
        Objects.requireNonNull(layouts, "layouts must not be null");
        Objects.requireNonNull(stringifier, "stringifier must not be null");
        Objects.requireNonNull(callOrigin, "callOrigin must not be null");
        KindPayload.JsonToClassPayload payload =
            (KindPayload.JsonToClassPayload) op.payload();

        // Layout resolution (K-D11): the payload is never interpreted
        // against a foreign layout.
        ClassLayout layout = layouts.get(payload.layout().classId());
        if (layout == null || !layout.equals(payload.layout())) {
            throw new Defect("JSON_TO_CLASS " + op.opId() + " layout of "
                + payload.layout().classId() + " does not resolve to exactly the "
                + "payload's layout in the layout-resolution context: the payload's "
                + "layout must be exactly the resolved layout — an unresolvable or "
                + "mismatched layout is a producer defect, never executed");
        }

        // The class value operand resolves exactly once (never
        // re-evaluated).
        Value operand = resolve(priorValues, payload.classValue());
        Set<Object> entered = java.util.Collections.newSetFromMap(
            new java.util.IdentityHashMap<>());
        try {
            String text = encodeToJson(op, layout, operand, layouts, stringifier,
                entered, 0, "");
            return new Outcome.Success<Value>(Value.string(text));
        } catch (JsonToFailure failure) {
            // The first declaration-order failure: the registry row's
            // exact template, projected at the call origin (never the
            // generated body's synthetic anchor) with no cause.
            BoundaryFailure row = BoundaryFailure.fromRow(
                FailureContractRegistry.row(FailurePolicyId.JSON_TO_ERROR), 0, null, null,
                metadataOf("fieldPath", failure.fieldPath, "actual", failure.actual),
                null);
            return new Outcome.Failure<Value>(new OpFailure(row, callOrigin));
        }
    }

    // =========================================================================
    // The JSON walk internals (fail closed, never a DEAL projection)
    // =========================================================================

    /**
     * The internal failure of the {@code JSON_FROM_CLASS} walk: exactly
     * the swallowed-failure carrier (K-D8 — policy {@code JSON_FROM_NULL}
     * has no visible failure). Every decode/default/field/nested/depth
     * failure of the walk throws it; {@link #executeJsonFromClass}
     * catches it and publishes language null. A default child's own
     * failure is wrapped (completed effects remain); producer defects
     * ({@link Defect}) and infrastructure failures never use this
     * carrier.
     */
    private static final class JsonFromFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        JsonFromFailure(String reason) {
            super(reason);
        }

        JsonFromFailure(String reason, Throwable cause) {
            super(reason, cause);
        }
    }

    /**
     * The internal failure of the {@code JSON_TO_CLASS} walk: the first
     * declaration-order failing position's pinned fieldPath and the
     * offending value's canonical actual-kind token — the carrier
     * {@link #executeJsonToClass} projects as the
     * {@code JSON_TO_ERROR} row at the call origin.
     */
    private static final class JsonToFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        final String fieldPath;
        final String actual;

        JsonToFailure(String fieldPath, String actual) {
            super("value at " + fieldPath + " is not JSON serializable: " + actual);
            this.fieldPath = fieldPath;
            this.actual = actual;
        }
    }

    /**
     * The declaration-order decode walk of one parsed JSON object
     * document (K-D8 steps 3-8): the extra-key gate in document order,
     * provided-field decode in declaration order, default application in
     * declaration order (the op's per-site {@code CLASS_DEFAULT}
     * children, skipping provided fields; K-D9 for an absent
     * required-present no-default field), final validation in
     * declaration order, and the tag. Returns the tagged fresh instance
     * or throws {@link JsonFromFailure} (language null).
     */
    private static Value decodeFromJson(
            SemanticOp op, ClassLayout layout, Value.Table document,
            List<OpId> defaultChildIds, Map<OpId, SemanticOp> defaultOps,
            Map<ClassId, ClassLayout> layouts, NestedClassFactory nestedFactory,
            BodyRunner bodyRunner, int depth) {
        if (depth > JSON_MAX_DEPTH) {
            throw new JsonFromFailure("walk depth exceeded " + JSON_MAX_DEPTH
                + " (the pinned retained bound)");
        }
        // The pinned default-child shape, checked fail closed before the
        // walk: exactly one CLASS_DEFAULT child per required-present
        // defaulted field in declaration order (the JsonDefaultChildTable
        // record's production shape).
        LinkedHashMap<String, SemanticOp> defaultsByField = new LinkedHashMap<>();
        for (OpId childId : defaultChildIds) {
            SemanticOp child = requireDefaultChild(defaultOps, childId, layout.classId(),
                op);
            KindPayload.ClassDefaultPayload defaultPayload =
                (KindPayload.ClassDefaultPayload) child.payload();
            ClassLayout.FieldLayout fieldLayout = fieldOf(layout, defaultPayload.field());
            if (fieldLayout == null || !fieldLayout.required()) {
                throw new Defect("JSON_FROM_CLASS " + op.opId() + " names CLASS_DEFAULT "
                    + "child " + childId + " for field '" + defaultPayload.field()
                    + "' which is not a required-present declared field of "
                    + layout.classId() + ": the JsonDefaultChildTable lists "
                    + "required-present defaulted fields only — a producer defect, "
                    + "never executed");
            }
            if (defaultsByField.containsKey(defaultPayload.field())) {
                throw new Defect("JSON_FROM_CLASS " + op.opId() + " names two "
                    + "CLASS_DEFAULT children for field '" + defaultPayload.field()
                    + "': the pinned shape carries exactly one default child per "
                    + "defaulted field — a duplicate is a producer defect, never "
                    + "executed");
            }
            defaultsByField.put(defaultPayload.field(), child);
        }

        // The extra-key gate, document order (K-D8 step 3): the first
        // parsed key not a declared field fails before any field decode
        // or default runs.
        SemanticTable<Value> entries = document.table();
        for (String key : entries.keys()) {
            if (fieldOf(layout, key) == null) {
                throw new JsonFromFailure("extra key '" + key + "' in the JSON document "
                    + "of " + layout.classId() + " (K-D8 step 3)");
            }
        }

        // Provided-field decode in declaration order (K-D8 step 4): a
        // decode failure fails the walk immediately and no defaults run.
        LinkedHashMap<String, Value> instanceFields = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout field : layout.fields()) {
            SemanticTable.Lookup<Value> lookup = entries.get(field.name());
            if (!(lookup instanceof SemanticTable.Lookup.Present<Value> present)) {
                continue;
            }
            Value raw = present.value();
            requireJsonShape(op, raw);
            instanceFields.put(field.name(), decodeRaw(op, field.descriptor(), raw,
                layouts, nestedFactory, bodyRunner, depth));
        }

        // Default application in declaration order (K-D8 step 5): an
        // omitted required-present field with a declared default runs its
        // CLASS_DEFAULT child exactly once (a provided field's default
        // never runs); an absent required-present field without a
        // declared default is a field failure (K-D9 — no per-type
        // reference defaults are invented); an omitted optional field
        // stays missing. A failing child fails the walk (language null)
        // with the completed children's effects remaining.
        for (ClassLayout.FieldLayout field : layout.fields()) {
            if (instanceFields.containsKey(field.name())) {
                continue; // provided: decoded; the skip-provided rule.
            }
            if (!field.required()) {
                continue; // optional: stays missing, no default ever runs.
            }
            SemanticOp child = defaultsByField.get(field.name());
            if (child == null) {
                throw new JsonFromFailure("required-present field '" + field.name()
                    + "' absent from the JSON document without a declared default "
                    + "(K-D9)");
            }
            Value produced;
            try {
                produced = bodyRunner.runDefault(child);
            } catch (Defect defect) {
                // Fail closed (K-D11): producer defects and infrastructure
                // failures never use the walk's language-null carrier.
                throw defect;
            } catch (RuntimeException childFailure) {
                throw new JsonFromFailure("CLASS_DEFAULT child " + child.opId()
                    + " of field '" + field.name() + "' failed (K-D8 step 5)",
                    childFailure);
            }
            if (produced instanceof Value.Missing) {
                throw new Defect("JSON_FROM_CLASS " + op.opId() + " CLASS_DEFAULT child "
                    + child.opId() + " produced the internal Missing view: a default "
                    + "block always produces a present value (language null is the "
                    + "explicit Null variant) — a wrong-kind value is a producer "
                    + "defect, never executed");
            }
            instanceFields.put(field.name(), produced);
        }

        // Final validation in declaration order (K-D8 step 7): every
        // present field (decoded or defaulted) validates against its
        // declared descriptor through the executor's internal descriptor
        // checks with the JSON_FROM_NULL projection — never BOUNDARY
        // children (walk-internal values have no IR ValueIds).
        for (ClassLayout.FieldLayout field : layout.fields()) {
            Value value = instanceFields.get(field.name());
            if (value == null) {
                continue;
            }
            requireDescriptorConforming(op, field.descriptor(), value, layouts);
        }

        // Tag and publish (K-D8 step 8): declaration-order states;
        // omitted optionals stay missing; present null stays present
        // null.
        return taggedInstance(layout, instanceFields);
    }

    /**
     * The nested-class decode of one {@code JSON_FROM_CLASS} walk
     * (K-D8 step 6, the same phase order as the top walk): the nested
     * extra-key gate, provided decode in declaration order, default
     * application through the nested class's {@code CLASS_FACTORY}
     * (the {@link NestedClassFactory} seam — K-D5 trigger (b); the
     * nested defaults evaluate in the nested declaring module's scope;
     * a failing factory child fails the walk end-to-end — language
     * null), the decoded provided fields overlay, final validation, and
     * the nested tag.
     */
    private static Value decodeNestedClass(
            SemanticOp op, ClassId classId, Value.Table document,
            Map<ClassId, ClassLayout> layouts, NestedClassFactory nestedFactory,
            BodyRunner bodyRunner, int depth) {
        if (depth > JSON_MAX_DEPTH) {
            throw new JsonFromFailure("walk depth exceeded " + JSON_MAX_DEPTH
                + " (the pinned retained bound)");
        }
        ClassLayout nested = layouts.get(classId);
        if (nested == null) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " nested decode of "
                + classId + " does not resolve in the layout-resolution context: every "
                + "nested @jsonable class resolves through the unit's classLayouts plus "
                + "the project interface index — an unresolvable nested layout is a "
                + "producer defect, never executed");
        }
        // The nested extra-key gate in document order.
        SemanticTable<Value> entries = document.table();
        for (String key : entries.keys()) {
            if (fieldOf(nested, key) == null) {
                throw new JsonFromFailure("extra key '" + key + "' in the JSON document "
                    + "of nested class " + classId + " (K-D8 step 6)");
            }
        }
        // Nested provided-field decode in declaration order.
        LinkedHashMap<String, Value> decoded = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout field : nested.fields()) {
            SemanticTable.Lookup<Value> lookup = entries.get(field.name());
            if (!(lookup instanceof SemanticTable.Lookup.Present<Value> present)) {
                continue;
            }
            Value raw = present.value();
            requireJsonShape(op, raw);
            decoded.put(field.name(), decodeRaw(op, field.descriptor(), raw, layouts,
                nestedFactory, bodyRunner, depth));
        }
        // Nested default application through the nested class's
        // CLASS_FACTORY (K-D5 trigger (b)): the factory fills the
        // omitted required-present defaults in the nested declaring
        // module's scope (skip-provided) and returns the default-filled
        // untagged transfer instance. A failing factory child fails the
        // walk end-to-end (language null, K-D8 step 6 / K-D5's
        // failing-child rule) with the completed children's effects
        // remaining; a producer Defect of the seam or the factory
        // execution fails closed (K-D11), never null.
        Value filled;
        try {
            filled = nestedFactory.fillDefaults(classId,
                new LinkedHashSet<>(decoded.keySet()));
        } catch (Defect defect) {
            // Fail closed (K-D11): producer defects and infrastructure
            // failures never use the walk's language-null carrier.
            throw defect;
        } catch (RuntimeException factoryFailure) {
            throw new JsonFromFailure("nested CLASS_FACTORY of " + classId
                + " failed during default filling (K-D8 step 6)",
                factoryFailure);
        }
        if (!(filled instanceof Value.Class instance)) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " nested factory of "
                + classId + " produced " + filled.actualKind() + ": the factory returns "
                + "the default-filled transfer instance (a Value.Class) — a producer "
                + "defect, never executed");
        }
        if (!instance.classId().equals(classId)) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " nested factory of "
                + classId + " produced an instance of " + instance.classId()
                + ": the factory fills its own class's declared layout — a wrong "
                + "identity is a producer defect, never executed");
        }
        if (instance.fields().size() != nested.fields().size()) {
            throw new Defect("JSON_FROM_CLASS " + op.opId() + " nested factory of "
                + classId + " produced an instance of " + instance.fields().size()
                + " field states for a layout of " + nested.fields().size()
                + " fields: the pinned instance shape matches its layout's declaration "
                + "order — a count mismatch is a producer defect, never executed");
        }
        // The decoded provided fields overlay the factory-filled instance
        // in declaration order; an absent required-present no-default
        // field is a field failure (K-D9); omitted optionals stay missing.
        LinkedHashMap<String, Value> instanceFields = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout field : nested.fields()) {
            Value provided = decoded.get(field.name());
            if (provided != null) {
                instanceFields.put(field.name(), provided);
                continue;
            }
            Value defaulted = defaultValueOf(instance, nested, field.name());
            if (defaulted != null) {
                instanceFields.put(field.name(), defaulted);
                continue;
            }
            if (field.required()) {
                throw new JsonFromFailure("required-present field '" + field.name()
                    + "' of nested class " + classId + " absent without a declared "
                    + "default (K-D9)");
            }
        }
        // Nested final validation in declaration order, then the nested
        // tag.
        for (ClassLayout.FieldLayout field : nested.fields()) {
            Value value = instanceFields.get(field.name());
            if (value == null) {
                continue;
            }
            requireDescriptorConforming(op, field.descriptor(), value, layouts);
        }
        return taggedInstance(nested, instanceFields);
    }

    /**
     * Decodes one raw parsed-JSON value per the field's declared
     * descriptor (K-D8 step 4): int fields accept only {@code Int}
     * carriers from the parse's signed32 lexical mapping; nullable
     * fields accept JSON null; a JSON null on a non-nullable field
     * fails; {@code table} fields accept only a JSON object or the
     * empty-array collapse, and their parsed subtrees are depth-bounded
     * by the walk's {@link #JSON_MAX_DEPTH} bound (the retained
     * {@code _json_table_shape} authority); {@code array} fields decode
     * element-wise; class fields recurse into the nested walk with an
     * identity check. Any failure throws {@link JsonFromFailure}
     * (language null).
     */
    private static Value decodeRaw(
            SemanticOp op, RuntimeDescriptor descriptor, Value raw,
            Map<ClassId, ClassLayout> layouts, NestedClassFactory nestedFactory,
            BodyRunner bodyRunner, int depth) {
        if (depth > JSON_MAX_DEPTH) {
            throw new JsonFromFailure("walk depth exceeded " + JSON_MAX_DEPTH
                + " (the pinned retained bound)");
        }
        return switch (descriptor) {
            case RuntimeDescriptor.Null ignored -> {
                if (!(raw instanceof Value.Null)) {
                    throw new JsonFromFailure("expected null, got " + raw.actualKind());
                }
                yield Value.Null.INSTANCE;
            }
            case RuntimeDescriptor.Boolean ignored -> {
                if (!(raw instanceof Value.Bool)) {
                    throw new JsonFromFailure(
                        "expected boolean, got " + raw.actualKind());
                }
                yield raw;
            }
            case RuntimeDescriptor.Int ignored -> {
                // Int fields accept only Int carriers from the parse's
                // signed32 lexical mapping — out-of-range, fractional,
                // or Number carriers fail (the retained pins).
                if (!(raw instanceof Value.Int)) {
                    throw new JsonFromFailure("expected int, got " + raw.actualKind()
                        + " (an int field accepts only signed32 integer lexical "
                        + "carriers)");
                }
                yield raw;
            }
            case RuntimeDescriptor.Number ignored -> {
                if (raw instanceof Value.Number) {
                    yield raw;
                }
                if (raw instanceof Value.Int intValue) {
                    // An integer lexical carrier converts exactly.
                    yield new Value.Number((double) intValue.value());
                }
                throw new JsonFromFailure("expected number, got " + raw.actualKind());
            }
            case RuntimeDescriptor.String ignored -> {
                if (!(raw instanceof Value.String)) {
                    throw new JsonFromFailure(
                        "expected string, got " + raw.actualKind());
                }
                yield raw;
            }
            case RuntimeDescriptor.Table ignored -> {
                if (raw instanceof Value.Table tableValue) {
                    boundParsedTableContents(op, tableValue, depth);
                    yield tableValue;
                }
                // The empty-array collapse: [] decodes as an empty table
                // (the retained pins; a non-empty array-shaped value
                // fails).
                if (raw instanceof Value.Array empty && empty.array().size() == 0) {
                    yield emptyTable();
                }
                throw new JsonFromFailure("expected table, got " + raw.actualKind());
            }
            case RuntimeDescriptor.Array arrayDescriptor -> {
                if (!(raw instanceof Value.Array elements)) {
                    throw new JsonFromFailure(
                        "expected array, got " + raw.actualKind());
                }
                List<Value> decoded = new ArrayList<>(elements.array().size());
                for (Value element : elements.array().elements()) {
                    requireJsonShape(op, element);
                    decoded.add(decodeRaw(op, arrayDescriptor.element(), element,
                        layouts, nestedFactory, bodyRunner, depth + 1));
                }
                yield new Value.Array(SemanticArray.of(decoded));
            }
            case RuntimeDescriptor.Nullable nullable -> {
                if (raw instanceof Value.Null) {
                    yield Value.Null.INSTANCE;
                }
                yield decodeRaw(op, nullable.inner(), raw, layouts, nestedFactory,
                    bodyRunner, depth);
            }
            case RuntimeDescriptor.Class classDescriptor -> {
                if (raw instanceof Value.Null) {
                    throw new JsonFromFailure("expected "
                        + classDescriptor.canonicalSpecText() + ", got null (a JSON "
                        + "null on a non-nullable field fails)");
                }
                if (raw instanceof Value.Table) {
                    yield decodeNestedClass(op, classDescriptor.classId(),
                        (Value.Table) raw, layouts, nestedFactory, bodyRunner,
                        depth + 1);
                }
                if (raw instanceof Value.Array empty && empty.array().size() == 0) {
                    // The {}/[] collapse of the nested walk's own
                    // top-level gate: [] decodes as the nested defaulted
                    // instance.
                    yield decodeNestedClass(op, classDescriptor.classId(),
                        (Value.Table) emptyTable(), layouts, nestedFactory, bodyRunner,
                        depth + 1);
                }
                throw new JsonFromFailure("expected "
                    + classDescriptor.canonicalSpecText() + ", got " + raw.actualKind());
            }
            case RuntimeDescriptor.Bytes ignored -> throw new Defect(
                "a @jsonable field never carries a bytes descriptor (the checker's "
                    + "E4007 allowlist) — a bytes-typed JSON field is a producer "
                    + "defect, never executed");
            case RuntimeDescriptor.Func ignored -> throw new Defect(
                "a @jsonable field never carries a function descriptor (the checker's "
                    + "E4007 allowlist) — a function-typed JSON field is a producer "
                    + "defect, never executed");
        };
    }

    /**
     * The declaration-order serialization walk of one
     * {@code JSON_TO_CLASS} execution (K-D10): the root identity check,
     * the per-field declaration-order encoding with the pinned
     * fieldPath convention, the path-local cycle seen-set over entered
     * class instances, and the {@link #JSON_MAX_DEPTH} bound. Returns
     * the deterministic RFC-8259 text or throws {@link JsonToFailure}.
     */
    private static String encodeToJson(
            SemanticOp op, ClassLayout layout, Value value,
            Map<ClassId, ClassLayout> layouts, JsonStringifier stringifier,
            Set<Object> entered, int depth, String fieldPath) {
        if (depth > JSON_MAX_DEPTH) {
            throw new JsonToFailure(fieldPath, actualTokenOf(value));
        }
        // The root identity check (K-D10 step 1): the value must be an
        // instance of exactly layout.classId — a wrong identity fails
        // with actual class:<other>, any other kind with its own token.
        if (!(value instanceof Value.Class instance)) {
            throw new JsonToFailure(fieldPath, actualTokenOf(value));
        }
        if (!instance.classId().equals(layout.classId())) {
            throw new JsonToFailure(fieldPath, actualTokenOf(value));
        }
        if (instance.fields().size() != layout.fields().size()) {
            throw new Defect("JSON_TO_CLASS " + op.opId() + " root instance of "
                + layout.classId() + " carries " + instance.fields().size()
                + " field states for a layout of " + layout.fields().size()
                + " fields: the pinned instance shape matches its layout's declaration "
                + "order — a count mismatch is a producer defect, never executed");
        }
        // The path-local cycle check over entered class instances.
        if (!entered.add(instance)) {
            throw new JsonToFailure(fieldPath, actualTokenOf(instance));
        }
        try {
            StringBuilder out = new StringBuilder();
            out.append('{');
            boolean first = true;
            for (int i = 0; i < layout.fields().size(); i++) {
                ClassLayout.FieldLayout field = layout.fields().get(i);
                FieldState state = instance.fields().get(i);
                if (state instanceof FieldState.Missing) {
                    // A missing required field fails (the "missing
                    // required value" arm); an omitted optional field is
                    // skipped.
                    if (field.required()) {
                        throw new JsonToFailure(fieldPathOf(fieldPath, field.name()),
                            ActualKind.canonicalToken(ActualKind.MISSING, null));
                    }
                    continue;
                }
                Value fieldValue = ((FieldState.Present) state).value();
                String fieldPosition = fieldPathOf(fieldPath, field.name());
                // Fields of the current instance encode at the current
                // depth (only nested class/array containers consume a
                // depth level, the K-D10 walk bound).
                String encoded = encodeField(op, field.descriptor(), fieldValue,
                    fieldPosition, layouts, stringifier, entered, depth);
                if (!first) {
                    out.append(',');
                }
                first = false;
                out.append(jsonStringOf(field.name()));
                out.append(':');
                out.append(encoded);
            }
            out.append('}');
            return out.toString();
        } finally {
            entered.remove(instance);
        }
    }

    /**
     * Encodes one present field value per its declared descriptor
     * (K-D10 step 2): primitives encode per JSON kind (nonfinite
     * numbers fail); present null serializes as JSON null on a nullable
     * field and fails on a non-nullable one; class fields recurse with
     * a nested identity check; array fields encode element-wise;
     * {@code table} fields run the seam's finite-acyclic JSON-shape
     * walk, bounded by the walk's {@link #JSON_MAX_DEPTH} over the
     * table subtree before the seam runs (the retained
     * {@code _json_table_shape} authority); every leaf/table text comes
     * from the {@link JsonStringifier}
     * seam (the E8 stringify algorithm — RFC-8259 escaping, shortest
     * round-trippable decimals, first-insertion and index order).
     */
    private static String encodeField(
            SemanticOp op, RuntimeDescriptor descriptor, Value value, String fieldPath,
            Map<ClassId, ClassLayout> layouts, JsonStringifier stringifier,
            Set<Object> entered, int depth) {
        if (depth > JSON_MAX_DEPTH) {
            throw new JsonToFailure(fieldPath, actualTokenOf(value));
        }
        return switch (descriptor) {
            case RuntimeDescriptor.Null ignored -> {
                if (!(value instanceof Value.Null)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.Boolean ignored -> {
                if (!(value instanceof Value.Bool)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.Int ignored -> {
                if (!(value instanceof Value.Int)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.Number ignored -> {
                if (!(value instanceof Value.Number) && !(value instanceof Value.Int)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                // Nonfinite numbers fail inside the seam (the E8 row).
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.String ignored -> {
                if (!(value instanceof Value.String string)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                if (!(string.scalar() instanceof UnicodeScalars.Valid)) {
                    throw new JsonToFailure(fieldPath,
                        ActualKind.canonicalToken(ActualKind.INVALID_UNICODE, null));
                }
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.Table ignored -> {
                if (!(value instanceof Value.Table)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                boundTableContentsDepth(op, value, fieldPath, depth,
                    java.util.Collections.newSetFromMap(
                        new java.util.IdentityHashMap<>()));
                yield seamText(op, stringifier, value, fieldPath);
            }
            case RuntimeDescriptor.Array arrayDescriptor -> {
                if (!(value instanceof Value.Array elements)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                yield encodeArrayElements(op, arrayDescriptor.element(), elements,
                    fieldPath, layouts, stringifier, entered, depth);
            }
            case RuntimeDescriptor.Nullable nullable -> {
                if (value instanceof Value.Null) {
                    yield seamText(op, stringifier, value, fieldPath);
                }
                yield encodeField(op, nullable.inner(), value, fieldPath, layouts,
                    stringifier, entered, depth);
            }
            case RuntimeDescriptor.Class classDescriptor -> {
                if (value instanceof Value.Null) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                if (!(value instanceof Value.Class nested)) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                if (!nested.classId().equals(classDescriptor.classId())) {
                    // The nested identity check: a wrong identity fails
                    // with actual class:<other> at the nested position.
                    throw new JsonToFailure(fieldPath, actualTokenOf(nested));
                }
                ClassLayout nestedLayout = layouts.get(classDescriptor.classId());
                if (nestedLayout == null) {
                    throw new Defect("JSON_TO_CLASS " + op.opId() + " nested class "
                        + classDescriptor.classId() + " does not resolve in the "
                        + "layout-resolution context — an unresolvable nested layout is "
                        + "a producer defect, never executed");
                }
                yield encodeToJson(op, nestedLayout, nested, layouts, stringifier,
                    entered, depth + 1, fieldPath);
            }
            case RuntimeDescriptor.Bytes ignored -> throw new Defect(
                "a @jsonable field never carries a bytes descriptor (the checker's "
                    + "E4007 allowlist) — a bytes-typed JSON field is a producer "
                    + "defect, never executed");
            case RuntimeDescriptor.Func ignored -> throw new Defect(
                "a @jsonable field never carries a function descriptor (the checker's "
                    + "E4007 allowlist) — a function-typed JSON field is a producer "
                    + "defect, never executed");
        };
    }

    /**
     * Encodes one array value element-wise (K-D10 step 2): each element
     * path appends the 0-based {@code [i]} segment; class-typed
     * elements recurse with a nested identity check, array elements
     * recurse the array walk, and every other element's text comes from
     * the {@link JsonStringifier} seam.
     */
    private static String encodeArrayElements(
            SemanticOp op, RuntimeDescriptor elementDescriptor, Value.Array elements,
            String fieldPath, Map<ClassId, ClassLayout> layouts,
            JsonStringifier stringifier, Set<Object> entered, int depth) {
        StringBuilder out = new StringBuilder();
        out.append('[');
        for (int i = 0; i < elements.array().size(); i++) {
            if (i > 0) {
                out.append(',');
            }
            String elementPath = fieldPath + "[" + i + "]";
            out.append(encodeField(op, elementDescriptor,
                elements.array().elementAt(i), elementPath, layouts, stringifier,
                entered, depth + 1));
        }
        out.append(']');
        return out.toString();
    }

    /**
     * Encodes one leaf/table value through the stringify seam and
     * converts the seam's failure into the walk's own
     * {@link JsonToFailure} (the seam reports the full pinned-convention
     * path prefixed with the caller's field path).
     */
    private static String seamText(SemanticOp op, JsonStringifier stringifier,
                                   Value value, String fieldPath) {
        JsonStringify rendered = stringifier.stringify(value, fieldPath);
        return switch (rendered) {
            case JsonStringify.Success success -> success.text().carrier();
            case JsonStringify.Failure failure ->
                throw new JsonToFailure(failure.fieldPath(), failure.actual());
        };
    }

    /** The canonical actual-kind token of one value (class values render {@code class:<ClassId>}). */
    private static String actualTokenOf(Value value) {
        if (value instanceof Value.Class instance) {
            return ActualKind.canonicalToken(ActualKind.CLASS, instance.classId().text());
        }
        return ActualKind.canonicalToken(value.actualKind(), null);
    }

    /**
     * The internal descriptor check of the two JSON walks (K-D8 step 7 /
     * K-D10's per-kind encoding admission): {@code value} must conform
     * to {@code descriptor} — null/bool/int/number/string(valid)/table/
     * array(recursive)/nullable/class (nominal identity plus the
     * layout's declaration-order field count) — fail closed on a
     * function descriptor (the checker's E4007 allowlist excludes
     * function-typed fields). A mismatch throws {@link JsonFromFailure}
     * (the {@code JSON_FROM_NULL} projection).
     */
    private static void requireDescriptorConforming(SemanticOp op,
                                                    RuntimeDescriptor descriptor,
                                                    Value value,
                                                    Map<ClassId, ClassLayout> layouts) {
        switch (descriptor) {
            case RuntimeDescriptor.Null ignored -> {
                if (value instanceof Value.Null) {
                    return;
                }
            }
            case RuntimeDescriptor.Boolean ignored -> {
                if (value instanceof Value.Bool) {
                    return;
                }
            }
            case RuntimeDescriptor.Int ignored -> {
                if (value instanceof Value.Int) {
                    return;
                }
            }
            case RuntimeDescriptor.Number ignored -> {
                if (value instanceof Value.Number || value instanceof Value.Int) {
                    return;
                }
            }
            case RuntimeDescriptor.String ignored -> {
                if (value instanceof Value.String string
                        && string.scalar() instanceof UnicodeScalars.Valid) {
                    return;
                }
            }
            case RuntimeDescriptor.Table ignored -> {
                if (value instanceof Value.Table) {
                    return;
                }
            }
            case RuntimeDescriptor.Array arrayDescriptor -> {
                if (value instanceof Value.Array elements) {
                    for (Value element : elements.array().elements()) {
                        requireDescriptorConforming(op, arrayDescriptor.element(),
                            element, layouts);
                    }
                    return;
                }
            }
            case RuntimeDescriptor.Nullable nullable -> {
                if (value instanceof Value.Null) {
                    return;
                }
                requireDescriptorConforming(op, nullable.inner(), value, layouts);
                return;
            }
            case RuntimeDescriptor.Class classDescriptor -> {
                if (value instanceof Value.Class instance) {
                    if (!instance.classId().equals(classDescriptor.classId())) {
                        break;
                    }
                    ClassLayout nested = layouts.get(classDescriptor.classId());
                    if (nested != null
                            && nested.fields().size() != instance.fields().size()) {
                        break;
                    }
                    return;
                }
            }
            case RuntimeDescriptor.Bytes ignored -> throw new Defect(
                "a @jsonable field never carries a bytes descriptor (the checker's "
                    + "E4007 allowlist) — a bytes-typed JSON field is a producer "
                    + "defect, never executed");
            case RuntimeDescriptor.Func ignored -> throw new Defect(
                "a @jsonable field never carries a function descriptor (the checker's "
                    + "E4007 allowlist) — a function-typed JSON field is a producer "
                    + "defect, never executed");
        }
        throw new JsonFromFailure("value for " + descriptor.canonicalSpecText() + " is "
            + actualTokenOf(value));
    }

    /**
     * Requires one parsed-JSON value to sit in the closed JSON-shaped
     * set of the seam's contract (null/bool/int/number/valid string/
     * table/array). A value outside the set is a seam-contract
     * violation and fails closed as a producer {@link Defect}, never as
     * a walk failure.
     */
    private static void requireJsonShape(SemanticOp op, Value raw) {
        switch (raw) {
            case Value.Null ignored -> {
            }
            case Value.Bool ignored -> {
            }
            case Value.Int ignored -> {
            }
            case Value.Number ignored -> {
            }
            case Value.Table ignored -> {
            }
            case Value.Array ignored -> {
            }
            case Value.String string -> {
                if (!(string.scalar() instanceof UnicodeScalars.Valid)) {
                    throw new Defect("JSON_FROM_CLASS " + op.opId() + ": the JSON "
                        + "algorithm seam produced an invalid-scalar string carrier: "
                        + "the closed parsed-JSON value model carries valid scalar "
                        + "strings only — a seam-contract violation is a producer "
                        + "defect, never executed");
                }
            }
            default -> throw new Defect("JSON_FROM_CLASS " + op.opId() + ": the JSON "
                + "algorithm seam produced a non-JSON-shaped value "
                + raw.actualKind() + ": the closed parsed-JSON value model carries "
                + "null/bool/int/number/string/object/array only — a seam-contract "
                + "violation is a producer defect, never executed");
        }
    }

    /**
     * The depth-aware shape walk over one table field's parsed subtree
     * (K-D8's bounded walk over table-field contents — the retained
     * {@code _json_table_shape} authority,
     * {@code deal/runtime.lua:1615-1659}): every nested table/array
     * container counts one depth level from the walk's current depth,
     * and a container past {@link #JSON_MAX_DEPTH} fails the walk
     * (language null). The parsed model is always JSON-shaped, so a
     * non-JSON-shaped nested value fails closed as a producer
     * {@link Defect}, never as a walk failure.
     */
    private static void boundParsedTableContents(SemanticOp op, Value value, int depth) {
        switch (value) {
            case Value.Table table -> {
                if (depth > JSON_MAX_DEPTH) {
                    throw new JsonFromFailure("a table field's contents exceed the "
                        + "pinned walk depth bound " + JSON_MAX_DEPTH
                        + " (the retained _json_table_shape authority)");
                }
                for (String key : table.table().keys()) {
                    SemanticTable.Lookup<Value> lookup = table.table().get(key);
                    if (!(lookup instanceof SemanticTable.Lookup.Present<Value> present)) {
                        throw new Defect("JSON_FROM_CLASS " + op.opId() + ": a parsed "
                            + "table key '" + key + "' reads Missing: the closed parsed "
                            + "model keeps every listed key present — a seam-contract "
                            + "violation is a producer defect, never executed");
                    }
                    requireJsonShape(op, present.value());
                    boundParsedTableContents(op, present.value(), depth + 1);
                }
            }
            case Value.Array array -> {
                if (depth > JSON_MAX_DEPTH) {
                    throw new JsonFromFailure("a table field's contents exceed the "
                        + "pinned walk depth bound " + JSON_MAX_DEPTH
                        + " (the retained _json_table_shape authority)");
                }
                for (Value element : array.array().elements()) {
                    requireJsonShape(op, element);
                    boundParsedTableContents(op, element, depth + 1);
                }
            }
            default -> {
                // JSON-shaped leaves (validated by requireJsonShape at
                // every recursion site): no depth level consumed.
            }
        }
    }

    /**
     * The depth-aware pre-walk over one table field's subtree (K-D10's
     * bounded walk over table-field contents — the retained
     * {@code _json_table_shape} authority,
     * {@code deal/runtime.lua:1615-1659,2145-2180}): every nested
     * table/array container counts one depth level from the walk's
     * current depth, and a container past {@link #JSON_MAX_DEPTH} fails
     * {@code JSON_TO_ERROR} at its pinned path with its canonical
     * actual-kind token. Unsupported carriers, nonfinite leaves, and
     * cycles stay the seam's pinned failures: the pre-walk bounds only
     * depth (a path-local re-entry stops the recursion and the seam
     * reports the pinned cycle token), so the seam's own recursion
     * never exceeds the bound — no infrastructure stack overflow can
     * escape a DEAL-visible failure.
     */
    private static void boundTableContentsDepth(SemanticOp op, Value value,
                                                String fieldPath, int depth,
                                                Set<Object> entered) {
        switch (value) {
            case Value.Table table -> {
                if (depth > JSON_MAX_DEPTH) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                if (!entered.add(table.table())) {
                    return; // path-local re-entry: the seam reports the pinned cycle token
                }
                try {
                    for (String key : table.table().keys()) {
                        SemanticTable.Lookup<Value> lookup = table.table().get(key);
                        if (!(lookup instanceof SemanticTable.Lookup.Present<Value> present)) {
                            throw new Defect("JSON_TO_CLASS " + op.opId() + ": a table "
                                + "key '" + key + "' reads Missing: a table's listed key "
                                + "is always present — a wrong table view is a producer "
                                + "defect, never executed");
                        }
                        boundTableContentsDepth(op, present.value(),
                            fieldPath + "." + key, depth + 1, entered);
                    }
                } finally {
                    entered.remove(table.table());
                }
            }
            case Value.Array array -> {
                if (depth > JSON_MAX_DEPTH) {
                    throw new JsonToFailure(fieldPath, actualTokenOf(value));
                }
                if (!entered.add(array.array())) {
                    return; // path-local re-entry: the seam reports the pinned cycle token
                }
                try {
                    for (int i = 0; i < array.array().size(); i++) {
                        boundTableContentsDepth(op, array.array().elementAt(i),
                            fieldPath + "[" + i + "]", depth + 1, entered);
                    }
                } finally {
                    entered.remove(array.array());
                }
            }
            default -> {
                // Leaves (unsupported carriers included): the seam's
                // pinned failures, never this walk's depth concern.
            }
        }
    }

    /**
     * The pinned fieldPath append of the two JSON walks (K-D10): the
     * root is {@code ""}, a declared field {@code f} appends
     * {@code "f"} (the first segment) or {@code ".f"}, a nested class
     * field under {@code f} becomes {@code "f.g"}, an array element
     * appends {@code "[i]"} (0-based), and a table object key appends
     * {@code ".k"} (the seam's convention inside table fields).
     */
    private static String fieldPathOf(String parent, String fieldName) {
        return parent.isEmpty() ? fieldName : parent + "." + fieldName;
    }

    /** A fresh empty table value (the {@code {}} document shape). */
    private static Value.Table emptyTable() {
        return new Value.Table(new SemanticTable<>());
    }

    /** Tags one decoded instance in declaration order (K-D8 step 8). */
    private static Value taggedInstance(ClassLayout layout,
                                        LinkedHashMap<String, Value> instanceFields) {
        List<FieldState> states = new ArrayList<>(layout.fields().size());
        for (ClassLayout.FieldLayout field : layout.fields()) {
            Value value = instanceFields.get(field.name());
            states.add(value == null ? FieldState.Missing.INSTANCE
                : new FieldState.Present(value));
        }
        return new Value.Class(layout.classId(), List.copyOf(states));
    }

    /** The RFC-8259 text of one declared field name (an identifier scalar sequence). */
    private static String jsonStringOf(String name) {
        // Field names are checker-pinned identifiers: quote, backslash,
        // and control scalars cannot appear, so the exact RFC-8259 text
        // is the quoted name itself.
        return "\"" + name + "\"";
    }

    // =========================================================================
    // Shared fail-closed helpers
    // =========================================================================

    /**
     * Requires the pinned op shape: exactly {@code kind} and exactly
     * {@code policy}. The executor interprets validated shapes only — a
     * different kind is not the op this method executes, and a
     * non-pinned policy would silently change the contract, so both fail
     * closed as producer defects (never executed, never projected).
     */
    /**
     * K-D4 step 1: the payload's provided-field prior steps resolve in
     * literal order. With {@code declaredLayout} non-null every provided
     * name must be a declared field (the builtin/host fail-closed rule);
     * with {@code declaredLayout} null the undeclared-name policy stays
     * with the caller's extra-key gate.
     */
    private static void resolveProvidedFields(
            SemanticOp op, KindPayload.ClassNewPayload payload,
            Map<ValueId, Value> priorValues, ClassLayout declaredLayout,
            LinkedHashMap<String, Value> providedValues,
            LinkedHashMap<String, ValueId> providedValueIds) {
        for (KindPayload.ProvidedField field : payload.providedFields()) {
            Value value = resolve(priorValues, field.valueOpId());
            if (value instanceof Value.Missing) {
                throw new Defect("CLASS_NEW " + op.opId() + " provided field '"
                    + field.name() + "' (" + field.valueOpId() + ") resolves to the"
                    + " internal Missing view: a provided field always carries a"
                    + " present value (language null is the explicit Null variant) — a"
                    + " wrong-kind value is a producer defect, never executed");
            }
            if (declaredLayout != null && fieldOf(declaredLayout, field.name()) == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " provides field '"
                    + field.name() + "' which is not a declared field of "
                    + payload.classId() + ": the checker's E4002 rejects an extra"
                    + " literal field before lowering — a producer defect, never"
                    + " executed");
            }
            providedValues.put(field.name(), value);
            providedValueIds.put(field.name(), field.valueOpId());
        }
    }

    /**
     * K-D4 step 2: the payload's {@code CLASS_DEFAULT} children run in
     * declaration order, skipping every child whose field the triggering
     * context records as provided (a provided field's default never
     * runs). The default values fill {@code values} and the applied child
     * ops are returned by field; {@code optionalDefaultReason} carries
     * the caller's pinned optional-field rule text.
     */
    private static LinkedHashMap<String, SemanticOp> applyClassDefaults(
            SemanticOp op, ClassId classId, List<OpId> defaultOpIds,
            Map<OpId, SemanticOp> defaultOps, ClassLayout layout,
            Set<String> skipFields, String optionalDefaultReason,
            BodyRunner bodyRunner, LinkedHashMap<String, Value> values) {
        LinkedHashMap<String, SemanticOp> opsByField = new LinkedHashMap<>();
        for (OpId defaultOpId : defaultOpIds) {
            SemanticOp defaultOp = requireDefaultChild(defaultOps, defaultOpId,
                classId, op);
            KindPayload.ClassDefaultPayload defaultPayload =
                (KindPayload.ClassDefaultPayload) defaultOp.payload();
            if (skipFields.contains(defaultPayload.field())) {
                // The skip-provided rule: a provided field's default
                // block is never executed by this construction attempt.
                continue;
            }
            ClassLayout.FieldLayout fieldLayout = fieldOf(layout, defaultPayload.field());
            if (fieldLayout == null) {
                throw new Defect(op.kind() + " " + op.opId() + " names CLASS_DEFAULT child "
                    + defaultOpId + " for field '" + defaultPayload.field() + "' which is "
                    + "not a declared field of " + classId + ": a default child "
                    + "of an undeclared field is a producer defect, never executed");
            }
            if (!fieldLayout.required()) {
                throw new Defect(op.kind() + " " + op.opId() + " names CLASS_DEFAULT child "
                    + defaultOpId + " for optional field '" + defaultPayload.field()
                    + "': " + optionalDefaultReason);
            }
            if (values.containsKey(defaultPayload.field())) {
                throw new Defect(op.kind() + " " + op.opId() + " names two CLASS_DEFAULT "
                    + "children for field '" + defaultPayload.field() + "': the pinned "
                    + "shape carries exactly one default child per defaulted field — a "
                    + "duplicate is a producer defect, never executed");
            }
            Outcome<Value> produced = executeClassDefault(defaultOp, bodyRunner);
            if (!(produced instanceof Outcome.Success<Value> success)) {
                // executeClassDefault cannot fail by itself: a default-block
                // failure propagates as the callback's own throw.
                throw new Defect(op.kind() + " " + op.opId() + " CLASS_DEFAULT child "
                    + defaultOpId + " returned a failure terminal from the default "
                    + "execution: the default op's policy is NO_DEAL_FAILURE and only "
                    + "already-started child/operand failures may propagate — a "
                    + "producer defect, never executed");
            }
            values.put(defaultPayload.field(), success.value());
            opsByField.put(defaultPayload.field(), defaultOp);
        }
        return opsByField;
    }

    /**
     * K-D4 step 3: the extra-key E8007 projection in provided-source order
     * — the first provided name the layout does not declare — or
     * {@code null} when every provided name is declared.
     */
    private static Outcome.Failure<Value> undeclaredProvidedFieldFailure(
            SemanticOp op, KindPayload.ClassNewPayload payload, ClassLayout layout) {
        for (KindPayload.ProvidedField field : payload.providedFields()) {
            if (fieldOf(layout, field.name()) == null) {
                BoundaryFailure failure = BoundaryFailure.fromRow(
                    FailureContractRegistry.row(FailurePolicyId.CLASS_CONSTRUCTION), 0,
                    null, null,
                    metadataOf("field", field.name(), "classId", payload.classId().text()),
                    null);
                return new Outcome.Failure<Value>(new OpFailure(failure, op.origin()));
            }
        }
        return null;
    }

    /**
     * The pinned field-boundary coverage (K-D4 step 5 shape): exactly one
     * entry per present field — provided ({@code CLASS_LITERAL_FIELD}) or
     * omitted required-present defaulted ({@code CLASS_DEFAULT_FIELD}) —
     * in declaration order. A count, order, or kind deviation is a
     * producer defect.
     */
    private static void requireBoundaryShape(
            SemanticOp op, KindPayload.ClassNewPayload payload, ClassLayout layout,
            Map<String, Value> providedValues,
            List<KindPayload.FieldBoundary> boundaries,
            java.util.function.Predicate<String> hasDefault) {
        List<java.lang.String> expectedBoundaryFields = new ArrayList<>();
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            if (providedValues.containsKey(fieldLayout.name())
                    || hasDefault.test(fieldLayout.name())) {
                expectedBoundaryFields.add(fieldLayout.name());
            }
        }
        if (boundaries.size() != expectedBoundaryFields.size()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries " + boundaries.size()
                + " field-boundary entries for " + expectedBoundaryFields.size()
                + " present fields: the pinned shape carries exactly one boundary per "
                + "provided field and per omitted required-present defaulted field in "
                + "declaration order — a child-count mismatch is a producer defect, "
                + "never executed");
        }
        for (int i = 0; i < boundaries.size(); i++) {
            KindPayload.FieldBoundary entry = boundaries.get(i);
            java.lang.String expectedField = expectedBoundaryFields.get(i);
            if (!entry.field().equals(expectedField)) {
                throw new Defect("CLASS_NEW " + op.opId() + " field-boundary entry " + i
                    + " names field '" + entry.field() + "': the pinned declaration order "
                    + "names '" + expectedField + "' — a field-boundary order mismatch "
                    + "is a producer defect, never executed");
            }
            BoundaryKind expectedKind = providedValues.containsKey(entry.field())
                ? BoundaryKind.CLASS_LITERAL_FIELD : BoundaryKind.CLASS_DEFAULT_FIELD;
            if (entry.kind() != expectedKind) {
                throw new Defect("CLASS_NEW " + op.opId() + " field-boundary entry for '"
                    + entry.field() + "' carries kind " + entry.kind() + ": the pinned "
                    + "kind is " + expectedKind + " (CLASS_LITERAL_FIELD for provided "
                    + "values, CLASS_DEFAULT_FIELD for defaulted values) — a kind "
                    + "mismatch is a producer defect, never executed");
            }
        }
    }

    /** The input-value wiring of one {@code CLASS_DEFAULT_FIELD} entry. */
    @FunctionalInterface
    private interface DefaultFieldInputResolver {

        Value resolve(SemanticOp child, KindPayload.FieldBoundary entry,
                      KindPayload.BoundaryPayload boundaryPayload);
    }

    /**
     * K-D4 step 5: the field boundaries run in declaration order through
     * the {@link BoundaryCheckRunner} seam — the shared child-shape
     * checks and the literal-provided wiring live here, the
     * default-field wiring is the {@code defaultInput} seam. On the first
     * failing child the helper returns the op failure; on success
     * {@code checkedValues} carries the boundary-published values by
     * field.
     */
    private static OpFailure applyFieldBoundaries(
            SemanticOp op, KindPayload.ClassNewPayload payload, ClassLayout layout,
            List<KindPayload.FieldBoundary> boundaries,
            Map<String, Value> providedValues, Map<String, ValueId> providedValueIds,
            Map<OpId, SemanticOp> boundaryOps, BoundaryCheckRunner checkRunner,
            LinkedHashMap<String, Value> checkedValues,
            DefaultFieldInputResolver defaultInput) {
        for (KindPayload.FieldBoundary entry : boundaries) {
            ClassLayout.FieldLayout fieldLayout = fieldOf(layout, entry.field());
            if (fieldLayout == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " field-boundary entry names "
                    + "field '" + entry.field() + "' which is not a declared field of "
                    + payload.classId() + ": a boundary of an undeclared field is a "
                    + "producer defect, never executed");
            }
            SemanticOp child = requireBoundaryChild(boundaryOps, entry.boundaryOpId(), op,
                entry.kind());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) child.payload();
            if (!boundaryPayload.descriptor().equals(fieldLayout.descriptor())) {
                throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                    + child.opId() + " carries descriptor "
                    + boundaryPayload.descriptor().canonicalSpecText()
                    + ": the pinned child descriptor is the field's declared descriptor "
                    + fieldLayout.descriptor().canonicalSpecText() + " — a mismatch is a "
                    + "producer defect, never executed");
            }
            requireDescriptorKindPolicy(child, boundaryPayload.descriptor());
            Value input;
            if (entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD) {
                Value provided = providedValues.get(entry.field());
                ValueId providedId = providedValueIds.get(entry.field());
                if (provided == null || providedId == null) {
                    throw new Defect("CLASS_NEW " + op.opId() + " carries a "
                        + "CLASS_LITERAL_FIELD boundary for field '" + entry.field()
                        + "' without a provided value: the pinned kind names provided "
                        + "values only — a producer defect, never executed");
                }
                if (!boundaryPayload.input().equals(providedId)) {
                    throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                        + child.opId() + " carries input " + boundaryPayload.input()
                        + ": the pinned CLASS_LITERAL_FIELD input is the field's "
                        + "provided value op " + providedId + " (K-D4 input wiring) — a "
                        + "mismatch is a producer defect, never executed");
                }
                input = provided;
            } else {
                input = defaultInput.resolve(child, entry, boundaryPayload);
            }
            BoundaryResult result = checkRunner.run(boundaryPayload, input);
            if (result instanceof BoundaryResult.Pass pass) {
                checkedValues.put(entry.field(), pass.value());
                continue;
            }
            // The first failing child fails the op: no instance, no tag,
            // and the later children never run.
            BoundaryResult.Fail fail = (BoundaryResult.Fail) result;
            return new OpFailure(fail.failure(), op.origin());
        }
        return null;
    }

    /**
     * The pinned literal-field boundary coverage of the builtin/host
     * construction surfaces: exactly one {@code CLASS_LITERAL_FIELD}
     * entry per provided field in provided order, each running through
     * the delegate. The {@code shapeLabel} names the pinned shape in the
     * fail-closed messages. Returns the first failing boundary's op
     * failure, or {@code null} on success with {@code checkedValues}
     * filled.
     */
    private static OpFailure applyLiteralFieldBoundaries(
            SemanticOp op, KindPayload.ClassNewPayload payload, ClassLayout layout,
            Map<String, Value> providedValues, Map<String, ValueId> providedValueIds,
            List<KindPayload.FieldBoundary> boundaries,
            Map<OpId, SemanticOp> boundaryOps, BoundaryCheckRunner checkRunner,
            LinkedHashMap<String, Value> checkedValues, String shapeLabel) {
        if (boundaries.size() != providedValues.size()) {
            throw new Defect("CLASS_NEW " + op.opId() + " carries "
                + boundaries.size() + " field-boundary entries for "
                + providedValues.size() + " provided fields: the pinned " + shapeLabel
                + " carries exactly one CLASS_LITERAL_FIELD boundary per provided field"
                + " — a child-count mismatch is a producer defect, never executed");
        }
        for (KindPayload.FieldBoundary entry : boundaries) {
            Value provided = providedValues.get(entry.field());
            ValueId providedId = providedValueIds.get(entry.field());
            if (entry.kind() != BoundaryKind.CLASS_LITERAL_FIELD || provided == null
                    || providedId == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " carries boundary entry"
                    + " for field '" + entry.field() + "' of kind " + entry.kind()
                    + ": the pinned " + shapeLabel
                    + " carries exactly one CLASS_LITERAL_FIELD boundary per provided"
                    + " field — a shape deviation is a producer defect, never executed");
            }
            ClassLayout.FieldLayout fieldLayout = fieldOf(layout, entry.field());
            if (fieldLayout == null) {
                throw new Defect("CLASS_NEW " + op.opId() + " field-boundary entry"
                    + " names field '" + entry.field() + "' which is not a declared"
                    + " field of " + payload.classId() + " — a producer defect, never"
                    + " executed");
            }
            SemanticOp child = requireBoundaryChild(boundaryOps, entry.boundaryOpId(), op,
                entry.kind());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) child.payload();
            if (!boundaryPayload.descriptor().equals(fieldLayout.descriptor())) {
                throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                    + child.opId() + " carries descriptor "
                    + boundaryPayload.descriptor().canonicalSpecText()
                    + ": the pinned child descriptor is the field's declared descriptor "
                    + fieldLayout.descriptor().canonicalSpecText() + " — a mismatch is a "
                    + "producer defect, never executed");
            }
            requireDescriptorKindPolicy(child, boundaryPayload.descriptor());
            if (!boundaryPayload.input().equals(providedId)) {
                throw new Defect("CLASS_NEW " + op.opId() + " field boundary "
                    + child.opId() + " carries input " + boundaryPayload.input()
                    + ": the pinned CLASS_LITERAL_FIELD input is the field's provided"
                    + " value op " + providedId + " (K-D4 input wiring) — a mismatch"
                    + " is a producer defect, never executed");
            }
            BoundaryResult result = checkRunner.run(boundaryPayload, provided);
            if (result instanceof BoundaryResult.Pass pass) {
                checkedValues.put(entry.field(), pass.value());
                continue;
            }
            // The first failing child fails the op: no instance, no tag, and
            // the later children never run.
            BoundaryResult.Fail fail = (BoundaryResult.Fail) result;
            return new OpFailure(fail.failure(), op.origin());
        }
        return null;
    }

    private static void requireOp(SemanticOp op, SemanticOpKind kind, FailurePolicyId policy) {
        String defect = ExecutorGuards.opShapeDefect(op, kind, policy);
        if (defect != null) {
            throw new Defect(defect);
        }
    }

    /**
     * Resolves one payload-referenced provided-field prior step. Prior
     * steps complete before operation START in the validated machine, so
     * an unresolved reference is a producer defect (fail closed, never a
     * projection and never a silent skip).
     */
    private static Value resolve(Map<ValueId, Value> priorValues, ValueId id) {
        Value value = priorValues.get(id);
        if (value == null) {
            throw new Defect("prior-step value " + id + " is not resolved in the value "
                + "lookup: every payload-referenced provided-field prior step resolves "
                + "before the op's behavior — an unresolved reference is a producer "
                + "defect, never executed");
        }
        return value;
    }

    /**
     * Resolves one named {@code CLASS_DEFAULT} child and requires the
     * pinned shape fail closed: a {@code CLASS_DEFAULT} op carrying
     * {@code NO_DEAL_FAILURE} and the payload's classId. The op is a
     * detached structural op (K-D12: the payload membership records its
     * nesting under the triggering construction, not a static
     * {@code parentOpId}), so no parentage check applies — the
     * {@code classDefaultOpIds} membership is the pinned owner relation.
     */
    private static SemanticOp requireDefaultChild(Map<OpId, SemanticOp> defaultOps,
                                                  OpId childId, ClassId classId,
                                                  SemanticOp owner) {
        SemanticOp child = defaultOps.get(childId);
        if (child == null) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names CLASS_DEFAULT "
                + "child " + childId + " which the default-op lookup does not resolve — a "
                + "producer defect, never executed");
        }
        if (child.kind() != SemanticOpKind.CLASS_DEFAULT) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names default child "
                + child.opId() + " of kind " + child.kind()
                + ": the pinned child kind is CLASS_DEFAULT — a producer defect, never "
                + "executed");
        }
        if (child.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names default child "
                + child.opId() + " carrying failure policy " + child.failurePolicy()
                + ": the pinned CLASS_DEFAULT policy is NO_DEAL_FAILURE — a non-pinned "
                + "policy is a producer defect, never executed");
        }
        KindPayload.ClassDefaultPayload payload =
            (KindPayload.ClassDefaultPayload) child.payload();
        if (!payload.classId().equals(classId)) {
            throw new Defect(owner.kind() + " " + owner.opId() + " names default child "
                + child.opId() + " of class " + payload.classId()
                + ": the pinned default child belongs to the constructed class " + classId
                + " — a classId mismatch is a producer defect, never executed");
        }
        return child;
    }

    /**
     * Resolves one named field-boundary child and requires the
     * validator-pinned shape fail closed: a {@code BOUNDARY} op of the
     * given boundary kind whose origin {@code parentOpId} is the owning
     * {@code CLASS_NEW} op (the K-D4 parentage pin).
     */
    private static SemanticOp requireBoundaryChild(Map<OpId, SemanticOp> boundaryOps,
                                                   OpId childId, SemanticOp owner,
                                                   BoundaryKind pinnedKind) {
        SemanticOp child = boundaryOps.get(childId);
        if (child == null) {
            throw new Defect(ExecutorGuards.missingBoundaryChildDefect(owner, childId));
        }
        requireChildOf(child, owner, pinnedKind);
        return child;
    }

    /** The shared child-shape checks of {@link #requireBoundaryChild}. */
    private static void requireChildOf(SemanticOp child, SemanticOp owner,
                                       BoundaryKind pinnedKind) {
        String defect = ExecutorGuards.childShapeDefect(child, owner, pinnedKind);
        if (defect != null) {
            throw new Defect(defect);
        }
    }

    /**
     * Requires the descriptor-kind rule on one field-boundary child (the
     * pinned policy of the {@code CLASS_LITERAL_FIELD}/
     * {@code CLASS_DEFAULT_FIELD} cells): {@code TYPE_DESCRIPTOR} for
     * non-function descriptors, {@code FUNCTION_SIGNATURE} for function
     * descriptors. A deviation would silently change the contract — fail
     * closed.
     */
    private static void requireDescriptorKindPolicy(SemanticOp child,
                                                    RuntimeDescriptor descriptor) {
        FailurePolicyId pinned = descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
        if (child.failurePolicy() != pinned) {
            throw new Defect(child.kind() + " " + child.opId() + " carries failure policy "
                + child.failurePolicy() + " on descriptor "
                + descriptor.canonicalSpecText() + ": the pinned descriptor-kind-rule "
                + "policy is " + pinned + " — a non-pinned policy is a producer defect, "
                + "never executed");
        }
    }

    /** The layout field of {@code name} in declaration order, or {@code null}. */
    private static ClassLayout.FieldLayout fieldOf(ClassLayout layout, java.lang.String name) {
        for (ClassLayout.FieldLayout field : layout.fields()) {
            if (field.name().equals(name)) {
                return field;
            }
        }
        return null;
    }

    /** A deterministic insertion-ordered metadata map (the row's pinned keys). */
    private static Map<String, String> metadataOf(String key1, String value1,
                                                  String key2, String value2) {
        Map<String, String> metadata = new LinkedHashMap<>();
        metadata.put(key1, value1);
        metadata.put(key2, value2);
        return metadata;
    }
}
