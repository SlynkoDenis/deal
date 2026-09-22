package deal.semantic;

import deal.semantic.ir.ActualKind;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.UnicodeScalars;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The single standard-library algorithm executor of
 * {@code deal.semantic-ir/1} ({@code stdlib-operations-and-time-lock} D4,
 * Contracts §{@code SharedStdlibSemantics} algorithms and §Console
 * effect): the only component that computes the 21 named
 * {@link StdlibFunctionId} operations, as static per-family algorithms
 * over the closed value view ({@link Value} over
 * {@link UnicodeScalars.ScalarString} and {@link SemanticTable})
 * returning a sealed {@link Outcome} ({@code Success(value)} /
 * {@code Failure(StdlibFailure)}). Every DEAL-visible failure delegates
 * to the named {@link FailureContractRegistry} row through
 * {@link BoundaryFailure#fromRow} — the primitive never builds message
 * text ad hoc and consumers never select messages.
 *
 * <p><b>Executor-primitive pattern.</b> Like {@link SharedValueSemantics},
 * {@code ContainerOpsExecutor}, and {@code BoundaryExecutor}, the
 * component is pure, static, deterministic, stateless, and executes no
 * host code. The only non-pure surfaces are the injected
 * {@link ConsoleSink} (D5) and the injected {@link Clock} of
 * {@code TIME_NOW_MILLIS} (K7): the primitive performs no process I/O —
 * the executor supplies the sink and the clock reading, and a sink
 * failure is {@code INFRASTRUCTURE_ONLY} infrastructure failure: not a
 * DEAL error, no DEAL diagnostic, not catchable, and it aborts the run.
 * The primitive never catches a sink exception; the
 * exception propagates to the executor, which owns the run abort. The
 * dependency direction is exactly the pinned set: the IR enums,
 * {@link UnicodeScalars}, {@link SemanticTable}, the
 * {@link SharedValueSemantics} gates, and the registry — never a target
 * backend, the retained {@code std/*} files, the migration registry, or
 * the {@code StdlibFunctionCatalog} (the dispatch's arity/descriptor
 * facts come from the op's own operand types and the closed table, and
 * the catalog's closed-set coverage is the lowerer battery's fact).</p>
 *
 * <p><b>String family (Unicode scalar domain, D4 verbatim).</b>
 * {@code STRING_LENGTH} — Unicode scalar count as signed32; count
 * overflow fails E8004 ({@code INT32_RESULT} at the call origin —
 * defensive: the model's counts are bounded, but the closed policy pins
 * the gate). {@code STRING_SUBSTRING} — scalar indices;
 * {@code lo=max(0,start)}, {@code hi=min(max(0,end),length)}; empty when
 * {@code lo>=hi}; the result is the scalar slice {@code [lo,hi)}.
 * {@code STRING_CONTAINS}/{@code STRING_STARTS_WITH}/
 * {@code STRING_ENDS_WITH} — literal scalar-subsequence comparison; an
 * empty part is contained, a prefix, and a suffix.
 * {@code STRING_REPLACE} — replace all non-overlapping occurrences
 * left-to-right; empty {@code from} returns the input unchanged; the
 * replacement is literal, never pattern-interpreted.
 * {@code STRING_SPLIT} — empty input → {@code []} (regardless of the
 * separator); empty separator → one single-scalar string per element;
 * otherwise split at every non-overlapping literal separator occurrence
 * with leading/internal/trailing empty parts preserved.
 * {@code STRING_TRIM} — remove leading/trailing characters in exactly
 * the closed set U+0009–U+000D and U+0020 (U+000B/U+000C are trimmed;
 * U+00A0 is not). All string algorithms operate on
 * {@link UnicodeScalars.Valid} carriers: invalid scalar encodings were
 * already rejected at that argument's {@code STDLIB_PARAMETER} boundary
 * ({@code TYPE_DESCRIPTOR}, E8001
 * {@code expected string, got invalid Unicode scalar encoding}); the
 * primitive never re-interprets UTF-8, and an {@code Invalid} carrier
 * reaching an algorithm is a producer {@link Defect} — never a second
 * projection. Scalar indices/counts are code points: a surrogate pair is
 * one scalar.</p>
 *
 * <p><b>Table.</b> {@code TABLE_KEYS} — the string keys of the semantic
 * table in first-insertion order; delete removes the order slot and
 * reinsertion appends it ({@link SemanticTable} order contract); non-string
 * keys never exist on a semantic table. Policy {@code NO_DEAL_FAILURE} —
 * never fails.</p>
 *
 * <p><b>JSON.</b> {@code JSON_PARSE} — RFC-8259 scalar-valid parse of the
 * (already scalar-valid) input; object order follows text; duplicate keys
 * keep the last value and the first position; a signed32 <em>integer
 * lexical form</em> (the RFC-8259 integer grammar with the leading-zero
 * rules, mathematically within
 * {@code [-2147483648, 2147483647]}, {@code -0} normalized to {@code 0})
 * becomes {@link Value.Int}, and every other numeric form (fraction or
 * exponent forms, out-of-range integers) becomes {@link Value.Number}; a
 * syntax defect fails with policy {@code JSON_PARSE_SYNTAX} — E8001
 * {@code JSON parse error at position {oneBasedByteOffset}: {reason}}
 * with metadata {@code {oneBasedByteOffset}} (the defect's 1-based UTF-8
 * byte offset) and {@code {reason}} (a stable defect-classification text
 * owned by this component, the {@code REASON_*} constants), origin =
 * the {@code STDLIB_CALL(JSON_PARSE)} call origin, no cause, active
 * frames. A successful parse whose top-level value is not a table then
 * fails the {@code STDLIB_RETURN} boundary — that boundary is the call
 * machine's, never this primitive's. {@code JSON_STRINGIFY} — finite
 * acyclic JSON-shaped data (string-keyed objects, arrays, and
 * null/boolean/int/number/string leaves); object fields in
 * first-insertion order, arrays in index order; RFC-8259 escaping
 * (control characters, quote, backslash; surrogate pairs are emitted as
 * raw scalar UTF-8); shortest round-trippable decimal number formatting
 * ({@code Double.toString} — the JDK's unique-identification spelling);
 * the first failure in declaration order fails via
 * {@code JSON_TO_ERROR} — E8001
 * {@code unsupported type for JSON encoding: {actual}} with the pinned
 * expected text {@code string, number, boolean, or table} and metadata
 * {@code {fieldPath}}/{@code {actual}}, origin = the call
 * origin. The {@code {fieldPath}} spelling is owned by this component: a
 * dot-separated pre-order traversal from the root value — table fields
 * append the field name, array elements append the 0-based element
 * index, and the root itself has the empty path; it stays internal
 * metadata and never surfaces in the DEAL-visible projection.
 * Unsupported values
 * (functions, class instances, async-operation handles, missing values,
 * invalid Unicode scalar sequences), cycles, and nonfinite numbers fail
 * here; acyclic finite data never fails.</p>
 *
 * <p><b>Math.</b> {@code MATH_FLOOR}/{@code MATH_CEIL} — IEEE
 * floor/ceil, returned as Number. {@code MATH_SQRT} — IEEE sqrt; a
 * negative non-NaN input fails {@code SQRT_NEGATIVE} (E8001
 * {@code sqrt of negative number}; the failure carries the negative
 * operand in its {@code actual} field as the canonical IEEE-754
 * hex-float spelling, {@link CanonicalJson#numberHex}); NaN returns NaN
 * and {@code -0.0} returns {@code -0.0}. {@code MATH_ABS_INT} — signed32
 * absolute value; {@code -2147483648} fails {@code INT32_RESULT} (E8004
 * {@code int out of safe range} at the call origin). {@code MATH_ABS_NUMBER}
 * — IEEE absolute value ({@code -0.0} → {@code +0.0}).
 * {@code MATH_MIN_INT}/{@code MATH_MAX_INT} — return the selected
 * signed32 operand; equal operands return that operand value.</p>
 *
 * <p><b>Console (D5).</b> {@code CONSOLE_LOG}/{@code CONSOLE_ERROR}
 * append the argument's exact scalar UTF-8 bytes plus one {@code \n} to
 * the named channel ({@code STDOUT}/{@code STDERR}) as exactly one
 * ordered effect through the injected {@link ConsoleSink} — one
 * {@code write(byte[])} call per execution, byte-exact bytes, ordered
 * {@code \n} suffix, channel identity — then return the null value. The
 * effect is irreversible and ordered before terminal SUCCESS.</p>
 *
 * <p><b>Fail-closed discipline.</b> A shape outside the closed contracts
 * — a non-{@code STDLIB_CALL} op, a payload whose
 * {@code effectCapability} is not {@code STDLIB_SEMANTICS}, a stamped
 * {@code failurePolicy} differing from the single
 * {@link SemanticIrValidator#stdlibPolicy} table, an argument-count
 * mismatch, a wrong-kind argument carrier, an {@code Invalid} scalar
 * carrier reaching a string algorithm, a sink whose {@code channel()}
 * mismatches the call's channel, or a null sink on a console call —
 * fails closed as a producer {@link Defect}, never as a DEAL projection
 * and never as a crash. {@code execute} additionally checks that the op's
 * {@code failurePolicy} was stamped from the single table — the closed
 * algorithm→policy assignment stays single-sourced.</p>
 *
 * <p><b>Purity and bounds.</b> No mutation of the unit, no randomness,
 * no retry, no target knowledge; string algorithms are linear in the
 * scalar count, table keys linear in the key count, and parse/stringify
 * recursion is bounded by the input nesting depth (≤ input length) — a
 * resource exhaustion during execution is infrastructure failure
 * (propagated as an {@code Error}), never a DEAL error. The failure rows
 * are the registry's: codes and templates come from
 * {@link FailureContractRegistry#row(FailurePolicyId)}.</p>
 */
public final class SharedStdlibSemantics {

    private SharedStdlibSemantics() {
        // Static surface only; pure and stateless.
    }

    // =========================================================================
    // Producer defects (fail closed, never a DEAL projection)
    // =========================================================================

    /**
     * An executor producer defect: a shape outside the closed stdlib
     * contracts reached the primitive. Internal control flow — fail
     * closed, never a DEAL projection and never a crash.
     */
    public static final class Defect extends RuntimeException {

        private static final long serialVersionUID = 1L;

        public Defect(String message) {
            super(message);
        }
    }

    // =========================================================================
    // The closed value view of the 21 operations
    // =========================================================================

    /**
     * The closed value view the executor consumes and produces over the
     * semantic value model: exactly the values the 21 operations resolve,
     * compare, store, encode, and publish — language null, boolean,
     * signed32 int, IEEE-754 number, string (carrying the closed
     * {@link UnicodeScalars.ScalarString} classification), table
     * ({@link SemanticTable}, first-insertion order), array
     * ({@link SemanticArray}, index order), and the unsupported-value
     * carrier {@link Other} (an actual kind outside the JSON-shaped set,
     * reported through its canonical {@link ActualKind} token by
     * {@code JSON_STRINGIFY}). Null references never appear: language
     * null is the explicit {@link Null} variant, and every variant
     * renders its canonical {@link ActualKind}. The view is realized by
     * the oracle's heap and by test fixtures; the executor interprets
     * classifications and carriers only, never target representations.
     */
    public sealed interface Value
        permits Value.Null, Value.Bool, Value.Int, Value.Number, Value.String,
                Value.Table, Value.Array, Value.Other {

        /** The canonical actual kind this value renders as. */
        ActualKind actualKind();

        /** A string view carrying the validated classification of {@code carrier}. */
        static Value string(java.lang.String carrier) {
            return new String(UnicodeScalars.validate(carrier));
        }

        /** A string view carrying an explicit scalar classification. */
        static Value string(UnicodeScalars.ScalarString scalar) {
            return new String(Objects.requireNonNull(scalar, "scalar must not be null"));
        }

        /** An array view over the ordered elements. */
        static Value array(List<Value> elements) {
            return new Array(SemanticArray.of(elements));
        }

        /** An array view over the ordered elements. */
        static Value array(Value... elements) {
            return new Array(SemanticArray.of(elements));
        }

        /** An empty table view with a fresh identity. */
        static Value table() {
            return new Table(new SemanticTable<>());
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

        /** An array value carrying its ordered element model. */
        record Array(SemanticArray<Value> elements) implements Value {

            public Array {
                Objects.requireNonNull(elements, "elements must not be null");
            }

            @Override
            public ActualKind actualKind() {
                return ActualKind.ARRAY;
            }
        }

        /**
         * A value outside the JSON-shaped set: exactly the actual kinds
         * {@code missing}, {@code function}, {@code async-operation},
         * and {@code class} (with the canonical class-id atom text).
         * {@code JSON_STRINGIFY} reports it through its canonical
         * {@link ActualKind} token ({@code class:<ClassId>} for a class
         * value, never a target class name); no other algorithm consumes
         * an {@code Other} value.
         */
        record Other(ActualKind kind, java.lang.String classId) implements Value {

            public Other {
                Objects.requireNonNull(kind, "kind must not be null");
                switch (kind) {
                    case CLASS -> {
                        if (classId == null || classId.isEmpty()) {
                            throw new IllegalArgumentException(
                                "a CLASS Other view carries the canonical class-id atom "
                                    + "text (@modulePath/ClassName); classId must be "
                                    + "non-null and non-empty");
                        }
                    }
                    case MISSING, FUNCTION, ASYNC_OPERATION -> {
                        if (classId != null) {
                            throw new IllegalArgumentException(
                                "only a CLASS Other view carries a class id");
                        }
                    }
                    default -> throw new IllegalArgumentException(
                        "an Other view carries a value outside the JSON-shaped set "
                            + "(missing, function, async-operation, class); got " + kind);
                }
            }

            @Override
            public ActualKind actualKind() {
                return kind;
            }
        }
    }

    // =========================================================================
    // Console sink (D5)
    // =========================================================================

    /** The named console channel of {@code STDLIB_CALL(CONSOLE_*)}. */
    public enum Channel { STDOUT, STDERR }

    /**
     * The injected console sink (D5): the executor supplies it, the
     * primitive performs no process I/O. {@link #write(byte[])} receives
     * exactly one byte sequence per call — the argument's exact scalar
     * UTF-8 bytes plus one {@code \n}. A sink failure (any exception
     * thrown by {@code write}) is infrastructure failure
     * ({@code INFRASTRUCTURE_ONLY}): not a DEAL error, no DEAL
     * diagnostic, not catchable — the primitive catches nothing and the
     * exception propagates to the executor, which aborts the run.
     */
    public interface ConsoleSink {

        /** The channel this sink writes to ({@code STDOUT} or {@code STDERR}). */
        Channel channel();

        /**
         * Writes the exact effect bytes (scalar UTF-8 + {@code \n}).
         *
         * @param bytes the exact byte sequence of one console effect;
         *              non-null
         */
        void write(byte[] bytes);
    }

    /**
     * The injected clock seam of {@code STDLIB_CALL(TIME_NOW_MILLIS)}
     * (K7 item 4): the executor supplies the target-clock reading the
     * shared algorithm returns, so the primitive stays pure/deterministic
     * and performs no process I/O — the LuaJIT artifact reads
     * {@code os.time() * 1000} and the JVM artifact
     * {@code System.currentTimeMillis()} in their own closed realization
     * tables, while the oracle injects its pinned deterministic reading.
     */
    public interface Clock {

        /** The current epoch-millisecond reading of the target clock. */
        long nowMillis();
    }

    /**
     * The production default clock: the wall clock of the executing
     * process. The oracle never uses it — the oracle injects its own
     * deterministic reading through the four-argument
     * {@code execute} surface.
     */
    public static final Clock SYSTEM_CLOCK = System::currentTimeMillis;

    // =========================================================================
    // Sealed outcome
    // =========================================================================

    /**
     * One algorithm failure: the structured registry-row projection
     * (built with {@link BoundaryFailure#fromRow} — the primitive never
     * selects message text) paired with the operation origin of the
     * closed table's rule — the {@code STDLIB_CALL} call origin for
     * every stdlib row ({@code JSON_PARSE_SYNTAX},
     * {@code JSON_TO_ERROR}, {@code SQRT_NEGATIVE} operation origin,
     * {@code INT32_RESULT} at the call origin).
     */
    public record StdlibFailure(BoundaryFailure failure, SourceOrigin origin) {

        public StdlibFailure {
            Objects.requireNonNull(failure, "failure must not be null");
            Objects.requireNonNull(origin, "origin must not be null");
        }
    }

    /**
     * The closed terminal of one executor call:
     * {@code Success(value) | Failure(StdlibFailure)}. A {@code Failure}
     * is exactly one pinned projection — never a partial value and never
     * a retry. A console sink exception is not a {@code Failure}: it
     * propagates out of the primitive as infrastructure failure.
     *
     * @param <V> the success value type (always {@link Value} for the
     *            published algorithm results)
     */
    public sealed interface Outcome<V> permits Outcome.Success, Outcome.Failure {

        /** The algorithm succeeded; {@code value} is the published result. */
        record Success<V>(V value) implements Outcome<V> {

            public Success {
                Objects.requireNonNull(value, "value must not be null");
            }
        }

        /** The algorithm failed; {@code failure} is the registry-row projection. */
        record Failure<V>(StdlibFailure failure) implements Outcome<V> {

            public Failure {
                Objects.requireNonNull(failure, "failure must not be null");
            }
        }
    }

    // =========================================================================
    // The single execution dispatch over a validated STDLIB_CALL op
    // =========================================================================

    /**
     * Executes one validated {@code STDLIB_CALL} op with its resolved
     * argument values in left-to-right order (the declared-descriptor
     * inputs whose {@code STDLIB_PARAMETER} boundaries passed), through
     * the per-family algorithm of the closed stdlib table, and returns
     * the sealed outcome. The op's stamped {@code failurePolicy} is
     * cross-checked against the single
     * {@link SemanticIrValidator#stdlibPolicy} table (the closed
     * algorithm→policy assignment stays single-sourced), and the
     * payload's {@code effectCapability} must be
     * {@code STDLIB_SEMANTICS} — any deviation is a producer defect,
     * never executed.
     *
     * <p>Argument carriers follow the boundary admission rule exactly:
     * a string parameter is a {@link Value.String} whose scalar is
     * {@link UnicodeScalars.Valid} (an {@code Invalid} carrier is a
     * {@link Defect} — the parameter boundary rejects it first, so the
     * primitive is never reached with an invalid carrier); an int
     * parameter is {@link Value.Int} or an in-range integral
     * {@link Value.Number} (the int boundary's admission set, passed
     * unchanged); a number parameter is {@link Value.Number} or
     * {@link Value.Int} (converted exactly, {@code int} → {@code double}
     * is exact); a table parameter is {@link Value.Table}. Any other
     * carrier fails closed. Console calls require the injected
     * {@link ConsoleSink} whose {@code channel()} matches the call's
     * channel; non-console calls ignore the sink.</p>
     *
     * @param op   the validated {@code STDLIB_CALL} op; non-null
     * @param args the resolved argument values in left-to-right source
     *             order (same count as the op's operands); non-null, no
     *             null elements
     * @param sink the injected console sink for
     *             {@code CONSOLE_LOG}/{@code CONSOLE_ERROR}; ignored by
     *             every other id (may be null there)
     * @return the sealed per-family outcome; a console sink exception
     *         propagates uncaught (infrastructure failure, never a DEAL
     *         failure)
     * @throws Defect               if the op is not a
     *                              {@code STDLIB_CALL}, if the payload's
     *                              effect capability is not
     *                              {@code STDLIB_SEMANTICS}, if the
     *                              stamped policy differs from
     *                              {@link SemanticIrValidator#stdlibPolicy},
     *                              if the argument count mismatches the
     *                              op shapes or the declared arity, if an
     *                              argument carrier is outside the
     *                              boundary admission set, or if a console
     *                              call's sink is null or carries the
     *                              wrong channel
     * @throws NullPointerException if {@code op} or {@code args} is null
     */
    public static Outcome<Value> execute(SemanticOp op, List<Value> args,
                                         ConsoleSink sink) {
        return execute(op, args, sink, SYSTEM_CLOCK);
    }

    /**
     * Executes one validated {@code STDLIB_CALL} op with an injected
     * {@link Clock} (the {@code TIME_NOW_MILLIS} seam, K7 item 4): the
     * full surface of {@link #execute(SemanticOp, List, ConsoleSink)};
     * the clock is consulted only by {@code TIME_NOW_MILLIS} and every
     * other id ignores it.
     *
     * @param op    the validated {@code STDLIB_CALL} op; non-null
     * @param args  the resolved argument values in left-to-right source
     *              order; non-null, no null elements
     * @param sink  the injected console sink (may be null for non-console
     *              ids)
     * @param clock the injected clock of {@code TIME_NOW_MILLIS}; non-null
     * @return the sealed per-family outcome
     */
    public static Outcome<Value> execute(SemanticOp op, List<Value> args,
                                         ConsoleSink sink, Clock clock) {
        Objects.requireNonNull(op, "op must not be null");
        Objects.requireNonNull(args, "args must not be null");
        if (op.kind() != SemanticOpKind.STDLIB_CALL) {
            throw new Defect("execute receives only STDLIB_CALL ops, got " + op.kind()
                + " — a producer defect, never executed");
        }
        if (!(op.payload() instanceof KindPayload.StdlibCallPayload payload)) {
            throw new Defect("a STDLIB_CALL op carries a StdlibCallPayload; got "
                + op.payload().getClass().getSimpleName());
        }
        if (payload.effectCapability() != SemanticCapability.STDLIB_SEMANTICS) {
            throw new Defect("the STDLIB_CALL effect capability is STDLIB_SEMANTICS; got "
                + payload.effectCapability());
        }
        StdlibFunctionId function = payload.function();
        FailurePolicyId stamped = op.failurePolicy();
        FailurePolicyId pinned = SemanticIrValidator.stdlibPolicy(function);
        if (stamped != pinned) {
            throw new Defect("STDLIB_CALL(" + function + ") stamps failurePolicy " + pinned
                + " from the single stdlibPolicy table; got " + stamped
                + " — the closed algorithm→policy assignment is single-sourced");
        }
        if (args.size() != payload.args().size() || args.size() != op.operands().size()
                || args.size() != op.operandTypes().size()) {
            throw new Defect("STDLIB_CALL(" + function + ") carries " + payload.args().size()
                + " payload args, " + op.operands().size() + " operands, "
                + op.operandTypes().size() + " operand types, but " + args.size()
                + " resolved argument values were supplied — a count mismatch is a "
                + "producer defect, never executed");
        }
        List<Value> argv = List.copyOf(args); // rejects null elements
        requireArity(function, argv.size());
        return switch (function) {
            case CONSOLE_LOG ->
                consoleLog(op.origin(), validTextOf(argv, 0, function), sink);
            case CONSOLE_ERROR ->
                consoleError(op.origin(), validTextOf(argv, 0, function), sink);
            case STRING_LENGTH ->
                stringLength(op.origin(), validTextOf(argv, 0, function));
            case STRING_SUBSTRING -> stringSubstring(op.origin(),
                validTextOf(argv, 0, function), intOf(argv, 1, function),
                intOf(argv, 2, function));
            case STRING_CONTAINS -> stringContains(op.origin(),
                validTextOf(argv, 0, function), validTextOf(argv, 1, function));
            case STRING_STARTS_WITH -> stringStartsWith(op.origin(),
                validTextOf(argv, 0, function), validTextOf(argv, 1, function));
            case STRING_ENDS_WITH -> stringEndsWith(op.origin(),
                validTextOf(argv, 0, function), validTextOf(argv, 1, function));
            case STRING_REPLACE -> stringReplace(op.origin(),
                validTextOf(argv, 0, function), validTextOf(argv, 1, function),
                validTextOf(argv, 2, function));
            case STRING_SPLIT -> stringSplit(op.origin(),
                validTextOf(argv, 0, function), validTextOf(argv, 1, function));
            case STRING_TRIM -> stringTrim(op.origin(), validTextOf(argv, 0, function));
            case TABLE_KEYS -> tableKeys(op.origin(), tableOf(argv, 0, function));
            case JSON_PARSE -> jsonParse(op.origin(), validTextOf(argv, 0, function));
            case JSON_STRINGIFY -> jsonStringify(op.origin(), tableOf(argv, 0, function));
            case MATH_FLOOR -> mathFloor(op.origin(), numberOf(argv, 0, function));
            case MATH_CEIL -> mathCeil(op.origin(), numberOf(argv, 0, function));
            case MATH_SQRT -> mathSqrt(op.origin(), numberOf(argv, 0, function));
            case MATH_ABS_INT -> mathAbsInt(op.origin(), intOf(argv, 0, function));
            case MATH_ABS_NUMBER ->
                mathAbsNumber(op.origin(), numberOf(argv, 0, function));
            case MATH_MIN_INT -> mathMinInt(op.origin(), intOf(argv, 0, function),
                intOf(argv, 1, function));
            case MATH_MAX_INT -> mathMaxInt(op.origin(), intOf(argv, 0, function),
                intOf(argv, 1, function));
            case TIME_NOW_MILLIS -> timeNowMillis(op.origin(), clock);
        };
    }

    /**
     * The declared parameter arity of one closed stdlib id (D1 table plus
     * the K7 {@code std.time} row, arity 0).
     */
    private static int declaredArity(StdlibFunctionId function) {
        return switch (function) {
            case TIME_NOW_MILLIS -> 0;
            case CONSOLE_LOG, CONSOLE_ERROR, STRING_LENGTH, STRING_TRIM, TABLE_KEYS,
                 JSON_PARSE, JSON_STRINGIFY, MATH_FLOOR, MATH_CEIL, MATH_SQRT,
                 MATH_ABS_INT, MATH_ABS_NUMBER -> 1;
            case STRING_CONTAINS, STRING_STARTS_WITH, STRING_ENDS_WITH, STRING_SPLIT,
                 MATH_MIN_INT, MATH_MAX_INT -> 2;
            case STRING_SUBSTRING, STRING_REPLACE -> 3;
        };
    }

    private static void requireArity(StdlibFunctionId function, int count) {
        int declared = declaredArity(function);
        if (count != declared) {
            throw new Defect("STDLIB_CALL(" + function + ") declares " + declared
                + " parameter(s); got " + count + " resolved arguments — a producer "
                + "defect, never executed");
        }
    }

    /** A string parameter carrier: {@link Value.String} with a {@code Valid} scalar. */
    private static UnicodeScalars.Valid validTextOf(List<Value> args, int index,
                                                    StdlibFunctionId function) {
        Value arg = args.get(index);
        if (arg instanceof Value.String string
                && string.scalar() instanceof UnicodeScalars.Valid valid) {
            return valid;
        }
        throw new Defect("STDLIB_CALL(" + function + ") argument " + (index + 1)
            + " must be a Valid string carrier (the STDLIB_PARAMETER boundary rejects "
            + "invalid scalar encodings first); got " + describe(arg)
            + " — the primitive is never reached with an invalid carrier");
    }

    /** An int parameter carrier: {@link Value.Int} or an in-range integral {@link Value.Number}. */
    private static int intOf(List<Value> args, int index, StdlibFunctionId function) {
        Value arg = args.get(index);
        return switch (arg) {
            case Value.Int intValue -> intValue.value();
            case Value.Number number -> {
                double value = number.value();
                if (!Double.isFinite(value) || value != Math.rint(value)
                        || value < -2147483648d || value > 2147483647d) {
                    throw new Defect("STDLIB_CALL(" + function + ") argument " + (index + 1)
                        + " must be a signed32 int carrier (the int boundary's admission "
                        + "set); got number " + value);
                }
                yield (int) value;
            }
            default -> throw new Defect("STDLIB_CALL(" + function + ") argument "
                + (index + 1) + " must be a signed32 int carrier; got " + describe(arg));
        };
    }

    /** A number parameter carrier: {@link Value.Number} or {@link Value.Int} (exact double). */
    private static double numberOf(List<Value> args, int index, StdlibFunctionId function) {
        Value arg = args.get(index);
        return switch (arg) {
            case Value.Number number -> number.value();
            case Value.Int intValue ->
                SharedValueSemantics.numberFromInt(intValue.value());
            default -> throw new Defect("STDLIB_CALL(" + function + ") argument "
                + (index + 1) + " must be a number carrier; got " + describe(arg));
        };
    }

    /** A table parameter carrier: {@link Value.Table}. */
    private static SemanticTable<Value> tableOf(List<Value> args, int index,
                                                StdlibFunctionId function) {
        Value arg = args.get(index);
        if (arg instanceof Value.Table table) {
            return table.table();
        }
        throw new Defect("STDLIB_CALL(" + function + ") argument " + (index + 1)
            + " must be a table carrier; got " + describe(arg));
    }

    /** The closed variant name for defect reporting. */
    private static String describe(Value value) {
        return value.getClass().getSimpleName() + "/" + value.actualKind();
    }

    // =========================================================================
    // Registry-row projection (codes/templates stay the registry's single source)
    // =========================================================================

    /**
     * Instantiates one pinned registry-row template into an outcome
     * failure at {@code origin} — the only failure-construction surface.
     *
     * @param policy        the closed policy of the named row; non-null
     * @param templateIndex the row's template list position
     * @param expected      the canonical expected text, or {@code null}
     * @param actual        the canonical actual text, or {@code null}
     * @param metadata      the row's pinned metadata values in the row's
     *                      pinned key order; may be empty, never null
     * @param origin        the operation origin of the row's rule (the
     *                      {@code STDLIB_CALL} call origin); non-null
     * @return the sealed {@code Failure} outcome
     */
    private static Outcome.Failure<Value> failOf(FailurePolicyId policy, int templateIndex,
                                                 String expected, String actual,
                                                 Map<String, String> metadata,
                                                 SourceOrigin origin) {
        BoundaryFailure failure = BoundaryFailure.fromRow(
            FailureContractRegistry.row(policy), templateIndex, expected, actual,
            metadata, null);
        return new Outcome.Failure<>(new StdlibFailure(failure, origin));
    }

    /** The pinned two-key metadata map of the {@code JSON_PARSE_SYNTAX} row. */
    private static Map<String, String> parseMetadata(long oneBasedByteOffset, String reason) {
        Map<String, String> metadata = new LinkedHashMap<>();
        metadata.put("oneBasedByteOffset", Long.toString(oneBasedByteOffset));
        metadata.put("reason", reason);
        return metadata;
    }

    /** The pinned two-key metadata map of the {@code JSON_TO_ERROR} row. */
    private static Map<String, String> jsonToErrorMetadata(String fieldPath, String actual) {
        Map<String, String> metadata = new LinkedHashMap<>();
        metadata.put("fieldPath", fieldPath);
        metadata.put("actual", actual);
        return metadata;
    }

    /** The signed32 gate ({@code INT32_RESULT}): success publishes the int, overflow E8004. */
    private static Outcome<Value> int32Gate(long value, SourceOrigin origin) {
        SharedValueSemantics.Int32Result result =
            SharedValueSemantics.checkInt32Integral(value, origin);
        return switch (result) {
            case SharedValueSemantics.Int32Result.Value intValue ->
                new Outcome.Success<>(new Value.Int(intValue.value()));
            case SharedValueSemantics.Int32Result.Fail ignored -> failOf(
                FailurePolicyId.INT32_RESULT, 0, null, null, new LinkedHashMap<>(), origin);
        };
    }

    // =========================================================================
    // Console (D5): byte-exact one-effect contract over the injected sink
    // =========================================================================

    /**
     * {@code CONSOLE_LOG}: appends the argument's exact scalar UTF-8
     * bytes plus one {@code \n} to {@code STDOUT} as exactly one ordered
     * effect through the injected {@link ConsoleSink}, then publishes
     * the null result. The effect is byte-exact, the {@code \n} suffix
     * is ordered, and the write happens exactly once before terminal
     * SUCCESS. A sink failure is infrastructure failure
     * ({@code INFRASTRUCTURE_ONLY}): the primitive catches nothing — the
     * sink exception propagates to the executor, which aborts the run,
     * and no DEAL failure is ever reported.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param text   the scalar-valid string argument; non-null
     * @param sink   the injected sink; non-null, channel
     *               {@link Channel#STDOUT}
     * @return {@code Success} with the language-null value
     * @throws Defect               if the sink's channel is not
     *                              {@code STDOUT}
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> consoleLog(SourceOrigin origin, UnicodeScalars.Valid text,
                                            ConsoleSink sink) {
        return consoleEffect(origin, Channel.STDOUT, text, sink);
    }

    /**
     * {@code CONSOLE_ERROR}: appends the argument's exact scalar UTF-8
     * bytes plus one {@code \n} to {@code STDERR} as exactly one ordered
     * effect through the injected {@link ConsoleSink}, then publishes
     * the null result. The same one-effect, byte-exact,
     * infrastructure-only contract as {@link #consoleLog} on the
     * {@code STDERR} channel.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param text   the scalar-valid string argument; non-null
     * @param sink   the injected sink; non-null, channel
     *               {@link Channel#STDERR}
     * @return {@code Success} with the language-null value
     * @throws Defect               if the sink's channel is not
     *                              {@code STDERR}
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> consoleError(SourceOrigin origin, UnicodeScalars.Valid text,
                                              ConsoleSink sink) {
        return consoleEffect(origin, Channel.STDERR, text, sink);
    }

    /** The shared one-effect console realization (D5). */
    private static Outcome<Value> consoleEffect(SourceOrigin origin, Channel channel,
                                                UnicodeScalars.Valid text,
                                                ConsoleSink sink) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(text, "text must not be null");
        Objects.requireNonNull(sink, "sink must not be null");
        if (sink.channel() != channel) {
            throw new Defect("the console call writes " + channel + ", but the injected "
                + "sink carries channel " + sink.channel()
                + " — the channel identity is part of the operation-level effect "
                + "contract");
        }
        byte[] scalarUtf8 = text.carrier().getBytes(StandardCharsets.UTF_8);
        byte[] effectBytes = Arrays.copyOf(scalarUtf8, scalarUtf8.length + 1);
        effectBytes[effectBytes.length - 1] = (byte) '\n';
        // Exactly one ordered effect before terminal SUCCESS. The
        // primitive catches nothing: a sink exception is infrastructure
        // failure (INFRASTRUCTURE_ONLY) and propagates to the executor,
        // which aborts the run — never a DEAL failure.
        sink.write(effectBytes);
        return new Outcome.Success<>(Value.Null.INSTANCE);
    }

    // =========================================================================
    // String family (Unicode scalar domain)
    // =========================================================================

    /**
     * {@code STRING_LENGTH}: the Unicode scalar count (code points — a
     * surrogate pair is one scalar) as signed32; a count outside
     * {@code [-2147483648, 2147483647]} fails E8004
     * {@code int out of safe range} ({@code INT32_RESULT} at the call origin).
     * Defensive: the model's counts are bounded, but the closed policy
     * pins the gate.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @return {@code Success} with the signed32 scalar count, or
     *         {@code Failure} with the E8004 range projection
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringLength(SourceOrigin origin,
                                              UnicodeScalars.Valid input) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        return int32Gate(input.carrier().codePointCount(0, input.carrier().length()), origin);
    }

    /**
     * {@code STRING_SUBSTRING}: scalar indices;
     * {@code lo=max(0,start)}, {@code hi=min(max(0,end),length)}; empty
     * when {@code lo>=hi}; the result is the scalar slice
     * {@code [lo,hi)}. Policy {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @param start  the declared {@code int} start index (0-based,
     *               inclusive; clamped to {@code [0, length]})
     * @param end    the declared {@code int} end index (0-based,
     *               exclusive; clamped to {@code [0, length]})
     * @return {@code Success} with the scalar slice {@code [lo,hi)}
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringSubstring(SourceOrigin origin,
                                                 UnicodeScalars.Valid input,
                                                 int start, int end) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        int[] codePoints = input.carrier().codePoints().toArray();
        int lo = Math.max(0, start);
        int hi = Math.min(Math.max(0, end), codePoints.length);
        if (lo >= hi) {
            return new Outcome.Success<>(Value.string(""));
        }
        return new Outcome.Success<>(
            Value.string(new java.lang.String(codePoints, lo, hi - lo)));
    }

    /**
     * {@code STRING_CONTAINS}: literal scalar-subsequence comparison —
     * true iff {@code part} occurs as a scalar subsequence of
     * {@code input}; an empty part is contained. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @param part   the scalar-valid part argument; non-null
     * @return {@code Success} with the boolean result
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringContains(SourceOrigin origin,
                                                UnicodeScalars.Valid input,
                                                UnicodeScalars.Valid part) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(part, "part must not be null");
        return new Outcome.Success<>(new Value.Bool(indexOfSubsequence(
            codePointsOf(input), codePointsOf(part), 0) >= 0));
    }

    /**
     * {@code STRING_STARTS_WITH}: literal scalar-subsequence comparison —
     * true iff {@code input} starts with the scalar sequence
     * {@code part}; an empty part is a prefix. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @param part   the scalar-valid part argument; non-null
     * @return {@code Success} with the boolean result
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringStartsWith(SourceOrigin origin,
                                                  UnicodeScalars.Valid input,
                                                  UnicodeScalars.Valid part) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(part, "part must not be null");
        int[] inputCodePoints = codePointsOf(input);
        int[] partCodePoints = codePointsOf(part);
        return new Outcome.Success<>(new Value.Bool(
            partCodePoints.length <= inputCodePoints.length
                && matchAt(inputCodePoints, partCodePoints, 0)));
    }

    /**
     * {@code STRING_ENDS_WITH}: literal scalar-subsequence comparison —
     * true iff {@code input} ends with the scalar sequence
     * {@code part}; an empty part is a suffix. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @param part   the scalar-valid part argument; non-null
     * @return {@code Success} with the boolean result
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringEndsWith(SourceOrigin origin,
                                                UnicodeScalars.Valid input,
                                                UnicodeScalars.Valid part) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(part, "part must not be null");
        int[] inputCodePoints = codePointsOf(input);
        int[] partCodePoints = codePointsOf(part);
        return new Outcome.Success<>(new Value.Bool(
            partCodePoints.length <= inputCodePoints.length
                && matchAt(inputCodePoints, partCodePoints,
                    inputCodePoints.length - partCodePoints.length)));
    }

    /**
     * {@code STRING_REPLACE}: replace all non-overlapping occurrences of
     * {@code from} in {@code input}, left-to-right; an empty
     * {@code from} returns the input unchanged; the replacement
     * {@code to} is literal — never pattern-interpreted. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @param from   the scalar-valid search argument; non-null
     * @param to     the scalar-valid literal replacement; non-null
     * @return {@code Success} with the replaced scalar sequence
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringReplace(SourceOrigin origin,
                                               UnicodeScalars.Valid input,
                                               UnicodeScalars.Valid from,
                                               UnicodeScalars.Valid to) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(from, "from must not be null");
        Objects.requireNonNull(to, "to must not be null");
        int[] inputCodePoints = codePointsOf(input);
        int[] fromCodePoints = codePointsOf(from);
        int[] toCodePoints = codePointsOf(to);
        if (fromCodePoints.length == 0) {
            return new Outcome.Success<>(Value.string(input));
        }
        StringBuilder result = new StringBuilder();
        int cursor = 0;
        while (cursor <= inputCodePoints.length - fromCodePoints.length) {
            if (matchAt(inputCodePoints, fromCodePoints, cursor)) {
                appendCodePoints(result, toCodePoints);
                cursor += fromCodePoints.length;
            } else {
                result.appendCodePoint(inputCodePoints[cursor]);
                cursor++;
            }
        }
        for (int i = cursor; i < inputCodePoints.length; i++) {
            result.appendCodePoint(inputCodePoints[i]);
        }
        return new Outcome.Success<>(Value.string(result.toString()));
    }

    /**
     * {@code STRING_SPLIT}: empty input → {@code []} (regardless of the
     * separator); empty separator → one single-scalar string per
     * element; otherwise split at every non-overlapping literal
     * separator occurrence with leading/internal/trailing empty parts
     * preserved. Policy {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin    the {@code STDLIB_CALL} operation origin; non-null
     * @param input     the scalar-valid string argument; non-null
     * @param separator the scalar-valid separator argument; non-null
     * @return {@code Success} with the array of parts in order
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringSplit(SourceOrigin origin,
                                             UnicodeScalars.Valid input,
                                             UnicodeScalars.Valid separator) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(separator, "separator must not be null");
        int[] inputCodePoints = codePointsOf(input);
        int[] separatorCodePoints = codePointsOf(separator);
        if (inputCodePoints.length == 0) {
            return new Outcome.Success<>(Value.array());
        }
        if (separatorCodePoints.length == 0) {
            List<Value> singles = new ArrayList<>(inputCodePoints.length);
            for (int codePoint : inputCodePoints) {
                singles.add(Value.string(UnicodeScalars.scalarString(codePoint)));
            }
            return new Outcome.Success<>(Value.array(singles));
        }
        List<Value> parts = new ArrayList<>();
        int cursor = 0;
        int occurrence;
        while ((occurrence = indexOfSubsequence(inputCodePoints, separatorCodePoints,
                cursor)) >= 0) {
            parts.add(Value.string(
                new java.lang.String(inputCodePoints, cursor, occurrence - cursor)));
            cursor = occurrence + separatorCodePoints.length;
        }
        // The trailing part is always appended — an empty remainder after
        // a separator at the end is preserved exactly.
        parts.add(Value.string(new java.lang.String(inputCodePoints, cursor,
            inputCodePoints.length - cursor)));
        return new Outcome.Success<>(Value.array(parts));
    }

    /**
     * {@code STRING_TRIM}: remove leading/trailing characters in exactly
     * the closed set U+0009–U+000D and U+0020 (tab, LF, VT, FF, CR, and
     * space — U+000B/U+000C are trimmed; U+00A0 is not). Interior
     * characters are never removed. Policy {@code NO_DEAL_FAILURE} —
     * never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid string argument; non-null
     * @return {@code Success} with the trimmed scalar sequence
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> stringTrim(SourceOrigin origin,
                                            UnicodeScalars.Valid input) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        int[] codePoints = codePointsOf(input);
        int first = 0;
        while (first < codePoints.length && isTrimScalar(codePoints[first])) {
            first++;
        }
        int last = codePoints.length;
        while (last > first && isTrimScalar(codePoints[last - 1])) {
            last--;
        }
        return new Outcome.Success<>(Value.string(
            new java.lang.String(codePoints, first, last - first)));
    }

    /** The closed trim set: U+0009–U+000D and U+0020, exactly. */
    private static boolean isTrimScalar(int codePoint) {
        return (codePoint >= 0x09 && codePoint <= 0x0D) || codePoint == 0x20;
    }

    // =========================================================================
    // Table
    // =========================================================================

    /**
     * {@code TABLE_KEYS}: the string keys of the semantic table in
     * first-insertion order (delete removes the order slot and
     * reinsertion appends it — the {@link SemanticTable} order
     * contract); non-string keys never exist on a semantic table. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param table  the declared table argument; non-null
     * @return {@code Success} with the array of string keys in
     *         first-insertion order
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> tableKeys(SourceOrigin origin,
                                           SemanticTable<Value> table) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(table, "table must not be null");
        List<Value> keys = new ArrayList<>();
        for (String key : table.keys()) {
            keys.add(Value.string(key));
        }
        return new Outcome.Success<>(Value.array(keys));
    }

    // =========================================================================
    // JSON
    // =========================================================================

    // Stable JSON_PARSE_SYNTAX defect-classification texts owned by this
    // component ({reason} metadata). The set is closed: every parse
    // defect classifies into exactly one of these texts.
    /** The defect class: a character that cannot appear at its position (value start, raw control). */
    public static final String REASON_UNEXPECTED_CHARACTER = "unexpected character";
    /** The defect class: a string reaching the end of input without its closing quote. */
    public static final String REASON_UNTERMINATED_STRING = "unterminated string";
    /** The defect class: an object reaching the end of input after a complete member. */
    public static final String REASON_UNTERMINATED_OBJECT = "unterminated object";
    /** The defect class: an array reaching the end of input after a complete element. */
    public static final String REASON_UNTERMINATED_ARRAY = "unterminated array";
    /** The defect class: an unknown escape or a malformed {@code \\uXXXX} escape. */
    public static final String REASON_INVALID_ESCAPE = "invalid escape";
    /** The defect class: a {@code \\uXXXX} surrogate escape not paired with its counterpart. */
    public static final String REASON_UNPAIRED_SURROGATE_ESCAPE = "unpaired surrogate escape";
    /** The defect class: a number violating the RFC-8259 grammar (not a leading-zero defect). */
    public static final String REASON_INVALID_NUMBER = "invalid number";
    /** The defect class: an integer part with a leading zero followed by another digit. */
    public static final String REASON_LEADING_ZERO = "leading zero";
    /** The defect class: an object member not starting with a string key. */
    public static final String REASON_MISSING_KEY = "missing key";
    /** The defect class: a member key not followed by {@code :}. */
    public static final String REASON_MISSING_COLON = "missing colon";
    /** The defect class: a member/element not followed by {@code ,} or its closer. */
    public static final String REASON_MISSING_COMMA = "missing comma";
    /** The defect class: content after the top-level value. */
    public static final String REASON_TRAILING_CONTENT = "trailing content";
    /** The defect class: the end of input where a value was required. */
    public static final String REASON_UNEXPECTED_END = "unexpected end of input";

    /**
     * The pinned expected text of the {@code STDLIB_CALL(JSON_STRINGIFY)}
     * rejection (the {@code JSON_TO_ERROR} row's second template): the
     * value kinds JSON encoding admits. Shared by the primitive's
     * projection and by the two target runtimes' stdlib realizations —
     * the three consumers are compared event-for-event.
     */
    public static final String JSON_STRINGIFY_EXPECTED =
        "string, number, boolean, or table";

    /** The internal parse failure: the defect class and its 1-based UTF-8 byte offset. */
    private static final class JsonParseFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        final String reason;
        final long oneBasedByteOffset;

        JsonParseFailure(String reason, long oneBasedByteOffset) {
            super(reason + " at byte " + oneBasedByteOffset);
            this.reason = reason;
            this.oneBasedByteOffset = oneBasedByteOffset;
        }
    }

    /** The internal stringify failure: the first declaration-order path and actual token. */
    private static final class JsonStringifyFailure extends RuntimeException {

        private static final long serialVersionUID = 1L;

        final String fieldPath;
        final String actual;

        JsonStringifyFailure(String fieldPath, String actual) {
            super("value at " + fieldPath + " is not JSON serializable: " + actual);
            this.fieldPath = fieldPath;
            this.actual = actual;
        }
    }

    /**
     * {@code JSON_PARSE}: RFC-8259 scalar-valid parse of the (already
     * scalar-valid) input; object order follows text; duplicate keys
     * keep the last value and the first position; a signed32 integer
     * lexical form becomes {@link Value.Int} ({@code -0} normalized to
     * {@code 0}) and every other numeric form becomes
     * {@link Value.Number}; a syntax defect fails with policy
     * {@code JSON_PARSE_SYNTAX} — E8001
     * {@code JSON parse error at position {oneBasedByteOffset}: {reason}}
     * with metadata {@code {oneBasedByteOffset}} (the defect's 1-based
     * UTF-8 byte offset) and {@code {reason}} (one of the
     * {@code REASON_*} defect-classification texts), origin = the
     * {@code STDLIB_CALL(JSON_PARSE)} call origin, no cause, active
     * frames. A successful parse whose top-level value is not a table
     * fails the {@code STDLIB_RETURN} boundary afterwards — that
     * boundary is the call machine's, never this primitive's.
     *
     * <p>Offset rule (owned here): the 1-based UTF-8 byte offset of the
     * defect position — the offending character for a character-class
     * defect (unexpected character, invalid escape, unpaired surrogate
     * escape, invalid number, leading zero, missing key/colon/comma,
     * trailing content), and one past the last input byte for an
     * end-of-input defect (unterminated string/object/array, unexpected
     * end of input). Multi-byte scalars count their full UTF-8 length.</p>
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param input  the scalar-valid JSON text argument; non-null
     * @return {@code Success} with the parsed value (the top-level table
     *         shape is the {@code STDLIB_RETURN} boundary's), or
     *         {@code Failure} with the {@code JSON_PARSE_SYNTAX}
     *         projection
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> jsonParse(SourceOrigin origin,
                                           UnicodeScalars.Valid input) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(input, "input must not be null");
        JsonReader reader = new JsonReader(input.carrier().codePoints().toArray());
        try {
            // RFC-8259: whitespace may precede and follow the top-level value.
            reader.skipWs();
            Value value = reader.parseValue();
            reader.skipWs();
            if (!reader.atEnd()) {
                throw reader.failure(REASON_TRAILING_CONTENT);
            }
            return new Outcome.Success<>(value);
        } catch (JsonParseFailure parseFailure) {
            return failOf(FailurePolicyId.JSON_PARSE_SYNTAX, 0, null, null,
                parseMetadata(parseFailure.oneBasedByteOffset, parseFailure.reason),
                origin);
        }
    }

    /**
     * {@code JSON_STRINGIFY}: finite acyclic JSON-shaped data
     * (string-keyed objects, arrays, and null/boolean/int/number/string
     * leaves); object fields in first-insertion order, arrays in index
     * order; RFC-8259 escaping (control characters U+0000–U+001F as the
     * named short escapes {@code \b \f \n \r \t} or {@code \\u00XX},
     * quote, backslash; surrogate pairs emitted as raw scalar UTF-8);
     * shortest round-trippable decimal number formatting
     * ({@code Double.toString}); the first failure in declaration order
     * fails via {@code JSON_TO_ERROR} — E8001
     * {@code unsupported type for JSON encoding: {actual}}
     * with the pinned expected text {@code string, number, boolean, or
     * table}, actual = the value's canonical actual-kind token, and
     * metadata {@code {fieldPath}}/{@code {actual}} (the field path
     * stays internal metadata), origin = the call origin. Unsupported
     * values, cycles, and nonfinite numbers fail here; acyclic finite
     * data never fails.
     *
     * <p>{@code {fieldPath}} spelling (owned here): a dot-separated
     * pre-order traversal from the root value — table fields append the
     * field name, array elements append the 0-based element index, and
     * the root itself has the empty path ({@code {"a": [1, fn]}} fails
     * at {@code a.1}). The first failure in declaration order wins:
     * table keys in first-insertion order, array elements in index
     * order, pre-order depth-first.</p>
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param table  the declared table argument; non-null
     * @return {@code Success} with the RFC-8259 JSON text as a valid
     *         scalar string, or {@code Failure} with the first
     *         declaration-order {@code JSON_TO_ERROR} projection
     * @throws NullPointerException if any argument is null
     */
    public static Outcome<Value> jsonStringify(SourceOrigin origin,
                                               SemanticTable<Value> table) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(table, "table must not be null");
        StringBuilder out = new StringBuilder();
        Set<Object> path = Collections.newSetFromMap(new IdentityHashMap<>());
        try {
            stringifyTable(out, table, "", path);
        } catch (JsonStringifyFailure stringifyFailure) {
            // The STDLIB_CALL(JSON_STRINGIFY) rejection: row template 1
            // (the corpus-aligned visible text); the walker's fieldPath
            // stays internal metadata.
            return failOf(FailurePolicyId.JSON_TO_ERROR, 1, JSON_STRINGIFY_EXPECTED,
                stringifyFailure.actual,
                jsonToErrorMetadata(stringifyFailure.fieldPath, stringifyFailure.actual),
                origin);
        }
        return new Outcome.Success<>(Value.string(out.toString()));
    }

    /** Serializes one table (object) with cycle detection and first-insertion order. */
    private static void stringifyTable(StringBuilder out, SemanticTable<Value> table,
                                       String fieldPath, Set<Object> path) {
        if (!path.add(table)) {
            throw new JsonStringifyFailure(fieldPath,
                ActualKind.canonicalToken(ActualKind.TABLE, null));
        }
        out.append('{');
        List<String> keys = table.keys();
        for (int i = 0; i < keys.size(); i++) {
            String key = keys.get(i);
            if (!(UnicodeScalars.validate(key) instanceof UnicodeScalars.Valid)) {
                throw new Defect("a semantic-table key must be a valid scalar sequence "
                    + "(keys are identifier-derived); the key at slot " + i
                    + " is not — a producer defect, never a projection");
            }
            if (i > 0) {
                out.append(',');
            }
            appendJsonString(out, key);
            out.append(':');
            SemanticTable.Lookup<Value> lookup = table.get(key);
            if (!(lookup instanceof SemanticTable.Lookup.Present<Value> present)) {
                throw new Defect("a table key returned by keys() is always present; got "
                    + "Missing for '" + key + "' — a producer defect, never a projection");
            }
            stringifyValue(out, present.value(),
                fieldPath.isEmpty() ? key : fieldPath + "." + key, path);
        }
        out.append('}');
        path.remove(table);
    }

    /** Serializes one array with cycle detection and index order. */
    private static void stringifyArray(StringBuilder out, SemanticArray<Value> elements,
                                       String fieldPath, Set<Object> path) {
        if (!path.add(elements)) {
            throw new JsonStringifyFailure(fieldPath,
                ActualKind.canonicalToken(ActualKind.ARRAY, null));
        }
        out.append('[');
        for (int i = 0; i < elements.size(); i++) {
            if (i > 0) {
                out.append(',');
            }
            stringifyValue(out, elements.elementAt(i),
                fieldPath.isEmpty() ? Integer.toString(i) : fieldPath + "." + i, path);
        }
        out.append(']');
        path.remove(elements);
    }

    /** Serializes one value: the first declaration-order failure wins (pre-order). */
    private static void stringifyValue(StringBuilder out, Value value, String fieldPath,
                                       Set<Object> path) {
        switch (value) {
            case Value.Null ignored -> out.append("null");
            case Value.Bool bool -> out.append(bool.value() ? "true" : "false");
            case Value.Int intValue -> out.append(Integer.toString(intValue.value()));
            case Value.Number number -> {
                if (!Double.isFinite(number.value())) {
                    throw new JsonStringifyFailure(fieldPath,
                        ActualKind.canonicalToken(ActualKind.NUMBER, null));
                }
                out.append(Double.toString(number.value()));
            }
            case Value.String string -> {
                if (string.scalar() instanceof UnicodeScalars.Invalid) {
                    throw new JsonStringifyFailure(fieldPath,
                        ActualKind.canonicalToken(ActualKind.INVALID_UNICODE, null));
                }
                appendJsonString(out, ((UnicodeScalars.Valid) string.scalar()).carrier());
            }
            case Value.Table table -> stringifyTable(out, table.table(), fieldPath, path);
            case Value.Array array ->
                stringifyArray(out, array.elements(), fieldPath, path);
            case Value.Other other -> throw new JsonStringifyFailure(fieldPath,
                ActualKind.canonicalToken(other.kind(), other.classId()));
        }
    }

    /**
     * RFC-8259 string escaping: quote and backslash escaped; the named
     * short escapes {@code \b \f \n \r \t}; every other control scalar
     * (U+0000–U+001F) as {@code \\u00XX} (lowercase hex); every other
     * scalar — surrogate pairs included — emitted as raw scalar UTF-8.
     */
    private static void appendJsonString(StringBuilder out, String carrier) {
        out.append('"');
        for (int i = 0; i < carrier.length(); ) {
            int codePoint = carrier.codePointAt(i);
            i += Character.charCount(codePoint);
            switch (codePoint) {
                case '"' -> out.append("\\\"");
                case '\\' -> out.append("\\\\");
                case '\b' -> out.append("\\b");
                case '\f' -> out.append("\\f");
                case '\n' -> out.append("\\n");
                case '\r' -> out.append("\\r");
                case '\t' -> out.append("\\t");
                default -> {
                    if (codePoint < 0x20) {
                        out.append(String.format("\\u%04x", codePoint));
                    } else {
                        out.appendCodePoint(codePoint);
                    }
                }
            }
        }
        out.append('"');
    }

    /**
     * The RFC-8259 recursive-descent reader over the input's code points,
     * tracking the 1-based UTF-8 byte offset of the current scan position.
     */
    private static final class JsonReader {

        private final int[] codePoints;
        private int position;
        private long bytesConsumed;

        JsonReader(int[] codePoints) {
            this.codePoints = codePoints;
        }

        boolean atEnd() {
            return position >= codePoints.length;
        }

        int peek() {
            return position < codePoints.length ? codePoints[position] : -1;
        }

        void advance() {
            bytesConsumed += utf8Length(codePoints[position]);
            position++;
        }

        /** The 1-based UTF-8 byte offset of the current scan position. */
        long offsetOfCurrent() {
            return bytesConsumed + 1;
        }

        JsonParseFailure failure(String reason) {
            return new JsonParseFailure(reason, offsetOfCurrent());
        }

        void skipWs() {
            while (!atEnd() && isWs(peek())) {
                advance();
            }
        }

        Value parseValue() {
            if (atEnd()) {
                throw failure(REASON_UNEXPECTED_END);
            }
            int c = peek();
            return switch (c) {
                case '{' -> parseObject();
                case '[' -> parseArray();
                case '"' -> Value.string(parseString());
                case 't' -> parseLiteral("true", new Value.Bool(true));
                case 'f' -> parseLiteral("false", new Value.Bool(false));
                case 'n' -> parseLiteral("null", Value.Null.INSTANCE);
                default -> {
                    if (c == '-' || (c >= '0' && c <= '9')) {
                        yield parseNumber();
                    }
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                }
            };
        }

        Value parseLiteral(String word, Value value) {
            for (int i = 0; i < word.length(); i++) {
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                if (peek() != word.codePointAt(i)) {
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                }
                advance();
            }
            return value;
        }

        Value parseObject() {
            advance(); // '{'
            SemanticTable<Value> table = new SemanticTable<>();
            skipWs();
            if (!atEnd() && peek() == '}') {
                advance();
                return new Value.Table(table);
            }
            while (true) {
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                if (peek() != '"') {
                    throw failure(REASON_MISSING_KEY);
                }
                String key = parseString();
                skipWs();
                if (atEnd() || peek() != ':') {
                    throw failure(REASON_MISSING_COLON);
                }
                advance(); // ':'
                skipWs();
                Value value = parseValue();
                // Duplicate keys keep the last value and the first
                // position: put replaces an existing slot in place and
                // appends only new keys (SemanticTable order contract).
                table.put(key, value);
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_OBJECT);
                }
                int c = peek();
                if (c == ',') {
                    advance();
                    continue;
                }
                if (c == '}') {
                    advance();
                    return new Value.Table(table);
                }
                throw failure(REASON_MISSING_COMMA);
            }
        }

        Value parseArray() {
            advance(); // '['
            List<Value> elements = new ArrayList<>();
            skipWs();
            if (!atEnd() && peek() == ']') {
                advance();
                return Value.array(elements);
            }
            while (true) {
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNEXPECTED_END);
                }
                elements.add(parseValue());
                skipWs();
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_ARRAY);
                }
                int c = peek();
                if (c == ',') {
                    advance();
                    continue;
                }
                if (c == ']') {
                    advance();
                    return Value.array(elements);
                }
                throw failure(REASON_MISSING_COMMA);
            }
        }

        String parseString() {
            advance(); // '"'
            StringBuilder result = new StringBuilder();
            while (true) {
                if (atEnd()) {
                    throw failure(REASON_UNTERMINATED_STRING);
                }
                int c = peek();
                if (c == '"') {
                    advance();
                    return result.toString();
                }
                if (c == '\\') {
                    advance(); // backslash
                    if (atEnd()) {
                        throw failure(REASON_UNTERMINATED_STRING);
                    }
                    int escaped = peek();
                    switch (escaped) {
                        case '"' -> {
                            advance();
                            result.append('"');
                        }
                        case '\\' -> {
                            advance();
                            result.append('\\');
                        }
                        case '/' -> {
                            advance();
                            result.append('/');
                        }
                        case 'b' -> {
                            advance();
                            result.append('\b');
                        }
                        case 'f' -> {
                            advance();
                            result.append('\f');
                        }
                        case 'n' -> {
                            advance();
                            result.append('\n');
                        }
                        case 'r' -> {
                            advance();
                            result.append('\r');
                        }
                        case 't' -> {
                            advance();
                            result.append('\t');
                        }
                        case 'u' -> {
                            advance(); // 'u'
                            int codePoint = parseHex4();
                            if (Character.isHighSurrogate((char) codePoint)) {
                                // A high surrogate must pair with a
                                // following \\uXXXX low surrogate escape.
                                if (atEnd() || peek() != '\\') {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                advance(); // backslash
                                if (atEnd() || peek() != 'u') {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                advance(); // 'u'
                                int low = parseHex4();
                                if (!Character.isLowSurrogate((char) low)) {
                                    throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                                }
                                result.appendCodePoint(Character.toCodePoint(
                                    (char) codePoint, (char) low));
                            } else if (Character.isLowSurrogate((char) codePoint)) {
                                throw failure(REASON_UNPAIRED_SURROGATE_ESCAPE);
                            } else {
                                result.appendCodePoint(codePoint);
                            }
                        }
                        default -> throw failure(REASON_INVALID_ESCAPE);
                    }
                } else if (c < 0x20) {
                    // A raw control character is never allowed unescaped.
                    throw failure(REASON_UNEXPECTED_CHARACTER);
                } else {
                    advance();
                    result.appendCodePoint(c);
                }
            }
        }

        /** Exactly four hex digits; a non-hex digit or end of input is an invalid escape. */
        int parseHex4() {
            int value = 0;
            for (int i = 0; i < 4; i++) {
                if (atEnd()) {
                    throw failure(REASON_INVALID_ESCAPE);
                }
                int digit = hexDigit(peek());
                if (digit < 0) {
                    throw failure(REASON_INVALID_ESCAPE);
                }
                advance();
                value = value * 16 + digit;
            }
            return value;
        }

        Value parseNumber() {
            int start = position;
            boolean negative = false;
            if (peek() == '-') {
                negative = true;
                advance();
            }
            if (atEnd()) {
                throw failure(REASON_INVALID_NUMBER);
            }
            int c = peek();
            if (c < '0' || c > '9') {
                throw failure(REASON_INVALID_NUMBER);
            }
            boolean integerForm = true;
            if (c == '0') {
                advance();
                if (!atEnd() && isDigit(peek())) {
                    throw failure(REASON_LEADING_ZERO);
                }
            } else {
                advance();
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            if (!atEnd() && peek() == '.') {
                integerForm = false;
                advance();
                if (atEnd() || !isDigit(peek())) {
                    throw failure(REASON_INVALID_NUMBER);
                }
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            if (!atEnd() && (peek() == 'e' || peek() == 'E')) {
                integerForm = false;
                advance();
                if (!atEnd() && (peek() == '+' || peek() == '-')) {
                    advance();
                }
                if (atEnd() || !isDigit(peek())) {
                    throw failure(REASON_INVALID_NUMBER);
                }
                while (!atEnd() && isDigit(peek())) {
                    advance();
                }
            }
            String text = codePointSlice(codePoints, start, position);
            if (integerForm) {
                // The signed32 integer lexical form: RFC-8259 integer
                // grammar with the leading-zero rules (already enforced),
                // mathematically within [-2147483648, 2147483647]; -0
                // normalizes to 0. Everything else is a Number.
                int digitsStart = start + (negative ? 1 : 0);
                int significantStart = digitsStart;
                while (significantStart < position
                        && codePoints[significantStart] == '0') {
                    significantStart++;
                }
                int significantLength = Math.max(1, position - significantStart);
                boolean outOfRange;
                if (significantLength > 10) {
                    outOfRange = true;
                } else if (significantLength == 10) {
                    long significant = 0L;
                    for (int i = significantStart; i < significantStart + 10; i++) {
                        significant = significant * 10 + (codePoints[i] - '0');
                    }
                    long limit = negative ? 2147483648L : 2147483647L;
                    outOfRange = significant > limit;
                } else {
                    outOfRange = false;
                }
                if (!outOfRange) {
                    // Exact digit accumulation: at most 10 significant
                    // digits, so the long value is exact; "-0" yields 0.
                    long value = 0L;
                    for (int i = digitsStart; i < position; i++) {
                        value = value * 10 + (codePoints[i] - '0');
                    }
                    if (negative) {
                        value = -value;
                    }
                    return new Value.Int((int) value);
                }
            }
            return new Value.Number(CanonicalJson.decodeDecimal(text));
        }
    }

    private static boolean isWs(int codePoint) {
        return codePoint == 0x20 || codePoint == 0x09
            || codePoint == 0x0A || codePoint == 0x0D;
    }

    private static boolean isDigit(int codePoint) {
        return codePoint >= '0' && codePoint <= '9';
    }

    private static int hexDigit(int codePoint) {
        if (codePoint >= '0' && codePoint <= '9') {
            return codePoint - '0';
        }
        if (codePoint >= 'a' && codePoint <= 'f') {
            return codePoint - 'a' + 10;
        }
        if (codePoint >= 'A' && codePoint <= 'F') {
            return codePoint - 'A' + 10;
        }
        return -1;
    }

    /** The UTF-8 byte length of one Unicode scalar value. */
    private static int utf8Length(int codePoint) {
        return codePoint < 0x80 ? 1 : codePoint < 0x800 ? 2 : codePoint < 0x10000 ? 3 : 4;
    }

    // =========================================================================
    // Math
    // =========================================================================

    /**
     * {@code MATH_FLOOR}: IEEE floor, returned as Number. Policy
     * {@code NO_DEAL_FAILURE} — never fails ({@code NaN} → {@code NaN},
     * {@code ±Infinity} → {@code ±Infinity}).
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param value  the declared number argument; non-null origin
     * @return {@code Success} with the IEEE floor as Number
     */
    public static Outcome<Value> mathFloor(SourceOrigin origin, double value) {
        Objects.requireNonNull(origin, "origin must not be null");
        return new Outcome.Success<>(new Value.Number(Math.floor(value)));
    }

    /**
     * {@code MATH_CEIL}: IEEE ceiling, returned as Number. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param value  the declared number argument
     * @return {@code Success} with the IEEE ceiling as Number
     */
    public static Outcome<Value> mathCeil(SourceOrigin origin, double value) {
        Objects.requireNonNull(origin, "origin must not be null");
        return new Outcome.Success<>(new Value.Number(Math.ceil(value)));
    }

    /**
     * {@code MATH_SQRT}: IEEE sqrt; a negative non-NaN input fails
     * {@code SQRT_NEGATIVE} (E8001 {@code sqrt of negative number} at
     * the operation origin); NaN returns NaN and {@code -0.0} returns
     * {@code -0.0} (IEEE). The failure carries the negative operand in
     * its {@code actual} field as the canonical IEEE-754 hex-float
     * spelling ({@link CanonicalJson#numberHex}).
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param value  the declared number argument
     * @return {@code Success} with the IEEE sqrt as Number, or
     *         {@code Failure} with the {@code SQRT_NEGATIVE} projection
     */
    public static Outcome<Value> mathSqrt(SourceOrigin origin, double value) {
        Objects.requireNonNull(origin, "origin must not be null");
        if (value < 0) {
            return failOf(FailurePolicyId.SQRT_NEGATIVE, 0, null,
                CanonicalJson.numberHex(value), new LinkedHashMap<>(), origin);
        }
        return new Outcome.Success<>(new Value.Number(Math.sqrt(value)));
    }

    /**
     * {@code MATH_ABS_INT}: signed32 absolute value;
     * {@code -2147483648} fails {@code INT32_RESULT} (E8004
     * {@code int out of safe range} at the call origin) — the exact long
     * intermediate makes the overflow visible before any narrowing.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param value  the declared int argument
     * @return {@code Success} with the signed32 absolute value, or
     *         {@code Failure} with the E8004 range projection
     */
    public static Outcome<Value> mathAbsInt(SourceOrigin origin, int value) {
        Objects.requireNonNull(origin, "origin must not be null");
        long absolute = value < 0 ? -(long) value : value;
        return int32Gate(absolute, origin);
    }

    /**
     * {@code MATH_ABS_NUMBER}: IEEE absolute value ({@code -0.0} →
     * {@code +0.0}, {@code NaN} → {@code NaN},
     * {@code -Infinity} → {@code +Infinity}). Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param value  the declared number argument
     * @return {@code Success} with the IEEE absolute value as Number
     */
    public static Outcome<Value> mathAbsNumber(SourceOrigin origin, double value) {
        Objects.requireNonNull(origin, "origin must not be null");
        return new Outcome.Success<>(new Value.Number(Math.abs(value)));
    }

    /**
     * {@code MATH_MIN_INT}: the selected signed32 operand; equal
     * operands return that operand value. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param a      the first declared int argument
     * @param b      the second declared int argument
     * @return {@code Success} with the selected signed32 operand
     */
    public static Outcome<Value> mathMinInt(SourceOrigin origin, int a, int b) {
        Objects.requireNonNull(origin, "origin must not be null");
        return new Outcome.Success<>(new Value.Int(Math.min(a, b)));
    }

    /**
     * {@code MATH_MAX_INT}: the selected signed32 operand; equal
     * operands return that operand value. Policy
     * {@code NO_DEAL_FAILURE} — never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param a      the first declared int argument
     * @param b      the second declared int argument
     * @return {@code Success} with the selected signed32 operand
     */
    public static Outcome<Value> mathMaxInt(SourceOrigin origin, int a, int b) {
        Objects.requireNonNull(origin, "origin must not be null");
        return new Outcome.Success<>(new Value.Int(Math.max(a, b)));
    }

    /**
     * {@code TIME_NOW_MILLIS} — the K7 {@code std.time}/{@code nowMillis}
     * operation: the target-clock reading returned as a
     * {@link Value.Number} (epoch milliseconds — an exact double for
     * contemporary readings). The operation has no parameter boundary and
     * its single terminal is the declared {@code int} {@code STDLIB_RETURN}
     * boundary with policy {@code INT32_RESULT}: a reading outside
     * {@code [-2147483648, 2147483647]} fails E8004
     * {@code int out of safe range} at the call origin — exactly what
     * every contemporary epoch-millisecond reading produces. Policy
     * {@code INT32_RESULT}; the reading itself never fails.
     *
     * @param origin the {@code STDLIB_CALL} operation origin; non-null
     * @param clock  the injected clock seam; non-null
     * @return {@code Success} with the target-clock reading as a number
     */
    public static Outcome<Value> timeNowMillis(SourceOrigin origin, Clock clock) {
        Objects.requireNonNull(origin, "origin must not be null");
        Objects.requireNonNull(clock, "clock must not be null");
        return new Outcome.Success<>(new Value.Number((double) clock.nowMillis()));
    }

    // =========================================================================
    // Scalar-sequence helpers
    // =========================================================================

    /** The code points of a valid scalar sequence in scalar order. */
    private static int[] codePointsOf(UnicodeScalars.Valid valid) {
        return valid.carrier().codePoints().toArray();
    }

    /** True iff {@code needle} occurs at {@code offset} of {@code haystack}. */
    private static boolean matchAt(int[] haystack, int[] needle, int offset) {
        for (int i = 0; i < needle.length; i++) {
            if (haystack[offset + i] != needle[i]) {
                return false;
            }
        }
        return true;
    }

    /**
     * The first occurrence of {@code needle} in {@code haystack} at or
     * after {@code fromIndex}, or {@code -1} — a literal scalar
     * subsequence search.
     */
    private static int indexOfSubsequence(int[] haystack, int[] needle, int fromIndex) {
        if (needle.length == 0) {
            return fromIndex <= haystack.length ? fromIndex : -1;
        }
        for (int i = Math.max(0, fromIndex); i + needle.length <= haystack.length; i++) {
            if (matchAt(haystack, needle, i)) {
                return i;
            }
        }
        return -1;
    }

    /** Appends code points to the builder in order. */
    private static void appendCodePoints(StringBuilder builder, int[] codePoints) {
        for (int codePoint : codePoints) {
            builder.appendCodePoint(codePoint);
        }
    }

    /** The UTF-16 text of the code-point slice {@code [start, end)}. */
    private static String codePointSlice(int[] codePoints, int start, int end) {
        return new java.lang.String(codePoints, start, end - start);
    }
}
