package deal.test;

import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContainerOpsExecutor;
import deal.semantic.ir.ContainerOpsExecutor.BodyRunner;
import deal.semantic.ir.ContainerOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ContainerOpsExecutor.BoundaryResult;
import deal.semantic.ir.ContainerOpsExecutor.Defect;
import deal.semantic.ir.ContainerOpsExecutor.LoopLoadResolver;
import deal.semantic.ir.ContainerOpsExecutor.OpFailure;
import deal.semantic.ir.ContainerOpsExecutor.Outcome;
import deal.semantic.ir.ContainerOpsExecutor.Value;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.UnicodeScalars;
import deal.semantic.ir.ValueId;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Verifies the ISSUE-0384 component C3 surface:
 * {@link ContainerOpsExecutor} as the single op-level execution form of
 * the six container/string operations of {@code deal.semantic-ir/1} —
 * {@code TABLE_NEW}, {@code ARRAY_NEW}, {@code MEMBER_READ},
 * {@code ARRAY_LENGTH}, {@code STRING_CONCAT}, and
 * {@code FOR_EACH(STRING_SCALARS)} — over the semantic value model
 * ({@link SemanticTable} D4, {@link UnicodeScalars} D5, the ordered
 * {@link SemanticArray} element list) with the value lookup for
 * payload-referenced prior steps, the {@code BoundaryCheckRunner}
 * delegate seam (D3: {@code (BoundaryPayload, Value) → Pass | Fail}),
 * the body-runner callback seam, and the loop-binding load-resolution
 * rule in the {@code FOR_EACH} protocol (D1: a load of the loop binding
 * carries the payload's initial generation and resolves to
 * initial + current iteration index at execution; the payload is never
 * rewritten).
 *
 * <p>Pinned cases (wiki Verification 4 and the task criteria):
 * <ol>
 *   <li>{@code TABLE_NEW}: entries stored in source order; duplicate keys
 *       keep the first position and the last value; every entry value
 *       resolved exactly once in source order; empty entries allocate an
 *       empty table.</li>
 *   <li>{@code ARRAY_NEW}: all element values resolve before any
 *       boundary child runs; children run strictly in payload order; a
 *       fixture delegate failing the second child fails the op with that
 *       child's failure, publishes no array, and never runs the third
 *       child (the first child's pass stays observable in the delegate
 *       call order); all-pass allocates only after the last child and the
 *       array holds the delegate-published checked values in source
 *       order.</li>
 *   <li>{@code MEMBER_READ}: the read completes before the child starts
 *       (the delegate receives the read outcome); present values are
 *       checked, missing→null for a nullable descriptor, E8001
 *       {@code expected {expected}, got missing} for non-nullable
 *       missing, and present null projects {@code got null} — distinct
 *       from missing (D4) — all through a fixture delegate wired to the
 *       real {@link BoundaryExecutor} (the E4 production delegate), the
 *       executor pinning only the orchestration; the receiver resolves
 *       exactly once.</li>
 *   <li>{@code ARRAY_LENGTH}: the signed32 element count with the
 *       receiver resolved exactly once.</li>
 *   <li>{@code STRING_CONCAT}: fragments resolve and concatenate in
 *       payload order (a surrogate pair stays one scalar); an
 *       {@code Invalid} operand is a producer defect, never a second
 *       projection.</li>
 *   <li>{@code FOR_EACH(STRING_SCALARS)}: an {@code Invalid} iterable
 *       runs zero body steps and fails with the E8001 invalid-string
 *       projection (code, template, expected {@code string}, actual kind
 *       {@code invalid-unicode}, policy {@code TYPE_DESCRIPTOR}, for-of
 *       origin — instantiated through the registry row and
 *       byte-identical to {@link BoundaryExecutor}'s classification
 *       projection for the same view); a valid multi-scalar iterable
 *       yields one single-scalar string per iteration in scalar order,
 *       each bound to a fresh generation (initial + iteration index); a
 *       body {@code BINDING_LOAD} of the loop binding carrying the
 *       payload's initial generation resolves per iteration to
 *       initial + iteration index; an empty string yields zero
 *       iterations.</li>
 *   <li>Combined dependency step: {@code STRING_CONCAT} fragments (C1)
 *       feed {@code TABLE_NEW} entries (C2), and {@code FOR_EACH} over a
 *       multi-scalar string accumulates each yielded scalar into a
 *       {@code SemanticTable} (C3) — the accumulated order and values
 *       fail this test if C1's scalar model or C2's order model is
 *       broken.</li>
 *   <li>Fail-closed defects: wrong op kinds/policies, unresolvable prior
 *       steps, wrong-kind receivers/iterables/fragments, element-boundary
 *       count mismatches, wrong-kind/unparented boundary children,
 *       non-{@code STRING_SCALARS} modes, and a loop-binding load
 *       carrying a non-initial generation are producer defects, never
 *       DEAL projections; null arguments throw the documented NPEs.</li>
 *   <li>Determinism: repeated executions with equal inputs produce equal
 *       results (the executor is stateless).</li>
 * </ol>
 */
public class ContainerOpsExecutorTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static void expectDefect(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected ContainerOpsExecutor.Defect for " + what
                + ", but no exception was raised");
        } catch (Defect expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected ContainerOpsExecutor.Defect for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    private static void expectNpe(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected NullPointerException for " + what + ", but no exception was raised");
        } catch (NullPointerException expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected NullPointerException for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    // =========================================================================
    // Semantic-id and op builders (the SemanticIrValidatorTest discipline)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("corpus.container");
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor STRING = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor TABLE = RuntimeDescriptor.Table.INSTANCE;
    private static final RuntimeDescriptor NULLABLE_INT = new RuntimeDescriptor.Nullable(INT);

    private static int nextOpId = 1;
    private static int nextValueId = 1;
    private static int nextColumn = 1;

    private static OpId nextOpId() {
        return new OpId(MOD, nextOpId++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextValueId++);
    }

    /** A distinct USER origin per op so origin identity is provable. */
    private static SourceOrigin originAt(OpId parent, int startColumn) {
        return new SourceOrigin("corpus.deal",
            new SourceSpan("corpus.deal", 1, startColumn, 1, startColumn + 3),
            SourceOriginKind.USER, new AnchorId(0), parent);
    }

    private static SourceOrigin nextOrigin(OpId parent) {
        int column = nextColumn;
        nextColumn += 10;
        return originAt(parent, column);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWithId(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, nextOrigin(parent), result, resultType, List.of(),
            List.of(), payload, policy, contract);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        return opWithId(nextOpId(), kind, payload, result, resultType, policy, parent);
    }

    private static SemanticOp boundaryChild(OpId parentId, BoundaryKind kind,
            RuntimeDescriptor descriptor, FailurePolicyId policy) {
        return op(SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, nextValue(),
                new BoundaryRealization.RuntimeValidation("runtime-validation")),
            null, null, policy, parentId);
    }

    private static SemanticOp forOfOp(ValueId iterable, BindingId binding, long generation,
            IterationMode mode, FailurePolicyId policy) {
        return op(SemanticOpKind.FOR_EACH,
            new KindPayload.ForEachPayload(mode, iterable, binding, generation, new BlockId(1)),
            null, null, policy, null);
    }

    private static SemanticOp tableNewOp(List<KindPayload.TableEntry> entries,
            FailurePolicyId policy) {
        return op(SemanticOpKind.TABLE_NEW, new KindPayload.TableNewPayload(entries),
            nextValue(), TABLE, policy, null);
    }

    private static SemanticOp concatOp(List<ValueId> fragments, FailurePolicyId policy) {
        return op(SemanticOpKind.STRING_CONCAT,
            new KindPayload.StringConcatPayload(fragments), nextValue(), STRING, policy, null);
    }

    private static SemanticOp arrayLengthOp(ValueId arrayValue, FailurePolicyId policy) {
        return op(SemanticOpKind.ARRAY_LENGTH,
            new KindPayload.ArrayLengthPayload(arrayValue), nextValue(), INT, policy, null);
    }

    private static Map<String, String> metadataOf(String key, String value) {
        Map<String, String> metadata = new LinkedHashMap<>();
        metadata.put(key, value);
        return metadata;
    }

    private static String carrier(Value value) {
        return ((UnicodeScalars.Valid) ((Value.String) value).scalar()).carrier();
    }

    private static Value present(SemanticTable<Value> table, String key) {
        return switch (table.get(key)) {
            case SemanticTable.Lookup.Present<Value> value -> value.value();
            case SemanticTable.Lookup.Missing<Value> ignored -> null;
        };
    }

    // =========================================================================
    // Fixtures: the recording value lookup and the delegate stand-ins (D3)
    // =========================================================================

    /** A value lookup that records every resolution in the shared log. */
    private static final class RecordingValues extends AbstractMap<ValueId, Value> {

        private final Map<ValueId, Value> inner;
        private final List<String> log;

        RecordingValues(Map<ValueId, Value> inner, List<String> log) {
            this.inner = inner;
            this.log = log;
        }

        @Override
        public Set<Entry<ValueId, Value>> entrySet() {
            return inner.entrySet();
        }

        @Override
        public Value get(Object key) {
            Value value = inner.get(key);
            log.add("resolve " + key + (value == null ? " (unresolved)" : ""));
            return value;
        }
    }

    /**
     * A pass-through/fail-first fixture delegate (D3: E3's unit tests use
     * fixtures; E4 wires {@link BoundaryExecutor}): records every call in
     * the shared log (the call order proves the payload order), returns
     * {@code Pass(input)} (or the pinned republished value) and fails
     * child index {@code failAtIndex} with the supplied failure.
     */
    private static final class ScriptedDelegate implements BoundaryCheckRunner {

        private final List<String> log;
        private final int failAtIndex;
        private final BoundaryFailure failure;
        private final Value republished;
        private int calls = 0;

        ScriptedDelegate(List<String> log, int failAtIndex, BoundaryFailure failure,
                         Value republished) {
            this.log = log;
            this.failAtIndex = failAtIndex;
            this.failure = failure;
            this.republished = republished;
        }

        @Override
        public BoundaryResult run(KindPayload.BoundaryPayload boundary, Value input) {
            int index = calls++;
            log.add("child[" + index + "] " + boundary.kind() + " <- " + input.actualKind().token());
            if (index == failAtIndex) {
                return new BoundaryResult.Fail(failure);
            }
            return new BoundaryResult.Pass(republished != null ? republished : input);
        }
    }

    /**
     * The E4 production-delegate stand-in: every check runs through the
     * real {@link BoundaryExecutor} (the closed 11-policy projection
     * engine), adapted from the executor's {@link Value} view to the
     * boundary's {@link BoundaryValueView}. The child's policy is
     * derived from the closed boundary-assignment table — the
     * descriptor-kind rule for {@code CONTEXTUAL_TABLE_READ} cells. This
     * proves the delegate seam accepts the production executor and that
     * the executor itself never performs a boundary projection.
     */
    private static BoundaryCheckRunner realProjectionDelegate(List<String> log) {
        return (boundary, input) -> {
            if (log != null) {
                log.add("child " + boundary.kind() + " <- " + input.actualKind().token());
            }
            FailurePolicyId policy = boundary.descriptor() instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
            BoundaryOutcome outcome = BoundaryExecutor.check(policy, boundary.descriptor(),
                valueView(input), BoundaryContext.none());
            return switch (outcome) {
                case BoundaryOutcome.Pass pass ->
                    new BoundaryResult.Pass(publishValue(pass.value(), input));
                case BoundaryOutcome.Fail fail -> new BoundaryResult.Fail(fail.failure());
            };
        };
    }

    private static BoundaryValueView valueView(Value value) {
        return switch (value) {
            case Value.Null ignored -> BoundaryValueView.of(ActualKind.NULL);
            case Value.Bool bool -> BoundaryValueView.of(ActualKind.BOOLEAN);
            case Value.Int intValue -> BoundaryValueView.ofInt(intValue.value());
            case Value.Number number -> BoundaryValueView.ofNumber(number.value());
            case Value.String string -> BoundaryValueView.of(string.scalar().actualKind());
            case Value.Bytes ignored -> BoundaryValueView.of(ActualKind.BYTES);
            case Value.Table ignored -> BoundaryValueView.of(ActualKind.TABLE);
            case Value.Array ignored -> BoundaryValueView.of(ActualKind.ARRAY);
            case Value.Missing ignored -> BoundaryValueView.of(ActualKind.MISSING);
        };
    }

    /**
     * The boundary's published value: a passing boundary never copies or
     * converts — except the pinned missing→null mapping, which the
     * executor's closed table assigns to the delegate and which the
     * published null view reflects.
     */
    private static Value publishValue(BoundaryValueView view, Value input) {
        return view.kind() == ActualKind.NULL ? Value.Null.INSTANCE : input;
    }

    // =========================================================================
    // 1. The closed value view
    // =========================================================================

    static void testValueViewClassification() {
        System.out.println("-- the closed value view renders the canonical actual kinds --");

        check(Value.Null.INSTANCE.actualKind() == ActualKind.NULL,
            "Null renders NULL");
        check(new Value.Bool(true).actualKind() == ActualKind.BOOLEAN,
            "Bool renders BOOLEAN");
        check(new Value.Int(-2147483648).actualKind() == ActualKind.INT,
            "Int renders INT");
        check(new Value.Number(Double.NaN).actualKind() == ActualKind.NUMBER,
            "Number renders NUMBER");
        check(Value.string("x").actualKind() == ActualKind.STRING,
            "a valid String renders STRING");
        check(Value.string("\uD800").actualKind() == ActualKind.INVALID_UNICODE,
            "a lone-surrogate String renders INVALID_UNICODE (the classification "
                + "travels with the value)");
        check(Value.string(UnicodeScalars.Invalid.INSTANCE).actualKind()
                == ActualKind.INVALID_UNICODE,
            "an explicit Invalid classification renders INVALID_UNICODE");
        check(new Value.Table(new SemanticTable<>()).actualKind() == ActualKind.TABLE,
            "Table renders TABLE");
        check(new Value.Array(SemanticArray.of()).actualKind() == ActualKind.ARRAY,
            "Array renders ARRAY");
        check(Value.Missing.INSTANCE.actualKind() == ActualKind.MISSING,
            "Missing renders the schema's internal MISSING, never Java null");

        check("invalid-unicode".equals(ActualKind.canonicalToken(ActualKind.INVALID_UNICODE, null)),
            "the INVALID_UNICODE canonical token is the pinned invalid-unicode text");
        check("missing".equals(ActualKind.canonicalToken(ActualKind.MISSING, null)),
            "the MISSING canonical token is the pinned missing text");

        expectNpe(() -> Value.string((UnicodeScalars.ScalarString) null),
            "Value.string((ScalarString) null)");
        expectNpe(() -> new Value.String(null), "new Value.String(null)");
        expectNpe(() -> new Value.Table(null), "new Value.Table(null)");
        expectNpe(() -> new Value.Array(null), "new Value.Array(null)");
    }

    // =========================================================================
    // 2. TABLE_NEW
    // =========================================================================

    static void testTableNew() {
        System.out.println("-- TABLE_NEW: source-order stores, duplicate keys, resolution order --");

        ValueId va1 = nextValue();
        ValueId vb = nextValue();
        ValueId va2 = nextValue();
        ValueId vc = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(va1, Value.string("a1"));
        values.put(vb, Value.string("b"));
        values.put(va2, Value.string("a2"));
        values.put(vc, Value.string("c"));

        List<String> log = new ArrayList<>();
        RecordingValues recording = new RecordingValues(values, log);
        SemanticOp tableOp = tableNewOp(List.of(
            new KindPayload.TableEntry("a", va1),
            new KindPayload.TableEntry("b", vb),
            new KindPayload.TableEntry("a", va2),
            new KindPayload.TableEntry("c", vc)), FailurePolicyId.NO_DEAL_FAILURE);
        SemanticTable<Value> table = ContainerOpsExecutor.executeTableNew(tableOp, recording);

        check(table.keys().equals(List.of("a", "b", "c")),
            "entries store in source order with the duplicate a keeping the first position; "
                + "got " + table.keys());
        check(table.size() == 3, "the duplicate key never changes the count; got " + table.size());
        check(Value.string("a2").equals(present(table, "a")),
            "the duplicate key keeps the last value (a2)");
        check(Value.string("b").equals(present(table, "b")), "b stores its value");
        check(Value.string("c").equals(present(table, "c")), "c stores its value");
        check(log.equals(List.of(
                "resolve " + va1,
                "resolve " + vb,
                "resolve " + va2,
                "resolve " + vc)),
            "every entry value resolves exactly once in source order; got " + log);

        SemanticTable<Value> empty = ContainerOpsExecutor.executeTableNew(
            tableNewOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE), Map.of());
        check(empty.keys().isEmpty() && empty.size() == 0,
            "an empty entry list allocates an empty table");

        SemanticTable<Value> again = ContainerOpsExecutor.executeTableNew(tableOp, values);
        check(table != again, "every execution allocates a fresh table identity");
        check(table.keys().equals(again.keys()),
            "repeated executions produce equal key order");

        // Fail-closed defects.
        expectDefect(() -> ContainerOpsExecutor.executeTableNew(
                op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null),
                Map.of()),
            "executing a CONST op as TABLE_NEW (wrong kind)");
        expectDefect(() -> ContainerOpsExecutor.executeTableNew(
                tableNewOp(List.of(), FailurePolicyId.INT32_RESULT), Map.of()),
            "a TABLE_NEW carrying a non-pinned policy");
        expectDefect(() -> ContainerOpsExecutor.executeTableNew(
                tableNewOp(List.of(new KindPayload.TableEntry("k", new ValueId(9000))),
                    FailurePolicyId.NO_DEAL_FAILURE),
                Map.of()),
            "an unresolvable entry value");
    }

    // =========================================================================
    // 3. ARRAY_NEW
    // =========================================================================

    /** Puts the three pinned element values (int, string, null) into the lookup. */
    private static List<ValueId> putTestElements(Map<ValueId, Value> values) {
        List<ValueId> ids = new ArrayList<>();
        for (Value element : List.of(new Value.Int(40), Value.string("mid"), Value.Null.INSTANCE)) {
            ValueId id = nextValue();
            values.put(id, element);
            ids.add(id);
        }
        return ids;
    }

    /** Builds a 3-element ARRAY_NEW op with three parented boundary children. */
    private static SemanticOp arrayNewOpWithChildren(List<ValueId> elementIds,
                                                     Map<OpId, SemanticOp> boundaryOps) {
        OpId arrayId = nextOpId();
        List<OpId> childIds = new ArrayList<>();
        for (int i = 0; i < elementIds.size(); i++) {
            SemanticOp child = boundaryChild(arrayId, BoundaryKind.ARRAY_LITERAL_ELEMENT,
                i == 1 ? STRING : INT, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR);
            childIds.add(child.opId());
            boundaryOps.put(child.opId(), child);
        }
        return opWithId(arrayId, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.copyOf(elementIds), List.copyOf(childIds)),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    /** The pinned E8003 projection a failing element fixture uses. */
    private static BoundaryFailure e8003ElementFailure() {
        BoundaryFailure leaf = BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
            "int", "string", new LinkedHashMap<>(), null);
        return BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR), 0,
            "int", "string", metadataOf("oneBasedIndex", "2"), leaf);
    }

    static void testArrayNewOrchestration() {
        System.out.println("-- ARRAY_NEW: resolve-all-first, payload-order children, "
            + "first-failure and allocate-after-all-checks --");

        Map<ValueId, Value> values = new LinkedHashMap<>();
        List<ValueId> elementIds = putTestElements(values);
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        SemanticOp arrayOp = arrayNewOpWithChildren(elementIds, boundaryOps);

        // All-pass: resolution order precedes every child call; children
        // run strictly in payload order.
        List<String> log = new ArrayList<>();
        RecordingValues recording = new RecordingValues(values, log);
        ScriptedDelegate allPass = new ScriptedDelegate(log, -1, null, null);
        Outcome<SemanticArray<Value>> allPassOutcome =
            ContainerOpsExecutor.executeArrayNew(arrayOp, recording, boundaryOps, allPass);
        if (allPassOutcome instanceof Outcome.Success<SemanticArray<Value>> success) {
            check(success.value().size() == 3, "the fresh array holds three elements");
            check(success.value().elementAt(0).equals(new Value.Int(40))
                    && success.value().elementAt(1).equals(Value.string("mid"))
                    && success.value().elementAt(2) == Value.Null.INSTANCE,
                "the array elements keep source order with the delegate-published values");
        } else {
            fail("all-pass ARRAY_NEW failed unexpectedly");
        }
        List<String> expectedLog = new ArrayList<>();
        for (ValueId id : values.keySet()) {
            expectedLog.add("resolve " + id);
        }
        for (int i = 0; i < 3; i++) {
            expectedLog.add("child[" + i + "] ARRAY_LITERAL_ELEMENT <- "
                + switch (i) {
                    case 0 -> "int";
                    case 1 -> "string";
                    default -> "null";
                });
        }
        check(log.equals(expectedLog),
            "all element prior steps resolve before any child runs and children run in "
                + "payload order; got " + log);

        // The delegate-published checked values (never the raw inputs when
        // the delegate republishes) become the array elements.
        List<Value> published = new ArrayList<>();
        BoundaryCheckRunner republish = (boundary, input) -> {
            Value republished = switch (input) {
                case Value.Int intValue -> new Value.Int(intValue.value());
                case Value.String stringValue -> Value.string(stringValue.scalar());
                default -> input;
            };
            published.add(republished);
            return new BoundaryResult.Pass(republished);
        };
        Outcome<SemanticArray<Value>> republishedOutcome =
            ContainerOpsExecutor.executeArrayNew(arrayOp, values, boundaryOps, republish);
        if (republishedOutcome instanceof Outcome.Success<SemanticArray<Value>> success) {
            check(success.value().elementAt(0) == published.get(0)
                    && success.value().elementAt(1) == published.get(1)
                    && success.value().elementAt(2) == published.get(2),
                "the array holds the delegate-published checked instances in source order");
        } else {
            fail("republishing ARRAY_NEW failed unexpectedly");
        }

        // Failing second child: the op fails with that child's failure,
        // no array is published, the first child's pass is recorded, and
        // the third child never runs.
        BoundaryFailure e8003 = e8003ElementFailure();
        List<String> failLog = new ArrayList<>();
        RecordingValues failRecording = new RecordingValues(values, failLog);
        ScriptedDelegate failSecond = new ScriptedDelegate(failLog, 1, e8003, null);
        Outcome<SemanticArray<Value>> failed =
            ContainerOpsExecutor.executeArrayNew(arrayOp, failRecording, boundaryOps, failSecond);
        if (failed instanceof Outcome.Failure<SemanticArray<Value>> failure) {
            check(failure.failure().failure() == e8003,
                "the op fails with exactly the second child's failure instance");
            check(failure.failure().origin().equals(arrayOp.origin()),
                "the failure origin is the executed op's origin");
        } else {
            fail("the failing second child did not fail the op");
        }
        check(failLog.contains("child[0] ARRAY_LITERAL_ELEMENT <- int"),
            "the first child's pass stays observable in the delegate call order");
        check(failLog.contains("child[1] ARRAY_LITERAL_ELEMENT <- string"),
            "the failing child ran second (payload order)");
        check(failLog.stream().noneMatch(entry -> entry.contains("child[2]")),
            "the third child never runs after the first failure");
        check(failLog.size() == 5,
            "exactly the three resolutions and the two run children happened; got " + failLog);

        // Failing first child: only child[0] runs.
        List<String> firstFailLog = new ArrayList<>();
        ScriptedDelegate failFirst = new ScriptedDelegate(firstFailLog, 0, e8003, null);
        Outcome<SemanticArray<Value>> firstFailed =
            ContainerOpsExecutor.executeArrayNew(arrayOp,
                new RecordingValues(values, firstFailLog), boundaryOps, failFirst);
        check(firstFailed instanceof Outcome.Failure<SemanticArray<Value>>,
            "a failing first child fails the op with no array published");
        check(firstFailLog.stream().noneMatch(entry -> entry.contains("child[1]")),
            "no later child runs after the first child fails");

        // Empty literal: zero values, zero children, no delegate call.
        SemanticOp emptyOp = op(SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(), List.of()), nextValue(),
            new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
        List<String> emptyLog = new ArrayList<>();
        Outcome<SemanticArray<Value>> empty = ContainerOpsExecutor.executeArrayNew(emptyOp,
            new RecordingValues(Map.of(), emptyLog), Map.of(),
            new ScriptedDelegate(emptyLog, -1, null, null));
        if (empty instanceof Outcome.Success<SemanticArray<Value>> success) {
            check(success.value().size() == 0,
                "an empty literal allocates an empty array after zero checks");
        } else {
            fail("empty ARRAY_NEW failed unexpectedly");
        }
        check(emptyLog.isEmpty(),
            "an empty literal drives zero resolutions and zero delegate calls; got " + emptyLog);

        // Determinism: two identical all-pass executions produce equal arrays.
        Outcome<SemanticArray<Value>> run1 =
            ContainerOpsExecutor.executeArrayNew(arrayOp, values, boundaryOps, allPass);
        Outcome<SemanticArray<Value>> run2 =
            ContainerOpsExecutor.executeArrayNew(arrayOp, values, boundaryOps, allPass);
        check(run1 instanceof Outcome.Success<SemanticArray<Value>> s1
                && run2 instanceof Outcome.Success<SemanticArray<Value>> s2
                && s1.value().elements().equals(s2.value().elements()),
            "repeated executions produce equal element sequences");
    }

    static void testArrayNewDefects() {
        System.out.println("-- ARRAY_NEW fail-closed defects --");

        Map<ValueId, Value> values = new LinkedHashMap<>();
        putTestElements(values);
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        SemanticOp arrayOp = arrayNewOpWithChildren(
            new ArrayList<>(values.keySet()), boundaryOps);
        ScriptedDelegate pass = new ScriptedDelegate(new ArrayList<>(), -1, null, null);

        // Count mismatch (two values, one boundary child).
        ValueId solo = nextValue();
        Map<ValueId, Value> soloValues = new LinkedHashMap<>();
        soloValues.put(solo, new Value.Int(1));
        OpId soloId = nextOpId();
        SemanticOp soloChild = boundaryChild(soloId, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR);
        SemanticOp mismatched = opWithId(soloId, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(solo, solo), List.of(soloChild.opId())),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(mismatched, soloValues,
                Map.of(soloChild.opId(), soloChild), pass),
            "an element-boundary count mismatch");

        // Unresolvable element value.
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(
                opWithId(nextOpId(), SemanticOpKind.ARRAY_NEW,
                    new KindPayload.ArrayNewPayload(INT, List.of(new ValueId(9001)),
                        List.of(nextOpId())),
                    nextValue(), new RuntimeDescriptor.Array(INT),
                    FailurePolicyId.NO_DEAL_FAILURE, null),
                Map.of(), Map.of(), pass),
            "an unresolvable element value");

        // A boundary id the lookup does not resolve.
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(
                opWithId(nextOpId(), SemanticOpKind.ARRAY_NEW,
                    new KindPayload.ArrayNewPayload(INT, List.of(solo),
                        List.of(new OpId(MOD, 9002))),
                    nextValue(), new RuntimeDescriptor.Array(INT),
                    FailurePolicyId.NO_DEAL_FAILURE, null),
                soloValues, Map.of(), pass),
            "a boundary id the lookup does not resolve");

        // A named child that is not a BOUNDARY op.
        OpId arrayId2 = nextOpId();
        SemanticOp foreignChild = op(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, arrayId2);
        SemanticOp foreign = opWithId(arrayId2, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(solo),
                List.of(foreignChild.opId())),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(foreign, soloValues,
                Map.of(foreignChild.opId(), foreignChild), pass),
            "a named child that is not a BOUNDARY op");

        // An unparented child (origin parentOpId != the ARRAY_NEW op).
        OpId arrayId3 = nextOpId();
        SemanticOp unparentedChild = boundaryChild(nextOpId(), BoundaryKind.ARRAY_LITERAL_ELEMENT,
            INT, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR);
        SemanticOp unparented = opWithId(arrayId3, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(solo),
                List.of(unparentedChild.opId())),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(unparented, soloValues,
                Map.of(unparentedChild.opId(), unparentedChild), pass),
            "an element-boundary child not parented to the ARRAY_NEW op");

        // A child of the wrong boundary kind.
        OpId arrayId4 = nextOpId();
        SemanticOp wrongKindChild = boundaryChild(arrayId4, BoundaryKind.CONTEXTUAL_TABLE_READ,
            STRING, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp wrongKind = opWithId(arrayId4, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(solo),
                List.of(wrongKindChild.opId())),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(wrongKind, soloValues,
                Map.of(wrongKindChild.opId(), wrongKindChild), pass),
            "an element-boundary child of the wrong boundary kind");

        // Wrong op kind and wrong pinned policy.
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(
                tableNewOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE),
                Map.of(), Map.of(), pass),
            "executing a TABLE_NEW op as ARRAY_NEW (wrong kind)");
        expectDefect(() -> ContainerOpsExecutor.executeArrayNew(
                opWithId(nextOpId(), SemanticOpKind.ARRAY_NEW,
                    new KindPayload.ArrayNewPayload(INT, List.of(), List.of()), nextValue(),
                    new RuntimeDescriptor.Array(INT), FailurePolicyId.INT32_RESULT, null),
                Map.of(), Map.of(), pass),
            "an ARRAY_NEW carrying a non-pinned policy");

        // The well-formed op still passes after every negative (no shared state).
        Outcome<SemanticArray<Value>> stillPasses =
            ContainerOpsExecutor.executeArrayNew(arrayOp, values, boundaryOps, pass);
        check(stillPasses instanceof Outcome.Success<SemanticArray<Value>>,
            "the executor stays stateless after every defect");
    }

    // =========================================================================
    // 4. MEMBER_READ
    // =========================================================================

    static void testMemberRead() {
        System.out.println("-- MEMBER_READ: read-before-child, present/missing, "
            + "nullable/non-nullable through the real BoundaryExecutor delegate --");

        // Present read: the child checks the present value and publishes it.
        SemanticTable<Value> table = new SemanticTable<>();
        table.put("k", new Value.Int(7));
        ValueId receiver = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(receiver, new Value.Table(table));
        List<String> log = new ArrayList<>();
        OpId readId = nextOpId();
        SemanticOp child = boundaryChild(readId, BoundaryKind.CONTEXTUAL_TABLE_READ,
            INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp readOp = opWithId(readId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(receiver, "k"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> presentOutcome = ContainerOpsExecutor.executeMemberRead(readOp,
            new RecordingValues(values, log), child, realProjectionDelegate(log));
        if (presentOutcome instanceof Outcome.Success<Value> success) {
            check(success.value().equals(new Value.Int(7)),
                "a present value passes the check and is published unchanged");
        } else {
            fail("present MEMBER_READ failed unexpectedly");
        }
        check(log.equals(List.of("resolve " + receiver, "child CONTEXTUAL_TABLE_READ <- int")),
            "the receiver resolves exactly once before the child runs with the read outcome; "
                + "got " + log);

        // Present mismatch: the delegate (BoundaryExecutor) fails the check.
        SemanticTable<Value> mismatchTable = new SemanticTable<>();
        mismatchTable.put("k", Value.string("s"));
        ValueId mismatchReceiver = nextValue();
        Map<ValueId, Value> mismatchValues = new LinkedHashMap<>();
        mismatchValues.put(mismatchReceiver, new Value.Table(mismatchTable));
        OpId mismatchId = nextOpId();
        SemanticOp mismatchChild = boundaryChild(mismatchId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp mismatchOp = opWithId(mismatchId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(mismatchReceiver, "k"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> mismatch = ContainerOpsExecutor.executeMemberRead(mismatchOp,
            mismatchValues, mismatchChild, realProjectionDelegate(null));
        if (mismatch instanceof Outcome.Failure<Value> failure) {
            check(failure.failure().failure().code() == DiagnosticCode.E8001
                    && "expected int, got string".equals(failure.failure().failure().message())
                    && "int".equals(failure.failure().failure().expected())
                    && "string".equals(failure.failure().failure().actual()),
                "a present wrong-kind value fails through the delegate's projection");
        } else {
            fail("the present-mismatch read did not fail");
        }

        // Missing + nullable descriptor: the delegate maps missing -> null.
        SemanticTable<Value> emptyTable = new SemanticTable<>();
        ValueId emptyReceiver = nextValue();
        Map<ValueId, Value> emptyValues = new LinkedHashMap<>();
        emptyValues.put(emptyReceiver, new Value.Table(emptyTable));
        OpId nullableId = nextOpId();
        SemanticOp nullableChild = boundaryChild(nullableId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, NULLABLE_INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp nullableOp = opWithId(nullableId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(emptyReceiver, "absent"), nextValue(),
            NULLABLE_INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> nullable = ContainerOpsExecutor.executeMemberRead(nullableOp,
            emptyValues, nullableChild, realProjectionDelegate(null));
        if (nullable instanceof Outcome.Success<Value> success) {
            check(success.value() == Value.Null.INSTANCE,
                "missing against a nullable descriptor publishes language null "
                    + "(the delegate's pinned missing->null mapping)");
        } else {
            fail("missing + nullable did not publish null");
        }

        // Missing + non-nullable descriptor: the delegate fails with got missing.
        OpId nonNullableId = nextOpId();
        SemanticOp nonNullableChild = boundaryChild(nonNullableId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp nonNullableOp = opWithId(nonNullableId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(emptyReceiver, "absent"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> missing = ContainerOpsExecutor.executeMemberRead(nonNullableOp,
            emptyValues, nonNullableChild, realProjectionDelegate(null));
        if (missing instanceof Outcome.Failure<Value> failure) {
            check(failure.failure().failure().code() == DiagnosticCode.E8001
                    && "expected int, got missing".equals(failure.failure().failure().message())
                    && "int".equals(failure.failure().failure().expected())
                    && "missing".equals(failure.failure().failure().actual())
                    && failure.failure().failure().policy() == FailurePolicyId.TYPE_DESCRIPTOR,
                "missing against a non-nullable descriptor fails with the pinned "
                    + "expected int, got missing projection");
        } else {
            fail("missing + non-nullable did not fail with got missing");
        }

        // Present null: distinct from missing (D4) — nullable passes null,
        // non-nullable projects got null, never got missing.
        SemanticTable<Value> nullTable = new SemanticTable<>();
        nullTable.put("k", Value.Null.INSTANCE);
        ValueId nullReceiver = nextValue();
        Map<ValueId, Value> nullValues = new LinkedHashMap<>();
        nullValues.put(nullReceiver, new Value.Table(nullTable));
        OpId nullNullableId = nextOpId();
        SemanticOp nullNullableChild = boundaryChild(nullNullableId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, NULLABLE_INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp nullNullableOp = opWithId(nullNullableId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(nullReceiver, "k"), nextValue(), NULLABLE_INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> presentNull = ContainerOpsExecutor.executeMemberRead(nullNullableOp,
            nullValues, nullNullableChild, realProjectionDelegate(null));
        check(presentNull instanceof Outcome.Success<Value> success
                && success.value() == Value.Null.INSTANCE,
            "a present null passes a nullable descriptor (present null is not missing)");
        OpId nullNonNullableId = nextOpId();
        SemanticOp nullNonNullableChild = boundaryChild(nullNonNullableId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp nullNonNullableOp = opWithId(nullNonNullableId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(nullReceiver, "k"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Outcome<Value> presentNullInt = ContainerOpsExecutor.executeMemberRead(nullNonNullableOp,
            nullValues, nullNonNullableChild, realProjectionDelegate(null));
        check(presentNullInt instanceof Outcome.Failure<Value> failure
                && "expected int, got null".equals(failure.failure().failure().message()),
            "a present null against a non-nullable descriptor projects got null, "
                + "distinct from got missing");
    }

    static void testMemberReadDefects() {
        System.out.println("-- MEMBER_READ fail-closed defects --");

        ValueId receiver = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(receiver, new Value.Table(new SemanticTable<>()));
        OpId readId = nextOpId();
        SemanticOp child = boundaryChild(readId, BoundaryKind.CONTEXTUAL_TABLE_READ,
            INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp readOp = opWithId(readId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(receiver, "k"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        BoundaryCheckRunner pass = realProjectionDelegate(null);

        // Non-table receiver.
        Map<ValueId, Value> intReceiver = new LinkedHashMap<>();
        intReceiver.put(receiver, new Value.Int(3));
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(readOp, intReceiver,
                child, pass),
            "a receiver that resolves to a non-table value");

        // A child that is not a BOUNDARY op.
        SemanticOp foreignChild = op(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, readId);
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(readOp, values,
                foreignChild, pass),
            "a contextual child that is not a BOUNDARY op");

        // An unparented child.
        SemanticOp unparented = boundaryChild(nextOpId(), BoundaryKind.CONTEXTUAL_TABLE_READ,
            INT, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(readOp, values,
                unparented, pass),
            "a contextual child not parented to the MEMBER_READ op");

        // A child of the wrong boundary kind.
        SemanticOp wrongKind = boundaryChild(readId, BoundaryKind.ARRAY_LITERAL_ELEMENT,
            INT, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR);
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(readOp, values,
                wrongKind, pass),
            "a contextual child of the wrong boundary kind");

        // Wrong op kind and wrong pinned policy.
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(
                arrayLengthOp(nextValue(), FailurePolicyId.INT32_RESULT),
                Map.of(), child, pass),
            "executing an ARRAY_LENGTH op as MEMBER_READ (wrong kind)");
        OpId wrongPolicyId = nextOpId();
        SemanticOp wrongPolicyChild = boundaryChild(wrongPolicyId,
            BoundaryKind.CONTEXTUAL_TABLE_READ, INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp wrongPolicy = opWithId(wrongPolicyId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(receiver, "k"), nextValue(), INT,
            FailurePolicyId.INT32_RESULT, null);
        expectDefect(() -> ContainerOpsExecutor.executeMemberRead(wrongPolicy, values,
                wrongPolicyChild, pass),
            "a MEMBER_READ carrying a non-pinned policy");
    }

    // =========================================================================
    // 5. ARRAY_LENGTH
    // =========================================================================

    static void testArrayLength() {
        System.out.println("-- ARRAY_LENGTH: the signed32 count with a single receiver "
            + "resolution --");

        List<Value> elements = new ArrayList<>();
        for (int i = 0; i < 1000; i++) {
            elements.add(new Value.Int(i));
        }
        ValueId receiver = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(receiver, new Value.Array(SemanticArray.of(elements)));
        List<String> log = new ArrayList<>();
        Outcome<Integer> length = ContainerOpsExecutor.executeArrayLength(
            arrayLengthOp(receiver, FailurePolicyId.INT32_RESULT),
            new RecordingValues(values, log));
        check(length instanceof Outcome.Success<Integer> success && success.value() == 1000,
            "the signed32 count of 1000 elements is 1000");
        check(log.equals(List.of("resolve " + receiver)),
            "the receiver resolves exactly once; got " + log);

        ValueId emptyReceiver = nextValue();
        Map<ValueId, Value> emptyValues = new LinkedHashMap<>();
        emptyValues.put(emptyReceiver, new Value.Array(SemanticArray.of()));
        Outcome<Integer> empty = ContainerOpsExecutor.executeArrayLength(
            arrayLengthOp(emptyReceiver, FailurePolicyId.INT32_RESULT), emptyValues);
        check(empty instanceof Outcome.Success<Integer> success && success.value() == 0,
            "an empty array reports count 0");

        ValueId threeReceiver = nextValue();
        Map<ValueId, Value> threeValues = new LinkedHashMap<>();
        threeValues.put(threeReceiver, new Value.Array(
            SemanticArray.of(new Value.Int(1), new Value.Int(2), new Value.Int(3))));
        Outcome<Integer> three = ContainerOpsExecutor.executeArrayLength(
            arrayLengthOp(threeReceiver, FailurePolicyId.INT32_RESULT), threeValues);
        check(three instanceof Outcome.Success<Integer> success && success.value() == 3,
            "a three-element array reports count 3");

        // Fail-closed defects.
        Map<ValueId, Value> tableReceiver = new LinkedHashMap<>();
        tableReceiver.put(receiver, new Value.Table(new SemanticTable<>()));
        expectDefect(() -> ContainerOpsExecutor.executeArrayLength(
                arrayLengthOp(receiver, FailurePolicyId.INT32_RESULT), tableReceiver),
            "a receiver that resolves to a non-array value");
        expectDefect(() -> ContainerOpsExecutor.executeArrayLength(
                arrayLengthOp(receiver, FailurePolicyId.NO_DEAL_FAILURE), values),
            "an ARRAY_LENGTH carrying a non-pinned policy");
        expectDefect(() -> ContainerOpsExecutor.executeArrayLength(
                concatOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE), Map.of()),
            "executing a STRING_CONCAT op as ARRAY_LENGTH (wrong kind)");

        // Determinism.
        Outcome<Integer> again = ContainerOpsExecutor.executeArrayLength(
            arrayLengthOp(receiver, FailurePolicyId.INT32_RESULT), values);
        check(length.equals(again), "repeated executions produce the equal count outcome");
    }

    // =========================================================================
    // 6. STRING_CONCAT
    // =========================================================================

    static void testStringConcat() {
        System.out.println("-- STRING_CONCAT: fragment-order scalar concatenation --");

        ValueId f1 = nextValue();
        ValueId f2 = nextValue();
        ValueId f3 = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(f1, Value.string("A\uD83D\uDE00"));
        values.put(f2, Value.string("B"));
        values.put(f3, Value.string(""));
        List<String> log = new ArrayList<>();
        Value.String concatenated = ContainerOpsExecutor.executeStringConcat(
            concatOp(List.of(f1, f2, f3), FailurePolicyId.NO_DEAL_FAILURE),
            new RecordingValues(values, log));
        check("A\uD83D\uDE00B".equals(carrier(concatenated)),
            "fragments concatenate in payload order with a surrogate pair as one scalar; "
                + "got " + carrier(concatenated));
        check(log.equals(List.of("resolve " + f1, "resolve " + f2, "resolve " + f3)),
            "fragments resolve strictly in payload order; got " + log);

        ValueId single = nextValue();
        Map<ValueId, Value> singleValues = new LinkedHashMap<>();
        singleValues.put(single, Value.string("z"));
        check("z".equals(carrier(ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(single), FailurePolicyId.NO_DEAL_FAILURE), singleValues))),
            "a single fragment concatenates to its own carrier");
        check("".equals(carrier(ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE), Map.of()))),
            "an empty fragment list concatenates to the empty scalar sequence");

        // Fail-closed defects.
        Map<ValueId, Value> intFragment = new LinkedHashMap<>();
        intFragment.put(f1, new Value.Int(1));
        expectDefect(() -> ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(f1), FailurePolicyId.NO_DEAL_FAILURE), intFragment),
            "a fragment that resolves to a non-string value");
        Map<ValueId, Value> invalidFragment = new LinkedHashMap<>();
        invalidFragment.put(f1, Value.string("\uDC00"));
        expectDefect(() -> ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(f1), FailurePolicyId.NO_DEAL_FAILURE), invalidFragment),
            "an Invalid operand is a producer defect, never a second projection");
        expectDefect(() -> ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(), FailurePolicyId.TYPE_DESCRIPTOR), Map.of()),
            "a STRING_CONCAT carrying a non-pinned policy");
        expectDefect(() -> ContainerOpsExecutor.executeStringConcat(
                tableNewOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE), Map.of()),
            "executing a TABLE_NEW op as STRING_CONCAT (wrong kind)");

        // Determinism.
        Value.String again = ContainerOpsExecutor.executeStringConcat(
            concatOp(List.of(f1, f2, f3), FailurePolicyId.NO_DEAL_FAILURE), values);
        check(concatenated.equals(again),
            "repeated executions produce the byte-identical carrier");
    }

    // =========================================================================
    // 7. FOR_EACH(STRING_SCALARS)
    // =========================================================================

    static void testForEachInvalid() {
        System.out.println("-- FOR_EACH(STRING_SCALARS): Invalid fails before the first "
            + "binding with the pinned E8001 projection --");

        BindingId binding = new BindingId(1);
        ValueId iterable = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(iterable, Value.string("\uD800"));
        List<String> log = new ArrayList<>();
        SemanticOp forOf = forOfOp(iterable, binding, 10, IterationMode.STRING_SCALARS,
            FailurePolicyId.TYPE_DESCRIPTOR);
        List<String> bodySteps = new ArrayList<>();
        Outcome<Integer> outcome = ContainerOpsExecutor.executeForEach(forOf,
            new RecordingValues(values, log),
            (index, bindingGeneration, yielded, loopLoad) ->
                bodySteps.add("body[" + index + "] <- " + carrier(yielded)));

        BoundaryFailure executorFailure;
        if (outcome instanceof Outcome.Failure<Integer> failure) {
            OpFailure opFailure = failure.failure();
            executorFailure = opFailure.failure();
            check(executorFailure.code() == DiagnosticCode.E8001,
                "the Invalid projection carries code E8001");
            check("expected string, got invalid Unicode scalar encoding".equals(
                    executorFailure.message()),
                "the instantiated message is the pinned invalid-string template");
            check("expected string, got invalid Unicode scalar encoding".equals(
                    FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR)
                        .templates().get(1)),
                "the projection uses the registry row's pinned invalid-string template");
            check("string".equals(executorFailure.expected())
                    && "invalid-unicode".equals(executorFailure.actual()),
                "expected is string and actual is the invalid-unicode kind token");
            check(executorFailure.policy() == FailurePolicyId.TYPE_DESCRIPTOR,
                "the projection carries the op's own TYPE_DESCRIPTOR policy");
            check(opFailure.origin().equals(forOf.origin()),
                "the failure origin is the for-of origin (the executed op's origin)");
        } else {
            fail("an Invalid iterable did not fail the op");
            return;
        }
        check(bodySteps.isEmpty(),
            "an Invalid iterable runs zero body steps before the projection");
        check(log.equals(List.of("resolve " + iterable)),
            "the iterable resolves exactly once before validation; got " + log);

        // Byte-identity with the BoundaryExecutor's classification projection
        // for the same closed view: the executor's own terminal check and
        // E4's projection engine instantiate the same registry row.
        BoundaryOutcome projected = BoundaryExecutor.check(FailurePolicyId.TYPE_DESCRIPTOR,
            STRING, BoundaryValueView.of(ActualKind.INVALID_UNICODE), BoundaryContext.none());
        if (projected instanceof BoundaryOutcome.Fail fail) {
            BoundaryFailure reference = fail.failure();
            check(reference.code() == executorFailure.code()
                    && reference.message().equals(executorFailure.message())
                    && Objects.equals(reference.expected(), executorFailure.expected())
                    && Objects.equals(reference.actual(), executorFailure.actual()),
                "the executor's projection is byte-identical to BoundaryExecutor's "
                    + "invalid-unicode classification projection");
        } else {
            fail("BoundaryExecutor did not classify the invalid view");
        }
    }

    static void testForEachValid() {
        System.out.println("-- FOR_EACH(STRING_SCALARS): scalar-order yields, fresh "
            + "generations, and the loop-binding load-resolution rule --");

        BindingId binding = new BindingId(1);
        long initialGeneration = 10;
        ValueId iterable = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(iterable, Value.string("a\uD83D\uDE00b"));
        KindPayload.ForEachPayload payload = new KindPayload.ForEachPayload(
            IterationMode.STRING_SCALARS, iterable, binding, initialGeneration,
            new BlockId(1));
        SemanticOp forOf = op(SemanticOpKind.FOR_EACH, payload, null, null,
            FailurePolicyId.TYPE_DESCRIPTOR, null);

        List<String> yields = new ArrayList<>();
        List<Long> boundGenerations = new ArrayList<>();
        List<Long> resolvedGenerations = new ArrayList<>();
        List<LoopLoadResolver> captured = new ArrayList<>();
        List<String> log = new ArrayList<>();
        Outcome<Integer> outcome = ContainerOpsExecutor.executeForEach(forOf,
            new RecordingValues(values, log), (index, bindingGeneration, yielded, loopLoad) -> {
                log.add("body[" + index + "] <- " + carrier(yielded));
                yields.add(carrier(yielded));
                boundGenerations.add(bindingGeneration);
                KindPayload.BindingLoadPayload load =
                    new KindPayload.BindingLoadPayload(binding, initialGeneration);
                resolvedGenerations.add(loopLoad.effectiveGeneration(load.generation()));
                captured.add(loopLoad);
            });

        check(outcome instanceof Outcome.Success<Integer> success && success.value() == 3,
            "a three-scalar iterable completes three iterations");
        check(yields.equals(List.of("a", "\uD83D\uDE00", "b")),
            "one single-scalar string yields per iteration in scalar order; got " + yields);
        check(boundGenerations.equals(List.of(
                initialGeneration, initialGeneration + 1, initialGeneration + 2)),
            "each iteration binds a fresh generation (initial + iteration index); got "
                + boundGenerations);
        check(resolvedGenerations.equals(boundGenerations),
            "a body BINDING_LOAD of the loop binding carrying the payload's initial "
                + "generation resolves per iteration to initial + iteration index");
        check(forOf.payload() == payload && payload.generation() == initialGeneration,
            "the payload is never rewritten per iteration (same instance, same "
                + "generation field)");
        check(log.equals(List.of("resolve " + iterable,
                "body[0] <- a", "body[1] <- \uD83D\uDE00", "body[2] <- b")),
            "the iterable resolves once before the first body step and bodies run in "
                + "scalar order; got " + log);

        // The resolver fails closed for any other carried generation.
        long wrong = initialGeneration + 7;
        for (int i = 0; i < 3; i++) {
            final LoopLoadResolver resolver = captured.get(i);
            expectDefect(() -> resolver.effectiveGeneration(wrong),
                "a loop-binding load carrying a generation other than the payload's "
                    + "initial generation (iteration " + i + ")");
        }

        // An empty string yields zero iterations.
        ValueId emptyIterable = nextValue();
        Map<ValueId, Value> emptyValues = new LinkedHashMap<>();
        emptyValues.put(emptyIterable, Value.string(""));
        List<String> emptySteps = new ArrayList<>();
        Outcome<Integer> empty = ContainerOpsExecutor.executeForEach(
            forOfOp(emptyIterable, binding, 4, IterationMode.STRING_SCALARS,
                FailurePolicyId.TYPE_DESCRIPTOR),
            emptyValues,
            (index, bindingGeneration, yielded, loopLoad) -> emptySteps.add("body"));
        check(empty instanceof Outcome.Success<Integer> success && success.value() == 0
                && emptySteps.isEmpty(),
            "an empty string yields zero iterations");

        // Determinism: repeated runs yield byte-identical sequences.
        List<String> yields2 = new ArrayList<>();
        ContainerOpsExecutor.executeForEach(forOf, values,
            (index, bindingGeneration, yielded, loopLoad) -> yields2.add(carrier(yielded)));
        check(yields2.equals(yields), "repeated executions yield byte-identical sequences");
    }

    static void testForEachDefects() {
        System.out.println("-- FOR_EACH fail-closed defects --");

        BindingId binding = new BindingId(1);
        ValueId iterable = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(iterable, Value.string("ab"));
        BodyRunner noop = (index, bindingGeneration, yielded, loopLoad) -> { };

        expectDefect(() -> ContainerOpsExecutor.executeForEach(
                forOfOp(iterable, binding, 1, IterationMode.ARRAY_VALUES,
                    FailurePolicyId.TYPE_DESCRIPTOR),
                values, noop),
            "FOR_EACH(ARRAY_VALUES) is E5's and never executable here");

        Map<ValueId, Value> intIterable = new LinkedHashMap<>();
        intIterable.put(iterable, new Value.Int(3));
        expectDefect(() -> ContainerOpsExecutor.executeForEach(
                forOfOp(iterable, binding, 1, IterationMode.STRING_SCALARS,
                    FailurePolicyId.TYPE_DESCRIPTOR),
                intIterable, noop),
            "an iterable that resolves to a non-string value");

        expectDefect(() -> ContainerOpsExecutor.executeForEach(
                forOfOp(iterable, binding, 1, IterationMode.STRING_SCALARS,
                    FailurePolicyId.NO_DEAL_FAILURE),
                values, noop),
            "a FOR_EACH carrying a non-pinned policy");
        expectDefect(() -> ContainerOpsExecutor.executeForEach(
                concatOp(List.of(), FailurePolicyId.NO_DEAL_FAILURE), Map.of(), noop),
            "executing a STRING_CONCAT op as FOR_EACH (wrong kind)");
        expectNpe(() -> ContainerOpsExecutor.executeForEach(
                forOfOp(iterable, binding, 1, IterationMode.STRING_SCALARS,
                    FailurePolicyId.TYPE_DESCRIPTOR),
                values, null),
            "executing FOR_EACH with a null body runner");
    }

    // =========================================================================
    // 8. The combined dependency step (C1 + C2 + C3)
    // =========================================================================

    static void testCombinedDependencyStep() {
        System.out.println("-- combined dependency step: STRING_CONCAT (C1) feeds "
            + "TABLE_NEW (C2); FOR_EACH (C3) accumulates yielded scalars in order --");

        // C1: fragment-order scalar concatenation (a surrogate pair is one scalar).
        ValueId f1 = nextValue();
        ValueId f2 = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(f1, Value.string("ab"));
        values.put(f2, Value.string("\uD83D\uDE00c"));
        Value.String joined = ContainerOpsExecutor.executeStringConcat(
            concatOp(List.of(f1, f2), FailurePolicyId.NO_DEAL_FAILURE), values);
        check("ab\uD83D\uDE00c".equals(carrier(joined)),
            "C1: the concatenated scalar sequence is ab, U+1F600, c");

        // C2: TABLE_NEW stores the concat result as a prior step in source order.
        ValueId joinedId = nextValue();
        ValueId markerId = nextValue();
        values.put(joinedId, joined);
        values.put(markerId, Value.string("X"));
        SemanticTable<Value> table = ContainerOpsExecutor.executeTableNew(
            tableNewOp(List.of(
                new KindPayload.TableEntry("joined", joinedId),
                new KindPayload.TableEntry("marker", markerId)),
                FailurePolicyId.NO_DEAL_FAILURE),
            values);
        check(table.keys().equals(List.of("joined", "marker")),
            "C2: the table keeps first-insertion order [joined, marker]; got "
                + table.keys());
        check(Value.string("ab\uD83D\uDE00c").equals(present(table, "joined")),
            "C2: the joined entry stores C1's exact result");
        check(Value.string("X").equals(present(table, "marker")),
            "C2: the marker entry stores its value");

        // C3: FOR_EACH over a multi-scalar string; the body accumulates each
        // yielded scalar into a SemanticTable in iteration order.
        ValueId iterable = nextValue();
        values.put(iterable, Value.string("\u03B1\uD83D\uDE00z"));
        BindingId binding = new BindingId(2);
        SemanticTable<Value> accumulated = new SemanticTable<>();
        Outcome<Integer> outcome = ContainerOpsExecutor.executeForEach(
            forOfOp(iterable, binding, 20, IterationMode.STRING_SCALARS,
                FailurePolicyId.TYPE_DESCRIPTOR),
            values,
            (index, bindingGeneration, yielded, loopLoad) ->
                accumulated.put("s" + index, yielded));
        check(outcome instanceof Outcome.Success<Integer> success && success.value() == 3,
            "C3: the three-scalar iterable completes three iterations");
        check(accumulated.keys().equals(List.of("s0", "s1", "s2")),
            "C3: the accumulated table keeps the iteration (insertion) order; got "
                + accumulated.keys());
        check(Value.string("\u03B1").equals(present(accumulated, "s0"))
                && Value.string("\uD83D\uDE00").equals(present(accumulated, "s1"))
                && Value.string("z").equals(present(accumulated, "s2")),
            "C3: each yielded single-scalar string accumulated under its iteration "
                + "key in scalar order");
    }

    // =========================================================================
    // 9. Null arguments fail closed
    // =========================================================================

    static void testNullArgumentsFailClosed() {
        System.out.println("-- null arguments are producer defects (NPE), never projections --");

        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(nextValue(), new Value.Int(1));
        BodyRunner noop = (index, bindingGeneration, yielded, loopLoad) -> { };

        // One-entry TABLE_NEW so the null lookup is actually reached.
        ValueId entryValue = nextValue();
        SemanticOp oneEntryTable = tableNewOp(
            List.of(new KindPayload.TableEntry("k", entryValue)), FailurePolicyId.NO_DEAL_FAILURE);

        // One-element ARRAY_NEW with one parented child (a valid shape).
        OpId arrayId = nextOpId();
        SemanticOp child = boundaryChild(arrayId, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR);
        SemanticOp oneElementArray = opWithId(arrayId, SemanticOpKind.ARRAY_NEW,
            new KindPayload.ArrayNewPayload(INT, List.of(entryValue), List.of(child.opId())),
            nextValue(), new RuntimeDescriptor.Array(INT), FailurePolicyId.NO_DEAL_FAILURE, null);

        OpId readId = nextOpId();
        SemanticOp readChild = boundaryChild(readId, BoundaryKind.CONTEXTUAL_TABLE_READ,
            INT, FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp readOp = opWithId(readId, SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(entryValue, "k"), nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        BoundaryCheckRunner pass = realProjectionDelegate(null);

        expectNpe(() -> ContainerOpsExecutor.executeTableNew(null, Map.of()),
            "executeTableNew with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeTableNew(oneEntryTable, null),
            "executeTableNew with a null value lookup");
        expectNpe(() -> ContainerOpsExecutor.executeArrayNew(null, values, Map.of(), pass),
            "executeArrayNew with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeArrayNew(oneElementArray, null,
                Map.of(child.opId(), child), pass),
            "executeArrayNew with a null value lookup");
        expectNpe(() -> ContainerOpsExecutor.executeArrayNew(oneElementArray, values,
                null, pass),
            "executeArrayNew with a null boundary lookup");
        expectNpe(() -> ContainerOpsExecutor.executeArrayNew(oneElementArray, values,
                Map.of(child.opId(), child), null),
            "executeArrayNew with a null check runner");
        expectNpe(() -> ContainerOpsExecutor.executeMemberRead(null, values, readChild, pass),
            "executeMemberRead with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeMemberRead(readOp, null, readChild, pass),
            "executeMemberRead with a null value lookup");
        expectNpe(() -> ContainerOpsExecutor.executeMemberRead(readOp, values, null, pass),
            "executeMemberRead with a null contextual child");
        expectNpe(() -> ContainerOpsExecutor.executeMemberRead(readOp, values, readChild, null),
            "executeMemberRead with a null check runner");
        expectNpe(() -> ContainerOpsExecutor.executeArrayLength(null, values),
            "executeArrayLength with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeArrayLength(
                arrayLengthOp(entryValue, FailurePolicyId.INT32_RESULT), null),
            "executeArrayLength with a null value lookup");
        expectNpe(() -> ContainerOpsExecutor.executeStringConcat(null, values),
            "executeStringConcat with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeStringConcat(
                concatOp(List.of(entryValue), FailurePolicyId.NO_DEAL_FAILURE), null),
            "executeStringConcat with a null value lookup");
        expectNpe(() -> ContainerOpsExecutor.executeForEach(null, values, noop),
            "executeForEach with a null op");
        expectNpe(() -> ContainerOpsExecutor.executeForEach(
                forOfOp(entryValue, new BindingId(1), 1, IterationMode.STRING_SCALARS,
                    FailurePolicyId.TYPE_DESCRIPTOR),
                null, noop),
            "executeForEach with a null value lookup");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Container Ops Executor Test (ISSUE-0384 C3) ===\n");

        testValueViewClassification();
        testTableNew();
        testArrayNewOrchestration();
        testArrayNewDefects();
        testMemberRead();
        testMemberReadDefects();
        testArrayLength();
        testStringConcat();
        testForEachInvalid();
        testForEachValid();
        testForEachDefects();
        testCombinedDependencyStep();
        testNullArgumentsFailClosed();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
