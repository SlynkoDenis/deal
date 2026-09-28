package deal.test;

import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ClassOpsExecutor.BodyRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryResult;
import deal.semantic.ir.ClassOpsExecutor.Defect;
import deal.semantic.ir.ClassOpsExecutor.FieldState;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
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
import deal.semantic.ir.ValueId;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Verifies the ISSUE-0512 {@link ClassOpsExecutor} surface
 * (class-construction-jsonable-operations K-D4/K-D11; parent D16): the
 * single op-level execution form of {@code CLASS_DEFAULT} and
 * {@code CLASS_NEW(LOCAL)} over the closed value view extended with the
 * class variant {@code Class {classId, fields: [Present(Value) |
 * Missing]}} preserving missing versus null, with the pinned delegate
 * seams — the value lookup {@code Map<ValueId, Value>}, the
 * {@link BoundaryCheckRunner} boundary seam, the {@link BodyRunner}
 * default-block seam, and the layout-resolution context
 * {@code ClassId → ClassLayout} — driven by fixture delegates with
 * side-effect probes.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>the closed value view renders the canonical actual kinds and the
 *       class variant preserves the three presence states (missing,
 *       present null, present value); a {@code Present} field carrying
 *       the internal {@code Missing} view is a producer defect;</li>
 *   <li>{@code CLASS_DEFAULT} runs its default block exactly once per
 *       execution through the {@link BodyRunner} seam and publishes the
 *       produced default value (no boundary of its own, policy
 *       {@code NO_DEAL_FAILURE}; repeated execution re-invokes the
 *       block);</li>
 *   <li>{@code CLASS_NEW(LOCAL)} full success: provided values resolve
 *       in literal order; provided-field application and field
 *       validation run in declaration order (the overlay reorder pin
 *       observable through the boundary-input/order probes); the fresh
 *       instance is tagged with the classId; every successful
 *       construction publishes a fresh instance identity; zero return
 *       boundaries;</li>
 *   <li>default application runs only for omitted required-present
 *       fields — a provided field's default block is never executed by
 *       the {@link BodyRunner} fixture;</li>
 *   <li>default application completes before the extra-key scan: a
 *       fixture {@code CLASS_NEW} carrying an extra provided field still
 *       observes the completed default-block effects, then fails E8007
 *       with the exact template {@code extra field '{field}' in class
 *       '{classId}'} at the op origin, first extra key in
 *       provided-source order, with no provided application or field
 *       validation after;</li>
 *   <li>field boundaries run in declaration order through the
 *       {@link BoundaryCheckRunner} seam (the fixture records order and
 *       inputs); a failing boundary publishes no instance and stops
 *       validation at the first failing field (the tag never runs; the
 *       later children never run);</li>
 *   <li>the production-delegate stand-in: the real
 *       {@link BoundaryExecutor} drives the descriptor-kind policies —
 *       an E8001 kind mismatch and an E8010 function-signature mismatch
 *       fail the op at the op origin, and matching values pass;</li>
 *   <li>repeated construction re-executes default blocks so mutable
 *       defaults allocate freshly per instance (the fixture body runner
 *       re-invoked per attempt; two attempts publish two distinct
 *       default-table identities);</li>
 *   <li>fail-closed defects: wrong op kinds/policies, non-{@code LOCAL}
 *       owners, factory refs, unresolvable/mismatched layouts,
 *       unresolvable provided values, wrong-kind values, boundary
 *       children of the wrong kind/parentage/descriptor/policy/input,
 *       child-count/order/kind mismatches, wrong default children, and
 *       duplicate defaults are producer defects, never DEAL projections;
 *       null arguments throw the documented NPEs;</li>
 *   <li>determinism: repeated executions with equal inputs produce
 *       equal results (the executor is stateless).</li>
 * </ol>
 */
public class ClassOpsExecutorTest {

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
            fail("expected ClassOpsExecutor.Defect for " + what
                + ", but no exception was raised");
        } catch (Defect expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected ClassOpsExecutor.Defect for " + what + ", got "
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
    // Semantic-id and op builders (the ContainerOpsExecutorTest discipline)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("corpus.classops");
    private static final ClassId CLS = new ClassId(MOD.path(), "Point");
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor STRING = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor TABLE = RuntimeDescriptor.Table.INSTANCE;
    private static final RuntimeDescriptor.Func FUNC_NULL = new RuntimeDescriptor.Func(
        List.of(), RuntimeDescriptor.Null.INSTANCE, false);
    private static final RuntimeDescriptor.Func FUNC_NULL_ASYNC = new RuntimeDescriptor.Func(
        List.of(), RuntimeDescriptor.Null.INSTANCE, true);

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

    private static ClassLayout.FieldLayout field(String name, RuntimeDescriptor descriptor,
                                                 boolean required) {
        return new ClassLayout.FieldLayout(name, descriptor, required, DefaultOwner.LOCAL);
    }

    private static ClassLayout layout(ClassLayout.FieldLayout... fields) {
        return new ClassLayout(CLS, List.of(fields));
    }

    /** A detached CLASS_DEFAULT op (K-D12: no static parent). */
    private static SemanticOp defaultOp(String field, SemanticValue result,
                                        RuntimeDescriptor resultType, FailurePolicyId policy) {
        return op(SemanticOpKind.CLASS_DEFAULT,
            new KindPayload.ClassDefaultPayload(CLS, field, new BlockId(1)),
            result, resultType, policy, null);
    }

    /** A parented field-boundary child (K-D4 parentage pin). */
    private static SemanticOp boundaryChild(OpId parentId, BoundaryKind kind,
            RuntimeDescriptor descriptor, ValueId input, FailurePolicyId policy) {
        return op(SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("runtime-validation")),
            null, null, policy, parentId);
    }

    /** The value of the declared field {@code name} of one published instance. */
    private static Value fieldValue(Value.Class instance, ClassLayout layout, String name) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(name)) {
                FieldState state = instance.fields().get(i);
                return state instanceof FieldState.Present present
                    ? present.value() : null;
            }
        }
        return null;
    }

    /** The field state of the declared field {@code name} of one published instance. */
    private static FieldState fieldState(Value.Class instance, ClassLayout layout, String name) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(name)) {
                return instance.fields().get(i);
            }
        }
        return null;
    }

    // =========================================================================
    // Fixtures: the recording value lookup and the delegate stand-ins
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
     * A pass-through/fail-first boundary fixture: records every call in
     * the shared log (the call order proves the declaration order),
     * returns {@code Pass(input)} and fails child index
     * {@code failAtIndex} with the supplied failure.
     */
    private static final class ScriptedDelegate implements BoundaryCheckRunner {

        private final List<String> log;
        private final int failAtIndex;
        private final BoundaryFailure failure;
        private int calls = 0;

        ScriptedDelegate(List<String> log, int failAtIndex, BoundaryFailure failure) {
            this.log = log;
            this.failAtIndex = failAtIndex;
            this.failure = failure;
        }

        int calls() {
            return calls;
        }

        @Override
        public BoundaryResult run(KindPayload.BoundaryPayload boundary, Value input) {
            int index = calls++;
            log.add("child[" + index + "] " + boundary.kind() + " <- " + input.actualKind().token());
            if (index == failAtIndex) {
                return new BoundaryResult.Fail(failure);
            }
            return new BoundaryResult.Pass(input);
        }
    }

    /**
     * A recording body-runner fixture: every invocation of a
     * {@code CLASS_DEFAULT} default block is recorded (the invocation
     * log proves the declaration order and the skip-provided rule) and
     * returns the scripted produced value of the op.
     */
    private static final class RecordingBodyRunner implements BodyRunner {

        private final List<String> log;
        private final Map<OpId, Value> produced;
        private int calls = 0;

        RecordingBodyRunner(List<String> log, Map<OpId, Value> produced) {
            this.log = log;
            this.produced = produced;
        }

        int calls() {
            return calls;
        }

        @Override
        public Value runDefault(SemanticOp defaultOp) {
            calls++;
            log.add("default " + defaultOp.opId());
            return produced.get(defaultOp.opId());
        }
    }

    /**
     * The E4 production-delegate stand-in: every check runs through the
     * real {@link BoundaryExecutor} (the closed projection engine),
     * adapted from the executor's {@link Value} view to the boundary's
     * {@link BoundaryValueView}. The child's policy is the
     * descriptor-kind rule for the {@code CLASS_LITERAL_FIELD}/
     * {@code CLASS_DEFAULT_FIELD} cells. This proves the delegate seam
     * accepts the production executor and that the executor itself never
     * performs a boundary projection.
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
            case Value.Class classValue -> BoundaryValueView.ofClass(classValue.classId().text());
            case Value.Function function -> BoundaryValueView.ofFunction(function.signature());
            case Value.Missing ignored -> BoundaryValueView.of(ActualKind.MISSING);
        };
    }

    /**
     * The boundary's published value: a passing boundary never copies or
     * converts, so the published null view maps to the explicit null
     * variant and every other view keeps the input value.
     */
    private static Value publishValue(BoundaryValueView view, Value input) {
        return view.kind() == ActualKind.NULL ? Value.Null.INSTANCE : input;
    }

    // =========================================================================
    // Shared CLASS_NEW builders
    // =========================================================================

    /** A provided-field entry with a fresh prior-step id (not yet resolved). */
    private record ProvidedEntry(String name, ValueId valueId) {
    }

    /** One field-boundary entry plus its resolved child op. */
    private record BoundaryEntry(String field, BoundaryKind kind, SemanticOp child) {
    }

    /**
     * Builds a validated-shape CLASS_NEW op with the pinned children:
     * {@code classDefaultOpIds} naming the given detached CLASS_DEFAULT
     * ops; one field-boundary entry per {@code entries} record. The
     * returned handle carries the op plus the child lookups.
     */
    private record ClassNewFixture(SemanticOp op, Map<OpId, SemanticOp> defaultOps,
                                   Map<OpId, SemanticOp> boundaryOps) {
    }

    private static ClassNewFixture classNewFixture(ClassLayout layout,
            List<ProvidedEntry> provided, List<SemanticOp> defaults,
            List<BoundaryEntry> entries) {
        OpId opId = nextOpId();
        List<KindPayload.ProvidedField> providedFields = new ArrayList<>();
        for (ProvidedEntry entry : provided) {
            providedFields.add(new KindPayload.ProvidedField(entry.name(), entry.valueId()));
        }
        List<OpId> defaultIds = new ArrayList<>();
        Map<OpId, SemanticOp> defaultOps = new LinkedHashMap<>();
        for (SemanticOp defaultOp : defaults) {
            defaultIds.add(defaultOp.opId());
            defaultOps.put(defaultOp.opId(), defaultOp);
        }
        List<KindPayload.FieldBoundary> boundaries = new ArrayList<>();
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        for (BoundaryEntry entry : entries) {
            boundaries.add(new KindPayload.FieldBoundary(entry.field(), entry.kind(),
                entry.child().opId()));
            boundaryOps.put(entry.child().opId(), entry.child());
        }
        SemanticOp op = opWithId(opId, SemanticOpKind.CLASS_NEW,
            new KindPayload.ClassNewPayload(CLS, layout, providedFields, DefaultOwner.LOCAL,
                defaultIds, null, boundaries),
            nextValue(), new RuntimeDescriptor.Class(CLS),
            FailurePolicyId.CLASS_CONSTRUCTION, null);
        return new ClassNewFixture(op, defaultOps, boundaryOps);
    }

    /**
     * Re-parents the fixture's boundary children to the CLASS_NEW op id
     * (the children were built before the op id existed) and returns the
     * boundary lookup — the validator-pinned K-D4 parentage.
     */
    private static Map<OpId, SemanticOp> reparent(ClassNewFixture fixture,
                                                  List<BoundaryEntry> entries) {
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        for (BoundaryEntry entry : entries) {
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) entry.child().payload();
            OpId childId = entry.child().opId();
            SourceOrigin origin = new SourceOrigin(entry.child().origin().sourceId(),
                entry.child().origin().span(), entry.child().origin().kind(),
                entry.child().origin().anchorId(), fixture.op().opId());
            OperationContractSnapshot contract =
                contractFor(SemanticOpKind.BOUNDARY, payload, null, List.of(),
                    entry.child().failurePolicy(), "placeholder");
            String digest = ContractSnapshotCanonicalizer.digest(contract);
            contract = contractFor(SemanticOpKind.BOUNDARY, payload, null, List.of(),
                entry.child().failurePolicy(), digest);
            SemanticOp child = new SemanticOp(childId, SemanticOpKind.BOUNDARY, origin,
                null, null, List.of(), List.of(), payload, entry.child().failurePolicy(),
                contract);
            boundaryOps.put(childId, child);
        }
        return boundaryOps;
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
        check(new Value.Table(new SemanticTable<>()).actualKind() == ActualKind.TABLE,
            "Table renders TABLE");
        check(new Value.Array(SemanticArray.of(List.of())).actualKind() == ActualKind.ARRAY,
            "Array renders ARRAY");
        check(new Value.Class(CLS, List.of()).actualKind() == ActualKind.CLASS,
            "Class renders CLASS");
        check(new Value.Function(FUNC_NULL).actualKind() == ActualKind.FUNCTION,
            "Function renders FUNCTION");
        check(Value.Missing.INSTANCE.actualKind() == ActualKind.MISSING,
            "Missing renders the schema's internal MISSING, never Java null");
        check(("class:" + CLS.text()).equals(
                ActualKind.canonicalToken(ActualKind.CLASS, CLS.text())),
            "the CLASS canonical token is the pinned class:<ClassId> atom text; got "
                + ActualKind.canonicalToken(ActualKind.CLASS, CLS.text()));

        // The class variant preserves the three presence states exactly.
        Value.Class instance = new Value.Class(CLS, List.of(
            new FieldState.Present(Value.Null.INSTANCE),
            new FieldState.Present(new Value.Int(7)),
            FieldState.Missing.INSTANCE));
        check(instance.classId().equals(CLS), "the class value carries the canonical classId tag");
        check(instance.fields().size() == 3, "the class value carries its fields in order");
        check(instance.fields().get(0) instanceof FieldState.Present present
                && present.value() == Value.Null.INSTANCE,
            "a present null field is Present (never conflated with Missing)");
        check(instance.fields().get(1) instanceof FieldState.Present present
                && present.value().equals(new Value.Int(7)),
            "a present value field is Present with its value");
        check(instance.fields().get(2) == FieldState.Missing.INSTANCE,
            "an absent field is the Missing state (distinct from present null)");

        expectDefect(() -> new Value.Class(CLS, List.of(
                new FieldState.Present(Value.Missing.INSTANCE))),
            "a Present field carrying the internal Missing view");
        expectDefect(() -> new FieldState.Present(Value.Missing.INSTANCE),
            "a FieldState.Present carrying the internal Missing view");
        expectNpe(() -> new Value.Class(null, List.of()), "new Value.Class(null, …)");
        expectNpe(() -> new Value.Class(CLS, null), "new Value.Class(CLS, null)");
        expectNpe(() -> new Value.Function(null), "new Value.Function(null)");
        expectNpe(() -> new Value.String(null), "new Value.String(null)");
        expectNpe(() -> new Value.Table(null), "new Value.Table(null)");
        expectNpe(() -> new Value.Array(null), "new Value.Array(null)");
        expectNpe(() -> new FieldState.Present(null), "new FieldState.Present(null)");
    }

    // =========================================================================
    // 2. CLASS_DEFAULT
    // =========================================================================

    static void testClassDefaultExecution() {
        System.out.println("-- CLASS_DEFAULT: the block runs exactly once per execution "
            + "through the BodyRunner seam --");

        ValueId result = nextValue();
        SemanticOp defaultOp = defaultOp("a", result, INT, FailurePolicyId.NO_DEAL_FAILURE);
        List<String> log = new ArrayList<>();
        RecordingBodyRunner body = new RecordingBodyRunner(log,
            Map.of(defaultOp.opId(), new Value.Int(41)));

        Outcome<Value> outcome = ClassOpsExecutor.executeClassDefault(defaultOp, body);
        check(outcome instanceof Outcome.Success<Value> success
                && success.value().equals(new Value.Int(41)),
            "the op publishes the block's produced default value");
        check(body.calls() == 1 && log.equals(List.of("default " + defaultOp.opId())),
            "the default block runs exactly once through the BodyRunner seam; got " + log);

        // Per-construction re-execution: a second triggering attempt runs
        // the block again (freshness is produced by re-execution).
        ClassOpsExecutor.executeClassDefault(defaultOp, body);
        check(body.calls() == 2,
            "a second triggering attempt re-invokes the default block (per-construction "
                + "re-execution, never a cached value)");

        // Fail-closed defects.
        expectDefect(() -> ClassOpsExecutor.executeClassDefault(
                op(SemanticOpKind.CONST,
                    new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null),
                body),
            "executing a CONST op as CLASS_DEFAULT (wrong kind)");
        expectDefect(() -> ClassOpsExecutor.executeClassDefault(
                defaultOp("a", nextValue(), INT, FailurePolicyId.CLASS_CONSTRUCTION), body),
            "a CLASS_DEFAULT carrying a non-pinned policy");
        expectDefect(() -> ClassOpsExecutor.executeClassDefault(defaultOp,
                opArg -> Value.Missing.INSTANCE),
            "a default block producing the internal Missing view (wrong-kind value)");
        expectNpe(() -> ClassOpsExecutor.executeClassDefault(null, body),
            "executeClassDefault with a null op");
        expectNpe(() -> ClassOpsExecutor.executeClassDefault(defaultOp, null),
            "executeClassDefault with a null body runner");
    }

    // =========================================================================
    // 3. CLASS_NEW(LOCAL): the full K-D4 order
    // =========================================================================

    static void testClassNewLocalSuccessReorderAndOverlay() {
        System.out.println("-- CLASS_NEW(LOCAL) success: literal-order resolution, "
            + "declaration-order application/validation, tag, fresh identity, zero "
            + "return boundaries --");

        ClassLayout layout = layout(field("x", INT, true), field("tag", STRING, true),
            field("y", INT, false));
        ValueId vTag = nextValue();
        ValueId vX = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(vTag, Value.string("pt"));
        values.put(vX, new Value.Int(3));

        // Provided in literal order (tag before x — the reorder source);
        // boundaries in declaration order (x before tag).
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("tag", vTag),
            new ProvidedEntry("x", vX));
        List<BoundaryEntry> entries = new ArrayList<>();
        entries.add(new BoundaryEntry("x", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vX,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        entries.add(new BoundaryEntry("tag", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, STRING, vTag,
                FailurePolicyId.TYPE_DESCRIPTOR)));

        List<String> log = new ArrayList<>();
        RecordingValues recording = new RecordingValues(values, log);
        ScriptedDelegate delegate = new ScriptedDelegate(log, -1, null);
        ClassNewFixture fixture = classNewFixture(layout, provided, List.of(), entries);
        // The boundary children parent to the CLASS_NEW op (the builder
        // pins the payload; the parentage is pinned after the op id is
        // known).
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);

        Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            recording, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            delegate, new RecordingBodyRunner(new ArrayList<>(), Map.of()));

        check(log.subList(0, 2).equals(List.of(
                "resolve " + vTag, "resolve " + vX)),
            "provided values resolve in literal order (tag, x); got " + log);
        check(outcome instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Class instance
                && instance.classId().equals(CLS),
            "SUCCESS publishes a fresh instance tagged with the classId");
        if (outcome instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Class instance) {
            check(instance.fields().size() == 3
                    && fieldValue(instance, layout, "x").equals(new Value.Int(3))
                    && fieldValue(instance, layout, "tag").equals(Value.string("pt"))
                    && fieldState(instance, layout, "y") == FieldState.Missing.INSTANCE,
                "the instance holds the overlaid provided values in declaration order "
                    + "and the omitted optional stays missing");
        }
        check(log.get(2).equals("child[0] CLASS_LITERAL_FIELD <- int")
                && log.get(3).equals("child[1] CLASS_LITERAL_FIELD <- string"),
            "field validation runs in declaration order (x then tag — the provided "
                + "overlay reorder) with the pinned inputs; got " + log);
        check(delegate.calls() == 2, "exactly one boundary run per provided field");
        for (String line : log) {
            check(!line.contains("FUNCTION_RETURN"),
                "zero return boundaries: no FUNCTION_RETURN child ever runs (log line: "
                    + line + ")");
        }

        // Fresh identity per construction; equal contents.
        Outcome<Value> again = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            recording, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            delegate, new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        Value firstInstance = outcome instanceof Outcome.Success<Value> first
            ? first.value() : null;
        Value secondInstance = again instanceof Outcome.Success<Value> second
            ? second.value() : null;
        check(firstInstance != null && secondInstance != null
                && firstInstance != secondInstance
                && firstInstance.equals(secondInstance),
            "each successful construction publishes a fresh instance identity with "
                + "equal contents (the model's allocation rule)");
    }

    static void testClassNewLocalDefaultsAndSkipProvided() {
        System.out.println("-- default application runs only for omitted required-present "
            + "fields; a provided field's default never runs --");

        ClassLayout layout = layout(field("a", INT, true), field("b", INT, true),
            field("c", INT, false));
        ValueId vB = nextValue();
        Map<ValueId, Value> values = Map.of(vB, new Value.Int(20));

        SemanticOp defA = defaultOp("a", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        SemanticOp defB = defaultOp("b", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        Map<OpId, Value> produced = new LinkedHashMap<>();
        produced.put(defA.opId(), new Value.Int(10));
        produced.put(defB.opId(), new Value.Int(99));

        List<ProvidedEntry> provided = List.of(new ProvidedEntry("b", vB));
        List<BoundaryEntry> entries = new ArrayList<>();
        entries.add(new BoundaryEntry("a", BoundaryKind.CLASS_DEFAULT_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_DEFAULT_FIELD, INT,
                (ValueId) defA.result(), FailurePolicyId.TYPE_DESCRIPTOR)));
        entries.add(new BoundaryEntry("b", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vB,
                FailurePolicyId.TYPE_DESCRIPTOR)));

        List<String> log = new ArrayList<>();
        RecordingBodyRunner body = new RecordingBodyRunner(log, produced);
        ScriptedDelegate delegate = new ScriptedDelegate(log, -1, null);
        ClassNewFixture fixture = classNewFixture(layout, provided,
            List.of(defA, defB), entries);
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);

        Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            delegate, body);

        check(outcome instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Class instance
                && fieldValue(instance, layout, "a").equals(new Value.Int(10))
                && fieldValue(instance, layout, "b").equals(new Value.Int(20))
                && fieldState(instance, layout, "c") == FieldState.Missing.INSTANCE,
            "the default-filled omitted field a, the provided field b, and the "
                + "omitted optional c (missing) are preserved");
        check(body.calls() == 1 && log.contains("default " + defA.opId())
                && !log.contains("default " + defB.opId()),
            "only the omitted field's default block runs — a provided field's default "
                + "block is never executed by the BodyRunner fixture; got " + log);
        int firstChildLine = -1;
        for (int i = 0; i < log.size(); i++) {
            if (log.get(i).startsWith("child[0]")) {
                firstChildLine = i;
                break;
            }
        }
        check(log.indexOf("default " + defA.opId()) >= 0 && firstChildLine >= 0
                && log.indexOf("default " + defA.opId()) < firstChildLine,
            "default application completes before the first boundary run; got " + log);
        check(log.contains("child[0] CLASS_DEFAULT_FIELD <- int")
                && log.contains("child[1] CLASS_LITERAL_FIELD <- int"),
            "the boundaries run in declaration order with the default-produced and "
                + "provided inputs; got " + log);
    }

    static void testExtraKeyRejectionAfterDefaults() {
        System.out.println("-- the extra-key scan runs after default application and "
            + "before any provided application or field validation --");

        ClassLayout layout = layout(field("a", INT, true));
        ValueId vX = nextValue();
        ValueId vZz = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(vX, new Value.Int(1));
        values.put(vZz, new Value.Int(2));

        SemanticOp defA = defaultOp("a", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        Map<OpId, Value> produced = Map.of(defA.opId(), new Value.Int(10));

        // Two extra keys in provided-source order: the scan must name the
        // first one (x), never the second (zz).
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("x", vX),
            new ProvidedEntry("zz", vZz));
        ClassNewFixture fixture = classNewFixture(layout, provided, List.of(defA), List.of());

        List<String> log = new ArrayList<>();
        RecordingBodyRunner body = new RecordingBodyRunner(log, produced);
        ScriptedDelegate delegate = new ScriptedDelegate(log, -1, null);
        Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), fixture.boundaryOps(), Map.of(CLS, layout),
            delegate, body);

        check(outcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().policy() == FailurePolicyId.CLASS_CONSTRUCTION
                && failure.failure().failure().code() == DiagnosticCode.E8007,
            "the first extra key fails CLASS_CONSTRUCTION with E8007");
        if (outcome instanceof Outcome.Failure<Value> failure) {
            check(failure.failure().failure().message()
                    .equals("extra field 'x' in class '@corpus.classops/Point'"),
                "the exact template extra field '{field}' in class '{classId}'; got "
                    + failure.failure().failure().message());
            check(failure.failure().origin().equals(fixture.op().origin()),
                "the E8007 origin is the operation origin");
        }
        check(body.calls() == 1 && log.equals(List.of("default " + defA.opId())),
            "the completed default-block effects are observable before the scan fails; "
                + "got " + log);
        check(delegate.calls() == 0,
            "no provided application or field validation runs after the scan fails");
    }

    static void testBoundaryFailureStopsValidationAndPublishesNothing() {
        System.out.println("-- a failing boundary publishes no instance and stops "
            + "validation at the first failing field --");

        ClassLayout layout = layout(field("a", INT, true), field("b", INT, true),
            field("c", INT, true));
        ValueId vA = nextValue();
        ValueId vB = nextValue();
        ValueId vC = nextValue();
        Map<ValueId, Value> values = new LinkedHashMap<>();
        values.put(vA, new Value.Int(1));
        values.put(vB, new Value.Int(2));
        values.put(vC, new Value.Int(3));

        // Provided in scrambled literal order (c, a, b): resolution stays
        // literal, validation stays declaration order (a, b, c).
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("c", vC),
            new ProvidedEntry("a", vA), new ProvidedEntry("b", vB));
        List<BoundaryEntry> entries = new ArrayList<>();
        entries.add(new BoundaryEntry("a", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vA,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        entries.add(new BoundaryEntry("b", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vB,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        entries.add(new BoundaryEntry("c", BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vC,
                FailurePolicyId.TYPE_DESCRIPTOR)));

        BoundaryFailure scripted = BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
            "int", "string", new LinkedHashMap<>(), null);
        List<String> log = new ArrayList<>();
        ScriptedDelegate delegate = new ScriptedDelegate(log, 1, scripted);
        ClassNewFixture fixture = classNewFixture(layout, provided, List.of(), entries);
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);

        Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            delegate, new RecordingBodyRunner(new ArrayList<>(), Map.of()));

        check(outcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().message()
                    .equals("expected int, got string")
                && failure.failure().origin().equals(fixture.op().origin()),
            "the first failing boundary (b, the second field in declaration order) "
                + "fails the op with that child's failure at the op origin");
        check(delegate.calls() == 2,
            "validation stopped at the first failing field — the third child never "
                + "ran; got " + delegate.calls() + " calls");
        check(log.get(log.size() - 2).equals("child[0] CLASS_LITERAL_FIELD <- int")
                && log.get(log.size() - 1).equals("child[1] CLASS_LITERAL_FIELD <- int"),
            "the boundary order is declaration order (a then b) despite the literal "
                + "order (c, a, b); got " + log);
        check(!(outcome instanceof Outcome.Success<Value>),
            "a failing construction publishes no instance — the result is absent and "
                + "the tag never runs");
    }

    static void testRealProjectionDelegate() {
        System.out.println("-- the production-delegate stand-in: the real "
            + "BoundaryExecutor drives the descriptor-kind policies --");

        // A kind mismatch on an int field fails E8001 at the op origin.
        ClassLayout intLayout = layout(field("a", INT, true));
        ValueId vA = nextValue();
        Map<ValueId, Value> values = Map.of(vA, Value.string("wrong"));
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("a", vA));
        List<BoundaryEntry> entries = List.of(new BoundaryEntry("a",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vA,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        ClassNewFixture fixture = classNewFixture(intLayout, provided, List.of(), entries);
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);
        List<String> log = new ArrayList<>();
        Outcome<Value> mismatch = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), boundaryOps, Map.of(CLS, intLayout),
            realProjectionDelegate(log), new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        check(mismatch instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().policy() == FailurePolicyId.TYPE_DESCRIPTOR
                && failure.failure().failure().expected().equals("int")
                && failure.failure().failure().actual().equals("string")
                && failure.failure().failure().message().equals("expected int, got string")
                && failure.failure().origin().equals(fixture.op().origin()),
            "the real delegate projects the int-field kind mismatch as E8001 "
                + "expected int, got string at the op origin");

        // A function-typed field: a differing carried signature fails E8010.
        ClassLayout fnLayout = layout(field("f", FUNC_NULL, true));
        ValueId vF = nextValue();
        Map<ValueId, Value> fnValues = Map.of(vF,
            new Value.Function(FUNC_NULL_ASYNC));
        List<ProvidedEntry> fnProvided = List.of(new ProvidedEntry("f", vF));
        List<BoundaryEntry> fnEntries = List.of(new BoundaryEntry("f",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, FUNC_NULL, vF,
                FailurePolicyId.FUNCTION_SIGNATURE)));
        ClassNewFixture fnFixture = classNewFixture(fnLayout, fnProvided, List.of(), fnEntries);
        Map<OpId, SemanticOp> fnBoundaryOps = reparent(fnFixture, fnEntries);
        Outcome<Value> sigMismatch = ClassOpsExecutor.executeClassNewLocal(fnFixture.op(),
            fnValues, fnFixture.defaultOps(), fnBoundaryOps, Map.of(CLS, fnLayout),
            realProjectionDelegate(null), new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        check(sigMismatch instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8010
                && failure.failure().failure().policy() == FailurePolicyId.FUNCTION_SIGNATURE
                && failure.failure().failure().message().startsWith(
                    "function signature mismatch: expected"),
            "the real delegate projects the function-signature mismatch as E8010 "
                + "(descriptor-kind rule FUNCTION_SIGNATURE)");

        // The matching signature passes and the instance carries the function.
        ValueId vOk = nextValue();
        Map<ValueId, Value> okValues = Map.of(vOk, new Value.Function(FUNC_NULL));
        List<ProvidedEntry> okProvided = List.of(new ProvidedEntry("f", vOk));
        List<BoundaryEntry> okEntries = List.of(new BoundaryEntry("f",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, FUNC_NULL, vOk,
                FailurePolicyId.FUNCTION_SIGNATURE)));
        ClassNewFixture okFixture = classNewFixture(fnLayout, okProvided, List.of(), okEntries);
        Map<OpId, SemanticOp> okBoundaryOps = reparent(okFixture, okEntries);
        Outcome<Value> pass = ClassOpsExecutor.executeClassNewLocal(okFixture.op(),
            okValues, okFixture.defaultOps(), okBoundaryOps, Map.of(CLS, fnLayout),
            realProjectionDelegate(null), new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        check(pass instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Class instance
                && fieldValue(instance, fnLayout, "f").equals(new Value.Function(FUNC_NULL)),
            "the matching function value passes its FUNCTION_SIGNATURE boundary and "
                + "the instance carries it");
    }

    static void testFreshDefaultsPerConstruction() {
        System.out.println("-- repeated construction re-executes default blocks so "
            + "mutable defaults allocate freshly per instance --");

        ClassLayout layout = layout(field("items", TABLE, true));
        SemanticOp defItems = defaultOp("items", nextValue(), TABLE,
            FailurePolicyId.NO_DEAL_FAILURE);
        List<String> log = new ArrayList<>();
        // A body runner producing a fresh table per invocation (the
        // block-re-execution stand-in for a literal-typed default).
        BodyRunner freshTables = defaultOp -> {
            log.add("default " + defaultOp.opId());
            SemanticTable<Value> table = new SemanticTable<>();
            table.put("k", Value.string("v"));
            return new Value.Table(table);
        };
        List<BoundaryEntry> entries = List.of(new BoundaryEntry("items",
            BoundaryKind.CLASS_DEFAULT_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_DEFAULT_FIELD, TABLE,
                (ValueId) defItems.result(), FailurePolicyId.TYPE_DESCRIPTOR)));
        ClassNewFixture fixture = classNewFixture(layout, List.of(), List.of(defItems),
            entries);
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);

        Outcome<Value> first = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            Map.of(), fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            new ScriptedDelegate(new ArrayList<>(), -1, null), freshTables);
        Outcome<Value> second = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            Map.of(), fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            new ScriptedDelegate(new ArrayList<>(), -1, null), freshTables);

        check(first instanceof Outcome.Success<Value> s1
                && second instanceof Outcome.Success<Value> s2
                && s1.value() instanceof Value.Class i1
                && s2.value() instanceof Value.Class i2,
            "both constructions publish tagged instances");
        if (first instanceof Outcome.Success<Value> s1
                && second instanceof Outcome.Success<Value> s2
                && s1.value() instanceof Value.Class i1
                && s2.value() instanceof Value.Class i2) {
            Value table1 = fieldValue(i1, layout, "items");
            Value table2 = fieldValue(i2, layout, "items");
            check(table1 instanceof Value.Table && table2 instanceof Value.Table
                    && table1 != table2,
                "the two attempts re-executed the default block, so the mutable table "
                    + "defaults are freshly constructed per instance (distinct "
                    + "identities)");
            if (table1 instanceof Value.Table t1 && table2 instanceof Value.Table t2) {
                check(switch (t1.table().get("k")) {
                        case SemanticTable.Lookup.Present<Value> p ->
                            p.value().equals(Value.string("v"));
                        case SemanticTable.Lookup.Missing<Value> ignored -> false;
                    }
                    && switch (t2.table().get("k")) {
                        case SemanticTable.Lookup.Present<Value> p ->
                            p.value().equals(Value.string("v"));
                        case SemanticTable.Lookup.Missing<Value> ignored -> false;
                    },
                    "both fresh tables carry the equal default contents");
            }
            check(s1.value() != s2.value(),
                "each successful construction publishes a fresh instance identity");
        }
        check(log.size() == 2,
            "the default block re-executed once per construction attempt; got " + log);
    }

    // =========================================================================
    // 4. Fail-closed defects
    // =========================================================================

    static void testFailClosedDefects() {
        System.out.println("-- fail-closed: shapes outside the pinned contracts are "
            + "producer defects, never DEAL projections --");

        ClassLayout layout = layout(field("a", INT, true));
        ValueId vA = nextValue();
        Map<ValueId, Value> values = Map.of(vA, new Value.Int(1));
        SemanticOp defA = defaultOp("a", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        List<String> log = new ArrayList<>();
        BodyRunner body = new RecordingBodyRunner(log, Map.of(defA.opId(), new Value.Int(10)));
        BoundaryCheckRunner pass = new ScriptedDelegate(new ArrayList<>(), -1, null);

        List<ProvidedEntry> provided = List.of(new ProvidedEntry("a", vA));
        List<BoundaryEntry> entries = List.of(new BoundaryEntry("a",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vA,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        ClassNewFixture good = classNewFixture(layout, provided, List.of(), entries);
        Map<OpId, SemanticOp> goodBoundaryOps = reparent(good, entries);
        Map<ClassId, ClassLayout> layouts = Map.of(CLS, layout);

        // Wrong op kind and non-pinned policy.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                op(SemanticOpKind.CONST,
                    new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    nextValue(), INT, FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(), Map.of(), Map.of(), pass, body),
            "executing a CONST op as CLASS_NEW (wrong kind)");
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.NO_DEAL_FAILURE, null),
                Map.of(), Map.of(), Map.of(), layouts, pass, body),
            "a CLASS_NEW carrying a non-pinned failure policy");

        // Non-LOCAL owners and factory refs.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.SHARED_FACTORY, List.of(), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(), Map.of(), layouts, pass, body),
            "a SHARED_FACTORY owner (the later epic child's surface)");
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.RETAINED_ABI, List.of(), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(), Map.of(), layouts, pass, body),
            "a RETAINED_ABI owner (E10's surface)");
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(),
                        new deal.semantic.ir.ClassFactoryId(1), List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(), Map.of(), layouts, pass, body),
            "a LOCAL CLASS_NEW carrying a non-null classFactoryRef");

        // Layout resolution failures.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(good.op(),
                values, good.defaultOps(), goodBoundaryOps, Map.of(), pass, body),
            "an unresolvable layout in the layout-resolution context");
        ClassLayout foreign = new ClassLayout(CLS, List.of(field("z", INT, true)));
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(good.op(),
                values, good.defaultOps(), goodBoundaryOps, Map.of(CLS, foreign), pass, body),
            "a payload layout differing from the resolved layout");

        // Unresolvable and wrong-kind provided values.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(good.op(),
                Map.of(), good.defaultOps(), goodBoundaryOps, layouts, pass, body),
            "an unresolvable provided-field prior step");
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(good.op(),
                Map.of(vA, Value.Missing.INSTANCE), good.defaultOps(), goodBoundaryOps,
                layouts, pass, body),
            "a provided value resolving to the internal Missing view (wrong-kind value)");

        // Default-child defects.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                classNewFixture(layout, List.of(), List.of(
                    opWithId(nextOpId(), SemanticOpKind.CLASS_DEFAULT,
                        new KindPayload.ClassDefaultPayload(CLS, "a", new BlockId(1)),
                        nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null)),
                    List.of(new BoundaryEntry("a", BoundaryKind.CLASS_DEFAULT_FIELD,
                        boundaryChild(null, BoundaryKind.CLASS_DEFAULT_FIELD, INT,
                            nextValue(), FailurePolicyId.TYPE_DESCRIPTOR)))).op(),
                Map.of(), Map.of(), Map.of(), layouts, pass, body),
            "an unresolvable CLASS_DEFAULT child id");
        // Wrong default child kind: a CONST op id listed in classDefaultOpIds.
        SemanticOp constDefault = op(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(constDefault.opId()), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(constDefault.opId(), constDefault), Map.of(), layouts,
                pass, body),
            "a classDefaultOpIds entry naming a non-CLASS_DEFAULT op");
        SemanticOp badPolicyDefault = defaultOp("a", nextValue(), INT,
            FailurePolicyId.CLASS_CONSTRUCTION);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(badPolicyDefault.opId()), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(badPolicyDefault.opId(), badPolicyDefault), Map.of(),
                layouts, pass, body),
            "a CLASS_DEFAULT child carrying a non-pinned policy");
        SemanticOp foreignDefault = op(SemanticOpKind.CLASS_DEFAULT,
            new KindPayload.ClassDefaultPayload(new ClassId("other.mod", "C"), "a",
                new BlockId(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(foreignDefault.opId()), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(foreignDefault.opId(), foreignDefault), Map.of(), layouts,
                pass, body),
            "a CLASS_DEFAULT child of a different class");
        ClassLayout optionalLayout = layout(field("o", INT, false));
        SemanticOp optionalDefault = defaultOp("o", nextValue(), INT,
            FailurePolicyId.NO_DEAL_FAILURE);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, optionalLayout, List.of(),
                        DefaultOwner.LOCAL, List.of(optionalDefault.opId()), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(optionalDefault.opId(), optionalDefault), Map.of(),
                Map.of(CLS, optionalLayout), pass, body),
            "a CLASS_DEFAULT child naming an optional field (defaults never run for "
                + "optional fields at construction)");
        SemanticOp dupA = defaultOp("a", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL,
                        List.of(defA.opId(), dupA.opId()), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(defA.opId(), defA, dupA.opId(), dupA), Map.of(), layouts,
                pass, body),
            "two CLASS_DEFAULT children for the same field");

        // A CLASS_DEFAULT child publishing a non-ValueId result fails the
        // CLASS_DEFAULT_FIELD input wiring fail-closed.
        OpId tokenOpId = nextOpId();
        SemanticOp tokenDefault = opWithId(nextOpId(), SemanticOpKind.CLASS_DEFAULT,
            new KindPayload.ClassDefaultPayload(CLS, "a", new BlockId(1)),
            new AsyncTokenId.Canonical(7, AsyncTokenOwner.DEAL_BODY_TASK),
            INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp tokenBoundary = boundaryChild(tokenOpId, BoundaryKind.CLASS_DEFAULT_FIELD,
            INT, nextValue(), FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp tokenClassNew = opWithId(tokenOpId, SemanticOpKind.CLASS_NEW,
            new KindPayload.ClassNewPayload(CLS, layout, List.of(), DefaultOwner.LOCAL,
                List.of(tokenDefault.opId()), null,
                List.of(new KindPayload.FieldBoundary("a", BoundaryKind.CLASS_DEFAULT_FIELD,
                    tokenBoundary.opId()))),
            nextValue(), new RuntimeDescriptor.Class(CLS),
            FailurePolicyId.CLASS_CONSTRUCTION, null);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(tokenClassNew, Map.of(),
                Map.of(tokenDefault.opId(), tokenDefault),
                Map.of(tokenBoundary.opId(), tokenBoundary), layouts, pass,
                new RecordingBodyRunner(new ArrayList<>(),
                    Map.of(tokenDefault.opId(), new Value.Int(9)))),
            "a CLASS_DEFAULT child publishing a non-ValueId result");

        // Boundary-child defects (each child parented to the op that names
        // it, so the targeted check is the one that fires).
        OpId kindOpId = nextOpId();
        SemanticOp wrongKindChild = boundaryChild(kindOpId, BoundaryKind.CLASS_DEFAULT_FIELD,
            INT, vA, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(kindOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, wrongKindChild.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(wrongKindChild.opId(), wrongKindChild), layouts,
                pass, body),
            "a field-boundary entry whose child carries a different boundary kind");
        SemanticOp unparented = boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD,
            INT, vA, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, unparented.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(unparented.opId(), unparented), layouts, pass,
                body),
            "an unparented boundary child (parentOpId mismatch)");
        OpId constOpId = nextOpId();
        SemanticOp constChild = opWithId(nextOpId(), SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, constOpId);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(constOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, constChild.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(constChild.opId(), constChild), layouts, pass,
                body),
            "a field-boundary entry naming a non-BOUNDARY op");
        OpId policyOpId = nextOpId();
        SemanticOp badPolicy = boundaryChild(policyOpId, BoundaryKind.CLASS_LITERAL_FIELD,
            INT, vA, FailurePolicyId.INT32_RESULT);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(policyOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, badPolicy.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(badPolicy.opId(), badPolicy), layouts, pass, body),
            "a field boundary carrying a non-descriptor-kind policy");
        OpId descriptorOpId = nextOpId();
        SemanticOp badDescriptor = boundaryChild(descriptorOpId,
            BoundaryKind.CLASS_LITERAL_FIELD, STRING, vA, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(descriptorOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, badDescriptor.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(badDescriptor.opId(), badDescriptor), layouts,
                pass, body),
            "a field boundary carrying a descriptor different from the field's "
                + "declared descriptor");
        ValueId otherValue = nextValue();
        OpId inputOpId = nextOpId();
        SemanticOp badInput = boundaryChild(inputOpId, BoundaryKind.CLASS_LITERAL_FIELD,
            INT, otherValue, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(inputOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_LITERAL_FIELD, badInput.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(badInput.opId(), badInput), layouts, pass, body),
            "a CLASS_LITERAL_FIELD boundary whose input is not the field's provided "
                + "value op id (input-wiring mismatch)");
        ValueId wrongDefaultInput = nextValue();
        OpId defaultInputOpId = nextOpId();
        SemanticOp badDefaultInput = boundaryChild(defaultInputOpId,
            BoundaryKind.CLASS_DEFAULT_FIELD, INT, wrongDefaultInput,
            FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(defaultInputOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, List.of(),
                        DefaultOwner.LOCAL, List.of(defA.opId()), null,
                        List.of(new KindPayload.FieldBoundary("a",
                            BoundaryKind.CLASS_DEFAULT_FIELD, badDefaultInput.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                Map.of(), Map.of(defA.opId(), defA),
                Map.of(badDefaultInput.opId(), badDefaultInput), layouts, pass, body),
            "a CLASS_DEFAULT_FIELD boundary whose input is not the field's "
                + "CLASS_DEFAULT op result (input-wiring mismatch)");

        // Child-count/order/kind defects.
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(nextOpId(), SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, layout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null, List.of()),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(), Map.of(), layouts, pass, body),
            "a provided field without a field-boundary entry (child-count mismatch)");
        OpId optionalBoundaryOpId = nextOpId();
        SemanticOp optionalChild = boundaryChild(optionalBoundaryOpId,
            BoundaryKind.CLASS_DEFAULT_FIELD, INT, vA, FailurePolicyId.TYPE_DESCRIPTOR);
        ClassLayout optLayout = layout(field("a", INT, true), field("o", INT, false));
        expectDefect(() -> ClassOpsExecutor.executeClassNewLocal(
                opWithId(optionalBoundaryOpId, SemanticOpKind.CLASS_NEW,
                    new KindPayload.ClassNewPayload(CLS, optLayout, providedList(vA),
                        DefaultOwner.LOCAL, List.of(), null,
                        List.of(new KindPayload.FieldBoundary("a",
                                BoundaryKind.CLASS_LITERAL_FIELD, optionalChild.opId()),
                            new KindPayload.FieldBoundary("o",
                                BoundaryKind.CLASS_DEFAULT_FIELD, optionalChild.opId()))),
                    nextValue(), new RuntimeDescriptor.Class(CLS),
                    FailurePolicyId.CLASS_CONSTRUCTION, null),
                values, Map.of(),
                Map.of(optionalChild.opId(), optionalChild), Map.of(CLS, optLayout),
                pass, body),
            "a boundary entry for an omitted optional field (child-count mismatch)");
    }

    private static List<KindPayload.ProvidedField> providedList(ValueId valueId) {
        return List.of(new KindPayload.ProvidedField("a", valueId));
    }

    // =========================================================================
    // 5. Determinism
    // =========================================================================

    static void testDeterminism() {
        System.out.println("-- determinism: repeated executions with equal inputs "
            + "produce equal results --");

        ClassLayout layout = layout(field("a", INT, true), field("b", INT, false));
        ValueId vA = nextValue();
        Map<ValueId, Value> values = Map.of(vA, new Value.Int(5));
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("a", vA));
        List<BoundaryEntry> entries = List.of(new BoundaryEntry("a",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vA,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        ClassNewFixture fixture = classNewFixture(layout, provided, List.of(), entries);
        Map<OpId, SemanticOp> boundaryOps = reparent(fixture, entries);

        Outcome<Value> first = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            new ScriptedDelegate(new ArrayList<>(), -1, null),
            new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        Outcome<Value> second = ClassOpsExecutor.executeClassNewLocal(fixture.op(),
            values, fixture.defaultOps(), boundaryOps, Map.of(CLS, layout),
            new ScriptedDelegate(new ArrayList<>(), -1, null),
            new RecordingBodyRunner(new ArrayList<>(), Map.of()));
        check(first instanceof Outcome.Success<Value> s1
                && second instanceof Outcome.Success<Value> s2
                && s1.value().equals(s2.value()),
            "equal inputs produce equal published instances");
    }

    // =========================================================================
    // 6. Null arguments fail closed
    // =========================================================================

    static void testNullArgumentsFailClosed() {
        System.out.println("-- null arguments are producer defects (NPE), never projections --");

        ClassLayout layout = layout(field("a", INT, true));
        ValueId vA = nextValue();
        Map<ValueId, Value> values = Map.of(vA, new Value.Int(1));
        SemanticOp defA = defaultOp("a", nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE);
        BodyRunner body = new RecordingBodyRunner(new ArrayList<>(),
            Map.of(defA.opId(), new Value.Int(10)));
        BoundaryCheckRunner pass = new ScriptedDelegate(new ArrayList<>(), -1, null);
        List<ProvidedEntry> provided = List.of(new ProvidedEntry("a", vA));
        List<BoundaryEntry> entries = List.of(new BoundaryEntry("a",
            BoundaryKind.CLASS_LITERAL_FIELD,
            boundaryChild(null, BoundaryKind.CLASS_LITERAL_FIELD, INT, vA,
                FailurePolicyId.TYPE_DESCRIPTOR)));
        ClassNewFixture good = classNewFixture(layout, provided, List.of(), entries);
        Map<OpId, SemanticOp> goodBoundaryOps = reparent(good, entries);
        Map<ClassId, ClassLayout> layouts = Map.of(CLS, layout);

        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(null, values,
                good.defaultOps(), goodBoundaryOps, layouts, pass, body),
            "executeClassNewLocal with a null op");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), null,
                good.defaultOps(), goodBoundaryOps, layouts, pass, body),
            "executeClassNewLocal with a null value lookup");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), values,
                null, goodBoundaryOps, layouts, pass, body),
            "executeClassNewLocal with a null default-op lookup");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), values,
                good.defaultOps(), null, layouts, pass, body),
            "executeClassNewLocal with a null boundary lookup");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), values,
                good.defaultOps(), goodBoundaryOps, null, pass, body),
            "executeClassNewLocal with a null layout-resolution context");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), values,
                good.defaultOps(), goodBoundaryOps, layouts, null, body),
            "executeClassNewLocal with a null check runner");
        expectNpe(() -> ClassOpsExecutor.executeClassNewLocal(good.op(), values,
                good.defaultOps(), goodBoundaryOps, layouts, pass, null),
            "executeClassNewLocal with a null body runner");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Class Ops Executor Tests (ISSUE-0512 K-D4/K-D11) ===\n");

        testValueViewClassification();
        testClassDefaultExecution();
        testClassNewLocalSuccessReorderAndOverlay();
        testClassNewLocalDefaultsAndSkipProvided();
        testExtraKeyRejectionAfterDefaults();
        testBoundaryFailureStopsValidationAndPublishesNothing();
        testRealProjectionDelegate();
        testFreshDefaultsPerConstruction();
        testFailClosedDefects();
        testDeterminism();
        testNullArgumentsFailClosed();

        System.out.println("\nClassOpsExecutorTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
