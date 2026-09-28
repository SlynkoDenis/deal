package deal.test;

import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
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
import deal.semantic.ir.ClassOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryResult;
import deal.semantic.ir.ClassOpsExecutor.Defect;
import deal.semantic.ir.ClassOpsExecutor.FieldState;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
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
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
/**
 * Verifies the ISSUE-0513 field-operation slice of
 * {@link ClassOpsExecutor} (class-construction-jsonable-operations
 * K-D6/K-D7; parent D16 rows {@code FIELD_READ}/{@code FIELD_WRITE}/
 * {@code FIELD_DELETE}/{@code HAS_FIELD}): the op-level execution of
 * the field arms over the closed value view — the nominal receiver
 * boundary first, the presence-aware read (missing pre-maps to
 * language null before the {@code OPTIONAL_FIELD_READ} boundary), the
 * commit-only-after-both-boundaries write, the idempotent delete, and
 * the presence boolean of {@code has} — driven by fixture delegates
 * with side-effect probes and the real {@link BoundaryExecutor} as the
 * production-delegate stand-in for the canonical projections.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>the presence matrix (missing / present null / present value)
 *       through read, write, delete, and {@code has} on instances
 *       produced by T2's {@code CLASS_NEW} execution (the
 *       {@code executeClassNewLocal} drive) — reads publish the
 *       checked values, {@code has} returns true/false per the pinned
 *       semantics, writes land and later reads observe them, deletes
 *       turn present into missing and are idempotent;</li>
 *   <li>nominal receiver failures for read/write/delete — a null
 *       receiver fails E8001 {@code expected @corpus.fieldops/Point,
 *       got null} and a wrong-identity receiver fails with actual
 *       {@code class:@corpus.fieldops/Other} (the canonical
 *       descriptor-kind projections);</li>
 *   <li>the required-field missing read — a missing {@code x} of a
 *       defective instance pre-maps to null and the non-nullable
 *       result descriptor fails E8001 {@code expected int, got null};</li>
 *   <li>write-commit ordering — a failing
 *       {@code CLASS_FIELD_ASSIGNMENT} boundary commits nothing (the
 *       prior field state is unchanged and no updated instance
 *       exists); the receiver boundary runs first and its failure
 *       stops the field boundary;</li>
 *   <li>the receiver is consumed exactly once from the value lookup
 *       (a counting fixture proves no re-evaluation) and the stored
 *       value resolves exactly once;</li>
 *   <li>fail-closed defects — wrong op kinds/policies, a non-{@code
 *       ValueId} read result, boundary children of the wrong
 *       kind/parentage/realization/descriptor/policy/input,
 *       unresolvable/mismatched layouts, undeclared fields,
 *       field-count mismatches, and post-boundary shape violations are
 *       producer defects, never DEAL projections; null arguments throw
 *       the documented NPEs;</li>
 *   <li>determinism — repeated executions with equal inputs produce
 *       equal outcomes.</li>
 * </ol>
 */
public class FieldOpsExecutorTest {

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
    // Semantic-id and op builders (the ClassOpsExecutorTest discipline)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("corpus.fieldops");
    private static final ClassId CLS = new ClassId(MOD.path(), "Point");
    private static final ClassId OTHER_CLS = new ClassId(MOD.path(), "Other");
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor STRING = RuntimeDescriptor.String.INSTANCE;
    private static final RuntimeDescriptor NULLABLE_INT = new RuntimeDescriptor.Nullable(INT);
    private static final RuntimeDescriptor BOOLEAN = RuntimeDescriptor.Boolean.INSTANCE;

    private static final ClassLayout LAYOUT = layout(
        field("x", INT, true),
        field("y", INT, false),
        field("t", STRING, true));

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
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, payload instanceof KindPayload.SelectorCarrying carrying
                ? carrying.selector() : null,
            payload, policy, List.of(), digest);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OpId id = nextOpId();
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, nextOrigin(parent), result, resultType, List.of(),
            List.of(), payload, policy, contract);
    }

    private static ClassLayout.FieldLayout field(String name, RuntimeDescriptor descriptor,
                                                 boolean required) {
        return new ClassLayout.FieldLayout(name, descriptor, required, DefaultOwner.LOCAL);
    }

    private static ClassLayout layout(ClassLayout.FieldLayout... fields) {
        return new ClassLayout(CLS, List.of(fields));
    }

    /** A parented boundary child (the field-op cells, RuntimeValidation only). */
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

    /** The field state of the declared field {@code name} of one instance. */
    private static FieldState fieldState(Value.Class instance, ClassLayout layout, String name) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(name)) {
                return instance.fields().get(i);
            }
        }
        return null;
    }

    /** A class instance of {@code classId} with the named field states. */
    private static Value.Class instanceOf(ClassId classId, FieldState... states) {
        return new Value.Class(classId, List.of(states));
    }

    // =========================================================================
    // The T2 tie: the base instance is produced by CLASS_NEW execution
    // =========================================================================

    private record BaseInstanceFixture(Value.Class instance, Map<ValueId, Value> heap,
                                       ClassLayout layout) {
    }

    /**
     * Produces the presence-matrix base instance through T2's
     * {@code executeClassNewLocal} (K-D4): provided x=1 and t="v", the
     * optional y omitted — so y stays missing. The heap maps the
     * provided values' prior steps; the construction publishes the
     * instance under {@link #BASE_REF}.
     */
    private static final ValueId BASE_REF = new ValueId(9001);
    private static final ValueId X_REF = new ValueId(9002);
    private static final ValueId T_REF = new ValueId(9003);

    private static BaseInstanceFixture baseInstance(Map<String, Value> provided,
                                                    ClassLayout layout) {
        // The CLASS_NEW fixture: provided fields in literal order, the
        // pinned field boundaries, LOCAL ownership, no defaults.
        OpId classNewId = nextOpId();
        List<KindPayload.ProvidedField> providedFields = new ArrayList<>();
        List<KindPayload.FieldBoundary> boundaries = new ArrayList<>();
        Map<ValueId, Value> heap = new LinkedHashMap<>();
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            Value value = provided.get(fieldLayout.name());
            if (value == null) {
                continue;
            }
            ValueId providedId = nextValue();
            heap.put(providedId, value);
            providedFields.add(new KindPayload.ProvidedField(fieldLayout.name(), providedId));
            OpId childId = nextOpId();
            boundaries.add(new KindPayload.FieldBoundary(fieldLayout.name(),
                BoundaryKind.CLASS_LITERAL_FIELD, childId));
        }
        SemanticOp classNew = op(SemanticOpKind.CLASS_NEW,
            new KindPayload.ClassNewPayload(CLS, layout, providedFields, DefaultOwner.LOCAL,
                List.of(), null, boundaries),
            BASE_REF, new RuntimeDescriptor.Class(CLS), FailurePolicyId.CLASS_CONSTRUCTION,
            null);
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : boundaries) {
            SemanticOp child = boundaryChild(classNew.opId(), BoundaryKind.CLASS_LITERAL_FIELD,
                declaredField(layout, entry.field()).descriptor(), providedIdOf(providedFields,
                    entry.field()), descriptorKindPolicy(
                        declaredField(layout, entry.field()).descriptor()));
            boundaryOps.put(entry.boundaryOpId(), child);
        }
        ClassOpsExecutor.BoundaryCheckRunner pass = (boundary, input) ->
            new ClassOpsExecutor.BoundaryResult.Pass(input);
        ClassOpsExecutor.Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(
            classNew, heap, Map.of(), boundaryOps, Map.of(CLS, layout), pass,
            defaultOp -> { throw new IllegalStateException("no defaults in this fixture"); });
        if (!(outcome instanceof ClassOpsExecutor.Outcome.Success<Value> success
                && success.value() instanceof Value.Class instance)) {
            throw new IllegalStateException("the T2 CLASS_NEW drive must construct the base "
                + "instance (producer defect in the fixture): " + outcome);
        }
        heap.put(BASE_REF, instance);
        return new BaseInstanceFixture(instance, heap, layout);
    }

    private static ClassLayout.FieldLayout declaredField(ClassLayout layout, String name) {
        for (ClassLayout.FieldLayout fieldLayout : layout.fields()) {
            if (fieldLayout.name().equals(name)) {
                return fieldLayout;
            }
        }
        throw new IllegalStateException("fixture names an undeclared field " + name);
    }

    private static ValueId providedIdOf(List<KindPayload.ProvidedField> fields, String name) {
        for (KindPayload.ProvidedField field : fields) {
            if (field.name().equals(name)) {
                return field.valueOpId();
            }
        }
        return null;
    }

    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    // =========================================================================
    // Field-op fixtures (the pinned child shapes)
    // =========================================================================

    private record FieldReadFixture(SemanticOp op, SemanticOp receiverBoundary,
                                    SemanticOp fieldBoundary) {
    }

    private record FieldWriteFixture(SemanticOp op, SemanticOp receiverBoundary,
                                     SemanticOp fieldBoundary) {
    }

    private record FieldDeleteFixture(SemanticOp op, SemanticOp receiverBoundary) {
    }

    /** The read's checked result descriptor (the checker's optional-read wrap). */
    private static RuntimeDescriptor readResultDescriptor(ClassLayout layout, String field) {
        ClassLayout.FieldLayout fieldLayout = declaredField(layout, field);
        if (!fieldLayout.required() && !(fieldLayout.descriptor() instanceof RuntimeDescriptor.Nullable)) {
            return new RuntimeDescriptor.Nullable(fieldLayout.descriptor());
        }
        return fieldLayout.descriptor();
    }

    private static FieldReadFixture fieldReadFixture(ValueId receiver, ClassId classId,
                                                     String field, ClassLayout layout) {
        ValueId result = nextValue();
        SemanticOp read = op(SemanticOpKind.FIELD_READ,
            new KindPayload.FieldReadPayload(receiver, classId, field),
            result, readResultDescriptor(layout, field), FailurePolicyId.NO_DEAL_FAILURE, null);
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(classId);
        SemanticOp receiverBoundary = boundaryChild(read.opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor, receiver,
            descriptorKindPolicy(classDescriptor));
        SemanticOp fieldBoundary = boundaryChild(read.opId(),
            BoundaryKind.OPTIONAL_FIELD_READ, readResultDescriptor(layout, field), result,
            descriptorKindPolicy(readResultDescriptor(layout, field)));
        return new FieldReadFixture(read, receiverBoundary, fieldBoundary);
    }

    private static FieldWriteFixture fieldWriteFixture(ValueId receiver, ClassId classId,
                                                       String field, ClassLayout layout,
                                                       ValueId stored) {
        SemanticOp write = op(SemanticOpKind.FIELD_WRITE,
            new KindPayload.FieldWritePayload(receiver, classId, field, stored),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(classId);
        SemanticOp receiverBoundary = boundaryChild(write.opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor, receiver,
            descriptorKindPolicy(classDescriptor));
        RuntimeDescriptor declared = declaredField(layout, field).descriptor();
        SemanticOp fieldBoundary = boundaryChild(write.opId(),
            BoundaryKind.CLASS_FIELD_ASSIGNMENT, declared, stored,
            descriptorKindPolicy(declared));
        return new FieldWriteFixture(write, receiverBoundary, fieldBoundary);
    }

    private static FieldDeleteFixture fieldDeleteFixture(ValueId receiver, ClassId classId,
                                                         String field) {
        SemanticOp delete = op(SemanticOpKind.FIELD_DELETE,
            new KindPayload.FieldDeletePayload(receiver, classId, field),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(classId);
        SemanticOp receiverBoundary = boundaryChild(delete.opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor, receiver,
            descriptorKindPolicy(classDescriptor));
        return new FieldDeleteFixture(delete, receiverBoundary);
    }

    private static SemanticOp hasFieldOp(ValueId receiver, String key) {
        return op(SemanticOpKind.HAS_FIELD,
            new KindPayload.HasFieldPayload(receiver, key),
            nextValue(), BOOLEAN, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    // =========================================================================
    // The production-delegate stand-in (the real BoundaryExecutor)
    // =========================================================================

    private static BoundaryCheckRunner realDelegate(List<String> log) {
        return (boundary, input) -> {
            if (log != null) {
                log.add("child " + boundary.kind() + " <- " + tokenOf(input));
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

    /** A passing boundary never copies or converts: null views map to the explicit null. */
    private static Value publishValue(BoundaryValueView view, Value input) {
        return view.kind() == ActualKind.NULL ? Value.Null.INSTANCE : input;
    }

    /** A pass-through fixture delegate recording order. */
    private static BoundaryCheckRunner passThrough(List<String> log) {
        return (boundary, input) -> {
            if (log != null) {
                log.add("child " + boundary.kind() + " <- " + tokenOf(input));
            }
            return new BoundaryResult.Pass(input);
        };
    }

    /** The canonical token of one value (a class value renders class:<ClassId>). */
    private static String tokenOf(Value input) {
        return input.actualKind() == ActualKind.CLASS
            ? "class:" + ((Value.Class) input).classId().text()
            : input.actualKind().token();
    }

    private static BoundaryCheckRunner failFirst() {
        return (boundary, input) -> new BoundaryResult.Fail(BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
            boundary.descriptor().canonicalSpecText(), "number", new LinkedHashMap<>(), null));
    }

    // =========================================================================
    // (a) the T2 tie and the read presence matrix
    // =========================================================================

    private static void testT2InstanceFeedsFieldReads() {
        System.out.println("-- T2 tie: the CLASS_NEW-produced instance feeds FIELD_READ --");

        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);
        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        List<String> log = new ArrayList<>();

        FieldReadFixture x = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> xRead = ClassOpsExecutor.executeFieldRead(x.op(), base.heap(),
            x.receiverBoundary(), x.fieldBoundary(), layouts, realDelegate(log));
        check(xRead instanceof Outcome.Success<Value> xSuccess
                && xSuccess.value().equals(new Value.Int(1)),
            "reading the required present x publishes the checked value 1; got " + xRead);
        check(log.size() == 2
                && log.get(0).equals("child UNTYPED_CLASS_INPUT <- class:" + CLS.text())
                && log.get(1).equals("child OPTIONAL_FIELD_READ <- int"),
            "the nominal receiver boundary runs first, then the field boundary; got " + log);

        FieldReadFixture t = fieldReadFixture(BASE_REF, CLS, "t", LAYOUT);
        Outcome<Value> tRead = ClassOpsExecutor.executeFieldRead(t.op(), base.heap(),
            t.receiverBoundary(), t.fieldBoundary(), layouts, realDelegate(null));
        check(tRead instanceof Outcome.Success<Value> tSuccess
                && tSuccess.value().equals(Value.string("v")),
            "reading the required present t publishes the checked value 'v'; got " + tRead);

        FieldReadFixture y = fieldReadFixture(BASE_REF, CLS, "y", LAYOUT);
        Outcome<Value> yRead = ClassOpsExecutor.executeFieldRead(y.op(), base.heap(),
            y.receiverBoundary(), y.fieldBoundary(), layouts, realDelegate(null));
        check(yRead instanceof Outcome.Success<Value> ySuccess
                && ySuccess.value() == Value.Null.INSTANCE,
            "reading the omitted optional y pre-maps missing to null and the nullable "
                + "boundary passes; got " + yRead);
    }

    private static void testReadPresenceMatrix() {
        System.out.println("-- read presence matrix: missing / present null / present value --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);

        // y present-null through T2's CLASS_NEW (provided y = null).
        BaseInstanceFixture nullY = baseInstance(
            Map.of("x", new Value.Int(1), "y", Value.Null.INSTANCE, "t", Value.string("v")),
            LAYOUT);
        FieldReadFixture yRead = fieldReadFixture(BASE_REF, CLS, "y", LAYOUT);
        Outcome<Value> presentNull = ClassOpsExecutor.executeFieldRead(yRead.op(),
            nullY.heap(), yRead.receiverBoundary(), yRead.fieldBoundary(), layouts,
            realDelegate(null));
        check(presentNull instanceof Outcome.Success<Value> presentNullSuccess
                && presentNullSuccess.value() == Value.Null.INSTANCE,
            "reading a present-null optional field publishes null (present null passes the "
                + "nullable descriptor); got " + presentNull);

        // y present-value through T2's CLASS_NEW (provided y = 7).
        BaseInstanceFixture valueY = baseInstance(
            Map.of("x", new Value.Int(1), "y", new Value.Int(7), "t", Value.string("v")),
            LAYOUT);
        Outcome<Value> presentValue = ClassOpsExecutor.executeFieldRead(yRead.op(),
            valueY.heap(), yRead.receiverBoundary(), yRead.fieldBoundary(), layouts,
            realDelegate(null));
        check(presentValue instanceof Outcome.Success<Value> presentValueSuccess
                && presentValueSuccess.value().equals(new Value.Int(7)),
            "reading a present-value optional field publishes the checked value 7; got "
                + presentValue);

        // The required-field missing read: a defective instance whose
        // required x is missing — the pre-map to null crosses the
        // non-nullable int descriptor and fails E8001 expected int, got null.
        Value.Class defective = instanceOf(CLS,
            FieldState.Missing.INSTANCE, FieldState.Missing.INSTANCE,
            new FieldState.Present(Value.string("v")));
        Map<ValueId, Value> defectiveHeap = Map.of(BASE_REF, defective);
        FieldReadFixture xRead = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> requiredMissing = ClassOpsExecutor.executeFieldRead(xRead.op(),
            defectiveHeap, xRead.receiverBoundary(), xRead.fieldBoundary(), layouts,
            realDelegate(null));
        check(requiredMissing instanceof Outcome.Failure<Value> requiredFail
                && requiredFail.failure().failure().code() == DiagnosticCode.E8001
                && "expected int, got null".equals(requiredFail.failure().failure().message())
                && "int".equals(requiredFail.failure().failure().expected())
                && "null".equals(requiredFail.failure().failure().actual())
                && requiredFail.failure().origin().equals(xRead.op().origin()),
            "a missing required field pre-maps to null and the non-nullable descriptor "
                + "fails E8001 'expected int, got null' at the op origin; got "
                + requiredMissing);
    }

    private static void testNominalReceiverFailures() {
        System.out.println("-- nominal receiver failures: got null / got class:<other> --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        String classText = CLS.text();

        // (a) null receiver — read/write/delete.
        Map<ValueId, Value> nullHeap = Map.of(BASE_REF, Value.Null.INSTANCE);
        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> nullRead = ClassOpsExecutor.executeFieldRead(read.op(), nullHeap,
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        check(nullRead instanceof Outcome.Failure<Value> nullReadFail
                && nullReadFail.failure().failure().code() == DiagnosticCode.E8001
                && ("expected " + classText + ", got null")
                    .equals(nullReadFail.failure().failure().message())
                && "null".equals(nullReadFail.failure().failure().actual()),
            "a null receiver read fails E8001 'expected " + classText + ", got null'; got "
                + nullRead);

        ValueId stored = nextValue();
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, stored);
        Map<ValueId, Value> nullWriteHeap = new LinkedHashMap<>();
        nullWriteHeap.put(BASE_REF, Value.Null.INSTANCE);
        nullWriteHeap.put(stored, new Value.Int(9));
        Outcome<Value> nullWrite = ClassOpsExecutor.executeFieldWrite(write.op(),
            nullWriteHeap, write.receiverBoundary(), write.fieldBoundary(), layouts,
            realDelegate(null));
        check(nullWrite instanceof Outcome.Failure<Value> nullWriteFail
                && nullWriteFail.failure().failure().code() == DiagnosticCode.E8001
                && ("expected " + classText + ", got null")
                    .equals(nullWriteFail.failure().failure().message()),
            "a null receiver write fails E8001 'expected " + classText + ", got null'; got "
                + nullWrite);

        FieldDeleteFixture delete = fieldDeleteFixture(BASE_REF, CLS, "y");
        Outcome<Value> nullDelete = ClassOpsExecutor.executeFieldDelete(delete.op(),
            nullHeap, delete.receiverBoundary(), layouts, realDelegate(null));
        check(nullDelete instanceof Outcome.Failure<Value> nullDeleteFail
                && nullDeleteFail.failure().failure().code() == DiagnosticCode.E8001
                && ("expected " + classText + ", got null")
                    .equals(nullDeleteFail.failure().failure().message()),
            "a null receiver delete fails E8001 'expected " + classText + ", got null'; got "
                + nullDelete);

        // (b) wrong-identity receiver — read/write/delete.
        Value.Class other = instanceOf(OTHER_CLS, new FieldState.Present(new Value.Int(3)));
        Map<ValueId, Value> otherHeap = Map.of(BASE_REF, other);
        Outcome<Value> wrongRead = ClassOpsExecutor.executeFieldRead(read.op(), otherHeap,
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        check(wrongRead instanceof Outcome.Failure<Value> wrongReadFail
                && wrongReadFail.failure().failure().code() == DiagnosticCode.E8001
                && ("expected " + classText + ", got class:" + OTHER_CLS.text())
                    .equals(wrongReadFail.failure().failure().message())
                && ("class:" + OTHER_CLS.text())
                    .equals(wrongReadFail.failure().failure().actual()),
            "a wrong-identity receiver read fails E8001 with actual class:<other>; got "
                + wrongRead);

        Map<ValueId, Value> otherWriteHeap = new LinkedHashMap<>();
        otherWriteHeap.put(BASE_REF, other);
        otherWriteHeap.put(stored, new Value.Int(9));
        Outcome<Value> wrongWrite = ClassOpsExecutor.executeFieldWrite(write.op(),
            otherWriteHeap, write.receiverBoundary(), write.fieldBoundary(), layouts,
            realDelegate(null));
        check(wrongWrite instanceof Outcome.Failure<Value> wrongWriteFail
                && wrongWriteFail.failure().failure().code() == DiagnosticCode.E8001
                && ("class:" + OTHER_CLS.text())
                    .equals(wrongWriteFail.failure().failure().actual()),
            "a wrong-identity receiver write fails E8001 with actual class:<other>; got "
                + wrongWrite);

        Outcome<Value> wrongDelete = ClassOpsExecutor.executeFieldDelete(delete.op(),
            otherHeap, delete.receiverBoundary(), layouts, realDelegate(null));
        check(wrongDelete instanceof Outcome.Failure<Value> wrongDeleteFail
                && wrongDeleteFail.failure().failure().code() == DiagnosticCode.E8001
                && ("class:" + OTHER_CLS.text())
                    .equals(wrongDeleteFail.failure().failure().actual()),
            "a wrong-identity receiver delete fails E8001 with actual class:<other>; got "
                + wrongDelete);
    }

    // =========================================================================
    // (b) write commit ordering and the presence matrix through writes
    // =========================================================================

    private static void testWriteCommitOrderingAndPresence() {
        System.out.println("-- write commit ordering: both boundaries pass, then the "
            + "store; a failing field boundary commits nothing --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);

        // A successful write of the required x: the updated instance
        // carries the committed value; the other fields are unchanged.
        ValueId stored = nextValue();
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, stored);
        List<String> log = new ArrayList<>();
        Map<ValueId, Value> writeHeap = new LinkedHashMap<>(base.heap());
        writeHeap.put(stored, new Value.Int(9));
        Outcome<Value> committed = ClassOpsExecutor.executeFieldWrite(write.op(), writeHeap,
            write.receiverBoundary(), write.fieldBoundary(), layouts, realDelegate(log));
        check(committed instanceof Outcome.Success<Value> committedSuccess
                && committedSuccess.value() instanceof Value.Class updated
                && updated.classId().equals(CLS)
                && fieldValue(updated, LAYOUT, "x").equals(new Value.Int(9))
                && fieldState(updated, LAYOUT, "y") == FieldState.Missing.INSTANCE
                && fieldValue(updated, LAYOUT, "t").equals(Value.string("v")),
            "the successful write publishes the updated instance with x=9, y still "
                + "missing, t unchanged; got " + committed);
        check(log.size() == 2
                && log.get(0).equals("child UNTYPED_CLASS_INPUT <- class:" + CLS.text())
                && log.get(1).equals("child CLASS_FIELD_ASSIGNMENT <- int"),
            "the write runs the receiver boundary first, then the field boundary; got "
                + log);

        // A later read observes the write (the caller rebinds the heap).
        Map<ValueId, Value> rebounded = new LinkedHashMap<>(writeHeap);
        rebounded.put(BASE_REF, ((Outcome.Success<Value>) committed).value());
        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> observed = ClassOpsExecutor.executeFieldRead(read.op(), rebounded,
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        check(observed instanceof Outcome.Success<Value> observedSuccess
                && observedSuccess.value().equals(new Value.Int(9)),
            "a later read observes the committed write; got " + observed);

        // A successful optional-field write: y=3 lands and later reads
        // observe it (the checker's write context admits it).
        ValueId yStored = nextValue();
        FieldWriteFixture yWrite = fieldWriteFixture(BASE_REF, CLS, "y", LAYOUT, yStored);
        Map<ValueId, Value> yHeap = new LinkedHashMap<>(rebounded);
        yHeap.put(yStored, new Value.Int(3));
        Outcome<Value> yCommitted = ClassOpsExecutor.executeFieldWrite(yWrite.op(), yHeap,
            yWrite.receiverBoundary(), yWrite.fieldBoundary(), layouts, realDelegate(null));
        check(yCommitted instanceof Outcome.Success<Value> yCommittedSuccess
                && yCommittedSuccess.value() instanceof Value.Class yUpdated
                && fieldValue(yUpdated, LAYOUT, "y").equals(new Value.Int(3)),
            "the optional-field write y=3 lands; got " + yCommitted);

        // A failing field boundary commits nothing: writing the string
        // 's' to the int field x fails the CLASS_FIELD_ASSIGNMENT
        // boundary (the declared descriptor) and the prior state is
        // unchanged — the original instance is untouched and no updated
        // instance exists.
        ValueId badStored = nextValue();
        FieldWriteFixture badWrite = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, badStored);
        Map<ValueId, Value> badHeap = new LinkedHashMap<>(rebounded);
        badHeap.put(badStored, Value.string("s"));
        Outcome<Value> badCommitted = ClassOpsExecutor.executeFieldWrite(badWrite.op(),
            badHeap, badWrite.receiverBoundary(), badWrite.fieldBoundary(), layouts,
            realDelegate(null));
        check(badCommitted instanceof Outcome.Failure<Value> badFail
                && badFail.failure().failure().code() == DiagnosticCode.E8001
                && "expected int, got string".equals(badFail.failure().failure().message()),
            "a wrong-kind stored value fails the CLASS_FIELD_ASSIGNMENT boundary E8001 "
                + "'expected int, got string'; got " + badCommitted);
        check(fieldValue(base.instance(), LAYOUT, "x").equals(new Value.Int(1))
                && fieldState(base.instance(), LAYOUT, "y") == FieldState.Missing.INSTANCE
                && fieldValue(base.instance(), LAYOUT, "t").equals(Value.string("v")),
            "a failed write commits nothing: the receiver instance state is unchanged "
                + "(x=1, y missing, t='v')");

        // A failing receiver boundary stops the field boundary: the
        // field boundary never runs (the log holds only the receiver
        // child) and nothing commits.
        Map<ValueId, Value> nullHeap = new LinkedHashMap<>();
        nullHeap.put(BASE_REF, Value.Null.INSTANCE);
        nullHeap.put(stored, new Value.Int(9));
        List<String> stopped = new ArrayList<>();
        Outcome<Value> stoppedOutcome = ClassOpsExecutor.executeFieldWrite(write.op(),
            nullHeap, write.receiverBoundary(), write.fieldBoundary(), layouts,
            realDelegate(stopped));
        check(stoppedOutcome instanceof Outcome.Failure<Value>
                && stopped.size() == 1
                && stopped.get(0).equals("child UNTYPED_CLASS_INPUT <- null"),
            "a failing receiver boundary runs once and the field boundary never runs; got "
                + stopped);
    }

    // =========================================================================
    // (c) delete idempotency and the presence matrix through deletes
    // =========================================================================

    private static void testDeleteTurnsPresentIntoMissingAndIsIdempotent() {
        System.out.println("-- delete: present becomes missing; already-missing is a "
            + "no-op SUCCESS --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "y", new Value.Int(7), "t", Value.string("v")),
            LAYOUT);

        FieldDeleteFixture delete = fieldDeleteFixture(BASE_REF, CLS, "y");
        Outcome<Value> deleted = ClassOpsExecutor.executeFieldDelete(delete.op(), base.heap(),
            delete.receiverBoundary(), layouts, realDelegate(null));
        check(deleted instanceof Outcome.Success<Value> deletedSuccess
                && deletedSuccess.value() instanceof Value.Class afterDelete
                && fieldState(afterDelete, LAYOUT, "y") == FieldState.Missing.INSTANCE
                && fieldValue(afterDelete, LAYOUT, "x").equals(new Value.Int(1))
                && fieldValue(afterDelete, LAYOUT, "t").equals(Value.string("v")),
            "the delete turns present y into missing and every other field is unchanged; "
                + "got " + deleted);

        Map<ValueId, Value> afterDeleteHeap = new LinkedHashMap<>(base.heap());
        afterDeleteHeap.put(BASE_REF, ((Outcome.Success<Value>) deleted).value());
        Outcome<Value> again = ClassOpsExecutor.executeFieldDelete(delete.op(),
            afterDeleteHeap, delete.receiverBoundary(), layouts, realDelegate(null));
        check(again instanceof Outcome.Success<Value> againSuccess
                && againSuccess.value() instanceof Value.Class afterAgain
                && fieldState(afterAgain, LAYOUT, "y") == FieldState.Missing.INSTANCE,
            "deleting an already-missing field is a no-op SUCCESS; got " + again);
    }

    // =========================================================================
    // (d) has presence semantics
    // =========================================================================

    private static void testHasPresenceMatrix() {
        System.out.println("-- has: present (present null included) -> true, missing -> "
            + "false --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture missing = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);
        SemanticOp hasY = hasFieldOp(BASE_REF, "y");
        Outcome<Value> missingOutcome = ClassOpsExecutor.executeHasField(hasY, missing.heap(),
            layouts);
        check(missingOutcome instanceof Outcome.Success<Value> missingSuccess
                && missingSuccess.value().equals(new Value.Bool(false)),
            "has(y) on a missing field publishes false; got " + missingOutcome);

        BaseInstanceFixture presentNull = baseInstance(
            Map.of("x", new Value.Int(1), "y", Value.Null.INSTANCE, "t", Value.string("v")),
            LAYOUT);
        Outcome<Value> nullOutcome = ClassOpsExecutor.executeHasField(hasY, presentNull.heap(),
            layouts);
        check(nullOutcome instanceof Outcome.Success<Value> nullSuccess
                && nullSuccess.value().equals(new Value.Bool(true)),
            "has(y) on a present-null field publishes true (present null is present); got "
                + nullOutcome);

        BaseInstanceFixture presentValue = baseInstance(
            Map.of("x", new Value.Int(1), "y", new Value.Int(7), "t", Value.string("v")),
            LAYOUT);
        Outcome<Value> valueOutcome = ClassOpsExecutor.executeHasField(hasY,
            presentValue.heap(), layouts);
        check(valueOutcome instanceof Outcome.Success<Value> valueSuccess
                && valueSuccess.value().equals(new Value.Bool(true)),
            "has(y) on a present-value field publishes true; got " + valueOutcome);

        SemanticOp hasX = hasFieldOp(BASE_REF, "x");
        Outcome<Value> requiredOutcome = ClassOpsExecutor.executeHasField(hasX,
            missing.heap(), layouts);
        check(requiredOutcome instanceof Outcome.Success<Value> requiredSuccess
                && requiredSuccess.value().equals(new Value.Bool(true)),
            "has(x) on the present required field publishes true; got " + requiredOutcome);
    }

    // =========================================================================
    // (e) the receiver is consumed exactly once
    // =========================================================================

    private static void testReceiverConsumedExactlyOnce() {
        System.out.println("-- single evaluation: the receiver and the stored value each "
            + "resolve exactly once --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);

        CountingMap readHeap = new CountingMap(base.heap());
        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> readOutcome = ClassOpsExecutor.executeFieldRead(read.op(), readHeap,
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        check(readOutcome instanceof Outcome.Success<Value>,
            "the read succeeds over the counting lookup; got " + readOutcome);
        check(readHeap.gets(BASE_REF) == 1 && readHeap.totalGets() == 1,
            "the read resolves the receiver exactly once and resolves nothing else; got "
                + readHeap.summary());

        ValueId stored = nextValue();
        CountingMap writeHeap = new CountingMap(base.heap());
        writeHeap.put(stored, new Value.Int(9));
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, stored);
        Outcome<Value> writeOutcome = ClassOpsExecutor.executeFieldWrite(write.op(),
            writeHeap, write.receiverBoundary(), write.fieldBoundary(), layouts,
            realDelegate(null));
        check(writeOutcome instanceof Outcome.Success<Value>,
            "the write succeeds over the counting lookup; got " + writeOutcome);
        check(writeHeap.gets(BASE_REF) == 1 && writeHeap.gets(stored) == 1
                && writeHeap.totalGets() == 2,
            "the write resolves the receiver and the stored value exactly once each; got "
                + writeHeap.summary());

        CountingMap deleteHeap = new CountingMap(base.heap());
        FieldDeleteFixture delete = fieldDeleteFixture(BASE_REF, CLS, "y");
        Outcome<Value> deleteOutcome = ClassOpsExecutor.executeFieldDelete(delete.op(),
            deleteHeap, delete.receiverBoundary(), layouts, realDelegate(null));
        check(deleteOutcome instanceof Outcome.Success<Value>
                && deleteHeap.gets(BASE_REF) == 1 && deleteHeap.totalGets() == 1,
            "the delete resolves the receiver exactly once; got " + deleteHeap.summary());

        CountingMap hasHeap = new CountingMap(base.heap());
        SemanticOp has = hasFieldOp(BASE_REF, "y");
        Outcome<Value> hasOutcome = ClassOpsExecutor.executeHasField(has, hasHeap, layouts);
        check(hasOutcome instanceof Outcome.Success<Value>
                && hasHeap.gets(BASE_REF) == 1 && hasHeap.totalGets() == 1,
            "has resolves the receiver exactly once (the key is the static payload "
                + "name, never evaluated); got " + hasHeap.summary());
    }

    /** A value lookup counting every get per key (the no-re-evaluation probe). */
    private static final class CountingMap implements Map<ValueId, Value> {

        private final Map<ValueId, Value> delegate = new LinkedHashMap<>();
        private final Map<ValueId, Integer> gets = new LinkedHashMap<>();

        CountingMap(Map<ValueId, Value> initial) {
            delegate.putAll(initial);
        }

        int gets(ValueId key) {
            return gets.getOrDefault(key, 0);
        }

        int totalGets() {
            int total = 0;
            for (int count : gets.values()) {
                total += count;
            }
            return total;
        }

        String summary() {
            return "gets=" + gets;
        }

        @Override
        public int size() { return delegate.size(); }

        @Override
        public boolean isEmpty() { return delegate.isEmpty(); }

        @Override
        public boolean containsKey(Object key) { return delegate.containsKey(key); }

        @Override
        public boolean containsValue(Object value) { return delegate.containsValue(value); }

        @Override
        public Value get(Object key) {
            gets.merge((ValueId) key, 1, Integer::sum);
            return delegate.get(key);
        }

        @Override
        public Value put(ValueId key, Value value) { return delegate.put(key, value); }

        @Override
        public Value remove(Object key) { return delegate.remove(key); }

        @Override
        public void putAll(Map<? extends ValueId, ? extends Value> m) { delegate.putAll(m); }

        @Override
        public void clear() { delegate.clear(); }

        @Override
        public java.util.Set<ValueId> keySet() { return delegate.keySet(); }

        @Override
        public java.util.Collection<Value> values() { return delegate.values(); }

        @Override
        public java.util.Set<Entry<ValueId, Value>> entrySet() { return delegate.entrySet(); }
    }

    // =========================================================================
    // (f) fail-closed defects
    // =========================================================================

    private static void testFailClosedDefects() {
        System.out.println("-- fail-closed defects: wrong shapes are Defects, never "
            + "DEAL projections --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);

        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, nextValue());
        FieldDeleteFixture delete = fieldDeleteFixture(BASE_REF, CLS, "y");
        SemanticOp has = hasFieldOp(BASE_REF, "y");
        BoundaryCheckRunner pass = passThrough(null);

        // Wrong op kinds and policies.
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(write.op(), base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a FIELD_WRITE op");
        SemanticOp wrongPolicyRead = op(SemanticOpKind.FIELD_READ,
            new KindPayload.FieldReadPayload(BASE_REF, CLS, "x"),
            read.op().result(), INT, FailurePolicyId.TYPE_DESCRIPTOR, null);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(wrongPolicyRead, base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a TYPE_DESCRIPTOR FIELD_READ op");
        expectDefect(() -> ClassOpsExecutor.executeFieldDelete(write.op(), base.heap(),
                delete.receiverBoundary(), layouts, pass),
            "executeFieldDelete with a FIELD_WRITE op");

        // A non-ValueId read result.
        SemanticOp noResult = op(SemanticOpKind.FIELD_READ,
            new KindPayload.FieldReadPayload(BASE_REF, CLS, "x"),
            null, INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(noResult, base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a null (non-ValueId) result");

        // Child kind mismatches.
        SemanticOp wrongReceiverKind = boundaryChild(read.op().opId(),
            BoundaryKind.CLASS_FIELD_ASSIGNMENT, new RuntimeDescriptor.Class(CLS), BASE_REF,
            FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                wrongReceiverKind, read.fieldBoundary(), layouts, pass),
            "a receiver child of kind CLASS_FIELD_ASSIGNMENT");
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                read.receiverBoundary(), read.receiverBoundary(), layouts, pass),
            "a field child of kind UNTYPED_CLASS_INPUT");

        // Child parentage mismatches.
        SemanticOp unparented = boundaryChild(null, BoundaryKind.UNTYPED_CLASS_INPUT,
            new RuntimeDescriptor.Class(CLS), BASE_REF, FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                unparented, read.fieldBoundary(), layouts, pass),
            "a receiver child parented to no op");

        // Child descriptor mismatches.
        SemanticOp wrongDescriptor = boundaryChild(read.op().opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, new RuntimeDescriptor.Class(OTHER_CLS), BASE_REF,
            FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                wrongDescriptor, read.fieldBoundary(), layouts, pass),
            "a receiver child of the wrong class descriptor");

        // Child input mismatches.
        ValueId otherInput = nextValue();
        SemanticOp wrongInput = boundaryChild(read.op().opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, new RuntimeDescriptor.Class(CLS), otherInput,
            FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                wrongInput, read.fieldBoundary(), layouts, pass),
            "a receiver child input different from the payload's classValue");

        // Child policy mismatches.
        SemanticOp wrongPolicy = boundaryChild(read.op().opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, new RuntimeDescriptor.Class(CLS), BASE_REF,
            FailurePolicyId.ARRAY_DELETE_BOUNDS);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                wrongPolicy, read.fieldBoundary(), layouts, pass),
            "a receiver child with a non-descriptor-kind policy");

        // A RepresentationProof realization is inadmissible on these cells.
        SemanticOp proofChild = op(SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(BoundaryKind.UNTYPED_CLASS_INPUT,
                new RuntimeDescriptor.Class(CLS), BASE_REF,
                new BoundaryRealization.RepresentationProof("proof")),
            null, null, FailurePolicyId.TYPE_DESCRIPTOR, read.op().opId());
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                proofChild, read.fieldBoundary(), layouts, pass),
            "a RepresentationProof receiver child");

        // Unresolvable layouts and undeclared fields.
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), Map.of(), pass),
            "executeFieldRead with an empty layout-resolution context");
        ValueId undeclaredResult = nextValue();
        SemanticOp undeclaredRead = op(SemanticOpKind.FIELD_READ,
            new KindPayload.FieldReadPayload(BASE_REF, CLS, "zz"), undeclaredResult, INT,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp undeclaredReceiver = boundaryChild(undeclaredRead.opId(),
            BoundaryKind.UNTYPED_CLASS_INPUT, new RuntimeDescriptor.Class(CLS), BASE_REF,
            FailurePolicyId.TYPE_DESCRIPTOR);
        SemanticOp undeclaredField = boundaryChild(undeclaredRead.opId(),
            BoundaryKind.OPTIONAL_FIELD_READ, INT, undeclaredResult,
            FailurePolicyId.TYPE_DESCRIPTOR);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(undeclaredRead, base.heap(),
                undeclaredReceiver, undeclaredField, layouts, pass),
            "a read of an undeclared field");

        // Field-count mismatches.
        Value.Class shortInstance = instanceOf(CLS,
            new FieldState.Present(new Value.Int(1)));
        Map<ValueId, Value> shortHeap = Map.of(BASE_REF, shortInstance);
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(), shortHeap,
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "an instance whose field count mismatches the layout");

        // Post-boundary shape violations through a pass-through fixture.
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(),
                Map.of(BASE_REF, Value.Null.INSTANCE),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "a null receiver passing a pass-through receiver boundary");
        expectDefect(() -> ClassOpsExecutor.executeFieldRead(read.op(),
                Map.of(BASE_REF, instanceOf(OTHER_CLS,
                    new FieldState.Present(new Value.Int(3)))),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "a wrong-identity instance passing a pass-through receiver boundary");
        expectDefect(() -> ClassOpsExecutor.executeHasField(has,
                Map.of(BASE_REF, new Value.Int(4)), layouts),
            "a non-class has receiver");
        expectDefect(() -> ClassOpsExecutor.executeHasField(has, base.heap(), Map.of()),
            "executeHasField with an empty layout-resolution context");
        SemanticOp undeclaredHas = hasFieldOp(BASE_REF, "zz");
        expectDefect(() -> ClassOpsExecutor.executeHasField(undeclaredHas, base.heap(),
                layouts),
            "has of an undeclared key");
    }

    // =========================================================================
    // (g) determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- determinism: equal inputs produce equal outcomes --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);
        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        Outcome<Value> first = ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        Outcome<Value> second = ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
            read.receiverBoundary(), read.fieldBoundary(), layouts, realDelegate(null));
        check(first.equals(second), "repeated reads with equal inputs produce equal outcomes");

        ValueId stored = nextValue();
        Map<ValueId, Value> writeHeap = new LinkedHashMap<>(base.heap());
        writeHeap.put(stored, new Value.Int(9));
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, stored);
        Outcome<Value> firstWrite = ClassOpsExecutor.executeFieldWrite(write.op(), writeHeap,
            write.receiverBoundary(), write.fieldBoundary(), layouts, realDelegate(null));
        Outcome<Value> secondWrite = ClassOpsExecutor.executeFieldWrite(write.op(), writeHeap,
            write.receiverBoundary(), write.fieldBoundary(), layouts, realDelegate(null));
        check(firstWrite.equals(secondWrite),
            "repeated writes with equal inputs produce equal outcomes");

        SemanticOp has = hasFieldOp(BASE_REF, "y");
        Outcome<Value> firstHas = ClassOpsExecutor.executeHasField(has, base.heap(), layouts);
        Outcome<Value> secondHas = ClassOpsExecutor.executeHasField(has, base.heap(), layouts);
        check(firstHas.equals(secondHas),
            "repeated has executions with equal inputs produce equal outcomes");
    }

    // =========================================================================
    // (h) null arguments
    // =========================================================================

    private static void testNullArgumentsFailClosed() {
        System.out.println("-- null arguments throw the documented NPEs --");

        Map<ClassId, ClassLayout> layouts = Map.of(CLS, LAYOUT);
        BaseInstanceFixture base = baseInstance(
            Map.of("x", new Value.Int(1), "t", Value.string("v")), LAYOUT);
        FieldReadFixture read = fieldReadFixture(BASE_REF, CLS, "x", LAYOUT);
        FieldWriteFixture write = fieldWriteFixture(BASE_REF, CLS, "x", LAYOUT, nextValue());
        FieldDeleteFixture delete = fieldDeleteFixture(BASE_REF, CLS, "y");
        SemanticOp has = hasFieldOp(BASE_REF, "y");
        BoundaryCheckRunner pass = passThrough(null);

        expectNpe(() -> ClassOpsExecutor.executeFieldRead(null, base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a null op");
        expectNpe(() -> ClassOpsExecutor.executeFieldRead(read.op(), null,
                read.receiverBoundary(), read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a null value lookup");
        expectNpe(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                null, read.fieldBoundary(), layouts, pass),
            "executeFieldRead with a null receiver boundary");
        expectNpe(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                read.receiverBoundary(), null, layouts, pass),
            "executeFieldRead with a null field boundary");
        expectNpe(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), null, pass),
            "executeFieldRead with a null layout context");
        expectNpe(() -> ClassOpsExecutor.executeFieldRead(read.op(), base.heap(),
                read.receiverBoundary(), read.fieldBoundary(), layouts, null),
            "executeFieldRead with a null check runner");

        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(null, base.heap(),
                write.receiverBoundary(), write.fieldBoundary(), layouts, pass),
            "executeFieldWrite with a null op");
        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(write.op(), null,
                write.receiverBoundary(), write.fieldBoundary(), layouts, pass),
            "executeFieldWrite with a null value lookup");
        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(write.op(), base.heap(),
                null, write.fieldBoundary(), layouts, pass),
            "executeFieldWrite with a null receiver boundary");
        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(write.op(), base.heap(),
                write.receiverBoundary(), null, layouts, pass),
            "executeFieldWrite with a null field boundary");
        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(write.op(), base.heap(),
                write.receiverBoundary(), write.fieldBoundary(), null, pass),
            "executeFieldWrite with a null layout context");
        expectNpe(() -> ClassOpsExecutor.executeFieldWrite(write.op(), base.heap(),
                write.receiverBoundary(), write.fieldBoundary(), layouts, null),
            "executeFieldWrite with a null check runner");

        expectNpe(() -> ClassOpsExecutor.executeFieldDelete(null, base.heap(),
                delete.receiverBoundary(), layouts, pass),
            "executeFieldDelete with a null op");
        expectNpe(() -> ClassOpsExecutor.executeFieldDelete(delete.op(), null,
                delete.receiverBoundary(), layouts, pass),
            "executeFieldDelete with a null value lookup");
        expectNpe(() -> ClassOpsExecutor.executeFieldDelete(delete.op(), base.heap(),
                null, layouts, pass),
            "executeFieldDelete with a null receiver boundary");
        expectNpe(() -> ClassOpsExecutor.executeFieldDelete(delete.op(), base.heap(),
                delete.receiverBoundary(), null, pass),
            "executeFieldDelete with a null layout context");
        expectNpe(() -> ClassOpsExecutor.executeFieldDelete(delete.op(), base.heap(),
                delete.receiverBoundary(), layouts, null),
            "executeFieldDelete with a null check runner");

        expectNpe(() -> ClassOpsExecutor.executeHasField(null, base.heap(), layouts),
            "executeHasField with a null op");
        expectNpe(() -> ClassOpsExecutor.executeHasField(has, null, layouts),
            "executeHasField with a null value lookup");
        expectNpe(() -> ClassOpsExecutor.executeHasField(has, base.heap(), null),
            "executeHasField with a null layout context");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Field Ops Executor Tests (ISSUE-0513 K-D6/K-D7) ===\n");

        testT2InstanceFeedsFieldReads();
        testReadPresenceMatrix();
        testNominalReceiverFailures();
        testWriteCommitOrderingAndPresence();
        testDeleteTurnsPresentIntoMissingAndIsIdempotent();
        testHasPresenceMatrix();
        testReceiverConsumedExactlyOnce();
        testFailClosedDefects();
        testDeterminism();
        testNullArgumentsFailClosed();

        System.out.println("\nFieldOpsExecutorTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
