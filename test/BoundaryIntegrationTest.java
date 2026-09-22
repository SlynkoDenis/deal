package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.DescriptorService;
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
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.test.IdentityTestFixtures;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The epic's decomposition tail (ISSUE-0367): the end-to-end chain
 * descriptor → boundary payload → exact projection through
 * synthetic lowered units, with in-memory failure injection proving the
 * chain fails when any constituent (service, validator, executor)
 * is broken. No mocked substitute at any seam: descriptors are produced by
 * {@link DescriptorService#describe(Type)} from checked {@code Type}s
 * (int, number, array, class, nullable, sync and async {@code Func}); the
 * synthetic unit is validated by
 * {@link SemanticIrValidator#validate(LoweredModuleUnit,
 * SemanticIrValidator.ComparisonFacts)}; every {@code BOUNDARY} op is
 * executed cell-by-cell through {@link BoundaryExecutor} (the
 * {@code RuntimeValidation} cells through {@code check}, the proved cell
 * through the realization dispatch whose terminal is always {@code Pass});
 * and each active boundary realization is read directly from its payload.
 * Every projection
 * is asserted against the exact pinned message, never a substring match.
 *
 * <p>Tests:
 * <ol>
 *   <li>The happy chain: one synthetic lowered unit carrying thirteen
 *       {@code BOUNDARY} ops — the descriptor-kind-rule cells for every
 *       produced descriptor (int/number/array/class/nullable/sync/async
 *       function), a {@code FUNCTION_PARAMETER}/{@code FUNCTION_RETURN}
 *       pair under {@code CALL(DIRECT)}, an {@code ARRAY_ELEMENT_READ}
 *       cell under {@code INDEX_READ}, a
 *       {@code DEAL_TO_HOST}+{@code HOST_PARAMETER} +
 *       {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} cell set under
 *       {@code CALL(HOST)} (one {@code RuntimeValidation} parameter cell,
 *       one {@code RepresentationProof} parameter cell — the only
 *       proof-admissible cell), and an {@code ARRAY_ELEMENT_DELETE} cell
 *       under {@code DELETE} — validated, executed cell-by-cell against
 *       the exact pinned projections, and report-completed.</li>
 *   <li>Representative exact projections end-to-end (descriptor from
 *       {@code Type} → boundary op → executor → report entry): the int
 *       path (Pass with the same in-range number carrier; E8004
 *       {@code int out of safe range} at the signed32 upper end), E8010
 *       function-signature mismatch, E8002 {@code negative array index},
 *       the {@code HOST_PARAMETER} {@code {index}} projection, E8002
 *       {@code array index out of bounds} for index &gt; length, the
 *       E8003 first-failing-element arm with the leaf cause, and the
 *       proved cell that always Passes without check logic.</li>
 *   <li>Failure injection (in-memory unit variants):
 *       {@code describe(Type.Bytes)} (the bytes member since ISSUE-0158) and
 *       {@code describe(Type.Error)} →
 *       {@code DescriptorService.Defect} → E6005
 *       {@code DESCRIPTOR_UNREPRESENTABLE}; a unit whose boundary triple
 *       is outside the closed table → validator R-BOUNDARY-TRIPLE E6005
 *       before any execution; an executor policy outside the closed
 *       11-policy subset → {@code BoundaryExecutor.Defect} (fail closed).</li>
 * </ol>
 */
public class BoundaryIntegrationTest {

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
            fail("expected BoundaryExecutor.Defect for " + what + ", but no exception was raised");
        } catch (BoundaryExecutor.Defect expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected BoundaryExecutor.Defect for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    public static void main(String[] args) {
        try {
            testEndToEndHappyChain();
            testProvedCellPair();
            testFailureInjectionDescriptorDefect();
            testFailureInjectionValidatorOutOfTableTriple();
            testExecutorOutOfSubsetPolicyFailsClosed();
        } catch (Throwable t) {
            failed++;
            System.err.println("FAIL: unexpected " + t);
            t.printStackTrace();
        }
        System.out.println();
        System.out.println("BoundaryIntegrationTest: " + passed + " passed, "
            + failed + " failed");
        System.exit(failed > 0 ? 1 : 0);
    }

    // =========================================================================
    // Shared synthetic fixtures (descriptors produced through DescriptorService)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.a");
    private static final ModuleId HOST_MOD = new ModuleId("host.a");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(IFACE, SemanticProfile.DEAL_V1_2_INT32, REGISTRY);
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    // Every descriptor of the integration chain comes from the single
    // Type→descriptor producer (the pinned D1 producer-singularity seam):
    // int, number, array, class, nullable, sync and async Func.
    private static final RuntimeDescriptor INT = DescriptorService.describe(Type.Int.INSTANCE);
    private static final RuntimeDescriptor NUMBER = DescriptorService.describe(Type.Number.INSTANCE);
    private static final RuntimeDescriptor BOOLEAN = DescriptorService.describe(Type.Boolean.INSTANCE);
    private static final RuntimeDescriptor STRING = DescriptorService.describe(Type.String.INSTANCE);
    private static final RuntimeDescriptor INT_ARRAY =
        DescriptorService.describe(new Type.Array(Type.Int.INSTANCE));
    private static final RuntimeDescriptor USER =
        DescriptorService.describe(IdentityTestFixtures.classType("User", "src/app"));
    private static final RuntimeDescriptor NULLABLE_STRING =
        DescriptorService.describe(new Type.Nullable(Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func FUNC_INT_TO_INT = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE));
    private static final RuntimeDescriptor.Func FUNC_INT_TO_STR = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func ASYNC_INT_TO_STR = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE,
            true));
    /** A call whose single parameter is itself a function: {@code ((int)->int)->boolean}. */
    private static final RuntimeDescriptor.Func FUNC_PARAM_CALL = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(
            List.of(new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE)),
            Type.Boolean.INSTANCE));
    /** The host call signature {@code (int,int)->string}. */
    private static final RuntimeDescriptor.Func HOST_SIG = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(
            List.of(Type.Int.INSTANCE, Type.Int.INSTANCE), Type.String.INSTANCE));

    private static int nextOp = 1;
    private static int nextVal = 1;

    private static OpId nextOpId() {
        return new OpId(MOD, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin("test.deal", SourceSpan.synthetic("test.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, BoundaryRealization realization, OpId parent) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, nextValue(), realization),
            null, null, policy, parent);
    }

    private static LoweredModuleUnit unit(List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, LCH, Set.of(), Map.of(), Map.of(),
            Map.of(), new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            Map.of(), ops);
    }

    // =========================================================================
    // Executor-arm model and assertion helpers
    // =========================================================================

    /** One executor arm: a view, a context, and the pinned expected outcome. */
    private record ExecArm(BoundaryValueView view, BoundaryContext context,
                           ExecExpectation expected) {
    }

    private sealed interface ExecExpectation permits ExecPass, ExecFail {
    }

    /** An expected Pass; {@code sameInstance} pins "the same semantic value" (never copied). */
    private record ExecPass(BoundaryValueView value, boolean sameInstance)
        implements ExecExpectation {
    }

    /** An expected structured failure (registry-row projection fields). */
    private record ExecFail(FailurePolicyId policy, DiagnosticCode code, String message,
                            String expected, String actual, Map<String, String> metadata,
                            BoundaryFailure cause) implements ExecExpectation {
    }

    /** A Pass arm holding one view instance: the executor must return the same instance. */
    private static ExecArm passArm(BoundaryValueView view) {
        return new ExecArm(view, BoundaryContext.none(), new ExecPass(view, true));
    }

    /** A Pass arm holding one view instance under an explicit context. */
    private static ExecArm passArm(BoundaryValueView view, BoundaryContext context) {
        return new ExecArm(view, context, new ExecPass(view, true));
    }

    /** A failure arm carrying its view and context. */
    private static ExecArm failArm(BoundaryValueView view, BoundaryContext context,
                                   ExecFail failure) {
        return new ExecArm(view, context, failure);
    }

    private static void assertExec(BoundaryOutcome outcome, ExecExpectation expected,
                                   String what) {
        switch (expected) {
            case ExecPass passExpectation -> {
                if (outcome instanceof BoundaryOutcome.Pass pass) {
                    if (passExpectation.sameInstance()) {
                        check(pass.value() == passExpectation.value(),
                            what + ": Pass publishes the same semantic value (same view "
                                + "instance, never copied)");
                    } else {
                        check(pass.value().kind() == passExpectation.value().kind(),
                            what + ": Pass publishes a view of kind "
                                + passExpectation.value().kind() + ", got " + pass.value().kind());
                    }
                    passed++;
                } else {
                    fail(what + ": expected Pass, got " + outcome);
                }
            }
            case ExecFail failExpectation -> {
                if (!(outcome instanceof BoundaryOutcome.Fail failOutcome)) {
                    fail(what + ": expected Fail, got " + outcome);
                    return;
                }
                BoundaryFailure failure = failOutcome.failure();
                check(failure.policy() == failExpectation.policy(),
                    what + " policy: expected " + failExpectation.policy() + ", got "
                        + failure.policy());
                check(failure.code() == failExpectation.code(),
                    what + " code: expected " + failExpectation.code() + ", got " + failure.code());
                check(failExpectation.message().equals(failure.message()),
                    what + " message: expected [" + failExpectation.message() + "], got ["
                        + failure.message() + "]");
                check(Objects.equals(failExpectation.expected(), failure.expected()),
                    what + " expected field: expected [" + failExpectation.expected() + "], got ["
                        + failure.expected() + "]");
                check(Objects.equals(failExpectation.actual(), failure.actual()),
                    what + " actual field: expected [" + failExpectation.actual() + "], got ["
                        + failure.actual() + "]");
                check(failExpectation.metadata().equals(failure.metadata()),
                    what + " metadata: expected " + failExpectation.metadata() + ", got "
                        + failure.metadata());
                check(Objects.equals(failExpectation.cause(), failure.cause()),
                    what + " cause: expected " + failExpectation.cause() + ", got "
                        + failure.cause());
                passed++;
            }
        }
    }

    // =========================================================================
    // The synthetic happy fixture: descriptor → boundary payload → executor
    // =========================================================================

    /**
     * One synthetic lowered unit whose thirteen {@code BOUNDARY} ops carry
     * the closed table's cells for every produced descriptor family, plus
     * its per-boundary executor arms:
     * <ol>
     *   <li>{@code VARIABLE_DECLARATION} — int, {@code TYPE_DESCRIPTOR}.</li>
     *   <li>{@code MODULE_EXPORT} — number, {@code TYPE_DESCRIPTOR}.</li>
     *   <li>{@code IMPORTED_MEMBER_READ} — [int], {@code TYPE_DESCRIPTOR}.</li>
     *   <li>{@code CLASS_FIELD_ASSIGNMENT} — {@code @src/app/User},
     *       {@code TYPE_DESCRIPTOR}.</li>
     *   <li>{@code OPTIONAL_FIELD_READ} — ?string, {@code TYPE_DESCRIPTOR}.</li>
     *   <li>{@code VARIABLE_ASSIGNMENT} — async(int)->string,
     *       {@code FUNCTION_SIGNATURE}.</li>
     *   <li>{@code FUNCTION_PARAMETER} — (int)->int,
     *       {@code FUNCTION_SIGNATURE}, under {@code CALL(DIRECT)}.</li>
     *   <li>{@code FUNCTION_RETURN} — boolean, {@code TYPE_DESCRIPTOR},
     *       under the same {@code CALL(DIRECT)}.</li>
     *   <li>{@code ARRAY_ELEMENT_READ} — int,
     *       {@code ARRAY_READ_INDEX_THEN_DESCRIPTOR}, under
     *       {@code INDEX_READ}.</li>
     *   <li>{@code DEAL_TO_HOST} — int, {@code HOST_PARAMETER}
     *       ({@code RuntimeValidation}), under {@code CALL(HOST)}.</li>
     *   <li>{@code DEAL_TO_HOST} — int, {@code HOST_PARAMETER}
     *       ({@code RepresentationProof} — the only admissible proof
     *       cell), under the same {@code CALL(HOST)}.</li>
     *   <li>{@code HOST_TO_DEAL} — string, {@code HOST_SYNC_RETURN},
     *       under the same {@code CALL(HOST)}.</li>
     *   <li>{@code ARRAY_ELEMENT_DELETE} — int, {@code ARRAY_DELETE_BOUNDS},
     *       under {@code DELETE} {@code ARRAY_SLOT}.</li>
     * </ol>
     */
    private record HappyFixture(LoweredModuleUnit unit, Map<OpId, List<ExecArm>> arms) {
    }

    private static HappyFixture happyFixture(boolean badProofOnVar) {
        List<SemanticOp> ops = new ArrayList<>();
        Map<OpId, List<ExecArm>> arms = new LinkedHashMap<>();

        // 1. VARIABLE_DECLARATION int — the int path in the pinned order.
        OpId varBoundary = nextOpId();
        ops.add(boundaryWith(varBoundary, BoundaryKind.VARIABLE_DECLARATION, INT,
            FailurePolicyId.TYPE_DESCRIPTOR,
            badProofOnVar
                ? new BoundaryRealization.RepresentationProof("jvm-method-signature")
                : new BoundaryRealization.RuntimeValidation("check-var"),
            null));
        arms.put(varBoundary, List.of(
            passArm(BoundaryValueView.ofNumber(7.0)),
            failArm(BoundaryValueView.ofNumber(2147483648.0), BoundaryContext.none(),
                new ExecFail(FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004,
                    "int out of safe range", "int", "number", new LinkedHashMap<>(), null))));

        // 2. MODULE_EXPORT number — number accepts an int carrier.
        OpId numBoundary = nextOpId();
        ops.add(boundaryWith(numBoundary, BoundaryKind.MODULE_EXPORT, NUMBER,
            FailurePolicyId.TYPE_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-num"), null));
        arms.put(numBoundary, List.of(
            passArm(BoundaryValueView.ofNumber(1.5)),
            passArm(BoundaryValueView.ofInt(5))));

        // 3. IMPORTED_MEMBER_READ [int] — first failing element with the leaf cause.
        OpId arrBoundary = nextOpId();
        ops.add(boundaryWith(arrBoundary, BoundaryKind.IMPORTED_MEMBER_READ, INT_ARRAY,
            FailurePolicyId.TYPE_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-arr"), null));
        BoundaryFailure leafNonIntegral = BoundaryFailure.fromRow(
            FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
            "int", "non-integer number", new LinkedHashMap<>(), null);
        arms.put(arrBoundary, List.of(
            passArm(BoundaryValueView.ofArray(BoundaryValueView.ofInt(1),
                BoundaryValueView.ofInt(2))),
            failArm(BoundaryValueView.ofArray(BoundaryValueView.ofInt(1),
                    BoundaryValueView.ofNumber(1.5), BoundaryValueView.ofInt(3)),
                BoundaryContext.none(),
                new ExecFail(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
                    "array element 2 type mismatch", "int", "number",
                    Map.of("oneBasedIndex", "2"), leafNonIntegral))));

        // 4. CLASS_FIELD_ASSIGNMENT @src/app/User — class atom byte-equality.
        OpId clsBoundary = nextOpId();
        ops.add(boundaryWith(clsBoundary, BoundaryKind.CLASS_FIELD_ASSIGNMENT, USER,
            FailurePolicyId.TYPE_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-cls"), null));
        arms.put(clsBoundary, List.of(
            passArm(BoundaryValueView.ofClass("@src/app/User")),
            failArm(BoundaryValueView.ofClass("@src/app/Admin"), BoundaryContext.none(),
                new ExecFail(FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
                    "expected @src/app/User, got class:@src/app/Admin", "@src/app/User",
                    "class:@src/app/Admin", new LinkedHashMap<>(), null))));

        // 5. OPTIONAL_FIELD_READ ?string — language null passes the nullable.
        OpId optBoundary = nextOpId();
        ops.add(boundaryWith(optBoundary, BoundaryKind.OPTIONAL_FIELD_READ, NULLABLE_STRING,
            FailurePolicyId.TYPE_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-opt"), null));
        arms.put(optBoundary, List.of(
            passArm(BoundaryValueView.nullView()),
            passArm(BoundaryValueView.of(ActualKind.STRING))));

        // 6. VARIABLE_ASSIGNMENT async(int)->string — the async marker is part of the signature.
        OpId asyncBoundary = nextOpId();
        ops.add(boundaryWith(asyncBoundary, BoundaryKind.VARIABLE_ASSIGNMENT, ASYNC_INT_TO_STR,
            FailurePolicyId.FUNCTION_SIGNATURE,
            new BoundaryRealization.RuntimeValidation("check-async"), null));
        arms.put(asyncBoundary, List.of(
            passArm(BoundaryValueView.ofFunction(ASYNC_INT_TO_STR)),
            failArm(BoundaryValueView.ofFunction(FUNC_INT_TO_STR), BoundaryContext.none(),
                new ExecFail(FailurePolicyId.FUNCTION_SIGNATURE, DiagnosticCode.E8010,
                    "function signature mismatch: expected async(int)->string, "
                        + "got (int)->string",
                    "async(int)->string", "(int)->string", new LinkedHashMap<>(), null))));

        // 7-9. CALL(DIRECT): FUNCTION_PARAMETER ((int)->int parameter) + FUNCTION_RETURN boolean.
        OpId callOp = nextOpId();
        OpId paramBoundary = nextOpId();
        OpId retBoundary = nextOpId();
        ops.add(boundaryWith(paramBoundary, BoundaryKind.FUNCTION_PARAMETER, FUNC_INT_TO_INT,
            FailurePolicyId.FUNCTION_SIGNATURE,
            new BoundaryRealization.RuntimeValidation("check-param"), callOp));
        arms.put(paramBoundary, List.of(
            passArm(BoundaryValueView.ofFunction(FUNC_INT_TO_INT)),
            failArm(BoundaryValueView.ofFunction(FUNC_INT_TO_STR), BoundaryContext.none(),
                new ExecFail(FailurePolicyId.FUNCTION_SIGNATURE, DiagnosticCode.E8010,
                    "function signature mismatch: expected (int)->int, got (int)->string",
                    "(int)->int", "(int)->string", new LinkedHashMap<>(), null))));
        ops.add(boundaryWith(retBoundary, BoundaryKind.FUNCTION_RETURN, BOOLEAN,
            FailurePolicyId.TYPE_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-ret"), callOp));
        arms.put(retBoundary, List.of(
            passArm(BoundaryValueView.of(ActualKind.BOOLEAN))));
        ops.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.DIRECT,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                        new BlockId(1))),
                FUNC_PARAM_CALL, List.of(paramBoundary), retBoundary, null,
                new BlockId(1), null),
            nextValue(), BOOLEAN, FailurePolicyId.NO_DEAL_FAILURE, null));

        // 10-11. ARRAY_ELEMENT_READ int under INDEX_READ — negative index first.
        OpId indexReadOp = nextOpId();
        OpId readBoundary = nextOpId();
        ops.add(boundaryWith(readBoundary, BoundaryKind.ARRAY_ELEMENT_READ, INT,
            FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
            new BoundaryRealization.RuntimeValidation("check-read"), indexReadOp));
        arms.put(readBoundary, List.of(
            failArm(BoundaryValueView.ofInt(7), BoundaryContext.arrayIndex(-1),
                new ExecFail(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
                    DiagnosticCode.E8002, "negative array index", null, null,
                    new LinkedHashMap<>(), null)),
            passArm(BoundaryValueView.ofInt(7), BoundaryContext.arrayIndex(0))));
        ops.add(opWith(indexReadOp, SemanticOpKind.INDEX_READ,
            new KindPayload.IndexReadPayload(nextValue(), nextValue(), readBoundary),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));

        // 12-15. CALL(HOST): DEAL_TO_HOST + HOST_PARAMETER (RuntimeValidation),
        // DEAL_TO_HOST + HOST_PARAMETER (RepresentationProof — the admissible
        // proof cell), HOST_TO_DEAL + HOST_SYNC_RETURN.
        OpId hostCallOp = nextOpId();
        OpId hostPb1 = nextOpId();
        OpId hostPb2 = nextOpId();
        OpId hostRb = nextOpId();
        ops.add(boundaryWith(hostPb1, BoundaryKind.DEAL_TO_HOST, INT,
            FailurePolicyId.HOST_PARAMETER,
            new BoundaryRealization.RuntimeValidation("check-host-p1"), hostCallOp));
        arms.put(hostPb1, List.of(
            passArm(BoundaryValueView.ofInt(3), BoundaryContext.parameter(1)),
            failArm(BoundaryValueView.ofNumber(3.5), BoundaryContext.parameter(1),
                new ExecFail(FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
                    "parameter 1 type mismatch: expected int, got non-integer number",
                    "int", "non-integer number", Map.of("index", "1"), null))));
        ops.add(boundaryWith(hostPb2, BoundaryKind.DEAL_TO_HOST, INT,
            FailurePolicyId.HOST_PARAMETER,
            new BoundaryRealization.RepresentationProof("jvm-method-signature"), hostCallOp));
        arms.put(hostPb2, List.of(
            passArm(BoundaryValueView.ofNumber(3.5), BoundaryContext.parameter(2))));
        ops.add(boundaryWith(hostRb, BoundaryKind.HOST_TO_DEAL, STRING,
            FailurePolicyId.HOST_SYNC_RETURN,
            new BoundaryRealization.RuntimeValidation("check-host-ret"), hostCallOp));
        arms.put(hostRb, List.of(
            passArm(BoundaryValueView.of(ActualKind.STRING))));
        ops.add(opWith(hostCallOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.HOST,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.HostFunction(HOST_MOD, "add", HOST_SIG)),
                HOST_SIG, List.of(hostPb1, hostPb2), hostRb, null, null, null),
            nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));

        // 16-17. ARRAY_ELEMENT_DELETE int under DELETE ARRAY_SLOT — bounds first.
        OpId deleteOp = nextOpId();
        OpId delBoundary = nextOpId();
        ops.add(boundaryWith(delBoundary, BoundaryKind.ARRAY_ELEMENT_DELETE, INT,
            FailurePolicyId.ARRAY_DELETE_BOUNDS,
            new BoundaryRealization.RuntimeValidation("check-del"), deleteOp));
        arms.put(delBoundary, List.of(
            failArm(BoundaryValueView.ofInt(7), BoundaryContext.writeBounds(4, 3),
                new ExecFail(FailurePolicyId.ARRAY_DELETE_BOUNDS, DiagnosticCode.E8002,
                    "array index out of bounds", null, null, new LinkedHashMap<>(), null)),
            passArm(BoundaryValueView.ofInt(7), BoundaryContext.writeBounds(1, 3))));
        ops.add(opWith(deleteOp, SemanticOpKind.DELETE,
            new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                List.of(nextOpId(), nextOpId(), delBoundary, nextOpId())),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));

        return new HappyFixture(unit(ops), arms);
    }

    // =========================================================================
    // The end-to-end chain runner
    // =========================================================================

    private static final String STEP_VALIDATION = "validation";
    private static final String STEP_COMPLETE = "complete";

    /** The outcome of one chain run: the first failing step and its diagnostic. */
    private record ChainRun(boolean ok, String step, CompilerDiagnostic diagnostic) {
    }

    /**
     * Runs the validated execution chain over one synthetic unit:
     * <ol>
     *   <li>validation — {@code SemanticIrValidator.validate(unit, facts)}
     *       must be empty; a rejected unit never reaches the executor;</li>
     *   <li>execution — every {@code BOUNDARY} op executed cell-by-cell
     *       through {@code BoundaryExecutor.execute} using the realization
     *       carried by its active Semantic IR payload (the
     *       {@code RuntimeValidation} cells run {@code check}; the proved
     *       cell's terminal is always {@code Pass}) against the pinned
     *       projections.</li>
     * </ol>
     */
    private static ChainRun runChain(LoweredModuleUnit unit, Map<OpId, List<ExecArm>> arms) {
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit, FACTS);
        if (validation.isPresent()) {
            return new ChainRun(false, STEP_VALIDATION, validation.get());
        }
        int executed = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.BOUNDARY) {
                continue;
            }
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            List<ExecArm> cellArms = arms.getOrDefault(op.opId(), List.of());
            check(!cellArms.isEmpty(),
                "every BOUNDARY op of the chain has at least one executor arm: " + op.opId());
            for (ExecArm arm : cellArms) {
                BoundaryOutcome outcome = BoundaryExecutor.execute(op.failurePolicy(),
                    payload.descriptor(), arm.view(), arm.context(), payload.realization());
                assertExec(outcome, arm.expected(),
                    "chain cell " + op.opId() + " (" + payload.kind() + ", "
                        + op.failurePolicy() + ")");
                executed++;
            }
        }
        check(executed > 0, "the chain executed at least one boundary arm");
        return new ChainRun(true, STEP_COMPLETE, null);
    }

    private static void assertE6005(CompilerDiagnostic diagnostic, String rule,
                                    String... contains) {
        check(diagnostic != null, rule + " is rejected with E6005");
        if (diagnostic == null) {
            return;
        }
        check("E6005".equals(diagnostic.code()), rule + " diagnostic code is E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            rule + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            rule + " phase is BACKEND_LOWERING");
        check("error".equals(diagnostic.severity()), rule + " severity is error");
        String message = diagnostic.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            rule + " is named as the validator rule (exactly one rule per defect); got \""
                + message + "\"");
        check(message.contains("module 'mod.a'"),
            rule + " message names the module; got \"" + message + "\"");
        check(message.contains("deal.semantic-ir/1"),
            rule + " message carries the pinned irVersion");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \""
                + message + "\"");
        }
    }

    private static void assertE6005Descriptor(CompilerDiagnostic diagnostic, String what) {
        check(diagnostic != null, what + " is rejected with E6005");
        if (diagnostic == null) {
            return;
        }
        check("E6005".equals(diagnostic.code()), what + " diagnostic code is E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            what + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            what + " phase is BACKEND_LOWERING");
        check("error".equals(diagnostic.severity()), what + " severity is error");
        String message = diagnostic.message();
        check(message.startsWith("Common semantic lowering failed"),
            what + " message instantiates the registry-owned E6005 template");
        check(message.contains("module 'mod.a'"), what + " message names the module");
        check(message.contains("capability DESCRIPTORS"),
            what + " message carries capability DESCRIPTORS");
        check(message.contains("validatorRule DESCRIPTOR_UNREPRESENTABLE,"),
            what + " message names validatorRule DESCRIPTOR_UNREPRESENTABLE");
        check(message.contains("semanticProfile DEAL_V1_2_INT32"),
            what + " message carries the semantic profile");
        check(message.contains("irVersion deal.semantic-ir/1"),
            what + " message carries the pinned irVersion");
        check(message.contains("origin DescriptorService DESCRIPTOR_UNREPRESENTABLE ("),
            what + " message names the DescriptorService origin");
    }

    // =========================================================================
    // 1. The happy chain: descriptor → boundary → executor → report
    // =========================================================================

    static void testEndToEndHappyChain() {
        System.out.println("-- Happy chain: DescriptorService → SemanticIrValidator → "
            + "BoundaryExecutor --");

        // T1 combined: every chain descriptor is produced by the single
        // Type→descriptor producer with the schema-owned canonical text.
        check("int".equals(INT.canonicalSpecText()), "describe(Type.Int) is int");
        check("number".equals(NUMBER.canonicalSpecText()), "describe(Type.Number) is number");
        check("[int]".equals(INT_ARRAY.canonicalSpecText()),
            "describe(Type.Array(Type.Int)) is [int]");
        check("@src/app/User".equals(USER.canonicalSpecText()),
            "describe(Type.Class(User, src/app)) is @src/app/User");
        check("?string".equals(NULLABLE_STRING.canonicalSpecText()),
            "describe(Type.Nullable(Type.String)) is ?string");
        check("(int)->int".equals(FUNC_INT_TO_INT.canonicalSpecText()),
            "describe(sync Func) is (int)->int");
        check("async(int)->string".equals(ASYNC_INT_TO_STR.canonicalSpecText()),
            "describe(async Func) is async(int)->string");
        check("((int)->int)->boolean".equals(FUNC_PARAM_CALL.canonicalSpecText()),
            "describe(Func([Func([Int],Int)],Boolean)) is ((int)->int)->boolean");
        check(RuntimeDescriptor.parseCanonicalText(USER.canonicalSpecText()).equals(USER),
            "the class descriptor text round-trips through parseCanonicalText");
        check(RuntimeDescriptor.parseCanonicalText(FUNC_PARAM_CALL.canonicalSpecText())
                .equals(FUNC_PARAM_CALL),
            "the function-parameter descriptor text round-trips");

        HappyFixture fixture = happyFixture(false);
        LoweredModuleUnit unit = fixture.unit();

        // The unit carries exactly the thirteen pinned BOUNDARY ops.
        List<SemanticOp> boundaries = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY) {
                boundaries.add(op);
            }
        }
        check(boundaries.size() == 13,
            "the synthetic unit carries exactly 13 BOUNDARY ops; got " + boundaries.size());

        // The complete chain: validation (empty) → cell-by-cell execution
        // (exact projections) → report completion (empty).
        ChainRun run = runChain(unit, fixture.arms());
        check(run.ok() && STEP_COMPLETE.equals(run.step()),
            "the descriptor → boundary → realization report → exact projection chain "
                + "completes end to end; step='" + run.step() + "'"
                + (run.diagnostic() != null ? " diagnostic=" + run.diagnostic().message() : ""));

        // Inspect the active Semantic IR payloads directly and pin the one
        // representation-proof boundary.
        int proofEntries = 0;
        for (SemanticOp op : boundaries) {
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            if (payload.realization() instanceof BoundaryRealization.RepresentationProof proof) {
                proofEntries++;
                check(!proof.proofKind().isEmpty()
                        && payload.kind() == BoundaryKind.DEAL_TO_HOST
                        && op.failurePolicy() == FailurePolicyId.HOST_PARAMETER,
                    "the non-empty RepresentationProof sits on DEAL_TO_HOST + HOST_PARAMETER; "
                        + "got (" + payload.kind() + ", " + op.failurePolicy() + ")");
            } else if (payload.realization()
                    instanceof BoundaryRealization.RuntimeValidation validation) {
                check(!validation.checkId().isEmpty(),
                    "the RuntimeValidation payload carries a non-empty check id: " + op.opId());
            }
        }
        check(proofEntries == 1,
            "exactly one RepresentationProof payload in the happy unit; got " + proofEntries);

        // The chain is deterministic: a repeated run over a fresh unit
        // completes identically.
        HappyFixture second = happyFixture(false);
        ChainRun secondRun = runChain(second.unit(), second.arms());
        check(secondRun.ok() && STEP_COMPLETE.equals(secondRun.step()),
            "the repeated chain run completes identically; step='" + secondRun.step() + "'");
    }

    // =========================================================================
    // 2. The RuntimeValidation/RepresentationProof pair on the pinned host cell
    // =========================================================================

    static void testProvedCellPair() {
        System.out.println("-- RuntimeValidation + RepresentationProof pair: the proved cell "
            + "always Passes without check logic --");

        HappyFixture fixture = happyFixture(false);
        LoweredModuleUnit unit = fixture.unit();

        // Locate the two DEAL_TO_HOST + HOST_PARAMETER cells: one
        // RuntimeValidation, one RepresentationProof (the only admissible
        // proof cell).
        List<SemanticOp> hostParams = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) op.payload()).kind()
                        == BoundaryKind.DEAL_TO_HOST
                    && op.failurePolicy() == FailurePolicyId.HOST_PARAMETER) {
                hostParams.add(op);
            }
        }
        check(hostParams.size() == 2,
            "the unit carries exactly two DEAL_TO_HOST + HOST_PARAMETER cells; got "
                + hostParams.size());
        if (hostParams.size() != 2) {
            return;
        }
        SemanticOp validated = null;
        SemanticOp proved = null;
        for (SemanticOp op : hostParams) {
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            if (payload.realization() instanceof BoundaryRealization.RuntimeValidation) {
                validated = op;
            } else if (payload.realization()
                    instanceof BoundaryRealization.RepresentationProof) {
                proved = op;
            }
        }
        check(validated != null && proved != null,
            "one cell carries RuntimeValidation and one carries RepresentationProof");
        if (validated == null || proved == null) {
            return;
        }

        // The same failing view on the RuntimeValidation cell projects the
        // pinned E8010 {index} template.
        KindPayload.BoundaryPayload provedPayload = (KindPayload.BoundaryPayload) proved.payload();
        BoundaryValueView failingView = BoundaryValueView.ofNumber(3.5);
        BoundaryOutcome validatedOutcome = BoundaryExecutor.execute(
            validated.failurePolicy(), INT, failingView, BoundaryContext.parameter(1),
            new BoundaryRealization.RuntimeValidation("physical-check"));
        assertExec(validatedOutcome,
            new ExecFail(FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
                "parameter 1 type mismatch: expected int, got non-integer number",
                "int", "non-integer number", Map.of("index", "1"), null),
            "the RuntimeValidation cell projects the {index} E8010 template");

        // The physical check on the proved cell's shape projects {index}=2
        // (context-supplied) — the check logic that the proof skips.
        BoundaryOutcome physicalCheck = BoundaryExecutor.check(proved.failurePolicy(), INT,
            failingView, BoundaryContext.parameter(2));
        assertExec(physicalCheck,
            new ExecFail(FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
                "parameter 2 type mismatch: expected int, got non-integer number",
                "int", "non-integer number", Map.of("index", "2"), null),
            "the same cell under a physical check projects parameter 2 ({index} from context)");

        // The proved cell always Passes with the value unchanged — no check
        // logic runs on the proof path, even for views the physical check
        // rejects.
        BoundaryOutcome provedOutcome = BoundaryExecutor.execute(proved.failurePolicy(), INT,
            failingView, BoundaryContext.parameter(2), provedPayload.realization());
        assertExec(provedOutcome, new ExecPass(failingView, true),
            "the RepresentationProof cell passes the failing view without check logic");

        BoundaryValueView hostileView = BoundaryValueView.of(ActualKind.STRING);
        BoundaryOutcome provedHostile = BoundaryExecutor.execute(proved.failurePolicy(), INT,
            hostileView, BoundaryContext.parameter(2), provedPayload.realization());
        assertExec(provedHostile, new ExecPass(hostileView, true),
            "the RepresentationProof cell passes even a hostile view (terminal is always "
                + "SUCCESS)");
    }

    // =========================================================================
    // 3. Failure injection: Type.Bytes / Type.Error fail closed (T1)
    // =========================================================================

    static void testFailureInjectionDescriptorDefect() {
        System.out.println("-- Fault: describe(Type.Bytes) produces the bytes member; "
            + "describe(Type.Error) fails closed as E6005 DESCRIPTOR_UNREPRESENTABLE (T1) --");

        // Type.Bytes is descriptor-representable since ISSUE-0158 (the
        // bytes member); only the internal Error sentinel stays fail
        // closed on the injection path.
        check(DescriptorService.describe(Type.Bytes.INSTANCE)
                == RuntimeDescriptor.Bytes.INSTANCE,
            "Type.Bytes maps to RuntimeDescriptor.Bytes.INSTANCE");

        record DefectCase(Type type, String what) { }
        for (DefectCase defectCase : List.of(
                new DefectCase(Type.Error.INSTANCE, "Type.Error"))) {
            DescriptorService.Defect defect = null;
            try {
                DescriptorService.describe(defectCase.type());
                fail("expected DescriptorService.Defect for " + defectCase.what()
                    + ", but a descriptor was produced");
            } catch (DescriptorService.Defect raised) {
                defect = raised;
                passed++;
            } catch (Throwable other) {
                fail("expected DescriptorService.Defect for " + defectCase.what() + ", got "
                    + other.getClass().getSimpleName() + ": " + other.getMessage());
            }
            check(defect != null, defectCase.what() + " raises DescriptorService.Defect");
            if (defect != null) {
                assertE6005Descriptor(DescriptorService.e6005(MOD, defect), defectCase.what());
            }
        }
    }

    // =========================================================================
    // 6. Failure injection: an out-of-table triple is rejected before execution
    // =========================================================================

    static void testFailureInjectionValidatorOutOfTableTriple() {
        System.out.println("-- Fault: a (kind, descriptor, policy) triple outside the closed "
            + "table (R-BOUNDARY-TRIPLE) --");

        // In-memory variant: VARIABLE_DECLARATION with the FUNCTION_SIGNATURE
        // policy on a non-function descriptor — the descriptor-kind rule's
        // wrong-policy arm.
        OpId badBoundary = nextOpId();
        LoweredModuleUnit badUnit = unit(List.of(boundaryWith(badBoundary,
            BoundaryKind.VARIABLE_DECLARATION, STRING, FailurePolicyId.FUNCTION_SIGNATURE,
            new BoundaryRealization.RuntimeValidation("check-bad"), null)));

        ChainRun run = runChain(badUnit, Map.of());
        check(!run.ok() && STEP_VALIDATION.equals(run.step()),
            "the out-of-table triple fails the chain at the validation step before any "
                + "execution or report completion; step='" + run.step() + "'");
        assertE6005(run.diagnostic(), SemanticIrValidator.R_BOUNDARY_TRIPLE,
            "VARIABLE_DECLARATION", "FUNCTION_SIGNATURE", "descriptor-kind rule");
    }

    // =========================================================================
    // 7. Failure injection: an executor policy outside the closed 11-policy subset
    // =========================================================================

    static void testExecutorOutOfSubsetPolicyFailsClosed() {
        System.out.println("-- Fault: an executor policy outside the closed 11-policy "
            + "subset fails closed (T2) --");

        // SQRT_NEGATIVE is a closed FailurePolicyId but is never a BOUNDARY
        // policy: the validator's table rejects it, so the executor has no
        // projection and must fail closed as a producer defect.
        expectDefect(() -> BoundaryExecutor.execute(FailurePolicyId.SQRT_NEGATIVE, INT,
            BoundaryValueView.ofInt(1), BoundaryContext.none(),
            new BoundaryRealization.RuntimeValidation("check-x")),
            "SQRT_NEGATIVE outside the closed 11-policy BOUNDARY subset");
        expectDefect(() -> BoundaryExecutor.check(FailurePolicyId.HOST_LOAD, STRING,
            BoundaryValueView.of(ActualKind.STRING), BoundaryContext.none()),
            "HOST_LOAD outside the closed 11-policy BOUNDARY subset");
    }
}
