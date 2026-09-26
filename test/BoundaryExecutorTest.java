package deal.test;

import deal.diagnostics.DiagnosticCode;
import deal.semantic.DescriptorService;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.RuntimeDescriptor;
import deal.types.Type;
import deal.test.IdentityTestFixtures;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Verifies the ISSUE-0233 D3 surface: {@link BoundaryExecutor} as the
 * single, pure execution form of the closed boundary-assignment table at
 * the {@code BOUNDARY}-op level — the closed 11-policy projection engine
 * over the closed value view, with every message instantiated from the
 * registry rows' pinned templates.
 *
 * <p>Tests (wiki Verification 2, one pinned case per D3 projection):
 * <ol>
 *   <li>E8001 generic templates with every canonical actual kind
 *       including {@code class:<ClassId>}, {@code missing},
 *       {@code nothing}, and the pinned invalid-string message.</li>
 *   <li>The int path in normative order (non-numeric → NaN → infinity →
 *       non-integer → E8004 at both signed32 ends, with the nearest valid
 *       values passing), and {@code number} accepting an int carrier.</li>
 *   <li>Class atom byte-equality, including the builtin {@code @/Error}
 *       spelling.</li>
 *   <li>E8003 first failing element in increasing index order with
 *       cause = the leaf failure (nested arrays included).</li>
 *   <li>E8010 signature mismatch versus non-function E8001.</li>
 *   <li>HOST_PARAMETER {@code {index}}, HOST_SYNC_RETURN
 *       {@code got nothing}/{@code got {actual}}, ASYNC_COMPLETION
 *       (the corpus-aligned {@code expected {expected}} with the cell's
 *       actual kind — a numeric completion carrier is the number kind).</li>
 *   <li>All four array cells including index/length boundaries.</li>
 *   <li>JSON_FROM_NULL swallow and JSON_TO_ERROR {@code {fieldPath}}.</li>
 *   <li>Missing→null at the two named cells and {@code got missing}
 *       elsewhere; Pass returns the same semantic value (same view
 *       instance, never copied).</li>
 *   <li>Proved cells ({@code RepresentationProof}): SUCCESS without any
 *       check logic — a view that fails under {@code RuntimeValidation}
 *       still passes under the proof, and the proof path never requires a
 *       context; a policy outside the closed 11 fails closed as a
 *       producer defect; a null descriptor on the proof path throws the
 *       documented NPE.</li>
 *   <li>Combined behavior with T1: every descriptor is built through
 *       {@code DescriptorService.describe} from checked {@code Type}s.</li>
 *   <li>Determinism: repeated checks are byte-identical.</li>
 * </ol>
 *
 * <p>Every failure assertion compares the instantiated message against
 * the literal expected string (never a substring match) and checks the
 * structured fields (policy, code, expected, actual, metadata, cause)
 * against the registry rows.</p>
 */
public class BoundaryExecutorTest {

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

    private static void expectIllegalArgument(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected IllegalArgumentException for " + what + ", but no exception was raised");
        } catch (IllegalArgumentException expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected IllegalArgumentException for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    /** Pins a documented NullPointerException with the exact message. */
    private static void expectNpe(Runnable runnable, String message, String what) {
        try {
            runnable.run();
            fail("expected NullPointerException for " + what + ", but no exception was raised");
        } catch (NullPointerException expected) {
            check(message.equals(expected.getMessage()),
                what + " NPE message: expected [" + message + "], got ["
                    + expected.getMessage() + "]");
        } catch (Throwable other) {
            fail("expected NullPointerException for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    // =========================================================================
    // Descriptors built through DescriptorService (combined behavior with T1)
    // =========================================================================

    private static final RuntimeDescriptor STRING = DescriptorService.describe(Type.String.INSTANCE);
    private static final RuntimeDescriptor INT = DescriptorService.describe(Type.Int.INSTANCE);
    private static final RuntimeDescriptor NUMBER = DescriptorService.describe(Type.Number.INSTANCE);
    private static final RuntimeDescriptor BOOLEAN = DescriptorService.describe(Type.Boolean.INSTANCE);
    private static final RuntimeDescriptor NULL_DESCRIPTOR = DescriptorService.describe(Type.Null.INSTANCE);
    private static final RuntimeDescriptor TABLE = DescriptorService.describe(Type.Table.INSTANCE);
    private static final RuntimeDescriptor USER =
        DescriptorService.describe(IdentityTestFixtures.classType("User", "src/app"));
    private static final RuntimeDescriptor BUILTIN_ERROR =
        DescriptorService.describe(IdentityTestFixtures.errorClassType());
    private static final RuntimeDescriptor NUMBER_ARRAY =
        DescriptorService.describe(new Type.Array(Type.Number.INSTANCE));
    private static final RuntimeDescriptor INT_ARRAY =
        DescriptorService.describe(new Type.Array(Type.Int.INSTANCE));
    private static final RuntimeDescriptor NESTED_INT_ARRAY =
        DescriptorService.describe(new Type.Array(new Type.Array(Type.Int.INSTANCE)));
    private static final RuntimeDescriptor NULLABLE_STRING =
        DescriptorService.describe(new Type.Nullable(Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func SYNC_INT_TO_STRING = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func SYNC_INT_TO_INT = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE));
    private static final RuntimeDescriptor.Func ASYNC_INT_TO_STRING = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE, true));

    // =========================================================================
    // Outcome assertion helpers
    // =========================================================================

    private static BoundaryOutcome checkCell(FailurePolicyId policy, RuntimeDescriptor descriptor,
                                             BoundaryValueView view) {
        return BoundaryExecutor.check(policy, descriptor, view, BoundaryContext.none());
    }

    private static BoundaryOutcome checkCell(FailurePolicyId policy, RuntimeDescriptor descriptor,
                                             BoundaryValueView view, BoundaryContext context) {
        return BoundaryExecutor.check(policy, descriptor, view, context);
    }

    private static BoundaryOutcome.Pass expectPass(BoundaryOutcome outcome, String what) {
        if (outcome instanceof BoundaryOutcome.Pass passOutcome) {
            passed++;
            return passOutcome;
        }
        fail(what + ": expected Pass, got " + outcome);
        return null;
    }

    private static void expectFail(BoundaryOutcome outcome, FailurePolicyId policy,
                                   DiagnosticCode code, String message, String expected,
                                   String actual, Map<String, String> metadata,
                                   BoundaryFailure cause, String what) {
        if (!(outcome instanceof BoundaryOutcome.Fail failOutcome)) {
            fail(what + ": expected Fail, got " + outcome);
            return;
        }
        BoundaryFailure failure = failOutcome.failure();
        check(failure.policy() == policy,
            what + " policy: expected " + policy + ", got " + failure.policy());
        check(failure.code() == code,
            what + " code: expected " + code + ", got " + failure.code());
        check(message.equals(failure.message()),
            what + " message: expected [" + message + "], got [" + failure.message() + "]");
        check(Objects.equals(expected, failure.expected()),
            what + " expected field: expected [" + expected + "], got [" + failure.expected()
                + "]");
        check(Objects.equals(actual, failure.actual()),
            what + " actual field: expected [" + actual + "], got [" + failure.actual() + "]");
        check(metadata.equals(failure.metadata()),
            what + " metadata: expected " + metadata + ", got " + failure.metadata());
        if (cause == null) {
            check(failure.cause() == null,
                what + " cause: expected null, got " + failure.cause());
        } else {
            check(cause.equals(failure.cause()),
                what + " cause: expected " + cause + ", got " + failure.cause());
        }
    }

    /** Builds an expected leaf failure straight from the registry row (the
     *  executor must produce byte-identical projections). */
    private static BoundaryFailure expected(FailurePolicyRow row, int templateIndex,
                                            String expected, String actual,
                                            Map<String, String> metadata,
                                            BoundaryFailure cause) {
        return BoundaryFailure.fromRow(row, templateIndex, expected, actual, metadata, cause);
    }

    private static BoundaryFailure expectedKindMismatch(String descriptorText, String actual) {
        return expected(FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
            descriptorText, actual, new LinkedHashMap<>(), null);
    }

    private static final FailurePolicyRow TD_ROW =
        FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR);
    private static final FailurePolicyRow RANGE_ROW =
        FailureContractRegistry.row(FailurePolicyId.INT32_RESULT);
    private static final FailurePolicyRow AC_ROW =
        FailureContractRegistry.row(FailurePolicyId.ASYNC_COMPLETION);

    // =========================================================================
    // 1. T1 combined behavior: the suite's descriptors come from DescriptorService
    // =========================================================================

    static void testT1DescriptorWiring() {
        System.out.println("-- DescriptorService wiring (T1 combined behavior) --");
        check("string".equals(STRING.canonicalSpecText()), "describe(Type.String) is string");
        check("int".equals(INT.canonicalSpecText()), "describe(Type.Int) is int");
        check("[number]".equals(NUMBER_ARRAY.canonicalSpecText()),
            "describe(Type.Array(Type.Number)) is [number]");
        check("[[int]]".equals(NESTED_INT_ARRAY.canonicalSpecText()),
            "describe(Array(Array(Int))) is [[int]]");
        check("(int)->string".equals(SYNC_INT_TO_STRING.canonicalSpecText()),
            "describe(Func([Int], String)) is (int)->string");
        check("(int)->int".equals(SYNC_INT_TO_INT.canonicalSpecText()),
            "describe(Func([Int], Int)) is (int)->int");
        check("async(int)->string".equals(ASYNC_INT_TO_STRING.canonicalSpecText()),
            "describe(async Func) is async(int)->string");
        check("@src/app/User".equals(USER.canonicalSpecText()),
            "describe(Type.Class(User, src/app)) is @src/app/User");
        check("@/Error".equals(BUILTIN_ERROR.canonicalSpecText()),
            "describe(Type.Class(Error, \"\")) is @/Error");
    }

    // =========================================================================
    // 2. E8001 generic templates with every canonical actual kind
    // =========================================================================

    static void testGenericE8001EveryCanonicalKind() {
        System.out.println("-- E8001 generic template with every canonical actual kind --");

        record Case(BoundaryValueView view, String token) {}
        List<Case> cases = List.of(
            new Case(BoundaryValueView.nullView(), "null"),
            new Case(BoundaryValueView.of(ActualKind.MISSING), "missing"),
            new Case(BoundaryValueView.of(ActualKind.BOOLEAN), "boolean"),
            new Case(BoundaryValueView.ofInt(7), "int"),
            new Case(BoundaryValueView.ofNumber(1.5), "number"),
            new Case(BoundaryValueView.of(ActualKind.TABLE), "table"),
            new Case(BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1)), "array"),
            new Case(BoundaryValueView.ofFunction(SYNC_INT_TO_STRING), "function"),
            new Case(BoundaryValueView.ofClass("@src/app/User"), "class:@src/app/User"),
            new Case(BoundaryValueView.of(ActualKind.ASYNC_OPERATION), "async-operation"),
            new Case(BoundaryValueView.of(ActualKind.NOTHING), "nothing"));

        for (Case c : cases) {
            BoundaryOutcome outcome = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, c.view());
            expectFail(outcome, FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
                "expected string, got " + c.token(), "string", c.token(),
                new LinkedHashMap<>(), null,
                "string descriptor vs " + c.token() + " view");
        }

        // The matching kind passes with the same value.
        BoundaryValueView stringView = BoundaryValueView.of(ActualKind.STRING);
        BoundaryOutcome match = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, stringView);
        expectPass(match, "string descriptor vs string view");
        check(((BoundaryOutcome.Pass) match).value() == stringView,
            "a passing TYPE_DESCRIPTOR returns the same view instance");

        // The same generic template serves every non-function descriptor kind.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, BOOLEAN,
                BoundaryValueView.nullView()),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected boolean, got null", "boolean", "null", new LinkedHashMap<>(), null,
            "boolean descriptor vs null view");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NULL_DESCRIPTOR,
                BoundaryValueView.of(ActualKind.BOOLEAN)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected null, got boolean", "null", "boolean", new LinkedHashMap<>(), null,
            "null descriptor vs boolean view");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, TABLE,
                BoundaryValueView.of(ActualKind.NOTHING)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected table, got nothing", "table", "nothing", new LinkedHashMap<>(), null,
            "table descriptor vs nothing view");
    }

    static void testInvalidStringMessage() {
        System.out.println("-- the pinned invalid-string projection --");

        BoundaryValueView invalid = BoundaryValueView.of(ActualKind.INVALID_UNICODE);
        BoundaryOutcome outcome = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, invalid);
        expectFail(outcome, FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected string, got invalid Unicode scalar encoding", "string", "invalid-unicode",
            new LinkedHashMap<>(), null, "string descriptor vs invalid-unicode view");

        // The pinned message is the registry row's second template, verbatim.
        check(TD_ROW.templates().get(1).equals("expected string, got invalid Unicode scalar encoding"),
            "the invalid-string message is the TYPE_DESCRIPTOR row's pinned template");

        // A valid string view still passes (the invalid variant is separate).
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING,
            BoundaryValueView.of(ActualKind.STRING)), "string descriptor vs string view");
    }

    // =========================================================================
    // 3. The int path in normative order
    // =========================================================================

    static void testIntPathNormativeOrder() {
        System.out.println("-- int path: kind -> NaN -> infinity -> non-integer -> E8004 range --");

        // Non-numeric kind first.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.of(ActualKind.STRING)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got string", "int", "string", new LinkedHashMap<>(), null,
            "int descriptor vs string view");

        // NaN.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(Double.NaN)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got NaN", "int", "NaN", new LinkedHashMap<>(), null,
            "int descriptor vs NaN number");

        // Both infinities.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(Double.POSITIVE_INFINITY)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got infinity", "int", "infinity", new LinkedHashMap<>(), null,
            "int descriptor vs +infinity");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(Double.NEGATIVE_INFINITY)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got infinity", "int", "infinity", new LinkedHashMap<>(), null,
            "int descriptor vs -infinity");

        // Non-integral.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(3.5)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got non-integer number", "int", "non-integer number",
            new LinkedHashMap<>(), null, "int descriptor vs 3.5");

        // E8004 at both signed32 ends; the pinned message is the INT32_RESULT
        // row's template.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(2147483648.0)),
            FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004, "int out of safe range",
            "int", "number", new LinkedHashMap<>(), null,
            "int descriptor vs 2147483648.0");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(-2147483649.0)),
            FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004, "int out of safe range",
            "int", "number", new LinkedHashMap<>(), null,
            "int descriptor vs -2147483649.0");

        // The nearest valid values on each side pass and keep the same value.
        BoundaryValueView maxInt = BoundaryValueView.ofNumber(2147483647.0);
        BoundaryOutcome maxOutcome = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT, maxInt);
        expectPass(maxOutcome, "int descriptor vs 2147483647.0");
        check(((BoundaryOutcome.Pass) maxOutcome).value() == maxInt,
            "an in-range integral number carrier passes and stays the same value");

        BoundaryValueView minInt = BoundaryValueView.ofNumber(-2147483648.0);
        BoundaryOutcome minOutcome = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT, minInt);
        expectPass(minOutcome, "int descriptor vs -2147483648.0");
        check(((BoundaryOutcome.Pass) minOutcome).value() == minInt,
            "-2147483648.0 stays the same value");

        // The fraction just outside each end is non-integral (before the range).
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(2147483647.5)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got non-integer number", "int", "non-integer number",
            new LinkedHashMap<>(), null, "int descriptor vs 2147483647.5");

        // Zero forms and plain integral carriers pass.
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
            BoundaryValueView.ofNumber(3.0)), "int descriptor vs 3.0");
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
            BoundaryValueView.ofNumber(0.0)), "int descriptor vs 0.0");
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
            BoundaryValueView.ofNumber(-0.0)), "int descriptor vs -0.0");
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
            BoundaryValueView.ofInt(-2147483648)), "int descriptor vs INT(-2147483648)");
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT,
            BoundaryValueView.ofInt(2147483647)), "int descriptor vs INT(2147483647)");

        // number accepts an int carrier.
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER,
            BoundaryValueView.ofInt(5)), "number descriptor vs INT(5)");
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER,
            BoundaryValueView.ofNumber(5.5)), "number descriptor vs 5.5");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER,
                BoundaryValueView.of(ActualKind.BOOLEAN)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected number, got boolean", "number", "boolean", new LinkedHashMap<>(), null,
            "number descriptor vs boolean view");
    }

    // =========================================================================
    // 4. Class atom byte-equality
    // =========================================================================

    static void testClassAtom() {
        System.out.println("-- class atom byte-equality --");

        BoundaryValueView user = BoundaryValueView.ofClass("@src/app/User");
        BoundaryOutcome match = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, USER, user);
        expectPass(match, "class descriptor vs byte-equal atom");
        check(((BoundaryOutcome.Pass) match).value() == user, "same value passes through");

        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, USER,
                BoundaryValueView.ofClass("@src/app/Admin")),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected @src/app/User, got class:@src/app/Admin", "@src/app/User",
            "class:@src/app/Admin", new LinkedHashMap<>(), null,
            "class descriptor vs byte-mismatched atom");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, USER,
                BoundaryValueView.ofNumber(1)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected @src/app/User, got number", "@src/app/User", "number",
            new LinkedHashMap<>(), null, "class descriptor vs non-class view");

        // The builtin Error atom is the schema-pinned @/Error spelling.
        expectPass(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, BUILTIN_ERROR,
            BoundaryValueView.ofClass("@/Error")), "builtin Error atom matches");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, BUILTIN_ERROR,
                BoundaryValueView.ofClass("@src/app/User")),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected @/Error, got class:@src/app/User", "@/Error", "class:@src/app/User",
            new LinkedHashMap<>(), null, "builtin Error vs foreign class atom");
    }

    // =========================================================================
    // 5. E8003: first failing element in increasing index order, cause = leaf
    // =========================================================================

    static void testArrayE8003() {
        System.out.println("-- array [D]: E8003 first failing element with leaf cause --");

        BoundaryValueView badSecond = BoundaryValueView.ofArray(
            BoundaryValueView.ofNumber(1.5),
            BoundaryValueView.of(ActualKind.STRING),
            BoundaryValueView.ofNumber(2.5));
        BoundaryFailure leafSecond = expectedKindMismatch("number", "string");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER_ARRAY, badSecond),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 2 type mismatch", "number", "string",
            Map.of("oneBasedIndex", "2"), leafSecond,
            "[number] vs [1.5, string, 2.5]");

        // The first failure wins in increasing index order (position 1 here).
        BoundaryValueView badFirst = BoundaryValueView.ofArray(
            BoundaryValueView.of(ActualKind.STRING),
            BoundaryValueView.ofNumber(1.5));
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER_ARRAY, badFirst),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 1 type mismatch", "number", "string",
            Map.of("oneBasedIndex", "1"), expectedKindMismatch("number", "string"),
            "[number] vs [string, 1.5]");

        // Nested arrays: the outer index is the failing element's position;
        // the cause is the leaf descriptor error.
        BoundaryValueView nested = BoundaryValueView.ofArray(
            BoundaryValueView.ofArray(BoundaryValueView.ofInt(3)),
            BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1.5)));
        BoundaryFailure leafNonIntegral = expected(TD_ROW, 0, "int", "non-integer number",
            new LinkedHashMap<>(), null);
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NESTED_INT_ARRAY, nested),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 2 type mismatch", "[int]", "array",
            Map.of("oneBasedIndex", "2"), leafNonIntegral,
            "[[int]] vs [[3], [1.5]]");

        // A leaf E8004 travels inside the cause with its code and template.
        BoundaryValueView rangeLeaf = BoundaryValueView.ofArray(
            BoundaryValueView.ofNumber(3000000000.0));
        BoundaryFailure leafRange = expected(RANGE_ROW, 0, "int", "number",
            new LinkedHashMap<>(), null);
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, INT_ARRAY, rangeLeaf),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 1 type mismatch", "int", "number",
            Map.of("oneBasedIndex", "1"), leafRange,
            "[int] vs [3000000000.0]");

        // Non-array kind against an array descriptor is a plain E8001.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER_ARRAY,
                BoundaryValueView.of(ActualKind.STRING)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected [number], got string", "[number]", "string", new LinkedHashMap<>(),
            null, "[number] vs string view");

        // An empty array passes with the same value.
        BoundaryValueView empty = BoundaryValueView.ofArray();
        BoundaryOutcome emptyOutcome = checkCell(FailurePolicyId.TYPE_DESCRIPTOR,
            NUMBER_ARRAY, empty);
        expectPass(emptyOutcome, "[number] vs empty array");
        check(((BoundaryOutcome.Pass) emptyOutcome).value() == empty, "empty array unchanged");
    }

    // =========================================================================
    // 6. FUNCTION_SIGNATURE: E8010 mismatch vs non-function E8001
    // =========================================================================

    static void testFunctionSignature() {
        System.out.println("-- FUNCTION_SIGNATURE: E8010 signature mismatch vs E8001 --");

        BoundaryValueView matching = BoundaryValueView.ofFunction(SYNC_INT_TO_STRING);
        BoundaryOutcome matchOutcome = checkCell(FailurePolicyId.FUNCTION_SIGNATURE,
            SYNC_INT_TO_STRING, matching);
        expectPass(matchOutcome, "function descriptor vs structurally equal signature");
        check(((BoundaryOutcome.Pass) matchOutcome).value() == matching,
            "a matching function value passes unchanged");

        expectFail(checkCell(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(SYNC_INT_TO_INT)),
            FailurePolicyId.FUNCTION_SIGNATURE, DiagnosticCode.E8010,
            "function signature mismatch: expected (int)->string, got (int)->int",
            "(int)->string", "(int)->int", new LinkedHashMap<>(), null,
            "differing carried signature");

        // The async marker is part of the signature.
        expectFail(checkCell(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(ASYNC_INT_TO_STRING)),
            FailurePolicyId.FUNCTION_SIGNATURE, DiagnosticCode.E8010,
            "function signature mismatch: expected (int)->string, got async(int)->string",
            "(int)->string", "async(int)->string", new LinkedHashMap<>(), null,
            "async marker mismatch");

        // Non-function values are E8001 with the pinned function row: the
        // fixed "function" expected token both target runtimes project and
        // the shared actual-kind classification (never the descriptor
        // text; ISSUE-0681).
        expectFail(checkCell(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.ofNumber(1)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected function, got number", "function", "number",
            new LinkedHashMap<>(), null, "non-function view vs function descriptor");
        expectFail(checkCell(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.of(ActualKind.MISSING)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected function, got missing", "function", "missing",
            new LinkedHashMap<>(), null, "missing view vs function descriptor");

        // The descriptor/policy pairing is a validator cell: broken pairings fail closed.
        expectDefect(() -> checkCell(FailurePolicyId.TYPE_DESCRIPTOR, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(SYNC_INT_TO_STRING)),
            "TYPE_DESCRIPTOR with a function descriptor");
        expectDefect(() -> checkCell(FailurePolicyId.FUNCTION_SIGNATURE, STRING,
                BoundaryValueView.of(ActualKind.STRING)),
            "FUNCTION_SIGNATURE with a non-function descriptor");
    }

    // =========================================================================
    // 7. HOST_PARAMETER {index}
    // =========================================================================

    static void testHostParameter() {
        System.out.println("-- HOST_PARAMETER: the single pinned E8010 template --");

        expectFail(checkCell(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofNumber(3.5), BoundaryContext.parameter(2)),
            FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
            "parameter 2 type mismatch: expected int, got non-integer number",
            "int", "non-integer number", Map.of("index", "2"), null,
            "host parameter 2 vs 3.5");

        expectFail(checkCell(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofNumber(Double.NaN), BoundaryContext.parameter(1)),
            FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
            "parameter 1 type mismatch: expected int, got NaN",
            "int", "NaN", Map.of("index", "1"), null,
            "host parameter 1 vs NaN");

        // Function-typed parameters project the carried signature as actual.
        expectFail(checkCell(FailurePolicyId.HOST_PARAMETER, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(SYNC_INT_TO_INT), BoundaryContext.parameter(1)),
            FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
            "parameter 1 type mismatch: expected (int)->string, got (int)->int",
            "(int)->string", "(int)->int", Map.of("index", "1"), null,
            "host function parameter signature mismatch");

        // An array parameter with a failing element projects the whole array kind.
        expectFail(checkCell(FailurePolicyId.HOST_PARAMETER, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1),
                    BoundaryValueView.of(ActualKind.STRING)),
                BoundaryContext.parameter(1)),
            FailurePolicyId.HOST_PARAMETER, DiagnosticCode.E8010,
            "parameter 1 type mismatch: expected [number], got array",
            "[number]", "array", Map.of("index", "1"), null,
            "host array parameter with a failing element");

        // Success passes the same value.
        BoundaryValueView ok = BoundaryValueView.ofInt(3);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.HOST_PARAMETER, INT, ok,
            BoundaryContext.parameter(1));
        expectPass(okOutcome, "host parameter 1 vs INT(3)");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok, "host parameter pass unchanged");

        // Context defects: missing or non-one-based parameterIndex fails closed.
        expectDefect(() -> checkCell(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofInt(1), BoundaryContext.none()),
            "HOST_PARAMETER without parameterIndex");
        expectDefect(() -> checkCell(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofInt(1),
                new BoundaryContext(0, null, null, null, null)),
            "HOST_PARAMETER with a zero parameterIndex");
    }

    // =========================================================================
    // 8. HOST_SYNC_RETURN: got nothing / got {actual}
    // =========================================================================

    static void testHostSyncReturn() {
        System.out.println("-- HOST_SYNC_RETURN: no value first, then the check --");

        expectFail(checkCell(FailurePolicyId.HOST_SYNC_RETURN, STRING,
                BoundaryValueView.of(ActualKind.NOTHING)),
            FailurePolicyId.HOST_SYNC_RETURN, DiagnosticCode.E8010,
            "return value 1 type mismatch: expected string, got nothing",
            "string", "nothing", new LinkedHashMap<>(), null,
            "host sync return vs nothing");

        expectFail(checkCell(FailurePolicyId.HOST_SYNC_RETURN, STRING,
                BoundaryValueView.ofNumber(1)),
            FailurePolicyId.HOST_SYNC_RETURN, DiagnosticCode.E8010,
            "return value 1 type mismatch: expected string, got number",
            "string", "number", new LinkedHashMap<>(), null,
            "host sync return vs number");

        expectFail(checkCell(FailurePolicyId.HOST_SYNC_RETURN, NULL_DESCRIPTOR,
                BoundaryValueView.of(ActualKind.NOTHING)),
            FailurePolicyId.HOST_SYNC_RETURN, DiagnosticCode.E8010,
            "return value 1 type mismatch: expected null, got nothing",
            "null", "nothing", new LinkedHashMap<>(), null,
            "null host sync return vs nothing");

        BoundaryValueView ok = BoundaryValueView.of(ActualKind.STRING);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.HOST_SYNC_RETURN, STRING, ok);
        expectPass(okOutcome, "host sync return vs string");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok, "host return pass unchanged");
        expectPass(checkCell(FailurePolicyId.HOST_SYNC_RETURN, NULL_DESCRIPTOR,
            BoundaryValueView.nullView()), "null host sync return vs null");
    }

    // =========================================================================
    // 9. ASYNC_COMPLETION
    // =========================================================================

    static void testAsyncCompletion() {
        System.out.println("-- ASYNC_COMPLETION: mismatch through the row's E8001 template "
            + "(the corpus-aligned expected-only text; a numeric carrier is the "
            + "number kind) --");

        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, STRING,
                BoundaryValueView.ofNumber(1)),
            FailurePolicyId.ASYNC_COMPLETION, DiagnosticCode.E8001,
            "expected string", "string", "number", new LinkedHashMap<>(), null,
            "async completion vs number");

        // The cell's numeric carriers share the single number kind: the
        // shared int carrier mismatching a non-numeric descriptor projects
        // the pinned corpus actual kind, never "int".
        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, STRING,
                BoundaryValueView.ofInt(1)),
            FailurePolicyId.ASYNC_COMPLETION, DiagnosticCode.E8001,
            "expected string", "string", "number", new LinkedHashMap<>(), null,
            "async completion vs int carrier");

        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, INT,
                BoundaryValueView.ofNumber(Double.NaN)),
            FailurePolicyId.ASYNC_COMPLETION, DiagnosticCode.E8001,
            "expected int, got NaN", "int", "NaN", new LinkedHashMap<>(), null,
            "async int completion vs NaN");

        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, INT,
                BoundaryValueView.ofNumber(2147483648.0)),
            FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004, "int out of safe range",
            "int", "number", new LinkedHashMap<>(), null,
            "async int completion out of range");

        // Array completions project the shared E8003 with the leaf cause;
        // the leaf's projection is the executing policy's row (ASYNC_COMPLETION).
        BoundaryFailure leaf = expected(AC_ROW, 0, "number", "string",
            new LinkedHashMap<>(), null);
        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1),
                    BoundaryValueView.of(ActualKind.STRING))),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 2 type mismatch", "number", "string",
            Map.of("oneBasedIndex", "2"), leaf, "async array completion element 2");

        BoundaryValueView ok = BoundaryValueView.of(ActualKind.STRING);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.ASYNC_COMPLETION, STRING, ok);
        expectPass(okOutcome, "async completion vs string");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok,
            "async completion pass unchanged");
    }

    // =========================================================================
    // 10. All four array cells, including index/length boundaries
    // =========================================================================

    static void testArrayElementCell() {
        System.out.println("-- ARRAY_ELEMENT_DESCRIPTOR: E8003 with the context elementIndex --");

        expectFail(checkCell(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(1.5), BoundaryContext.element(3)),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 3 type mismatch", "int", "number",
            Map.of("oneBasedIndex", "3"),
            expected(TD_ROW, 0, "int", "non-integer number", new LinkedHashMap<>(), null),
            "array element 3 vs 1.5");

        // A nested array element: the wrap uses the boundary's descriptor, the
        // whole value's kind, and the leaf cause.
        expectFail(checkCell(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, NESTED_INT_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1.5)),
                BoundaryContext.element(1)),
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
            "array element 1 type mismatch", "[[int]]", "array",
            Map.of("oneBasedIndex", "1"),
            expected(TD_ROW, 0, "[int]", "number", new LinkedHashMap<>(), null),
            "nested array element vs [1.5]");

        BoundaryValueView ok = BoundaryValueView.ofInt(2);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, INT, ok,
            BoundaryContext.element(3));
        expectPass(okOutcome, "array element 3 vs INT(2)");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok,
            "array element pass unchanged");

        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, INT,
                BoundaryValueView.ofInt(2), BoundaryContext.none()),
            "ARRAY_ELEMENT_DESCRIPTOR without elementIndex");
        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, INT,
                BoundaryValueView.ofInt(2),
                new BoundaryContext(null, null, null, 0, null)),
            "ARRAY_ELEMENT_DESCRIPTOR with a zero elementIndex");
    }

    static void testArrayReadCell() {
        System.out.println("-- ARRAY_READ_INDEX_THEN_DESCRIPTOR: negative index first --");

        expectFail(checkCell(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.arrayIndex(-1)),
            FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, DiagnosticCode.E8002,
            "negative array index", null, null, new LinkedHashMap<>(), null,
            "read index -1");

        // Otherwise the cell passes through: the read's value/missing decision
        // is the contextual boundary's, not this cell's.
        BoundaryValueView ok = BoundaryValueView.ofInt(3);
        BoundaryOutcome zeroOutcome = checkCell(
            FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, INT, ok,
            BoundaryContext.arrayIndex(0));
        expectPass(zeroOutcome, "read index 0");
        check(((BoundaryOutcome.Pass) zeroOutcome).value() == ok, "read pass unchanged");
        expectPass(checkCell(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, INT,
            ok, BoundaryContext.arrayIndex(7)), "read index 7 passes through");

        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.none()),
            "ARRAY_READ_INDEX_THEN_DESCRIPTOR without index");
    }

    static void testArrayWriteCell() {
        System.out.println("-- ARRAY_WRITE_BOUNDS_THEN_ELEMENT: bounds first, then the element --");

        expectFail(checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.writeBounds(-1, 5)),
            FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, DiagnosticCode.E8002,
            "array index out of bounds", null, null, new LinkedHashMap<>(), null,
            "write index -1, length 5");

        expectFail(checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.writeBounds(6, 5)),
            FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, DiagnosticCode.E8002,
            "array index out of bounds", null, null, new LinkedHashMap<>(), null,
            "gap write index 6, length 5");

        // index == length is the append slot: the element check runs.
        expectFail(checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofNumber(1.5), BoundaryContext.writeBounds(5, 5)),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected int, got non-integer number", "int", "non-integer number",
            new LinkedHashMap<>(), null, "append-slot write vs 1.5 (leaf projection)");

        BoundaryValueView ok = BoundaryValueView.ofInt(3);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
            INT, ok, BoundaryContext.writeBounds(0, 0));
        expectPass(okOutcome, "write index 0 into an empty array");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok, "write pass unchanged");

        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.none()),
            "ARRAY_WRITE_BOUNDS_THEN_ELEMENT without index/length");
        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(3),
                new BoundaryContext(null, 0, null, null, null)),
            "ARRAY_WRITE_BOUNDS_THEN_ELEMENT without length");
        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(3),
                new BoundaryContext(null, 0, -1, null, null)),
            "ARRAY_WRITE_BOUNDS_THEN_ELEMENT with a negative length");
    }

    static void testArrayDeleteCell() {
        System.out.println("-- ARRAY_DELETE_BOUNDS: index < 0 or > length --");

        expectFail(checkCell(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.writeBounds(-1, 5)),
            FailurePolicyId.ARRAY_DELETE_BOUNDS, DiagnosticCode.E8002,
            "array index out of bounds", null, null, new LinkedHashMap<>(), null,
            "delete index -1, length 5");

        expectFail(checkCell(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.writeBounds(6, 5)),
            FailurePolicyId.ARRAY_DELETE_BOUNDS, DiagnosticCode.E8002,
            "array index out of bounds", null, null, new LinkedHashMap<>(), null,
            "delete index 6, length 5");

        // index == length passes: the commit's nil write runs after the boundary.
        BoundaryValueView ok = BoundaryValueView.ofInt(3);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT, ok,
            BoundaryContext.writeBounds(5, 5));
        expectPass(okOutcome, "delete index 5, length 5");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok, "delete pass unchanged");

        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT,
                BoundaryValueView.ofInt(3), BoundaryContext.none()),
            "ARRAY_DELETE_BOUNDS without index/length");
        expectDefect(() -> checkCell(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT,
                BoundaryValueView.ofInt(3),
                new BoundaryContext(null, 0, null, null, null)),
            "ARRAY_DELETE_BOUNDS without length");
    }

    // =========================================================================
    // 11. JSON_FROM_NULL swallow and JSON_TO_ERROR {fieldPath}
    // =========================================================================

    static void testJsonFromNull() {
        System.out.println("-- JSON_FROM_NULL: every failure swallows into language null --");

        BoundaryOutcome bad = checkCell(FailurePolicyId.JSON_FROM_NULL, STRING,
            BoundaryValueView.ofNumber(1));
        BoundaryOutcome.Pass badPass = expectPass(bad, "JSON_FROM_NULL vs number (swallowed)");
        check(badPass.value().kind() == ActualKind.NULL,
            "a swallowed JSON_FROM_NULL failure publishes language null");

        // A function-typed field failure swallows too (never a DEAL failure).
        BoundaryOutcome funcBad = checkCell(FailurePolicyId.JSON_FROM_NULL, SYNC_INT_TO_STRING,
            BoundaryValueView.ofFunction(SYNC_INT_TO_INT));
        expectPass(funcBad, "JSON_FROM_NULL signature failure swallowed");
        check(((BoundaryOutcome.Pass) funcBad).value().kind() == ActualKind.NULL,
            "swallowed signature failure publishes language null");

        // A valid value passes through unchanged.
        BoundaryValueView ok = BoundaryValueView.of(ActualKind.STRING);
        BoundaryOutcome okOutcome = checkCell(FailurePolicyId.JSON_FROM_NULL, STRING, ok);
        expectPass(okOutcome, "JSON_FROM_NULL vs string");
        check(((BoundaryOutcome.Pass) okOutcome).value() == ok,
            "a valid JSON_FROM_NULL value passes unchanged");
    }

    static void testJsonToError() {
        System.out.println("-- JSON_TO_ERROR: first failure projects {fieldPath} --");

        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.ofNumber(Double.NaN), BoundaryContext.jsonField("data.value")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at data.value is not JSON serializable: number",
            null, "number", Map.of("fieldPath", "data.value"), null,
            "nonfinite number at data.value");

        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.ofFunction(SYNC_INT_TO_STRING),
                BoundaryContext.jsonField("f")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at f is not JSON serializable: function",
            null, "function", Map.of("fieldPath", "f"), null,
            "function value at f");

        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.of(ActualKind.MISSING), BoundaryContext.jsonField("f")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at f is not JSON serializable: missing",
            null, "missing", Map.of("fieldPath", "f"), null,
            "missing required value at f");

        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, USER,
                BoundaryValueView.ofClass("@src/app/Admin"), BoundaryContext.jsonField("u")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at u is not JSON serializable: class:@src/app/Admin",
            null, "class:@src/app/Admin", Map.of("fieldPath", "u"), null,
            "wrong class identity at u");

        // Arrays fail at the first declaration-order element.
        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1),
                    BoundaryValueView.of(ActualKind.STRING)),
                BoundaryContext.jsonField("rows")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at rows is not JSON serializable: string",
            null, "string", Map.of("fieldPath", "rows"), null,
            "array element 2 at rows");

        // Nonfinite elements fail inside arrays too.
        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(Double.POSITIVE_INFINITY)),
                BoundaryContext.jsonField("rows")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at rows is not JSON serializable: number",
            null, "number", Map.of("fieldPath", "rows"), null,
            "nonfinite array element at rows");

        // An int field rejects non-integral and out-of-range carriers as numbers.
        expectFail(checkCell(FailurePolicyId.JSON_TO_ERROR, INT,
                BoundaryValueView.ofNumber(3.5), BoundaryContext.jsonField("i")),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "value at i is not JSON serializable: number",
            null, "number", Map.of("fieldPath", "i"), null,
            "int field vs 3.5");

        // Valid values pass unchanged.
        BoundaryValueView okNumber = BoundaryValueView.ofNumber(1.5);
        BoundaryOutcome okNumberOutcome = checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER,
            okNumber, BoundaryContext.jsonField("n"));
        expectPass(okNumberOutcome, "JSON_TO_ERROR vs finite number");
        check(((BoundaryOutcome.Pass) okNumberOutcome).value() == okNumber,
            "valid JSON_TO_ERROR value unchanged");

        BoundaryOutcome okUserOutcome = checkCell(FailurePolicyId.JSON_TO_ERROR, USER,
            BoundaryValueView.ofClass("@src/app/User"), BoundaryContext.jsonField("u"));
        expectPass(okUserOutcome, "JSON_TO_ERROR vs matching class atom");

        expectPass(checkCell(FailurePolicyId.JSON_TO_ERROR,
                DescriptorService.describe(new Type.Nullable(Type.Number.INSTANCE)),
                BoundaryValueView.nullView(), BoundaryContext.jsonField("n")),
            "JSON_TO_ERROR nullable vs null");

        expectDefect(() -> checkCell(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.ofNumber(1), BoundaryContext.none()),
            "JSON_TO_ERROR without fieldPath");
    }

    // =========================================================================
    // 12. Missing rules: the two named cells and 'got missing' elsewhere
    // =========================================================================

    static void testMissingRules() {
        System.out.println("-- missing: the named missing->null cells and 'got missing' --");

        BoundaryValueView missing = BoundaryValueView.of(ActualKind.MISSING);

        // CONTEXTUAL_TABLE_READ with a nullable descriptor (and OPTIONAL_FIELD_READ
        // with a nullable descriptor): missing maps to null and passes.
        BoundaryOutcome nullableMissing = checkCell(FailurePolicyId.TYPE_DESCRIPTOR,
            NULLABLE_STRING, missing);
        BoundaryOutcome.Pass nullablePass = expectPass(nullableMissing,
            "nullable descriptor vs missing (missing->null mapping)");
        check(nullablePass.value().kind() == ActualKind.NULL,
            "the missing->null mapping publishes a language-null view");

        // CONTEXTUAL_TABLE_READ with a non-nullable descriptor — and every other
        // cell: missing is classified as actual kind 'missing'.
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, missing),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected string, got missing", "string", "missing", new LinkedHashMap<>(), null,
            "non-nullable descriptor vs missing");

        // OPTIONAL_FIELD_READ pre-maps missing to null at the op before
        // validation: the boundary sees null, so a nullable field passes and a
        // non-nullable field projects 'got null' (never 'got missing').
        BoundaryValueView nullView = BoundaryValueView.nullView();
        BoundaryOutcome mappedNullPass = checkCell(FailurePolicyId.TYPE_DESCRIPTOR,
            NULLABLE_STRING, nullView);
        expectPass(mappedNullPass, "OPTIONAL_FIELD_READ nullable vs pre-mapped null");
        expectFail(checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, nullView),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected string, got null", "string", "null", new LinkedHashMap<>(), null,
            "OPTIONAL_FIELD_READ non-nullable vs pre-mapped null");

        // The same classification serves every other cell of the closed table.
        expectFail(checkCell(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING, missing),
            FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected function, got missing", "function", "missing",
            new LinkedHashMap<>(), null, "function boundary vs missing");
        expectFail(checkCell(FailurePolicyId.ASYNC_COMPLETION, STRING, missing),
            FailurePolicyId.ASYNC_COMPLETION, DiagnosticCode.E8001,
            "expected string", "string", "missing", new LinkedHashMap<>(), null,
            "completion boundary vs missing");
    }

    // =========================================================================
    // 13. Pass returns the same semantic value (never copied or converted)
    // =========================================================================

    static void testPassSameValue() {
        System.out.println("-- Pass returns the same semantic value --");

        record PassCase(FailurePolicyId policy, RuntimeDescriptor descriptor,
                        BoundaryValueView view, String what) {}
        List<PassCase> cases = List.of(
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, STRING,
                BoundaryValueView.of(ActualKind.STRING), "string pass"),
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER,
                BoundaryValueView.ofInt(5), "int carrier for number"),
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(3.0), "integral number for int"),
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, NULLABLE_STRING,
                BoundaryValueView.nullView(), "language null for nullable"),
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, USER,
                BoundaryValueView.ofClass("@src/app/User"), "class atom"),
            new PassCase(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1)), "array"),
            new PassCase(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(SYNC_INT_TO_STRING), "function signature"),
            new PassCase(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofInt(1), "host parameter"),
            new PassCase(FailurePolicyId.HOST_SYNC_RETURN, STRING,
                BoundaryValueView.of(ActualKind.STRING), "host sync return"),
            new PassCase(FailurePolicyId.ASYNC_COMPLETION, STRING,
                BoundaryValueView.of(ActualKind.STRING), "async completion"),
            new PassCase(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, INT,
                BoundaryValueView.ofInt(1), "array element"),
            new PassCase(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, INT,
                BoundaryValueView.ofInt(1), "array write"),
            new PassCase(FailurePolicyId.ARRAY_DELETE_BOUNDS, INT,
                BoundaryValueView.ofInt(1), "array delete"),
            new PassCase(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.ofNumber(1), "json to error"));

        for (PassCase c : cases) {
            BoundaryContext context = c.policy() == FailurePolicyId.HOST_PARAMETER
                ? BoundaryContext.parameter(1)
                : c.policy() == FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR
                    ? BoundaryContext.element(1)
                    : c.policy() == FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT
                            || c.policy() == FailurePolicyId.ARRAY_DELETE_BOUNDS
                        ? BoundaryContext.writeBounds(0, 1)
                        : c.policy() == FailurePolicyId.JSON_TO_ERROR
                            ? BoundaryContext.jsonField("v")
                            : BoundaryContext.none();
            BoundaryOutcome outcome = checkCell(c.policy(), c.descriptor(), c.view(), context);
            BoundaryOutcome.Pass passOutcome = expectPass(outcome, c.what());
            if (passOutcome != null) {
                check(passOutcome.value() == c.view(),
                    c.what() + ": Pass carries the same view instance (never copied)");
            }
        }

        // The only permitted conversion is the named missing->null mapping:
        // the published value is a null view.
        BoundaryOutcome mapped = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, NULLABLE_STRING,
            BoundaryValueView.of(ActualKind.MISSING));
        BoundaryOutcome.Pass mappedPass = expectPass(mapped, "missing->null mapping");
        check(mappedPass.value().kind() == ActualKind.NULL,
            "the missing->null mapping is the only value conversion");
    }

    // =========================================================================
    // 14. Proved cells: SUCCESS without any check logic; closed-11 fail closed
    // =========================================================================

    static void testProvedCells() {
        System.out.println("-- proved cells: RepresentationProof never runs check logic --");

        BoundaryValueView wouldFail = BoundaryValueView.ofNumber(1);
        BoundaryOutcome checked = checkCell(FailurePolicyId.TYPE_DESCRIPTOR, STRING, wouldFail);
        expectFail(checked, FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected string, got number", "string", "number", new LinkedHashMap<>(), null,
            "the same view fails under RuntimeValidation");

        BoundaryOutcome proved = BoundaryExecutor.execute(FailurePolicyId.TYPE_DESCRIPTOR,
            STRING, wouldFail, BoundaryContext.none(),
            new BoundaryRealization.RepresentationProof("jvm-method-signature"));
        BoundaryOutcome.Pass provedPass = expectPass(proved,
            "a proved boundary passes the same view that fails under RuntimeValidation");
        check(provedPass.value() == wouldFail,
            "the proved boundary's terminal keeps the value unchanged");

        // The proof path never requires the cell's context (no check runs).
        BoundaryOutcome provedNoContext = BoundaryExecutor.execute(
            FailurePolicyId.HOST_PARAMETER, INT, BoundaryValueView.ofNumber(3.5),
            BoundaryContext.none(), new BoundaryRealization.RepresentationProof("sig"));
        expectPass(provedNoContext,
            "a proved HOST_PARAMETER cell passes without its context (no check logic)");

        // The documented null contract holds on the proof path too: a null
        // descriptor throws NPE instead of silently passing — the proof
        // branch never succeeds through an unvalidated input.
        expectNpe(() -> BoundaryExecutor.execute(FailurePolicyId.TYPE_DESCRIPTOR, null,
                BoundaryValueView.ofNumber(1.0), BoundaryContext.none(),
                new BoundaryRealization.RepresentationProof("sig")),
            "descriptor must not be null",
            "execute on the RepresentationProof path with a null descriptor");

        // RuntimeValidation dispatches to the check engine with equal outcomes.
        BoundaryOutcome validated = BoundaryExecutor.execute(FailurePolicyId.TYPE_DESCRIPTOR,
            STRING, wouldFail, BoundaryContext.none(),
            new BoundaryRealization.RuntimeValidation("check-1"));
        expectFail(validated, FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
            "expected string, got number", "string", "number", new LinkedHashMap<>(), null,
            "RuntimeValidation dispatches to check");

        // A policy outside the closed 11 fails closed on both paths.
        expectDefect(() -> BoundaryExecutor.execute(FailurePolicyId.INT32_RESULT,
                INT, BoundaryValueView.ofInt(1), BoundaryContext.none(),
                new BoundaryRealization.RepresentationProof("sig")),
            "execute with a proved boundary and an out-of-subset policy");
    }

    static void testOutsideClosed11() {
        System.out.println("-- every policy outside the closed 11 fails closed --");

        List<FailurePolicyId> outside = List.of(
            FailurePolicyId.NO_DEAL_FAILURE,
            FailurePolicyId.INT32_RESULT,
            FailurePolicyId.INT32_DIVISOR_THEN_RESULT,
            FailurePolicyId.INT32_EXPONENT_THEN_RESULT,
            FailurePolicyId.INT_CONVERSION,
            FailurePolicyId.NUMBER_CONVERSION,
            FailurePolicyId.ASYNC_OPERATION_HANDLE,
            FailurePolicyId.HOST_LOAD,
            FailurePolicyId.CLASS_CONSTRUCTION,
            FailurePolicyId.JSON_PARSE_SYNTAX,
            FailurePolicyId.SQRT_NEGATIVE,
            FailurePolicyId.THROW_TRANSFER,
            FailurePolicyId.INFRASTRUCTURE_ONLY);
        for (FailurePolicyId policy : outside) {
            expectDefect(() -> checkCell(policy, INT, BoundaryValueView.ofInt(1)),
                "policy " + policy.name() + " outside the closed 11");
        }

        // The closed 11 are exactly executable (each is exercised by the
        // projection tests above; the pairing pins keep the subset closed).
        List<FailurePolicyId> inside = List.of(
            FailurePolicyId.TYPE_DESCRIPTOR,
            FailurePolicyId.FUNCTION_SIGNATURE,
            FailurePolicyId.HOST_PARAMETER,
            FailurePolicyId.HOST_SYNC_RETURN,
            FailurePolicyId.ASYNC_COMPLETION,
            FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
            FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
            FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
            FailurePolicyId.ARRAY_DELETE_BOUNDS,
            FailurePolicyId.JSON_FROM_NULL,
            FailurePolicyId.JSON_TO_ERROR);
        check(inside.size() == 11, "the closed subset has exactly 11 policies");
    }

    // =========================================================================
    // 15. View shape invariants (closed and canonical)
    // =========================================================================

    static void testViewShapeInvariants() {
        System.out.println("-- BoundaryValueView shape invariants fail closed --");

        expectIllegalArgument(() -> BoundaryValueView.of(ActualKind.NUMBER),
            "a NUMBER view without its payload");
        expectIllegalArgument(() -> BoundaryValueView.of(ActualKind.CLASS),
            "a CLASS view without its class id");
        expectIllegalArgument(() -> BoundaryValueView.of(ActualKind.FUNCTION),
            "a FUNCTION view without its signature");
        expectIllegalArgument(() -> BoundaryValueView.of(ActualKind.ARRAY),
            "an ARRAY view without its elements");
        expectIllegalArgument(() -> new BoundaryValueView(ActualKind.NUMBER, null, null,
                null, null),
            "a NUMBER view with a null numberValue");
        expectIllegalArgument(() -> new BoundaryValueView(ActualKind.CLASS, "", null, null,
                null),
            "a CLASS view with an empty class id");
        expectIllegalArgument(() -> new BoundaryValueView(ActualKind.STRING, "@x/Y", null,
                null, null),
            "a non-class kind carrying a class id");
        expectIllegalArgument(() -> BoundaryValueView.ofInt(2147483648L),
            "an INT view outside signed32");
        expectIllegalArgument(() -> new BoundaryValueView(ActualKind.INT, null, 3.5, null,
                null),
            "an INT view with a non-integral value");
        expectIllegalArgument(() -> new BoundaryValueView(ActualKind.INT, null,
                Double.POSITIVE_INFINITY, null, null),
            "an INT view with an infinite value");

        check(BoundaryValueView.of(ActualKind.INT).kind() == ActualKind.INT
                && BoundaryValueView.of(ActualKind.INT).numberValue() == null,
            "an INT view may be classification-only");
        check(BoundaryValueView.ofNumber(Double.NaN).numberValue().isNaN(),
            "a NUMBER view carries NaN");
    }

    // =========================================================================
    // 16. Determinism
    // =========================================================================

    static void testDeterminism() {
        System.out.println("-- determinism: byte-identical repeats --");

        record Case(FailurePolicyId policy, RuntimeDescriptor descriptor,
                    BoundaryValueView view, BoundaryContext context) {}
        List<Case> cases = List.of(
            new Case(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(Double.NaN), BoundaryContext.none()),
            new Case(FailurePolicyId.TYPE_DESCRIPTOR, INT,
                BoundaryValueView.ofNumber(2147483648.0), BoundaryContext.none()),
            new Case(FailurePolicyId.TYPE_DESCRIPTOR, NUMBER_ARRAY,
                BoundaryValueView.ofArray(BoundaryValueView.ofNumber(1),
                    BoundaryValueView.of(ActualKind.STRING)), BoundaryContext.none()),
            new Case(FailurePolicyId.FUNCTION_SIGNATURE, SYNC_INT_TO_STRING,
                BoundaryValueView.ofFunction(SYNC_INT_TO_INT), BoundaryContext.none()),
            new Case(FailurePolicyId.HOST_PARAMETER, INT,
                BoundaryValueView.ofNumber(3.5), BoundaryContext.parameter(2)),
            new Case(FailurePolicyId.JSON_TO_ERROR, NUMBER,
                BoundaryValueView.ofNumber(Double.NaN), BoundaryContext.jsonField("a.b")));

        for (Case c : cases) {
            BoundaryOutcome first = checkCell(c.policy(), c.descriptor(), c.view(),
                c.context());
            for (int i = 0; i < 3; i++) {
                BoundaryOutcome repeat = checkCell(c.policy(), c.descriptor(), c.view(),
                    c.context());
                check(first.equals(repeat),
                    "repeated check of " + c.policy() + " is structurally identical");
            }
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Boundary Executor Test (ISSUE-0364, ISSUE-0233 D3) ===\n");

        testT1DescriptorWiring();
        testGenericE8001EveryCanonicalKind();
        testInvalidStringMessage();
        testIntPathNormativeOrder();
        testClassAtom();
        testArrayE8003();
        testFunctionSignature();
        testHostParameter();
        testHostSyncReturn();
        testAsyncCompletion();
        testArrayElementCell();
        testArrayReadCell();
        testArrayWriteCell();
        testArrayDeleteCell();
        testJsonFromNull();
        testJsonToError();
        testMissingRules();
        testPassSameValue();
        testProvedCells();
        testOutsideClosed11();
        testViewShapeInvariants();
        testDeterminism();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
