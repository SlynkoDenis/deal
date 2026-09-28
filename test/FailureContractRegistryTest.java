package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.RangeOrigin;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticProfile;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Verifies the ISSUE-0285 {@link FailureContractRegistry}: the closed
 * 24-row failure-policy table (code, exact templates, metadata keys,
 * origin rule, cause rule, frame rule, precedence — verbatim from the
 * parent's "Closed failure policies and canonical visible errors"), the
 * registry-owned E6005 detail→message construction, the parent-D11
 * single-producer coverage list, and the closed canonical actual-kind
 * tokens.
 *
 * <p>Tests:
 * <ol>
 *   <li>Exhaustive row coverage: enumerating all 24 closed
 *       {@link FailurePolicyId} values asserts exactly one row each —
 *       none missing, none extra, no fallback; the four reserved policy
 *       names are not enum members, not rows, and fail closed at the type
 *       level (no string-keyed lookup surface exists).</li>
 *   <li>Per-row goldens: all 24 rows' code/templates/metadata keys/origin
 *       rule/cause rule/frame rule/precedence against pinned goldens —
 *       every exact template string included (JSON parse template with
 *       {@code {oneBasedByteOffset}}/{@code {reason}}, "int out of
 *       range", "integer division by zero", "extra field '{field}' in
 *       class '{classId}'", "array index out of bounds", "function
 *       signature mismatch: expected {expected}, got {actual}", all six
 *       HOST_LOAD templates).</li>
 *   <li>E6005 construction: a detail {module, capability:
 *       FOUNDATION_VALUES, validatorRule:
 *       INDEX_INTERNAL_ERROR_SENTINEL, semanticProfile: DEAL_V1_2_INT32,
 *       irVersion: "deal.semantic-ir/1", origin} yields a diagnostic with
 *       code E6005, phase BACKEND_LOWERING, and the instantiated message
 *       carrying the detail; E6000 construction stays E6000 and carries
 *       no E6005 payload.</li>
 *   <li>Canonical actual-kind tokens: exactly the 13 pinned values; the
 *       class token renders {@code class:<ClassId>}; target class names
 *       never appear on a non-class kind (fails closed).</li>
 *   <li>Immutability: rows and the table are immutable; repeated lookups
 *       return the identical row instance.</li>
 * </ol>
 */
public class FailureContractRegistryTest {

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

    private static void expectThrows(Class<? extends Throwable> type, Runnable action,
                                     String message) {
        try {
            action.run();
            fail(message + " (no exception thrown)");
        } catch (Throwable t) {
            check(type.isInstance(t), message + " (threw " + t.getClass().getSimpleName()
                + ": " + t.getMessage() + ")");
        }
    }

    // =========================================================================
    // 1. Exhaustive row coverage + reserved names fail closed
    // =========================================================================

    static void testExhaustiveRowCoverage() {
        System.out.println("-- Exhaustive row coverage --");

        Map<FailurePolicyId, FailurePolicyRow> rows = FailureContractRegistry.rows();
        check(rows.size() == 27, "exactly 27 rows; got " + rows.size());
        check(rows.keySet().equals(EnumSet.allOf(FailurePolicyId.class)),
            "the row keys are exactly all 27 FailurePolicyId values (none missing, none extra)");

        int enumerated = 0;
        for (FailurePolicyId policy : FailurePolicyId.values()) {
            FailurePolicyRow row = FailureContractRegistry.row(policy);
            check(row != null, "row exists for " + policy);
            check(row.policy() == policy, "row key matches for " + policy);
            check(row == rows.get(policy), "row(policy) and rows() agree for " + policy);
            check(row == FailureContractRegistry.row(policy),
                "one immutable row instance per policy for " + policy);
            enumerated++;
        }
        check(enumerated == 27, "enumerated all 27 policies (got " + enumerated + ")");

        expectThrows(NullPointerException.class,
            () -> FailureContractRegistry.row(null), "null policy fails closed");

        // The four reserved policy names are not rows: no enum member, no
        // registry entry, no string-keyed fallback surface, and valueOf
        // fails closed (type-level impossibility).
        List<String> reserved = List.of("EXTERNAL_PARAMETER", "EXTERNAL_RETURN",
            "STDLIB_PARAMETER", "STDLIB_RETURN");
        check(FailurePolicyId.RESERVED_NAMES.equals(reserved),
            "the four reserved policy names are pinned on the closed enum");
        for (String name : reserved) {
            check(FailurePolicyId.isReservedName(name),
                name + " is a reserved policy name");
            boolean isMember = false;
            for (FailurePolicyId p : FailurePolicyId.values()) {
                if (p.name().equals(name)) {
                    isMember = true;
                }
            }
            check(!isMember, name + " is not a FailurePolicyId enum member");
            expectThrows(IllegalArgumentException.class,
                () -> FailurePolicyId.valueOf(name),
                name + " fails closed through valueOf");
        }

        // Fail closed: no public registry surface accepts a string policy
        // name and returns a row (the only lookup key is the closed enum).
        for (Method m : FailureContractRegistry.class.getDeclaredMethods()) {
            if (Modifier.isPublic(m.getModifiers()) && Modifier.isStatic(m.getModifiers())
                    && m.getReturnType() == FailurePolicyRow.class) {
                for (Class<?> param : m.getParameterTypes()) {
                    check(param == FailurePolicyId.class,
                        "the only row-lookup key type is the closed FailurePolicyId enum "
                            + "(offending surface: " + m + ")");
                }
            }
        }
    }

    // =========================================================================
    // 2. Per-row goldens (verbatim parent row data)
    // =========================================================================

    private static void expectRow(FailurePolicyId policy, String code, String phase,
                                  List<String> templates, List<String> metadataKeys,
                                  String originRule, String causeRule, String frameRule,
                                  String precedence) {
        FailurePolicyRow row = FailureContractRegistry.row(policy);
        if (code == null) {
            check(row.code() == null,
                policy + " pins no fixed DEAL-visible code (got " + row.code() + ")");
        } else {
            check(row.code() != null && code.equals(row.code().code()),
                policy + " code is " + code + " (got "
                    + (row.code() == null ? "null" : row.code().code()) + ")");
            check(row.code() == DiagnosticCode.fromCode(code),
                policy + " code resolves to the registered diagnostic");
            check(row.code() != null && phase.equals(row.code().phase().name()),
                policy + " phase is " + phase);
        }
        check(templates.equals(row.templates()),
            policy + " templates are exactly " + templates + " (got " + row.templates() + ")");
        check(metadataKeys.equals(row.metadataKeys()),
            policy + " metadata keys are exactly " + metadataKeys
                + " (got " + row.metadataKeys() + ")");
        check(originRule.equals(row.originRule()),
            policy + " origin rule is exactly \"" + originRule
                + "\" (got \"" + row.originRule() + "\")");
        check(causeRule.equals(row.causeRule()),
            policy + " cause rule is exactly \"" + causeRule
                + "\" (got \"" + row.causeRule() + "\")");
        check(frameRule.equals(row.frameRule()),
            policy + " frame rule is exactly \"" + frameRule
                + "\" (got \"" + row.frameRule() + "\")");
        check(precedence.equals(row.precedence()),
            policy + " precedence is exactly \"" + precedence
                + "\" (got \"" + row.precedence() + "\")");
        if (templates.isEmpty()) {
            check(row.template() == null, policy + " primary template is null (no templates)");
        } else {
            check(templates.get(0).equals(row.template()),
                policy + " primary template is the first pinned template");
        }
    }

    static void testPerRowGoldens() {
        System.out.println("-- Per-row goldens (24 policies) --");

        String op = "the operation origin";
        String none = "no cause";
        String frames = "active DEAL calls from innermost to outermost";

        expectRow(FailurePolicyId.NO_DEAL_FAILURE, null, null, List.of(), List.of(),
            "propagation only: a propagated child/operand failure keeps its own origin",
            "propagation only: a propagated child/operand failure keeps its own cause",
            "propagation only: a propagated child/operand failure keeps its own frames",
            "only already-started child/operand failure may propagate");

        expectRow(FailurePolicyId.TYPE_DESCRIPTOR, "E8001", "RUNTIME",
            List.of("expected {expected}, got {actual}",
                "expected string, got invalid Unicode scalar encoding",
                "expected bytes"),
            List.of("expected", "actual"),
            op, none, frames,
            "single check: wrong-kind or invalid-unicode-string projection per the checked "
                + "descriptor (descriptor is expected; actual kind is actual)");

        expectRow(FailurePolicyId.INT32_RESULT, "E8004", "RUNTIME",
            List.of("int out of safe range"), List.of(),
            "arithmetic/boundary origin", none, frames,
            "single range check: integral result outside [-2147483648, 2147483647]");

        expectRow(FailurePolicyId.INT32_DIVISOR_THEN_RESULT, "E8005", "RUNTIME",
            List.of("integer division by zero"), List.of(),
            op, none, frames,
            "zero divisor first, then INT32_RESULT; -2147483648 / -1 is E8004");

        expectRow(FailurePolicyId.INT32_EXPONENT_THEN_RESULT, "E8006", "RUNTIME",
            List.of("integer exponent must be non-negative"), List.of(),
            op, none, frames,
            "negative exponent first, then INT32_RESULT");

        expectRow(FailurePolicyId.INT_CONVERSION, "E8001", "RUNTIME",
            List.of("cannot convert null to int", "expected int, got NaN",
                "expected int, got infinity", "expected int, got non-integer number"),
            List.of(),
            op, none, frames,
            "normative order: null, then NaN, then infinity, then fractional, then wrong kind "
                + "via TYPE_DESCRIPTOR, then integral out of range via E8004");

        expectRow(FailurePolicyId.NUMBER_CONVERSION, "E8001", "RUNTIME",
            List.of("cannot convert null to number"), List.of(),
            op, none, frames,
            "null first, then wrong kind via TYPE_DESCRIPTOR; int converts exactly to double");

        expectRow(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, "E8003", "RUNTIME",
            List.of("array element {oneBasedIndex} type mismatch"),
            List.of("oneBasedIndex"),
            op, "cause equal to the leaf descriptor error", frames,
            "first failing element in increasing index order");

        expectRow(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, "E8002", "RUNTIME",
            List.of("negative array index"), List.of(),
            op, none, frames,
            "negative index first, then read missing and let the contextual boundary decide "
                + "E8001/null");

        expectRow(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, "E8002", "RUNTIME",
            List.of("array index out of bounds"), List.of(),
            op, none, frames,
            "index < 0 or > length first, then the element boundary; mutation last");

        expectRow(FailurePolicyId.ARRAY_DELETE_BOUNDS, "E8002", "RUNTIME",
            List.of("array index out of bounds"), List.of(),
            "the delete-target origin", none, frames,
            "index < 0 or > length fails; otherwise no failure and the commit's nil write "
                + "runs after the boundary");

        expectRow(FailurePolicyId.FUNCTION_SIGNATURE, "E8010", "RUNTIME",
            List.of("function signature mismatch: expected {expected}, got {actual}"),
            List.of("expected", "actual"),
            "adaptation/boundary origin", none, frames,
            "single signature check; the descriptor-kind rule selects this policy for every "
                + "descriptor-checking boundary whose checked descriptor is a function type");

        expectRow(FailurePolicyId.HOST_PARAMETER, "E8010", "RUNTIME",
            List.of("parameter {index} type mismatch: expected {expected}, got {actual}"),
            List.of("index", "expected", "actual"),
            "the call origin", none, frames,
            "in one-based parameter order at the host call; all argument expressions finish "
                + "before checks");

        expectRow(FailurePolicyId.HOST_SYNC_RETURN, "E8010", "RUNTIME",
            List.of("return value 1 type mismatch: expected {expected}, got nothing",
                "return value 1 type mismatch: expected {expected}, got {actual}"),
            List.of("expected", "actual"),
            "the call origin", none, frames,
            "no value first, then wrong value");

        expectRow(FailurePolicyId.ASYNC_COMPLETION, "E8001", "RUNTIME",
            List.of("expected {expected}", "expected {expected}, got {actual}"),
            List.of("expected", "actual"),
            "await origin", none, frames,
            "operation failure wins, then the completion descriptor check");

        expectRow(FailurePolicyId.ASYNC_OPERATION_HANDLE, "E8010", "RUNTIME",
            List.of("async operation mismatch: expected {expected}, got {actual}"),
            List.of("expected", "actual"),
            "the async call origin", none, frames,
            "the ASYNC_START(HOST) op's own terminal check, not a BOUNDARY child");

        expectRow(FailurePolicyId.HOST_LOAD, "E8011", "RUNTIME",
            List.of("failed to load host module '{module}': {reason}",
                "host module '{module}' did not return a module object",
                "missing host export '{name}' in module '{module}'",
                "host export '{name}' in module '{module}' has signature mismatch: "
                    + "expected {expected}, got {actual}",
                "host class '{name}' in module '{module}' has identity mismatch: "
                    + "expected {expected}, got {actual}",
                "host class '{name}' in module '{module}' has invalid {defaults|fields} "
                    + "metadata"),
            List.of("module", "reason", "name", "expected", "actual", "defaults|fields"),
            "import origin", none, frames,
            "first declaration-order defect wins");

        expectRow(FailurePolicyId.CLASS_CONSTRUCTION, "E8007", "RUNTIME",
            List.of("extra field '{field}' in class '{classId}'"),
            List.of("field", "classId"),
            op, none, frames,
            "extra key first in provided-source order, then declaration-order field "
                + "boundaries");

        expectRow(FailurePolicyId.JSON_PARSE_SYNTAX, "E8001", "RUNTIME",
            List.of("JSON parse error at position {oneBasedByteOffset}: {reason}"),
            List.of("oneBasedByteOffset", "reason"),
            "the STDLIB_CALL(JSON_PARSE) call origin", none, frames,
            "parameter boundaries first, then the parse; a successful parse whose "
                + "top-level value is not a table then fails the STDLIB_RETURN boundary");

        expectRow(FailurePolicyId.JSON_FROM_NULL, null, null, List.of(), List.of(),
            "no visible failure: the conversion returns language null",
            "no visible failure: the swallowed failure never escapes",
            "no visible failure: the swallowed failure never escapes",
            "any syntax, unknown-key, descriptor, default, or field failure returns language "
                + "null; no partial instance is visible");

        expectRow(FailurePolicyId.JSON_TO_ERROR, "E8001", "RUNTIME",
            List.of("value at {fieldPath} is not JSON serializable: {actual}",
                "unsupported type for JSON encoding: {actual}"),
            List.of("fieldPath", "actual"),
            "call origin", none, frames,
            "first declaration-order unsupported value, wrong identity, cycle, missing "
                + "required value, or nonfinite number");

        expectRow(FailurePolicyId.SQRT_NEGATIVE, "E8001", "RUNTIME",
            List.of("sqrt of negative number"), List.of(),
            op, none, frames,
            "negative non-NaN number fails; NaN returns NaN");

        expectRow(FailurePolicyId.THROW_TRANSFER, null, null, List.of(), List.of(),
            "the supplied Error's origin; if it has no origin, the THROW origin",
            none, frames,
            "the supplied Error code/message/origin are preserved unchanged; no new failure "
                + "is synthesized");

        expectRow(FailurePolicyId.INFRASTRUCTURE_ONLY, null, null, List.of(), List.of(),
            "not a DEAL error: no DEAL diagnostic origin",
            "not a DEAL error: no cause",
            "not a DEAL error: no DEAL frames",
            "sink, clock, process, or harness failure is not a DEAL error and is not "
                + "catchable");
    }

    // =========================================================================
    // 3. E6005 construction + E6000 stays distinct
    // =========================================================================

    static void testE6005Construction() {
        System.out.println("-- E6005 construction --");

        LoweringFailureDetail detail = new LoweringFailureDetail(
            "app.main", SemanticCapability.FOUNDATION_VALUES,
            "INDEX_INTERNAL_ERROR_SENTINEL", SemanticProfile.DEAL_V1_2_INT32,
            "deal.semantic-ir/1", "CheckedProjectBuilder");

        String pinnedMessage = "Common semantic lowering failed: module 'app.main'"
            + ", capability FOUNDATION_VALUES"
            + ", validatorRule INDEX_INTERNAL_ERROR_SENTINEL"
            + ", semanticProfile DEAL_V1_2_INT32"
            + ", irVersion deal.semantic-ir/1"
            + ", origin CheckedProjectBuilder";
        check(pinnedMessage.equals(FailureContractRegistry.instantiateMessage(detail)),
            "instantiated message is exactly \"" + pinnedMessage + "\"");

        CompilerDiagnostic diagnostic = FailureContractRegistry.e6005(detail);
        check("E6005".equals(diagnostic.code()), "diagnostic code is E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            "diagnosticCode is the registered E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            "E6005 phase is BACKEND_LOWERING");
        check("error".equals(diagnostic.severity()), "E6005 severity is error");
        check(pinnedMessage.equals(diagnostic.message()),
            "diagnostic message is the registry-instantiated message carrying the detail");
        check(diagnostic.message().contains("app.main")
                && diagnostic.message().contains("FOUNDATION_VALUES")
                && diagnostic.message().contains("INDEX_INTERNAL_ERROR_SENTINEL")
                && diagnostic.message().contains("DEAL_V1_2_INT32")
                && diagnostic.message().contains("deal.semantic-ir/1")
                && diagnostic.message().contains("CheckedProjectBuilder"),
            "message carries all six detail fields");
        check("Common semantic lowering failed".equals(
                DiagnosticCode.E6005.messageTemplate())
                && diagnostic.message().startsWith("Common semantic lowering failed"),
            "message instantiates the E6005 template prefix");
        check(diagnostic.range() != null
                && diagnostic.range().origin() == RangeOrigin.SYNTHETIC
                && diagnostic.range().isCanonicalSynthetic()
                && "".equals(diagnostic.range().file()),
            "E6005 uses the canonical synthetic range (the detail names a producer, "
                + "not a source span)");
        check(diagnostic.notes().isEmpty(), "no notes attached");

        // Fail closed: null detail or a null detail field never renders.
        expectThrows(NullPointerException.class,
            () -> FailureContractRegistry.e6005(null), "e6005(null) fails closed");
        expectThrows(NullPointerException.class,
            () -> FailureContractRegistry.instantiateMessage(null),
            "instantiateMessage(null) fails closed");
        expectThrows(NullPointerException.class,
            () -> FailureContractRegistry.e6005(new LoweringFailureDetail(
                null, SemanticCapability.FOUNDATION_VALUES, "R-ENUM",
                SemanticProfile.DEAL_V1_2_INT32, "deal.semantic-ir/1", "SemanticIrValidator")),
            "a null module field fails closed");

        // E6000 remains distinct: intentional retained-target rejections
        // produce E6000, never E6005, and carry no E6005 payload.
        CompilerDiagnostic retainedRejection = CompilerDiagnostic.error(
            DiagnosticCode.E6000, "Unsupported statement type", DiagnosticRange.synthetic(""));
        check("E6000".equals(retainedRejection.code()), "E6000 construction stays E6000");
        check(retainedRejection.diagnosticCode() == DiagnosticCode.E6000,
            "E6000 diagnosticCode is the registered E6000");
        check(DiagnosticCode.E6000 != DiagnosticCode.E6005,
            "E6000 and E6005 are distinct codes");
        check(!retainedRejection.message().contains("Common semantic lowering failed")
                && !retainedRejection.message().contains("validatorRule")
                && !retainedRejection.message().contains("semanticProfile"),
            "E6000 carries no E6005 payload in its message");
    }

    // =========================================================================
    // 4. Canonical actual-kind tokens
    // =========================================================================

    static void testCanonicalActualKinds() {
        System.out.println("-- Canonical actual-kind tokens --");

        List<String> pinned = List.of("NULL", "MISSING", "BOOLEAN", "INT", "NUMBER",
            "STRING", "BYTES", "TABLE", "ARRAY", "FUNCTION", "CLASS", "ASYNC_OPERATION",
            "NOTHING", "INVALID_UNICODE");
        List<String> actual = new ArrayList<>();
        for (ActualKind kind : ActualKind.values()) {
            actual.add(kind.name());
        }
        check(actual.equals(pinned), "exactly the 14 pinned actual kinds in the pinned "
            + "order; got " + actual);
        check(ActualKind.values().length == 14,
            "no open/unknown fallback member (14 values)");

        Map<ActualKind, String> tokens = new LinkedHashMap<>();
        tokens.put(ActualKind.NULL, "null");
        tokens.put(ActualKind.MISSING, "missing");
        tokens.put(ActualKind.BOOLEAN, "boolean");
        tokens.put(ActualKind.INT, "int");
        tokens.put(ActualKind.NUMBER, "number");
        tokens.put(ActualKind.STRING, "string");
        tokens.put(ActualKind.TABLE, "table");
        tokens.put(ActualKind.ARRAY, "array");
        tokens.put(ActualKind.FUNCTION, "function");
        tokens.put(ActualKind.ASYNC_OPERATION, "async-operation");
        tokens.put(ActualKind.NOTHING, "nothing");
        tokens.put(ActualKind.INVALID_UNICODE, "invalid-unicode");
        for (var entry : tokens.entrySet()) {
            check(entry.getValue().equals(entry.getKey().token()),
                entry.getKey() + " token is \"" + entry.getValue() + "\"");
            check(entry.getValue().equals(ActualKind.canonicalToken(entry.getKey(), null)),
                "canonicalToken(" + entry.getKey() + ", null) renders the fixed token");
        }
        check(ActualKind.CLASS.token() == null,
            "CLASS has no fixed token (it renders class:<ClassId>)");
        check("class:a.b.C".equals(ActualKind.canonicalToken(ActualKind.CLASS, "a.b.C")),
            "CLASS renders class:<ClassId>");

        // Target class names never appear: fail closed for every illegal
        // combination.
        expectThrows(NullPointerException.class,
            () -> ActualKind.canonicalToken(null, null), "null kind fails closed");
        expectThrows(NullPointerException.class,
            () -> ActualKind.canonicalToken(ActualKind.CLASS, null),
            "CLASS without a class id fails closed");
        expectThrows(IllegalArgumentException.class,
            () -> ActualKind.canonicalToken(ActualKind.CLASS, ""),
            "CLASS with an empty class id fails closed");
        expectThrows(IllegalArgumentException.class,
            () -> ActualKind.canonicalToken(ActualKind.TABLE, "some.Class"),
            "a non-class actual kind with a class name fails closed (target class names "
                + "never appear)");
    }

    // =========================================================================
    // 5. Immutability
    // =========================================================================

    static void testImmutability() {
        System.out.println("-- Immutability --");

        Map<FailurePolicyId, FailurePolicyRow> rows = FailureContractRegistry.rows();
        expectThrows(UnsupportedOperationException.class,
            () -> rows.put(FailurePolicyId.NO_DEAL_FAILURE,
                FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR)),
            "the row table is unmodifiable");

        FailurePolicyRow row = FailureContractRegistry.row(FailurePolicyId.HOST_LOAD);
        expectThrows(UnsupportedOperationException.class,
            () -> row.templates().add("x"), "row templates are unmodifiable");
        expectThrows(UnsupportedOperationException.class,
            () -> row.metadataKeys().add("x"), "row metadata keys are unmodifiable");
        check(row.templates() == row.templates() && row.metadataKeys() == row.metadataKeys(),
            "row list accessors return the stable copies");

        Map<String, String> coverage = FailureContractRegistry.e6005CoverageItems();
        expectThrows(UnsupportedOperationException.class,
            () -> coverage.put("x", "y"), "the coverage-item map is unmodifiable");
        check(coverage.size() == 6, "the parent-D11 coverage list has exactly 6 items");

        Map<String, String> pinnedCoverage = new LinkedHashMap<>();
        pinnedCoverage.put("missing checked facts", "CheckedProjectBuilder");
        pinnedCoverage.put("invalid semantic IR",
            "SemanticIrValidator (the closed 14-condition rule set)");
        pinnedCoverage.put("unknown or reserved closed selector/policy",
            "SemanticIrValidator R-ENUM / R-RESERVED-NAME");
        pinnedCoverage.put("an operation outside a claimed capability",
            "the construct epics at unit-production time (ISSUE-0231..0239) against the S4 "
                + "capability catalog");
        pinnedCoverage.put("missing boundary realization",
            "the construct epics' boundary production (ISSUE-0233..0236) per parent D7");
        pinnedCoverage.put("ABI mismatch after compatibility was claimed",
            "TargetAbiValidator at stage time");
        List<String> order = new ArrayList<>(coverage.keySet());
        check(order.equals(new ArrayList<>(pinnedCoverage.keySet())),
            "coverage items appear in the pinned D11 order; got " + order);
        for (var entry : pinnedCoverage.entrySet()) {
            check(entry.getValue().equals(coverage.get(entry.getKey())),
                "coverage item \"" + entry.getKey() + "\" names its single producer "
                    + "\"" + entry.getValue() + "\"");
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Failure Contract Registry Test (ISSUE-0285) ===\n");

        testExhaustiveRowCoverage();
        testPerRowGoldens();
        testE6005Construction();
        testCanonicalActualKinds();
        testImmutability();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
