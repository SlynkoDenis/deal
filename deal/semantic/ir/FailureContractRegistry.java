package deal.semantic.ir;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.diagnostics.DiagnosticRange;

import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The closed failure-policy registry of {@code deal.semantic-ir/1}
 * (schema S5; parent "Closed failure policies and canonical visible
 * errors"): exactly one immutable {@link FailurePolicyRow} per
 * {@link FailurePolicyId}, and the registry-owned construction of every
 * E6005 diagnostic.
 *
 * <p>Closed rows. The table maps each of the 27 policies to exactly one
 * row — no missing row, no extra row, and no fallback. The row data
 * (code, templates, metadata keys, origin rule, cause rule, frame
 * rule, precedence) is the parent's closed table, including
 * the exact visible-error templates (E8001
 * {@code expected {expected}, got {actual}} plus the invalid-Unicode
 * variant, the {@code ASYNC_COMPLETION} cell's corpus-aligned
 * {@code expected {expected}} — the completion check's pinned transcript
 * text, whose numeric actual kind is the single number kind — E8002
 * {@code negative array index} /
 * {@code array index out of bounds}, E8003
 * {@code array element {oneBasedIndex} type mismatch}, E8004
 * {@code int out of safe range}, E8005 {@code integer division by zero},
 * E8006 {@code integer exponent must be non-negative}, E8007
 * {@code extra field '{field}' in class '{classId}'}, the E8010
 * signature/parameter/return/async variants, the six E8011 host-load
 * templates, the JSON parse template with
 * {@code {oneBasedByteOffset}}/{@code {reason}} metadata,
 * {@code sqrt of negative number}, and the propagation/preserve/infrastructure
 * rows). Consumers receive the resolved record in the operation snapshot
 * and never select messages.</p>
 *
 * <p>Reserved policy names are not rows. The four reserved names
 * {@code EXTERNAL_PARAMETER}, {@code EXTERNAL_RETURN},
 * {@code STDLIB_PARAMETER}, {@code STDLIB_RETURN} are not members of the
 * closed {@link FailurePolicyId} enum (they are valid
 * {@link BoundaryKind} values whose policies are selected by the
 * descriptor-kind rule), so constructing behavior for a reserved name is
 * impossible at the type level: the registry's only lookup key is the
 * enum type, there is no string-keyed row lookup and no fallback row, and
 * {@code FailurePolicyId.valueOf("EXTERNAL_PARAMETER")} fails closed.</p>
 *
 * <p>E6005 ownership. E6005 is
 * {@code E6005(Phase.BACKEND_LOWERING, "Common semantic lowering failed")}
 * in {@code deal.diagnostics.DiagnosticCode} (parent D11). This registry
 * owns the {@code LoweringFailureDetail} → instantiated E6005 message
 * construction: every foundation component submits the immutable detail
 * record to {@link #e6005(LoweringFailureDetail)} and receives the
 * diagnostic — no consumer hand-crafts an E6005 message. E6000 remains
 * distinct: intentional retained-target rejections produce E6000, never
 * E6005.</p>
 *
 * <p>E6005 coverage (parent D11) has exactly one producing component per
 * item ({@link #e6005CoverageItems()}):</p>
 * <ol>
 *   <li>missing checked facts → {@code CheckedProjectBuilder};</li>
 *   <li>invalid semantic IR → {@code SemanticIrValidator} (the closed
 *       14-condition rule set);</li>
 *   <li>unknown or reserved closed selector/policy →
 *       {@code SemanticIrValidator} R-ENUM / R-RESERVED-NAME;</li>
 *   <li>an operation outside a claimed capability → the construct epics
 *       at unit-production time (ISSUE-0231..0239) against the S4
 *       capability catalog — not a validator rule;</li>
 *   <li>missing boundary realization → the construct epics' boundary
 *       production (ISSUE-0233..0236) per parent D7;</li>
 *   <li>ABI mismatch after compatibility was claimed →
 *       {@code TargetAbiValidator} at stage time.</li>
 * </ol>
 */
public final class FailureContractRegistry {

    private FailureContractRegistry() { /* closed data table + E6005 owner */ }

    // =========================================================================
    // Closed row data (parent "Closed failure policies and canonical visible errors")
    // =========================================================================

    private static final String ORIGIN_OPERATION = "the operation origin";
    private static final String CAUSE_NONE = "no cause";
    private static final String FRAMES_ACTIVE = "active DEAL calls from innermost to outermost";

    private static final Map<FailurePolicyId, FailurePolicyRow> ROWS = buildRows();

    private static Map<FailurePolicyId, FailurePolicyRow> buildRows() {
        Map<FailurePolicyId, FailurePolicyRow> rows = new EnumMap<>(FailurePolicyId.class);

        rows.put(FailurePolicyId.NO_DEAL_FAILURE, makeRow(FailurePolicyId.NO_DEAL_FAILURE,
            null, List.of(), List.of(),
            "propagation only: a propagated child/operand failure keeps its own origin",
            "propagation only: a propagated child/operand failure keeps its own cause",
            "propagation only: a propagated child/operand failure keeps its own frames",
            "only already-started child/operand failure may propagate"));

        // Three projections share the row: template 0 is the general
        // descriptor-kind projection, template 1 the invalid-Unicode-string
        // variant, and template 2 the bytes carrier's pinned v1.2
        // projection ({@code "expected bytes"} — the canonical text every
        // backend produces for a non-bytes value at a bytes descriptor,
        // with the expected/actual metadata carried beside it).
        rows.put(FailurePolicyId.TYPE_DESCRIPTOR, makeRow(FailurePolicyId.TYPE_DESCRIPTOR,
            DiagnosticCode.E8001,
            List.of("expected {expected}, got {actual}",
                "expected string, got invalid Unicode scalar encoding",
                "expected bytes"),
            List.of("expected", "actual"),
            ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
            "single check: wrong-kind or invalid-unicode-string projection per the checked "
                + "descriptor (descriptor is expected; actual kind is actual)"));

        rows.put(FailurePolicyId.INT32_RESULT, makeRow(FailurePolicyId.INT32_RESULT,
            DiagnosticCode.E8004, List.of("int out of safe range"), List.of(),
            "arithmetic/boundary origin", CAUSE_NONE, FRAMES_ACTIVE,
            "single range check: integral result outside [-2147483648, 2147483647]"));

        rows.put(FailurePolicyId.INT32_DIVISOR_THEN_RESULT,
            makeRow(FailurePolicyId.INT32_DIVISOR_THEN_RESULT, DiagnosticCode.E8005,
                List.of("integer division by zero"), List.of(),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "zero divisor first, then INT32_RESULT; -2147483648 / -1 is E8004"));

        rows.put(FailurePolicyId.INT32_EXPONENT_THEN_RESULT,
            makeRow(FailurePolicyId.INT32_EXPONENT_THEN_RESULT, DiagnosticCode.E8006,
                List.of("integer exponent must be non-negative"), List.of(),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "negative exponent first, then INT32_RESULT"));

        rows.put(FailurePolicyId.INT_CONVERSION, makeRow(FailurePolicyId.INT_CONVERSION,
            DiagnosticCode.E8001,
            List.of("cannot convert null to int", "expected int, got NaN",
                "expected int, got infinity", "expected int, got non-integer number"),
            List.of(),
            ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
            "normative order: null, then NaN, then infinity, then fractional, then wrong kind "
                + "via TYPE_DESCRIPTOR, then integral out of range via E8004"));

        rows.put(FailurePolicyId.NUMBER_CONVERSION,
            makeRow(FailurePolicyId.NUMBER_CONVERSION, DiagnosticCode.E8001,
                List.of("cannot convert null to number"), List.of(),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "null first, then wrong kind via TYPE_DESCRIPTOR; int converts exactly to double"));

        rows.put(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
            makeRow(FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
                List.of("array element {oneBasedIndex} type mismatch"),
                List.of("oneBasedIndex"),
                ORIGIN_OPERATION, "cause equal to the leaf descriptor error", FRAMES_ACTIVE,
                "first failing element in increasing index order"));

        rows.put(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
            makeRow(FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, DiagnosticCode.E8002,
                List.of("negative array index"), List.of(),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "negative index first, then read missing and let the contextual boundary decide "
                    + "E8001/null"));

        rows.put(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
            makeRow(FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, DiagnosticCode.E8002,
                List.of("array index out of bounds"), List.of(),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "index < 0 or > length first, then the element boundary; mutation last"));

        rows.put(FailurePolicyId.ARRAY_DELETE_BOUNDS,
            makeRow(FailurePolicyId.ARRAY_DELETE_BOUNDS, DiagnosticCode.E8002,
                List.of("array index out of bounds"), List.of(),
                "the delete-target origin", CAUSE_NONE, FRAMES_ACTIVE,
                "index < 0 or > length fails; otherwise no failure and the commit's nil write "
                    + "runs after the boundary"));

        // The bytes rows (K6; the pinned v1.2 texts): allocation
        // (E8012, the bytes(...) call expression), the element read
        // (E8012, the index expression), and the element write (E8012
        // bounds first at the index expression, then E8013 range at the
        // assignment expression; the mutation runs only after both pass
        // and a failed write changes no storage).
        rows.put(FailurePolicyId.BYTES_ALLOCATE,
            makeRow(FailurePolicyId.BYTES_ALLOCATE, DiagnosticCode.E8012,
                List.of("bytes length must be non-negative"), List.of(),
                "the bytes(...) call expression", CAUSE_NONE, FRAMES_ACTIVE,
                "single check: the allocation length value is non-negative and its "
                    + "allocation succeeds"));

        rows.put(FailurePolicyId.BYTES_READ,
            makeRow(FailurePolicyId.BYTES_READ, DiagnosticCode.E8012,
                List.of("bytes index out of bounds"), List.of(),
                "the index expression", CAUSE_NONE, FRAMES_ACTIVE,
                "single bounds check: index < 0 or index >= b.length fails; otherwise the "
                    + "unsigned byte is read"));

        // Two projections share the row: template 0 is the bounds check
        // (the row's own E8012 at the index expression), template 1 is
        // the value-range check committed by the write (E8013 at the
        // assignment expression; the mutation runs last and a failed
        // write changes no storage).
        rows.put(FailurePolicyId.BYTES_WRITE,
            makeRow(FailurePolicyId.BYTES_WRITE, DiagnosticCode.E8012,
                List.of("bytes index out of bounds", "bytes value out of range"),
                List.of(),
                "the index expression for the bounds check, the assignment expression for "
                    + "the value-range check", CAUSE_NONE, FRAMES_ACTIVE,
                "bounds first (index < 0 or index >= b.length), then the value range "
                    + "(0..255), then the single mutation"));

        rows.put(FailurePolicyId.FUNCTION_SIGNATURE,
            makeRow(FailurePolicyId.FUNCTION_SIGNATURE, DiagnosticCode.E8010,
                List.of("function signature mismatch: expected {expected}, got {actual}"),
                List.of("expected", "actual"),
                "adaptation/boundary origin", CAUSE_NONE, FRAMES_ACTIVE,
                "single signature check; the descriptor-kind rule selects this policy for every "
                    + "descriptor-checking boundary whose checked descriptor is a function type"));

        rows.put(FailurePolicyId.HOST_PARAMETER, makeRow(FailurePolicyId.HOST_PARAMETER,
            DiagnosticCode.E8010,
            List.of("parameter {index} type mismatch: expected {expected}, got {actual}"),
            List.of("index", "expected", "actual"),
            "the call origin", CAUSE_NONE, FRAMES_ACTIVE,
            "in one-based parameter order at the host call; all argument expressions finish "
                + "before checks"));

        rows.put(FailurePolicyId.HOST_SYNC_RETURN,
            makeRow(FailurePolicyId.HOST_SYNC_RETURN, DiagnosticCode.E8010,
                List.of("return value 1 type mismatch: expected {expected}, got nothing",
                    "return value 1 type mismatch: expected {expected}, got {actual}"),
                List.of("expected", "actual"),
                "the call origin", CAUSE_NONE, FRAMES_ACTIVE,
                "no value first, then wrong value"));

        rows.put(FailurePolicyId.ASYNC_COMPLETION,
            makeRow(FailurePolicyId.ASYNC_COMPLETION, DiagnosticCode.E8001,
                List.of("expected {expected}", "expected {expected}, got {actual}"),
                List.of("expected", "actual"),
                "await origin", CAUSE_NONE, FRAMES_ACTIVE,
                "operation failure wins, then the completion descriptor check"));

        rows.put(FailurePolicyId.ASYNC_OPERATION_HANDLE,
            makeRow(FailurePolicyId.ASYNC_OPERATION_HANDLE, DiagnosticCode.E8010,
                List.of("async operation mismatch: expected {expected}, got {actual}"),
                List.of("expected", "actual"),
                "the async call origin", CAUSE_NONE, FRAMES_ACTIVE,
                "the ASYNC_START(HOST) op's own terminal check, not a BOUNDARY child"));

        rows.put(FailurePolicyId.HOST_LOAD, makeRow(FailurePolicyId.HOST_LOAD,
            DiagnosticCode.E8011,
            List.of("failed to load host module '{module}': {reason}",
                "host module '{module}' did not return a module object",
                "missing host export '{name}' in module '{module}'",
                "host export '{name}' in module '{module}' has signature mismatch: "
                    + "expected {expected}, got {actual}",
                "host class '{name}' in module '{module}' has identity mismatch: "
                    + "expected {expected}, got {actual}",
                "host class '{name}' in module '{module}' has invalid {defaults|fields} metadata"),
            List.of("module", "reason", "name", "expected", "actual", "defaults|fields"),
            "import origin", CAUSE_NONE, FRAMES_ACTIVE,
            "first declaration-order defect wins"));

        rows.put(FailurePolicyId.CLASS_CONSTRUCTION,
            makeRow(FailurePolicyId.CLASS_CONSTRUCTION, DiagnosticCode.E8007,
                List.of("extra field '{field}' in class '{classId}'"),
                List.of("field", "classId"),
                ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
                "extra key first in provided-source order, then declaration-order field "
                    + "boundaries"));

        rows.put(FailurePolicyId.JSON_PARSE_SYNTAX,
            makeRow(FailurePolicyId.JSON_PARSE_SYNTAX, DiagnosticCode.E8001,
                List.of("JSON parse error at position {oneBasedByteOffset}: {reason}"),
                List.of("oneBasedByteOffset", "reason"),
                "the STDLIB_CALL(JSON_PARSE) call origin", CAUSE_NONE, FRAMES_ACTIVE,
                "parameter boundaries first, then the parse; a successful parse whose "
                    + "top-level value is not a table then fails the STDLIB_RETURN boundary"));

        rows.put(FailurePolicyId.JSON_FROM_NULL, makeRow(FailurePolicyId.JSON_FROM_NULL,
            null, List.of(), List.of(),
            "no visible failure: the conversion returns language null",
            "no visible failure: the swallowed failure never escapes",
            "no visible failure: the swallowed failure never escapes",
            "any syntax, unknown-key, descriptor, default, or field failure returns language "
                + "null; no partial instance is visible"));

        // Two projections share the row: template 0 is the @jsonable
        // C$toJson walk's first declaration-order failure (the generated
        // body's pinned fieldPath spelling), template 1 is the
        // STDLIB_CALL(JSON_STRINGIFY) rejection aligned to the corpus
        // pins (the canonical actual-kind token; the walker's fieldPath
        // stays internal metadata, never part of the visible projection).
        rows.put(FailurePolicyId.JSON_TO_ERROR, makeRow(FailurePolicyId.JSON_TO_ERROR,
            DiagnosticCode.E8001,
            List.of("value at {fieldPath} is not JSON serializable: {actual}",
                "unsupported type for JSON encoding: {actual}"),
            List.of("fieldPath", "actual"),
            "call origin", CAUSE_NONE, FRAMES_ACTIVE,
            "first declaration-order unsupported value, wrong identity, cycle, missing "
                + "required value, or nonfinite number"));

        rows.put(FailurePolicyId.SQRT_NEGATIVE, makeRow(FailurePolicyId.SQRT_NEGATIVE,
            DiagnosticCode.E8001, List.of("sqrt of negative number"), List.of(),
            ORIGIN_OPERATION, CAUSE_NONE, FRAMES_ACTIVE,
            "negative non-NaN number fails; NaN returns NaN"));

        rows.put(FailurePolicyId.THROW_TRANSFER, makeRow(FailurePolicyId.THROW_TRANSFER,
            null, List.of(), List.of(),
            "the supplied Error's origin; if it has no origin, the THROW origin",
            CAUSE_NONE, FRAMES_ACTIVE,
            "the supplied Error code/message/origin are preserved unchanged; no new failure "
                + "is synthesized"));

        rows.put(FailurePolicyId.INFRASTRUCTURE_ONLY,
            makeRow(FailurePolicyId.INFRASTRUCTURE_ONLY,
                null, List.of(), List.of(),
                "not a DEAL error: no DEAL diagnostic origin",
                "not a DEAL error: no cause",
                "not a DEAL error: no DEAL frames",
                "sink, clock, process, or harness failure is not a DEAL error and is not "
                    + "catchable"));

        // Fail closed: exactly one row per closed policy — none missing, none extra.
        if (!rows.keySet().equals(EnumSet.allOf(FailurePolicyId.class))) {
            throw new IllegalStateException(
                "failure registry must carry exactly one row per FailurePolicyId value");
        }
        return Collections.unmodifiableMap(new EnumMap<>(rows));
    }

    private static FailurePolicyRow makeRow(FailurePolicyId policy, DiagnosticCode code,
                                            List<String> templates, List<String> metadataKeys,
                                            String originRule, String causeRule,
                                            String frameRule, String precedence) {
        return new FailurePolicyRow(policy, code, templates, metadataKeys,
            originRule, causeRule, frameRule, precedence);
    }

    // =========================================================================
    // Row access
    // =========================================================================

    /**
     * The closed table: every {@link FailurePolicyId} mapped to its single
     * immutable row (unmodifiable; iteration order is the enum
     * declaration order).
     */
    public static Map<FailurePolicyId, FailurePolicyRow> rows() {
        return ROWS;
    }

    /**
     * The single immutable row of a closed policy. The key type is the
     * closed enum — reserved names cannot be expressed — and a missing row
     * fails closed instead of returning any fallback.
     *
     * @param policy the closed failure policy; must not be null
     * @return the row
     * @throws NullPointerException     if {@code policy} is null
     * @throws IllegalArgumentException if no row exists (never for a
     *                                  closed enum member — fail-closed
     *                                  backstop)
     */
    public static FailurePolicyRow row(FailurePolicyId policy) {
        Objects.requireNonNull(policy, "policy must not be null");
        FailurePolicyRow row = ROWS.get(policy);
        if (row == null) {
            throw new IllegalArgumentException("no failure-contract row for policy " + policy);
        }
        return row;
    }

    // =========================================================================
    // E6005 coverage items (parent D11): one named producer per item
    // =========================================================================

    private static final Map<String, String> E6005_COVERAGE_ITEMS = buildCoverageItems();

    private static Map<String, String> buildCoverageItems() {
        Map<String, String> items = new LinkedHashMap<>();
        items.put("missing checked facts", "CheckedProjectBuilder");
        items.put("invalid semantic IR",
            "SemanticIrValidator (the closed 14-condition rule set)");
        items.put("unknown or reserved closed selector/policy",
            "SemanticIrValidator R-ENUM / R-RESERVED-NAME");
        items.put("an operation outside a claimed capability",
            "the construct epics at unit-production time (ISSUE-0231..0239) against the S4 "
                + "capability catalog");
        items.put("missing boundary realization",
            "the construct epics' boundary production (ISSUE-0233..0236) per parent D7");
        items.put("ABI mismatch after compatibility was claimed",
            "TargetAbiValidator at stage time");
        return Collections.unmodifiableMap(items);
    }

    /**
     * The parent-D11 E6005 coverage items in order, each mapped to its
     * single named producing component (unmodifiable).
     */
    public static Map<String, String> e6005CoverageItems() {
        return E6005_COVERAGE_ITEMS;
    }

    // =========================================================================
    // E6005 construction (registry-owned; no consumer hand-crafts the message)
    // =========================================================================

    /**
     * Instantiates the canonical E6005 message from the detail record.
     * The registry owns this construction: the message is the instantiated
     * E6005 template carrying every {@link LoweringFailureDetail} field,
     * deterministically, with no other content.
     *
     * @param detail the lowering-failure detail; must not be null and
     *               every field must be non-null
     * @return the instantiated message
     * @throws NullPointerException if {@code detail} or any of its fields
     *                              is null (fail closed — a broken detail
     *                              never renders)
     */
    public static String instantiateMessage(LoweringFailureDetail detail) {
        Objects.requireNonNull(detail, "detail must not be null");
        Objects.requireNonNull(detail.module(), "detail.module must not be null");
        Objects.requireNonNull(detail.capability(), "detail.capability must not be null");
        Objects.requireNonNull(detail.validatorRule(), "detail.validatorRule must not be null");
        Objects.requireNonNull(detail.semanticProfile(),
            "detail.semanticProfile must not be null");
        Objects.requireNonNull(detail.irVersion(), "detail.irVersion must not be null");
        Objects.requireNonNull(detail.origin(), "detail.origin must not be null");
        return "Common semantic lowering failed: module '" + detail.module()
            + "', capability " + detail.capability()
            + ", validatorRule " + detail.validatorRule()
            + ", semanticProfile " + detail.semanticProfile()
            + ", irVersion " + detail.irVersion()
            + ", origin " + detail.origin();
    }

    /**
     * Builds the E6005 diagnostic for a submitted detail record — the only
     * sanctioned E6005 construction surface. The diagnostic carries code
     * {@code E6005} ({@link DiagnosticCode.Phase#BACKEND_LOWERING}),
     * error severity, the instantiated message carrying the detail, and
     * the canonical synthetic range (the detail carries a producer name,
     * not a source span).
     *
     * @param detail the lowering-failure detail; must not be null and
     *               every field must be non-null
     * @return the E6005 diagnostic
     * @throws NullPointerException if {@code detail} or any of its fields
     *                              is null
     */
    public static CompilerDiagnostic e6005(LoweringFailureDetail detail) {
        return CompilerDiagnostic.error(DiagnosticCode.E6005, instantiateMessage(detail),
            DiagnosticRange.synthetic(""));
    }
}
