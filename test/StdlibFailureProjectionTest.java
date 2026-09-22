package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.LoweringSupport;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.SharedStdlibSemantics.Outcome;
import deal.semantic.SharedStdlibSemantics.Value;
import deal.semantic.SharedValueSemantics;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.RawOp;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.UnicodeScalars;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The ISSUE-0496 stdlib failure-projection and boundary-realization
 * battery: every stdlib-visible failure resolves through the canonical
 * {@link FailureContractRegistry} rows with the exact code, instantiated
 * template, metadata, origin, cause, and frame list, and every
 * {@code STDLIB_PARAMETER}/{@code STDLIB_RETURN} boundary op reports
 * exactly one realization (stdlib-operations-and-time-lock D6,
 * Contracts §{@code STDLIB_CALL} visible errors, Verification 2 and 4).
 *
 * <p>Tests:
 * <ol>
 *   <li>Registry rows: every stdlib row's pinned code/templates/metadata
 *       keys/origin/cause/frame rules, and the fail-closed unbound-
 *       placeholder defect.</li>
 *   <li>Primitive projections: the named defect classes with the exact
 *       {@code JSON_PARSE_SYNTAX} template/metadata (unexpected
 *       character, invalid escape, unterminated string, trailing
 *       content — UTF-8 byte offsets incl. multi-byte scalars), the
 *       first declaration-order {@code JSON_TO_ERROR}
 *       ({@code {fieldPath}}/{@code {actual}}), {@code SQRT_NEGATIVE},
 *       {@code INT32_RESULT} ({@code absInt(-2147483648)} and the
 *       string-length count-overflow gate), and the
 *       {@code TYPE_DESCRIPTOR} invalid-string rule.</li>
 *   <li>Oracle wiring (the single resolved-record consumer): lowered
 *       modules whose {@code STDLIB_CALL}s fail execute through the
 *       semantic oracle — parameter boundaries in order, then
 *       {@link SharedStdlibSemantics}, then the single
 *       {@code STDLIB_RETURN} boundary — and the terminal failure
 *       carries the exact code, the registry-instantiated message, the
 *       row's pinned origin, the active DEAL frames, and no cause.</li>
 *   <li>Precedence: a successful parse whose top-level value is not a
 *       table fails the {@code STDLIB_RETURN} boundary
 *       ({@code expected table, got {actual}}) before the call's
 *       terminal; a syntax defect fails the call's algorithm policy
 *       after the parameter boundaries passed; an invalid scalar
 *       encoding fails the {@code STDLIB_PARAMETER} boundary first and
 *       the algorithm never runs.</li>
 *   <li>Boundary realization: every validated stdlib boundary op carries
 *       one non-empty {@code RuntimeValidation(checkId)} directly in its
 *       active Semantic IR payload.</li>
 *   <li>Validator negative: a stdlib boundary op whose policy is
 *       outside the descriptor-kind rule is invalid IR.</li>
 * </ol>
 */
public class StdlibFailureProjectionTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (Files.isDirectory(dir)) {
                try (var walk = Files.walk(dir)) {
                    for (Path path : walk.sorted(java.util.Comparator.reverseOrder())
                            .toList()) {
                        Files.deleteIfExists(path);
                    }
                }
            }
        } catch (Exception ignored) {
            // best-effort cleanup of a temp workspace
        }
    }

    // =========================================================================
    // Sanitizer-proof string construction: bracket-bearing and quoted texts
    // are built from code points at runtime, never from single-line literals
    // (a quote-stripping compile environment would otherwise rewrite them).
    // =========================================================================

    /** A string built from Unicode code points. */
    private static String s(int... codePoints) {
        StringBuilder out = new StringBuilder();
        for (int codePoint : codePoints) {
            out.appendCodePoint(codePoint);
        }
        return out.toString();
    }

    /** The double-quote character. */
    private static String q() {
        return s(34);
    }

    /** Wraps content in double quotes (a DEAL/JSON quoted text). */
    private static String quoted(String content) {
        return q() + content + q();
    }

    // Common quoted JSON inputs (built once, deterministic).
    private static final String JSON_ARRAY_1 = s(91, 49, 93);              // [1]
    private static final String JSON_STRING_X = quoted("x");               // "x"
    private static final String JSON_NUMBER_1 = "1";                       // 1
    private static final String JSON_BAD_X = "x";                          // x
    private static final String JSON_BAD_ESCAPE = quoted("a" + s(92) + "q"); // "a\q"
    private static final String JSON_UNTERMINATED = q() + "abc";          // "abc (open only)
    private static final String JSON_TRAILING = s(123, 125, 120);          // {}x
    private static final String JSON_MULTIBYTE_TRAILING =
        s(123) + quoted("k") + s(58, 32) + quoted(s(233)) + s(125, 120);   // {"k": "é"}x
    private static final String JSON_ARRAY_MISSING = s(91, 49, 44);        // [1,

    /** The DEAL source argument text of one JSON input string: the JSON
     *  text DEAL-escaped (backslash and quote doubled) inside one pair of
     *  quotes — e.g. the JSON text `[1]` becomes `"[1]"` and the JSON text
     *  `"x"` becomes `"\"x\""` (quote = 34, backslash = 92). */
    private static String dealArg(String jsonText) {
        StringBuilder out = new StringBuilder();
        out.appendCodePoint(34);
        for (int i = 0; i < jsonText.length(); ) {
            int codePoint = jsonText.codePointAt(i);
            if (codePoint == 34 || codePoint == 92) {
                out.appendCodePoint(92);
            }
            out.appendCodePoint(codePoint);
            i += Character.charCount(codePoint);
        }
        out.appendCodePoint(34);
        return out.toString();
    }

    // =========================================================================
    // Helpers for the oracle scenarios
    // =========================================================================

    /** The synthetic primitive-level operation origin. */
    private static SourceOrigin origin() {
        return new SourceOrigin("stdlib-failure-test", SourceSpan.synthetic("stdlib"),
            SourceOriginKind.SYNTHETIC, new AnchorId(1), null);
    }

    /** The scalar-valid carrier of a test string. */
    private static UnicodeScalars.Valid valid(String text) {
        return (UnicodeScalars.Valid) UnicodeScalars.validate(text);
    }

    /** A shared stdlib string value. */
    private static Value text(String carrier) {
        return Value.string(carrier);
    }

    // =========================================================================
    // 1. The registry rows of every stdlib failure policy
    // =========================================================================

    static void testRegistryRows() {
        System.out.println("-- Registry rows: the stdlib policies' pinned data --");

        FailurePolicyRow parseRow = FailureContractRegistry.row(
            FailurePolicyId.JSON_PARSE_SYNTAX);
        check(parseRow.policy() == FailurePolicyId.JSON_PARSE_SYNTAX
                && parseRow.code() == DiagnosticCode.E8001,
            "JSON_PARSE_SYNTAX is E8001");
        check(parseRow.templates().size() == 1
                && parseRow.template().contains("JSON parse error at position ")
                && parseRow.template().contains("oneBasedByteOffset")
                && parseRow.template().contains("reason")
                && parseRow.metadataKeys().equals(
                    List.of("oneBasedByteOffset", "reason")),
            "JSON_PARSE_SYNTAX pins the exact template and the two metadata keys");
        check(parseRow.originRule().contains("STDLIB_CALL")
                && parseRow.originRule().contains("JSON_PARSE")
                && parseRow.originRule().contains("call origin"),
            "JSON_PARSE_SYNTAX pins the STDLIB_CALL JSON_PARSE call origin");
        check(parseRow.causeRule().equals("no cause")
                && parseRow.frameRule().contains("active DEAL calls"),
            "JSON_PARSE_SYNTAX pins no cause and active DEAL frames");
        check(parseRow.precedence().contains("parameter boundaries first")
                && parseRow.precedence().contains("STDLIB_RETURN"),
            "JSON_PARSE_SYNTAX pins the parameter → parse → return precedence");

        FailurePolicyRow toErrorRow = FailureContractRegistry.row(
            FailurePolicyId.JSON_TO_ERROR);
        check(toErrorRow.code() == DiagnosticCode.E8001
                && toErrorRow.templates().size() == 2
                && toErrorRow.templates().get(0).contains("is not JSON serializable")
                && toErrorRow.templates().get(1).equals(
                    "unsupported type for JSON encoding: {actual}")
                && toErrorRow.metadataKeys().equals(List.of("fieldPath", "actual")),
            "JSON_TO_ERROR pins the @jsonable template first and the corpus-aligned "
                + "STDLIB_CALL(JSON_STRINGIFY) rejection second, with the "
                + "fieldPath/actual keys");
        check(toErrorRow.originRule().equals("call origin"),
            "JSON_TO_ERROR pins the call origin");

        FailurePolicyRow sqrtRow = FailureContractRegistry.row(
            FailurePolicyId.SQRT_NEGATIVE);
        check(sqrtRow.code() == DiagnosticCode.E8001
                && sqrtRow.templates().equals(List.of("sqrt of negative number"))
                && sqrtRow.metadataKeys().isEmpty(),
            "SQRT_NEGATIVE pins E8001 'sqrt of negative number' with no metadata");
        check(sqrtRow.precedence().contains("NaN returns NaN"),
            "SQRT_NEGATIVE pins NaN-passes");

        FailurePolicyRow int32Row = FailureContractRegistry.row(
            FailurePolicyId.INT32_RESULT);
        check(int32Row.code() == DiagnosticCode.E8004
                && int32Row.templates().equals(List.of("int out of safe range")),
            "INT32_RESULT pins E8004 'int out of safe range'");

        FailurePolicyRow infraRow = FailureContractRegistry.row(
            FailurePolicyId.INFRASTRUCTURE_ONLY);
        check(infraRow.code() == null && infraRow.templates().isEmpty(),
            "INFRASTRUCTURE_ONLY has no DEAL code and no template, never a DEAL error");
        check(infraRow.precedence().contains("not catchable"),
            "INFRASTRUCTURE_ONLY is not catchable");

        FailurePolicyRow typeRow = FailureContractRegistry.row(
            FailurePolicyId.TYPE_DESCRIPTOR);
        check(typeRow.code() == DiagnosticCode.E8001
                && typeRow.templates().size() == 2
                && typeRow.templates().get(1).equals(
                    "expected string, got invalid Unicode scalar encoding"),
            "TYPE_DESCRIPTOR pins the wrong-kind template and the invalid-string "
                + "variant");

        // Row instantiation is the only message source; an unbound
        // placeholder fails closed.
        String expectedMessage = BoundaryFailure.fromRow(parseRow, 0, null, null,
            Map.of("oneBasedByteOffset", "4", "reason",
                SharedStdlibSemantics.REASON_INVALID_ESCAPE), null).message();
        check(expectedMessage.equals(
                "JSON parse error at position 4: invalid escape"),
            "the row instantiates to the exact message: " + expectedMessage);
        BoundaryFailure instantiated = BoundaryFailure.fromRow(parseRow, 0, null, null,
            Map.of("oneBasedByteOffset", "4", "reason",
                SharedStdlibSemantics.REASON_INVALID_ESCAPE), null);
        check(instantiated.code() == DiagnosticCode.E8001
                && instantiated.metadata().equals(Map.of(
                    "oneBasedByteOffset", "4",
                    "reason", SharedStdlibSemantics.REASON_INVALID_ESCAPE))
                && instantiated.cause() == null,
            "the row instantiates with the pinned metadata and no cause");
        boolean unboundFailed = false;
        try {
            BoundaryFailure.fromRow(parseRow, 0, null, null,
                new LinkedHashMap<>(), null);
        } catch (BoundaryExecutor.Defect expected) {
            unboundFailed = true;
        }
        check(unboundFailed,
            "an unbound placeholder fails closed — a broken projection never renders");
        BoundaryFailure invalidString = BoundaryFailure.fromRow(typeRow, 1, null, null,
            new LinkedHashMap<>(), null);
        check(invalidString.message().equals(
                "expected string, got invalid Unicode scalar encoding"),
            "the TYPE_DESCRIPTOR invalid-string template instantiates exactly");
    }

    // =========================================================================
    // 2. Primitive projections: the named defect classes with exact records
    // =========================================================================

    /** Asserts one sealed failure's exact projection (policy/code/message/
     *  metadata/origin/cause) against the same row's re-instantiation. */
    private static void expectProjection(Outcome<Value> outcome, FailurePolicyId policy,
                                         Map<String, String> metadata,
                                         SourceOrigin origin, String note) {
        expectProjection(outcome, policy, 0, null, null, metadata, origin, false, note);
    }

    /** Asserts one sealed failure's exact projection against the row's
     *  selected template index with the pinned expected/actual pair. */
    private static void expectProjection(Outcome<Value> outcome, FailurePolicyId policy,
                                         int templateIndex, String expected, String actual,
                                         Map<String, String> metadata,
                                         SourceOrigin origin, String note) {
        expectProjection(outcome, policy, templateIndex, expected, actual, metadata,
            origin, true, note);
    }

    private static void expectProjection(Outcome<Value> outcome, FailurePolicyId policy,
                                         int templateIndex, String expected, String actual,
                                         Map<String, String> metadata, SourceOrigin origin,
                                         boolean compareExpectedActual, String note) {
        if (outcome instanceof Outcome.Failure<Value> failure) {
            SharedStdlibSemantics.StdlibFailure stdlibFailure = failure.failure();
            BoundaryFailure projection = stdlibFailure.failure();
            FailurePolicyRow row = FailureContractRegistry.row(policy);
            String expectedMessage = BoundaryFailure.fromRow(row, templateIndex, expected,
                actual, metadata, null).message();
            boolean ok = projection.policy() == policy
                && projection.code() == row.code()
                && projection.message().equals(expectedMessage)
                && (!compareExpectedActual
                    || (java.util.Objects.equals(projection.expected(), expected)
                        && java.util.Objects.equals(projection.actual(), actual)))
                && projection.metadata().equals(metadata)
                && projection.cause() == null
                && stdlibFailure.origin().equals(origin);
            if (ok) {
                passed++;
                return;
            }
            fail(note + " — projection mismatch: policy=" + projection.policy()
                + " code=" + projection.code() + " message=\"" + projection.message()
                + "\" expected=" + projection.expected() + " actual="
                + projection.actual() + " metadata=" + projection.metadata()
                + " origin=" + stdlibFailure.origin());
            return;
        }
        fail(note + " — expected Failure, got " + outcome);
    }

    /** The two-key parse-defect metadata map. */
    private static Map<String, String> parseMeta(String offset, String reason) {
        return Map.of("oneBasedByteOffset", offset, "reason", reason);
    }

    static void testPrimitiveProjections() {
        System.out.println("-- Primitive projections: exact template/metadata/origin/cause --");

        // JSON_PARSE_SYNTAX defect classes (exact UTF-8 byte offsets;
        // multi-byte scalars count their full length).
        expectProjection(SharedStdlibSemantics.jsonParse(origin(), valid(JSON_BAD_X)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("1",
                SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER),
            origin(), "unexpected character at offset 1");
        expectProjection(SharedStdlibSemantics.jsonParse(origin(),
                valid(JSON_BAD_ESCAPE)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("4",
                SharedStdlibSemantics.REASON_INVALID_ESCAPE),
            origin(), "invalid escape at offset 4");
        expectProjection(SharedStdlibSemantics.jsonParse(origin(),
                valid(JSON_UNTERMINATED)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("5",
                SharedStdlibSemantics.REASON_UNTERMINATED_STRING),
            origin(), "unterminated string at one past the last byte");
        expectProjection(SharedStdlibSemantics.jsonParse(origin(),
                valid(JSON_TRAILING)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("3",
                SharedStdlibSemantics.REASON_TRAILING_CONTENT),
            origin(), "trailing content at offset 3");
        expectProjection(SharedStdlibSemantics.jsonParse(origin(),
                valid(JSON_MULTIBYTE_TRAILING)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("12",
                SharedStdlibSemantics.REASON_TRAILING_CONTENT),
            origin(), "a multi-byte scalar counts its full UTF-8 length, offset 12");
        expectProjection(SharedStdlibSemantics.jsonParse(origin(),
                valid(JSON_ARRAY_MISSING)),
            FailurePolicyId.JSON_PARSE_SYNTAX, parseMeta("4",
                SharedStdlibSemantics.REASON_UNEXPECTED_END),
            origin(), "a missing array value reports the end-of-input defect");

        // JSON_TO_ERROR: first declaration-order failure with the
        // corpus-aligned rejection text; the walker's {fieldPath} stays
        // internal metadata (never part of the visible projection).
        SemanticTable<Value> table = new SemanticTable<>();
        table.put("f", new Value.Other(ActualKind.FUNCTION, null));
        table.put("m", new Value.Other(ActualKind.MISSING, null));
        expectProjection(SharedStdlibSemantics.jsonStringify(origin(), table),
            FailurePolicyId.JSON_TO_ERROR, 1,
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "function",
            Map.of("fieldPath", "f", "actual", "function"),
            origin(), "the first declaration-order failure wins with fieldPath f");
        SemanticTable<Value> nested = new SemanticTable<>();
        SemanticTable<Value> inner = new SemanticTable<>();
        inner.put("bad", new Value.Other(ActualKind.FUNCTION, null));
        nested.put("a", new Value.Table(inner));
        expectProjection(SharedStdlibSemantics.jsonStringify(origin(), nested),
            FailurePolicyId.JSON_TO_ERROR, 1,
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "function",
            Map.of("fieldPath", "a.bad", "actual", "function"),
            origin(), "nested failures keep the dot-separated path as internal "
                + "metadata");

        // SQRT_NEGATIVE: E8001, operation origin; NaN passes.
        expectProjection(SharedStdlibSemantics.mathSqrt(origin(), -4.0),
            FailurePolicyId.SQRT_NEGATIVE, new LinkedHashMap<>(), origin(),
            "sqrt of -4.0 fails SQRT_NEGATIVE");
        Outcome<Value> sqrtNan = SharedStdlibSemantics.mathSqrt(origin(), Double.NaN);
        check(sqrtNan instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.isNaN(number.value()),
            "sqrt of NaN returns NaN, never a failure");

        // INT32_RESULT: absInt(-2147483648) at the call origin, and the
        // string-length count-overflow gate.
        expectProjection(SharedStdlibSemantics.mathAbsInt(origin(), -2147483648),
            FailurePolicyId.INT32_RESULT, new LinkedHashMap<>(), origin(),
            "absInt of -2147483648 fails E8004 at the call origin");
        SharedValueSemantics.Int32Result overflowGate =
            SharedValueSemantics.checkInt32Integral(2147483648L, origin());
        check(overflowGate instanceof SharedValueSemantics.Int32Result.Fail,
            "the STRING_LENGTH count-overflow gate checkInt32Integral rejects "
                + "2147483648, the INT32_RESULT path the string-length algorithm "
                + "pins");
    }

    // =========================================================================
    // 3. The oracle wiring: resolved records with origin and frames
    // =========================================================================

    /** One lowered-and-validated stdlib scenario unit. */
    private record Scenario(LoweredModuleUnit unit, StructuredBodyTable table,
                            CheckedProjectBuildResult checked, Path tmp) {
    }

    /**
     * Compiles + lowers one scenario in the two-module carrier shape: the
     * entry module "main.deal" (exported main, never lowered — the
     * carrier's subject admits no export declaration) and the subject
     * "lib.deal" whose plain functions carry the stdlib calls.
     */
    private static Scenario lowerScenario(String libSource, String what) {
        try {
            Path tmp = Files.createTempDirectory("deal-stdlib-projection");
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                import * as lib from "./lib"

                export function main(): null {
                  return null
                }
                """);
            Files.writeString(src.resolve("lib.deal"), libSource);
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize());
            boolean ok = orchestrator.compile();
            check(ok, what + ": compiles through phase 3 + builder: "
                + orchestrator.diagnostics());
            if (!ok) {
                return null;
            }
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            if (checked == null || checked.hasErrors() || checked.input() == null) {
                fail(what + ": no clean checked project");
                return null;
            }
            CheckedModuleInput subject = null;
            for (CheckedModuleInput module : checked.input().modules()) {
                if (module.moduleId().path().equals("lib")) {
                    subject = module;
                }
            }
            if (subject == null) {
                fail(what + ": no lib module in the checked project");
                return null;
            }
            CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                CapabilityRegistry.releaseRegistry());
            RequirementManifestResult manifests = LoweringSupport.computeManifests(
                invocation, checked.input(), checked.index());
            if (manifests == null || manifests.hasErrors()
                    || manifests.manifests() == null
                    || manifests.manifests().isEmpty()) {
                fail(what + ": no clean manifest: "
                    + (manifests == null ? "null" : manifests.diagnostics()));
                return null;
            }
            SemanticRequirementManifest manifest = manifests.manifests().get(0);
            List<ModuleId> moduleIds = new ArrayList<>();
            for (CheckedModuleInput module : checked.input().modules()) {
                moduleIds.add(module.moduleId());
            }
            SemanticLowerer.LoweringResult lowering = SemanticLowerer.lowerModuleFullProgram(
                subject, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
                checked.index().interfaceIndexDigest(),
                CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
                SemanticIdAllocator.over(moduleIds));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                fail(what + ": lowering failed: " + (lowering == null ? "null"
                    : lowering.diagnostics()));
                return null;
            }
            return new Scenario(lowering.unit(), lowering.table(), checked, tmp);
        } catch (Exception e) {
            fail(what + ": scenario setup threw: " + e);
            return null;
        }
    }

    /** The single {@code STDLIB_CALL} op carrying the given id, or null. */
    private static SemanticOp stdlibOpBy(LoweredModuleUnit unit,
                                         StdlibFunctionId function) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL
                    && ((KindPayload.StdlibCallPayload) op.payload()).function()
                        == function) {
                return op;
            }
        }
        return null;
    }

    /** The stdlib boundary children of the call op with the given kind. */
    private static List<SemanticOp> stdlibBoundariesOf(LoweredModuleUnit unit,
                                                       SemanticOp call,
                                                       BoundaryKind kind) {
        List<SemanticOp> boundaries = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && call.opId().equals(op.origin().parentOpId())
                    && ((KindPayload.BoundaryPayload) op.payload()).kind() == kind) {
                boundaries.add(op);
            }
        }
        return boundaries;
    }

    /** The canonical origin atom of an op (sourceId:line:column). */
    private static String originAtomOf(SemanticOp op) {
        SourceOrigin origin = op.origin();
        SourceSpan span = origin.span();
        return SemanticRuntimeModel.originAtom(origin.sourceId(),
            span == null ? null : span.startLine(),
            span == null ? null : span.startColumn());
    }

    /** The FunctionId whose body block contains the op, or null. */
    private static FunctionId owningFunctionOf(LoweredModuleUnit unit,
                                               StructuredBodyTable table,
                                               SemanticOp op) {
        for (Map.Entry<FunctionId, LoweredFunction> entry : unit.functions().entrySet()) {
            List<OpId> bodyOps = table.blockOps().get(entry.getValue().body());
            if (bodyOps != null && bodyOps.contains(op.opId())) {
                return entry.getKey();
            }
        }
        return null;
    }

    /**
     * The expected frame id strings of a failure inside the op's owning
     * function: the active direct-call chain innermost-first, derived
     * from the unit's CALL ops (the entry delegation's call owner is the
     * module-init, so the chain stops at main).
     */
    private static List<String> expectedFrames(Scenario scenario, SemanticOp call) {
        LoweredModuleUnit unit = scenario.unit();
        Map<FunctionId, FunctionId> callerOf = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CALL
                    && op.payload() instanceof KindPayload.CallPayload callPayload
                    && callPayload.callee() instanceof KindPayload.CallCallee.Static
                        staticCallee
                    && staticCallee.binding()
                        instanceof FunctionExecutionBinding.LoweredBody body) {
                FunctionId caller = owningFunctionOf(unit, scenario.table(), op);
                if (caller != null) {
                    callerOf.put(body.functionId(), caller);
                }
            }
        }
        List<String> frames = new ArrayList<>();
        FunctionId current = owningFunctionOf(unit, scenario.table(), call);
        while (current != null) {
            frames.add(String.valueOf(current.id()));
            current = callerOf.get(current);
        }
        return frames;
    }

    /**
     * Asserts the oracle terminal of one scenario: the exact code,
     * message, origin, no cause, and the active frame list.
     */
    private static void expectTerminal(Scenario scenario,
                                       SemanticRuntimeModel.ConsumerRun run,
                                       String code, String message, String origin,
                                       List<String> frames, String what) {
        expectTerminal(scenario, run, code, message, origin, frames, null, null, false,
            what);
    }

    /**
     * Asserts the oracle terminal of one scenario: the exact code,
     * message, expected/actual pair, origin, no cause, and the active
     * frame list.
     */
    private static void expectTerminal(Scenario scenario,
                                       SemanticRuntimeModel.ConsumerRun run,
                                       String code, String message, String origin,
                                       List<String> frames, String expected,
                                       String actual, String what) {
        expectTerminal(scenario, run, code, message, origin, frames, expected, actual,
            true, what);
    }

    private static void expectTerminal(Scenario scenario,
                                       SemanticRuntimeModel.ConsumerRun run,
                                       String code, String message, String origin,
                                       List<String> frames, String expected,
                                       String actual, boolean compareExpectedActual,
                                       String what) {
        if (run.terminal()
                instanceof SemanticRuntimeModel.Terminal.DealFailure terminal) {
            SemanticRuntimeModel.ErrorSnapshot error = terminal.error();
            boolean ok = error.code().equals(code)
                && error.message().equals(message)
                && (!compareExpectedActual
                    || (java.util.Objects.equals(error.expected(), expected)
                        && java.util.Objects.equals(error.actual(), actual)))
                && (origin == null || origin.equals(error.origin()))
                && error.frames().equals(frames)
                && error.cause() == null;
            if (ok) {
                passed++;
                return;
            }
            fail(what + " — terminal mismatch: code=" + error.code() + " message=\""
                + error.message() + "\" expected=" + error.expected() + " actual="
                + error.actual() + " origin=" + error.origin() + " frames="
                + error.frames() + " cause=" + error.cause());
            return;
        }
        fail(what + " — expected a DealFailure terminal, got " + run.terminal());
    }

    /** The first FAILURE event of a run, or null. */
    private static SemanticRuntimeModel.TraceEvent firstFailure(
            SemanticRuntimeModel.ConsumerRun run) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                return event;
            }
        }
        return null;
    }

    static void testOracleWiringPrecedence() {
        System.out.println("-- Oracle wiring: resolved records, precedence, frames --");

        // (a) A syntax defect: parameter boundaries pass, the algorithm
        // fails JSON_PARSE_SYNTAX at the call origin, frames [helper, main].
        Scenario syntax = lowerScenario("""
            import * as json from "std/json"

            function helper(): null {
              let t: table = json.parse("x")
              return null
            }

            function main(): null {
              helper()
              return null
            }
            """, "the nested syntax-defect scenario");
        if (syntax != null) {
            SemanticOp call = stdlibOpBy(syntax.unit(), StdlibFunctionId.JSON_PARSE);
            check(call != null, "the syntax scenario lowers one JSON_PARSE call");
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(syntax.unit(), syntax.table());
                expectTerminal(syntax, run, "E8001",
                    "JSON parse error at position 1: unexpected character",
                    originAtomOf(call), expectedFrames(syntax, call),
                    "the syntax defect projects JSON_PARSE_SYNTAX at the call origin "
                        + "with the active frames");
                SemanticRuntimeModel.TraceEvent firstFailure = firstFailure(run);
                check(firstFailure != null && firstFailure.op().equals(call.opId()),
                    "the first failing op is the STDLIB_CALL itself, no boundary "
                        + "failure; the parameter boundary passed");
                boolean paramPassed = false;
                for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                    if (event.kind() == SemanticOpKind.BOUNDARY
                            && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        paramPassed = true;
                        break;
                    }
                }
                check(paramPassed,
                    "the STDLIB_PARAMETER boundary STARTed and succeeded before the "
                        + "algorithm ran, the pinned precedence");
            }
            deleteRecursively(syntax.tmp());
        }

        // (b) A successful parse of a non-table top-level value fails the
        // STDLIB_RETURN boundary (expected table, got array/string/int).
        for (Object[] seed : List.<Object[]>of(
                new Object[] {JSON_ARRAY_1, "array"},
                new Object[] {JSON_STRING_X, "string"},
                new Object[] {JSON_NUMBER_1, "int"})) {
            String input = dealArg((String) seed[0]);
            String actual = (String) seed[1];
            Scenario nonTable = lowerScenario("""
                import * as json from "std/json"

                function main(): null {
                  let t: table = json.parse(%s)
                  return null
                }
                """.formatted(input), "the non-table top-level scenario " + input);
            if (nonTable == null) {
                continue;
            }
            SemanticOp call = stdlibOpBy(nonTable.unit(), StdlibFunctionId.JSON_PARSE);
            List<SemanticOp> returns =
                stdlibBoundariesOf(nonTable.unit(), call, BoundaryKind.STDLIB_RETURN);
            check(call != null && returns.size() == 1,
                "the scenario lowers one JSON_PARSE call with one STDLIB_RETURN");
            if (call != null && returns.size() == 1) {
                SemanticOp returnBoundary = returns.get(0);
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(nonTable.unit(), nonTable.table());
                expectTerminal(nonTable, run, "E8001",
                    "expected table, got " + actual, originAtomOf(returnBoundary),
                    expectedFrames(nonTable, call),
                    "a successful parse of " + input + " fails the STDLIB_RETURN "
                        + "boundary at the boundary origin");
                SemanticRuntimeModel.TraceEvent firstFailure = firstFailure(run);
                check(firstFailure != null
                        && firstFailure.op().equals(returnBoundary.opId()),
                    "the first failing op is the STDLIB_RETURN boundary; the "
                        + "algorithm succeeded and the return boundary failed");
            }
            deleteRecursively(nonTable.tmp());
        }

        // (c) SQRT_NEGATIVE: sqrt(-4.0) through the wiring.
        Scenario sqrt = lowerScenario("""
            import * as math from "std/math"

            function main(): null {
              let n: number = math.sqrt(-4.0)
              return null
            }
            """, "the sqrt-negative scenario");
        if (sqrt != null) {
            SemanticOp call = stdlibOpBy(sqrt.unit(), StdlibFunctionId.MATH_SQRT);
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(sqrt.unit(), sqrt.table());
                expectTerminal(sqrt, run, "E8001", "sqrt of negative number",
                    originAtomOf(call), expectedFrames(sqrt, call),
                    "sqrt of -4.0 projects SQRT_NEGATIVE at the operation origin");
            }
            deleteRecursively(sqrt.tmp());
        }

        // (d) INT32_RESULT: absInt(-2147483648) through the wiring.
        Scenario abs = lowerScenario("""
            import * as math from "std/math"

            function main(): null {
              let x: int = -2147483647 - 1
              let n: int = math.absInt(x)
              return null
            }
            """, "the absInt-min scenario");
        if (abs != null) {
            SemanticOp call = stdlibOpBy(abs.unit(), StdlibFunctionId.MATH_ABS_INT);
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(abs.unit(), abs.table());
                expectTerminal(abs, run, "E8004", "int out of safe range",
                    originAtomOf(call), expectedFrames(abs, call),
                    "absInt of -2147483648 projects E8004 at the call origin");
            }
            deleteRecursively(abs.tmp());
        }

        // (e) JSON_TO_ERROR: the first declaration-order failure through
        // the wiring (two function members; 'f' wins).
        Scenario stringify = lowerScenario("""
            import * as json from "std/json"

            function f(): null {
              return null
            }

            function g(): null {
              return null
            }

            function main(): null {
              f()
              g()
              let t: table = {f: f, g: g}
              let s: string = json.stringify(t)
              return null
            }
            """, "the stringify first-failure scenario");
        if (stringify != null) {
            SemanticOp call = stdlibOpBy(stringify.unit(),
                StdlibFunctionId.JSON_STRINGIFY);
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(stringify.unit(), stringify.table());
                expectTerminal(stringify, run, "E8001",
                    "unsupported type for JSON encoding: function",
                    originAtomOf(call), expectedFrames(stringify, call),
                    SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "function",
                    "the first declaration-order stringify failure projects "
                        + "JSON_TO_ERROR at the call origin");
            }
            deleteRecursively(stringify.tmp());
        }

        // (f) Console success through the wiring (the D5 effect path).
        Scenario console = lowerScenario("""
            import * as console from "std/console"

            function main(): null {
              console.log("ok")
              return null
            }
            """, "the console-wiring scenario");
        if (console != null) {
            SemanticRuntimeModel.ConsumerRun run =
                SemanticOracle.execute(console.unit(), console.table());
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    && run.effects().size() == 1
                    && run.effects().get(0).kind()
                        == SemanticRuntimeModel.EffectEvent.Kind.CONSOLE_WRITE
                    && run.effects().get(0).text().equals("ok"),
                "console.log through the wiring records exactly one ordered effect "
                    + "with the exact scalar text and succeeds with null: "
                    + run.comparisonReport());
            deleteRecursively(console.tmp());
        }

        // (g) The invalid-scalar precedence at the executor level: the
        // STDLIB_PARAMETER boundary rejects the invalid encoding first
        // (E8001 expected string, got invalid Unicode scalar encoding)
        // and the algorithm never runs on an invalid carrier.
        Scenario invalid = lowerScenario("""
            import * as str from "std/string"

            function main(): null {
              let n: int = str.length("abc")
              return null
            }
            """, "the invalid-scalar-precedence scenario");
        if (invalid != null) {
            SemanticOp call = stdlibOpBy(invalid.unit(),
                StdlibFunctionId.STRING_LENGTH);
            List<SemanticOp> parameters =
                stdlibBoundariesOf(invalid.unit(), call, BoundaryKind.STDLIB_PARAMETER);
            check(call != null && parameters.size() == 1,
                "the scenario lowers one STRING_LENGTH call with one parameter "
                    + "boundary");
            if (call != null && parameters.size() == 1) {
                SemanticOp boundary = parameters.get(0);
                KindPayload.BoundaryPayload payload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                BoundaryOutcome outcome = BoundaryExecutor.execute(
                    boundary.failurePolicy(), payload.descriptor(),
                    BoundaryValueView.of(ActualKind.INVALID_UNICODE),
                    BoundaryContext.parameter(1), payload.realization());
                boolean rejected = outcome instanceof BoundaryOutcome.Fail failOutcome
                    && failOutcome.failure().code() == DiagnosticCode.E8001
                    && failOutcome.failure().message().equals(
                        "expected string, got invalid Unicode scalar encoding");
                check(rejected,
                    "the STDLIB_PARAMETER boundary rejects an invalid scalar encoding "
                        + "with the exact invalid-string E8001 before any algorithm");
                boolean defect = false;
                try {
                    SharedStdlibSemantics.execute(call,
                        List.of(Value.string(UnicodeScalars.Invalid.INSTANCE)), null);
                } catch (SharedStdlibSemantics.Defect expected) {
                    defect = true;
                }
                check(defect,
                    "the algorithm never runs on an invalid carrier; the primitive "
                        + "fails closed because the boundary rejects it first");
            }
            deleteRecursively(invalid.tmp());
        }
    }

    // =========================================================================
    // 4. Boundary realizations carried by active stdlib Semantic IR
    // =========================================================================

    static void testBoundaryRealizationPayloads() {
        System.out.println("-- Boundary realization payloads: one RuntimeValidation per "
            + "stdlib boundary --");

        Scenario scenario = lowerScenario("""
            import * as str from "std/string"
            import * as json from "std/json"

            function main(): null {
              let n: int = str.length("abc")
              let t: table = json.parse("{\\"a\\": 1}")
              return null
            }
            """, "the realization-payload scenario");
        if (scenario == null) {
            return;
        }
        LoweredModuleUnit unit = scenario.unit();
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
            factsOf(scenario.checked()));
        check(validation.isEmpty(),
            "the active stdlib Semantic IR validates before payload inspection"
                + validation.map(d -> ": " + d.message()).orElse(""));

        int stdlibBoundaries = 0;
        Set<OpId> boundaryIds = new java.util.LinkedHashSet<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.BOUNDARY) {
                continue;
            }
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) op.payload();
            check(boundaryIds.add(op.opId()),
                "each boundary realization is carried by one unique IR op " + op.opId());
            if (payload.kind() == BoundaryKind.STDLIB_PARAMETER
                    || payload.kind() == BoundaryKind.STDLIB_RETURN) {
                stdlibBoundaries++;
                check(payload.realization()
                            instanceof BoundaryRealization.RuntimeValidation runtime
                        && runtime.checkId().equals(
                            SemanticLowerer.CANONICAL_RUNTIME_VALIDATION_ID),
                    "stdlib boundary " + payload.kind()
                        + " carries RuntimeValidation("
                        + SemanticLowerer.CANONICAL_RUNTIME_VALIDATION_ID + ")");
                FailurePolicyId expectedPolicy =
                    payload.descriptor() instanceof RuntimeDescriptor.Func
                        ? FailurePolicyId.FUNCTION_SIGNATURE
                        : FailurePolicyId.TYPE_DESCRIPTOR;
                check(op.failurePolicy() == expectedPolicy,
                    "stdlib boundary " + payload.kind()
                        + " equals the closed descriptor-kind policy row");
            }
        }
        check(stdlibBoundaries == 4,
            "the scenario unit carries 4 stdlib boundaries, one parameter + one "
                + "return per call; got " + stdlibBoundaries);
        deleteRecursively(scenario.tmp());
    }

    // =========================================================================
    // 5. Validator negative: a stdlib boundary policy outside the
    //    descriptor-kind rule is invalid IR
    // =========================================================================

    /** One raw op with its failurePolicy replaced (op + snapshot, digest
     *  recomputed) — the closed text-surface modification seam. */
    private static RawOp withPolicy(RawOp op, String policyName) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.snapshot().entries()) {
            if (entry.key().equals(ContractSnapshotCanonicalizer.FIELD_FAILURE_POLICY)) {
                entries.add(CanonicalJson.e(
                    ContractSnapshotCanonicalizer.FIELD_FAILURE_POLICY,
                    CanonicalJson.str(policyName)));
            } else {
                entries.add(entry);
            }
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(entries);
        String digest = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(snapshot);
        return new RawOp(op.opId(), op.kind(), policyName, op.parentOpId(),
            op.resultValue(), op.resultToken(), op.resultType(), op.operands(),
            op.operandTypes(), op.payload(), op.selector(), digest, snapshot);
    }

    /** The validated-lowering facts of the checked project (R-PROFILE). */
    private static SemanticIrValidator.ComparisonFacts factsOf(
            CheckedProjectBuildResult checked) {
        return new SemanticIrValidator.ComparisonFacts(
            checked.index().interfaceIndexDigest(), SemanticProfile.DEAL_V1_2_INT32,
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash());
    }

    static void testValidatorStdlibCellNegative() {
        System.out.println("-- Validator: a stdlib boundary policy outside the "
            + "descriptor-kind rule fails --");

        Scenario scenario = lowerScenario("""
            import * as str from "std/string"

            function main(): null {
              let n: int = str.length("abc")
              return null
            }
            """, "the validator-negative scenario");
        if (scenario == null) {
            return;
        }
        SemanticOp call = stdlibOpBy(scenario.unit(),
            StdlibFunctionId.STRING_LENGTH);
        List<SemanticOp> parameters =
            stdlibBoundariesOf(scenario.unit(), call, BoundaryKind.STDLIB_PARAMETER);
        check(call != null && parameters.size() == 1,
            "the scenario lowers one STRING_LENGTH call with one parameter "
                + "boundary");
        if (call == null || parameters.size() != 1) {
            deleteRecursively(scenario.tmp());
            return;
        }
        SemanticOp parameter = parameters.get(0);
        SemanticIrValidator.ComparisonFacts facts = factsOf(scenario.checked());

        // Positive control: the untouched unit passes both surfaces.
        Optional<CompilerDiagnostic> untouched =
            SemanticIrValidator.validate(scenario.unit(), facts);
        check(untouched.isEmpty(),
            "the untouched unit passes the closed validator"
                + (untouched.isPresent() ? ": " + untouched.get().message() : ""));

        // Hand-modified raw unit: the STDLIB_PARAMETER boundary's policy
        // is replaced by NO_DEAL_FAILURE (outside the descriptor-kind
        // rule) — the only defect is the boundary's policy.
        RawUnit raw = RawUnit.fromTyped(scenario.unit());
        List<RawOp> modified = new ArrayList<>();
        for (RawOp op : raw.ops()) {
            if (op.opId().equals(parameter.opId())) {
                modified.add(withPolicy(op, FailurePolicyId.NO_DEAL_FAILURE.name()));
            } else {
                modified.add(op);
            }
        }
        RawUnit modifiedUnit = new RawUnit(raw.modulePath(), raw.semanticProfile(),
            raw.interfaceHash(), raw.loweringContextHash(), raw.requiredCapabilities(),
            raw.coverage(), raw.bindings(), modified);
        Optional<CompilerDiagnostic> wrongPolicy = SemanticIrValidator.validateText(
            ContractSnapshotCanonicalizer.serializeText(
                ContractSnapshotCanonicalizer.toJson(modifiedUnit)), facts);
        check(wrongPolicy.isPresent()
                && wrongPolicy.get().message().contains("descriptor-kind rule"),
            "a stdlib boundary policy outside the descriptor-kind rule fails "
                + "validation, the closed stdlibCell: "
                + wrongPolicy.map(CompilerDiagnostic::message).orElse("none"));

        // The same modification on the STDLIB_RETURN boundary also fails.
        List<SemanticOp> returns =
            stdlibBoundariesOf(scenario.unit(), call, BoundaryKind.STDLIB_RETURN);
        if (returns.size() == 1) {
            List<RawOp> returnModified = new ArrayList<>();
            for (RawOp op : raw.ops()) {
                if (op.opId().equals(returns.get(0).opId())) {
                    returnModified.add(withPolicy(op,
                        FailurePolicyId.NO_DEAL_FAILURE.name()));
                } else {
                    returnModified.add(op);
                }
            }
            RawUnit returnUnit = new RawUnit(raw.modulePath(), raw.semanticProfile(),
                raw.interfaceHash(), raw.loweringContextHash(),
                raw.requiredCapabilities(), raw.coverage(), raw.bindings(),
                returnModified);
            Optional<CompilerDiagnostic> wrongReturn = SemanticIrValidator.validateText(
                ContractSnapshotCanonicalizer.serializeText(
                    ContractSnapshotCanonicalizer.toJson(returnUnit)), facts);
            check(wrongReturn.isPresent()
                    && wrongReturn.get().message().contains("descriptor-kind rule"),
                "a STDLIB_RETURN policy outside the descriptor-kind rule fails "
                    + "validation too: "
                    + wrongReturn.map(CompilerDiagnostic::message).orElse("none"));
        }

        deleteRecursively(scenario.tmp());
    }

    // =========================================================================
    // 6. Combined T3: the resolved records derive from the registry rows
    // =========================================================================

    static void testCombinedT3() {
        System.out.println("-- Combined T3: the wiring's records are the registry rows' --");

        // The same defect re-instantiated through the registry row must
        // equal the wiring's terminal message byte-for-byte: a broken
        // algorithm (wrong offset, wrong reason, wrong first-failure
        // ordering) changes the record and fails the equality.
        FailurePolicyRow parseRow = FailureContractRegistry.row(
            FailurePolicyId.JSON_PARSE_SYNTAX);
        for (Object[] defect : List.<Object[]>of(
                new Object[] {JSON_BAD_X, "1",
                    SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER},
                new Object[] {JSON_BAD_ESCAPE, "4",
                    SharedStdlibSemantics.REASON_INVALID_ESCAPE},
                new Object[] {JSON_UNTERMINATED, "5",
                    SharedStdlibSemantics.REASON_UNTERMINATED_STRING},
                new Object[] {JSON_TRAILING, "3",
                    SharedStdlibSemantics.REASON_TRAILING_CONTENT})) {
            String input = (String) defect[0];
            String offset = (String) defect[1];
            String reason = (String) defect[2];
            String expected = BoundaryFailure.fromRow(parseRow, 0, null, null,
                Map.of("oneBasedByteOffset", offset, "reason", reason), null).message();
            Outcome<Value> outcome = SharedStdlibSemantics.jsonParse(origin(),
                valid(input));
            boolean matches = outcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().message().equals(expected)
                && failure.failure().failure().metadata().equals(
                    Map.of("oneBasedByteOffset", offset, "reason", reason))
                && failure.failure().origin().equals(origin());
            check(matches,
                "parse defect " + input + " resolves to the registry row's exact "
                    + "record, message " + q() + expected + q());
        }
        FailurePolicyRow toErrorRow = FailureContractRegistry.row(
            FailurePolicyId.JSON_TO_ERROR);
        SemanticTable<Value> firstOrder = new SemanticTable<>();
        firstOrder.put("a", new Value.Other(ActualKind.FUNCTION, null));
        firstOrder.put("b", new Value.Other(ActualKind.MISSING, null));
        String toErrorExpected = BoundaryFailure.fromRow(toErrorRow, 1,
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "function",
            Map.of("fieldPath", "a", "actual", "function"), null).message();
        Outcome<Value> toErrorOutcome =
            SharedStdlibSemantics.jsonStringify(origin(), firstOrder);
        boolean firstWins = toErrorOutcome instanceof Outcome.Failure<Value> failure
            && failure.failure().failure().message().equals(toErrorExpected)
            && SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED.equals(
                failure.failure().failure().expected())
            && "function".equals(failure.failure().failure().actual())
            && failure.failure().failure().metadata().equals(
                Map.of("fieldPath", "a", "actual", "function"));
        check(firstWins,
            "the first declaration-order stringify failure wins and equals the "
                + "registry record; a wrong ordering would change the record");
    }

    // =========================================================================

    public static void main(String[] args) {
        System.out.println("StdlibFailureProjectionTest ISSUE-0496: stdlib failure "
            + "projections and boundary realization reporting");
        testRegistryRows();
        testPrimitiveProjections();
        testOracleWiringPrecedence();
        testBoundaryRealizationPayloads();
        testValidatorStdlibCellNegative();
        testCombinedT3();
        System.out.println();
        System.out.println("StdlibFailureProjectionTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
