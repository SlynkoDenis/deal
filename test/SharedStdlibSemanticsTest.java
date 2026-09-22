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
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.SharedStdlibSemantics.ConsoleSink;
import deal.semantic.SharedStdlibSemantics.Outcome;
import deal.semantic.SharedStdlibSemantics.Value;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.UnicodeScalars;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

/**
 * The ISSUE-0495 {@code SharedStdlibSemantics} battery: the single
 * stdlib algorithm executor — the 20-id family batteries with every
 * named edge case, the exact failure projections, the console
 * operation-level effect contract, the boundary-precedence and
 * anti-hollow controls, and the combined T2/T1 drive (the landed
 * {@code STDLIB_CALL} lowering battery over the T1 catalog, each
 * produced op executed through {@link SharedStdlibSemantics} on
 * declared-descriptor inputs whose parameters passed the produced
 * {@code STDLIB_PARAMETER} boundaries via the landed
 * {@link BoundaryExecutor}).
 *
 * <p>Tests:
 * <ol>
 *   <li>String family: length (scalar count incl. surrogate pairs),
 *       substring clamping, contains/starts-with/ends-with incl. empty
 *       parts, replace (non-overlapping, empty-{@code from}, literal
 *       replacement), split (empty input/separator, preserved
 *       leading/internal/trailing empties), trim (exactly U+0009–U+000D
 *       and U+0020; U+000B/U+000C trimmed, U+00A0 preserved).</li>
 *   <li>Table keys: first-insertion order; delete removes the slot and
 *       reinsertion appends to the end; overwrite keeps the position.</li>
 *   <li>JSON parse: RFC-8259 values, text object order, duplicate keys
 *       (last value, first position), the signed32 lexical-form mapping
 *       ({@code 2147483647}/{@code -2147483648} → int,
 *       {@code 2147483648}/{@code -2147483649} → number, {@code -0} → 0,
 *       {@code 1.0}/{@code 1e3} → number, {@code -0.0} → number), RFC
 *       escaping incl. surrogate pairs, and every named syntax-defect
 *       class with the exact {@code JSON_PARSE_SYNTAX} template,
 *       metadata, and origin (multi-byte offsets included).</li>
 *   <li>JSON stringify: insertion/index order, RFC-8259 escaping
 *       (quote, backslash, control characters, surrogate pairs),
 *       shortest round-trippable decimals, and the first
 *       declaration-order {@code JSON_TO_ERROR} failure
 *       ({@code {fieldPath}}/{@code {actual}}) incl. cycles and
 *       nonfinite numbers.</li>
 *   <li>Math: IEEE floor/ceil/sqrt (NaN → NaN; {@code -0.0} → -0.0),
 *       {@code SQRT_NEGATIVE} carrying the negative operand,
 *       {@code absInt(-2147483648)} → E8004 at the call origin,
 *       {@code absNumber(-0.0)} → +0.0, min/max equal-operand returns.</li>
 *   <li>Console: capture sinks on both channels assert the exact scalar
 *       UTF-8 bytes plus one ordered {@code \n}, one effect per call,
 *       the null result, and channel identity; a failing sink propagates
 *       as infrastructure (run abort, no DEAL error).</li>
 *   <li>Boundary precedence: the landed {@code BoundaryExecutor} rejects
 *       an invalid scalar encoding at the {@code STDLIB_PARAMETER}
 *       position (exact E8001 {@code expected string, got invalid
 *       Unicode scalar encoding}) before any algorithm runs; the
 *       primitive fails closed (defect) on an invalid carrier.</li>
 *   <li>Combined T2/T1: the 20-id lowered battery's produced
 *       {@code STDLIB_CALL} ops are stamped correctly (id, declared
 *       descriptors, single-source policy) and each executes through
 *       {@link SharedStdlibSemantics} to the parent-table outcome
 *       (fails if the catalog misses/adds an entry, if the lowerer
 *       misstamps, or if the primitive returns a wrong result).</li>
 *   <li>Fail-closed defects: wrong op kind, wrong argument count, wrong
 *       carriers, wrong-channel/absent sinks, and the boundary
 *       admission sets (number parameter admits an int carrier; int
 *       parameter admits an integral number carrier) fail closed.</li>
 * </ol>
 */
public class SharedStdlibSemanticsTest {

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

    // =========================================================================
    // Shared fixtures
    // =========================================================================

    /** The synthetic operation origin of the per-family drives. */
    private static SourceOrigin origin() {
        return new SourceOrigin("stdlib-test", SourceSpan.synthetic("stdlib-test"),
            deal.semantic.ir.SourceOriginKind.SYNTHETIC, new AnchorId(1), null);
    }

    /** Deep structural equality over the closed value view (numbers via {@code Double.compare}). */
    private static boolean valueEquals(Value a, Value b) {
        if (a == b) {
            return true;
        }
        if (a.getClass() != b.getClass()) {
            return false;
        }
        return switch (a) {
            case Value.Null ignored -> true;
            case Value.Bool bool -> bool.value() == ((Value.Bool) b).value();
            case Value.Int intValue -> intValue.value() == ((Value.Int) b).value();
            case Value.Number number ->
                Double.compare(number.value(), ((Value.Number) b).value()) == 0;
            case Value.String string -> {
                UnicodeScalars.ScalarString left = string.scalar();
                UnicodeScalars.ScalarString right = ((Value.String) b).scalar();
                yield left instanceof UnicodeScalars.Invalid
                    ? right instanceof UnicodeScalars.Invalid
                    : right instanceof UnicodeScalars.Valid valid
                        && ((UnicodeScalars.Valid) left).carrier().equals(valid.carrier());
            }
            case Value.Table table -> {
                SemanticTable<Value> left = table.table();
                SemanticTable<Value> right = ((Value.Table) b).table();
                if (!left.keys().equals(right.keys())) {
                    yield false;
                }
                boolean equal = true;
                for (String key : left.keys()) {
                    SemanticTable.Lookup<Value> leftLookup = left.get(key);
                    SemanticTable.Lookup<Value> rightLookup = right.get(key);
                    if (!(leftLookup instanceof SemanticTable.Lookup.Present<Value> leftPresent)
                            || !(rightLookup
                                instanceof SemanticTable.Lookup.Present<Value> rightPresent)
                            || !valueEquals(leftPresent.value(), rightPresent.value())) {
                        equal = false;
                        break;
                    }
                }
                yield equal;
            }
            case Value.Array array -> {
                SemanticArray<Value> left = array.elements();
                SemanticArray<Value> right = ((Value.Array) b).elements();
                if (left.size() != right.size()) {
                    yield false;
                }
                boolean equal = true;
                for (int i = 0; i < left.size(); i++) {
                    if (!valueEquals(left.elementAt(i), right.elementAt(i))) {
                        equal = false;
                        break;
                    }
                }
                yield equal;
            }
            case Value.Other other -> other.kind() == ((Value.Other) b).kind()
                && Objects.equals(other.classId(), ((Value.Other) b).classId());
        };
    }

    /** Asserts one sealed success outcome with the exact expected value. */
    private static void expectSuccess(Outcome<Value> outcome, Value expected, String note) {
        if (outcome instanceof Outcome.Success<Value> success
                && valueEquals(success.value(), expected)) {
            passed++;
            return;
        }
        failed++;
        System.err.println("FAIL: " + note + " — expected Success with " + expected
            + ", got " + describe(outcome));
    }

    /** Asserts one sealed failure outcome with the exact registry-row projection. */
    private static void expectFailure(Outcome<Value> outcome, FailurePolicyId policy,
                                      DiagnosticCode code, String message, String expectedText,
                                      String actualText, Map<String, String> metadata,
                                      SourceOrigin origin, String note) {
        if (outcome instanceof Outcome.Failure<Value> failure) {
            SharedStdlibSemantics.StdlibFailure stdlibFailure = failure.failure();
            BoundaryFailure projection = stdlibFailure.failure();
            boolean ok = projection.policy() == policy
                && projection.code() == code
                && projection.message().equals(message)
                && Objects.equals(projection.expected(), expectedText)
                && Objects.equals(projection.actual(), actualText)
                && projection.metadata().equals(metadata)
                && projection.cause() == null
                && stdlibFailure.origin().equals(origin);
            if (ok) {
                passed++;
                return;
            }
            failed++;
            System.err.println("FAIL: " + note + " — projection mismatch: policy="
                + projection.policy() + " code=" + projection.code() + " message=\""
                + projection.message() + "\" expected=" + projection.expected()
                + " actual=" + projection.actual() + " metadata=" + projection.metadata()
                + " origin=" + stdlibFailure.origin());
            return;
        }
        failed++;
        System.err.println("FAIL: " + note + " — expected Failure, got " + describe(outcome));
    }

    /** Asserts a fail-closed producer defect of the expected type/marker. */
    private static void expectDefect(Runnable action, Class<? extends Throwable> type,
                                     String marker, String note) {
        try {
            action.run();
            failed++;
            System.err.println("FAIL: " + note + " — expected a " + type.getSimpleName()
                + " defect containing \"" + marker + "\", but nothing was thrown");
        } catch (Throwable thrown) {
            if (type.isInstance(thrown) && thrown.getMessage() != null
                    && thrown.getMessage().contains(marker)) {
                passed++;
            } else {
                failed++;
                System.err.println("FAIL: " + note + " — expected a "
                    + type.getSimpleName() + " containing \"" + marker + "\", got " + thrown);
            }
        }
    }

    private static String describe(Outcome<Value> outcome) {
        if (outcome instanceof Outcome.Success<Value> success) {
            return "Success(" + success.value() + ")";
        }
        if (outcome instanceof Outcome.Failure<Value> failure) {
            return "Failure(" + failure.failure().failure().message() + ")";
        }
        return String.valueOf(outcome);
    }

    /** A valid scalar carrier of the given text. */
    private static UnicodeScalars.Valid valid(String text) {
        return new UnicodeScalars.Valid(text);
    }

    /** A JSON text value (scalar-valid by construction). */
    private static Value text(String carrier) {
        return Value.string(carrier);
    }

    // =========================================================================
    // 1. String family
    // =========================================================================

    static void testStringLength() {
        System.out.println("-- STRING_LENGTH: Unicode scalar count as signed32 --");

        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("")),
            new Value.Int(0), "length of the empty string is 0");
        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("abc")),
            new Value.Int(3), "length of 'abc' is 3");
        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("h\u00e9llo")),
            new Value.Int(5), "length of 'h\u00e9llo' is 5 scalars (\u00e9 is one scalar)");
        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("\ud83d\ude00")),
            new Value.Int(1), "a surrogate pair is one scalar");
        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("a\ud83d\ude00b")),
            new Value.Int(3), "mixed BMP/supplementary count is scalar-exact");
        expectSuccess(SharedStdlibSemantics.stringLength(origin(), valid("a".repeat(4000))),
            new Value.Int(4000), "a long carrier counts every scalar");
    }

    static void testStringSubstring() {
        System.out.println("-- STRING_SUBSTRING: scalar indices with clamping --");

        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 1, 2),
            text("b"), "substring('abc',1,2) is 'b'");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 0, 3),
            text("abc"), "substring('abc',0,3) is 'abc'");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), -2, 2),
            text("ab"), "negative start clamps to lo=0");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 1, 99),
            text("bc"), "end beyond length clamps to hi=length");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), -5, -1),
            text(""), "lo=hi=0 is empty");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 2, 1),
            text(""), "lo>=hi is empty (start>end)");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 99, 100),
            text(""), "start beyond length is empty");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid("abc"), 3, 5),
            text(""), "start==length is empty");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(),
                valid("\ud83d\ude00\ud83d\ude00"), 1, 2),
            text("\ud83d\ude00"), "indices are scalar indices (pair = one scalar)");
        expectSuccess(SharedStdlibSemantics.stringSubstring(origin(), valid(""), 0, 1),
            text(""), "empty input is empty");
    }

    static void testStringContainsStartsEnds() {
        System.out.println("-- STRING_CONTAINS / STARTS_WITH / ENDS_WITH --");

        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid("abc"), valid("b")),
            new Value.Bool(true), "'abc' contains 'b'");
        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid("abc"), valid("")),
            new Value.Bool(true), "an empty part is contained");
        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid(""), valid("")),
            new Value.Bool(true), "an empty part is contained in the empty string");
        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid("abc"), valid("d")),
            new Value.Bool(false), "'abc' does not contain 'd'");
        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid("abc"), valid("abcd")),
            new Value.Bool(false), "a longer part is never contained");
        expectSuccess(SharedStdlibSemantics.stringContains(origin(), valid("a\ud83d\ude00b"),
                valid("\ud83d\ude00")),
            new Value.Bool(true), "a pair part is found as one scalar");

        expectSuccess(SharedStdlibSemantics.stringStartsWith(origin(), valid("abc"), valid("a")),
            new Value.Bool(true), "'abc' starts with 'a'");
        expectSuccess(SharedStdlibSemantics.stringStartsWith(origin(), valid("abc"), valid("")),
            new Value.Bool(true), "an empty part is a prefix");
        expectSuccess(SharedStdlibSemantics.stringStartsWith(origin(), valid("abc"), valid("d")),
            new Value.Bool(false), "'abc' does not start with 'd'");
        expectSuccess(SharedStdlibSemantics.stringStartsWith(origin(), valid("abc"), valid("abcd")),
            new Value.Bool(false), "a longer part is never a prefix");
        expectSuccess(SharedStdlibSemantics.stringStartsWith(origin(), valid("\ud83d\ude00b"),
                valid("\ud83d\ude00")),
            new Value.Bool(true), "a pair prefix matches as one scalar");

        expectSuccess(SharedStdlibSemantics.stringEndsWith(origin(), valid("abc"), valid("c")),
            new Value.Bool(true), "'abc' ends with 'c'");
        expectSuccess(SharedStdlibSemantics.stringEndsWith(origin(), valid("abc"), valid("")),
            new Value.Bool(true), "an empty part is a suffix");
        expectSuccess(SharedStdlibSemantics.stringEndsWith(origin(), valid("abc"), valid("d")),
            new Value.Bool(false), "'abc' does not end with 'd'");
        expectSuccess(SharedStdlibSemantics.stringEndsWith(origin(), valid("abc"), valid("abcd")),
            new Value.Bool(false), "a longer part is never a suffix");
        expectSuccess(SharedStdlibSemantics.stringEndsWith(origin(), valid("b\ud83d\ude00"),
                valid("\ud83d\ude00")),
            new Value.Bool(true), "a pair suffix matches as one scalar");
    }

    static void testStringReplace() {
        System.out.println("-- STRING_REPLACE: non-overlapping left-to-right, literal --");

        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("aba"), valid("a"),
                valid("z")),
            text("zbz"), "'aba' replace 'a' with 'z' is 'zbz'");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("abc"), valid("d"),
                valid("z")),
            text("abc"), "an absent from returns the input unchanged");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("abc"), valid(""),
                valid("z")),
            text("abc"), "an empty from returns the input unchanged");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("aaa"), valid("aa"),
                valid("b")),
            text("ba"), "occurrences are non-overlapping: 'aaa'/'aa' → 'ba'");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("aaaa"), valid("aa"),
                valid("b")),
            text("bb"), "non-overlapping left-to-right: 'aaaa'/'aa' → 'bb'");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("a.b"), valid("a.b"),
                valid("x")),
            text("x"), "the search is literal, never pattern-interpreted");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("100%"), valid("%"),
                valid("pct")),
            text("100pct"), "a magic-pattern character is literal");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("x"), valid("y"),
                valid("$0")),
            text("x"), "the replacement is literal, never pattern-interpreted");
        expectSuccess(SharedStdlibSemantics.stringReplace(origin(), valid("a\ud83d\ude00a"),
                valid("a"), valid("z")),
            text("z\ud83d\ude00z"), "scalar-domain replacement keeps the pair intact");
    }

    static void testStringSplit() {
        System.out.println("-- STRING_SPLIT: empty input/separator and preserved empties --");

        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid(""), valid(",")),
            Value.array(), "empty input → [] regardless of the separator");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid(""), valid("")),
            Value.array(), "empty input with an empty separator → []");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("abc"), valid("")),
            Value.array(text("a"), text("b"), text("c")),
            "empty separator → one single-scalar string per element");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(),
                valid("\ud83d\ude00b"), valid("")),
            Value.array(text("\ud83d\ude00"), text("b")),
            "empty separator splits by scalars (a pair is one element)");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("a,b"), valid(",")),
            Value.array(text("a"), text("b")), "'a,b' split ',' → ['a','b']");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid(",a"), valid(",")),
            Value.array(text(""), text("a")), "a leading empty part is preserved");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("a,"), valid(",")),
            Value.array(text("a"), text("")), "a trailing empty part is preserved");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("a,,b"), valid(",")),
            Value.array(text("a"), text(""), text("b")),
            "an internal empty part is preserved");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("abc"), valid("d")),
            Value.array(text("abc")), "an absent separator yields the input as one part");
        expectSuccess(SharedStdlibSemantics.stringSplit(origin(), valid("a::b"), valid("::")),
            Value.array(text("a"), text("b")), "a multi-scalar separator is literal");
    }

    static void testStringTrim() {
        System.out.println("-- STRING_TRIM: exactly U+0009-U+000D and U+0020 --");

        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("  x  ")),
            text("x"), "spaces are trimmed");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("")),
            text(""), "the empty string stays empty");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("   ")),
            text(""), "an all-whitespace string trims to empty");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("a b")),
            text("a b"), "interior characters are never removed");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("\u0009x\u0009")),
            text("x"), "U+0009 (tab) is trimmed");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("\rx")),
            text("x"), "U+000D (CR) is trimmed");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(),
                valid("\u000b\f x \u000b\f")),
            text("x"), "U+000B/U+000C (VT/FF) are trimmed — the closed set includes them");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(),
                valid("\t\r\n\u000b\fx\u000b\f\n\r\t")),
            text("x"), "the full closed set trims from both ends");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("\u00a0x\u00a0")),
            text("\u00a0x\u00a0"), "U+00A0 (NBSP) is not in the set and stays");
        expectSuccess(SharedStdlibSemantics.stringTrim(origin(), valid("x\u00a0")),
            text("x\u00a0"), "a trailing NBSP is preserved");
    }

    // =========================================================================
    // 2. Table keys
    // =========================================================================

    static void testTableKeys() {
        System.out.println("-- TABLE_KEYS: first-insertion order; delete+reinsert appends --");

        SemanticTable<Value> table = new SemanticTable<>();
        table.put("a", new Value.Int(1));
        table.put("b", new Value.Int(2));
        table.put("c", new Value.Int(3));
        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), table),
            Value.array(text("a"), text("b"), text("c")),
            "keys come out in first-insertion order");

        table.put("a", new Value.Int(9));
        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), table),
            Value.array(text("a"), text("b"), text("c")),
            "overwriting an existing key keeps its position");

        table.remove("b");
        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), table),
            Value.array(text("a"), text("c")), "delete removes the order slot");

        table.put("b", new Value.Int(4));
        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), table),
            Value.array(text("a"), text("c"), text("b")),
            "delete+reinsert moves the key to the end");

        table.remove("absent");
        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), table),
            Value.array(text("a"), text("c"), text("b")),
            "removing an absent key is a no-op");

        expectSuccess(SharedStdlibSemantics.tableKeys(origin(), new SemanticTable<>()),
            Value.array(), "the empty table yields an empty array");
    }

    // =========================================================================
    // 3. JSON parse
    // =========================================================================

    private static void expectParseValue(String json, Value expected, String note) {
        expectSuccess(SharedStdlibSemantics.jsonParse(origin(), valid(json)), expected, note);
    }

    private static void expectParseFailure(String json, long oneBasedByteOffset, String reason,
                                           String note) {
        expectFailure(SharedStdlibSemantics.jsonParse(origin(), valid(json)),
            FailurePolicyId.JSON_PARSE_SYNTAX, DiagnosticCode.E8001,
            "JSON parse error at position " + oneBasedByteOffset + ": " + reason,
            null, null,
            Map.of("oneBasedByteOffset", Long.toString(oneBasedByteOffset), "reason", reason),
            origin(), note);
    }

    static void testJsonParseValues() {
        System.out.println("-- JSON_PARSE: RFC-8259 values, order, duplicates, number mapping --");

        expectParseValue("null", Value.Null.INSTANCE, "null parses to language null");
        expectParseValue("true", new Value.Bool(true), "true parses to a boolean");
        expectParseValue("false", new Value.Bool(false), "false parses to a boolean");
        expectParseValue("\"hi\"", text("hi"), "a string parses to its scalar text");
        expectParseValue("\"\"", text(""), "the empty JSON string parses");

        expectParseValue("{}", new Value.Table(new SemanticTable<>()),
            "{} parses to an empty table");
        expectParseValue("[]", Value.array(), "[] parses to an empty array");
        expectParseValue("[1, 2, 3]",
            Value.array(new Value.Int(1), new Value.Int(2), new Value.Int(3)),
            "an array keeps index order");
        expectParseValue("[null, true, \"x\", 1.5]",
            Value.array(Value.Null.INSTANCE, new Value.Bool(true), text("x"),
                new Value.Number(1.5)),
            "mixed arrays parse in order");

        // Object order follows text.
        SemanticTable<Value> ordered = new SemanticTable<>();
        ordered.put("b", new Value.Int(2));
        ordered.put("a", new Value.Int(1));
        expectParseValue("{\"b\": 2, \"a\": 1}", new Value.Table(ordered),
            "object order follows the text order");

        // Duplicate keys keep the last value and the first position.
        SemanticTable<Value> duplicate = new SemanticTable<>();
        duplicate.put("a", new Value.Int(3));
        duplicate.put("b", new Value.Int(2));
        expectParseValue("{\"a\": 1, \"b\": 2, \"a\": 3}", new Value.Table(duplicate),
            "duplicate keys keep the last value and the first position");

        // Nested structures.
        SemanticTable<Value> nestedInner = new SemanticTable<>();
        nestedInner.put("b", Value.array(new Value.Int(1), new Value.Int(2)));
        SemanticTable<Value> nested = new SemanticTable<>();
        nested.put("a", new Value.Table(nestedInner));
        expectParseValue("{\"a\": {\"b\": [1, 2]}}", new Value.Table(nested),
            "nested objects/arrays parse recursively");

        // Whitespace: space, tab, CR, LF.
        SemanticTable<Value> whitespaceTable = new SemanticTable<>();
        whitespaceTable.put("a", new Value.Int(1));
        expectParseValue(" \t\r\n { \"a\" : 1 } \t ", new Value.Table(whitespaceTable),
            "RFC-8259 whitespace is skipped outside strings");

        // String escapes: the RFC-8259 escape set.
        expectParseValue("\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"",
            text("\"\\/\b\f\n\r\t"), "the RFC-8259 escape set decodes");
        expectParseValue("\"\\u0041\"", text("A"), "\\uXXXX decodes a BMP scalar");
        expectParseValue("\"\\u00e9\"", text("\u00e9"), "\\uXXXX decodes \u00e9");
        expectParseValue("\"\\ud83d\\ude00\"", text("\ud83d\ude00"),
            "a surrogate-pair escape combines to one supplementary scalar");
        expectParseValue("\"a\\ud83d\\ude00b\"", text("a\ud83d\ude00b"),
            "a pair escape inside text is one scalar");

        // Signed32 integer lexical forms → Int; everything else → Number.
        expectParseValue("0", new Value.Int(0), "0 → int 0");
        expectParseValue("-0", new Value.Int(0), "-0 normalizes to int 0");
        expectParseValue("42", new Value.Int(42), "42 → int");
        expectParseValue("2147483647", new Value.Int(2147483647), "2147483647 → int");
        expectParseValue("2147483648", new Value.Number(2147483648d), "2147483648 → number");
        expectParseValue("-2147483648", new Value.Int(-2147483648), "-2147483648 → int");
        expectParseValue("-2147483649", new Value.Number(-2147483649d), "-2147483649 → number");
        expectParseValue("1.0", new Value.Number(1.0), "1.0 → number (fraction form)");
        expectParseValue("1e3", new Value.Number(1000.0), "1e3 → number (exponent form)");
        expectParseValue("-1.5e-2", new Value.Number(-0.015), "-1.5e-2 → number");
        expectParseValue("3E2", new Value.Number(300.0), "uppercase E exponent → number");
        expectParseValue("0.5", new Value.Number(0.5), "a fraction with zero int part → number");
        expectParseValue("0e3", new Value.Number(0.0), "0e3 → number (exponent form)");
        expectParseValue("123456789012345678901234567890",
            new Value.Number(Double.parseDouble("123456789012345678901234567890")),
            "an out-of-range integer lexical form → number");

        // -0.0: a fraction form stays an IEEE number with its sign.
        Value parsedNegativeZero = ((Outcome.Success<Value>) SharedStdlibSemantics.jsonParse(
            origin(), valid("-0.0"))).value();
        check(parsedNegativeZero instanceof Value.Number
                && Double.doubleToLongBits(((Value.Number) parsedNegativeZero).value())
                    == Double.doubleToLongBits(-0.0),
            "-0.0 → number -0.0 (the IEEE value, not the int normalization)");

        // Round-trip: parse then stringify reproduces the RFC text.
        Outcome<Value> roundTripParse = SharedStdlibSemantics.jsonParse(origin(),
            valid("{\"a\": [1, 2.5, \"x\"], \"b\": true}"));
        check(roundTripParse instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Table table,
            "the round-trip fixture parses to a table");
        if (roundTripParse instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Table table) {
            Outcome<Value> roundTripStringify =
                SharedStdlibSemantics.jsonStringify(origin(), table.table());
            expectSuccess(roundTripStringify, text("{\"a\":[1,2.5,\"x\"],\"b\":true}"),
                "parse→stringify round-trips the JSON text");
        }
    }

    static void testJsonParseSyntaxFailures() {
        System.out.println("-- JSON_PARSE: every named syntax defect with exact projection --");

        expectParseFailure("", 1, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "empty input");
        expectParseFailure("   ", 4, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "whitespace-only input");
        expectParseFailure(" x", 2, SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
            "an unexpected value-start character at its byte offset");
        expectParseFailure("+1", 1, SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
            "a leading + can never start a value");
        expectParseFailure("{", 2, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "an unclosed object at end of input expects a member (unexpected end)");
        expectParseFailure("{\"a\":1", 7, SharedStdlibSemantics.REASON_UNTERMINATED_OBJECT,
            "EOF after a complete member is an unterminated object");
        expectParseFailure("[1", 3, SharedStdlibSemantics.REASON_UNTERMINATED_ARRAY,
            "EOF after a complete element is an unterminated array");
        expectParseFailure("[1,", 4, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "EOF after a comma expects a value");
        expectParseFailure("{\"a\":", 6, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "EOF after a colon expects a value");
        expectParseFailure("\"abc", 5, SharedStdlibSemantics.REASON_UNTERMINATED_STRING,
            "an unclosed string at end of input");
        expectParseFailure("\"a\\q\"", 4, SharedStdlibSemantics.REASON_INVALID_ESCAPE,
            "an unknown escape character at its offset");
        expectParseFailure("\"\\u12g4\"", 6, SharedStdlibSemantics.REASON_INVALID_ESCAPE,
            "a non-hex \\u digit at its offset");
        expectParseFailure("\"\\u123\"", 7, SharedStdlibSemantics.REASON_INVALID_ESCAPE,
            "a truncated \\u escape at its non-hex digit");
        expectParseFailure("\"\\ud800\"", 8,
            SharedStdlibSemantics.REASON_UNPAIRED_SURROGATE_ESCAPE,
            "a high-surrogate escape without a pair");
        expectParseFailure("\"\\ud800x\"", 8,
            SharedStdlibSemantics.REASON_UNPAIRED_SURROGATE_ESCAPE,
            "a high-surrogate escape followed by a non-pair");
        expectParseFailure("\"\\udc00\"", 8,
            SharedStdlibSemantics.REASON_UNPAIRED_SURROGATE_ESCAPE,
            "a lone low-surrogate escape");
        expectParseFailure("\"x\n\"", 3, SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
            "a raw control character inside a string");
        expectParseFailure("01", 2, SharedStdlibSemantics.REASON_LEADING_ZERO,
            "a leading zero followed by a digit");
        expectParseFailure("-01", 3, SharedStdlibSemantics.REASON_LEADING_ZERO,
            "a negative leading zero at the following digit");
        expectParseFailure("1.", 3, SharedStdlibSemantics.REASON_INVALID_NUMBER,
            "a fraction with no digits");
        expectParseFailure("1e", 3, SharedStdlibSemantics.REASON_INVALID_NUMBER,
            "an exponent with no digits");
        expectParseFailure("1e+", 4, SharedStdlibSemantics.REASON_INVALID_NUMBER,
            "an exponent sign with no digits");
        expectParseFailure("-x", 2, SharedStdlibSemantics.REASON_INVALID_NUMBER,
            "a minus without digits");
        expectParseFailure("{1: 2}", 2, SharedStdlibSemantics.REASON_MISSING_KEY,
            "a member without a string key");
        expectParseFailure("{\"a\" 1}", 6, SharedStdlibSemantics.REASON_MISSING_COLON,
            "a key without a colon");
        expectParseFailure("{\"a\"", 5, SharedStdlibSemantics.REASON_MISSING_COLON,
            "a key then EOF is a missing colon");
        expectParseFailure("{\"a\":1 \"b\":2}", 8, SharedStdlibSemantics.REASON_MISSING_COMMA,
            "members without a comma");
        expectParseFailure("[1 2]", 4, SharedStdlibSemantics.REASON_MISSING_COMMA,
            "elements without a comma");
        expectParseFailure("{\"a\":1,}", 8, SharedStdlibSemantics.REASON_MISSING_KEY,
            "a trailing comma then a closer is a missing key");
        expectParseFailure("1 2", 3, SharedStdlibSemantics.REASON_TRAILING_CONTENT,
            "content after the top-level value");
        expectParseFailure("{}x", 3, SharedStdlibSemantics.REASON_TRAILING_CONTENT,
            "trailing content after an object");
        expectParseFailure("tru", 4, SharedStdlibSemantics.REASON_UNEXPECTED_END,
            "a truncated literal at end of input");
        expectParseFailure("nulX", 4, SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
            "a mismatched literal character");

        // Multi-byte offsets: the offset is a 1-based UTF-8 byte offset.
        expectParseFailure("\"\u00e9", 4, SharedStdlibSemantics.REASON_UNTERMINATED_STRING,
            "an unterminated string's offset counts the 2-byte \u00e9");
        expectParseFailure("{\"\u00e9\": 1}x", 10,
            SharedStdlibSemantics.REASON_TRAILING_CONTENT,
            "trailing content offset counts multi-byte scalars before it");

        // The JSON_PARSE_SYNTAX projection carries the exact template,
        // metadata, origin, and no cause (spot check on the structured
        // outcome).
        Outcome<Value> spot = SharedStdlibSemantics.jsonParse(origin(), valid("{,}"));
        expectFailure(spot, FailurePolicyId.JSON_PARSE_SYNTAX, DiagnosticCode.E8001,
            "JSON parse error at position 2: missing key", null, null,
            Map.of("oneBasedByteOffset", "2", "reason", "missing key"),
            origin(), "the JSON_PARSE_SYNTAX outcome carries {oneBasedByteOffset}/{reason}");
    }

    // =========================================================================
    // 4. JSON stringify
    // =========================================================================

    private static SemanticTable<Value> tableOf(Object... pairs) {
        SemanticTable<Value> table = new SemanticTable<>();
        for (int i = 0; i < pairs.length; i += 2) {
            table.put((String) pairs[i], (Value) pairs[i + 1]);
        }
        return table;
    }

    private static void expectStringify(SemanticTable<Value> table, String expected,
                                        String note) {
        expectSuccess(SharedStdlibSemantics.jsonStringify(origin(), table), text(expected),
            note);
    }

    private static void expectStringifyFailure(SemanticTable<Value> table, String fieldPath,
                                               String actual, String note) {
        expectFailure(SharedStdlibSemantics.jsonStringify(origin(), table),
            FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "unsupported type for JSON encoding: " + actual,
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, actual,
            Map.of("fieldPath", fieldPath, "actual", actual), origin(), note);
    }

    static void testJsonStringifyValues() {
        System.out.println("-- JSON_STRINGIFY: order, escaping, shortest round-trip decimals --");

        expectStringify(tableOf("n", Value.Null.INSTANCE), "{\"n\":null}",
            "language null stringifies as JSON null");
        expectStringify(tableOf("t", new Value.Bool(true), "f", new Value.Bool(false)),
            "{\"t\":true,\"f\":false}", "booleans stringify in insertion order");
        expectStringify(tableOf("i", new Value.Int(42), "n", new Value.Int(-7)),
            "{\"i\":42,\"n\":-7}", "ints stringify as decimal integers");
        expectStringify(tableOf("z", new Value.Int(0)), "{\"z\":0}", "int zero is 0");

        expectStringify(tableOf("n", new Value.Number(1.5)), "{\"n\":1.5}",
            "a finite number uses its shortest round-trippable decimal");
        expectStringify(tableOf("n", new Value.Number(1.0)), "{\"n\":1.0}",
            "1.0 keeps its fraction (shortest spelling)");
        expectStringify(tableOf("n", new Value.Number(100.0)), "{\"n\":100.0}",
            "100.0 keeps its fraction");
        expectStringify(tableOf("n", new Value.Number(0.1)), "{\"n\":0.1}",
            "0.1 is '0.1', never a longer expansion");
        expectStringify(tableOf("n", new Value.Number(1e-7)), "{\"n\":1.0E-7}",
            "a small magnitude uses the exponent spelling");
        expectStringify(tableOf("n", new Value.Number(9.007199254740992E15)),
            "{\"n\":9.007199254740992E15}",
            "2^53 keeps its exact shortest spelling");
        expectStringify(tableOf("n", new Value.Number(-0.0)), "{\"n\":-0.0}",
            "negative zero keeps its sign");

        // Object insertion order; arrays index order.
        SemanticTable<Value> ordered = tableOf("a", new Value.Int(1), "b", new Value.Int(2),
            "c", new Value.Int(3));
        expectStringify(ordered, "{\"a\":1,\"b\":2,\"c\":3}",
            "object fields follow first-insertion order");
        expectStringify(tableOf("xs", Value.array(new Value.Int(1), text("x"),
                Value.Null.INSTANCE)),
            "{\"xs\":[1,\"x\",null]}", "array elements follow index order");

        // Nested structures and empty containers.
        SemanticTable<Value> inner = new SemanticTable<>();
        inner.put("b", Value.array(new Value.Int(1), new Value.Int(2)));
        SemanticTable<Value> nested = new SemanticTable<>();
        nested.put("a", new Value.Table(inner));
        expectStringify(nested, "{\"a\":{\"b\":[1,2]}}", "nested objects/arrays stringify");
        expectStringify(new SemanticTable<>(), "{}", "the empty table is {}");
        expectStringify(tableOf("xs", Value.array()), "{\"xs\":[]}", "the empty array is []");

        // RFC-8259 escaping: quote, backslash, named controls, other
        // controls, and raw surrogate pairs.
        expectStringify(tableOf("s", text("a\"b\\c")), "{\"s\":\"a\\\"b\\\\c\"}",
            "quote and backslash are escaped");
        expectStringify(tableOf("s", text("d\ne\tf\bg\fh\ri")),
            "{\"s\":\"d\\ne\\tf\\bg\\fh\\ri\"}", "the named short escapes are used");
        expectStringify(tableOf("s", text("x\u0001y\u001fz")),
            "{\"s\":\"x\\u0001y\\u001fz\"}", "other control scalars use \\u00XX");
        expectStringify(tableOf("s", text("\ud83d\ude00")),
            "{\"s\":\"\ud83d\ude00\"}",
            "a surrogate pair is emitted raw (one supplementary scalar)");
        expectStringify(tableOf("k\u00e9y", text("v")), "{\"k\u00e9y\":\"v\"}",
            "a non-ASCII key emits its raw scalars");
    }

    static void testJsonStringifyFailures() {
        System.out.println("-- JSON_STRINGIFY: first declaration-order JSON_TO_ERROR --");

        expectStringifyFailure(tableOf("f", new Value.Other(ActualKind.FUNCTION, null)),
            "f", "function", "a function value fails with its actual kind");
        expectStringifyFailure(tableOf("m", new Value.Other(ActualKind.MISSING, null)),
            "m", "missing", "a missing value fails with actual 'missing'");
        expectStringifyFailure(tableOf("a",
                new Value.Other(ActualKind.ASYNC_OPERATION, null)),
            "a", "async-operation", "an async-operation handle fails");
        expectStringifyFailure(tableOf("c",
                new Value.Other(ActualKind.CLASS, "@src/app/Admin")),
            "c", "class:@src/app/Admin", "a class value fails with the canonical class token");
        expectStringifyFailure(tableOf("n", new Value.Number(Double.NaN)),
            "n", "number", "NaN fails with actual 'number'");
        expectStringifyFailure(tableOf("n", new Value.Number(Double.POSITIVE_INFINITY)),
            "n", "number", "+Infinity fails with actual 'number'");
        expectStringifyFailure(tableOf("n", new Value.Number(Double.NEGATIVE_INFINITY)),
            "n", "number", "-Infinity fails with actual 'number'");
        expectStringifyFailure(tableOf("s",
                Value.string(UnicodeScalars.Invalid.INSTANCE)),
            "s", "invalid-unicode", "an invalid scalar sequence fails");

        // First declaration-order failure wins.
        expectStringifyFailure(tableOf("a", new Value.Other(ActualKind.FUNCTION, null),
                "b", new Value.Other(ActualKind.MISSING, null)),
            "a", "function",
            "the first declaration-order failure wins (a before b)");
        expectStringifyFailure(tableOf("ok", new Value.Int(1),
                "a", new Value.Table(tableOf("b", new Value.Other(ActualKind.FUNCTION, null),
                    "c", new Value.Other(ActualKind.MISSING, null)))),
            "a.b", "function",
            "nested failures report the dot-separated field path in pre-order");
        expectStringifyFailure(tableOf("arr", Value.array(new Value.Int(1),
                new Value.Other(ActualKind.FUNCTION, null))),
            "arr.1", "function", "array elements append the 0-based index");
        expectStringifyFailure(tableOf("arr", Value.array(new Value.Number(Double.NaN))),
            "arr.0", "number", "a nonfinite element reports its index path");

        // A cycle fails at the repeated container's path.
        SemanticTable<Value> self = new SemanticTable<>();
        self.put("self", new Value.Table(self));
        expectStringifyFailure(self, "self", "table",
            "a table cycle fails at the repeated table's path");
        SemanticTable<Value> root = new SemanticTable<>();
        SemanticTable<Value> child = new SemanticTable<>();
        child.put("up", new Value.Table(root));
        root.put("a", new Value.Table(child));
        expectStringifyFailure(root, "a.up", "table",
            "an indirect cycle reports the path of the repetition");

        // Acyclic finite data never fails: a deep but finite shape passes.
        SemanticTable<Value> deep = new SemanticTable<>();
        SemanticTable<Value> cursor = deep;
        for (int i = 0; i < 200; i++) {
            SemanticTable<Value> next = new SemanticTable<>();
            cursor.put("d", new Value.Table(next));
            cursor = next;
        }
        cursor.put("leaf", new Value.Int(1));
        Outcome<Value> deepOutcome = SharedStdlibSemantics.jsonStringify(origin(), deep);
        check(deepOutcome instanceof Outcome.Success<Value>,
            "a finite 200-deep shape stringifies without failure");
    }

    // =========================================================================
    // 5. Math
    // =========================================================================

    static void testMath() {
        System.out.println("-- Math: IEEE floor/ceil/sqrt/abs and signed32 min/max --");

        expectSuccess(SharedStdlibSemantics.mathFloor(origin(), 1.5),
            new Value.Number(1.0), "floor(1.5) = 1.0");
        expectSuccess(SharedStdlibSemantics.mathFloor(origin(), -1.5),
            new Value.Number(-2.0), "floor(-1.5) = -2.0");
        expectSuccess(SharedStdlibSemantics.mathFloor(origin(), 2.0),
            new Value.Number(2.0), "floor of an integral number is itself");
        expectSuccess(SharedStdlibSemantics.mathCeil(origin(), 1.5),
            new Value.Number(2.0), "ceil(1.5) = 2.0");
        expectSuccess(SharedStdlibSemantics.mathCeil(origin(), -1.5),
            new Value.Number(-1.0), "ceil(-1.5) = -1.0");

        Outcome<Value> floorNan = SharedStdlibSemantics.mathFloor(origin(), Double.NaN);
        check(floorNan instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.isNaN(number.value()),
            "floor(NaN) is NaN, never a failure");
        Outcome<Value> floorInf = SharedStdlibSemantics.mathFloor(origin(),
            Double.POSITIVE_INFINITY);
        check(floorInf instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && number.value() == Double.POSITIVE_INFINITY,
            "floor(+Infinity) is +Infinity");

        expectSuccess(SharedStdlibSemantics.mathSqrt(origin(), 4.0),
            new Value.Number(2.0), "sqrt(4.0) = 2.0");
        expectSuccess(SharedStdlibSemantics.mathSqrt(origin(), 2.0),
            new Value.Number(Math.sqrt(2.0)), "sqrt(2.0) is the IEEE value");
        expectSuccess(SharedStdlibSemantics.mathSqrt(origin(), 0.0),
            new Value.Number(0.0), "sqrt(0.0) = 0.0");
        Outcome<Value> sqrtNan = SharedStdlibSemantics.mathSqrt(origin(), Double.NaN);
        check(sqrtNan instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.isNaN(number.value()),
            "sqrt(NaN) is NaN — NaN is never a negative input");
        Outcome<Value> sqrtNegativeZero =
            SharedStdlibSemantics.mathSqrt(origin(), -0.0);
        check(sqrtNegativeZero instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.doubleToLongBits(number.value())
                    == Double.doubleToLongBits(-0.0),
            "sqrt(-0.0) is -0.0 (IEEE); -0.0 is not negative");

        // SQRT_NEGATIVE: exact projection; the outcome carries the operand.
        expectFailure(SharedStdlibSemantics.mathSqrt(origin(), -4.0),
            FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001, "sqrt of negative number",
            null, CanonicalJson.numberHex(-4.0), Map.of(), origin(),
            "sqrt(-4.0) fails SQRT_NEGATIVE carrying the negative operand");
        expectFailure(SharedStdlibSemantics.mathSqrt(origin(), -0.5),
            FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001, "sqrt of negative number",
            null, CanonicalJson.numberHex(-0.5), Map.of(), origin(),
            "sqrt(-0.5) fails SQRT_NEGATIVE");
        expectFailure(SharedStdlibSemantics.mathSqrt(origin(), Double.NEGATIVE_INFINITY),
            FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001, "sqrt of negative number",
            null, CanonicalJson.numberHex(Double.NEGATIVE_INFINITY), Map.of(), origin(),
            "sqrt(-Infinity) fails SQRT_NEGATIVE");

        expectSuccess(SharedStdlibSemantics.mathAbsInt(origin(), -3),
            new Value.Int(3), "absInt(-3) = 3");
        expectSuccess(SharedStdlibSemantics.mathAbsInt(origin(), 3),
            new Value.Int(3), "absInt(3) = 3");
        expectSuccess(SharedStdlibSemantics.mathAbsInt(origin(), 0),
            new Value.Int(0), "absInt(0) = 0");
        expectSuccess(SharedStdlibSemantics.mathAbsInt(origin(), 2147483647),
            new Value.Int(2147483647), "absInt(2147483647) = 2147483647");
        expectFailure(SharedStdlibSemantics.mathAbsInt(origin(), -2147483648),
            FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004, "int out of safe range",
            null, null, Map.of(), origin(),
            "absInt(-2147483648) fails E8004 int out of safe range at the call origin");

        expectSuccess(SharedStdlibSemantics.mathAbsNumber(origin(), -1.5),
            new Value.Number(1.5), "absNumber(-1.5) = 1.5");
        Outcome<Value> absNegativeZero =
            SharedStdlibSemantics.mathAbsNumber(origin(), -0.0);
        check(absNegativeZero instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.doubleToLongBits(number.value())
                    == Double.doubleToLongBits(0.0),
            "absNumber(-0.0) = +0.0 (IEEE)");
        Outcome<Value> absNan = SharedStdlibSemantics.mathAbsNumber(origin(), Double.NaN);
        check(absNan instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && Double.isNaN(number.value()),
            "absNumber(NaN) is NaN");
        Outcome<Value> absInf = SharedStdlibSemantics.mathAbsNumber(origin(),
            Double.NEGATIVE_INFINITY);
        check(absInf instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Number number
                && number.value() == Double.POSITIVE_INFINITY,
            "absNumber(-Infinity) = +Infinity");

        expectSuccess(SharedStdlibSemantics.mathMinInt(origin(), 2, 3),
            new Value.Int(2), "minInt(2,3) = 2");
        expectSuccess(SharedStdlibSemantics.mathMinInt(origin(), 3, 2),
            new Value.Int(2), "minInt(3,2) = 2");
        expectSuccess(SharedStdlibSemantics.mathMinInt(origin(), 5, 5),
            new Value.Int(5), "equal operands return that operand value");
        expectSuccess(SharedStdlibSemantics.mathMinInt(origin(), -2147483648, 5),
            new Value.Int(-2147483648), "minInt(-2147483648,5) = -2147483648");
        expectSuccess(SharedStdlibSemantics.mathMaxInt(origin(), 2, 3),
            new Value.Int(3), "maxInt(2,3) = 3");
        expectSuccess(SharedStdlibSemantics.mathMaxInt(origin(), 3, 2),
            new Value.Int(3), "maxInt(3,2) = 3");
        expectSuccess(SharedStdlibSemantics.mathMaxInt(origin(), 5, 5),
            new Value.Int(5), "equal max operands return that operand value");
        expectSuccess(SharedStdlibSemantics.mathMaxInt(origin(), -2147483648, 5),
            new Value.Int(5), "maxInt(-2147483648,5) = 5");
    }

    // =========================================================================
    // 6. Console
    // =========================================================================

    private static final class CaptureSink implements ConsoleSink {
        final SharedStdlibSemantics.Channel channel;
        final List<byte[]> writes = new ArrayList<>();

        CaptureSink(SharedStdlibSemantics.Channel channel) {
            this.channel = channel;
        }

        @Override
        public SharedStdlibSemantics.Channel channel() {
            return channel;
        }

        @Override
        public void write(byte[] bytes) {
            writes.add(bytes);
        }
    }

    private static final class FailingSink implements ConsoleSink {
        final SharedStdlibSemantics.Channel channel;

        FailingSink(SharedStdlibSemantics.Channel channel) {
            this.channel = channel;
        }

        @Override
        public SharedStdlibSemantics.Channel channel() {
            return channel;
        }

        @Override
        public void write(byte[] bytes) {
            throw new IllegalStateException("infrastructure sink failure");
        }
    }

    static void testConsoleEffects() {
        System.out.println("-- Console: byte-exact one-effect contract over the injected sink --");

        CaptureSink stdout = new CaptureSink(SharedStdlibSemantics.Channel.STDOUT);
        expectSuccess(SharedStdlibSemantics.consoleLog(origin(), valid("hi"), stdout),
            Value.Null.INSTANCE, "console.log publishes the null result");
        check(stdout.writes.size() == 1, "exactly one effect per call");
        check(Arrays.equals(stdout.writes.get(0), new byte[] {'h', 'i', '\n'}),
            "the effect bytes are the exact scalar UTF-8 bytes plus one '\\n'");

        CaptureSink stderr = new CaptureSink(SharedStdlibSemantics.Channel.STDERR);
        expectSuccess(SharedStdlibSemantics.consoleError(origin(), valid("err"), stderr),
            Value.Null.INSTANCE, "console.error publishes the null result");
        check(stderr.writes.size() == 1, "exactly one effect per stderr call");
        check(Arrays.equals(stderr.writes.get(0), new byte[] {'e', 'r', 'r', '\n'}),
            "stderr bytes are exact plus one '\\n'");

        // Byte-exactness for multi-byte scalars: exact scalar UTF-8.
        String text = "h\u00e9llo \ud83d\ude00";
        CaptureSink utf8 = new CaptureSink(SharedStdlibSemantics.Channel.STDOUT);
        SharedStdlibSemantics.consoleLog(origin(), valid(text), utf8);
        byte[] expectedBytes = text.getBytes(StandardCharsets.UTF_8);
        byte[] expected = Arrays.copyOf(expectedBytes, expectedBytes.length + 1);
        expected[expected.length - 1] = '\n';
        check(utf8.writes.size() == 1 && Arrays.equals(utf8.writes.get(0), expected),
            "multi-byte scalars write their exact UTF-8 bytes plus '\\n' ("
                + expectedBytes.length + " scalar bytes)");

        // One effect per call: two calls → two ordered writes.
        CaptureSink ordered = new CaptureSink(SharedStdlibSemantics.Channel.STDOUT);
        SharedStdlibSemantics.consoleLog(origin(), valid("a"), ordered);
        SharedStdlibSemantics.consoleLog(origin(), valid("b"), ordered);
        check(ordered.writes.size() == 2
                && Arrays.equals(ordered.writes.get(0), new byte[] {'a', '\n'})
                && Arrays.equals(ordered.writes.get(1), new byte[] {'b', '\n'}),
            "two calls emit two ordered effects");

        // Channel identity: a sink of the wrong channel is a defect.
        expectDefect(() -> SharedStdlibSemantics.consoleLog(origin(), valid("x"), stderr),
            SharedStdlibSemantics.Defect.class, "channel", "a wrong-channel sink is a defect");
        expectDefect(() -> SharedStdlibSemantics.consoleError(origin(), valid("x"), stdout),
            SharedStdlibSemantics.Defect.class, "channel",
            "a wrong-channel sink on error is a defect");

        // A failing sink is infrastructure: the exception propagates
        // uncaught (run abort), and no DEAL failure is ever reported.
        boolean propagated = false;
        try {
            SharedStdlibSemantics.consoleLog(origin(), valid("x"),
                new FailingSink(SharedStdlibSemantics.Channel.STDOUT));
        } catch (IllegalStateException infrastructure) {
            propagated = infrastructure.getMessage().contains("infrastructure sink failure");
        }
        check(propagated,
            "a failing sink propagates as infrastructure (run abort), never a DEAL failure");
    }

    // =========================================================================
    // 7. Combined T2/T1: lower the 20-id battery and execute every op
    // =========================================================================

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception e) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    private static CheckedProjectBuildResult compileProject(Path tmp,
            Map<String, String> sources, String entryName) {
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            for (Map.Entry<String, String> source : sources.entrySet()) {
                Files.writeString(src.resolve(source.getKey()), source.getValue());
            }
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve(entryName).toAbsolutePath(), tmp.resolve("build"), false, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize());
            boolean ok = orchestrator.compile();
            check(ok, entryName + " compiles through phase 3 + builder: "
                + orchestrator.diagnostics());
            if (!ok) {
                return null;
            }
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            check(checked != null && !checked.hasErrors(),
                "the orchestrator built exactly one checked project: "
                    + (checked == null ? "null" : checked.diagnostics()));
            return checked;
        } catch (Exception e) {
            fail(entryName + " fixture setup threw: " + e);
            return null;
        }
    }

    private static CheckedModuleInput moduleOf(CheckedProjectInput input,
                                               String modulePath) {
        if (input == null) {
            return null;
        }
        for (CheckedModuleInput module : input.modules()) {
            if (module.moduleId().path().equals(modulePath)) {
                return module;
            }
        }
        return null;
    }

    private static SemanticRequirementManifest manifestOf(RequirementManifestResult manifests,
                                                          ModuleId moduleId) {
        if (manifests == null || manifests.hasErrors() || manifests.manifests() == null) {
            return null;
        }
        for (SemanticRequirementManifest manifest : manifests.manifests()) {
            if (manifest.moduleId().equals(moduleId)) {
                return manifest;
            }
        }
        return null;
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(SemanticProfile.DEAL_V1_2_INT32,
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
    }

    private static SemanticIrValidator.ComparisonFacts factsOf(
            CheckedProjectBuildResult checked) {
        return new SemanticIrValidator.ComparisonFacts(
            checked.index().interfaceIndexDigest(), SemanticProfile.DEAL_V1_2_INT32,
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash());
    }

    private static SemanticLowerer.LoweringResult lowerSubject(
            CheckedProjectBuildResult checked, String modulePath) {
        CheckedModuleInput subject = moduleOf(checked.input(), modulePath);
        if (subject == null) {
            fail("the checked project has no module " + modulePath);
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation(),
            checked.input(), checked.index());
        check(manifests != null && !manifests.hasErrors(),
            "the manifest computation is clean"
                + (manifests == null ? " (null)" : ": " + manifests.diagnostics()));
        if (manifests == null || manifests.hasErrors()) {
            return null;
        }
        SemanticRequirementManifest manifest = manifestOf(manifests, subject.moduleId());
        if (manifest == null) {
            fail("no manifest for module " + modulePath);
            return null;
        }
        List<ModuleId> moduleIds = new ArrayList<>();
        for (CheckedModuleInput module : checked.input().modules()) {
            moduleIds.add(module.moduleId());
        }
        return SemanticLowerer.lowerModuleFullProgram(
            subject, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
            checked.index().interfaceIndexDigest(),
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
            SemanticIdAllocator.over(moduleIds));
    }

    /** The single {@code STDLIB_CALL} carrying the given id, or null. */
    private static SemanticOp stdlibOpBy(LoweredModuleUnit unit, StdlibFunctionId function) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL
                    && ((KindPayload.StdlibCallPayload) op.payload()).function() == function) {
                return op;
            }
        }
        return null;
    }

    /** The descriptor-kind rule of the closed boundary table. */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    /** The closed catalog row of one id (the single row carrying it). */
    private static StdlibFunctionCatalog.Entry catalogEntryOf(StdlibFunctionId function) {
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            if (entry.function() == function) {
                return entry;
            }
        }
        throw new IllegalStateException("no catalog row for " + function);
    }

    /** The {@code BoundaryValueView} classification of one seeded value. */
    private static BoundaryValueView viewOf(Value value) {
        return switch (value) {
            case Value.Null ignored -> BoundaryValueView.of(ActualKind.NULL);
            case Value.Bool ignored -> BoundaryValueView.of(ActualKind.BOOLEAN);
            case Value.Int intValue -> BoundaryValueView.ofInt(intValue.value());
            case Value.Number number -> BoundaryValueView.ofNumber(number.value());
            case Value.String string -> BoundaryValueView.of(string.scalar()
                instanceof UnicodeScalars.Valid ? ActualKind.STRING : ActualKind.INVALID_UNICODE);
            case Value.Table ignored -> BoundaryValueView.of(ActualKind.TABLE);
            case Value.Array array -> {
                List<BoundaryValueView> elements = new ArrayList<>();
                for (Value element : array.elements().elements()) {
                    elements.add(viewOf(element));
                }
                yield BoundaryValueView.ofArray(elements);
            }
            case Value.Other other -> other.kind() == ActualKind.CLASS
                ? BoundaryValueView.ofClass(other.classId())
                : BoundaryValueView.of(other.kind());
        };
    }

    /** One seed: the declared-descriptor arguments and the parent-table outcome. */
    private record Seed(StdlibFunctionId function, List<Value> args, Value expected) {
    }

    /**
     * The injected deterministic clock of the combined battery (K7): the
     * {@code TIME_NOW_MILLIS} algorithm returns exactly this reading, so
     * the seed outcome is pinned; the oracle and each target read their
     * own clock of the same kind (a contemporary epoch-millisecond
     * value).
     */
    private static final long FIXED_CLOCK_MILLIS = 1_700_000_000_000L;
    private static final SharedStdlibSemantics.Clock FIXED_CLOCK =
        () -> FIXED_CLOCK_MILLIS;

    private static Seed seed(StdlibFunctionId function, Value arg, Value expected) {
        return new Seed(function, List.of(arg), expected);
    }

    /** The 21-id seed table in the closed enum declaration order. */
    private static List<Seed> seeds() {
        SemanticTable<Value> table = new SemanticTable<>();
        table.put("k", new Value.Int(1));
        table.put("a", new Value.Int(2));
        SemanticTable<Value> parsed = new SemanticTable<>();
        parsed.put("a", new Value.Int(1));
        return List.of(
            seed(StdlibFunctionId.CONSOLE_LOG, Value.string("log"), Value.Null.INSTANCE),
            seed(StdlibFunctionId.CONSOLE_ERROR, Value.string("error"), Value.Null.INSTANCE),
            seed(StdlibFunctionId.STRING_LENGTH, Value.string("abc"), new Value.Int(3)),
            new Seed(StdlibFunctionId.STRING_SUBSTRING,
                List.of(Value.string("abc"), new Value.Int(1), new Value.Int(2)),
                Value.string("b")),
            new Seed(StdlibFunctionId.STRING_CONTAINS,
                List.of(Value.string("abc"), Value.string("b")), new Value.Bool(true)),
            new Seed(StdlibFunctionId.STRING_STARTS_WITH,
                List.of(Value.string("abc"), Value.string("a")), new Value.Bool(true)),
            new Seed(StdlibFunctionId.STRING_ENDS_WITH,
                List.of(Value.string("abc"), Value.string("c")), new Value.Bool(true)),
            new Seed(StdlibFunctionId.STRING_REPLACE,
                List.of(Value.string("aba"), Value.string("a"), Value.string("z")),
                Value.string("zbz")),
            new Seed(StdlibFunctionId.STRING_SPLIT,
                List.of(Value.string("a,b"), Value.string(",")),
                Value.array(Value.string("a"), Value.string("b"))),
            seed(StdlibFunctionId.STRING_TRIM, Value.string(" x "), Value.string("x")),
            seed(StdlibFunctionId.TABLE_KEYS, new Value.Table(table),
                Value.array(Value.string("k"), Value.string("a"))),
            seed(StdlibFunctionId.JSON_PARSE, Value.string("{\"a\": 1}"),
                new Value.Table(parsed)),
            seed(StdlibFunctionId.JSON_STRINGIFY, new Value.Table(table),
                Value.string("{\"k\":1,\"a\":2}")),
            seed(StdlibFunctionId.MATH_FLOOR, new Value.Number(1.5), new Value.Number(1.0)),
            seed(StdlibFunctionId.MATH_CEIL, new Value.Number(1.5), new Value.Number(2.0)),
            seed(StdlibFunctionId.MATH_SQRT, new Value.Number(4.0), new Value.Number(2.0)),
            seed(StdlibFunctionId.MATH_ABS_INT, new Value.Int(-3), new Value.Int(3)),
            seed(StdlibFunctionId.MATH_ABS_NUMBER, new Value.Number(-1.5),
                new Value.Number(1.5)),
            new Seed(StdlibFunctionId.MATH_MIN_INT,
                List.of(new Value.Int(2), new Value.Int(3)), new Value.Int(2)),
            new Seed(StdlibFunctionId.MATH_MAX_INT,
                List.of(new Value.Int(2), new Value.Int(3)), new Value.Int(3)),
            new Seed(StdlibFunctionId.TIME_NOW_MILLIS, List.of(),
                new Value.Number((double) FIXED_CLOCK_MILLIS)));
    }

    /**
     * The combined T2/T1 battery: lowers the 20-id module through the
     * landed carrier, validates the produced {@code STDLIB_CALL} ops and
     * their stamping, drives each declared parameter through the landed
     * {@code BoundaryExecutor} at the {@code STDLIB_PARAMETER} position,
     * then executes each op through {@link SharedStdlibSemantics} and
     * asserts the parent-table outcome. Returns the lowered unit for the
     * boundary-precedence and defect batteries.
     */
    static LoweredModuleUnit testCombinedT2T1() throws Exception {
        System.out.println("-- Combined T2/T1: the 21-id battery through SharedStdlibSemantics --");

        Path tmp = Files.createTempDirectory("deal-stdlib-semantics-battery");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"
                    import * as str from "std/string"
                    import * as tbl from "std/table"
                    import * as json from "std/json"
                    import * as math from "std/math"
                    import * as time from "std/time"

                    function run(): null {
                      console.log("log")
                      console.error("error")
                      let n1: int = str.length("abc")
                      let s2: string = str.substring("abc", 1, 2)
                      let b3: boolean = str.contains("abc", "b")
                      let b4: boolean = str.startsWith("abc", "a")
                      let b5: boolean = str.endsWith("abc", "c")
                      let s6: string = str.replace("aba", "a", "z")
                      let xs7: string[] = str.split("a,b", ",")
                      let s8: string = str.trim(" x ")
                      let t: table = {k: 1}
                      let ks9: string[] = tbl.keys(t)
                      let jt10: table = json.parse("{\\"a\\": 1}")
                      let js11: string = json.stringify(t)
                      let f12: number = math.floor(1.5)
                      let f13: number = math.ceil(1.5)
                      let f14: number = math.sqrt(4.0)
                      let i15: int = math.absInt(-3)
                      let f16: number = math.absNumber(-1.5)
                      let i17: int = math.minInt(2, 3)
                      let i18: int = math.maxInt(2, 3)
                      let now: int = time.nowMillis()
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return null;
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
                "the 21-id battery lowers through the validator/chain protocol/"
                    + "control-flow validator: " + (lowering == null ? "null"
                        : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return null;
            }
            LoweredModuleUnit unit = lowering.unit();

            List<SemanticOp> stdlibOps = new ArrayList<>();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.STDLIB_CALL) {
                    stdlibOps.add(op);
                }
            }
            check(stdlibOps.size() == 21,
                "exactly one STDLIB_CALL per cataloged call: 21 ops; got "
                    + stdlibOps.size());
            EnumSet<StdlibFunctionId> produced = EnumSet.noneOf(StdlibFunctionId.class);
            for (SemanticOp op : stdlibOps) {
                produced.add(((KindPayload.StdlibCallPayload) op.payload()).function());
            }
            check(produced.equals(EnumSet.allOf(StdlibFunctionId.class)),
                "the produced function set equals the catalog's closed 21-id set (the step "
                    + "fails if the catalog misses or adds an entry); got " + produced);

            Map<StdlibFunctionId, Seed> seedsByFunction = new LinkedHashMap<>();
            for (Seed seed : seeds()) {
                seedsByFunction.put(seed.function(), seed);
            }
            check(seedsByFunction.keySet().equals(EnumSet.allOf(StdlibFunctionId.class)),
                "the seed table covers the closed 21-id set exactly");

            CaptureSink sink = new CaptureSink(SharedStdlibSemantics.Channel.STDOUT);
            List<byte[]> stderrWrites = new ArrayList<>();
            ConsoleSink routingSink = new ConsoleSink() {
                @Override
                public SharedStdlibSemantics.Channel channel() {
                    return sink.channel();
                }

                @Override
                public void write(byte[] bytes) {
                    sink.writes.add(bytes);
                }
            };
            ConsoleSink stderrRouting = new ConsoleSink() {
                @Override
                public SharedStdlibSemantics.Channel channel() {
                    return SharedStdlibSemantics.Channel.STDERR;
                }

                @Override
                public void write(byte[] bytes) {
                    stderrWrites.add(bytes);
                }
            };

            for (SemanticOp op : stdlibOps) {
                KindPayload.StdlibCallPayload payload =
                    (KindPayload.StdlibCallPayload) op.payload();
                StdlibFunctionId function = payload.function();
                Seed seed = seedsByFunction.get(function);
                StdlibFunctionCatalog.Entry row = catalogEntryOf(function);

                // Misstamp checks: id, declared descriptors, and the
                // single-source policy must match the closed table.
                check(payload.effectCapability() == SemanticCapability.STDLIB_SEMANTICS,
                    function + " carries effectCapability STDLIB_SEMANTICS");
                check(op.failurePolicy() == SemanticIrValidator.stdlibPolicy(function),
                    function + " stamps failurePolicy "
                        + SemanticIrValidator.stdlibPolicy(function)
                        + " from the single table; got " + op.failurePolicy());
                check(op.operandTypes().equals(row.parameterDescriptors()),
                    function + " operandTypes equal the declared parameter descriptors: "
                        + op.operandTypes() + " vs " + row.parameterDescriptors());
                check(op.resultType().equals(row.returnDescriptor()),
                    function + " resultType is the declared return descriptor "
                        + row.returnDescriptor().canonicalSpecText());
                check(payload.args().equals(op.operands()),
                    function + " payload args equal the operands in order");
                check(seed.args().size() == row.parameterDescriptors().size(),
                    function + " seed arity matches the declared descriptor count");

                // Every declared parameter passes its STDLIB_PARAMETER
                // boundary through the landed BoundaryExecutor at the
                // descriptor-kind-rule policy before the algorithm runs.
                for (int i = 0; i < row.parameterDescriptors().size(); i++) {
                    RuntimeDescriptor descriptor = row.parameterDescriptors().get(i);
                    BoundaryOutcome boundary = BoundaryExecutor.check(
                        descriptorKindPolicy(descriptor), descriptor,
                        viewOf(seed.args().get(i)), BoundaryContext.none());
                    check(boundary instanceof BoundaryOutcome.Pass,
                        function + " parameter " + (i + 1) + " passes its "
                            + "STDLIB_PARAMETER boundary for the declared-descriptor seed");
                }

                // Execute the produced op through the single executor.
                ConsoleSink opSink = function == StdlibFunctionId.CONSOLE_ERROR
                    ? stderrRouting
                    : routingSink;
                Outcome<Value> outcome = SharedStdlibSemantics.execute(op, seed.args(),
                    opSink, FIXED_CLOCK);
                expectSuccess(outcome, seed.expected(),
                    "STDLIB_CALL(" + function + ") executes the parent-table outcome");
            }

            // The two console calls of the battery produced exactly the
            // pinned ordered effects on the named channels.
            check(sink.writes.size() == 1
                    && Arrays.equals(sink.writes.get(0), new byte[] {'l', 'o', 'g', '\n'}),
                "the battery's console.log emitted exactly one STDOUT effect 'log\\n'");
            check(stderrWrites.size() == 1
                    && Arrays.equals(stderrWrites.get(0),
                        new byte[] {'e', 'r', 'r', 'o', 'r', '\n'}),
                "the battery's console.error emitted exactly one STDERR effect 'error\\n'");

            // The unit itself passes the closed validator on the typed surface.
            Optional<CompilerDiagnostic> validation =
                SemanticIrValidator.validate(unit, factsOf(checked));
            check(validation.isEmpty(),
                "the battery unit passes the closed validator"
                    + (validation.isPresent() ? ": " + validation.get().message() : ""));
            return unit;
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 8. Boundary precedence: invalid encodings fail at STDLIB_PARAMETER
    // =========================================================================

    static void testBoundaryPrecedence(LoweredModuleUnit unit) {
        System.out.println("-- Boundary precedence: invalid scalar encodings fail at "
            + "STDLIB_PARAMETER before any algorithm runs --");

        if (unit == null) {
            fail("no lowered unit for the boundary-precedence battery");
            return;
        }
        SemanticOp stringLengthOp = stdlibOpBy(unit, StdlibFunctionId.STRING_LENGTH);
        check(stringLengthOp != null, "the battery unit carries the STRING_LENGTH call");
        if (stringLengthOp == null) {
            return;
        }
        // The produced parameter boundary is kind STDLIB_PARAMETER with
        // the declared string descriptor and the descriptor-kind rule.
        boolean sawStdlibParameter = false;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && stringLengthOp.opId().equals(op.origin().parentOpId())
                    && op.payload() instanceof KindPayload.BoundaryPayload boundary) {
                if (boundary.kind() == deal.semantic.ir.BoundaryKind.STDLIB_PARAMETER) {
                    sawStdlibParameter = true;
                    check(boundary.descriptor().equals(RuntimeDescriptor.String.INSTANCE),
                        "the STRING_LENGTH parameter boundary carries the string descriptor");
                    check(op.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                        "the parameter boundary carries the descriptor-kind-rule policy");
                }
            }
        }
        check(sawStdlibParameter, "the STRING_LENGTH call carries its STDLIB_PARAMETER child");

        // Positive control: a valid scalar carrier passes the check.
        BoundaryOutcome validPass = BoundaryExecutor.check(FailurePolicyId.TYPE_DESCRIPTOR,
            RuntimeDescriptor.String.INSTANCE, BoundaryValueView.of(ActualKind.STRING),
            BoundaryContext.none());
        check(validPass instanceof BoundaryOutcome.Pass,
            "a valid string carrier passes the STDLIB_PARAMETER descriptor check");

        // The exact invalid-encoding projection at the boundary.
        BoundaryOutcome invalidCheck = BoundaryExecutor.check(FailurePolicyId.TYPE_DESCRIPTOR,
            RuntimeDescriptor.String.INSTANCE,
            BoundaryValueView.of(ActualKind.INVALID_UNICODE), BoundaryContext.none());
        check(invalidCheck instanceof BoundaryOutcome.Fail,
            "an invalid scalar carrier fails the STDLIB_PARAMETER check");
        if (invalidCheck instanceof BoundaryOutcome.Fail invalidFail) {
            check(invalidFail.failure().code() == DiagnosticCode.E8001
                    && invalidFail.failure().message()
                        .equals("expected string, got invalid Unicode scalar encoding"),
                "the exact E8001 'expected string, got invalid Unicode scalar encoding' "
                    + "projects at the boundary; got " + invalidFail.failure().message());
            check(invalidFail.failure().expected() == null
                    || "string".equals(invalidFail.failure().expected()),
                "the projection attains the expected/actual classification");
        }

        // The primitive is never reached with an invalid carrier: the
        // Value-level dispatch fails closed (defect, never a projection).
        expectDefect(() -> SharedStdlibSemantics.execute(stringLengthOp,
                List.of(Value.string(UnicodeScalars.Invalid.INSTANCE)), null),
            SharedStdlibSemantics.Defect.class, "never reached with an invalid carrier",
            "an Invalid carrier reaching the primitive is a producer defect, never a "
                + "second projection");
    }

    // =========================================================================
    // 9. Fail-closed defects and the spot-check origins
    // =========================================================================

    static void testFailClosedDefects(LoweredModuleUnit unit) {
        System.out.println("-- Fail-closed defects and boundary admission sets --");

        if (unit == null) {
            fail("no lowered unit for the defect battery");
            return;
        }
        SemanticOp nonStdlib = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.STDLIB_CALL) {
                nonStdlib = op;
                break;
            }
        }
        check(nonStdlib != null, "the unit carries a non-stdlib op for the defect drive");
        if (nonStdlib != null) {
            SemanticOp nonStdlibOp = nonStdlib;
            expectDefect(() -> SharedStdlibSemantics.execute(nonStdlibOp, List.of(), null),
                SharedStdlibSemantics.Defect.class, "only STDLIB_CALL ops",
                "a non-STDLIB op fails closed");
        }

        SemanticOp length = stdlibOpBy(unit, StdlibFunctionId.STRING_LENGTH);
        expectDefect(() -> SharedStdlibSemantics.execute(length, List.of(), null),
            SharedStdlibSemantics.Defect.class, "count mismatch",
            "a wrong argument count fails closed");
        expectDefect(() -> SharedStdlibSemantics.execute(length,
                List.of(new Value.Number(3.0)), null),
            SharedStdlibSemantics.Defect.class, "Valid string carrier",
            "a wrong-kind carrier fails closed");

        SemanticOp log = stdlibOpBy(unit, StdlibFunctionId.CONSOLE_LOG);
        expectDefect(() -> SharedStdlibSemantics.execute(log, List.of(Value.string("x")), null),
            NullPointerException.class, "sink",
            "a null sink on a console call fails closed");
        CaptureSink wrongChannel = new CaptureSink(SharedStdlibSemantics.Channel.STDERR);
        expectDefect(() -> SharedStdlibSemantics.execute(log, List.of(Value.string("x")),
                wrongChannel),
            SharedStdlibSemantics.Defect.class, "channel",
            "a wrong-channel sink fails closed");

        // Boundary admission sets: a number parameter admits an int
        // carrier (exact conversion); an int parameter admits an
        // in-range integral number carrier; anything else fails closed.
        SemanticOp floor = stdlibOpBy(unit, StdlibFunctionId.MATH_FLOOR);
        expectSuccess(SharedStdlibSemantics.execute(floor, List.of(new Value.Int(2)), null),
            new Value.Number(2.0), "a number parameter admits an int carrier exactly");
        SemanticOp absInt = stdlibOpBy(unit, StdlibFunctionId.MATH_ABS_INT);
        expectSuccess(SharedStdlibSemantics.execute(absInt,
                List.of(new Value.Number(3.0)), null),
            new Value.Int(3), "an int parameter admits an in-range integral number carrier");
        expectDefect(() -> SharedStdlibSemantics.execute(absInt,
                List.of(new Value.Number(3.5)), null),
            SharedStdlibSemantics.Defect.class, "int carrier",
            "a fractional number carrier fails the int admission set");

        // An invalid-scalar table key is a producer defect (keys are
        // identifier-derived), never a projection and never a crash.
        SemanticTable<Value> badKeyTable = new SemanticTable<>();
        badKeyTable.put("\ud800", new Value.Int(1));
        expectDefect(() -> SharedStdlibSemantics.jsonStringify(origin(), badKeyTable),
            SharedStdlibSemantics.Defect.class, "valid scalar sequence",
            "an invalid-scalar table key fails closed");

        // Spot check: INT32_RESULT carries the overflow origin (the
        // STDLIB_CALL call origin).
        Outcome<Value> overflow = SharedStdlibSemantics.execute(absInt,
            List.of(new Value.Int(-2147483648)), null);
        expectFailure(overflow, FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004,
            "int out of safe range", null, null, Map.of(), absInt.origin(),
            "absInt(-2147483648) through execute fails E8004 at the call origin");

        // Spot check: SQRT_NEGATIVE through execute carries the operand.
        SemanticOp sqrt = stdlibOpBy(unit, StdlibFunctionId.MATH_SQRT);
        Outcome<Value> negativeSqrt = SharedStdlibSemantics.execute(sqrt,
            List.of(new Value.Number(-4.0)), null);
        expectFailure(negativeSqrt, FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001,
            "sqrt of negative number", null, CanonicalJson.numberHex(-4.0), Map.of(),
            sqrt.origin(), "sqrt(-4.0) through execute carries the operand at the call "
                + "origin");
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Shared Stdlib Semantics Tests (ISSUE-0495) ===\n");

        testStringLength();
        testStringSubstring();
        testStringContainsStartsEnds();
        testStringReplace();
        testStringSplit();
        testStringTrim();
        testTableKeys();
        testJsonParseValues();
        testJsonParseSyntaxFailures();
        testJsonStringifyValues();
        testJsonStringifyFailures();
        testMath();
        testConsoleEffects();
        LoweredModuleUnit unit = testCombinedT2T1();
        testBoundaryPrecedence(unit);
        testFailClosedDefects(unit);

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
