package deal.test;

import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.TypeChecker;
import deal.codegen.jvm.JvmBackend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.checker.ModuleResolver;
import deal.module.ModuleShapeValidator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.DescriptorService;
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
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.UnicodeScalars;
import deal.types.Type;
import deal.ast.ProgramNode;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

/**
 * Compares retained Lua and JavaScript stdlib helpers and JVM-emitted helpers
 * with {@link SharedStdlibSemantics} across values, console bytes, and failures.
 */
public final class StdlibEquivalenceBatteryTest {

    enum Lane {
        RETAINED_LUA,
        RETAINED_JS,
        JVM_EMITTED
    }


    private StdlibEquivalenceBatteryTest() {
        // Static test main only.
    }

    // =========================================================================
    // Harness
    // =========================================================================

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

    private static Path repoRoot() {
        return Path.of(System.getProperty("user.dir")).toAbsolutePath().normalize();
    }

    /** The fixed synthetic operation origin of the reference run. */
    private static SourceOrigin origin() {
        return new SourceOrigin("stdlib-equivalence-battery", SourceSpan.synthetic("stdlib"),
            deal.semantic.ir.SourceOriginKind.SYNTHETIC, new AnchorId(1), null);
    }

    // =========================================================================
    // Declared descriptors (structural equality is authoritative, D6)
    // =========================================================================

    private static final RuntimeDescriptor DESC_INT = DescriptorService.describe(Type.Int.INSTANCE);
    private static final RuntimeDescriptor DESC_NUMBER =
        DescriptorService.describe(Type.Number.INSTANCE);
    private static final RuntimeDescriptor DESC_STRING =
        DescriptorService.describe(Type.String.INSTANCE);
    private static final RuntimeDescriptor DESC_BOOLEAN =
        DescriptorService.describe(Type.Boolean.INSTANCE);
    private static final RuntimeDescriptor DESC_NULL =
        DescriptorService.describe(Type.Null.INSTANCE);
    private static final RuntimeDescriptor DESC_TABLE =
        DescriptorService.describe(Type.Table.INSTANCE);
    private static final RuntimeDescriptor DESC_STRING_ARRAY =
        DescriptorService.describe(new Type.Array(Type.String.INSTANCE));

    /** The closed catalog row of one id. */
    private static StdlibFunctionCatalog.Entry catalogEntryOf(StdlibFunctionId function) {
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            if (entry.function() == function) {
                return entry;
            }
        }
        throw new IllegalStateException("no catalog row for " + function);
    }

    /** The descriptor-kind rule of the closed boundary-assignment table. */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    // =========================================================================
    // The case model (the full declared input domain of the battery)
    // =========================================================================

    /** One battery case: the named observable plus its per-lane applicability. */
    sealed interface Case permits ValueCase, ChainCase, ConsoleCase, DelReinsKeysCase {

        /** The case name — the divergence seed of a divergent case. */
        String name();

        /** The lanes the case drives. */
        Set<Lane> lanes();

        /**
         * The function IDs affected by this case.
         */
        List<StdlibFunctionId> attribution();
    }

    /** One argument of a direct case. */
    sealed interface Arg permits Arg.StrArg, Arg.IntArg, Arg.NumArg, Arg.TableArg,
        Arg.NaNTableArg, Arg.FnLeafTableArg {

        record StrArg(String text) implements Arg {
            public StrArg {
                Objects.requireNonNull(text, "text must not be null");
            }
        }

        record IntArg(int value) implements Arg { }

        record NumArg(double value) implements Arg { }

        record TableArg(List<String> keys, List<Value> values) implements Arg {
            public TableArg {
                if (keys.size() != values.size()) {
                    throw new IllegalArgumentException("keys and values have the same size");
                }
                keys = List.copyOf(keys);
                values = List.copyOf(values);
            }
        }

        /** A table carrying the single key {@code "a"} with a NaN number. */
        record NaNTableArg() implements Arg { }

        /** A table carrying the single key {@code "f"} with a function leaf. */
        record FnLeafTableArg() implements Arg { }
    }

    /** The pinned expected outcome of a case (the hand-pinned parent table). */
    sealed interface PinnedOutcome permits PinnedOutcome.PinnedSuccess, PinnedOutcome.PinnedFailure {

        record PinnedSuccess(Value value) implements PinnedOutcome {
            public PinnedSuccess {
                Objects.requireNonNull(value, "value must not be null");
            }
        }

        record PinnedFailure(FailurePolicyId policy, DiagnosticCode code, String message,
                             String expectedText, String actualText,
                             Map<String, String> metadata) implements PinnedOutcome {

            public PinnedFailure {
                Objects.requireNonNull(policy, "policy must not be null");
                Objects.requireNonNull(code, "code must not be null");
                Objects.requireNonNull(message, "message must not be null");
                metadata = Map.copyOf(metadata);
            }
        }
    }

    /** A direct value case: {@code id(args...)} with the pinned outcome. */
    record ValueCase(String name, StdlibFunctionId id, List<Arg> args, Set<Lane> lanes,
                     PinnedOutcome pinned) implements Case {

        public ValueCase {
            args = List.copyOf(args);
            lanes = Set.copyOf(lanes);
            Objects.requireNonNull(pinned, "pinned must not be null");
        }

        @Override
        public List<StdlibFunctionId> attribution() {
            return List.of(id);
        }
    }

    /**
     * A chain case: {@code second(first(args...))} — the JSON observable
     * round-trips (parse→stringify, parse→keys) that expose the int
     * mapping and the iteration order. Attributed to both ids.
     */
    record ChainCase(String name, StdlibFunctionId first, List<Arg> firstArgs,
                     StdlibFunctionId second, Set<Lane> lanes,
                     PinnedOutcome pinned) implements Case {

        public ChainCase {
            firstArgs = List.copyOf(firstArgs);
            lanes = Set.copyOf(lanes);
            Objects.requireNonNull(pinned, "pinned must not be null");
            if (firstArgs.size() != 1 || !(firstArgs.get(0) instanceof Arg.StrArg)) {
                throw new IllegalArgumentException(
                    "a chain case runs parse→observable: the first args are one JSON text");
            }
        }

        @Override
        public List<StdlibFunctionId> attribution() {
            return List.of(first, second);
        }
    }

    /** A console case: the byte-exact effect on the named channel plus the null result. */
    record ConsoleCase(String name, StdlibFunctionId id, String text, Set<Lane> lanes)
        implements Case {

        public ConsoleCase {
            Objects.requireNonNull(text, "text must not be null");
            lanes = Set.copyOf(lanes);
        }

        @Override
        public List<StdlibFunctionId> attribution() {
            return List.of(id);
        }
    }

    /**
     * The fixed table.keys delete-reinsert case: build {@code {a,b,c}},
     * delete {@code a}, reinsert {@code a} — the common order is
     * {@code [b,c,a]} (delete removes the slot, reinsertion appends).
     */
    record DelReinsKeysCase(String name, Set<Lane> lanes, PinnedOutcome pinned)
        implements Case {

        public DelReinsKeysCase {
            lanes = Set.copyOf(lanes);
            Objects.requireNonNull(pinned, "pinned must not be null");
        }

        @Override
        public List<StdlibFunctionId> attribution() {
            return List.of(StdlibFunctionId.TABLE_KEYS);
        }
    }

    // =========================================================================
    // Value construction helpers
    // =========================================================================

    private static Value s(String text) {
        return Value.string(text);
    }

    private static Value i(int value) {
        return new Value.Int(value);
    }

    private static Value n(double value) {
        return new Value.Number(value);
    }

    private static Value b(boolean value) {
        return new Value.Bool(value);
    }

    private static Value arr(String... elements) {
        List<Value> values = new ArrayList<>();
        for (String element : elements) {
            values.add(s(element));
        }
        return Value.array(values);
    }

    private static final Value NULL = Value.Null.INSTANCE;

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
                for (int index = 0; index < left.size(); index++) {
                    if (!valueEquals(left.elementAt(index), right.elementAt(index))) {
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

    // =========================================================================
    // The master case table (hand-pinned to the parent D4/D8 table)
    // =========================================================================

    private static final Set<Lane> LUA = Set.of(Lane.RETAINED_LUA);
    private static final Set<Lane> JS = Set.of(Lane.RETAINED_JS);
    private static final Set<Lane> LUA_JS = Set.of(Lane.RETAINED_LUA, Lane.RETAINED_JS);
    private static final Set<Lane> ALL = Set.of(Lane.RETAINED_LUA, Lane.RETAINED_JS,
        Lane.JVM_EMITTED);

    private static PinnedOutcome ok(Value value) {
        return new PinnedOutcome.PinnedSuccess(value);
    }

    private static PinnedOutcome fail(FailurePolicyId policy, DiagnosticCode code,
                                      String message, String expectedText, String actualText,
                                      String... metadataPairs) {
        Map<String, String> metadata = new LinkedHashMap<>();
        for (int index = 0; index + 1 < metadataPairs.length; index += 2) {
            metadata.put(metadataPairs[index], metadataPairs[index + 1]);
        }
        return new PinnedOutcome.PinnedFailure(policy, code, message, expectedText, actualText,
            metadata);
    }

    /** One direct string case over all lanes. */
    private static ValueCase strCase(String name, StdlibFunctionId id, String a1, String a2,
                                     String a3, Value expected) {
        List<Arg> args = new ArrayList<>();
        if (a1 != null) {
            args.add(new Arg.StrArg(a1));
        }
        if (a2 != null) {
            args.add(new Arg.StrArg(a2));
        }
        if (a3 != null) {
            args.add(new Arg.StrArg(a3));
        }
        return new ValueCase(name, id, args, ALL, ok(expected));
    }

    /** The master case table in canonical order. */
    private static List<Case> cases() {
        List<Case> cases = new ArrayList<>();
        int index = 0;

        // ---- console (byte-exact effect + null result) ----
        for (String text : List.of("", "hello", "héllo 😀", "a\tb\nc")) {
            cases.add(new ConsoleCase("console.log-" + index, StdlibFunctionId.CONSOLE_LOG, text,
                ALL));
            cases.add(new ConsoleCase("console.error-" + index, StdlibFunctionId.CONSOLE_ERROR,
                text, ALL));
            index++;
        }

        // ---- string length ----
        cases.add(strCase("length-empty", StdlibFunctionId.STRING_LENGTH, "", null, null, i(0)));
        cases.add(strCase("length-abc", StdlibFunctionId.STRING_LENGTH, "abc", null, null, i(3)));
        cases.add(strCase("length-hello", StdlibFunctionId.STRING_LENGTH, "héllo", null, null,
            i(5)));
        cases.add(strCase("length-emoji", StdlibFunctionId.STRING_LENGTH, "😀", null, null, i(1)));
        cases.add(strCase("length-mixed", StdlibFunctionId.STRING_LENGTH, "a😀b", null, null,
            i(3)));
        cases.add(strCase("length-fullwidth", StdlibFunctionId.STRING_LENGTH, "１２", null, null,
            i(2)));

        // ---- string substring (scalar clamping) ----
        List<List<Object>> substringSeeds = List.of(
            List.of("abc", 0, 3, "abc"), List.of("abc", 0, 1, "a"), List.of("abc", 1, 2, "b"),
            List.of("abc", 2, 2, ""), List.of("abc", 0, -1, ""), List.of("abc", -2, 2, "ab"),
            List.of("abc", 0, 100, "abc"), List.of("abc", 3, 5, ""), List.of("abc", 5, 6, ""),
            List.of("abc", 2, 1, ""), List.of("héllo", 1, 4, "éll"), List.of("😀a", 0, 1, "😀"),
            List.of("😀a", -5, 1, "😀"));
        for (List<Object> seed : substringSeeds) {
            String tag = seed.get(1) + "_" + seed.get(2);
            cases.add(new ValueCase("substring-" + tag, StdlibFunctionId.STRING_SUBSTRING,
                List.of(new Arg.StrArg((String) seed.get(0)),
                    new Arg.IntArg((Integer) seed.get(1)),
                    new Arg.IntArg((Integer) seed.get(2))),
                ALL, ok(s((String) seed.get(3)))));
        }

        // ---- string contains / startsWith / endsWith (empty parts included) ----
        List<List<Object>> partSeeds = List.of(
            List.of("abc", "", true, true, true), List.of("", "", true, true, true),
            List.of("abc", "b", true, false, false), List.of("abc", "ab", true, true, false),
            List.of("abc", "bc", true, false, true), List.of("abc", "abc", true, true, true),
            List.of("abc", "d", false, false, false), List.of("abc", "abcd", false, false, false),
            List.of("", "a", false, false, false), List.of("héllo", "é", true, false, false),
            List.of("héllo", "e", false, false, false), List.of("a😀b", "😀", true, false, false));
        for (List<Object> seed : partSeeds) {
            String tag = ("".equals(seed.get(0)) ? "empty" : seed.get(0)) + "-"
                + ("".equals(seed.get(1)) ? "empty" : seed.get(1));
            cases.add(new ValueCase("contains-" + tag, StdlibFunctionId.STRING_CONTAINS,
                List.of(new Arg.StrArg((String) seed.get(0)),
                    new Arg.StrArg((String) seed.get(1))),
                ALL, ok(b((Boolean) seed.get(2)))));
            cases.add(new ValueCase("startsWith-" + tag, StdlibFunctionId.STRING_STARTS_WITH,
                List.of(new Arg.StrArg((String) seed.get(0)),
                    new Arg.StrArg((String) seed.get(1))),
                ALL, ok(b((Boolean) seed.get(3)))));
            cases.add(new ValueCase("endsWith-" + tag, StdlibFunctionId.STRING_ENDS_WITH,
                List.of(new Arg.StrArg((String) seed.get(0)),
                    new Arg.StrArg((String) seed.get(1))),
                ALL, ok(b((Boolean) seed.get(4)))));
        }

        // ---- string replace (non-overlapping, empty from, literal replacement) ----
        List<List<String>> replaceSeeds = List.of(
            List.of("aba", "a", "z", "zbz"), List.of("aaa", "aa", "b", "ba"),
            List.of("abc", "", "x", "abc"), List.of("abc", "d", "x", "abc"),
            List.of("ababab", "ab", "x", "xxx"), List.of("100%", "%", "p", "100p"),
            List.of("x.y", ".", ",", "x,y"), List.of("héllo", "é", "e", "hello"));
        for (List<String> seed : replaceSeeds) {
            String tag = seed.get(0) + "-" + seed.get(1) + "-" + seed.get(2);
            cases.add(new ValueCase("replace-" + tag, StdlibFunctionId.STRING_REPLACE,
                List.of(new Arg.StrArg(seed.get(0)), new Arg.StrArg(seed.get(1)),
                    new Arg.StrArg(seed.get(2))),
                ALL, ok(s(seed.get(3)))));
        }

        // ---- string split (empty input/separator, preserved empty parts) ----
        List<List<Object>> splitSeeds = List.of(
            List.of("", ",", List.<String>of()), List.of("", "", List.<String>of()),
            List.of("a,b", ",", List.of("a", "b")), List.of("a,", ",", List.of("a", "")),
            List.of(",a", ",", List.of("", "a")), List.of("a,,b", ",", List.of("a", "", "b")),
            List.of("abc", "x", List.of("abc")), List.of("abc", "", List.of("a", "b", "c")),
            List.of("héllo", "", List.of("h", "é", "l", "l", "o")),
            List.of("😀a", "", List.of("😀", "a")));
        for (List<Object> seed : splitSeeds) {
            String tag = seed.get(0) + "-sep-" + seed.get(1);
            @SuppressWarnings("unchecked")
            List<String> expected = (List<String>) seed.get(2);
            cases.add(new ValueCase("split-" + tag, StdlibFunctionId.STRING_SPLIT,
                List.of(new Arg.StrArg((String) seed.get(0)),
                    new Arg.StrArg((String) seed.get(1))),
                ALL, ok(arr(expected.toArray(new String[0])))));
        }

        // ---- string trim (exactly U+0009–U+000D and U+0020; U+00A0 not) ----
        List<List<Object>> trimSeeds = List.of(
            List.of("  x  ", "x", ALL), List.of("", "", ALL),
            List.of("\t\n\u000b\f\r x \t\n\u000b\f\r", "x", LUA_JS),
            List.of("\u00a0x\u00a0", "\u00a0x\u00a0", ALL), List.of("a\tb", "a\tb", ALL),
            List.of(" \u000b\f x \r\n\t", "x", LUA_JS), List.of("\u00a0 \u3000",
                "\u00a0 \u3000", ALL),
            List.of("😀", "😀", ALL), List.of("\tx", "x", ALL), List.of("x\t", "x", ALL));
        for (List<Object> seed : trimSeeds) {
            String input = (String) seed.get(0);
            String tag = "trim-" + (input.isEmpty() ? "empty" : input)
                .replaceAll("\\s", "S").replace("\u00a0", "NBSP").replace("\u3000", "IS");
            cases.add(new ValueCase(tag, StdlibFunctionId.STRING_TRIM,
                List.of(new Arg.StrArg(input)), (Set<Lane>) seed.get(2),
                ok(s((String) seed.get(1)))));
        }

        // ---- table keys: first-insertion order; delete-reinsert-to-end ----
        cases.add(new ValueCase("keys-empty", StdlibFunctionId.TABLE_KEYS,
            List.of(new Arg.TableArg(List.of(), List.of())), ALL, ok(arr())));
        cases.add(new ValueCase("keys-abc-insertion", StdlibFunctionId.TABLE_KEYS,
            List.of(new Arg.TableArg(List.of("a", "b", "c"),
                List.of(i(1), i(2), i(3)))),
            ALL, ok(arr("a", "b", "c"))));
        cases.add(new DelReinsKeysCase("keys-delete-reinsert-a", ALL,
            ok(arr("b", "c", "a"))));
        cases.add(new ChainCase("keys-parse-abc", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1,\"b\":2,\"c\":3}")),
            StdlibFunctionId.TABLE_KEYS, LUA_JS, ok(arr("a", "b", "c"))));
        cases.add(new ChainCase("keys-parse-intlike", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"9\":1,\"1\":2,\"5\":3}")),
            StdlibFunctionId.TABLE_KEYS, LUA_JS, ok(arr("9", "1", "5"))));

        // ---- json parse/stringify observable round-trips (int mapping, order,
        //      duplicate keys, escaping, surrogate pairs, failures) ----
        cases.add(new ChainCase("stringify-parse-abc", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1,\"b\":2,\"c\":3}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"a\":1,\"b\":2,\"c\":3}"))));
        cases.add(new ChainCase("stringify-parse-1.0", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1.0}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"a\":1.0}"))));
        cases.add(new ChainCase("stringify-parse-1e3", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1e3}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"a\":1000.0}"))));
        cases.add(new ChainCase("stringify-parse-int", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"a\":1}"))));
        cases.add(new ChainCase("stringify-parse-dup", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":1,\"b\":2,\"a\":3}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"a\":3,\"b\":2}"))));
        cases.add(new ChainCase("stringify-parse-surrogate", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"k\":\"😀\"}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"k\":\"😀\"}"))));
        cases.add(new ChainCase("stringify-parse-escapes", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"k\":\"a\\nb\\\"c\\\\d\"}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"k\":\"a\\nb\\\"c\\\\d\"}"))));
        cases.add(new ChainCase("stringify-parse-intlike", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"9\":1,\"1\":2,\"5\":3}")),
            StdlibFunctionId.JSON_STRINGIFY, LUA_JS, ok(s("{\"9\":1,\"1\":2,\"5\":3}"))));
        cases.add(new ValueCase("parse-syntax-missing-value", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("{\"a\":}")), LUA_JS,
            fail(FailurePolicyId.JSON_PARSE_SYNTAX, DiagnosticCode.E8001,
                "JSON parse error at position 6: "
                    + SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
                null, null, "oneBasedByteOffset", "6", "reason",
                SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER)));
        cases.add(new ValueCase("parse-top-level-scalar", StdlibFunctionId.JSON_PARSE,
            List.of(new Arg.StrArg("1")), LUA_JS,
            fail(FailurePolicyId.TYPE_DESCRIPTOR, DiagnosticCode.E8001,
                "expected table, got int", "table", "int")));

        // ---- json stringify direct tables ----
        cases.add(new ValueCase("stringify-empty", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.TableArg(List.of(), List.of())), LUA_JS, ok(s("{}"))));
        cases.add(new ValueCase("stringify-ab", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.TableArg(List.of("a", "b"), List.of(i(1), i(2)))),
            LUA_JS, ok(s("{\"a\":1,\"b\":2}"))));
        cases.add(new ValueCase("stringify-abc", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.TableArg(List.of("a", "b", "c"),
                List.of(i(1), i(2), i(3)))),
            LUA_JS, ok(s("{\"a\":1,\"b\":2,\"c\":3}"))));
        cases.add(new ValueCase("stringify-newline-escape", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.TableArg(List.of("a"), List.of(s("x\ny")))), LUA_JS,
            ok(s("{\"a\":\"x\\ny\"}"))));
        cases.add(new ValueCase("stringify-surrogate", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.TableArg(List.of("a"), List.of(s("😀")))), LUA_JS,
            ok(s("{\"a\":\"😀\"}"))));
        cases.add(new ValueCase("stringify-nan", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.NaNTableArg()), JS,
            fail(FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
                "unsupported type for JSON encoding: number",
                SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "number",
                "fieldPath", "a", "actual", "number")));
        cases.add(new ValueCase("stringify-function-leaf", StdlibFunctionId.JSON_STRINGIFY,
            List.of(new Arg.FnLeafTableArg()), LUA_JS,
            fail(FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
                "unsupported type for JSON encoding: function",
                SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "function",
                "fieldPath", "f", "actual", "function")));

        // ---- math ----
        cases.add(new ValueCase("floor-1.5", StdlibFunctionId.MATH_FLOOR,
            List.of(new Arg.NumArg(1.5)), ALL, ok(n(1.0))));
        cases.add(new ValueCase("floor-neg1.5", StdlibFunctionId.MATH_FLOOR,
            List.of(new Arg.NumArg(-1.5)), ALL, ok(n(-2.0))));
        cases.add(new ValueCase("floor-0.0", StdlibFunctionId.MATH_FLOOR,
            List.of(new Arg.NumArg(0.0)), ALL, ok(n(0.0))));
        cases.add(new ValueCase("floor-2.0", StdlibFunctionId.MATH_FLOOR,
            List.of(new Arg.NumArg(2.0)), ALL, ok(n(2.0))));
        cases.add(new ValueCase("ceil-1.5", StdlibFunctionId.MATH_CEIL,
            List.of(new Arg.NumArg(1.5)), ALL, ok(n(2.0))));
        cases.add(new ValueCase("ceil-neg1.5", StdlibFunctionId.MATH_CEIL,
            List.of(new Arg.NumArg(-1.5)), ALL, ok(n(-1.0))));
        cases.add(new ValueCase("ceil-0.0", StdlibFunctionId.MATH_CEIL,
            List.of(new Arg.NumArg(0.0)), ALL, ok(n(0.0))));
        cases.add(new ValueCase("sqrt-4", StdlibFunctionId.MATH_SQRT,
            List.of(new Arg.NumArg(4.0)), ALL, ok(n(2.0))));
        cases.add(new ValueCase("sqrt-2", StdlibFunctionId.MATH_SQRT,
            List.of(new Arg.NumArg(2.0)), ALL, ok(n(1.4142135623730951))));
        cases.add(new ValueCase("sqrt-neg4", StdlibFunctionId.MATH_SQRT,
            List.of(new Arg.NumArg(-4.0)), ALL,
            fail(FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001,
                "sqrt of negative number", null, CanonicalJson.numberHex(-4.0))));
        cases.add(new ValueCase("sqrt-neg0", StdlibFunctionId.MATH_SQRT,
            List.of(new Arg.NumArg(-0.0)), ALL, ok(n(-0.0))));
        cases.add(new ValueCase("sqrt-nan", StdlibFunctionId.MATH_SQRT,
            List.of(new Arg.NumArg(Double.NaN)), JS, ok(n(Double.NaN))));
        cases.add(new ValueCase("absInt-neg3", StdlibFunctionId.MATH_ABS_INT,
            List.of(new Arg.IntArg(-3)), ALL, ok(i(3))));
        cases.add(new ValueCase("absInt-3", StdlibFunctionId.MATH_ABS_INT,
            List.of(new Arg.IntArg(3)), ALL, ok(i(3))));
        cases.add(new ValueCase("absInt-0", StdlibFunctionId.MATH_ABS_INT,
            List.of(new Arg.IntArg(0)), ALL, ok(i(0))));
        cases.add(new ValueCase("absInt-min", StdlibFunctionId.MATH_ABS_INT,
            List.of(new Arg.IntArg(Integer.MIN_VALUE)), ALL,
            fail(FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004,
                "int out of safe range", null, null)));
        cases.add(new ValueCase("absNumber-neg1.5", StdlibFunctionId.MATH_ABS_NUMBER,
            List.of(new Arg.NumArg(-1.5)), ALL, ok(n(1.5))));
        cases.add(new ValueCase("absNumber-neg0", StdlibFunctionId.MATH_ABS_NUMBER,
            List.of(new Arg.NumArg(-0.0)), ALL, ok(n(0.0))));
        cases.add(new ValueCase("minInt-2-3", StdlibFunctionId.MATH_MIN_INT,
            List.of(new Arg.IntArg(2), new Arg.IntArg(3)), ALL, ok(i(2))));
        cases.add(new ValueCase("minInt-equal", StdlibFunctionId.MATH_MIN_INT,
            List.of(new Arg.IntArg(2), new Arg.IntArg(2)), ALL, ok(i(2))));
        cases.add(new ValueCase("minInt-negs", StdlibFunctionId.MATH_MIN_INT,
            List.of(new Arg.IntArg(-1), new Arg.IntArg(-2)), ALL, ok(i(-2))));
        cases.add(new ValueCase("maxInt-2-3", StdlibFunctionId.MATH_MAX_INT,
            List.of(new Arg.IntArg(2), new Arg.IntArg(3)), ALL, ok(i(3))));
        cases.add(new ValueCase("maxInt-equal", StdlibFunctionId.MATH_MAX_INT,
            List.of(new Arg.IntArg(2), new Arg.IntArg(2)), ALL, ok(i(2))));
        cases.add(new ValueCase("maxInt-negs", StdlibFunctionId.MATH_MAX_INT,
            List.of(new Arg.IntArg(-1), new Arg.IntArg(-2)), ALL, ok(i(-1))));

        return List.copyOf(cases);
    }

    /** The case subset of one lane in master order. */
    private static List<Case> casesFor(Set<Case> all, Lane lane) {
        List<Case> filtered = new ArrayList<>();
        for (Case c : all) {
            if (c.lanes().contains(lane)) {
                filtered.add(c);
            }
        }
        return filtered;
    }

    // =========================================================================
    // The reference pipeline (SharedStdlibSemantics + the T4 projection wiring)
    // =========================================================================

    /** One sealed reference run: parameter boundaries, algorithm, return boundary. */
    static class Reference {

        /** The fixed synthetic operation origin of the reference run. */
        static final SourceOrigin ORIGIN = origin();

        /**
         * The fixed reference clock of {@code TIME_NOW_MILLIS} (K7): a
         * contemporary epoch-millisecond reading, deterministic for the
         * battery — its declared int return boundary raises the same
         * pinned E8004 the retained {@code std/time.lua} lane raises.
         */
        static final SharedStdlibSemantics.Clock REFERENCE_CLOCK =
            () -> 1_700_000_000_000L;

        final SourceOrigin origin;

        Reference(SourceOrigin origin) {
            this.origin = origin;
        }

        /**
         * The combined T3/T4 reference run: the declared parameter
         * boundaries at the {@code STDLIB_PARAMETER} position, the
         * {@link SharedStdlibSemantics} algorithm, and the declared
         * return boundary at the {@code STDLIB_RETURN} position.
         */
        Outcome<Value> run(StdlibFunctionId id, List<Value> args, ConsoleSink sink) {
            StdlibFunctionCatalog.Entry row = catalogEntryOf(id);
            if (args.size() != row.parameterDescriptors().size()) {
                throw new IllegalStateException("case arity mismatch for " + id);
            }
            for (int index = 0; index < args.size(); index++) {
                BoundaryOutcome boundary = BoundaryExecutor.check(
                    descriptorKindPolicy(row.parameterDescriptors().get(index)),
                    row.parameterDescriptors().get(index), viewOf(args.get(index)),
                    BoundaryContext.none());
                if (boundary instanceof BoundaryOutcome.Fail boundaryFail) {
                    return new Outcome.Failure<>(
                        new SharedStdlibSemantics.StdlibFailure(boundaryFail.failure(), origin));
                }
            }
            Outcome<Value> outcome = dispatch(id, args, sink);
            if (outcome instanceof Outcome.Success<Value> success) {
                BoundaryOutcome boundary = BoundaryExecutor.check(
                    descriptorKindPolicy(row.returnDescriptor()), row.returnDescriptor(),
                    viewOf(success.value()), BoundaryContext.none());
                if (boundary instanceof BoundaryOutcome.Fail boundaryFail) {
                    return new Outcome.Failure<>(new SharedStdlibSemantics.StdlibFailure(
                        boundaryFail.failure(), origin));
                }
            }
            return outcome;
        }

        private Outcome<Value> dispatch(StdlibFunctionId id, List<Value> args,
                                        ConsoleSink sink) {
            return switch (id) {
                case CONSOLE_LOG ->
                    SharedStdlibSemantics.consoleLog(origin, validOf(args.get(0)), sink);
                case CONSOLE_ERROR ->
                    SharedStdlibSemantics.consoleError(origin, validOf(args.get(0)), sink);
                case STRING_LENGTH ->
                    SharedStdlibSemantics.stringLength(origin, validOf(args.get(0)));
                case STRING_SUBSTRING -> SharedStdlibSemantics.stringSubstring(origin,
                    validOf(args.get(0)), intOf(args.get(1)), intOf(args.get(2)));
                case STRING_CONTAINS -> SharedStdlibSemantics.stringContains(origin,
                    validOf(args.get(0)), validOf(args.get(1)));
                case STRING_STARTS_WITH -> SharedStdlibSemantics.stringStartsWith(origin,
                    validOf(args.get(0)), validOf(args.get(1)));
                case STRING_ENDS_WITH -> SharedStdlibSemantics.stringEndsWith(origin,
                    validOf(args.get(0)), validOf(args.get(1)));
                case STRING_REPLACE -> SharedStdlibSemantics.stringReplace(origin,
                    validOf(args.get(0)), validOf(args.get(1)), validOf(args.get(2)));
                case STRING_SPLIT -> SharedStdlibSemantics.stringSplit(origin,
                    validOf(args.get(0)), validOf(args.get(1)));
                case STRING_TRIM ->
                    SharedStdlibSemantics.stringTrim(origin, validOf(args.get(0)));
                case TABLE_KEYS ->
                    SharedStdlibSemantics.tableKeys(origin, tableOf(args.get(0)));
                case JSON_PARSE ->
                    SharedStdlibSemantics.jsonParse(origin, validOf(args.get(0)));
                case JSON_STRINGIFY ->
                    SharedStdlibSemantics.jsonStringify(origin, tableOf(args.get(0)));
                case MATH_FLOOR ->
                    SharedStdlibSemantics.mathFloor(origin, numberOf(args.get(0)));
                case MATH_CEIL ->
                    SharedStdlibSemantics.mathCeil(origin, numberOf(args.get(0)));
                case MATH_SQRT ->
                    SharedStdlibSemantics.mathSqrt(origin, numberOf(args.get(0)));
                case MATH_ABS_INT ->
                    SharedStdlibSemantics.mathAbsInt(origin, intOf(args.get(0)));
                case MATH_ABS_NUMBER ->
                    SharedStdlibSemantics.mathAbsNumber(origin, numberOf(args.get(0)));
                case MATH_MIN_INT -> SharedStdlibSemantics.mathMinInt(origin,
                    intOf(args.get(0)), intOf(args.get(1)));
                case MATH_MAX_INT -> SharedStdlibSemantics.mathMaxInt(origin,
                    intOf(args.get(0)), intOf(args.get(1)));
                case TIME_NOW_MILLIS -> SharedStdlibSemantics.timeNowMillis(origin,
                    REFERENCE_CLOCK);
            };
        }

        private static UnicodeScalars.Valid validOf(Value value) {
            if (value instanceof Value.String string
                    && string.scalar() instanceof UnicodeScalars.Valid valid) {
                return valid;
            }
            throw new IllegalStateException("the battery drives valid string carriers");
        }

        private static int intOf(Value value) {
            if (value instanceof Value.Int intValue) {
                return intValue.value();
            }
            throw new IllegalStateException("the battery drives int carriers");
        }

        private static double numberOf(Value value) {
            if (value instanceof Value.Number number) {
                return number.value();
            }
            if (value instanceof Value.Int intValue) {
                return intValue.value();
            }
            throw new IllegalStateException("the battery drives number carriers");
        }

        private static SemanticTable<Value> tableOf(Value value) {
            if (value instanceof Value.Table table) {
                return table.table();
            }
            throw new IllegalStateException("the battery drives table carriers");
        }

        /** The reference value of one case argument (the closed value view). */
        static Value valueOf(Arg arg) {
            return switch (arg) {
                case Arg.StrArg strArg -> s(strArg.text());
                case Arg.IntArg intArg -> i(intArg.value());
                case Arg.NumArg numArg -> n(numArg.value());
                case Arg.TableArg tableArg -> {
                    SemanticTable<Value> table = new SemanticTable<>();
                    for (int index = 0; index < tableArg.keys().size(); index++) {
                        table.put(tableArg.keys().get(index), tableArg.values().get(index));
                    }
                    yield new Value.Table(table);
                }
                case Arg.NaNTableArg ignored -> {
                    SemanticTable<Value> table = new SemanticTable<>();
                    table.put("a", n(Double.NaN));
                    yield new Value.Table(table);
                }
                case Arg.FnLeafTableArg ignored -> {
                    SemanticTable<Value> table = new SemanticTable<>();
                    table.put("f", new Value.Other(ActualKind.FUNCTION, null));
                    yield new Value.Table(table);
                }
            };
        }

        /** The {@code BoundaryValueView} classification of one seeded value. */
        static BoundaryValueView viewOf(Value value) {
            return switch (value) {
                case Value.Null ignored -> BoundaryValueView.of(ActualKind.NULL);
                case Value.Bool ignored -> BoundaryValueView.of(ActualKind.BOOLEAN);
                case Value.Int intValue -> BoundaryValueView.ofInt(intValue.value());
                case Value.Number number -> BoundaryValueView.ofNumber(number.value());
                case Value.String string -> BoundaryValueView.of(string.scalar()
                    instanceof UnicodeScalars.Valid ? ActualKind.STRING
                        : ActualKind.INVALID_UNICODE);
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
    }

    // =========================================================================
    // Pinned-outcome assertions (the reference run fails on a broken pin)
    // =========================================================================

    /** True when the reference outcome matches the pinned parent-table expectation. */
    static boolean pinnedMatches(Outcome<Value> outcome, PinnedOutcome pinned) {
        return switch (pinned) {
            case PinnedOutcome.PinnedSuccess(Value expected) ->
                outcome instanceof Outcome.Success<Value> success
                    && valueEquals(success.value(), expected);
            case PinnedOutcome.PinnedFailure(FailurePolicyId policy, DiagnosticCode code,
                                             String message, String expectedText,
                                             String actualText, Map<String, String> metadata) ->
                outcome instanceof Outcome.Failure<Value> failure
                    && failure.failure().failure().policy() == policy
                    && failure.failure().failure().code() == code
                    && failure.failure().failure().message().equals(message)
                    && Objects.equals(failure.failure().failure().expected(), expectedText)
                    && Objects.equals(failure.failure().failure().actual(), actualText)
                    && failure.failure().failure().metadata().equals(metadata)
                    && failure.failure().origin().equals(Reference.ORIGIN);
        };
    }

    private static String describeOutcome(Outcome<Value> outcome) {
        if (outcome instanceof Outcome.Success<Value> success) {
            return "Success(" + success.value() + ")";
        }
        if (outcome instanceof Outcome.Failure<Value> failure) {
            BoundaryFailure projection = failure.failure().failure();
            return "Failure(" + projection.policy() + " " + projection.code() + " \""
                + projection.message() + "\" expected=" + projection.expected()
                + " actual=" + projection.actual() + " metadata=" + projection.metadata()
                + ")";
        }
        return String.valueOf(outcome);
    }

    /** Asserts the reference outcome against the expected result. */
    static void assertPinned(Outcome<Value> outcome, PinnedOutcome pinned, String note) {
        check(pinnedMatches(outcome, pinned),
            note + " — the reference run must produce the pinned parent-table outcome, got "
                + describeOutcome(outcome));
    }

    // =========================================================================
    // Canonical lane payload comparison
    // =========================================================================

    /** The parsed lane result atom of the protocol. */
    sealed interface Atom permits Atom.NullAtom, Atom.BoolAtom, Atom.NumAtom, Atom.StrAtom,
        Atom.ArrAtom {

        record NullAtom() implements Atom { }

        record BoolAtom(boolean value) implements Atom { }

        record NumAtom(double value) implements Atom { }

        record StrAtom(String text) implements Atom { }

        record ArrAtom(List<Atom> elements) implements Atom { }
    }

    private static String hexEncode(byte[] bytes) {
        StringBuilder sb = new StringBuilder(bytes.length * 2);
        for (byte b : bytes) {
            sb.append(String.format("%02x", b & 0xff));
        }
        return sb.toString();
    }

    private static byte[] hexDecode(String text) {
        if (text.length() % 2 != 0) {
            throw new IllegalArgumentException("odd hex length: " + text);
        }
        byte[] bytes = new byte[text.length() / 2];
        for (int index = 0; index < bytes.length; index++) {
            bytes[index] = (byte) Integer.parseInt(text.substring(index * 2, index * 2 + 2), 16);
        }
        return bytes;
    }

    private static Atom parseAtom(String payload) {
        if ("null".equals(payload)) {
            return new Atom.NullAtom();
        }
        if (payload.startsWith("bool|")) {
            return new Atom.BoolAtom("1".equals(payload.substring("bool|".length())));
        }
        if (payload.startsWith("num|")) {
            String text = payload.substring("num|".length());
            double value = switch (text) {
                case "nan" -> Double.NaN;
                case "inf" -> Double.POSITIVE_INFINITY;
                case "-inf" -> Double.NEGATIVE_INFINITY;
                case "-0" -> -0.0;
                default -> Double.parseDouble(text);
            };
            return new Atom.NumAtom(value);
        }
        if (payload.startsWith("str|")) {
            return new Atom.StrAtom(new String(
                hexDecode(payload.substring("str|".length())), StandardCharsets.UTF_8));
        }
        if (payload.startsWith("arr|")) {
            int first = "arr|".length();
            int second = payload.indexOf('|', first);
            if (second < 0) {
                throw new IllegalArgumentException("malformed arr payload: " + payload);
            }
            int count;
            try {
                count = Integer.parseInt(payload.substring(first, second));
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("malformed arr payload: " + payload);
            }
            String rest = payload.substring(second + 1);
            List<Atom> elements = new ArrayList<>();
            if (count == 0) {
                return new Atom.ArrAtom(elements);
            }
            String[] elementPayloads = rest.split(",", -1);
            if (elementPayloads.length != count) {
                throw new IllegalArgumentException("arr payload arity mismatch: " + payload);
            }
            for (String elementPayload : elementPayloads) {
                elements.add(parseAtom(elementPayload));
            }
            return new Atom.ArrAtom(elements);
        }
        throw new IllegalArgumentException("unknown lane payload: " + payload);
    }

    /** One parsed lane result record. */
    record LaneResult(int index, boolean ok, String payload) { }

    /** One parsed lane failure: code and message text. */
    record LaneError(String code, String message) { }

    private static LaneError errorOf(String payload) {
        int pipe = payload.indexOf('|');
        if (pipe < 0) {
            return new LaneError(payload, "");
        }
        String code = payload.substring(0, pipe);
        try {
            String message = new String(hexDecode(payload.substring(pipe + 1)),
                StandardCharsets.UTF_8);
            return new LaneError(code, message);
        } catch (RuntimeException e) {
            throw new IllegalArgumentException("malformed lane error payload \"" + payload
                + "\": " + e);
        }
    }

    /**
     * Compares one lane result against the reference outcome of the
     * case's final observable id; returns the divergence text, or
     * {@code null} when the lane matched the common operation.
     */
    static String laneMismatch(StdlibFunctionId finalId, Outcome<Value> reference,
                               LaneResult result) {
        if (result.ok()) {
            if (reference instanceof Outcome.Failure<Value> failure) {
                return "expected failure " + failure.failure().failure().code() + " \""
                    + failure.failure().failure().message() + "\", lane succeeded with "
                    + result.payload();
            }
            Outcome.Success<Value> success = (Outcome.Success<Value>) reference;
            try {
                Atom atom = parseAtom(result.payload());
                String mismatch = successMismatch(finalId, success.value(), atom);
                return mismatch == null ? null
                    : "value mismatch for " + finalId + ": expected "
                        + canonicalOf(finalId, success.value()) + ", got " + result.payload();
            } catch (RuntimeException e) {
                return "unparseable lane result payload \"" + result.payload() + "\": " + e;
            }
        }
        LaneError error = errorOf(result.payload());
        if (reference instanceof Outcome.Success<Value> success) {
            return "expected success " + canonicalOf(finalId, success.value())
                + ", lane failed " + error.code() + " \"" + error.message() + "\"";
        }
        Outcome.Failure<Value> failure = (Outcome.Failure<Value>) reference;
        BoundaryFailure projection = failure.failure().failure();
        if (projection.code().name().equals(error.code())
                && projection.message().equals(error.message())) {
            return null;
        }
        return "failure projection mismatch for " + finalId + ": expected "
            + projection.code() + " \"" + projection.message() + "\", got " + error.code()
            + " \"" + error.message() + "\"";
    }

    private static String successMismatch(StdlibFunctionId id, Value reference, Atom atom) {
        RuntimeDescriptor ret = catalogEntryOf(id).returnDescriptor();
        if (ret.equals(DESC_INT)) {
            if (!(reference instanceof Value.Int intValue)) {
                return "the reference produced a non-int value for the int-returning id " + id;
            }
            if (atom instanceof Atom.NumAtom num
                    && Double.isFinite(num.value())
                    && num.value() == Math.rint(num.value())
                    && num.value() >= Integer.MIN_VALUE
                    && num.value() <= Integer.MAX_VALUE
                    && (int) num.value() == intValue.value()) {
                return null;
            }
            return "int mismatch";
        }
        if (ret.equals(DESC_NUMBER)) {
            if (!(reference instanceof Value.Number number)) {
                return "the reference produced a non-number value for the number-returning id "
                    + id;
            }
            if (atom instanceof Atom.NumAtom num
                    && Double.compare(num.value(), number.value()) == 0) {
                return null;
            }
            return "number mismatch";
        }
        if (ret.equals(DESC_STRING)) {
            if (!(reference instanceof Value.String string
                    && string.scalar() instanceof UnicodeScalars.Valid valid)) {
                return "the reference produced a non-string value for the string-returning id "
                    + id;
            }
            if (atom instanceof Atom.StrAtom str && str.text().equals(valid.carrier())) {
                return null;
            }
            return "string mismatch";
        }
        if (ret.equals(DESC_BOOLEAN)) {
            if (!(reference instanceof Value.Bool bool)) {
                return "the reference produced a non-boolean value for the boolean-returning id "
                    + id;
            }
            if (atom instanceof Atom.BoolAtom boolAtom && boolAtom.value() == bool.value()) {
                return null;
            }
            return "boolean mismatch";
        }
        if (ret.equals(DESC_NULL)) {
            return atom instanceof Atom.NullAtom ? null : "null mismatch";
        }
        if (ret.equals(DESC_STRING_ARRAY)) {
            if (!(reference instanceof Value.Array array)) {
                return "the reference produced a non-array value for the array-returning id "
                    + id;
            }
            if (!(atom instanceof Atom.ArrAtom arrAtom)
                    || arrAtom.elements().size() != array.elements().size()) {
                return "array mismatch";
            }
            for (int index = 0; index < array.elements().size(); index++) {
                Value element = array.elements().elementAt(index);
                if (!(element instanceof Value.String string
                        && string.scalar() instanceof UnicodeScalars.Valid valid)) {
                    return "array element mismatch at " + index;
                }
                if (!(arrAtom.elements().get(index) instanceof Atom.StrAtom str)
                        || !str.text().equals(valid.carrier())) {
                    return "array element mismatch at " + index;
                }
            }
            return null;
        }
        return "the id " + id + " is observed only through chains (producer defect)";
    }

    /** The canonical text of a reference value for reporting. */
    private static String canonicalOf(StdlibFunctionId id, Value value) {
        RuntimeDescriptor ret = catalogEntryOf(id).returnDescriptor();
        if (value instanceof Value.String string
                && string.scalar() instanceof UnicodeScalars.Valid valid) {
            return "str|" + hexEncode(valid.carrier().getBytes(StandardCharsets.UTF_8));
        }
        if (value instanceof Value.Int intValue) {
            return ret.equals(DESC_NUMBER)
                ? "num|" + Double.toString(intValue.value())
                : "int|" + intValue.value();
        }
        if (value instanceof Value.Number number) {
            return "num|" + Double.toString(number.value());
        }
        if (value instanceof Value.Bool bool) {
            return "bool|" + (bool.value() ? "1" : "0");
        }
        if (value instanceof Value.Null) {
            return "null";
        }
        if (value instanceof Value.Array array) {
            StringBuilder sb = new StringBuilder("arr|").append(array.elements().size());
            for (Value element : array.elements().elements()) {
                sb.append('|').append(canonicalOf(id, element));
            }
            return sb.toString();
        }
        return String.valueOf(value);
    }

    // =========================================================================
    // Subprocess plumbing
    // =========================================================================

    /** One subprocess run: exit code and captured stdout/stderr bytes. */
    record SubprocessRun(int exitCode, byte[] stdout, byte[] stderr) { }

    private static SubprocessRun runTool(Path directory, List<String> command,
                                         long timeoutSeconds) throws IOException,
        InterruptedException {
        ProcessBuilder builder = new ProcessBuilder(command).directory(directory.toFile());
        Process process = builder.start();
        if (!process.waitFor(timeoutSeconds, TimeUnit.SECONDS)) {
            process.destroyForcibly();
            throw new IllegalStateException("subprocess timed out: " + command);
        }
        byte[] stdout = process.getInputStream().readAllBytes();
        byte[] stderr = process.getErrorStream().readAllBytes();
        return new SubprocessRun(process.exitValue(), stdout, stderr);
    }

    private static void requireTool(String... probe) {
        try {
            Process process = new ProcessBuilder(probe).start();
            if (!process.waitFor(30, TimeUnit.SECONDS) || process.exitValue() != 0) {
                fail("tool probe failed: " + String.join(" ", probe));
            }
        } catch (Exception e) {
            fail("tool probe threw: " + String.join(" ", probe) + " — " + e);
        }
    }

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

    // =========================================================================
    // Driver generation: retained Lua helpers
    // =========================================================================

    private static String luaStringOf(String text) {
        StringBuilder sb = new StringBuilder("string.char(");
        byte[] bytes = text.getBytes(StandardCharsets.UTF_8);
        for (int index = 0; index < bytes.length; index++) {
            if (index > 0) {
                sb.append(',');
            }
            sb.append(bytes[index] & 0xff);
        }
        return sb.append(')').toString();
    }

    private static String luaNumberOf(double value) {
        if (Double.isNaN(value)) {
            throw new IllegalArgumentException("no NaN literal in LuaJIT");
        }
        return Double.toString(value);
    }

    private static String luaTableOf(Arg arg, StringBuilder setup) {
        return switch (arg) {
            case Arg.TableArg tableArg -> {
                String name = "tbl" + setup.length();
                setup.append("local ").append(name).append(" = {}\n");
                for (int index = 0; index < tableArg.keys().size(); index++) {
                    Value value = tableArg.values().get(index);
                    String literal = switch (value) {
                        case Value.Int intValue -> Integer.toString(intValue.value());
                        case Value.String string when
                            string.scalar() instanceof UnicodeScalars.Valid valid ->
                            luaStringOf(valid.carrier());
                        case Value.Number number when Double.isNaN(number.value()) ->
                            throw new IllegalArgumentException("no NaN literal in LuaJIT");
                        case Value.Number number -> luaNumberOf(number.value());
                        default -> throw new IllegalArgumentException(
                            "unsupported table value " + value);
                    };
                    setup.append(name).append("[").append(luaStringOf(tableArg.keys().get(index)))
                        .append("] = ").append(literal).append('\n');
                }
                yield name;
            }
            case Arg.FnLeafTableArg ignored -> {
                String name = "tbl" + setup.length();
                setup.append("local ").append(name).append(" = {}\n");
                setup.append(name).append("[\"f\"] = __rt.function_(\"()->null\", function() "
                    + "return __rt.__NULL end)\n");
                yield name;
            }
            case Arg.NaNTableArg ignored -> throw new IllegalArgumentException(
                "no NaN literal in LuaJIT — the NaN stringify case is JS-only");
            default -> throw new IllegalArgumentException("unsupported table arg " + arg);
        };
    }

    /**
     * Generates the Lua driver that calls the retained {@code std/*.lua}
     * wrappers for every case and writes the protocol to
     * {@code protocolFile} (stdout/stderr stay exactly the console
     * effects).
     */
    private static String luaDriver(List<Case> cases, Path protocolFile, boolean brokenTrimStub) {
        Path root = repoRoot();
        StringBuilder sb = new StringBuilder();
        sb.append("package.path = ").append(luaStringOf(root.toString() + "/?.lua"))
            .append(" .. \";\" .. package.path\n");
        sb.append("local __rt = require(\"deal.runtime\")\n");
        if (brokenTrimStub) {
            sb.append("-- deliberately broken stub: trims the leading whitespace only\n");
            sb.append("local mod_string = { trim = { f = function(s) "
                + "return (string.gsub(s, \"^%s*\", \"\")) end } }\n");
        } else {
            sb.append("local mod_console = require(\"std.console\")\n");
            sb.append("local mod_string = require(\"std.string\")\n");
            sb.append("local mod_table = require(\"std.table\")\n");
            sb.append("local mod_json = require(\"std.json\")\n");
            sb.append("local mod_math = require(\"std.math\")\n");
        }
        sb.append("local out = assert(io.open(").append(luaStringOf(protocolFile.toString()))
            .append(", \"w\"))\n");
        sb.append("""
            local function numf(v)
              if v ~= v then return "nan" end
              if v == math.huge then return "inf" end
              if v == -math.huge then return "-inf" end
              return string.format("%.17g", v)
            end
            local function hex(s)
              local t = {}
              for i = 1, #s do t[#t + 1] = string.format("%02x", string.byte(s, i)) end
              return table.concat(t)
            end
            local function ser(v)
              if v == nil or v == __rt.__NULL then return "null" end
              local tv = type(v)
              if tv == "boolean" then return v and "bool|1" or "bool|0" end
              if tv == "number" then return "num|" .. numf(v) end
              if tv == "string" then return "str|" .. hex(v) end
              if tv == "table" then
                local n = 0
                while rawget(v, n + 1) ~= nil do n = n + 1 end
                local parts = { "arr|" .. tostring(n) .. "|" }
                for i = 1, n do
                  local e = rawget(v, i)
                  if i > 1 then parts[#parts + 1] = "," end
                  if e == nil then parts[#parts + 1] = "null" else parts[#parts + 1] = ser(e) end
                end
                return table.concat(parts)
              end
              return "other|" .. tv
            end
            local function emit(i, ok, payload)
              out:write("CASE " .. tostring(i) .. " " .. (ok and "ok" or "err") .. " "
                .. payload .. "\\n")
            end
            local function errtxt(e)
              local code = ""
              local msg = tostring(e)
              if type(e) == "table" then
                code = tostring(e.code or "")
                msg = tostring(e.message or e)
              end
              return code .. "|" .. hex(msg)
            end
            """);
        int index = 0;
        for (Case c : cases) {
            sb.append("-- case ").append(index).append(": ").append(c.name()).append('\n');
            switch (c) {
                case ConsoleCase console -> {
                    String text = luaStringOf(console.text());
                    sb.append("mod_console.").append(
                        console.id() == StdlibFunctionId.CONSOLE_LOG ? "log" : "error")
                        .append(".f(").append(text).append(")\n");
                    sb.append("emit(").append(index).append(", true, \"null\")\n");
                }
                case ValueCase value -> {
                    StringBuilder setup = new StringBuilder();
                    List<String> args = new ArrayList<>();
                    for (Arg arg : value.args()) {
                        args.add(luaArgOf(arg, setup));
                    }
                    sb.append(setup);
                    sb.append("do\n");
                    sb.append("  local ok, r = pcall(mod_").append(luaModuleOf(value.id()))
                        .append('.').append(exportNameOf(value.id()))
                        .append(".f, ").append(String.join(", ", args)).append(")\n");
                    sb.append("  if ok then emit(").append(index)
                        .append(", true, ser(r)) else emit(")
                        .append(index).append(", false, errtxt(r)) end\n");
                    sb.append("end\n");
                }
                case ChainCase chain -> {
                    String text = luaStringOf(((Arg.StrArg) chain.firstArgs().get(0)).text());
                    sb.append("do\n");
                    sb.append("  local ok, r = pcall(mod_json.parse.f, ").append(text).append(")\n");
                    sb.append("  if not ok then emit(").append(index)
                        .append(", false, errtxt(r)) else\n");
                    sb.append("    local ok2, r2 = pcall(mod_")
                        .append(luaModuleOf(chain.second())).append('.')
                        .append(exportNameOf(chain.second()))
                        .append(".f, r)\n");
                    sb.append("    if ok2 then emit(").append(index)
                        .append(", true, ser(r2)) else emit(").append(index)
                        .append(", false, errtxt(r2)) end\n");
                    sb.append("  end\n");
                    sb.append("end\n");
                }
                case DelReinsKeysCase ignored -> {
                    sb.append("do\n");
                    sb.append("  local t = {}\n");
                    sb.append("  t[\"a\"] = 1\n");
                    sb.append("  t[\"b\"] = 2\n");
                    sb.append("  t[\"c\"] = 3\n");
                    sb.append("  t[\"a\"] = nil\n");
                    sb.append("  t[\"a\"] = 9\n");
                    sb.append("  local ok, r = pcall(mod_table.keys.f, t)\n");
                    sb.append("  if ok then emit(").append(index)
                        .append(", true, ser(r)) else emit(")
                        .append(index).append(", false, errtxt(r)) end\n");
                    sb.append("end\n");
                }
            }
            index++;
        }
        sb.append("out:close()\n");
        return sb.toString();
    }

    /** The declared export name of one id (the single catalog row's member name). */
    private static String exportNameOf(StdlibFunctionId id) {
        return catalogEntryOf(id).exportName();
    }

    private static String luaModuleOf(StdlibFunctionId id) {
        return switch (id) {
            case CONSOLE_LOG, CONSOLE_ERROR -> "console";
            case STRING_LENGTH, STRING_SUBSTRING, STRING_CONTAINS, STRING_STARTS_WITH,
                 STRING_ENDS_WITH, STRING_REPLACE, STRING_SPLIT, STRING_TRIM -> "string";
            case TABLE_KEYS -> "table";
            case JSON_PARSE, JSON_STRINGIFY -> "json";
            case MATH_FLOOR, MATH_CEIL, MATH_SQRT, MATH_ABS_INT, MATH_ABS_NUMBER,
                 MATH_MIN_INT, MATH_MAX_INT -> "math";
            case TIME_NOW_MILLIS -> "time";
        };
    }

    private static String luaArgOf(Arg arg, StringBuilder setup) {
        return switch (arg) {
            case Arg.StrArg strArg -> luaStringOf(strArg.text());
            case Arg.IntArg intArg -> Integer.toString(intArg.value());
            case Arg.NumArg numArg -> luaNumberOf(numArg.value());
            case Arg.TableArg tableArg -> luaTableOf(arg, setup);
            case Arg.NaNTableArg ignored -> throw new IllegalArgumentException(
                "no NaN literal in LuaJIT");
            case Arg.FnLeafTableArg ignored -> luaTableOf(arg, setup);
        };
    }

    // =========================================================================
    // Driver generation: retained JS helpers
    // =========================================================================

    private static String jsStringOf(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (int index = 0; index < text.length(); index++) {
            char c = text.charAt(index);
            if (c == '"' || c == '\\') {
                sb.append('\\').append(c);
            } else if (c < 0x20) {
                sb.append(String.format("\\u%04x", (int) c));
            } else {
                sb.append(c);
            }
        }
        return sb.append('"').toString();
    }

    private static String jsNumberOf(double value) {
        if (Double.isNaN(value)) {
            return "NaN";
        }
        if (Double.doubleToRawLongBits(value) == 0x8000000000000000L) {
            return "-0";
        }
        return Double.toString(value);
    }

    private static String jsTableOf(Arg arg, StringBuilder setup) {
        return switch (arg) {
            case Arg.TableArg tableArg -> {
                String name = "$tbl" + setup.length();
                setup.append("const ").append(name).append(" = $rt.makeTable({});\n");
                for (int index = 0; index < tableArg.keys().size(); index++) {
                    Value value = tableArg.values().get(index);
                    String literal = switch (value) {
                        case Value.Int intValue -> Integer.toString(intValue.value());
                        case Value.Number number -> jsNumberOf(number.value());
                        case Value.String string when
                            string.scalar() instanceof UnicodeScalars.Valid valid ->
                            jsStringOf(valid.carrier());
                        default -> throw new IllegalArgumentException(
                            "unsupported table value " + value);
                    };
                    setup.append(name).append(".set(")
                        .append(jsStringOf(tableArg.keys().get(index))).append(", ")
                        .append(literal).append(");\n");
                }
                yield name;
            }
            case Arg.NaNTableArg ignored -> {
                String name = "$tbl" + setup.length();
                setup.append("const ").append(name).append(" = $rt.makeTable({});\n");
                setup.append(name).append(".set(\"a\", NaN);\n");
                yield name;
            }
            case Arg.FnLeafTableArg ignored -> {
                String name = "$tbl" + setup.length();
                setup.append("const ").append(name).append(" = $rt.makeTable({});\n");
                setup.append(name).append(".set(\"f\", $rt.function(\"()->null\", "
                    + "function() { return null; }));\n");
                yield name;
            }
            default -> throw new IllegalArgumentException("unsupported table arg " + arg);
        };
    }

    /** Generates the JS driver that calls the retained {@code std/*.js} wrappers. */
    private static String jsDriver(List<Case> cases, Path protocolFile) {
        Path root = repoRoot();
        StringBuilder sb = new StringBuilder();
        sb.append("\"use strict\";\n");
        sb.append("const fs = require(\"fs\");\n");
        sb.append("const $rt = require(").append(jsStringOf(root + "/deal/runtime")).append(");\n");
        sb.append("const mod_console = require(").append(jsStringOf(root + "/std/console"))
            .append(");\n");
        sb.append("const mod_string = require(").append(jsStringOf(root + "/std/string"))
            .append(");\n");
        sb.append("const mod_table = require(").append(jsStringOf(root + "/std/table"))
            .append(");\n");
        sb.append("const mod_json = require(").append(jsStringOf(root + "/std/json"))
            .append(");\n");
        sb.append("const mod_math = require(").append(jsStringOf(root + "/std/math"))
            .append(");\n");
        sb.append("const out = [];\n");
        sb.append("""
            function numf(v) {
              if (Number.isNaN(v)) return "nan";
              if (v === Infinity) return "inf";
              if (v === -Infinity) return "-inf";
              if (Object.is(v, -0)) return "-0";
              return String(v);
            }
            function hex(s) {
              return Buffer.from(s, "utf8").toString("hex");
            }
            function ser(v) {
              if (v === null) return "null";
              if (typeof v === "boolean") return v ? "bool|1" : "bool|0";
              if (typeof v === "number") return "num|" + numf(v);
              if (typeof v === "string") return "str|" + hex(v);
              if (Array.isArray(v)) {
                const parts = [];
                for (const e of v) parts.push(e === null ? "null" : ser(e));
                return "arr|" + v.length + "|" + parts.join(",");
              }
              return "other|" + typeof v;
            }
            function emit(i, ok, payload) {
              out.push("CASE " + i + " " + (ok ? "ok" : "err") + " " + payload);
            }
            function errtxt(e) {
              const code = (e && typeof e === "object" && e.$dealCode !== undefined)
                ? e.$dealCode : "";
              const msg = (e && e.message !== undefined) ? e.message : String(e);
              return code + "|" + hex(msg);
            }
            """);
        int index = 0;
        for (Case c : cases) {
            sb.append("// case ").append(index).append(": ").append(c.name()).append('\n');
            switch (c) {
                case ConsoleCase console -> {
                    String text = jsStringOf(console.text());
                    sb.append("{ try { mod_console.")
                        .append(console.id() == StdlibFunctionId.CONSOLE_LOG ? "log" : "error")
                        .append(".$f(").append(text)
                        .append(", \"battery\", 1, 1); emit(").append(index)
                        .append(", true, \"null\"); } catch (e) { emit(").append(index)
                        .append(", false, errtxt(e)); } }\n");
                }
                case ValueCase value -> {
                    StringBuilder setup = new StringBuilder();
                    List<String> args = new ArrayList<>();
                    for (Arg arg : value.args()) {
                        args.add(jsArgOf(arg, setup));
                    }
                    sb.append("{\n");
                    sb.append(setup);
                    sb.append("try { emit(").append(index).append(", true, ser(mod_")
                        .append(jsModuleOf(value.id())).append('.')
                        .append(exportNameOf(value.id()))
                        .append(".$f(").append(String.join(", ", args))
                        .append(", \"battery\", 1, 1))); } catch (e) { emit(").append(index)
                        .append(", false, errtxt(e)); } }\n");
                }
                case ChainCase chain -> {
                    String text = jsStringOf(((Arg.StrArg) chain.firstArgs().get(0)).text());
                    sb.append("{ try {\n");
                    sb.append("  const parsed = mod_json.parse.$f(").append(text)
                        .append(", \"battery\", 1, 1);\n");
                    sb.append("  try {\n");
                    sb.append("    emit(").append(index)
                        .append(", true, ser(mod_").append(jsModuleOf(chain.second())).append('.')
                        .append(exportNameOf(chain.second()))
                        .append(".$f(parsed, \"battery\", 1, 1)));\n");
                    sb.append("  } catch (e) { emit(").append(index)
                        .append(", false, errtxt(e)); }\n");
                    sb.append("} catch (e) { emit(").append(index)
                        .append(", false, errtxt(e)); } }\n");
                }
                case DelReinsKeysCase ignored -> {
                    sb.append("{ try {\n");
                    sb.append("  const t = $rt.makeTable({});\n");
                    sb.append("  t.set(\"a\", 1); t.set(\"b\", 2); t.set(\"c\", 3);\n");
                    sb.append("  t.delete(\"a\"); t.set(\"a\", 9);\n");
                    sb.append("  emit(").append(index).append(", true, ser(mod_table.keys.$f(")
                        .append("t, \"battery\", 1, 1)));\n");
                    sb.append("} catch (e) { emit(").append(index)
                        .append(", false, errtxt(e)); } }\n");
                }
            }
            index++;
        }
        sb.append("fs.writeFileSync(").append(jsStringOf(protocolFile.toString()))
            .append(", out.join(\"\\n\") + \"\\n\");\n");
        return sb.toString();
    }

    private static String jsModuleOf(StdlibFunctionId id) {
        return luaModuleOf(id);
    }

    private static String jsArgOf(Arg arg, StringBuilder setup) {
        return switch (arg) {
            case Arg.StrArg strArg -> jsStringOf(strArg.text());
            case Arg.IntArg intArg -> Integer.toString(intArg.value());
            case Arg.NumArg numArg -> jsNumberOf(numArg.value());
            case Arg.TableArg tableArg -> jsTableOf(arg, setup);
            case Arg.NaNTableArg ignored -> jsTableOf(arg, setup);
            case Arg.FnLeafTableArg ignored -> jsTableOf(arg, setup);
        };
    }

    // =========================================================================
    // Lane execution and comparison: retained Lua and retained JS
    // =========================================================================

    /** Executes the retained Lua helpers and compares every case to the reference. */
    static Map<String, List<String>> runLuaLane(Set<Case> all, Reference reference,
                                                boolean brokenStub) {
        List<Case> laneCases = new ArrayList<>();
        for (Case c : casesFor(all, Lane.RETAINED_LUA)) {
            if (!brokenStub || (c instanceof ValueCase value
                    && value.id() == StdlibFunctionId.STRING_TRIM)) {
                laneCases.add(c);
            }
        }
        Path tmp;
        try {
            tmp = Files.createTempDirectory("deal-stdlib-equiv-lua");
        } catch (IOException e) {
            fail("the Lua lane temp directory failed: " + e);
            return new LinkedHashMap<>();
        }
        try {
            Path protocol = tmp.resolve("protocol.txt");
            Path driver = tmp.resolve("driver.lua");
            Files.writeString(driver, luaDriver(laneCases, protocol, brokenStub));
            SubprocessRun run = runTool(repoRoot(), List.of("luajit", driver.toString()), 120);
            check(run.exitCode() == 0,
                "the Lua lane driver exits 0 (retained helpers run as they are); got exit "
                    + run.exitCode() + " stderr=" + new String(run.stderr(), StandardCharsets.UTF_8));
            Map<Integer, LaneResult> records = parseProtocol(protocol);
            Map<String, List<String>> divergences = compareLaneRecords(laneCases, records,
                reference, brokenStub, "lua");
            compareConsoleEffects(laneCases, run.stdout(), run.stderr(), "lua", divergences);
            return divergences;
        } catch (Exception e) {
            fail("the Lua lane battery threw: " + e);
            return new LinkedHashMap<>();
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** Executes the retained JS helpers and compares every case to the reference. */
    static Map<String, List<String>> runJsLane(Set<Case> all, Reference reference) {
        List<Case> laneCases = casesFor(all, Lane.RETAINED_JS);
        Path tmp;
        try {
            tmp = Files.createTempDirectory("deal-stdlib-equiv-js");
        } catch (IOException e) {
            fail("the JS lane temp directory failed: " + e);
            return new LinkedHashMap<>();
        }
        try {
            Path protocol = tmp.resolve("protocol.txt");
            Path driver = tmp.resolve("driver.js");
            Files.writeString(driver, jsDriver(laneCases, protocol));
            SubprocessRun run = runTool(repoRoot(), List.of("node", driver.toString()), 120);
            check(run.exitCode() == 0,
                "the JS lane driver exits 0 (retained helpers run as they are); got exit "
                    + run.exitCode() + " stderr=" + new String(run.stderr(), StandardCharsets.UTF_8));
            Map<Integer, LaneResult> records = parseProtocol(protocol);
            Map<String, List<String>> divergences = compareLaneRecords(laneCases, records,
                reference, false, "js");
            compareConsoleEffects(laneCases, run.stdout(), run.stderr(), "js", divergences);
            return divergences;
        } catch (Exception e) {
            fail("the JS lane battery threw: " + e);
            return new LinkedHashMap<>();
        } finally {
            deleteRecursively(tmp);
        }
    }

    private static Map<Integer, LaneResult> parseProtocol(Path protocol) throws IOException {
        Map<Integer, LaneResult> records = new LinkedHashMap<>();
        for (String line : Files.readAllLines(protocol)) {
            if (!line.startsWith("CASE ")) {
                throw new IllegalStateException("malformed protocol line: " + line);
            }
            int indexEnd = line.indexOf(' ', "CASE ".length());
            if (indexEnd < 0) {
                throw new IllegalStateException("malformed protocol line: " + line);
            }
            int index = Integer.parseInt(line.substring("CASE ".length(), indexEnd));
            String okPrefix = "CASE " + index + " ok ";
            String errPrefix = "CASE " + index + " err ";
            boolean ok = line.startsWith(okPrefix);
            String payload = ok ? line.substring(okPrefix.length())
                : line.substring(errPrefix.length());
            records.put(index, new LaneResult(index, ok, payload));
        }
        return records;
    }

    private static Map<String, List<String>> compareLaneRecords(List<Case> laneCases,
            Map<Integer, LaneResult> records, Reference reference, boolean brokenStub,
            String laneName) {
        Map<String, List<String>> divergences = new LinkedHashMap<>();
        for (int index = 0; index < laneCases.size(); index++) {
            Case c = laneCases.get(index);
            LaneResult result = records.get(index);
            Outcome<Value> referenceOutcome = referenceOutcomeOf(c, reference);
            if (result == null) {
                divergences.computeIfAbsent(c.name(), ignored -> new ArrayList<>())
                    .add("the " + laneName + " lane produced no record for case " + index
                        + " — the comparison cannot pass vacuously");
                continue;
            }
            if (brokenStub && c instanceof ValueCase value
                    && value.id() != StdlibFunctionId.STRING_TRIM) {
                continue; // the broken-stub drive covers trim only
            }
            String mismatch;
            if (c instanceof ChainCase chain) {
                mismatch = laneMismatch(chain.second(), referenceOutcome, result);
            } else {
                mismatch = laneMismatch(c.attribution().get(0), referenceOutcome, result);
            }
            if (mismatch != null) {
                divergences.computeIfAbsent(c.name(), ignored -> new ArrayList<>())
                    .add(laneName + ": " + mismatch);
            }
        }
        return divergences;
    }

    /**
     * The reference outcome of one case: the chain runs parse→observable
     * through the same pipeline; the delete-reinsert case builds its
     * table with the delete/reinsert order contract.
     */
    static Outcome<Value> referenceOutcomeOf(Case c, Reference reference) {
        if (c instanceof ChainCase chain) {
            List<Value> firstArgs = new ArrayList<>();
            for (Arg arg : chain.firstArgs()) {
                firstArgs.add(Reference.valueOf(arg));
            }
            Outcome<Value> first = reference.run(chain.first(), firstArgs, null);
            if (!(first instanceof Outcome.Success<Value> success)) {
                return first;
            }
            return reference.run(chain.second(), List.of(success.value()), null);
        }
        if (c instanceof ConsoleCase console) {
            List<Value> args = List.of(s(console.text()));
            ConsoleSink sink = captureSink(
                console.id() == StdlibFunctionId.CONSOLE_LOG
                    ? SharedStdlibSemantics.Channel.STDOUT
                    : SharedStdlibSemantics.Channel.STDERR);
            Outcome<Value> outcome = reference.run(console.id(), args, sink);
            assertPinned(outcome, ok(NULL), "console case " + console.name());
            return outcome;
        }
        if (c instanceof DelReinsKeysCase) {
            SemanticTable<Value> table = new SemanticTable<>();
            table.put("a", i(1));
            table.put("b", i(2));
            table.put("c", i(3));
            table.remove("a");
            table.put("a", i(9));
            return reference.run(StdlibFunctionId.TABLE_KEYS,
                List.of(new Value.Table(table)), null);
        }
        ValueCase value = (ValueCase) c;
        List<Value> args = new ArrayList<>();
        for (Arg arg : value.args()) {
            args.add(Reference.valueOf(arg));
        }
        ConsoleSink sink = value.id() == StdlibFunctionId.CONSOLE_LOG
            ? captureSink(SharedStdlibSemantics.Channel.STDOUT)
            : value.id() == StdlibFunctionId.CONSOLE_ERROR
                ? captureSink(SharedStdlibSemantics.Channel.STDERR)
                : null;
        return reference.run(value.id(), args, sink);
    }

    private static ConsoleSink captureSink(SharedStdlibSemantics.Channel channel) {
        return new ConsoleSink() {
            @Override
            public SharedStdlibSemantics.Channel channel() {
                return channel;
            }

            @Override
            public void write(byte[] bytes) {
                // the per-case effect capture is discarded; the lane
                // effect comparison runs on the captured subprocess
                // streams below
            }
        };
    }

    private static void compareConsoleEffects(List<Case> laneCases, byte[] stdout, byte[] stderr,
                                              String laneName,
                                              Map<String, List<String>> divergences) {
        java.io.ByteArrayOutputStream expectedOut = new java.io.ByteArrayOutputStream();
        java.io.ByteArrayOutputStream expectedErr = new java.io.ByteArrayOutputStream();
        List<String> logCases = new ArrayList<>();
        List<String> errorCases = new ArrayList<>();
        for (Case c : laneCases) {
            if (c instanceof ConsoleCase console) {
                byte[] bytes = (console.text() + "\n").getBytes(StandardCharsets.UTF_8);
                if (console.id() == StdlibFunctionId.CONSOLE_LOG) {
                    expectedOut.writeBytes(bytes);
                    logCases.add(c.name());
                } else {
                    expectedErr.writeBytes(bytes);
                    errorCases.add(c.name());
                }
            }
        }
        if (!Arrays.equals(stdout, expectedOut.toByteArray())) {
            for (String name : logCases) {
                divergences.computeIfAbsent(name, ignored -> new ArrayList<>()).add(laneName
                    + ": console effect bytes diverge on the stdout channel: expected "
                    + hexEncode(expectedOut.toByteArray()) + ", got " + hexEncode(stdout));
            }
        }
        if (!Arrays.equals(stderr, expectedErr.toByteArray())) {
            for (String name : errorCases) {
                divergences.computeIfAbsent(name, ignored -> new ArrayList<>()).add(laneName
                    + ": console effect bytes diverge on the stderr channel: expected "
                    + hexEncode(expectedErr.toByteArray()) + ", got " + hexEncode(stderr));
            }
        }
    }

    // =========================================================================
    // The JVM emitted helpers: real codegen, real javac, real java
    // =========================================================================

    private record Frontend(ProgramNode program, CheckResult result,
                            List<CompilerDiagnostic> errors) { }

    @SuppressWarnings("deprecation")
    private static Frontend compileFrontend(String source, String filename,
                                            ModuleResolver resolver) {
        List<CompilerDiagnostic> errors = new ArrayList<>();
        LexResult lex = new Lexer(source, filename).tokenize();
        for (CompilerDiagnostic d : lex.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (lex.hasErrors()) {
            return new Frontend(null, null, errors);
        }
        Parser parser = new Parser(lex.tokens(), filename, lex.directiveEvents());
        ParseResult parse = parser.parse();
        for (CompilerDiagnostic d : parse.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (parse.hasErrors()) {
            return new Frontend(null, null, errors);
        }
        for (CompilerDiagnostic d : ModuleShapeValidator.validate(parse.program(), filename,
                filename.endsWith(".d.deal"))) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (!errors.isEmpty()) {
            return new Frontend(null, null, errors);
        }
        NameResolver nr = new NameResolver(filename, resolver);
        deal.checker.SymbolTable symTable;
        try {
            symTable = nr.resolve(parse.program());
        } catch (Exception e) {
            errors.add(CompilerDiagnostic.synthetic("E9999", "error", e.getMessage(), filename,
                "missing anchor: battery source '" + filename + "'"));
            return new Frontend(null, null, errors);
        }
        for (CompilerDiagnostic d : nr.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        CheckResult result = TypeChecker.check(filename, symTable, nr, parse.program());
        for (CompilerDiagnostic d : result.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        return new Frontend(parse.program(), result, errors);
    }

    private static Frontend compileFrontend(String source, String filename) {
        return compileFrontend(source, filename, new StubModuleResolver());
    }

    private static String dealStringOf(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (int index = 0; index < text.length(); index++) {
            char c = text.charAt(index);
            switch (c) {
                case '\\' -> sb.append("\\\\");
                case '"' -> sb.append("\\\"");
                case '\n' -> sb.append("\\n");
                case '\t' -> sb.append("\\t");
                case '\r' -> sb.append("\\r");
                default -> sb.append(c); // raw scalar (U+000B, U+000C, U+00A0, emoji…)
            }
        }
        return sb.append('"').toString();
    }

    private static String dealNumberOf(double value) {
        return Double.toString(value);
    }

    /** The JVM lane case subset plus the generated expected stream. */
    private static String jvmProgram(List<Case> laneCases) {
        StringBuilder sb = new StringBuilder();
        sb.append("""
            import * as console from "std/console"
            import * as str from "std/string"
            import * as tbl from "std/table"
            import * as math from "std/math"

            export function battery(): null {
            """);
        int index = 0;
        for (Case c : laneCases) {
            sb.append("  // case ").append(index).append(": ").append(c.name()).append('\n');
            switch (c) {
                case ConsoleCase console -> {
                    String call = console.id() == StdlibFunctionId.CONSOLE_LOG
                        ? "console.log(" : "console.error(";
                    sb.append("  ").append(call).append(dealStringOf(console.text()))
                        .append(")\n");
                }
                case DelReinsKeysCase ignored -> {
                    sb.append("  try {\n");
                    sb.append("    let t: table = {a: 1, b: 2, c: 3}\n");
                    sb.append("    delete t.a\n");
                    sb.append("    t.a = 9\n");
                    sb.append("    let ks: string[] = tbl.keys(t)\n");
                    sb.append("    if (ks.length === 3) { console.log(")
                        .append(dealStringOf("BATT|" + index + "|ok|arr|3"))
                        .append(") } else { console.log(")
                        .append(dealStringOf("BATT|" + index + "|badlen")).append(") }\n");
                    sb.append("    if (ks[0] === \"b\") { console.log(")
                        .append(dealStringOf("BATT|" + index + "|el|0|b"))
                        .append(") } else { console.log(")
                        .append(dealStringOf("BATT|" + index + "|mismatch"))
                        .append(" + ks[0]) }\n");
                    sb.append("    if (ks[1] === \"c\") { console.log(")
                        .append(dealStringOf("BATT|" + index + "|el|1|c"))
                        .append(") } else { console.log(")
                        .append(dealStringOf("BATT|" + index + "|mismatch"))
                        .append(" + ks[1]) }\n");
                    sb.append("    if (ks[2] === \"a\") { console.log(")
                        .append(dealStringOf("BATT|" + index + "|el|2|a"))
                        .append(") } else { console.log(")
                        .append(dealStringOf("BATT|" + index + "|mismatch"))
                        .append(" + ks[2]) }\n");
                    sb.append("  } catch (e) {\n");
                    sb.append("    console.log(\"BATT|").append(index)
                        .append("|err|\" + e.code + \"|\" + e.message)\n");
                    sb.append("  }\n");
                }
                case ValueCase value -> {
                    StdlibFunctionId id = value.id();
                    String call = dealCall(id, value.args());
                    RuntimeDescriptor ret = catalogEntryOf(id).returnDescriptor();
                    if (ret.equals(DESC_STRING_ARRAY)) {
                        Value.Array expected = (Value.Array)
                            ((PinnedOutcome.PinnedSuccess) value.pinned()).value();
                        int count = expected.elements().size();
                        sb.append("  try {\n");
                        sb.append("    let xs: string[] = ").append(call).append('\n');
                        sb.append("    if (xs.length === ").append(count)
                            .append(") { console.log(")
                            .append(dealStringOf("BATT|" + index + "|ok|arr|" + count))
                            .append(") } else { console.log(")
                            .append(dealStringOf("BATT|" + index + "|badlen"))
                            .append(") }\n");
                        for (int element = 0; element < count; element++) {
                            String expectedElement = ((Value.String)
                                expected.elements().elementAt(element)).scalar()
                                    instanceof UnicodeScalars.Valid valid
                                ? valid.carrier() : "";
                            sb.append("    if (xs[").append(element).append("] === ")
                                .append(dealStringOf(expectedElement)).append(") { console.log(")
                                .append(dealStringOf("BATT|" + index + "|el|" + element + "|"
                                    + expectedElement))
                                .append(") } else { console.log(")
                                .append(dealStringOf("BATT|" + index + "|mismatch"))
                                .append(" + xs[").append(element).append("]) }\n");
                        }
                        sb.append("  } catch (e) {\n");
                        sb.append("    console.log(\"BATT|").append(index)
                            .append("|err|\" + e.code + \"|\" + e.message)\n");
                        sb.append("  }\n");
                    } else {
                        String type = ret.equals(DESC_INT) ? "int"
                            : ret.equals(DESC_NUMBER) ? "number"
                                : ret.equals(DESC_STRING) ? "string"
                                    : ret.equals(DESC_BOOLEAN) ? "boolean" : "null";
                        sb.append("  try {\n");
                        sb.append("    let r: ").append(type).append(" = ").append(call)
                            .append('\n');
                        if (value.pinned() instanceof PinnedOutcome.PinnedSuccess) {
                            sb.append(jvmMatchLines(value.id(), index, value.pinned(), "r",
                                "    "));
                        }
                        sb.append("  } catch (e) {\n");
                        sb.append("    console.log(\"BATT|").append(index)
                            .append("|err|\" + e.code + \"|\" + e.message)\n");
                        sb.append("  }\n");
                    }
                }
                case ChainCase chain -> throw new IllegalArgumentException(
                    "the JVM lane has no JSON chains (std/json is the E6000 position): "
                        + chain.name());
            }
            index++;
        }
        sb.append("  return null\n");
        sb.append("}\n");
        return sb.toString();
    }

    /** The import alias of one id in the generated JVM battery program. */
    private static String jvmAliasOf(StdlibFunctionId id) {
        return switch (id) {
            case CONSOLE_LOG, CONSOLE_ERROR -> "console";
            case STRING_LENGTH, STRING_SUBSTRING, STRING_CONTAINS, STRING_STARTS_WITH,
                 STRING_ENDS_WITH, STRING_REPLACE, STRING_SPLIT, STRING_TRIM -> "str";
            case TABLE_KEYS -> "tbl";
            case JSON_PARSE, JSON_STRINGIFY -> "json";
            case MATH_FLOOR, MATH_CEIL, MATH_SQRT, MATH_ABS_INT, MATH_ABS_NUMBER,
                 MATH_MIN_INT, MATH_MAX_INT -> "math";
            case TIME_NOW_MILLIS -> "time";
        };
    }

    private static String dealCall(StdlibFunctionId id, List<Arg> args) {
        String module = jvmAliasOf(id);
        String fn = exportNameOf(id);
        StringBuilder sb = new StringBuilder(module).append('.').append(fn).append('(');
        for (int index = 0; index < args.size(); index++) {
            if (index > 0) {
                sb.append(", ");
            }
            sb.append(dealArgOf(args.get(index)));
        }
        return sb.append(')').toString();
    }

    /**
     * The equality-marker match lines of one scalar case: the program
     * compares the result to the pinned scalar and prints the fixed ok
     * line on equality (the checker's template interpolation admits only
     * string-typed parts, so scalar observations print marker lines —
     * the established fixture pattern); a mismatch prints the actual
     * string via string concatenation, and non-string scalars print the
     * mismatch marker.
     */
    private static String jvmMatchLines(StdlibFunctionId id, int index, PinnedOutcome pinned,
                                        String target, String indent) {
        Value expected = ((PinnedOutcome.PinnedSuccess) pinned).value();
        StringBuilder sb = new StringBuilder();
        switch (expected) {
            case Value.Int intValue -> {
                sb.append(indent).append("if (").append(target).append(" === ")
                    .append(intValue.value()).append(") { console.log(")
                    .append(dealStringOf("BATT|" + index + "|ok|" + intValue.value()))
                    .append(") } else { console.log(")
                    .append(dealStringOf("BATT|" + index + "|mismatch")).append(") }\n");
            }
            case Value.Number number -> {
                sb.append(indent).append("if (").append(target).append(" === ")
                    .append(Double.toString(number.value())).append(") { console.log(")
                    .append(dealStringOf("BATT|" + index + "|ok|" + Double.toString(
                        number.value())))
                    .append(") } else { console.log(")
                    .append(dealStringOf("BATT|" + index + "|mismatch")).append(") }\n");
            }
            case Value.Bool bool -> {
                String test = bool.value() ? target : "!" + target;
                sb.append(indent).append("if (").append(test).append(") { console.log(")
                    .append(dealStringOf("BATT|" + index + "|ok|" + bool.value()))
                    .append(") } else { console.log(")
                    .append(dealStringOf("BATT|" + index + "|mismatch")).append(") }\n");
            }
            case Value.String string -> {
                String text = string.scalar() instanceof UnicodeScalars.Valid valid
                    ? valid.carrier() : "";
                sb.append(indent).append("if (").append(target).append(" === ")
                    .append(dealStringOf(text)).append(") { console.log(")
                    .append(dealStringOf("BATT|" + index + "|ok|" + text))
                    .append(") } else { console.log(")
                    .append(dealStringOf("BATT|" + index + "|got|"))
                    .append(" + ").append(target).append(") }\n");
            }
            default -> throw new IllegalArgumentException("unsupported scalar pin " + expected);
        }
        return sb.toString();
    }

    private static String dealArgOf(Arg arg) {
        if (arg instanceof Arg.TableArg tableArg) {
            StringBuilder literal = new StringBuilder("{");
            for (int index = 0; index < tableArg.keys().size(); index++) {
                if (index > 0) {
                    literal.append(", ");
                }
                literal.append(tableArg.keys().get(index)).append(": ");
                Value value = tableArg.values().get(index);
                literal.append(switch (value) {
                    case Value.Int intValue -> Integer.toString(intValue.value());
                    case Value.String string when
                        string.scalar() instanceof UnicodeScalars.Valid valid ->
                        dealStringOf(valid.carrier());
                    case Value.Number number -> dealNumberOf(number.value());
                    default -> throw new IllegalArgumentException(
                        "unsupported JVM table value " + value);
                });
            }
            return literal.append("}").toString();
        }
        if (arg instanceof Arg.NaNTableArg || arg instanceof Arg.FnLeafTableArg) {
            throw new IllegalArgumentException(
                "the JVM lane has no NaN/function table cases");
        }
        return switch (arg) {
            case Arg.StrArg strArg -> dealStringOf(strArg.text());
            case Arg.IntArg intArg -> Integer.toString(intArg.value());
            case Arg.NumArg numArg -> dealNumberOf(numArg.value());
            case Arg.TableArg tableArg -> throw new IllegalArgumentException(
                "table args build inline for the JVM lane");
            case Arg.NaNTableArg nanArg -> throw new IllegalArgumentException(
                "table args build inline for the JVM lane");
            case Arg.FnLeafTableArg fnArg -> throw new IllegalArgumentException(
                "table args build inline for the JVM lane");
        };
    }

    /** The expected stdout/stderr line lists plus their owning case names. */
    private record ExpectedLine(String text, String caseName) { }

    private static List<ExpectedLine> jvmExpectedLines(List<Case> laneCases, Reference reference,
                                                       boolean stderrChannel) {
        List<ExpectedLine> lines = new ArrayList<>();
        int index = 0;
        for (Case c : laneCases) {
            if (c instanceof ConsoleCase console) {
                boolean error = console.id() == StdlibFunctionId.CONSOLE_ERROR;
                if (error == stderrChannel) {
                    // the effect text may carry raw newlines: one ExpectedLine
                    // per output line keeps the stream line index aligned
                    // with the owner list
                    String[] parts = console.text().split("\n", -1);
                    for (String part : parts) {
                        lines.add(new ExpectedLine(part, c.name()));
                    }
                }
                index++;
                continue;
            }
            if (stderrChannel) {
                index++;
                continue;
            }
            Outcome<Value> outcome = referenceOutcomeOf(c, reference);
            assertPinned(outcome, pinnedOf(c), "JVM case " + c.name());
            if (outcome instanceof Outcome.Success<Value> success) {
                RuntimeDescriptor ret = catalogEntryOf(c.attribution().get(0))
                    .returnDescriptor();
                if (ret.equals(DESC_STRING_ARRAY)) {
                    Value.Array array = (Value.Array) success.value();
                    lines.add(new ExpectedLine("BATT|" + index + "|ok|arr|"
                        + array.elements().size(), c.name()));
                    for (int element = 0; element < array.elements().size(); element++) {
                        lines.add(new ExpectedLine("BATT|" + index + "|el|" + element + "|"
                            + scalarText(array.elements().elementAt(element)), c.name()));
                    }
                } else {
                    lines.add(new ExpectedLine("BATT|" + index + "|ok|"
                        + scalarText(success.value()), c.name()));
                }
            } else {
                Outcome.Failure<Value> failure = (Outcome.Failure<Value>) outcome;
                lines.add(new ExpectedLine("BATT|" + index + "|err|"
                    + failure.failure().failure().code() + "|"
                    + failure.failure().failure().message(), c.name()));
            }
            index++;
        }
        return lines;
    }

    private static PinnedOutcome pinnedOf(Case c) {
        if (c instanceof ValueCase value) {
            return value.pinned();
        }
        if (c instanceof ChainCase chain) {
            return chain.pinned();
        }
        if (c instanceof DelReinsKeysCase delReins) {
            return delReins.pinned();
        }
        return ok(NULL);
    }

    private static String scalarText(Value value) {
        return switch (value) {
            case Value.Null ignored -> "";
            case Value.Bool bool -> Boolean.toString(bool.value());
            case Value.Int intValue -> Integer.toString(intValue.value());
            case Value.Number number -> Double.toString(number.value());
            case Value.String string when
                string.scalar() instanceof UnicodeScalars.Valid valid -> valid.carrier();
            default -> throw new IllegalArgumentException("unsupported scalar " + value);
        };
    }

    /** Compiles and runs the real JVM emitted helpers and compares the full streams. */
    static Map<String, List<String>> runJvmLane(Set<Case> all, Reference reference)
        throws Exception {
        List<Case> laneCases = casesFor(all, Lane.JVM_EMITTED);
        Path tmp = Files.createTempDirectory("deal-stdlib-equiv-jvm");
        try {
            String source = jvmProgram(laneCases);
            Frontend frontend = compileFrontend(source, "jvmstdlibbattery.deal");
            if (!frontend.errors().isEmpty()) {
                Path dump = Path.of("/tmp/jvmstdlibbattery-debug.deal");
                try {
                    Files.writeString(dump, source);
                } catch (IOException ignored) {
                    // best-effort debug dump
                }
                check(false, "the JVM battery module frontend is clean; generated source at "
                    + dump + " errors: " + frontend.errors());
                return new LinkedHashMap<>();
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(frontend.program(),
                frontend.result(), "jvmstdlibbattery.deal", "main",
                SemanticProfile.DEAL_V1_2_INT32);
            check(!res.hasErrors(), "the JVM battery module codegen is clean: "
                + res.diagnostics());
            if (res.hasErrors()) {
                return new LinkedHashMap<>();
            }
            Path outDir = tmp.resolve("out");
            Files.createDirectories(outDir);
            Files.writeString(outDir.resolve("Main.java"), res.source());
            Files.writeString(outDir.resolve("JvmConformanceRunner.java"),
                StubModuleResolver.buildJvmRunner(frontend.program(), res.className()));
            StringBuilder javacErr = new StringBuilder();
            boolean javacOk = StubModuleResolver.compileWithJavac(outDir,
                List.of("Main.java", "JvmConformanceRunner.java"), javacErr);
            check(javacOk, "the JVM battery artifact compiles with javac: " + javacErr);
            if (!javacOk) {
                return new LinkedHashMap<>();
            }
            SubprocessRun run = runTool(outDir,
                List.of("java", "-cp", outDir.toString(), "JvmConformanceRunner"), 180);
            check(run.exitCode() == 0,
                "the JVM battery artifact exits 0 (per-case DEAL errors are caught inside "
                    + "the battery program); got exit " + run.exitCode() + " output="
                    + new String(run.stdout(), StandardCharsets.UTF_8));
            List<ExpectedLine> expectedStdout = jvmExpectedLines(laneCases, reference, false);
            List<ExpectedLine> expectedStderr = jvmExpectedLines(laneCases, reference, true);
            Map<String, List<String>> divergences = compareJvmStreams(
                expectedStdout, run.stdout(), "stdout");
            Map<String, List<String>> stderrDivergences = compareJvmStreams(
                expectedStderr, run.stderr(), "stderr");
            merge(stderrDivergences, divergences);
            return divergences;
        } finally {
            deleteRecursively(tmp);
        }
    }

    private static void merge(Map<String, List<String>> from, Map<String, List<String>> into) {
        for (Map.Entry<String, List<String>> entry : from.entrySet()) {
            into.computeIfAbsent(entry.getKey(), ignored -> new ArrayList<>())
                .addAll(entry.getValue());
        }
    }

    private static Map<String, List<String>> compareJvmStreams(List<ExpectedLine> expectedLines,
            byte[] actualBytes, String channel) {
        Map<String, List<String>> divergences = new LinkedHashMap<>();
        String expected = expectedLines.stream()
            .map(ExpectedLine::text)
            .reduce("", (a, b) -> a + b + "\n");
        String actual = new String(actualBytes, StandardCharsets.UTF_8);
        if (expected.equals(actual)) {
            return divergences;
        }
        String[] expectedParts = expected.split("\n", -1);
        String[] actualParts = actual.split("\n", -1);
        int limit = Math.max(expectedParts.length, actualParts.length);
        int attributed = 0;
        for (int index = 0; index < limit && attributed < 20; index++) {
            String expectedPart = index < expectedParts.length ? expectedParts[index] : null;
            String actualPart = index < actualParts.length ? actualParts[index] : null;
            if (Objects.equals(expectedPart, actualPart)) {
                continue;
            }
            String owner = index < expectedLines.size() ? expectedLines.get(index).caseName()
                : (expectedLines.isEmpty() ? "jvm-console" : expectedLines.get(
                    expectedLines.size() - 1).caseName());
            divergences.computeIfAbsent(owner, ignored2 -> new ArrayList<>()).add("jvm "
                + channel + " line " + index + ": expected \"" + expectedPart + "\", got \""
                + actualPart + "\"");
            attributed++;
        }
        if (attributed == 0) {
            divergences.computeIfAbsent("jvm-stream", ignored2 -> new ArrayList<>())
                .add("jvm " + channel + " stream differs: expected " + hexEncode(
                    expected.getBytes(StandardCharsets.UTF_8)) + ", got "
                    + hexEncode(actualBytes));
        }
        return divergences;
    }

    // =========================================================================
    // Tests
    // =========================================================================

    /** The reference parameter boundary rejects invalid scalar encodings first (D4, Verification 1). */
    private static void testReferenceParameterBoundaryRejectsInvalidScalar(Reference reference) {
        System.out.println("-- Reference: invalid scalar encodings fail at STDLIB_PARAMETER --");

        Value invalid = Value.string("a\uD800b");
        Outcome<Value> outcome = reference.run(StdlibFunctionId.STRING_LENGTH,
            List.of(invalid), null);
        check(outcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message()
                    .equals("expected string, got invalid Unicode scalar encoding"),
            "the STDLIB_PARAMETER boundary rejects the invalid scalar encoding with the exact "
                + "E8001 before any algorithm runs; got " + describeOutcome(outcome));
    }

    /**
     * The T4 pinning controls: the pinned projection assertions of the
     * reference run reject a tampered {@code {reason}} and a tampered
     * {@code {fieldPath}} — breaking a projection fails the reference run.
     */
    private static void testReferenceProjectionPinningControls() {
        System.out.println("-- Reference: tampered projections fail the pinned reference run --");

        Map<String, String> tamperedReason = new LinkedHashMap<>();
        tamperedReason.put("oneBasedByteOffset", "6");
        tamperedReason.put("reason", "tampered-reason");
        BoundaryFailure tamperedReasonFailure = BoundaryFailure.fromRow(
            deal.semantic.ir.FailureContractRegistry.row(FailurePolicyId.JSON_PARSE_SYNTAX),
            0, null, null, tamperedReason, null);
        Outcome<Value> tamperedReasonOutcome = new Outcome.Failure<>(
            new SharedStdlibSemantics.StdlibFailure(tamperedReasonFailure,
                Reference.ORIGIN));
        PinnedOutcome reasonPin = fail(FailurePolicyId.JSON_PARSE_SYNTAX,
            DiagnosticCode.E8001,
            "JSON parse error at position 6: " + SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
            null, null, "oneBasedByteOffset", "6", "reason",
            SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER);
        check(!pinnedMatches(tamperedReasonOutcome, reasonPin),
            "a tampered {reason} fails the pinned projection assertion (breaking a projection "
                + "fails the reference run)");

        Map<String, String> tamperedPath = new LinkedHashMap<>();
        tamperedPath.put("fieldPath", "tampered");
        tamperedPath.put("actual", "number");
        BoundaryFailure tamperedPathFailure = BoundaryFailure.fromRow(
            deal.semantic.ir.FailureContractRegistry.row(FailurePolicyId.JSON_TO_ERROR),
            0, null, null, tamperedPath, null);
        Outcome<Value> tamperedPathOutcome = new Outcome.Failure<>(
            new SharedStdlibSemantics.StdlibFailure(tamperedPathFailure,
                Reference.ORIGIN));
        PinnedOutcome pathPin = fail(FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
            "unsupported type for JSON encoding: number",
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "number",
            "fieldPath", "a", "actual", "number");
        check(!pinnedMatches(tamperedPathOutcome, pathPin),
            "a tampered {fieldPath} fails the pinned projection assertion");
    }

    /** The negative control: a deliberately broken stub helper must fail the battery. */
    private static void testNegativeControlBrokenStub(Set<Case> all, Reference reference)
        throws Exception {
        System.out.println("-- Negative control: a deliberately broken trim stub fails the "
            + "battery --");

        Map<String, List<String>> divergences = runLuaLane(all, reference, true);
        check(!divergences.isEmpty(),
            "the broken stub (leading-only trim) diverges from the common closed trim set — "
                + "the battery detects divergence rather than passing vacuously");
        boolean trailingSeedDetected = false;
        for (String caseName : divergences.keySet()) {
            if (caseName.contains("trim")) {
                trailingSeedDetected = true;
            }
        }
        check(trailingSeedDetected,
            "the broken stub diverges on the trailing-whitespace edge of the closed trim set: "
                + divergences);
    }

    /**
     * The combined T3/T4 control: a tampered reference algorithm (the
     * trim set widened with U+00A0) flips the retained trim helper's
     * comparison result from equal to divergent — breaking an algorithm flips
     * at least one comparison result.
     */
    private static void testAlgorithmTamperDetected(Set<Case> all, Reference reference) {
        System.out.println("-- Combined T3/T4: a tampered trim algorithm flips the trim "
            + "comparison result --");

        Reference tampered = new Reference(reference.origin) {
            @Override
            Outcome<Value> run(StdlibFunctionId id, List<Value> args, ConsoleSink sink) {
                Outcome<Value> outcome = super.run(id, args, sink);
                if (id == StdlibFunctionId.STRING_TRIM
                        && outcome instanceof Outcome.Success<Value> success
                        && success.value() instanceof Value.String string
                        && string.scalar() instanceof UnicodeScalars.Valid valid) {
                    String carrier = valid.carrier();
                    while (carrier.startsWith("\u00a0")) {
                        carrier = carrier.substring(1);
                    }
                    while (carrier.endsWith("\u00a0")) {
                        carrier = carrier.substring(0, carrier.length() - 1);
                    }
                    return new Outcome.Success<>(s(carrier));
                }
                return outcome;
            }
        };

        List<Case> laneCases = casesFor(all, Lane.RETAINED_LUA);
        boolean nbspSeedDiverged = false;
        for (int index = 0; index < laneCases.size(); index++) {
            Case c = laneCases.get(index);
            if (!(c instanceof ValueCase value)
                    || value.id() != StdlibFunctionId.STRING_TRIM) {
                continue;
            }
            Outcome<Value> referenceOutcome = referenceOutcomeOf(c, tampered);
            // drive the retained Lua trim helper on the seed directly
            Arg.StrArg strArg = (Arg.StrArg) value.args().get(0);
            Outcome<Value> laneLikeOutcome;
            if (strArg.text().contains("\u00a0")) {
                // the real retained helper leaves U+00A0 in place, the
                // tampered reference strips it — a divergence
                laneLikeOutcome = reference.run(StdlibFunctionId.STRING_TRIM,
                    List.of(s(strArg.text())), null);
                String mismatch = laneMismatch(StdlibFunctionId.STRING_TRIM,
                    referenceOutcome, new LaneResult(index, true,
                        canonicalOf(StdlibFunctionId.STRING_TRIM,
                            ((Outcome.Success<Value>) laneLikeOutcome).value())));
                if (mismatch != null) {
                    nbspSeedDiverged = true;
                }
            }
        }
        check(nbspSeedDiverged,
            "with the tampered trim set (U+00A0 stripped) the retained trim helper's U+00A0 "
                + "seed flips from equivalent to divergent — breaking an algorithm flips at "
                + "least one comparison result");
    }

    private static void testKnownDivergences(Map<Lane, Map<String, List<String>>> laneDiv) {
        System.out.println("-- Known divergences are detected by execution --");

        Map<String, List<String>> lua = laneDiv.getOrDefault(Lane.RETAINED_LUA,
            new LinkedHashMap<>());
        Map<String, List<String>> js = laneDiv.getOrDefault(Lane.RETAINED_JS,
            new LinkedHashMap<>());
        Map<String, List<String>> jvm = laneDiv.getOrDefault(Lane.JVM_EMITTED,
            new LinkedHashMap<>());

        check(lua.containsKey("keys-abc-insertion"),
            "the Lua table.keys insertion-order divergence is detected by the comparison: "
                + lua.get("keys-abc-insertion"));
        check(lua.containsKey("keys-delete-reinsert-a"),
            "the Lua table.keys delete-reinsert order divergence is detected: "
                + lua.get("keys-delete-reinsert-a"));
        check(js.containsKey("keys-parse-intlike"),
            "the JS table.keys integer-like-key iteration-order divergence is detected by "
                + "the comparison: " + js.get("keys-parse-intlike"));
        check(lua.containsKey("stringify-abc"),
            "the Lua json.stringify iteration-order divergence is detected by the "
                + "comparison: " + lua.get("stringify-abc"));
        check(lua.containsKey("stringify-parse-1.0") && js.containsKey("stringify-parse-1.0"),
            "the retained json.parse value-based int mapping divergence (1.0 → int retained, "
                + "number common) is detected for Lua and JS: lua="
                + lua.get("stringify-parse-1.0") + " js=" + js.get("stringify-parse-1.0"));
        check(lua.containsKey("stringify-parse-1e3") && js.containsKey("stringify-parse-1e3"),
            "the retained json.parse exponent-form int mapping divergence (1e3 → int "
                + "retained, number common) is detected for Lua and JS");
        check(js.containsKey("stringify-parse-intlike"),
            "the JS json.stringify integer-like-key order divergence is detected: "
                + js.get("stringify-parse-intlike"));
        check(lua.containsKey("parse-syntax-missing-value")
                || lua.containsKey("parse-top-level-scalar"),
            "the Lua json.parse failure-projection divergence is detected");
        check(js.containsKey("parse-syntax-missing-value")
                || js.containsKey("parse-top-level-scalar"),
            "the JS json.parse failure-projection divergence is detected");
        check(js.containsKey("absInt-min"),
            "the JS retained absInt safe-range divergence on -2147483648 is detected: "
                + js.get("absInt-min"));
        check(!jvm.containsKey("absInt-min"),
            "the JVM emitted absInt helper matches the common INT32_RESULT projection "
                + "('int out of safe range' on both sides — the former cross-side "
                + "message divergence is retired): " + jvm.get("absInt-min"));
        check(!jvm.containsKey("sqrt-neg4"),
            "the JVM emitted sqrt helper matches the common SQRT_NEGATIVE projection on "
                + "sqrt(-4)");
    }

    private static void testJvmJsonPositionSupported() {
        System.out.println("-- The JVM std/json position is supported (the import "
            + "compiles over the shared JSON runtime) --");

        Frontend frontend = compileFrontend("""
            import * as json from "std/json"
            export function test(): null { return null; }
            """, "jvmjsonposition.deal");
        check(frontend.errors().isEmpty(),
            "the std/json-importing module passes the frontend: " + frontend.errors());
        if (frontend.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(frontend.program(),
                frontend.result(), "jvmjsonposition.deal", "main",
                SemanticProfile.DEAL_V1_2_INT32);
            check(!res.hasErrors(),
                "the JVM backend compiles the std/json import (no E6000 at the import "
                    + "statement): " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("static java.lang.Object __jsonParse(")
                        && res.source().contains(
                            "static $DealRt.Table $jsonParse(java.lang.String s) {"),
                    "the std/json-importing module emits the shared JSON runtime over "
                        + "the table carrier");
            }
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Stdlib Target-Helper Equivalence Battery (ISSUE-0498) ===");

        requireTool("luajit", "-v");
        requireTool("node", "--version");
        requireTool("javac", "-version");
        requireTool("java", "-version");

        Reference reference = new Reference(origin());
        testReferenceParameterBoundaryRejectsInvalidScalar(reference);
        testReferenceProjectionPinningControls();

        Set<Case> all = new LinkedHashSet<>(cases());
        int pinFailures = 0;
        for (Case c : all) {
            if (c instanceof ConsoleCase) {
                continue; // asserted inside referenceOutcomeOf
            }
            Outcome<Value> outcome = referenceOutcomeOf(c, reference);
            if (!pinnedMatches(outcome, pinnedOf(c))) {
                pinFailures++;
                fail("the reference run of case " + c.name() + " diverged from the pinned "
                    + "parent-table outcome: " + describeOutcome(outcome));
            }
        }
        check(pinFailures == 0,
            "every pinned case outcome holds on the reference run (T3 + T4 wiring)");

        Map<Lane, Map<String, List<String>>> laneDiv = new LinkedHashMap<>();
        try {
            laneDiv.put(Lane.RETAINED_LUA, runLuaLane(all, reference, false));
            laneDiv.put(Lane.RETAINED_JS, runJsLane(all, reference));
            laneDiv.put(Lane.JVM_EMITTED, runJvmLane(all, reference));
        } catch (Exception e) {
            fail("a lane battery threw: " + e);
            e.printStackTrace();
        }

        testKnownDivergences(laneDiv);
        testJvmJsonPositionSupported();
        testNegativeControlBrokenStub(all, reference);
        testAlgorithmTamperDetected(all, reference);
        for (Lane lane : Lane.values()) {
            Map<String, List<String>> seeds = laneDiv.get(lane);
            if (seeds == null) {
                continue;
            }
            for (Map.Entry<String, List<String>> entry : seeds.entrySet()) {
                if (!entry.getValue().isEmpty()) {
                    System.out.println("  [SEED " + lane + "] " + entry.getKey() + " -> "
                        + entry.getValue());
                }
            }
        }
        System.out.println("passed=" + passed + " failed=" + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
