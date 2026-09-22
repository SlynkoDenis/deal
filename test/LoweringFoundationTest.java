package deal.test;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
import deal.ast.Block;
import deal.ast.CallExpr;
import deal.ast.Either;
import deal.ast.ExpressionNode;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionStatement;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.IndexExpr;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.ProgramNode;
import deal.ast.ReturnStatement;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.SemanticLowerer;
import deal.semantic.SharedValueSemantics;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Verifies the ISSUE-0281 foundation surface: the E6005 registration in
 * {@link DiagnosticCode}, the {@link LoweringFailureDetail} payload carrier,
 * and the four closed foundation enums
 * ({@link SemanticProfile}, {@link InvocationPurpose}, {@link ReleaseState},
 * {@link SemanticCapability}).
 *
 * <p>Verifies the ISSUE-0390 value-semantics primitive (design I2):
 * {@link SharedValueSemantics} — pure, static, deterministic, no I/O, no
 * state — with its closed {@code Int32Result = Value(int) | Fail(code,
 * template, origin)} shape, every int32/IEEE-number row (both signs of
 * add/sub/mul/neg overflow, {@code MIN/-1} → E8004 and {@code MIN%-1} →
 * 0, zero-divisor E8005 first, negative-exponent E8006 first, the
 * int32Pow finite band {@code 2 ** 62} → E8004 and infinity band
 * {@code 2 ** 1024} → E8001, intFromNumber in the normative order,
 * checkInt32Integral, numberFromInt exactness, -0 normalization, IEEE
 * div-by-zero, NaN equality/relational, floor-mod signs, numberPow's
 * every pinned special case, failure precedence, and the supplied origin
 * on every failure), and a cross-check asserting the primitive's row
 * projection agrees with the closed {@code binaryPolicy} table data in
 * {@link SemanticIrValidator} for every covered selector, and the
 * complete unary set ({@code INT32_NEG}, {@code NUMBER_NEG},
 * {@code BOOL_NOT}) agrees with the closed {@code unaryPolicy} rule —
 * a selector stamped with any other policy is a failure.</p>
 *
 * <p>Verifies the ISSUE-0395 value-operation slice (design I3): the
 * {@link deal.semantic.SemanticLowerer} {@code CONST}/{@code UNARY}/
 * {@code BINARY}/{@code INTRINSIC_CALL} arms with the fixed
 * selector→policy stamping read from the closed validator tables
 * ({@code unaryPolicy}/{@code binaryPolicy}/{@code intrinsicPolicy}),
 * the pinned one-line scalar descriptor rows of the slice (realized
 * through the single DescriptorService producer), validated units with a deliberately wrong selector→policy pair
 * failing R-POLICY-KIND as the negative control, the
 * {@code LEGACY_SAFE_INT} pre-lowering rejection (E6005
 * {@code LOWER_LEGACY_PROFILE_REJECTED} before any op), out-of-scope
 * constructs failing E6005 naming the construct, byte-identical repeated
 * dumps, and the combined T1+T3 run — a fixture module using
 * {@code -2147483648}, unary negation, int32 arithmetic selectors, and
 * {@code int()}/{@code number()} conversions parsed under a
 * {@code COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION} invocation,
 * lowered by the slice, and validated (fails if the invocation path, the
 * profile-aware parser, or the slice is broken).</p>
 *
 * <p>Tests:
 * <ol>
 *   <li>E6000..E6005 are the complete E6 code set, all
 *       {@code BACKEND_LOWERING}, in declaration order, with E6005 directly
 *       beside E6000-E6004 and its message template exactly
 *       "Common semantic lowering failed"; E6000 remains the intentional
 *       retained-target rejection code and is never E6005; the E6000-E6004
 *       message templates are unchanged.</li>
 *   <li>Reflection-based exhaustive enumeration of the four closed enums:
 *       exactly the pinned values in the pinned order; enum type, implicit
 *       finality, and constructor surface checked; no open/unknown fallback
 *       member; no static factory or other extension point beyond the
 *       implicit values()/valueOf(String).</li>
 *   <li>{@link LoweringFailureDetail} is an immutable record with exactly
 *       the six pinned components in the pinned order and the pinned
 *       component types, and its accessors return the constructed values.</li>
 *   <li>{@link SharedValueSemantics} surface: final, no instances, no
 *       state, static entry points, the pinned {@code INT32_MIN}/{@code
 *       INT32_MAX} constants, the sealed two-permit {@code Int32Result}
 *       shape, and fail-closed null handling.</li>
 *   <li>Every int32 row: arithmetic both signs, div/mod truncation and
 *       precedence, pow bands and precedence, conversion order,
 *       checkInt32Integral, numberFromInt, and the caller-supplied origin
 *       on every failure.</li>
 *   <li>Every number row: IEEE add/sub/mul/div/neg, floor-mod signs,
 *       numberPow's pinned IEEE-754 special-case table, and the int32 /
 *       number comparison rules incl. NaN.</li>
 *   <li>The selector→policy cross-check against the closed
 *       {@code SemanticIrValidator.binaryPolicy} table and the
 *       {@code SemanticIrValidator.unaryPolicy} rule.</li>
 * </ol>
 */
public class LoweringFoundationTest {

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

    /** A throwing action for {@link #expectThrows}. */
    private interface ThrowingRunnable {
        void run() throws Throwable;
    }

    private static void expectThrows(Class<? extends Throwable> type, ThrowingRunnable action,
                                     String message) {
        try {
            action.run();
            fail(message);
        } catch (Throwable t) {
            check(type.isInstance(t), message + " (got " + t.getClass().getSimpleName() + ")");
        }
    }

    // =========================================================================
    // E6005 registration
    // =========================================================================

    static void testE6005Registration() {
        System.out.println("-- E6005 registration --");

        List<String> e6 = new ArrayList<>();
        for (DiagnosticCode dc : DiagnosticCode.values()) {
            if (dc.code().matches("E6\\d{3}")) {
                e6.add(dc.code());
            }
        }
        // ISSUE-0507 (FFI candidate fixture conformance) registers E6006
        // FFI_UNSUPPORTED_BACKEND at the end of the E6 range (corpus C6).
        check(e6.equals(List.of("E6000", "E6001", "E6002", "E6003",
                "E6004", "E6005", "E6006")),
            "E6 codes are exactly E6000..E6006 in declaration order; got " + e6);

        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            "E6005 is BACKEND_LOWERING");
        check("Common semantic lowering failed"
                .equals(DiagnosticCode.E6005.messageTemplate()),
            "E6005 message template is exactly \"Common semantic lowering failed\"");
        check(DiagnosticCode.fromCode("E6005") == DiagnosticCode.E6005,
            "E6005 resolves through fromCode");
        check(DiagnosticCode.isRegistered("E6005"), "E6005 is registered");

        check(DiagnosticCode.E6005.ordinal() == DiagnosticCode.E6004.ordinal() + 1
                && DiagnosticCode.E6004.ordinal() == DiagnosticCode.E6003.ordinal() + 1,
            "E6005 sits directly beside E6000-E6004 (ordinal adjacency)");

        // E6000 remains the intentional retained-target rejection code and is
        // never E6005 (parent D11).
        check(DiagnosticCode.E6000 != DiagnosticCode.E6005,
            "E6000 and E6005 are distinct codes");
        check(DiagnosticCode.E6000.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            "E6000 remains BACKEND_LOWERING (retained-target rejection)");

        // No existing E6000-E6004 code was renamed or renumbered: pin the
        // unchanged message templates.
        Map<String, String> pinnedMessages = Map.of(
            "E6000", "Unsupported statement type",
            "E6001", "Continue outside loop",
            "E6002", "Cannot break/continue across try boundary",
            "E6003", "Rest parameters are not part of DEAL v1.2",
            "E6004", "Entry module must export non-async main(): null");
        for (var entry : pinnedMessages.entrySet()) {
            DiagnosticCode dc = DiagnosticCode.fromCode(entry.getKey());
            check(dc != null && entry.getValue().equals(dc.messageTemplate()),
                entry.getKey() + " message template unchanged: "
                    + (dc == null ? "null" : dc.messageTemplate()));
        }
    }

    // =========================================================================
    // Closed enum verification (reflection-based)
    // =========================================================================

    static void testClosedEnum(Class<? extends Enum<?>> type, List<String> pinned,
                               String name) {
        System.out.println("-- Closed enum " + name + " --");

        check(type.isEnum(), name + " is an enum type");
        check(Enum.class.isAssignableFrom(type), name + " extends java.lang.Enum");
        check(Modifier.isFinal(type.getModifiers()),
            name + " is implicitly final (no subclass extension point)");

        Enum<?>[] constants = type.getEnumConstants();
        List<String> actual = new ArrayList<>();
        for (Enum<?> c : constants) {
            actual.add(c.name());
        }
        check(actual.equals(pinned),
            name + " contains exactly " + pinned + " in the pinned order; got " + actual);
        check(constants.length == pinned.size(),
            name + " has exactly " + pinned.size() + " constants (no extra members)");

        // No open/unknown fallback member.
        for (Enum<?> c : constants) {
            String n = c.name();
            check(!n.equals("UNKNOWN") && !n.equals("OPEN") && !n.equals("OTHER")
                    && !n.equals("UNSPECIFIED") && !n.equals("CUSTOM"),
                name + " has no open/unknown fallback member (offending: " + n + ")");
            check(c.getClass() == type,
                name + " constant " + n + " has no constant-specific class body");
        }

        // No external extension point: no public constructor, and the only
        // public static methods returning the enum type (or its array) are
        // the implicit values()/valueOf(String) — the javac-generated
        // private synthetic $values() helper is not a public surface.
        Constructor<?>[] ctors = type.getDeclaredConstructors();
        check(ctors.length == 1 && !Modifier.isPublic(ctors[0].getModifiers()),
            name + " has exactly one private constructor (no public construction)");
        for (Method m : type.getDeclaredMethods()) {
            boolean returnsEnumType = m.getReturnType() == type
                || (m.getReturnType().isArray()
                    && m.getReturnType().getComponentType() == type);
            if (Modifier.isPublic(m.getModifiers()) && Modifier.isStatic(m.getModifiers())
                    && returnsEnumType) {
                check(m.getName().equals("values") || m.getName().equals("valueOf"),
                    name + " public static enum-typed surface is exactly "
                        + "values()/valueOf(String); found " + m);
            }
        }

        // Reflection round-trip for every pinned value.
        for (int i = 0; i < pinned.size(); i++) {
            check(valueOfRaw(type, pinned.get(i)) == constants[i],
                name + " valueOf round-trip for " + pinned.get(i)
                    + " hits declaration position " + i);
        }
        try {
            valueOfRaw(type, "UNKNOWN");
            fail(name + " valueOf(\"UNKNOWN\") should have failed (closed set)");
        } catch (IllegalArgumentException expected) {
            check(true, name + " rejects an unknown value by name");
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private static Enum<?> valueOfRaw(Class<? extends Enum<?>> type, String name) {
        return Enum.valueOf((Class) type, name);
    }

    // =========================================================================
    // LoweringFailureDetail
    // =========================================================================

    static void testLoweringFailureDetail() {
        System.out.println("-- LoweringFailureDetail payload carrier --");

        Class<LoweringFailureDetail> type = LoweringFailureDetail.class;
        check(type.isRecord(), "LoweringFailureDetail is an immutable record");

        RecordComponent[] components = type.getRecordComponents();
        String[] pinnedNames = {"module", "capability", "validatorRule",
            "semanticProfile", "irVersion", "origin"};
        Class<?>[] pinnedTypes = {String.class, SemanticCapability.class,
            String.class, SemanticProfile.class, String.class, String.class};
        check(components.length == 6,
            "LoweringFailureDetail has exactly 6 components; got "
                + components.length + " " + Arrays.toString(components));
        for (int i = 0; i < Math.min(components.length, pinnedNames.length); i++) {
            check(pinnedNames[i].equals(components[i].getName()),
                "component " + i + " is named " + pinnedNames[i]
                    + "; got " + components[i].getName());
            check(components[i].getType() == pinnedTypes[i],
                "component " + i + " has type " + pinnedTypes[i].getSimpleName()
                    + "; got " + components[i].getType().getSimpleName());
        }

        Field[] fields = type.getDeclaredFields();
        check(fields.length == 6,
            "LoweringFailureDetail declares exactly 6 fields (no extras); got "
                + fields.length);
        for (Field f : fields) {
            check(Modifier.isPrivate(f.getModifiers()) && Modifier.isFinal(f.getModifiers()),
                "field " + f.getName() + " is private final (immutable carrier)");
        }

        LoweringFailureDetail detail = new LoweringFailureDetail(
            "a.b", SemanticCapability.MODULES, "INDEX_INTERNAL_ERROR_SENTINEL",
            SemanticProfile.DEAL_V1_2_INT32, "deal.semantic-ir/1", "CheckedProjectBuilder");
        check("a.b".equals(detail.module()), "module accessor");
        check(detail.capability() == SemanticCapability.MODULES, "capability accessor");
        check("INDEX_INTERNAL_ERROR_SENTINEL".equals(detail.validatorRule()),
            "validatorRule accessor");
        check(detail.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
            "semanticProfile accessor");
        check("deal.semantic-ir/1".equals(detail.irVersion()), "irVersion accessor");
        check("CheckedProjectBuilder".equals(detail.origin()), "origin accessor");
    }

    // =========================================================================
    // SharedValueSemantics (ISSUE-0390, design I2)
    // =========================================================================

    /** A distinct caller-supplied operation origin for one row under test. */
    private static SourceOrigin origin(String label) {
        return new SourceOrigin(label, SourceSpan.synthetic(label),
            SourceOriginKind.SYNTHETIC, new AnchorId(1), null);
    }

    private static void expectValue(SharedValueSemantics.Int32Result result, int value,
                                    String what) {
        if (result instanceof SharedValueSemantics.Int32Result.Value v) {
            check(v.value() == value,
                what + ": expected Value(" + value + "), got Value(" + v.value() + ")");
        } else {
            SharedValueSemantics.Int32Result.Fail f =
                (SharedValueSemantics.Int32Result.Fail) result;
            fail(what + ": expected Value(" + value + ") but got Fail(" + f.code().code()
                + ", \"" + f.template() + "\")");
        }
    }

    private static void expectFail(SharedValueSemantics.Int32Result result, String code,
                                   String template, String what) {
        if (result instanceof SharedValueSemantics.Int32Result.Fail f) {
            check(code.equals(f.code().code()),
                what + ": fail code " + code + " (got " + f.code().code() + ")");
            check(f.code() == DiagnosticCode.fromCode(code),
                what + ": fail code resolves through fromCode");
            check(template.equals(f.template()),
                what + ": fail template exactly \"" + template + "\" (got \""
                    + f.template() + "\")");
        } else {
            SharedValueSemantics.Int32Result.Value v =
                (SharedValueSemantics.Int32Result.Value) result;
            fail(what + ": expected Fail(" + code + ", \"" + template
                + "\") but got Value(" + v.value() + ")");
        }
    }

    /** Failure with the caller-supplied origin carried by identity. */
    private static void expectFailAt(SharedValueSemantics.Int32Result result, String code,
                                     String template, SourceOrigin origin, String what) {
        expectFail(result, code, template, what);
        if (result instanceof SharedValueSemantics.Int32Result.Fail f) {
            check(f.origin() == origin,
                what + ": the caller-supplied origin is carried by identity");
        }
    }

    static void testSharedValueSemanticsSurface() {
        System.out.println("-- SharedValueSemantics surface (pure, static, closed) --");

        Class<SharedValueSemantics> type = SharedValueSemantics.class;
        check(Modifier.isFinal(type.getModifiers()),
            "SharedValueSemantics is final (no subclass extension point)");
        Constructor<?>[] ctors = type.getDeclaredConstructors();
        check(ctors.length == 1 && !Modifier.isPublic(ctors[0].getModifiers()),
            "SharedValueSemantics has exactly one non-public constructor (no instances)");
        boolean hasInstanceFields = false;
        for (Field f : type.getDeclaredFields()) {
            if (!Modifier.isStatic(f.getModifiers())) {
                hasInstanceFields = true;
            }
        }
        check(!hasInstanceFields, "SharedValueSemantics declares no instance state");
        for (Method m : type.getDeclaredMethods()) {
            if (Modifier.isPublic(m.getModifiers()) && !Modifier.isStatic(m.getModifiers())) {
                fail("SharedValueSemantics public entry point is static: " + m);
            }
        }

        check(SharedValueSemantics.INT32_MIN == -2147483648,
            "INT32_MIN pins -2147483648");
        check(SharedValueSemantics.INT32_MAX == 2147483647,
            "INT32_MAX pins 2147483647");

        // Int32Result = Value(int) | Fail(code, template, origin).
        Class<SharedValueSemantics.Int32Result> ir = SharedValueSemantics.Int32Result.class;
        check(ir.isInterface(), "Int32Result is an interface");
        check(ir.isSealed(), "Int32Result is sealed");
        Class<?>[] permitted = ir.getPermittedSubclasses();
        check(permitted != null && permitted.length == 2,
            "Int32Result permits exactly Value and Fail; got "
                + Arrays.toString(permitted));
        RecordComponent[] valueComponents =
            SharedValueSemantics.Int32Result.Value.class.getRecordComponents();
        check(valueComponents.length == 1 && valueComponents[0].getType() == int.class,
            "Value is a record with exactly one int component");
        RecordComponent[] failComponents =
            SharedValueSemantics.Int32Result.Fail.class.getRecordComponents();
        check(failComponents.length == 3
                && failComponents[0].getType() == DiagnosticCode.class
                && failComponents[1].getType() == String.class
                && failComponents[2].getType() == SourceOrigin.class,
            "Fail is a record with exactly (DiagnosticCode, String, SourceOrigin) components");

        // Fail fails closed on null components.
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.Int32Result.fail(null, "int out of safe range",
                origin("null-code")),
            "Fail(null code) fails closed");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.Int32Result.fail(DiagnosticCode.E8004, null,
                origin("null-template")),
            "Fail(null template) fails closed");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.Int32Result.fail(DiagnosticCode.E8004,
                "int out of safe range", null),
            "Fail(null origin) fails closed");

        // A null origin fails closed on every failing-capable operation.
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Add(1, 1, null), "int32Add(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Sub(1, 1, null), "int32Sub(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Mul(1, 1, null), "int32Mul(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Neg(1, null), "int32Neg(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Div(1, 1, null), "int32Div(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Mod(1, 1, null), "int32Mod(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.int32Pow(1, 1, null), "int32Pow(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.intFromNumber(1.0, null),
            "intFromNumber(null origin)");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.checkInt32Integral(1L, null),
            "checkInt32Integral(null origin)");
    }

    static void testSharedValueSemanticsInt32Arithmetic() {
        System.out.println("-- Int32 arithmetic: INT32_RESULT, both signs --");

        SourceOrigin ok = origin("add-ok");
        SourceOrigin over = origin("add-over");
        SourceOrigin under = origin("add-under");
        SourceOrigin mulOk = origin("mul-ok");
        SourceOrigin mulOver = origin("mul-over");
        SourceOrigin negOk = origin("neg-ok");
        SourceOrigin negOver = origin("neg-over");

        // add
        expectValue(SharedValueSemantics.int32Add(2147483647, 0, ok),
            2147483647, "add max + 0");
        expectValue(SharedValueSemantics.int32Add(-2147483648, 0, ok),
            -2147483648, "add min + 0");
        expectValue(SharedValueSemantics.int32Add(0, 0, ok), 0, "add 0 + 0");
        expectValue(SharedValueSemantics.int32Add(1073741824, 1073741823, ok),
            2147483647, "add boundary sum");
        expectFailAt(SharedValueSemantics.int32Add(2147483647, 1, over),
            "E8004", "int out of safe range", over, "add max + 1");
        expectFailAt(SharedValueSemantics.int32Add(-2147483648, -1, under),
            "E8004", "int out of safe range", under, "add min + -1");
        expectFailAt(SharedValueSemantics.int32Add(1073741824, 1073741824, over),
            "E8004", "int out of safe range", over, "add 2^30 + 2^30");

        // sub
        expectValue(SharedValueSemantics.int32Sub(-2147483648, 0, ok),
            -2147483648, "sub min - 0");
        expectValue(SharedValueSemantics.int32Sub(2147483647, 2147483647, ok),
            0, "sub x - x");
        expectValue(SharedValueSemantics.int32Sub(0, 2147483647, ok),
            -2147483647, "sub 0 - max");
        expectFailAt(SharedValueSemantics.int32Sub(-2147483648, 1, under),
            "E8004", "int out of safe range", under, "sub min - 1");
        expectFailAt(SharedValueSemantics.int32Sub(2147483647, -1, over),
            "E8004", "int out of safe range", over, "sub max - -1");

        // mul
        expectValue(SharedValueSemantics.int32Mul(0, -2147483648, mulOk),
            0, "mul 0 * min");
        expectValue(SharedValueSemantics.int32Mul(1, -2147483648, mulOk),
            -2147483648, "mul 1 * min");
        expectValue(SharedValueSemantics.int32Mul(-1, 2147483647, mulOk),
            -2147483647, "mul -1 * max");
        expectValue(SharedValueSemantics.int32Mul(46340, 46340, mulOk),
            2147395600, "mul boundary product");
        expectFailAt(SharedValueSemantics.int32Mul(2147483647, 2, mulOver),
            "E8004", "int out of safe range", mulOver, "mul max * 2");
        expectFailAt(SharedValueSemantics.int32Mul(-2147483648, 2, mulOver),
            "E8004", "int out of safe range", mulOver, "mul min * 2");
        expectFailAt(SharedValueSemantics.int32Mul(46341, 46341, mulOver),
            "E8004", "int out of safe range", mulOver, "mul 46341 * 46341");
        expectFailAt(SharedValueSemantics.int32Mul(-46341, -46341, mulOver),
            "E8004", "int out of safe range", mulOver, "mul -46341 * -46341");

        // neg
        expectValue(SharedValueSemantics.int32Neg(0, negOk), 0, "neg 0 -> 0");
        expectValue(SharedValueSemantics.int32Neg(5, negOk), -5, "neg 5");
        expectValue(SharedValueSemantics.int32Neg(-5, negOk), 5, "neg -5");
        expectValue(SharedValueSemantics.int32Neg(2147483647, negOk),
            -2147483647, "neg max");
        expectValue(SharedValueSemantics.int32Neg(-2147483647, negOk),
            2147483647, "neg -max");
        expectFailAt(SharedValueSemantics.int32Neg(-2147483648, negOver),
            "E8004", "int out of safe range", negOver, "neg min -> E8004");
    }

    static void testSharedValueSemanticsInt32DivMod() {
        System.out.println("-- Int32 div/mod: INT32_DIVISOR_THEN_RESULT --");

        SourceOrigin divZero = origin("div-zero");
        SourceOrigin modZero = origin("mod-zero");
        SourceOrigin trunc = origin("div-trunc");
        SourceOrigin ok = origin("div-ok");
        SourceOrigin minNegOne = origin("div-min-neg-one");
        SourceOrigin modMinNegOne = origin("mod-min-neg-one");

        // Zero divisor is E8005 first — before any range gate.
        expectFailAt(SharedValueSemantics.int32Div(1, 0, divZero),
            "E8005", "integer division by zero", divZero, "div 1 / 0");
        expectFailAt(SharedValueSemantics.int32Div(-2147483648, 0, divZero),
            "E8005", "integer division by zero", divZero,
            "div min / 0 (E8005 wins)");
        expectFailAt(SharedValueSemantics.int32Div(0, 0, divZero),
            "E8005", "integer division by zero", divZero, "div 0 / 0");
        expectFailAt(SharedValueSemantics.int32Mod(0, 0, modZero),
            "E8005", "integer division by zero", modZero, "mod 0 % 0");
        expectFailAt(SharedValueSemantics.int32Mod(-2147483648, 0, modZero),
            "E8005", "integer division by zero", modZero,
            "mod min % 0 (E8005 wins)");

        // Truncation toward zero, both signs.
        expectValue(SharedValueSemantics.int32Div(5, 2, trunc), 2,
            "div 5 / 2 = 2");
        expectValue(SharedValueSemantics.int32Div(-5, 2, trunc), -2,
            "div -5 / 2 = -2");
        expectValue(SharedValueSemantics.int32Div(5, -2, trunc), -2,
            "div 5 / -2 = -2");
        expectValue(SharedValueSemantics.int32Div(-5, -2, trunc), 2,
            "div -5 / -2 = 2");
        expectValue(SharedValueSemantics.int32Mod(5, 2, trunc), 1,
            "mod 5 % 2 = 1");
        expectValue(SharedValueSemantics.int32Mod(-5, 2, trunc), -1,
            "mod -5 % 2 = -1");
        expectValue(SharedValueSemantics.int32Mod(5, -2, trunc), 1,
            "mod 5 % -2 = 1");
        expectValue(SharedValueSemantics.int32Mod(-5, -2, trunc), -1,
            "mod -5 % -2 = -1");

        // Boundaries.
        expectValue(SharedValueSemantics.int32Div(2147483647, 1, ok),
            2147483647, "div max / 1");
        expectValue(SharedValueSemantics.int32Div(2147483647, -1, ok),
            -2147483647, "div max / -1");
        expectValue(SharedValueSemantics.int32Div(-2147483648, 1, ok),
            -2147483648, "div min / 1");
        expectValue(SharedValueSemantics.int32Div(-2147483648, 2, ok),
            -1073741824, "div min / 2");
        expectValue(SharedValueSemantics.int32Mod(-2147483648, 2147483647, ok),
            -1, "mod min % max = -1");
        expectFailAt(SharedValueSemantics.int32Div(-2147483648, -1, minNegOne),
            "E8004", "int out of safe range", minNegOne,
            "div min / -1 -> E8004");
        expectValue(SharedValueSemantics.int32Mod(-2147483648, -1, modMinNegOne),
            0, "mod min % -1 = 0 (truncated remainder)");
    }

    static void testSharedValueSemanticsInt32Pow() {
        System.out.println("-- Int32 pow: INT32_EXPONENT_THEN_RESULT --");

        SourceOrigin negExp = origin("pow-neg-exp");
        SourceOrigin ok = origin("pow-ok");
        SourceOrigin over = origin("pow-over");
        SourceOrigin pow62 = origin("pow-62");
        SourceOrigin pow63 = origin("pow-63");
        SourceOrigin pow1024 = origin("pow-1024");
        SourceOrigin pow1024Neg = origin("pow-1024-neg");
        SourceOrigin powInf = origin("pow-inf");

        // Negative exponent is E8006 first — even for a zero base.
        expectFailAt(SharedValueSemantics.int32Pow(2, -1, negExp),
            "E8006", "integer exponent must be non-negative", negExp,
            "pow 2 ** -1 -> E8006");
        expectFailAt(SharedValueSemantics.int32Pow(0, -1, negExp),
            "E8006", "integer exponent must be non-negative", negExp,
            "pow 0 ** -1 -> E8006 first");
        expectFailAt(SharedValueSemantics.int32Pow(-2147483648, -2147483648, negExp),
            "E8006", "integer exponent must be non-negative", negExp,
            "pow min ** min -> E8006 first");

        // Exact in-range and boundary values.
        expectValue(SharedValueSemantics.int32Pow(0, 0, ok), 1,
            "pow 0 ** 0 = 1");
        expectValue(SharedValueSemantics.int32Pow(2, 0, ok), 1,
            "pow 2 ** 0 = 1");
        expectValue(SharedValueSemantics.int32Pow(-2147483648, 0, ok), 1,
            "pow min ** 0 = 1");
        expectValue(SharedValueSemantics.int32Pow(0, 5, ok), 0,
            "pow 0 ** 5 = 0");
        expectValue(SharedValueSemantics.int32Pow(1, 2147483647, ok), 1,
            "pow 1 ** max = 1");
        expectValue(SharedValueSemantics.int32Pow(-1, 2147483647, ok), -1,
            "pow -1 ** odd = -1");
        expectValue(SharedValueSemantics.int32Pow(-1, 2147483646, ok), 1,
            "pow -1 ** even = 1");
        expectValue(SharedValueSemantics.int32Pow(2, 30, ok), 1073741824,
            "pow 2 ** 30");
        expectValue(SharedValueSemantics.int32Pow(-2, 31, ok), -2147483648,
            "pow -2 ** 31 = min");
        expectValue(SharedValueSemantics.int32Pow(2147483647, 1, ok),
            2147483647, "pow max ** 1");
        expectValue(SharedValueSemantics.int32Pow(-2147483648, 1, ok),
            -2147483648, "pow min ** 1");

        // Finite out-of-range band -> E8004 (exact long, then the ±2^31 gate).
        expectFailAt(SharedValueSemantics.int32Pow(2, 31, over),
            "E8004", "int out of safe range", over, "pow 2 ** 31");
        expectFailAt(SharedValueSemantics.int32Pow(-2, 32, over),
            "E8004", "int out of safe range", over, "pow -2 ** 32");
        expectFailAt(SharedValueSemantics.int32Pow(-2147483648, 2, over),
            "E8004", "int out of safe range", over, "pow min ** 2");
        expectFailAt(SharedValueSemantics.int32Pow(2, 62, pow62),
            "E8004", "int out of safe range", pow62,
            "pow 2 ** 62 -> E8004 (finite band)");
        expectFailAt(SharedValueSemantics.int32Pow(-2, 63, pow63),
            "E8004", "int out of safe range", pow63,
            "pow -2 ** 63 -> E8004 (exactly in-long, out of range)");
        expectFailAt(SharedValueSemantics.int32Pow(2, 63, over),
            "E8004", "int out of safe range", over,
            "pow 2 ** 63 -> E8004 (long overflow, finite classification)");
        expectFailAt(SharedValueSemantics.int32Pow(-2, 64, over),
            "E8004", "int out of safe range", over,
            "pow -2 ** 64 -> E8004 (long overflow via squaring, finite)");
        expectFailAt(SharedValueSemantics.int32Pow(3, 64, over),
            "E8004", "int out of safe range", over,
            "pow 3 ** 64 -> E8004 (long overflow, finite)");

        // Infinity band -> E8001 expected int, got infinity (sign-insensitive).
        expectFailAt(SharedValueSemantics.int32Pow(2, 1024, pow1024),
            "E8001", "expected int, got infinity", pow1024,
            "pow 2 ** 1024 -> E8001 infinity band");
        expectFailAt(SharedValueSemantics.int32Pow(-2, 1024, pow1024Neg),
            "E8001", "expected int, got infinity", pow1024Neg,
            "pow -2 ** 1024 -> E8001 (sign-insensitive classification)");
        expectFailAt(SharedValueSemantics.int32Pow(2, 1025, powInf),
            "E8001", "expected int, got infinity", powInf,
            "pow 2 ** 1025 -> E8001");
    }

    static void testSharedValueSemanticsConversion() {
        System.out.println("-- Conversions: INT_CONVERSION order, NUMBER_CONVERSION, -0 --");

        SourceOrigin nan = origin("cvt-nan");
        SourceOrigin inf = origin("cvt-inf");
        SourceOrigin frac = origin("cvt-frac");
        SourceOrigin order = origin("cvt-order");
        SourceOrigin range = origin("cvt-range");
        SourceOrigin ok = origin("cvt-ok");
        SourceOrigin negZero = origin("cvt-negzero");
        SourceOrigin checkOk = origin("check-ok");
        SourceOrigin checkOver = origin("check-over");

        // intFromNumber in the normative order: NaN, then infinity, then
        // fractional, then integral out of range.
        expectFailAt(SharedValueSemantics.intFromNumber(Double.NaN, nan),
            "E8001", "expected int, got NaN", nan, "int(NaN)");
        expectFailAt(SharedValueSemantics.intFromNumber(Double.POSITIVE_INFINITY, inf),
            "E8001", "expected int, got infinity", inf, "int(+inf)");
        expectFailAt(SharedValueSemantics.intFromNumber(Double.NEGATIVE_INFINITY, inf),
            "E8001", "expected int, got infinity", inf, "int(-inf)");
        expectFailAt(SharedValueSemantics.intFromNumber(0.5, frac),
            "E8001", "expected int, got non-integer number", frac,
            "int(0.5)");
        expectFailAt(SharedValueSemantics.intFromNumber(-0.5, frac),
            "E8001", "expected int, got non-integer number", frac,
            "int(-0.5)");
        expectFailAt(SharedValueSemantics.intFromNumber(2147483647.999, frac),
            "E8001", "expected int, got non-integer number", frac,
            "int(max - epsilon) fractional");
        expectFailAt(SharedValueSemantics.intFromNumber(-2147483648.5, frac),
            "E8001", "expected int, got non-integer number", frac,
            "int(min - 0.5) fractional");
        expectFailAt(SharedValueSemantics.intFromNumber(2147483648.5, order),
            "E8001", "expected int, got non-integer number", order,
            "int(2^31 + 0.5): fractional wins over range (normative order)");
        expectFailAt(SharedValueSemantics.intFromNumber(2147483648.0, range),
            "E8004", "int out of safe range", range, "int(2^31)");
        expectFailAt(SharedValueSemantics.intFromNumber(-2147483649.0, range),
            "E8004", "int out of safe range", range, "int(-2^31 - 1)");
        expectFailAt(SharedValueSemantics.intFromNumber(9007199254740992.0, range),
            "E8004", "int out of safe range", range, "int(2^53)");
        expectFailAt(SharedValueSemantics.intFromNumber(1e300, range),
            "E8004", "int out of safe range", range, "int(1e300)");
        expectValue(SharedValueSemantics.intFromNumber(2147483647.0, ok),
            2147483647, "int(max)");
        expectValue(SharedValueSemantics.intFromNumber(-2147483648.0, ok),
            -2147483648, "int(min)");
        expectValue(SharedValueSemantics.intFromNumber(0.0, ok), 0,
            "int(0.0)");
        expectValue(SharedValueSemantics.intFromNumber(-0.0, negZero), 0,
            "int(-0.0) normalizes to 0");
        int normalized = ((SharedValueSemantics.Int32Result.Value)
            SharedValueSemantics.intFromNumber(-0.0, negZero)).value();
        check(1.0 / (double) normalized == Double.POSITIVE_INFINITY,
            "1 / int(-0.0) is +Infinity (the normalized value is +0, not -0)");

        // checkInt32Integral: the descriptor-path tail after kind checks.
        expectValue(SharedValueSemantics.checkInt32Integral(-2147483648L, checkOk),
            -2147483648, "checkInt32Integral(min)");
        expectValue(SharedValueSemantics.checkInt32Integral(2147483647L, checkOk),
            2147483647, "checkInt32Integral(max)");
        expectValue(SharedValueSemantics.checkInt32Integral(0L, checkOk), 0,
            "checkInt32Integral(0)");
        expectFailAt(SharedValueSemantics.checkInt32Integral(-2147483649L, checkOver),
            "E8004", "int out of safe range", checkOver,
            "checkInt32Integral(min - 1)");
        expectFailAt(SharedValueSemantics.checkInt32Integral(2147483648L, checkOver),
            "E8004", "int out of safe range", checkOver,
            "checkInt32Integral(max + 1)");
        expectFailAt(SharedValueSemantics.checkInt32Integral(Long.MIN_VALUE, checkOver),
            "E8004", "int out of safe range", checkOver,
            "checkInt32Integral(Long.MIN_VALUE)");
        expectFailAt(SharedValueSemantics.checkInt32Integral(Long.MAX_VALUE, checkOver),
            "E8004", "int out of safe range", checkOver,
            "checkInt32Integral(Long.MAX_VALUE)");

        // numberFromInt: exact double for every int32.
        check(SharedValueSemantics.numberFromInt(2147483647L) == 2147483647.0,
            "numberFromInt(max) == 2147483647.0 exact");
        check(SharedValueSemantics.numberFromInt(-2147483648L) == -2147483648.0,
            "numberFromInt(min) == -2147483648.0 exact");
        check(SharedValueSemantics.numberFromInt(0L) == 0.0
                && Double.doubleToRawLongBits(SharedValueSemantics.numberFromInt(0L)) == 0L,
            "numberFromInt(0) == +0.0");
        check(SharedValueSemantics.numberFromInt(16777217L) == 16777217.0,
            "numberFromInt(16777217) == 16777217.0 exact");

        // The normalized -0 proof: dividing by the normalized int gives
        // +Infinity, never -Infinity.
        check(SharedValueSemantics.numberDiv(1.0, (double) normalized)
                == Double.POSITIVE_INFINITY,
            "numberDiv(1.0, int(-0.0)) = +Infinity (normalized to +0)");
        check(Double.isNaN(SharedValueSemantics.numberDiv(0.0, (double) normalized)),
            "numberDiv(0.0, int(-0.0)) = NaN");
    }

    static void testSharedValueSemanticsNumberOps() {
        System.out.println("-- Number ops: IEEE add/sub/mul/div/neg, floor-mod --");

        check(SharedValueSemantics.numberAdd(2.5, 4.0) == 6.5, "numberAdd 2.5 + 4.0");
        check(SharedValueSemantics.numberSub(2.5, 4.0) == -1.5, "numberSub 2.5 - 4.0");
        check(SharedValueSemantics.numberMul(2.5, 4.0) == 10.0, "numberMul 2.5 * 4.0");
        check(SharedValueSemantics.numberAdd(0.0, -0.0) == 0.0,
            "numberAdd +0 + -0 = +0 (IEEE)");
        check(Double.isNaN(SharedValueSemantics.numberMul(
                SharedValueSemantics.numberDiv(1.0, 0.0), 0.0)),
            "numberMul(inf, 0) = NaN (IEEE)");

        // IEEE div-by-zero.
        check(SharedValueSemantics.numberDiv(1.0, 0.0) == Double.POSITIVE_INFINITY,
            "numberDiv 1.0 / 0.0 = +Infinity");
        check(SharedValueSemantics.numberDiv(-1.0, 0.0) == Double.NEGATIVE_INFINITY,
            "numberDiv -1.0 / 0.0 = -Infinity");
        check(SharedValueSemantics.numberDiv(1.0, -0.0) == Double.NEGATIVE_INFINITY,
            "numberDiv 1.0 / -0.0 = -Infinity (IEEE zero sign)");
        check(Double.isNaN(SharedValueSemantics.numberDiv(0.0, 0.0)),
            "numberDiv 0.0 / 0.0 = NaN");
        check(Double.isNaN(SharedValueSemantics.numberDiv(0.0, -0.0)),
            "numberDiv 0.0 / -0.0 = NaN");

        // IEEE negation, incl. the -0 -> +0 rule.
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberNeg(-0.0)) == 0L,
            "numberNeg -(-0.0) = +0.0 (raw bits)");
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberNeg(0.0))
                == Double.doubleToRawLongBits(-0.0),
            "numberNeg -(0.0) = -0.0 (raw bits)");
        check(SharedValueSemantics.numberNeg(5.5) == -5.5, "numberNeg 5.5");

        // Floor-mod signs: a - floor(a/b)*b.
        check(SharedValueSemantics.numberModFloor(7.0, 3.0) == 1.0,
            "numberModFloor 7 mod 3 = 1");
        check(SharedValueSemantics.numberModFloor(-7.0, 3.0) == 2.0,
            "numberModFloor -7 mod 3 = 2");
        check(SharedValueSemantics.numberModFloor(7.0, -3.0) == -2.0,
            "numberModFloor 7 mod -3 = -2");
        check(SharedValueSemantics.numberModFloor(-7.0, -3.0) == -1.0,
            "numberModFloor -7 mod -3 = -1");
        check(SharedValueSemantics.numberModFloor(5.5, 2.0) == 1.5,
            "numberModFloor 5.5 mod 2 = 1.5");
        check(SharedValueSemantics.numberModFloor(-5.5, 2.0) == 0.5,
            "numberModFloor -5.5 mod 2 = 0.5");
        check(Double.isNaN(SharedValueSemantics.numberModFloor(Double.NaN, 3.0)),
            "numberModFloor NaN propagates NaN");
        check(Double.isNaN(SharedValueSemantics.numberModFloor(1.0, 0.0)),
            "numberModFloor x mod 0 = NaN");
    }

    static void testSharedValueSemanticsNumberPow() {
        System.out.println("-- numberPow: the pinned IEEE-754 special-case table --");

        // Ordinary exact cases.
        check(SharedValueSemantics.numberPow(2.0, 10.0) == 1024.0,
            "2.0 ** 10.0 = 1024.0");
        check(SharedValueSemantics.numberPow(-2.0, 3.0) == -8.0,
            "(-2.0) ** 3.0 = -8.0");
        check(SharedValueSemantics.numberPow(-2.0, 4.0) == 16.0,
            "(-2.0) ** 4.0 = 16.0 (parity)");
        check(SharedValueSemantics.numberPow(-2.0, -3.0) == -0.125,
            "(-2.0) ** -3.0 = -0.125 (parity)");
        check(SharedValueSemantics.numberPow(-2.0, -4.0) == 0.0625,
            "(-2.0) ** -4.0 = 0.0625");

        // pow(x, ±0) = 1 for every x incl. NaN.
        check(SharedValueSemantics.numberPow(0.0, 0.0) == 1.0, "0.0 ** 0.0 = 1.0");
        check(SharedValueSemantics.numberPow(-0.0, 0.0) == 1.0, "(-0.0) ** 0.0 = 1.0");
        check(SharedValueSemantics.numberPow(Double.NaN, 0.0) == 1.0, "NaN ** 0.0 = 1.0");
        check(SharedValueSemantics.numberPow(2.0, -0.0) == 1.0, "2.0 ** -0.0 = 1.0");

        // pow(1, y) = 1 for every y incl. NaN (the first pinned correction).
        check(SharedValueSemantics.numberPow(1.0, Double.NaN) == 1.0,
            "1.0 ** NaN = 1.0 (Java-vs-IEEE correction)");
        check(SharedValueSemantics.numberPow(1.0, 5.0) == 1.0, "1.0 ** 5.0 = 1.0");

        // pow(±1, ±Infinity) = 1 (the second pinned correction).
        check(SharedValueSemantics.numberPow(1.0, Double.POSITIVE_INFINITY) == 1.0,
            "1.0 ** +Infinity = 1.0 (Java-vs-IEEE correction)");
        check(SharedValueSemantics.numberPow(1.0, Double.NEGATIVE_INFINITY) == 1.0,
            "1.0 ** -Infinity = 1.0 (Java-vs-IEEE correction)");
        check(SharedValueSemantics.numberPow(-1.0, Double.POSITIVE_INFINITY) == 1.0,
            "(-1.0) ** +Infinity = 1.0 (Java-vs-IEEE correction)");
        check(SharedValueSemantics.numberPow(-1.0, Double.NEGATIVE_INFINITY) == 1.0,
            "(-1.0) ** -Infinity = 1.0 (Java-vs-IEEE correction)");

        // pow(x, NaN) = NaN for x != 1.
        check(Double.isNaN(SharedValueSemantics.numberPow(Double.NaN, Double.NaN)),
            "NaN ** NaN = NaN");
        check(Double.isNaN(SharedValueSemantics.numberPow(2.0, Double.NaN)),
            "2.0 ** NaN = NaN");
        check(Double.isNaN(SharedValueSemantics.numberPow(0.0, Double.NaN)),
            "0.0 ** NaN = NaN");

        // ±0 bases: sign rules for negative odd-integer y.
        check(SharedValueSemantics.numberPow(0.0, -1.0) == Double.POSITIVE_INFINITY,
            "0.0 ** -1.0 = +Infinity");
        check(SharedValueSemantics.numberPow(-0.0, -1.0) == Double.NEGATIVE_INFINITY,
            "(-0.0) ** -1.0 = -Infinity (odd y preserves zero sign)");
        check(SharedValueSemantics.numberPow(-0.0, -3.0) == Double.NEGATIVE_INFINITY,
            "(-0.0) ** -3.0 = -Infinity (odd y)");
        check(SharedValueSemantics.numberPow(-0.0, -2.0) == Double.POSITIVE_INFINITY,
            "(-0.0) ** -2.0 = +Infinity (even y)");
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberPow(0.0, 3.0)) == 0L,
            "0.0 ** 3.0 = +0.0 (raw bits)");
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberPow(-0.0, 3.0))
                == Double.doubleToRawLongBits(-0.0),
            "(-0.0) ** 3.0 = -0.0 (odd y preserves zero sign)");
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberPow(-0.0, 2.0)) == 0L,
            "(-0.0) ** 2.0 = +0.0 (even y)");

        // ±Infinity bases: IEEE sign/parity rules.
        check(SharedValueSemantics.numberPow(Double.POSITIVE_INFINITY, 3.0)
                == Double.POSITIVE_INFINITY,
            "(+inf) ** 3.0 = +Infinity");
        check(SharedValueSemantics.numberPow(Double.POSITIVE_INFINITY, -3.0) == 0.0,
            "(+inf) ** -3.0 = +0.0");
        check(SharedValueSemantics.numberPow(Double.NEGATIVE_INFINITY, 3.0)
                == Double.NEGATIVE_INFINITY,
            "(-inf) ** 3.0 = -Infinity (odd y)");
        check(SharedValueSemantics.numberPow(Double.NEGATIVE_INFINITY, 2.0)
                == Double.POSITIVE_INFINITY,
            "(-inf) ** 2.0 = +Infinity (even y)");
        check(Double.doubleToRawLongBits(
                SharedValueSemantics.numberPow(Double.NEGATIVE_INFINITY, -3.0))
                == Double.doubleToRawLongBits(-0.0),
            "(-inf) ** -3.0 = -0.0 (odd y)");
        check(Double.doubleToRawLongBits(
                SharedValueSemantics.numberPow(Double.NEGATIVE_INFINITY, -2.0)) == 0L,
            "(-inf) ** -2.0 = +0.0 (even y)");

        // Finite bases with infinite exponents.
        check(SharedValueSemantics.numberPow(2.0, Double.POSITIVE_INFINITY)
                == Double.POSITIVE_INFINITY,
            "2.0 ** +Infinity = +Infinity");
        check(SharedValueSemantics.numberPow(2.0, Double.NEGATIVE_INFINITY) == 0.0,
            "2.0 ** -Infinity = +0.0");
        check(SharedValueSemantics.numberPow(-2.0, Double.POSITIVE_INFINITY)
                == Double.POSITIVE_INFINITY,
            "(-2.0) ** +Infinity = +Infinity");
        check(SharedValueSemantics.numberPow(-2.0, Double.NEGATIVE_INFINITY) == 0.0,
            "(-2.0) ** -Infinity = +0.0");
        check(SharedValueSemantics.numberPow(0.5, Double.POSITIVE_INFINITY) == 0.0,
            "0.5 ** +Infinity = +0.0");
        check(SharedValueSemantics.numberPow(0.5, Double.NEGATIVE_INFINITY)
                == Double.POSITIVE_INFINITY,
            "0.5 ** -Infinity = +Infinity");
        check(Double.doubleToRawLongBits(
                SharedValueSemantics.numberPow(-0.5, Double.POSITIVE_INFINITY)) == 0L,
            "(-0.5) ** +Infinity = +0.0");
        check(SharedValueSemantics.numberPow(-0.5, Double.NEGATIVE_INFINITY)
                == Double.POSITIVE_INFINITY,
            "(-0.5) ** -Infinity = +Infinity");

        // Negative finite base with a non-integer exponent -> NaN.
        check(Double.isNaN(SharedValueSemantics.numberPow(-2.0, 0.5)),
            "(-2.0) ** 0.5 = NaN (fractional exponent)");
        check(Double.isNaN(SharedValueSemantics.numberPow(-2.0, 2.5)),
            "(-2.0) ** 2.5 = NaN (fractional exponent)");

        // Overflow to ±Infinity and underflow to ±0 per IEEE.
        check(SharedValueSemantics.numberPow(2.0, 1024.0) == Double.POSITIVE_INFINITY,
            "2.0 ** 1024.0 = +Infinity (overflow)");
        check(SharedValueSemantics.numberPow(-2.0, 1024.0) == Double.POSITIVE_INFINITY,
            "(-2.0) ** 1024.0 = +Infinity (overflow, even y)");
        check(SharedValueSemantics.numberPow(-2.0, 1025.0) == Double.NEGATIVE_INFINITY,
            "(-2.0) ** 1025.0 = -Infinity (overflow, odd y)");
        check(Double.doubleToRawLongBits(SharedValueSemantics.numberPow(2.0, -1075.0)) == 0L,
            "2.0 ** -1075.0 = +0.0 (underflow)");
        check(Double.doubleToRawLongBits(
                SharedValueSemantics.numberPow(-2.0, -1075.0))
                == Double.doubleToRawLongBits(-0.0),
            "(-2.0) ** -1075.0 = -0.0 (underflow, odd y)");
    }

    static void testSharedValueSemanticsComparisons() {
        System.out.println("-- Comparisons: exact int32, IEEE number incl. NaN --");

        check(SharedValueSemantics.boolNot(true) == false, "boolNot true = false");
        check(SharedValueSemantics.boolNot(false) == true, "boolNot false = true");

        check(SharedValueSemantics.int32Eq(5, 5), "int32Eq 5 == 5");
        check(!SharedValueSemantics.int32Eq(5, 6), "int32Eq 5 != 6");
        check(SharedValueSemantics.int32Ne(5, 6), "int32Ne 5 != 6");
        check(!SharedValueSemantics.int32Ne(5, 5), "int32Ne 5 == 5 false");
        check(SharedValueSemantics.int32Lt(-2147483648, 2147483647),
            "int32Lt min < max");
        check(!SharedValueSemantics.int32Lt(2147483647, 2147483647),
            "int32Lt max < max false");
        check(SharedValueSemantics.int32Le(-2147483648, -2147483648),
            "int32Le min <= min");
        check(!SharedValueSemantics.int32Le(2147483647, -2147483648),
            "int32Le max <= min false");
        check(SharedValueSemantics.int32Gt(2147483647, -2147483648),
            "int32Gt max > min");
        check(!SharedValueSemantics.int32Gt(-2147483648, -2147483648),
            "int32Gt min > min false");
        check(SharedValueSemantics.int32Ge(2147483647, 2147483647),
            "int32Ge max >= max");
        check(!SharedValueSemantics.int32Ge(-2147483648, 2147483647),
            "int32Ge min >= max false");

        check(!SharedValueSemantics.numberEq(Double.NaN, Double.NaN),
            "numberEq NaN != NaN");
        check(SharedValueSemantics.numberEq(-0.0, 0.0), "numberEq -0 == +0");
        check(SharedValueSemantics.numberEq(1.5, 1.5), "numberEq 1.5 == 1.5");
        check(SharedValueSemantics.numberNe(Double.NaN, Double.NaN),
            "numberNe NaN != NaN is true");
        check(!SharedValueSemantics.numberNe(-0.0, 0.0), "numberNe -0 != +0 false");
        check(SharedValueSemantics.numberNe(1.5, 2.5), "numberNe 1.5 != 2.5");
        check(!SharedValueSemantics.numberLt(Double.NaN, 1.0),
            "numberLt NaN < 1 false");
        check(!SharedValueSemantics.numberLt(1.0, Double.NaN),
            "numberLt 1 < NaN false");
        check(!SharedValueSemantics.numberLe(Double.NaN, Double.NaN),
            "numberLe NaN <= NaN false");
        check(!SharedValueSemantics.numberGt(Double.NaN, 1.0),
            "numberGt NaN > 1 false");
        check(!SharedValueSemantics.numberGe(1.0, Double.NaN),
            "numberGe 1 >= NaN false");
        check(!SharedValueSemantics.numberLt(-0.0, 0.0), "numberLt -0 < +0 false");
        check(SharedValueSemantics.numberLe(-0.0, 0.0), "numberLe -0 <= +0");
        check(SharedValueSemantics.numberLt(1.5, 2.5), "numberLt 1.5 < 2.5");
        check(SharedValueSemantics.numberGe(2.5, 1.5), "numberGe 2.5 >= 1.5");
        check(!SharedValueSemantics.numberLt(2.5, 1.5), "numberLt 2.5 < 1.5 false");
        check(!SharedValueSemantics.numberGe(1.5, 2.5), "numberGe 1.5 >= 2.5 false");
        check(SharedValueSemantics.numberLt(Double.NEGATIVE_INFINITY,
                Double.POSITIVE_INFINITY),
            "numberLt -inf < +inf");
        check(SharedValueSemantics.numberGt(Double.POSITIVE_INFINITY,
                Double.NEGATIVE_INFINITY),
            "numberGt +inf > -inf");
        check(SharedValueSemantics.numberLe(Double.NEGATIVE_INFINITY,
                Double.NEGATIVE_INFINITY),
            "numberLe -inf <= -inf");
        check(!SharedValueSemantics.numberLt(Double.POSITIVE_INFINITY,
                Double.POSITIVE_INFINITY),
            "numberLt +inf < +inf false");
        check(!SharedValueSemantics.numberLt(Double.POSITIVE_INFINITY, Double.NaN),
            "numberLt +inf < NaN false");
    }

    static void testSharedValueSemanticsOrigins() {
        System.out.println("-- Failure origins: caller-supplied operation origin per row --");

        SourceOrigin add = origin("origin-add");
        SourceOrigin div = origin("origin-div");
        SourceOrigin pow = origin("origin-pow");
        SourceOrigin cvt = origin("origin-cvt");
        expectFailAt(SharedValueSemantics.int32Add(2147483647, 1, add),
            "E8004", "int out of safe range", add, "add overflow origin");
        expectFailAt(SharedValueSemantics.int32Div(1, 0, div),
            "E8005", "integer division by zero", div, "div zero origin");
        expectFailAt(SharedValueSemantics.int32Pow(2, -1, pow),
            "E8006", "integer exponent must be non-negative", pow,
            "pow negative-exponent origin");
        expectFailAt(SharedValueSemantics.int32Pow(2, 1024, pow),
            "E8001", "expected int, got infinity", pow, "pow infinity-band origin");
        expectFailAt(SharedValueSemantics.intFromNumber(Double.NaN, cvt),
            "E8001", "expected int, got NaN", cvt, "conversion NaN origin");
        expectFailAt(SharedValueSemantics.checkInt32Integral(2147483648L, add),
            "E8004", "int out of safe range", add, "checkInt32Integral origin");
    }

    static void testSelectorPolicyCrossCheck() {
        System.out.println("-- Selector->policy cross-check against the closed table --");

        int covered = 0;
        for (BinarySelector selector : BinarySelector.values()) {
            FailurePolicyId primitivePolicy;
            boolean inRows;
            try {
                primitivePolicy = SharedValueSemantics.binarySelectorPolicy(selector);
                inRows = true;
            } catch (IllegalArgumentException outsideRows) {
                primitivePolicy = null;
                inRows = false;
            }
            if (inRows) {
                FailurePolicyId tablePolicy = SemanticIrValidator.binaryPolicy(selector);
                check(primitivePolicy == tablePolicy,
                    "binary selector " + selector.name() + ": primitive row policy "
                        + primitivePolicy + " agrees with the closed binaryPolicy table ("
                        + tablePolicy + ")");
                covered++;
            }
        }
        check(covered == 24,
            "the primitive covers exactly the 6 INT32_* + 6 NUMBER_* + 12 comparison "
                + "binary selectors (got " + covered + ")");

        // The selectors outside this primitive's rows fail closed.
        for (BinarySelector selector : List.of(BinarySelector.STRING_EQ,
                BinarySelector.STRING_NE, BinarySelector.STRING_LT,
                BinarySelector.STRING_LE, BinarySelector.STRING_GT,
                BinarySelector.STRING_GE, BinarySelector.BOOLEAN_EQ,
                BinarySelector.BOOLEAN_NE, BinarySelector.NULL_EQ,
                BinarySelector.NULL_NE, BinarySelector.NULLABLE_EQ,
                BinarySelector.NULLABLE_NE, BinarySelector.NULLABLE_NULL_EQ,
                BinarySelector.NULLABLE_NULL_NE, BinarySelector.REFERENCE_EQ,
                BinarySelector.REFERENCE_NE)) {
            expectThrows(IllegalArgumentException.class,
                () -> SharedValueSemantics.binarySelectorPolicy(selector),
                selector.name() + " is outside the primitive's rows and fails closed");
        }
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.binarySelectorPolicy(null),
            "binarySelectorPolicy(null) fails closed");

        // Unary rows: the primitive covers the complete unary selector set
        // and each projected policy agrees with the validator's closed
        // UNARY rule (INT32_NEG -> INT32_RESULT; NUMBER_NEG, BOOL_NOT ->
        // NO_DEAL_FAILURE).
        int unaryCovered = 0;
        for (UnarySelector selector : UnarySelector.values()) {
            FailurePolicyId primitivePolicy =
                SharedValueSemantics.unarySelectorPolicy(selector);
            FailurePolicyId tablePolicy = SemanticIrValidator.unaryPolicy(selector);
            check(primitivePolicy == tablePolicy,
                "unary selector " + selector.name() + ": primitive row policy "
                    + primitivePolicy + " agrees with the closed unaryPolicy rule ("
                    + tablePolicy + ")");
            unaryCovered++;
        }
        check(unaryCovered == 3,
            "the primitive covers exactly the three closed unary selectors (got "
                + unaryCovered + ")");
        expectThrows(NullPointerException.class,
            () -> SharedValueSemantics.unarySelectorPolicy(null),
            "unarySelectorPolicy(null) fails closed");
    }

    // =========================================================================
    // ISSUE-0395: the SemanticLowerer value-operation slice (I3) —
    // CONST/UNARY/BINARY/INTRINSIC_CALL with the fixed selector->policy
    // stamping, the LEGACY_SAFE_INT pre-lowering rejection, the pinned
    // one-line scalar descriptor rows, and the combined T1+T3 invocation
    // proof.
    // =========================================================================

    private static final ModuleId VALUE_MODULE = new ModuleId("valueops");
    private static final String VALUE_SOURCE_ID = "valueops.deal";
    private static final String VALUE_REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String VALUE_INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(VALUE_MODULE,
            new ExternalModuleInterface(VALUE_MODULE, ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(),
                InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    /** The three coverage rows a value-operation corpus produces (S4 detector rows verbatim). */
    private static Map<ConstructKind, List<SemanticOpKind>> valueCoverage() {
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            new LinkedHashMap<>();
        coverage.put(ConstructKind.SCALAR_LITERAL,
            ConstructKind.SCALAR_LITERAL.mappedOpKinds());
        coverage.put(ConstructKind.UNARY_ARITHMETIC_COMPARISON,
            ConstructKind.UNARY_ARITHMETIC_COMPARISON.mappedOpKinds());
        coverage.put(ConstructKind.CALL, ConstructKind.CALL.mappedOpKinds());
        return coverage;
    }

    private record ValueSlice(ProgramNode program, CheckResult checks) {
    }

    /** Lexes, parses (profile-aware v1.2), resolves, and checks one slice. */
    private static ValueSlice checkValueSlice(String source) {
        LexResult lex = new Lexer(source, VALUE_SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), VALUE_SOURCE_ID,
            SemanticProfile.DEAL_V1_2_INT32).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly under "
            + "DEAL_V1_2_INT32: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(VALUE_SOURCE_ID, null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(VALUE_SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), "the slice checks cleanly: "
            + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new ValueSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(ValueSlice slice) {
        return new CheckedModuleInput(VALUE_MODULE, VALUE_SOURCE_ID,
            Path.of(VALUE_SOURCE_ID), slice.program(), slice.checks(), List.of(), List.of(),
            CheckedModuleKind.IMPLEMENTATION);
    }

    private static SemanticLowerer.ModuleLowerer valueLowerer(CheckResult checks) {
        return new SemanticLowerer.ModuleLowerer(VALUE_MODULE, VALUE_SOURCE_ID, checks,
            SemanticIdAllocator.over(List.of(VALUE_MODULE)));
    }

    /** Source-order statement walk collecting every statement and expression. */
    private static void collectStatements(StatementNode node, List<StatementNode> outStatements,
                                          List<ExpressionNode> outExpressions) {
        if (node == null) {
            return;
        }
        outStatements.add(node);
        switch (node) {
            case FunctionDeclaration fd -> collectStatements(fd.body(), outStatements,
                outExpressions);
            case VariableDeclaration vd ->
                collectExpressions(vd.initializer(), outExpressions);
            case ReturnStatement rs ->
                rs.expr().ifPresent(e -> collectExpressions(e, outExpressions));
            case IfStatement is -> {
                collectExpressions(is.condition(), outExpressions);
                collectStatements(is.thenBlock(), outStatements, outExpressions);
                is.elseBranch().ifPresent(branch -> {
                    if (branch instanceof Either.Left<IfStatement, Block> left) {
                        collectStatements(left.value(), outStatements, outExpressions);
                    } else if (branch instanceof Either.Right<IfStatement, Block> right) {
                        collectStatements(right.value(), outStatements, outExpressions);
                    }
                });
            }
            case WhileStatement ws -> {
                collectExpressions(ws.condition(), outExpressions);
                collectStatements(ws.body(), outStatements, outExpressions);
            }
            case ForStatement fs -> {
                if (fs.init().isPresent()) {
                    ForInit init = fs.init().get();
                    if (init instanceof ForInit.VarDecl varDecl) {
                        collectStatements(varDecl.decl(), outStatements, outExpressions);
                    } else if (init instanceof ForInit.AssignExpr assignExpr) {
                        collectExpressions(assignExpr.expr(), outExpressions);
                    }
                }
                if (fs.condition().isPresent()) {
                    collectExpressions(fs.condition().get(), outExpressions);
                }
                if (fs.update().isPresent()) {
                    collectExpressions(fs.update().get(), outExpressions);
                }
                collectStatements(fs.body(), outStatements, outExpressions);
            }
            case ForOfStatement fos -> {
                collectExpressions(fos.iterable(), outExpressions);
                collectStatements(fos.body(), outStatements, outExpressions);
            }
            case ExpressionStatement es -> collectExpressions(es.expr(), outExpressions);
            case Block block -> block.statements().forEach(st ->
                collectStatements(st, outStatements, outExpressions));
            case TryStatement ts -> {
                collectStatements(ts.tryBlock(), outStatements, outExpressions);
                collectStatements(ts.catchBlock(), outStatements, outExpressions);
            }
            case ThrowStatement throwStatement ->
                collectExpressions(throwStatement.expr(), outExpressions);
            default -> { /* declarations without expression positions */ }
        }
    }

    /** Source-order expression walk collecting every subexpression. */
    private static void collectExpressions(ExpressionNode expr, List<ExpressionNode> out) {
        if (expr == null) {
            return;
        }
        out.add(expr);
        switch (expr) {
            case UnaryExpr u -> collectExpressions(u.expr(), out);
            case BinaryExpr b -> {
                collectExpressions(b.left(), out);
                collectExpressions(b.right(), out);
            }
            case CallExpr c -> {
                collectExpressions(c.callee(), out);
                c.args().forEach(a -> collectExpressions(a, out));
            }
            case MemberAccessExpr m -> collectExpressions(m.object(), out);
            case IndexExpr ix -> {
                collectExpressions(ix.array(), out);
                collectExpressions(ix.index(), out);
            }
            case ArrayLiteralExpr al -> al.elements().forEach(e -> collectExpressions(e, out));
            case ObjectLiteralExpr ol -> ol.properties().forEach(p ->
                collectExpressions(p.value(), out));
            case TemplateLiteralExpr tl -> tl.parts().forEach(p -> collectExpressions(p, out));
            case AwaitExpression aw -> collectExpressions(aw.callee(), out);
            default -> { /* literal and identifier leaves */ }
        }
    }

    /** The first AST node of the given class in source order, or null. */
    @SuppressWarnings("unchecked")
    private static <T> T first(ProgramNode program, Class<T> type) {
        List<StatementNode> statements = new ArrayList<>();
        List<ExpressionNode> expressions = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            collectStatements(statement, statements, expressions);
        }
        for (StatementNode statement : statements) {
            if (type.isInstance(statement)) {
                return (T) statement;
            }
        }
        for (ExpressionNode expression : expressions) {
            if (type.isInstance(expression)) {
                return (T) expression;
            }
        }
        return null;
    }

    private static void deleteRecursively(Path path) {
        try {
            if (path == null || !Files.exists(path)) {
                return;
            }
            try (var walk = Files.walk(path)) {
                walk.sorted(java.util.Comparator.reverseOrder()).forEach(p -> {
                    try {
                        Files.deleteIfExists(p);
                    } catch (Exception ignored) {
                        // Best-effort temp cleanup only; never part of a test result.
                    }
                });
            }
        } catch (Exception ignored) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    // -------------------------------------------------------------------------
    // I3 arms: CONST / UNARY / BINARY / INTRINSIC_CALL
    // -------------------------------------------------------------------------

    static void testValueConstAndUnaryArms() {
        System.out.println("-- I3 CONST/UNARY: selectors, policies, operand types, origins --");

        // CONST over the immediate-minus literal (the I1 parser invariant:
        // -2147483648 is the combined-token signed32 literal).
        ValueSlice min = checkValueSlice("function f(): int { return -2147483648 }");
        if (min != null) {
            LiteralExpr literal = first(min.program(), LiteralExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(min.checks());
            ValueId result = lowerer.lowerExpression(literal);
            check(lowerer.ops().size() == 1, "the literal produces exactly one op");
            SemanticOp op = lowerer.ops().get(0);
            check(op.kind() == SemanticOpKind.CONST
                    && op.payload() instanceof KindPayload.ConstPayload constPayload
                    && constPayload.value() instanceof ScalarValue.Int intValue
                    && intValue.value() == -2147483648,
                "CONST carries ScalarValue.Int(-2147483648) — the immediate-minus literal "
                    + "is signed32 by the I1 parser invariant");
            check(op.resultType() == RuntimeDescriptor.Int.INSTANCE,
                "CONST result type is the signed32 int descriptor");
            check(op.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                "CONST policy is NO_DEAL_FAILURE");
            check(op.result() == result && result instanceof ValueId,
                "CONST publishes a fresh ValueId result");
        }

        // UNARY INT32_NEG: -1 -> policy INT32_RESULT (validator-pinned unaryPolicy).
        ValueSlice negInt = checkValueSlice("function f(): int { return -1 }");
        if (negInt != null) {
            UnaryExpr unary = first(negInt.program(), UnaryExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(negInt.checks());
            lowerer.lowerExpression(unary);
            SemanticOp op = lowerer.ops().get(lowerer.ops().size() - 1);
            check(op.kind() == SemanticOpKind.UNARY
                    && op.payload() instanceof KindPayload.UnaryPayload unaryPayload
                    && unaryPayload.selector() == UnarySelector.INT32_NEG,
                "unary - over int produces UNARY INT32_NEG");
            check(op.failurePolicy() == FailurePolicyId.INT32_RESULT,
                "INT32_NEG is stamped INT32_RESULT from the closed unaryPolicy rule");
            check(op.operandTypes().size() == 1
                    && op.operandTypes().get(0) == RuntimeDescriptor.Int.INSTANCE,
                "the operand type is the pinned one-line int row (identity)");
            check(op.resultType() == RuntimeDescriptor.Int.INSTANCE,
                "the result type is the signed32 int descriptor");
        }

        // UNARY NUMBER_NEG: -1.5 -> NO_DEAL_FAILURE.
        ValueSlice negNumber = checkValueSlice("function f(): number { return -1.5 }");
        if (negNumber != null) {
            UnaryExpr unary = first(negNumber.program(), UnaryExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(negNumber.checks());
            lowerer.lowerExpression(unary);
            SemanticOp op = lowerer.ops().get(lowerer.ops().size() - 1);
            check(op.payload() instanceof KindPayload.UnaryPayload unaryPayload
                    && unaryPayload.selector() == UnarySelector.NUMBER_NEG,
                "unary - over number produces UNARY NUMBER_NEG");
            check(op.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE
                    && op.operandTypes().get(0) == RuntimeDescriptor.Number.INSTANCE
                    && op.resultType() == RuntimeDescriptor.Number.INSTANCE,
                "NUMBER_NEG is stamped NO_DEAL_FAILURE with the pinned one-line number "
                    + "rows (identity)");
        }

        // UNARY BOOL_NOT: !true -> NO_DEAL_FAILURE.
        ValueSlice not = checkValueSlice("function f(): boolean { return !true }");
        if (not != null) {
            UnaryExpr unary = first(not.program(), UnaryExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(not.checks());
            lowerer.lowerExpression(unary);
            SemanticOp op = lowerer.ops().get(lowerer.ops().size() - 1);
            check(op.payload() instanceof KindPayload.UnaryPayload unaryPayload
                    && unaryPayload.selector() == UnarySelector.BOOL_NOT,
                "unary ! over boolean produces UNARY BOOL_NOT");
            check(op.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE
                    && op.operandTypes().get(0) == RuntimeDescriptor.Boolean.INSTANCE
                    && op.resultType() == RuntimeDescriptor.Boolean.INSTANCE,
                "BOOL_NOT is stamped NO_DEAL_FAILURE with the pinned one-line boolean "
                    + "rows (identity)");
        }

        // --2147483648: the outer negation over the immediate-minus literal.
        ValueSlice doubleNeg = checkValueSlice("function f(): int { return --2147483648 }");
        if (doubleNeg != null) {
            UnaryExpr unary = first(doubleNeg.program(), UnaryExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(doubleNeg.checks());
            lowerer.lowerExpression(unary);
            List<SemanticOp> ops = lowerer.ops();
            check(ops.size() == 2
                    && ops.get(0).kind() == SemanticOpKind.CONST
                    && ops.get(1).kind() == SemanticOpKind.UNARY
                    && ops.get(1).payload() instanceof KindPayload.UnaryPayload up
                    && up.selector() == UnarySelector.INT32_NEG,
                "--2147483648 lowers to CONST(-2147483648) then UNARY INT32_NEG "
                    + "(the runtime E8004 belongs to execution, never to this slice)");
        }
    }

    static void testValueBinaryArms() {
        System.out.println("-- I3 BINARY: int32/number arithmetic selector rows and policies --");

        record BinaryCase(String expr, String returnType, BinarySelector selector,
                          FailurePolicyId policy) {
        }
        List<BinaryCase> cases = List.of(
            new BinaryCase("1 + 2", "int", BinarySelector.INT32_ADD,
                FailurePolicyId.INT32_RESULT),
            new BinaryCase("1 - 2", "int", BinarySelector.INT32_SUB,
                FailurePolicyId.INT32_RESULT),
            new BinaryCase("2 * 3", "int", BinarySelector.INT32_MUL,
                FailurePolicyId.INT32_RESULT),
            new BinaryCase("6 / 2", "int", BinarySelector.INT32_DIV_TRUNC,
                FailurePolicyId.INT32_DIVISOR_THEN_RESULT),
            new BinaryCase("7 % 3", "int", BinarySelector.INT32_MOD_TRUNC,
                FailurePolicyId.INT32_DIVISOR_THEN_RESULT),
            new BinaryCase("2 ** 30", "int", BinarySelector.INT32_POW,
                FailurePolicyId.INT32_EXPONENT_THEN_RESULT),
            new BinaryCase("1.5 + 2.5", "number", BinarySelector.NUMBER_ADD,
                FailurePolicyId.NO_DEAL_FAILURE),
            new BinaryCase("1.5 - 2.5", "number", BinarySelector.NUMBER_SUB,
                FailurePolicyId.NO_DEAL_FAILURE),
            new BinaryCase("1.5 * 2.5", "number", BinarySelector.NUMBER_MUL,
                FailurePolicyId.NO_DEAL_FAILURE),
            new BinaryCase("6.0 / 2.0", "number", BinarySelector.NUMBER_DIV_IEEE,
                FailurePolicyId.NO_DEAL_FAILURE),
            new BinaryCase("7.0 % 3.0", "number", BinarySelector.NUMBER_MOD_FLOOR,
                FailurePolicyId.NO_DEAL_FAILURE),
            new BinaryCase("2.0 ** 10.0", "number", BinarySelector.NUMBER_POW_IEEE,
                FailurePolicyId.NO_DEAL_FAILURE));
        int covered = 0;
        for (BinaryCase binaryCase : cases) {
            ValueSlice slice = checkValueSlice("function f(): " + binaryCase.returnType()
                + " { return " + binaryCase.expr() + " }");
            if (slice == null) {
                continue;
            }
            BinaryExpr binary = first(slice.program(), BinaryExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(slice.checks());
            ValueId result = lowerer.lowerExpression(binary);
            SemanticOp op = lowerer.ops().get(lowerer.ops().size() - 1);
            check(op.kind() == SemanticOpKind.BINARY
                    && op.payload() instanceof KindPayload.BinaryPayload binaryPayload
                    && binaryPayload.selector() == binaryCase.selector()
                    && binaryPayload.innerDescriptor() == null
                    && binaryPayload.side() == null,
                binaryCase.expr() + " produces BINARY " + binaryCase.selector());
            check(op.failurePolicy() == binaryCase.policy(),
                binaryCase.selector() + " is stamped " + binaryCase.policy()
                    + " from the closed binaryPolicy table");
            check(op.operands().size() == 2 && op.operandTypes().size() == 2
                    && op.operands().get(0) instanceof ValueId
                    && op.operands().get(1) instanceof ValueId,
                "operands appear in source order (left then right)");
            boolean isInt = binaryCase.selector().name().startsWith("INT32");
            check(op.operandTypes().get(0) == (isInt ? RuntimeDescriptor.Int.INSTANCE
                        : RuntimeDescriptor.Number.INSTANCE)
                    && op.operandTypes().get(1) == (isInt ? RuntimeDescriptor.Int.INSTANCE
                        : RuntimeDescriptor.Number.INSTANCE)
                    && op.resultType() == (isInt ? RuntimeDescriptor.Int.INSTANCE
                        : RuntimeDescriptor.Number.INSTANCE),
                "operand/result types carry the pinned one-line scalar rows (identity)");
            check(op.result() == result, "BINARY publishes a fresh ValueId result");
            String recomputed = ContractSnapshotCanonicalizer.digest(op.contract());
            check(recomputed.equals(op.contract().canonicalDigest()),
                "the contract digest recomputes equal (T3-valid op)");
            check(op.contract().selector() == binaryCase.selector(),
                "the snapshot carries the exact selector");
            covered++;
        }
        check(covered == cases.size(), "all twelve int32/number arithmetic rows produced");
    }

    static void testValueIntrinsicArms() {
        System.out.println("-- I3 INTRINSIC_CALL: INT_CONVERT/NUMBER_CONVERT, zero boundaries --");

        ValueSlice toInt = checkValueSlice("function f(): int { return int(1.5) }");
        if (toInt != null) {
            CallExpr call = first(toInt.program(), CallExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(toInt.checks());
            ValueId result = lowerer.lowerExpression(call);
            List<SemanticOp> ops = lowerer.ops();
            check(ops.size() == 2
                    && ops.get(0).kind() == SemanticOpKind.CONST
                    && ops.get(1).kind() == SemanticOpKind.INTRINSIC_CALL,
                "int(1.5) lowers to the argument CONST then one INTRINSIC_CALL");
            SemanticOp op = ops.get(1);
            check(op.payload() instanceof KindPayload.IntrinsicCallPayload intrinsic
                    && intrinsic.kind() == IntrinsicKind.INT_CONVERT
                    && intrinsic.input() == ops.get(0).result(),
                "the INTRINSIC_CALL payload carries INT_CONVERT and the input ValueId");
            check(op.failurePolicy() == FailurePolicyId.INT_CONVERSION,
                "INT_CONVERT is stamped INT_CONVERSION (the closed intrinsic rule)");
            check(op.operands().size() == 1
                    && op.operandTypes().get(0) == RuntimeDescriptor.Number.INSTANCE
                    && op.resultType() == RuntimeDescriptor.Int.INSTANCE,
                "the input is the number operand row and the result is the signed32 "
                    + "int descriptor");
            check(op.result() == result, "INTRINSIC_CALL publishes a fresh ValueId result");
            boolean hasBoundary = ops.stream()
                .anyMatch(o -> o.kind() == SemanticOpKind.BOUNDARY);
            check(!hasBoundary,
                "INTRINSIC_CALL has zero BOUNDARY children — the conversion policy is the "
                    + "terminal check");
        }

        ValueSlice toNumber = checkValueSlice("function f(): number { return number(2) }");
        if (toNumber != null) {
            CallExpr call = first(toNumber.program(), CallExpr.class);
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(toNumber.checks());
            lowerer.lowerExpression(call);
            SemanticOp op = lowerer.ops().get(lowerer.ops().size() - 1);
            check(op.payload() instanceof KindPayload.IntrinsicCallPayload intrinsic
                    && intrinsic.kind() == IntrinsicKind.NUMBER_CONVERT,
                "number(2) produces INTRINSIC_CALL NUMBER_CONVERT");
            check(op.failurePolicy() == FailurePolicyId.NUMBER_CONVERSION,
                "NUMBER_CONVERT is stamped NUMBER_CONVERSION (the closed intrinsic rule)");
            check(op.operandTypes().get(0) == RuntimeDescriptor.Int.INSTANCE
                    && op.resultType() == RuntimeDescriptor.Number.INSTANCE,
                "the input is the int operand row and the result is the number descriptor");
        }

        // A non-intrinsic call is a foreign construct in this slice.
        ValueSlice userCall = checkValueSlice("""
            function g(x: number): number { return x }
            function f(): number { return g(1.5) }
            """);
        if (userCall != null) {
            CallExpr call = null;
            List<StatementNode> statements = new ArrayList<>();
            List<ExpressionNode> expressions = new ArrayList<>();
            for (StatementNode statement : userCall.program().statements()) {
                collectStatements(statement, statements, expressions);
            }
            for (ExpressionNode expression : expressions) {
                if (expression instanceof CallExpr c
                        && c.callee() instanceof IdentifierExpr id
                        && !"int".equals(id.name()) && !"number".equals(id.name())) {
                    call = c;
                    break;
                }
            }
            SemanticLowerer.ModuleLowerer lowerer = valueLowerer(userCall.checks());
            RuntimeException defect = null;
            try {
                lowerer.lowerExpression(call);
            } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                defect = unlowered;
            }
            check(defect != null, "a user call raises ConstructUnlowered (the CALL "
                + "machinery is E7's)");
        }
    }

    // -------------------------------------------------------------------------
    // Validated units, the R-POLICY-KIND negative, profile rejection, foreign
    // constructs, determinism
    // -------------------------------------------------------------------------

    static void testValueValidatedUnitAndPolicyNegative() {
        System.out.println("-- I3 validated unit + the R-POLICY-KIND negative control --");

        ValueSlice slice = checkValueSlice("""
            function f(): int {
              return -(2 ** 30) + int(number(2)) * -(-2147483648) / 7 % 3
            }
            """);
        if (slice == null) {
            return;
        }
        ReturnStatement returnStatement = first(slice.program(), ReturnStatement.class);
        ExpressionNode root = returnStatement.expr().orElse(null);
        SemanticLowerer.ModuleLowerer lowerer = valueLowerer(slice.checks());
        ValueId produced = lowerer.lowerExpression(root);
        check(produced != null, "the mixed value-operation tree lowers");
        LoweredModuleUnit unit = lowerer.buildUnit(valueCoverage(),
            List.of(), VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH);
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(VALUE_INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, VALUE_REGISTRY_HASH));
        check(failure.isEmpty(),
            "the produced unit passes the closed validator (selector->policy stamping "
                + "accepted against the closed tables): " + failure);
        if (failure.isEmpty()) {
            check(unit.requiredCapabilities().isEmpty(),
                "the unit claims the empty capability set (the manifest's plan-time "
                    + "claims are routing facts)");
            // The lowerer appends one detached module-level MODULE_INIT
            // envelope op per unit (ISSUE-0590 E3/E8); the I3 slice's own
            // ops stay value-operation kinds. The envelope is asserted
            // separately, then excluded from the value-kind sweep.
            check(unit.ops().stream()
                    .filter(op -> op.kind() == SemanticOpKind.MODULE_INIT).count() == 1,
                "the unit carries exactly one MODULE_INIT envelope op (the "
                    + "module-level init op, appended last and never a block member)");
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_INIT) {
                    continue;
                }
                check(op.kind() == SemanticOpKind.CONST
                        || op.kind() == SemanticOpKind.UNARY
                        || op.kind() == SemanticOpKind.BINARY
                        || op.kind() == SemanticOpKind.INTRINSIC_CALL,
                    "every produced value op is a value-operation kind; got " + op.kind());
            }
            boolean sawMinLiteral = unit.ops().stream().anyMatch(op ->
                op.kind() == SemanticOpKind.CONST
                    && op.payload() instanceof KindPayload.ConstPayload constPayload
                    && constPayload.value() instanceof ScalarValue.Int intValue
                    && intValue.value() == -2147483648);
            check(sawMinLiteral,
                "the immediate-minus literal -2147483648 lowers through the corpus");
        }

        // The R-POLICY-KIND negative: a deliberately wrong selector->policy
        // pair — INT32_ADD stamped NUMBER_CONVERSION — fails the validator.
        LoweredModuleUnit wrongUnit = tamperedPolicyUnit(
            BinarySelector.INT32_ADD, FailurePolicyId.NUMBER_CONVERSION);
        Optional<CompilerDiagnostic> wrongFailure = SemanticIrValidator.validate(wrongUnit,
            new SemanticIrValidator.ComparisonFacts(VALUE_INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, VALUE_REGISTRY_HASH));
        check(wrongFailure.isPresent()
                && wrongFailure.get().message().contains(SemanticIrValidator.R_POLICY_KIND),
            "INT32_ADD stamped NUMBER_CONVERSION fails R-POLICY-KIND: " + wrongFailure);

        // The same negative for the unary rule.
        LoweredModuleUnit wrongUnary = tamperedUnaryPolicyUnit(
            UnarySelector.INT32_NEG, FailurePolicyId.NO_DEAL_FAILURE);
        Optional<CompilerDiagnostic> wrongUnaryFailure =
            SemanticIrValidator.validate(wrongUnary,
                new SemanticIrValidator.ComparisonFacts(VALUE_INTERFACE_HASH,
                    SemanticProfile.DEAL_V1_2_INT32, VALUE_REGISTRY_HASH));
        check(wrongUnaryFailure.isPresent()
                && wrongUnaryFailure.get().message()
                    .contains(SemanticIrValidator.R_POLICY_KIND),
            "INT32_NEG stamped NO_DEAL_FAILURE fails R-POLICY-KIND: "
                + wrongUnaryFailure);
    }

    /** Builds a synthetic one-op unit around a tampered BINARY policy pair. */
    private static LoweredModuleUnit tamperedPolicyUnit(BinarySelector selector,
                                                        FailurePolicyId policy) {
        ValueId left = new ValueId(1);
        ValueId right = new ValueId(2);
        ValueId result = new ValueId(3);
        OpId opId = new OpId(VALUE_MODULE, 1);
        SourceOrigin origin = new SourceOrigin(VALUE_SOURCE_ID,
            SourceSpan.synthetic(VALUE_SOURCE_ID), SourceOriginKind.SYNTHETIC,
            new AnchorId(1), null);
        KindPayload.BinaryPayload payload =
            new KindPayload.BinaryPayload(selector, null, null);
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, SemanticOpKind.BINARY,
            RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            selector, payload, policy, List.of(), "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, SemanticOpKind.BINARY,
            RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            selector, payload, policy, List.of(), digest);
        SemanticOp op = new SemanticOp(opId, SemanticOpKind.BINARY, origin, result,
            RuntimeDescriptor.Int.INSTANCE, List.of(left, right),
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            payload, policy, contract);
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, VALUE_MODULE, VALUE_INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                VALUE_REGISTRY_HASH),
            EnumSet.noneOf(SemanticCapability.class), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            List.of(op));
    }

    /** Builds a synthetic one-op unit around a tampered UNARY policy pair. */
    private static LoweredModuleUnit tamperedUnaryPolicyUnit(UnarySelector selector,
                                                             FailurePolicyId policy) {
        ValueId operand = new ValueId(1);
        ValueId result = new ValueId(2);
        OpId opId = new OpId(VALUE_MODULE, 1);
        SourceOrigin origin = new SourceOrigin(VALUE_SOURCE_ID,
            SourceSpan.synthetic(VALUE_SOURCE_ID), SourceOriginKind.SYNTHETIC,
            new AnchorId(1), null);
        KindPayload.UnaryPayload payload = new KindPayload.UnaryPayload(selector);
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, SemanticOpKind.UNARY,
            RuntimeDescriptor.Int.INSTANCE, List.of(RuntimeDescriptor.Int.INSTANCE),
            selector, payload, policy, List.of(), "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, SemanticOpKind.UNARY,
            RuntimeDescriptor.Int.INSTANCE, List.of(RuntimeDescriptor.Int.INSTANCE),
            selector, payload, policy, List.of(), digest);
        SemanticOp op = new SemanticOp(opId, SemanticOpKind.UNARY, origin, result,
            RuntimeDescriptor.Int.INSTANCE, List.of(operand),
            List.of(RuntimeDescriptor.Int.INSTANCE), payload, policy, contract);
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, VALUE_MODULE, VALUE_INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                VALUE_REGISTRY_HASH),
            EnumSet.noneOf(SemanticCapability.class), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            List.of(op));
    }

    static void testValueLegacyProfileRejected() {
        System.out.println("-- I3 profile guard: LEGACY_SAFE_INT is rejected before any op --");

        ValueSlice slice = checkValueSlice("for (let s: string of \"a\") {}");
        if (slice == null) {
            return;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(
            ConstructKind.SCALAR_LITERAL, ConstructKind.SCALAR_LITERAL.mappedOpKinds(),
            ConstructKind.IF_WHILE_FOR_FOR_OF,
            ConstructKind.IF_WHILE_FOR_FOR_OF.mappedOpKinds());

        // The control: the same module lowers fine under DEAL_V1_2_INT32.
        SemanticLowerer.LoweringResult control = SemanticLowerer.lowerModule(
            moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, coverage,
            VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(VALUE_MODULE)));
        check(control != null && !control.hasErrors() && control.unit() != null,
            "the control lowering succeeds under DEAL_V1_2_INT32");

        // The guard: a LEGACY_SAFE_INT lowering request fails E6005 with no
        // unit — the rejection runs before any op is built.
        SemanticLowerer.LoweringResult rejected = SemanticLowerer.lowerModule(
            moduleOf(slice), SemanticProfile.LEGACY_SAFE_INT, coverage,
            VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(VALUE_MODULE)));
        check(rejected != null && rejected.hasErrors() && rejected.unit() == null,
            "the LEGACY_SAFE_INT lowering request fails with no unit");
        if (rejected != null && rejected.hasErrors()) {
            check(rejected.diagnostics().size() == 1,
                "exactly one E6005 diagnostic; got " + rejected.diagnostics().size());
            CompilerDiagnostic diagnostic = rejected.diagnostics().get(0);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.diagnosticCode() == DiagnosticCode.E6005
                    && "error".equals(diagnostic.severity()),
                "the rejection is error-severity E6005");
            check(diagnostic.message()
                    .contains(SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED),
                "the diagnostic names the pinned profile-guard rule: "
                    + diagnostic.message());
            check(diagnostic.message().contains("semanticProfile LEGACY_SAFE_INT"),
                "the diagnostic carries the offending profile");
        }
    }

    static void testValueOutOfScopeConstruct() {
        System.out.println("-- I3 foreign constructs: E6005 naming the construct --");

        ValueSlice slice = checkValueSlice("""
            let x = 1
            """);
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = SemanticLowerer.lowerModule(
            moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32, valueCoverage(),
            VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(VALUE_MODULE)));
        check(result != null && result.hasErrors() && result.unit() == null,
            "a module with a variable declaration fails hard with no unit (never a reroute)");
        if (result != null && result.hasErrors()) {
            check(result.diagnostics().size() == 1,
                "exactly one E6005 diagnostic; got " + result.diagnostics().size());
            CompilerDiagnostic diagnostic = result.diagnostics().get(0);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.message()
                        .contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                "the E6005 names CONSTRUCT_UNLOWERED: " + diagnostic.message());
            check(diagnostic.message().contains("variable declaration"),
                "the E6005 names the construct (variable declaration): "
                    + diagnostic.message());
        }
    }

    static void testValueScalarDescriptorRowsSingleProducer() throws Exception {
        System.out.println("-- I3 scalar descriptor rows: the pinned one-line rows through "
            + "the single producer --");

        // The slice admits exactly the pinned one-line scalar rows and
        // realizes them through the single DescriptorService producer
        // (ISSUE-0233's producer-singularity gate: no production file
        // outside DescriptorService maps Type -> RuntimeDescriptor). The
        // slice builds no structural descriptor service and constructs no
        // descriptor directly.
        String source = Files.readString(Path.of("deal/semantic/SemanticLowerer.java"));
        check(source.contains("DescriptorService.describe(type)"),
            "the slice's pinned scalar rows realize through the single "
                + "DescriptorService producer");
        check(!source.contains("new RuntimeDescriptor."),
            "the slice constructs no RuntimeDescriptor directly (the structural "
                + "descriptor service is ISSUE-0233's and is not built here)");
    }

    static void testValueDeterminism() {
        System.out.println("-- I3 determinism: repeated lowering produces byte-identical dumps --");

        ValueSlice slice = checkValueSlice("""
            function f(): int {
              return -(2147483647 + 1) + int(number(2)) * -(-2147483648) / 7 % 3
            }
            """);
        if (slice == null) {
            return;
        }
        ReturnStatement returnStatement = first(slice.program(), ReturnStatement.class);
        ExpressionNode root = returnStatement.expr().orElse(null);

        SemanticLowerer.ModuleLowerer firstLowerer = valueLowerer(slice.checks());
        firstLowerer.lowerExpression(root);
        LoweredModuleUnit first = firstLowerer.buildUnit(valueCoverage(), List.of(),
            VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH);
        Optional<CompilerDiagnostic> firstFailure = SemanticIrValidator.validate(first,
            new SemanticIrValidator.ComparisonFacts(VALUE_INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, VALUE_REGISTRY_HASH));
        check(firstFailure.isEmpty(), "the first lowering validates: " + firstFailure);

        SemanticLowerer.ModuleLowerer secondLowerer = valueLowerer(slice.checks());
        secondLowerer.lowerExpression(root);
        LoweredModuleUnit second = secondLowerer.buildUnit(valueCoverage(), List.of(),
            VALUE_INTERFACE_HASH, VALUE_REGISTRY_HASH);
        Optional<CompilerDiagnostic> secondFailure = SemanticIrValidator.validate(second,
            new SemanticIrValidator.ComparisonFacts(VALUE_INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, VALUE_REGISTRY_HASH));
        check(secondFailure.isEmpty(), "the repeated lowering validates: "
            + secondFailure);
        if (firstFailure.isEmpty() && secondFailure.isEmpty()) {
            check(Arrays.equals(SemanticIrDumper.dumpModule(first),
                    SemanticIrDumper.dumpModule(second)),
                "two fresh lowerings produce byte-identical unit dumps (D8/D10)");
        }
    }

    // -------------------------------------------------------------------------
    // Combined verification (T1 + T3): the invocation path, the profile-aware
    // parser, and one real lowering run through the orchestrator's checked facts.
    // -------------------------------------------------------------------------

    static void testCombinedInvocationParserAndLowering() throws Exception {
        System.out.println("-- Combined T1+T3: COMMON_SHADOW + DEAL_V1_2_INT32 + "
            + "PRE_ACTIVATION parse, lower, validate --");

        Path tmp = Files.createTempDirectory("deal-foundation-i3-combined");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                export function test(): int {
                  return -(2147483647 + 1) + int(number(2)) * -(-2147483648) / 7 % 3
                }

                export function main(): null { return null; }
                """);

            // T1 invocation path + T3 profile-aware parser through the real
            // orchestrator.
            CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry());
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                false, false, false, Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean ok = orchestrator.compile();
            check(ok, "the COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION compile "
                + "succeeds (the -2147483648 immediate token parses): "
                + orchestrator.diagnostics());
            check(orchestrator.invocation().purpose() == InvocationPurpose.COMMON_SHADOW
                    && orchestrator.invocation().semanticProfile()
                        == SemanticProfile.DEAL_V1_2_INT32
                    && orchestrator.invocation().releaseState()
                        == ReleaseState.PRE_ACTIVATION,
                "the invocation carries exactly one purpose/profile/release state");
            if (!ok) {
                return;
            }
            CheckedModuleInput module = null;
            for (CheckedModuleInput candidate
                    : orchestrator.checkedProject().input().modules()) {
                if ("main".equals(candidate.moduleId().path())) {
                    module = candidate;
                }
            }
            check(module != null, "the checked project carries the entry module");

            // The manifest claims: int constructs claim SIGNED_INT32 (the
            // fixture's int literals/negation/arithmetic/int()).
            boolean manifestClaimsSigned = orchestrator.requirementManifests() != null
                && !orchestrator.requirementManifests().hasErrors()
                && orchestrator.requirementManifests().manifests().stream()
                    .filter(m -> m.moduleId().path().equals("main"))
                    .allMatch(m -> m.capabilities()
                        .contains(SemanticCapability.SIGNED_INT32));
            check(manifestClaimsSigned,
                "the combined fixture's manifest claims SIGNED_INT32 (int constructs)");

            // One real lowering run over the invocation's checked facts: the
            // value-operation roots in source order, then the validated unit.
            SemanticLowerer.ModuleLowerer lowerer =
                new SemanticLowerer.ModuleLowerer(module.moduleId(), module.sourceId(),
                    module.checks(), SemanticIdAllocator.over(
                        orchestrator.checkedProject().input().modules().stream()
                            .map(CheckedModuleInput::moduleId).toList()));
            List<ExpressionNode> roots = new ArrayList<>();
            for (StatementNode statement : module.ast().statements()) {
                collectValueRootsStatement(statement, roots);
            }
            check(!roots.isEmpty(), "the fixture yields value-operation roots");
            for (ExpressionNode root : roots) {
                lowerer.lowerExpression(root);
            }
            LoweredModuleUnit unit = lowerer.buildUnit(valueCoverage(),
                module.imports().stream()
                    .map(deal.semantic.ir.ResolvedImport::resolvedModuleId).toList(),
                orchestrator.checkedProject().index().interfaceIndexDigest(),
                invocation.capabilityRegistryHash());
            Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit,
                new SemanticIrValidator.ComparisonFacts(
                    orchestrator.checkedProject().index().interfaceIndexDigest(),
                    SemanticProfile.DEAL_V1_2_INT32,
                    invocation.capabilityRegistryHash()));
            check(validation.isEmpty(),
                "the lowered unit validates against the real index digest and the "
                    + "invocation's lowering-context facts: " + validation);
            if (validation.isPresent()) {
                return;
            }
            List<SemanticOpKind> kinds = unit.ops().stream().map(SemanticOp::kind)
                .distinct().toList();
            check(kinds.contains(SemanticOpKind.CONST)
                    && kinds.contains(SemanticOpKind.UNARY)
                    && kinds.contains(SemanticOpKind.BINARY)
                    && kinds.contains(SemanticOpKind.INTRINSIC_CALL),
                "the one lowering run produces CONST/UNARY/BINARY/INTRINSIC_CALL: "
                    + kinds);
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.UNARY
                        && op.payload() instanceof KindPayload.UnaryPayload up) {
                    check(op.failurePolicy()
                            == SemanticIrValidator.unaryPolicy(up.selector()),
                        "UNARY " + up.selector() + " is stamped "
                            + SemanticIrValidator.unaryPolicy(up.selector()));
                }
                if (op.kind() == SemanticOpKind.BINARY
                        && op.payload() instanceof KindPayload.BinaryPayload bp) {
                    check(op.failurePolicy()
                            == SemanticIrValidator.binaryPolicy(bp.selector()),
                        "BINARY " + bp.selector() + " is stamped "
                            + SemanticIrValidator.binaryPolicy(bp.selector()));
                }
                if (op.kind() == SemanticOpKind.INTRINSIC_CALL
                        && op.payload() instanceof KindPayload.IntrinsicCallPayload ip) {
                    check(op.failurePolicy()
                            == SemanticIrValidator.intrinsicPolicy(ip.kind()),
                        "INTRINSIC_CALL " + ip.kind() + " is stamped "
                            + SemanticIrValidator.intrinsicPolicy(ip.kind()));
                }
            }
            boolean sawMinLiteral = unit.ops().stream().anyMatch(op ->
                op.kind() == SemanticOpKind.CONST
                    && op.payload() instanceof KindPayload.ConstPayload constPayload
                    && constPayload.value() instanceof ScalarValue.Int intValue
                    && intValue.value() == -2147483648);
            check(sawMinLiteral,
                "the parser invariant lands in the unit: -2147483648 is the signed32 "
                    + "combined-token literal");

            // T3 negative through the same invocation path: a bare
            // out-of-range literal is E1036 at the token.
            Files.writeString(src.resolve("overflow.deal"), """
                export function bad(): int {
                  return 2147483648
                }

                export function main(): null { return null; }
                """);
            CompilationOrchestrator overflow = new CompilationOrchestrator(
                src.resolve("overflow.deal").toAbsolutePath(),
                tmp.resolve("build-overflow"), false, false, false, false,
                Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean overflowOk = overflow.compile();
            check(!overflowOk, "the v1.2 compile of '2147483648' fails through real "
                + "phase-0 discovery/parsing");
            List<CompilerDiagnostic> diags = overflow.diagnostics();
            check(diags.size() == 1 && "E1036".equals(diags.get(0).code())
                    && "Integer literal out of range: 2147483648"
                        .equals(diags.get(0).message()),
                "the phase-0 diagnostic is E1036 'Integer literal out of range: "
                    + "2147483648': " + diags);

            // The parenthesized form is not the immediate token: E1036 too.
            Files.writeString(src.resolve("paren.deal"), """
                export function bad(): int {
                  return -(2147483648)
                }

                export function main(): null { return null; }
                """);
            CompilationOrchestrator paren = new CompilationOrchestrator(
                src.resolve("paren.deal").toAbsolutePath(),
                tmp.resolve("build-paren"), false, false, false, false,
                Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean parenOk = paren.compile();
            check(!parenOk && paren.diagnostics().stream()
                    .anyMatch(d -> "E1036".equals(d.code())
                        && d.message()
                            .contains("Integer literal out of range: 2147483648")),
                "-(2147483648) is E1036 (the parenthesized literal reaches the "
                    + "general literal arm, never the immediate token): "
                    + paren.diagnostics());
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** Collects the value-operation roots of one statement (non-value-op
     * children recurse; a value-op construct is a root and is not descended). */
    private static void collectValueRootsStatement(StatementNode statement,
                                                   List<ExpressionNode> out) {
        switch (statement) {
            case ExportDeclaration ed -> collectValueRootsStatement(ed.declaration(), out);
            case Block block -> block.statements()
                .forEach(st -> collectValueRootsStatement(st, out));
            case FunctionDeclaration fd -> collectValueRootsStatement(fd.body(), out);
            case VariableDeclaration vd -> collectValueRootsExpression(vd.initializer(), out);
            case ReturnStatement rs ->
                rs.expr().ifPresent(e -> collectValueRootsExpression(e, out));
            case IfStatement is -> {
                collectValueRootsExpression(is.condition(), out);
                collectValueRootsStatement(is.thenBlock(), out);
                is.elseBranch().ifPresent(branch -> {
                    if (branch instanceof Either.Left<IfStatement, Block> left) {
                        collectValueRootsStatement(left.value(), out);
                    } else if (branch instanceof Either.Right<IfStatement, Block> right) {
                        collectValueRootsStatement(right.value(), out);
                    }
                });
            }
            case WhileStatement ws -> {
                collectValueRootsExpression(ws.condition(), out);
                collectValueRootsStatement(ws.body(), out);
            }
            case ForStatement fs -> {
                if (fs.init().isPresent()) {
                    ForInit init = fs.init().get();
                    if (init instanceof ForInit.VarDecl varDecl) {
                        collectValueRootsStatement(varDecl.decl(), out);
                    } else if (init instanceof ForInit.AssignExpr assignExpr) {
                        collectValueRootsExpression(assignExpr.expr(), out);
                    }
                }
                if (fs.condition().isPresent()) {
                    collectValueRootsExpression(fs.condition().get(), out);
                }
                if (fs.update().isPresent()) {
                    collectValueRootsExpression(fs.update().get(), out);
                }
                collectValueRootsStatement(fs.body(), out);
            }
            case ForOfStatement fos -> {
                collectValueRootsExpression(fos.iterable(), out);
                collectValueRootsStatement(fos.body(), out);
            }
            case ExpressionStatement es -> collectValueRootsExpression(es.expr(), out);
            case TryStatement ts -> {
                collectValueRootsStatement(ts.tryBlock(), out);
                collectValueRootsStatement(ts.catchBlock(), out);
            }
            case ThrowStatement throwStatement ->
                collectValueRootsExpression(throwStatement.expr(), out);
            default -> { /* declarations without expression positions */ }
        }
    }

    /** True iff the expression is a value-operation construct of the I3 slice. */
    private static boolean isValueConstruct(ExpressionNode expr) {
        if (expr instanceof LiteralExpr || expr instanceof UnaryExpr) {
            return true;
        }
        if (expr instanceof BinaryExpr binary) {
            return switch (binary.op()) {
                case ADD, SUB, MUL, DIV, MOD, POW -> true;
                case EQ, NEQ, LT, LTE, GT, GTE, AND, OR -> false;
            };
        }
        return expr instanceof CallExpr call
            && call.callee() instanceof IdentifierExpr identifier
            && ("int".equals(identifier.name()) || "number".equals(identifier.name()));
    }

    /** Walks one expression: a value-op construct is a root; otherwise recurse. */
    private static void collectValueRootsExpression(ExpressionNode expr,
                                                    List<ExpressionNode> out) {
        if (expr == null) {
            return;
        }
        if (isValueConstruct(expr)) {
            out.add(expr);
            return;
        }
        switch (expr) {
            case BinaryExpr b -> {
                collectValueRootsExpression(b.left(), out);
                collectValueRootsExpression(b.right(), out);
            }
            case UnaryExpr u -> collectValueRootsExpression(u.expr(), out);
            case CallExpr c -> {
                collectValueRootsExpression(c.callee(), out);
                c.args().forEach(a -> collectValueRootsExpression(a, out));
            }
            case MemberAccessExpr m -> collectValueRootsExpression(m.object(), out);
            case IndexExpr ix -> {
                collectValueRootsExpression(ix.array(), out);
                collectValueRootsExpression(ix.index(), out);
            }
            case ArrayLiteralExpr al -> al.elements()
                .forEach(e -> collectValueRootsExpression(e, out));
            case ObjectLiteralExpr ol -> ol.properties()
                .forEach(p -> collectValueRootsExpression(p.value(), out));
            case TemplateLiteralExpr tl -> tl.parts()
                .forEach(p -> collectValueRootsExpression(p, out));
            case AwaitExpression aw -> collectValueRootsExpression(aw.callee(), out);
            default -> { /* identifier leaves and other foreign constructs */ }
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Lowering Foundation Test (ISSUE-0281 + ISSUE-0390 + "
            + "ISSUE-0395) ===\n");

        testE6005Registration();

        testClosedEnum(SemanticProfile.class,
            List.of("LEGACY_SAFE_INT", "DEAL_V1_2_INT32"), "SemanticProfile");
        testClosedEnum(InvocationPurpose.class,
            List.of("PUBLIC_BUILD", "COMMON_SHADOW", "LEGACY_REGRESSION"),
            "InvocationPurpose");
        testClosedEnum(ReleaseState.class,
            List.of("PRE_ACTIVATION", "V1_2_ACTIVE"), "ReleaseState");
        testClosedEnum(SemanticCapability.class,
            List.of("FOUNDATION_VALUES", "SIGNED_INT32", "CONTAINERS_AND_STRINGS",
                "DESCRIPTORS", "BOUNDARIES", "EVALUATION_ORDER", "BINDINGS",
                "CALLS", "STDLIB_SEMANTICS", "STDLIB_TIME_CONFLICT", "CLASSES",
                "MODULES"),
            "SemanticCapability");

        testLoweringFailureDetail();

        testSharedValueSemanticsSurface();
        testSharedValueSemanticsInt32Arithmetic();
        testSharedValueSemanticsInt32DivMod();
        testSharedValueSemanticsInt32Pow();
        testSharedValueSemanticsConversion();
        testSharedValueSemanticsNumberOps();
        testSharedValueSemanticsNumberPow();
        testSharedValueSemanticsComparisons();
        testSharedValueSemanticsOrigins();
        testSelectorPolicyCrossCheck();

        testValueConstAndUnaryArms();
        testValueBinaryArms();
        testValueIntrinsicArms();
        testValueValidatedUnitAndPolicyNegative();
        testValueLegacyProfileRejected();
        testValueOutOfScopeConstruct();
        try {
            testValueScalarDescriptorRowsSingleProducer();
        } catch (Exception descriptorScanFailure) {
            fail("the descriptor-row single-producer scan threw: " + descriptorScanFailure);
        }
        testValueDeterminism();
        try {
            testCombinedInvocationParserAndLowering();
        } catch (Exception combinedFailure) {
            fail("the combined T1+T3 invocation/lowering run threw: " + combinedFailure);
        }

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
