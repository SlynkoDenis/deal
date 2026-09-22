package deal.test;

import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweringContext;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.NullableSide;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticId;
import deal.semantic.ir.SemanticIrTextDecodeException;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SnapshotJsonRecord;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Base64;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * Verifies the ISSUE-0283 canonical JSON facility: the single
 * {@link CanonicalJson} serializer + parser, the
 * {@link ContractSnapshotCanonicalizer} digest, and the
 * {@link LoweringContextHash} helper (schema S1/S2; foundation F8).
 *
 * <p>Tests:
 * <ol>
 *   <li>Every canonicalization rule: sorted object keys, decimal signed32
 *       integers, unique IEEE-754 hex floats (negative zero, NaN,
 *       ±Infinity), explicit nulls, ordered arrays, minimal string
 *       escaping, UTF-8 — with a stored golden document recomputed in a
 *       fresh JVM invocation (cross-process determinism).</li>
 *   <li>Parser round-trips: every serializer golden, all 55 payload
 *       shapes, the 42-selector digest matrix, and the
 *       {@link RuntimeDescriptor} canonical spellings parse and
 *       re-serialize byte-exactly; a replaced reserved/open enum name
 *       survives the parse as a raw string (no enum conversion).</li>
 *   <li>Decode failures: malformed JSON, invalid UTF-8, non-canonical
 *       numbers, duplicate keys, unpaired surrogates, trailing content,
 *       unknown/missing fields, wrong value types, and a wrong version
 *       raise {@link SemanticIrTextDecodeException} — never E6005.</li>
 *   <li>Digest: the pinned snapshot digest equals a stored SHA-256
 *       golden; a mutation matrix flips each behavior field and changes
 *       the digest; opId/origin-only changes leave it unchanged.</li>
 *   <li>{@code loweringContextHash} golden and the legacy/v1.2 profile
 *       confusion guard (T1's closed {@link SemanticProfile} enum).</li>
 *   <li>Combined T1/T2 integration: the 42-selector matrix, descriptor
 *       spellings, and every {@link SemanticOpKind} payload shape produce
 *       valid digests; a T1/T2 fault is detectable through the pinned
 *       constants.</li>
 *   <li>Structural single-implementation scans: exactly one serializer,
 *       one parser, one digest facility, and one snapshot canonicalizer
 *       exist in production.</li>
 * </ol>
 */
public class CanonicalJsonTest {

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

    private static void expectDecode(Runnable action, String message) {
        try {
            action.run();
            fail(message + " (no exception thrown)");
        } catch (SemanticIrTextDecodeException expected) {
            check(true, message + " (SemanticIrTextDecodeException: " + expected.getMessage() + ")");
        } catch (RuntimeException unexpected) {
            fail(message + " (wrong exception type " + unexpected.getClass().getSimpleName()
                + ": " + unexpected.getMessage() + ")");
        }
    }

    private static final String REGISTRY_HASH =
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    private static final String PLACEHOLDER_DIGEST =
        "0000000000000000000000000000000000000000000000000000000000000000";

    // =========================================================================
    // Stored goldens (pinned; generated once from this exact serializer)
    // =========================================================================

    /** Stored golden: the exact canonical text of {@link #compositeDocument()}. */
    private static final String PINNED_COMPOSITE_DOCUMENT_GOLDEN =
        "{\"a\":\"x\",\"floats\":[0x1.921fb54442d18p1,-0x0.0p0,NaN,Infinity,-Infinity,0x1.0p0,0x0.0000000000001p-1022],\"intMax\":2147483647,\"nested\":{\"array\":[3,1,2],\"null\":null,\"text\":\"\u03c0\u00e9\ud83d\ude00 \\\"quote\\\" \\\\backslash \\n\\t\\u0000\\u001f\"},\"null\":null,\"z\":-2147483648,\"zero\":0}";

    /** Stored golden: SHA-256 of the canonical JSON of {@link #pinnedSnapshot()}. */
    private static final String PINNED_SNAPSHOT_DIGEST_GOLDEN =
        "810fcc608b7e27fa3dd23ec391e0d38aee56bf5e4ad0f7ef2f32fb91538545fb";

    /** Stored golden: {@code LoweringContextHash.of(DEAL_V1_2_INT32, REGISTRY_HASH)}. */
    private static final String PINNED_LOWERING_CONTEXT_GOLDEN =
        "808a9dc895a8a443f4cd972b16313c888169f5ea54051866c6a9a527adfb0b80";

    // =========================================================================
    // Fixtures
    // =========================================================================

    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId LIB = new ModuleId("lib.math");
    private static final ClassId CLS = new ClassId("m", "C");
    private static final RuntimeDescriptor.Func SIG =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);

    /** The composite document exercising every canonicalization rule. */
    static CanonicalJson.Value compositeDocument() {
        CanonicalJson.Obj nested = CanonicalJson.obj(
            CanonicalJson.e("null", CanonicalJson.nullValue()),
            CanonicalJson.e("array", CanonicalJson.arr(
                CanonicalJson.intValue(3), CanonicalJson.intValue(1), CanonicalJson.intValue(2))),
            CanonicalJson.e("text", CanonicalJson.str(
                "\u03c0\u00e9\ud83d\ude00 \"quote\" \\backslash \n\t\u0000\u001f")));
        return CanonicalJson.obj(
            CanonicalJson.e("z", CanonicalJson.intValue(-2147483648)),
            CanonicalJson.e("a", CanonicalJson.str("x")),
            CanonicalJson.e("floats", CanonicalJson.arr(
                CanonicalJson.number(Math.PI),
                CanonicalJson.number(-0.0),
                CanonicalJson.number(Double.NaN),
                CanonicalJson.number(Double.POSITIVE_INFINITY),
                CanonicalJson.number(Double.NEGATIVE_INFINITY),
                CanonicalJson.number(1.0),
                CanonicalJson.number(Double.MIN_VALUE))),
            CanonicalJson.e("nested", nested),
            CanonicalJson.e("null", CanonicalJson.nullValue()),
            CanonicalJson.e("intMax", CanonicalJson.intValue(Integer.MAX_VALUE)),
            CanonicalJson.e("zero", CanonicalJson.intValue(0)));
    }

    static byte[] compositeDocumentBytes() {
        return CanonicalJson.serializeBytes(compositeDocument());
    }

    /** The pinned snapshot whose digest is a stored golden. */
    static OperationContractSnapshot pinnedSnapshot() {
        RuntimeDescriptor.Func intInt = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);
        KindPayload.CallPayload call = new KindPayload.CallPayload(
            CallMode.EXTERNAL,
            new KindPayload.CallCallee.Static(new FunctionExecutionBinding.ExternalFunction(
                LIB, "add", intInt, ExternalExecutionOwner.SHARED_BODY)),
            intInt,
            List.of(new OpId(APP, 10), new OpId(APP, 11)),
            null,
            null,
            null,
            new OpId(LIB, 3));
        return new OperationContractSnapshot(1, SemanticOpKind.CALL,
            new RuntimeDescriptor.Array(RuntimeDescriptor.Int.INSTANCE),
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            null, call, FailurePolicyId.NO_DEAL_FAILURE,
            List.of(APP, LIB, new FunctionId(0), new BlockId(0), new OpId(LIB, 3)),
            PLACEHOLDER_DIGEST);
    }

    /** A snapshot exercising the remaining nested sealed shapes. */
    static OperationContractSnapshot richSnapshot() {
        AsyncTokenId canonical = new AsyncTokenId.Canonical(5, AsyncTokenOwner.DEAL_BODY_TASK);
        AsyncTokenId alias = new AsyncTokenId.Alias(6, canonical, AsyncLinkKind.ADAPTER_INNER);
        KindPayload.AsyncStartPayload asyncStart = new KindPayload.AsyncStartPayload(
            new KindPayload.CallCallee.Static(new FunctionExecutionBinding.AdapterBinding(
                new OpId(APP, 2), CaptureMode.REEVALUATE_THUNK,
                new AdaptSourceRef.Thunk(new BlockId(3),
                    List.of(new BindingGeneration(new BindingId(1), 2))),
                SIG, SIG)),
            AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
            List.of(new OpId(APP, 3)),
            RuntimeDescriptor.Null.INSTANCE, new OpId(APP, 4), null,
            new ExternalAsyncLink(LIB, "asyncExport", canonical));
        ClassLayout layout = new ClassLayout(CLS, List.of(
            new ClassLayout.FieldLayout("f", RuntimeDescriptor.Int.INSTANCE, false, DefaultOwner.LOCAL)));
        KindPayload.ClassNewPayload classNew = new KindPayload.ClassNewPayload(
            CLS, layout,
            List.of(new KindPayload.ProvidedField("g", new ValueId(7))),
            DefaultOwner.SHARED_FACTORY,
            List.of(new OpId(APP, 5)),
            new ClassFactoryId(9),
            List.of(new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_DEFAULT_FIELD, new OpId(APP, 6))));
        return new OperationContractSnapshot(1, SemanticOpKind.CLASS_NEW,
            new RuntimeDescriptor.Class(CLS),
            List.of(),
            null, classNew, FailurePolicyId.CLASS_CONSTRUCTION,
            List.of(new FunctionAllocationIdentity(1), alias, new AnchorId(2)),
            PLACEHOLDER_DIGEST);
    }

    static SourceOrigin origin(long anchor, String sourceId) {
        return new SourceOrigin(sourceId, SourceSpan.synthetic(sourceId),
            SourceOriginKind.SYNTHETIC, new AnchorId(anchor), null);
    }

    static OperationContractSnapshot snapshotFor(KindPayload payload, SemanticOpKind kind,
                                                 OpResultType resultType,
                                                 List<RuntimeDescriptor> operandTypes,
                                                 FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector()
            : null;
        return new OperationContractSnapshot(1, kind, resultType, operandTypes, selector,
            payload, policy, List.of(), digest);
    }

    // =========================================================================
    // 1. Canonicalization rules and cross-process determinism
    // =========================================================================

    static void testCanonicalRules() {
        System.out.println("-- Canonical JSON rules --");

        // Sorted object keys (construction order is deliberately unsorted).
        String sorted = CanonicalJson.serializeText(CanonicalJson.obj(
            CanonicalJson.e("z", CanonicalJson.intValue(1)),
            CanonicalJson.e("a", CanonicalJson.str("x")),
            CanonicalJson.e("m", CanonicalJson.arr(
                CanonicalJson.intValue(1), CanonicalJson.number(Math.PI),
                CanonicalJson.nullValue(), CanonicalJson.bool(true)))));
        check("{\"a\":\"x\",\"m\":[1,0x1.921fb54442d18p1,null,true],\"z\":1}".equals(sorted),
            "object keys are sorted lexicographically; got " + sorted);

        // Decimal signed32 integers.
        check("{\"v\":-2147483648}".equals(CanonicalJson.serializeText(
                CanonicalJson.obj(CanonicalJson.e("v", CanonicalJson.intValue(Integer.MIN_VALUE))))),
            "Integer.MIN_VALUE renders as the decimal integer -2147483648");
        check("{\"v\":2147483647}".equals(CanonicalJson.serializeText(
                CanonicalJson.obj(CanonicalJson.e("v", CanonicalJson.intValue(Integer.MAX_VALUE))))),
            "Integer.MAX_VALUE renders as the decimal integer 2147483647");
        check("{\"v\":0}".equals(CanonicalJson.serializeText(
                CanonicalJson.obj(CanonicalJson.e("v", CanonicalJson.intValue(0))))),
            "zero renders as the decimal integer 0");

        // Unique IEEE-754 hex floats.
        check("0x1.921fb54442d18p1".equals(Double.toHexString(Math.PI)),
            "pi hex form pinned: 0x1.921fb54442d18p1");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(-0.0)))).contains("\"v\":-0x0.0p0"),
            "negative zero is preserved (-0x0.0p0)");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(Double.NaN)))).contains("\"v\":NaN"),
            "NaN renders as NaN");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(Double.POSITIVE_INFINITY))))
                .contains("\"v\":Infinity"),
            "positive infinity renders as Infinity");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(Double.NEGATIVE_INFINITY))))
                .contains("\"v\":-Infinity"),
            "negative infinity renders as -Infinity");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(1.0)))).contains("\"v\":0x1.0p0"),
            "1.0 renders as 0x1.0p0");
        check(CanonicalJson.serializeText(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.number(Double.MIN_VALUE))))
                .contains("\"v\":0x0.0000000000001p-1022"),
            "the smallest subnormal renders as 0x0.0000000000001p-1022");

        // Explicit nulls.
        check("{\"a\":null}".equals(CanonicalJson.serializeText(
                CanonicalJson.obj(CanonicalJson.e("a", CanonicalJson.nullValue())))),
            "explicit nulls are emitted, never omitted");

        // Ordered arrays.
        check("[3,1,2]".equals(CanonicalJson.serializeText(
                CanonicalJson.arr(CanonicalJson.intValue(3), CanonicalJson.intValue(1),
                    CanonicalJson.intValue(2)))),
            "array element order is preserved");

        // Minimal string escaping + raw UTF-8 scalars.
        String escaped = CanonicalJson.serializeText(CanonicalJson.str(
            "a\"b\\c\nd\te\u0000f\u001f"));
        check("\"a\\\"b\\\\c\\nd\\te\\u0000f\\u001f\"".equals(escaped),
            "minimal string escaping; got " + escaped);
        String unicode = CanonicalJson.serializeText(CanonicalJson.str("\u03c0\u00e9\ud83d\ude00"));
        check("\"\u03c0\u00e9\ud83d\ude00\"".equals(unicode),
            "Unicode scalars are emitted raw (UTF-8); got " + unicode);

        // UTF-8 bytes.
        byte[] bytes = CanonicalJson.serializeBytes(CanonicalJson.str("\u03c0"));
        check(bytes.length == 4 && (bytes[0] & 0xff) == 0x22 && (bytes[3] & 0xff) == 0x22,
            "the output is UTF-8 (pi = 2 bytes inside the quotes)");

        // Unpaired surrogates are a producer defect at construction.
        try {
            CanonicalJson.str("\ud800");
            fail("an unpaired surrogate string cannot be constructed");
        } catch (IllegalArgumentException expected) {
            check(true, "unpaired surrogates are rejected at construction");
        }

        // The stored golden document (byte-exact).
        String doc = CanonicalJson.serializeText(compositeDocument());
        check(PINNED_COMPOSITE_DOCUMENT_GOLDEN.equals(doc),
            "the composite document matches the stored golden; got " + doc);
    }

    static void testCrossProcessDeterminism() {
        System.out.println("-- Cross-process determinism (fresh JVM recompute) --");

        byte[] expectedDoc = compositeDocumentBytes();
        byte[] expectedSnap = ContractSnapshotCanonicalizer.serialize(pinnedSnapshot());
        try {
            Process process = new ProcessBuilder(
                "java", "-cp", "build", "deal.test.CanonicalJsonTest", "--emit")
                .redirectErrorStream(true)
                .start();
            process.getOutputStream().close();
            BufferedReader reader = new BufferedReader(
                new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8));
            List<String> lines = new ArrayList<>();
            String line;
            while ((line = reader.readLine()) != null) {
                lines.add(line);
            }
            boolean finished = process.waitFor(60, TimeUnit.SECONDS);
            check(finished && process.exitValue() == 0,
                "the fresh JVM emit subprocess exits 0");
            String docLine = lines.stream().filter(l -> l.startsWith("CROSS:")).findFirst().orElse("");
            String snapLine = lines.stream().filter(l -> l.startsWith("SNAP:")).findFirst().orElse("");
            byte[] subDoc = Base64.getDecoder().decode(docLine.substring("CROSS:".length()));
            byte[] subSnap = Base64.getDecoder().decode(snapLine.substring("SNAP:".length()));
            check(java.util.Arrays.equals(expectedDoc, subDoc),
                "the composite document bytes are byte-equal across processes");
            check(java.util.Arrays.equals(expectedSnap, subSnap),
                "the pinned snapshot serialization is byte-equal across processes");
        } catch (Exception e) {
            fail("cross-process determinism check failed: " + e);
        }
    }

    // =========================================================================
    // 2. Parser round-trips
    // =========================================================================

    static void testRoundTripBytes(byte[] bytes, String message) {
        CanonicalJson.Value parsed = CanonicalJson.parse(bytes);
        byte[] reserialized = CanonicalJson.serializeBytes(parsed);
        check(java.util.Arrays.equals(bytes, reserialized), message);
    }

    static void testRoundTripSnapshot(OperationContractSnapshot snapshot, String message) {
        byte[] bytes = ContractSnapshotCanonicalizer.serialize(snapshot);
        SnapshotJsonRecord record = ContractSnapshotCanonicalizer.parseSnapshot(bytes);
        byte[] reserialized = ContractSnapshotCanonicalizer.serialize(record);
        check(java.util.Arrays.equals(bytes, reserialized), message);
    }

    static void testParserRoundTrips() {
        System.out.println("-- Parser: exact inverse round-trips --");

        // Generic golden round-trips (every canonicalization rule).
        testRoundTripBytes(compositeDocumentBytes(), "the composite document round-trips byte-exactly");
        testRoundTripBytes(CanonicalJson.serializeBytes(CanonicalJson.arr(
                CanonicalJson.number(-0.0), CanonicalJson.number(Double.NaN),
                CanonicalJson.number(Double.POSITIVE_INFINITY),
                CanonicalJson.number(Double.NEGATIVE_INFINITY))),
            "the special hex floats round-trip byte-exactly");
        testRoundTripBytes(CanonicalJson.serializeBytes(CanonicalJson.obj(
                CanonicalJson.e("v", CanonicalJson.intValue(Integer.MIN_VALUE)),
                CanonicalJson.e("w", CanonicalJson.intValue(Integer.MAX_VALUE)))),
            "the decimal int extrema round-trip byte-exactly");
        testRoundTripBytes(CanonicalJson.serializeBytes(CanonicalJson.obj(
                CanonicalJson.e("null", CanonicalJson.nullValue()))),
            "explicit nulls round-trip byte-exactly");
        testRoundTripBytes(CanonicalJson.serializeBytes(CanonicalJson.str(
                "a\"b\\c\nd\te\u0000f\u001f\u03c0\ud83d\ude00")),
            "escaped/unicode strings round-trip byte-exactly");

        // The pinned snapshot and the rich nested snapshot.
        testRoundTripSnapshot(pinnedSnapshot(), "the pinned snapshot round-trips byte-exactly");
        testRoundTripSnapshot(richSnapshot(), "the rich nested snapshot round-trips byte-exactly");

        // Every closed payload shape (55 kinds).
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            KindPayload payload = minimalPayload(kind);
            OperationContractSnapshot snapshot = snapshotFor(payload, kind,
                RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                PLACEHOLDER_DIGEST);
            testRoundTripSnapshot(snapshot, kind + " payload round-trips byte-exactly");
        }

        // The 42-selector digest matrix round-trips.
        for (BinarySelector selector : BinarySelector.values()) {
            OperationContractSnapshot snapshot = binaryMatrixSnapshot(selector);
            testRoundTripSnapshot(snapshot,
                "the " + selector + " selector snapshot round-trips byte-exactly");
        }

        // RuntimeDescriptor canonical spellings round-trip through snapshots.
        List<RuntimeDescriptor> spellings = List.of(
            RuntimeDescriptor.Null.INSTANCE, RuntimeDescriptor.Boolean.INSTANCE,
            RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Number.INSTANCE,
            RuntimeDescriptor.String.INSTANCE, RuntimeDescriptor.Table.INSTANCE,
            new RuntimeDescriptor.Class(new ClassId("src/app", "User")),
            new RuntimeDescriptor.Array(RuntimeDescriptor.Int.INSTANCE),
            new RuntimeDescriptor.Nullable(RuntimeDescriptor.String.INSTANCE),
            new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE,
                RuntimeDescriptor.String.INSTANCE), RuntimeDescriptor.Boolean.INSTANCE, false),
            new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE),
                RuntimeDescriptor.String.INSTANCE, true));
        for (RuntimeDescriptor descriptor : spellings) {
            OperationContractSnapshot snapshot = new OperationContractSnapshot(1,
                SemanticOpKind.CONST, descriptor, List.of(descriptor), null,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                FailurePolicyId.NO_DEAL_FAILURE, List.of(), PLACEHOLDER_DIGEST);
            testRoundTripSnapshot(snapshot,
                "the \"" + descriptor.canonicalSpecText() + "\" descriptor spelling round-trips");
        }

        // The parsed record maps the pinned field names and raw values
        // (both parser overloads).
        SnapshotJsonRecord record = ContractSnapshotCanonicalizer.parseSnapshot(
            ContractSnapshotCanonicalizer.serialize(pinnedSnapshot()));
        check(record.equals(ContractSnapshotCanonicalizer.parseSnapshot(
                ContractSnapshotCanonicalizer.serializeText(pinnedSnapshot()))),
            "the byte[] and String parse overloads are the exact same inverse");
        check(record.version() == 1, "parsed version is 1");
        check("CALL".equals(record.opKind()), "parsed opKind is the raw name CALL");
        check("[int]".equals(record.resultType()), "parsed resultType is the raw descriptor text [int]");
        check(record.operandTypes().equals(List.of("int", "int")),
            "parsed operandTypes are the raw descriptor texts");
        check(record.selector() == null, "parsed selector is null (explicit null)");
        check("NO_DEAL_FAILURE".equals(record.failurePolicy()),
            "parsed failurePolicy is the raw name");
        check(record.referencedSemanticIds().size() == 5,
            "parsed referencedSemanticIds has 5 raw objects");
        check(record.payload() instanceof CanonicalJson.Obj,
            "parsed payload is a generic JSON object");
    }

    static OperationContractSnapshot binaryMatrixSnapshot(BinarySelector selector) {
        return new OperationContractSnapshot(1, SemanticOpKind.BINARY,
            RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            selector, new KindPayload.BinaryPayload(selector, null, null),
            FailurePolicyId.NO_DEAL_FAILURE, List.of(new FunctionId(0)), PLACEHOLDER_DIGEST);
    }

    // =========================================================================
    // 3. Raw strings survive the parse; decode failures are transport-level
    // =========================================================================

    static void testRawStringsSurvive() {
        System.out.println("-- Reserved/open names survive the parse as raw strings --");

        OperationContractSnapshot unary = new OperationContractSnapshot(1, SemanticOpKind.UNARY,
            RuntimeDescriptor.Boolean.INSTANCE, List.of(RuntimeDescriptor.Boolean.INSTANCE),
            UnarySelector.NUMBER_NEG, new KindPayload.UnaryPayload(UnarySelector.NUMBER_NEG),
            FailurePolicyId.NO_DEAL_FAILURE, List.of(), PLACEHOLDER_DIGEST);
        String text = ContractSnapshotCanonicalizer.serializeText(unary);

        String closedSelectorName = text.replace("\"selector\":\"NUMBER_NEG\"",
            "\"selector\":\"TIME_NOW_MILLIS\"");
        SnapshotJsonRecord record = ContractSnapshotCanonicalizer.parseSnapshot(closedSelectorName);
        check("TIME_NOW_MILLIS".equals(record.selector()),
            "the closed selector name TIME_NOW_MILLIS survives the parse byte-intact as a "
                + "raw string");

        String reservedPolicy = text.replace("\"failurePolicy\":\"NO_DEAL_FAILURE\"",
            "\"failurePolicy\":\"EXTERNAL_PARAMETER\"");
        record = ContractSnapshotCanonicalizer.parseSnapshot(reservedPolicy);
        check("EXTERNAL_PARAMETER".equals(record.failurePolicy()),
            "the reserved policy name EXTERNAL_PARAMETER survives the parse byte-intact");

        String openKind = text.replace("\"opKind\":\"UNARY\"", "\"opKind\":\"PRIVATE_STEP\"");
        record = ContractSnapshotCanonicalizer.parseSnapshot(openKind);
        check("PRIVATE_STEP".equals(record.opKind()),
            "an open operation-kind name survives the parse byte-intact");

        // A payload-nested leaf enum value (BinaryPayload.side) also survives.
        OperationContractSnapshot binary = binaryMatrixSnapshot(BinarySelector.NULLABLE_EQ);
        String binaryText = ContractSnapshotCanonicalizer.serializeText(binary);
        String openSide = binaryText.replace("\"side\":null", "\"side\":\"NOT_A_SIDE\"");
        record = ContractSnapshotCanonicalizer.parseSnapshot(openSide);
        check(record.payload() instanceof CanonicalJson.Obj payloadObj
                && payloadObj.entries().stream().anyMatch(
                    entry -> entry.key().equals("side")
                        && entry.value() instanceof CanonicalJson.Str s
                        && "NOT_A_SIDE".equals(s.value())),
            "a payload-nested open enum name survives the parse as a raw string");

        // The reserved names are not enum members (no parse-time conversion exists);
        // TIME_NOW_MILLIS is a closed member since K7, so the raw-string example
        // uses the policy family's still-reserved names.
        check(enumMember(StdlibFunctionId.class, "TIME_NOW_MILLIS"),
            "TIME_NOW_MILLIS is a StdlibFunctionId member (the 21st closed selector; "
                + "the parser keeps raw strings regardless)");
        check(!enumMember(FailurePolicyId.class, "EXTERNAL_PARAMETER"),
            "EXTERNAL_PARAMETER is not a FailurePolicyId member (parse keeps raw strings)");
    }

    static boolean enumMember(Class<? extends Enum<?>> type, String name) {
        for (Enum<?> c : type.getEnumConstants()) {
            if (c.name().equals(name)) {
                return true;
            }
        }
        return false;
    }

    static void testDecodeFailures() {
        System.out.println("-- Decode failures are transport-level, never E6005 --");

        byte[] valid = ContractSnapshotCanonicalizer.serialize(pinnedSnapshot());

        // Malformed JSON syntax.
        expectDecode(() -> CanonicalJson.parse("{"), "truncated object");
        expectDecode(() -> CanonicalJson.parse("{\"a\":}"), "missing object value");
        expectDecode(() -> CanonicalJson.parse("[1,]"), "trailing array comma");
        expectDecode(() -> CanonicalJson.parse("\"unterminated"), "unterminated string");
        expectDecode(() -> CanonicalJson.parse("nul"), "malformed null literal");
        expectDecode(() -> CanonicalJson.parse("tru"), "malformed true literal");
        expectDecode(() -> CanonicalJson.parse("{} {}"), "trailing content after the top value");
        expectDecode(() -> CanonicalJson.parse(""), "empty input");
        expectDecode(() -> CanonicalJson.parse("{\"a\":1 \"b\":2}"), "missing comma");
        expectDecode(() -> CanonicalJson.parse("{'a':1}"), "single-quoted key");
        expectDecode(() -> CanonicalJson.parse("{\"a\":1.5}"), "decimal fraction (non-canonical)");
        expectDecode(() -> CanonicalJson.parse("{\"a\":1e3}"), "exponent (non-canonical)");
        expectDecode(() -> CanonicalJson.parse("{\"a\":0x2.0p0}"),
            "non-unique hex float 0x2.0p0 (canonical is 0x1.0p1)");
        expectDecode(() -> CanonicalJson.parse("{\"a\":0X1.0P0}"),
            "uppercase hex-float spelling (canonical is 0x1.0p0)");
        expectDecode(() -> CanonicalJson.parse("{\"a\":0x1.0P0}"),
            "uppercase hex-float exponent spelling (canonical is 0x1.0p0)");
        expectDecode(() -> CanonicalJson.parse("{\"a\":-0x0.0p0,\"a\":1}"), "duplicate object key");
        expectDecode(() -> CanonicalJson.parse("[\"\ud800\"]"), "unpaired raw high surrogate");
        expectDecode(() -> CanonicalJson.parse("[\"\\ud800\"]"), "unpaired high surrogate escape");
        expectDecode(() -> CanonicalJson.parse("[\"\\uDC00\"]"), "unpaired low surrogate escape");
        expectDecode(() -> CanonicalJson.parse(new byte[]{(byte) 0xc3, 0x28}),
            "invalid UTF-8 bytes");
        expectDecode(() -> CanonicalJson.parse("{\"a\":999999999999999999999}"),
            "decimal integer outside signed32");

        // Framing/field/value-type/version mismatches of the snapshot shape.
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"version\":1", "\"version\":2")),
            "wrong snapshot version");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"version\":1", "\"version\":\"1\"")),
            "string-typed version field");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"opKind\":\"CALL\"", "\"opKind\":7")),
            "wrong opKind value type");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8)
                    .replace("\"operandTypes\":[\"int\",\"int\"]", "\"operandTypes\":\"ints\"")),
            "string-typed operandTypes field");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8)
                    .replace("\"operandTypes\":[\"int\",\"int\"]", "\"operandTypes\":[\"int\",1]")),
            "non-string operandTypes element");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"payload\":{", "\"payload\":[")),
            "array-typed payload field");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8)
                    .replace("\"failurePolicy\":\"NO_DEAL_FAILURE\"", "\"failurePolicy\":7")),
            "wrong failurePolicy value type");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8)
                    .replace("\"selector\":null", "\"selector\":false")),
            "wrong selector value type");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"payload\":{", "\"extra\":1,\"payload\":{")),
            "unknown top-level snapshot field");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8).replace("\"selector\":null,", "")),
            "missing snapshot field");
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot("[1,2]"),
            "top-level non-object");

        // A referencedSemanticIds element that is not an object.
        expectDecode(() -> ContractSnapshotCanonicalizer.parseSnapshot(
                new String(valid, StandardCharsets.UTF_8)
                    .replace("\"referencedSemanticIds\":[",
                        "\"referencedSemanticIds\":[\"not-an-object\",")),
            "string-typed referencedSemanticIds element");

    }

    // =========================================================================
    // 4. Digest: golden, mutation matrix, opId/origin invariance
    // =========================================================================

    static void testDigest() {
        System.out.println("-- Contract snapshot digest --");

        // The digest input is exactly the eight pinned snapshot fields:
        // {version, opKind, resultType, operandTypes, selector?, payload,
        // failurePolicy, referencedSemanticIds} — nothing else. The
        // serialized object carries exactly those keys (sorted), with the
        // snapshot's carried canonicalDigest field outside the input.
        CanonicalJson.Value pinnedJson = ContractSnapshotCanonicalizer.toJson(pinnedSnapshot());
        check(pinnedJson instanceof CanonicalJson.Obj pinnedObj
                && pinnedObj.entries().stream().map(CanonicalJson.Entry::key)
                    .toList().equals(List.of("failurePolicy", "opKind", "operandTypes",
                        "payload", "referencedSemanticIds", "resultType", "selector", "version")),
            "the digest input is exactly the eight pinned fields in sorted order");
        check(ContractSnapshotCanonicalizer.SNAPSHOT_FIELDS.equals(List.of(
                "version", "opKind", "resultType", "operandTypes", "selector", "payload",
                "failurePolicy", "referencedSemanticIds")),
            "the pinned snapshot field-name list is the verbatim S2 digest field set");
        check(!ContractSnapshotCanonicalizer.serializeText(pinnedSnapshot())
                .contains("canonicalDigest"),
            "the carried canonicalDigest field is outside the digest input (never serialized)");

        String digest = ContractSnapshotCanonicalizer.digest(pinnedSnapshot());
        check(PINNED_SNAPSHOT_DIGEST_GOLDEN.equals(digest),
            "the pinned snapshot digest equals the stored SHA-256 golden; got " + digest);
        check(digest.length() == 64 && digest.equals(digest.toLowerCase())
                && digest.matches("[0-9a-f]{64}"),
            "the digest is lowercase 64-character hex");
        check(!ContractSnapshotCanonicalizer.matchesCarriedDigest(pinnedSnapshot()),
            "the placeholder carried digest does not match the recomputed digest");
        OperationContractSnapshot carrying = new OperationContractSnapshot(1,
            pinnedSnapshot().opKind(), pinnedSnapshot().resultType(),
            pinnedSnapshot().operandTypes(), pinnedSnapshot().selector(),
            pinnedSnapshot().payload(), pinnedSnapshot().failurePolicy(),
            pinnedSnapshot().referencedSemanticIds(), digest);
        check(ContractSnapshotCanonicalizer.matchesCarriedDigest(carrying),
            "a snapshot carrying the recomputed digest matches");

        // Mutation matrix: every behavior field flips the digest.
        String baseDigest = digest(binaryMatrixSnapshot(BinarySelector.INT32_ADD));
        check(!baseDigest.equals(digest(binaryMatrixSnapshot(BinarySelector.NUMBER_ADD))),
            "flipping the selector changes the digest");
        OperationContractSnapshot resultTypeFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Number.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                null, null), FailurePolicyId.NO_DEAL_FAILURE, List.of(new FunctionId(0)),
            PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(resultTypeFlip)),
            "flipping the result type changes the digest");
        OperationContractSnapshot operandFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                null, null), FailurePolicyId.NO_DEAL_FAILURE, List.of(new FunctionId(0)),
            PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(operandFlip)),
            "changing the operand types changes the digest");
        OperationContractSnapshot payloadFieldFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                null, NullableSide.LEFT), FailurePolicyId.NO_DEAL_FAILURE,
            List.of(new FunctionId(0)), PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(payloadFieldFlip)),
            "changing a payload field (side) changes the digest");
        OperationContractSnapshot payloadDescriptorFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                RuntimeDescriptor.Number.INSTANCE, null), FailurePolicyId.NO_DEAL_FAILURE,
            List.of(new FunctionId(0)), PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(payloadDescriptorFlip)),
            "changing a payload field (innerDescriptor) changes the digest");
        OperationContractSnapshot policyFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                null, null), FailurePolicyId.INT32_RESULT, List.of(new FunctionId(0)),
            PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(policyFlip)),
            "flipping the failure policy changes the digest");
        OperationContractSnapshot refFlip = new OperationContractSnapshot(1,
            SemanticOpKind.BINARY, RuntimeDescriptor.Int.INSTANCE,
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            BinarySelector.INT32_ADD, new KindPayload.BinaryPayload(BinarySelector.INT32_ADD,
                null, null), FailurePolicyId.NO_DEAL_FAILURE, List.of(new FunctionId(1)),
            PLACEHOLDER_DIGEST);
        check(!baseDigest.equals(digest(refFlip)),
            "changing a referenced semantic ID changes the digest");

        // Boundary descriptor and policy.
        KindPayload.BoundaryPayload intBoundary = new KindPayload.BoundaryPayload(
            BoundaryKind.MODULE_EXPORT, RuntimeDescriptor.Int.INSTANCE, new ValueId(0),
            new BoundaryRealization.RuntimeValidation("c"));
        String boundaryDigest = digest(snapshotFor(intBoundary, SemanticOpKind.BOUNDARY,
            RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            PLACEHOLDER_DIGEST));
        KindPayload.BoundaryPayload numberBoundary = new KindPayload.BoundaryPayload(
            BoundaryKind.MODULE_EXPORT, RuntimeDescriptor.Number.INSTANCE, new ValueId(0),
            new BoundaryRealization.RuntimeValidation("c"));
        check(!boundaryDigest.equals(digest(snapshotFor(numberBoundary,
                SemanticOpKind.BOUNDARY, RuntimeDescriptor.Int.INSTANCE, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST))),
            "changing the boundary descriptor changes the digest");
        check(!boundaryDigest.equals(digest(snapshotFor(intBoundary,
                SemanticOpKind.BOUNDARY, RuntimeDescriptor.Int.INSTANCE, List.of(),
                FailurePolicyId.TYPE_DESCRIPTOR, PLACEHOLDER_DIGEST))),
            "changing the boundary policy changes the digest");
        check(!boundaryDigest.equals(digest(snapshotFor(
                new KindPayload.BoundaryPayload(BoundaryKind.MODULE_EXPORT,
                    RuntimeDescriptor.Int.INSTANCE, new ValueId(0),
                    new BoundaryRealization.RepresentationProof("p")),
                SemanticOpKind.BOUNDARY, RuntimeDescriptor.Int.INSTANCE, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST))),
            "changing the boundary realization changes the digest");

        // Call mode and signature.
        RuntimeDescriptor.Func sig1 = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Int.INSTANCE);
        RuntimeDescriptor.Func sig2 = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);
        KindPayload.CallPayload direct = new KindPayload.CallPayload(CallMode.DIRECT,
            new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                new FunctionId(0), new BlockId(0))),
            sig1, List.of(), null, null, new BlockId(0), null);
        String callDigest = digest(snapshotFor(direct, SemanticOpKind.CALL,
            RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            PLACEHOLDER_DIGEST));
        KindPayload.CallPayload external = new KindPayload.CallPayload(CallMode.EXTERNAL,
            new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                new FunctionId(0), new BlockId(0))),
            sig1, List.of(), null, null, new BlockId(0), null);
        check(!callDigest.equals(digest(snapshotFor(external, SemanticOpKind.CALL,
                RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                PLACEHOLDER_DIGEST))),
            "changing the call mode changes the digest");
        KindPayload.CallPayload wider = new KindPayload.CallPayload(CallMode.DIRECT,
            new KindPayload.CallCallee.Static(new FunctionExecutionBinding.LoweredBody(
                new FunctionId(0), new BlockId(0))),
            sig2, List.of(), null, null, new BlockId(0), null);
        check(!callDigest.equals(digest(snapshotFor(wider, SemanticOpKind.CALL,
                RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                PLACEHOLDER_DIGEST))),
            "changing the call signature changes the digest");

        // opId/origin live outside the snapshot: identical snapshot fields,
        // different op ids/origins — identical digest.
        KindPayload payloadA = new KindPayload.ConstPayload(new ScalarValue.Int(1));
        KindPayload payloadB = new KindPayload.ConstPayload(new ScalarValue.Int(1));
        OperationContractSnapshot first = snapshotFor(
            payloadA, SemanticOpKind.CONST,
            RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            PLACEHOLDER_DIGEST);
        OperationContractSnapshot second = snapshotFor(
            payloadB, SemanticOpKind.CONST,
            RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            PLACEHOLDER_DIGEST);
        SemanticOp opA = new SemanticOp(new OpId(APP, 1), SemanticOpKind.CONST,
            origin(0, "a.deal"), new ValueId(5), RuntimeDescriptor.Int.INSTANCE, List.of(),
            List.of(), payloadA,
            FailurePolicyId.NO_DEAL_FAILURE, first);
        SemanticOp opB = new SemanticOp(new OpId(APP, 2), SemanticOpKind.CONST,
            origin(1, "b.deal"), new ValueId(6), RuntimeDescriptor.Int.INSTANCE, List.of(),
            List.of(), payloadB,
            FailurePolicyId.NO_DEAL_FAILURE, second);
        check(digest(opA.contract()).equals(digest(opB.contract())),
            "changing only opId/origin/result leaves the digest unchanged");
    }

    static String digest(OperationContractSnapshot snapshot) {
        return ContractSnapshotCanonicalizer.digest(snapshot);
    }

    // =========================================================================
    // 5. loweringContextHash golden + profile confusion guard
    // =========================================================================

    static void testLoweringContextHash() {
        System.out.println("-- Lowering context hash (pinned formula) --");

        String hash = LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        check(PINNED_LOWERING_CONTEXT_GOLDEN.equals(hash),
            "the lowering-context hash equals the stored golden; got " + hash);
        check(hash.length() == 64 && hash.matches("[0-9a-f]{64}"),
            "the lowering-context hash is lowercase 64-character hex");

        // The canonical JSON input has exactly the two pinned keys in sorted
        // order with the profile as its enum name and the registry hash
        // verbatim.
        String expected = "{\"capabilityRegistryHash\":\"" + REGISTRY_HASH
            + "\",\"semanticProfile\":\"DEAL_V1_2_INT32\"}";
        CanonicalJson.Value json = CanonicalJson.obj(
            CanonicalJson.e("semanticProfile",
                CanonicalJson.str(SemanticProfile.DEAL_V1_2_INT32.name())),
            CanonicalJson.e("capabilityRegistryHash", CanonicalJson.str(REGISTRY_HASH)));
        check(expected.equals(CanonicalJson.serializeText(json)),
            "the digest input serializes as " + expected);
        check(hash.equals(CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(json))),
            "the helper computes SHA-256 of exactly that canonical JSON");

        // T1 confusion guard: a legacy-profile input cannot be confused with
        // the v1.2 one (the enum names differ, so the digests differ).
        String legacy = LoweringContextHash.of(SemanticProfile.LEGACY_SAFE_INT, REGISTRY_HASH);
        check(!legacy.equals(hash),
            "a LEGACY_SAFE_INT lowering-context hash differs from the DEAL_V1_2_INT32 one");

        // Same input, different registry hash → different digest.
        check(!hash.equals(LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                REGISTRY_HASH.replace('a', 'b'))),
            "changing the capability-registry hash changes the digest");

        // The LoweringContext record overload (T2's pinned input domain).
        LoweringContext context = new LoweringContext(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        check(hash.equals(LoweringContextHash.of(context)),
            "the LoweringContext overload computes the same digest");
        check(LoweringContext.CANONICAL_JSON_KEYS.equals(
                List.of("capabilityRegistryHash", "semanticProfile")),
            "the pinned key list is {capabilityRegistryHash, semanticProfile} in sorted order");
    }

    // =========================================================================
    // 6. Combined T1/T2 integration
    // =========================================================================

    static void testCombinedT1T2() {
        System.out.println("-- Combined T1/T2 integration --");

        // T1: the helper consumes the closed SemanticProfile enum.
        check("DEAL_V1_2_INT32".equals(SemanticProfile.DEAL_V1_2_INT32.name())
                && "LEGACY_SAFE_INT".equals(SemanticProfile.LEGACY_SAFE_INT.name()),
            "T1's SemanticProfile enum names are pinned");
        try {
            SemanticProfile.valueOf("OUT_OF_SET");
            fail("an out-of-set SemanticProfile name must not resolve (T1 fault)");
        } catch (IllegalArgumentException expected) {
            check(true, "a T1 profile fault is detectable (valueOf throws)");
        }

        // T2: the canonicalizer consumes the closed schema facts.
        check(OperationContractSnapshot.VERSION == 1,
            "T2's snapshot version is pinned to 1");
        check(SemanticOpKind.BINARY.payloadClass() == KindPayload.BinaryPayload.class,
            "T2's BINARY payload shape is pinned");
        check(BinarySelector.values().length == 42,
            "T2's BinarySelector has exactly 42 values; got " + BinarySelector.values().length);

        // T2's RuntimeDescriptor canonical text renders in the JSON.
        String text = ContractSnapshotCanonicalizer.serializeText(pinnedSnapshot());
        check(text.contains("\"resultType\":\"[int]\"")
                && text.contains("\"operandTypes\":[\"int\",\"int\"]"),
            "descriptors render as T2's canonical spec text (int descriptor -> \"int\")");
        String unaryText = ContractSnapshotCanonicalizer.serializeText(
            snapshotFor(new KindPayload.UnaryPayload(UnarySelector.INT32_NEG),
                SemanticOpKind.UNARY, RuntimeDescriptor.Int.INSTANCE, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST));
        check(unaryText.contains("\"selector\":\"INT32_NEG\""),
            "the closed unary selector renders as its name");

        // The 42-selector digest matrix: valid distinct digests, one per
        // BinarySelector value.
        Set<String> digests = new LinkedHashSet<>();
        for (BinarySelector selector : BinarySelector.values()) {
            OperationContractSnapshot snapshot = binaryMatrixSnapshot(selector);
            String d = digest(snapshot);
            check(d.matches("[0-9a-f]{64}"), selector + " produces a valid digest");
            digests.add(d);
            check(ContractSnapshotCanonicalizer.serializeText(snapshot)
                    .contains("\"selector\":\"" + selector.name() + "\""),
                selector + " renders its exact selector name");
        }
        check(digests.size() == 42,
            "all 42 selector digests are distinct; got " + digests.size());

        // Every SemanticOpKind payload shape canonicalizes and digests.
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            KindPayload payload = minimalPayload(kind);
            check(kind.payloadClass().isInstance(payload),
                kind + " payload is the pinned shape (T2 fault detection)");
            OperationContractSnapshot snapshot = snapshotFor(payload, kind,
                RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE,
                PLACEHOLDER_DIGEST);
            String d = digest(snapshot);
            check(d.matches("[0-9a-f]{64}"),
                kind + " payload canonicalizes to a valid digest");
            check(ContractSnapshotCanonicalizer.toJson(snapshot)
                    instanceof CanonicalJson.Obj,
                kind + " snapshot maps to a canonical JSON object");
        }

        // Internal result-type sentinels and the none slot render distinctly.
        check(ContractSnapshotCanonicalizer.serializeText(
                snapshotFor(new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    SemanticOpKind.CONST, InternalResultType.INTERNAL_MISSING, List.of(),
                    FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST))
                .contains("\"resultType\":\"INTERNAL_MISSING\""),
            "INTERNAL_MISSING renders as its sentinel name");
        check(ContractSnapshotCanonicalizer.serializeText(
                snapshotFor(new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    SemanticOpKind.CONST, null, List.of(),
                    FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST))
                .contains("\"resultType\":null"),
            "the none result slot renders as an explicit null");
        check(ContractSnapshotCanonicalizer.serializeText(
                snapshotFor(new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                    SemanticOpKind.CONST, RuntimeDescriptor.Null.INSTANCE, List.of(),
                    FailurePolicyId.NO_DEAL_FAILURE, PLACEHOLDER_DIGEST))
                .contains("\"resultType\":\"null\""),
            "the null descriptor renders as the string \"null\" (distinct from JSON null)");
    }

    // =========================================================================
    // Minimal payload fixtures (one per SemanticOpKind; mirrors T2's shapes)
    // =========================================================================

    private static final ClassLayout LAYOUT = new ClassLayout(CLS, List.of(
        new ClassLayout.FieldLayout("f", RuntimeDescriptor.Int.INSTANCE, false, DefaultOwner.LOCAL)));

    static KindPayload minimalPayload(SemanticOpKind kind) {
        ValueId v0 = new ValueId(0);
        ValueId v1 = new ValueId(1);
        BlockId b0 = new BlockId(0);
        OpId o0 = new OpId(APP, 0);
        OpId o1 = new OpId(APP, 1);
        return switch (kind) {
            case CONST -> new KindPayload.ConstPayload(new ScalarValue.Int(1));
            case UNARY -> new KindPayload.UnaryPayload(UnarySelector.BOOL_NOT);
            case BINARY -> new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null);
            case STRING_CONCAT -> new KindPayload.StringConcatPayload(List.of(v0, v1));
            case ARRAY_NEW -> new KindPayload.ArrayNewPayload(RuntimeDescriptor.Int.INSTANCE,
                List.of(v0), List.of(o0));
            case TABLE_NEW -> new KindPayload.TableNewPayload(
                List.of(new KindPayload.TableEntry("k", v0)));
            case ARRAY_LENGTH -> new KindPayload.ArrayLengthPayload(v0);
            case MEMBER_READ -> new KindPayload.MemberReadPayload(v0, "k");
            case MEMBER_WRITE -> new KindPayload.MemberWritePayload(v0, "k", v1);
            case MEMBER_DELETE -> new KindPayload.MemberDeletePayload(v0, "k");
            case INDEX_NORMALIZE -> new KindPayload.IndexNormalizePayload(
                IndexMode.ARRAY_READ, v0, v1);
            case INDEX_READ -> new KindPayload.IndexReadPayload(v0, v1, o0);
            case INDEX_WRITE -> new KindPayload.IndexWritePayload(v0, v1, new ValueId(2));
            case INDEX_DELETE -> new KindPayload.IndexDeletePayload(v0, v1);
            case OPTIONAL_READ -> new KindPayload.OptionalReadPayload(
                v0, true, RuntimeDescriptor.Int.INSTANCE);
            case HAS_FIELD -> new KindPayload.HasFieldPayload(v0, "k");
            case BOUNDARY -> new KindPayload.BoundaryPayload(BoundaryKind.MODULE_EXPORT,
                RuntimeDescriptor.Int.INSTANCE, v0, new BoundaryRealization.RuntimeValidation("c"));
            case BINDING_ALLOC -> new KindPayload.BindingAllocPayload(
                new BindingId(0), b0, false, BindingCellKind.DIRECT, 0);
            case BINDING_INIT -> new KindPayload.BindingInitPayload(new BindingId(0), 0, v0);
            case BINDING_LOAD -> new KindPayload.BindingLoadPayload(new BindingId(0), 0);
            case BINDING_STORE -> new KindPayload.BindingStorePayload(new BindingId(0), 0, v0);
            case RECURSIVE_GROUP_INIT -> new KindPayload.RecursiveGroupInitPayload(
                List.of(new BindingId(0)), List.of(new FunctionId(0)));
            case CLOSURE_NEW -> new KindPayload.ClosureNewPayload(new FunctionId(0), SIG,
                List.of(), new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0));
            case FUNCTION_ADAPT -> new KindPayload.FunctionAdaptPayload(SIG, SIG,
                CaptureMode.SHARED_CELL, new AdaptSourceRef.SharedCell(new BindingId(0), 0), null);
            case ASSIGN -> new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                List.of(o0, o1));
            case DELETE -> new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                List.of(o0, o1));
            case CALL -> new KindPayload.CallPayload(CallMode.DIRECT,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0)),
                SIG, List.of(), null, null, b0, null);
            case EXTERNAL_ENTRY -> new KindPayload.ExternalEntryPayload(
                "export", new FunctionId(0), SIG, false, o0, null);
            case CALLBACK_INVOKE -> new KindPayload.CallbackInvokePayload(
                v0, SIG, List.of(), o0);
            case INTRINSIC_CALL -> new KindPayload.IntrinsicCallPayload(
                IntrinsicKind.INT_CONVERT, v0);
            case STDLIB_CALL -> new KindPayload.StdlibCallPayload(
                StdlibFunctionId.MATH_FLOOR, List.of(v0), SemanticCapability.STDLIB_SEMANTICS);
            case ASYNC_START -> new KindPayload.AsyncStartPayload(
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0)),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(),
                RuntimeDescriptor.Null.INSTANCE, o0, null, null);
            case AWAIT -> new KindPayload.AwaitPayload(new AsyncTokenId.Canonical(5,
                    AsyncTokenOwner.DEAL_BODY_TASK),
                RuntimeDescriptor.Null.INSTANCE, o0);
            case BRANCH -> new KindPayload.BranchPayload(ControlSelector.IF, v0, b0, null);
            case LOOP -> new KindPayload.LoopPayload(ControlSelector.WHILE, null, v0, b0, null);
            case FOR_EACH -> new KindPayload.ForEachPayload(IterationMode.ARRAY_VALUES,
                v0, new BindingId(0), 0, b0);
            case TRY_CATCH -> new KindPayload.TryCatchPayload(b0, new BindingId(0), new BlockId(1));
            case THROW -> new KindPayload.ThrowPayload(v0);
            case RETURN -> new KindPayload.ReturnPayload(null, new FunctionId(0), o0, o1);
            case BREAK -> new KindPayload.BreakPayload(o0);
            case CONTINUE -> new KindPayload.ContinuePayload(o0);
            case DISCARD -> new KindPayload.DiscardPayload(v0);
            case CLASS_DEFAULT -> new KindPayload.ClassDefaultPayload(CLS, "f", b0);
            case CLASS_NEW -> new KindPayload.ClassNewPayload(CLS, LAYOUT,
                List.of(), DefaultOwner.LOCAL, List.of(), null, List.of());
            case CLASS_FACTORY -> new KindPayload.ClassFactoryPayload(CLS, List.of(), o0);
            case FIELD_READ -> new KindPayload.FieldReadPayload(v0, CLS, "f");
            case FIELD_WRITE -> new KindPayload.FieldWritePayload(v0, CLS, "f", v1);
            case FIELD_DELETE -> new KindPayload.FieldDeletePayload(v0, CLS, "f");
            case JSON_FROM_CLASS -> new KindPayload.JsonFromClassPayload(LAYOUT, v0);
            case JSON_TO_CLASS -> new KindPayload.JsonToClassPayload(v0, LAYOUT);
            case MODULE_INIT -> new KindPayload.ModuleInitPayload(APP, List.of(), b0);
            case MODULE_IMPORT -> new KindPayload.ModuleImportPayload(
                "a", new ModuleId("a"), ModuleImportKind.COMPILED);
            case EXPORT_READ -> new KindPayload.ExportReadPayload(
                new ModuleId("a"), "x", RuntimeDescriptor.Int.INSTANCE, v0);
            case EXPORT_PUBLISH -> new KindPayload.ExportPublishPayload(
                APP, "x", RuntimeDescriptor.Int.INSTANCE, v0);
            case ENTRY_INVOKE -> new KindPayload.EntryInvokePayload(APP, new FunctionId(0));
        };
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        if (args.length > 0 && args[0].equals("--emit")) {
            System.out.println("CROSS:" + Base64.getEncoder().encodeToString(compositeDocumentBytes()));
            System.out.println("SNAP:" + Base64.getEncoder().encodeToString(
                ContractSnapshotCanonicalizer.serialize(pinnedSnapshot())));
            return;
        }
        if (args.length > 0 && args[0].equals("--print")) {
            System.out.println("DOC=" + CanonicalJson.serializeText(compositeDocument()));
            System.out.println("SNAP_DIGEST=" + ContractSnapshotCanonicalizer.digest(pinnedSnapshot()));
            System.out.println("LCH=" + LoweringContextHash.of(
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
            System.out.println("SNAP_TEXT=" + ContractSnapshotCanonicalizer.serializeText(
                pinnedSnapshot()));
            return;
        }

        System.out.println("=== Canonical JSON / Snapshot Digest / Lowering Context Test "
            + "(ISSUE-0283) ===\n");

        testCanonicalRules();
        testCrossProcessDeterminism();
        testParserRoundTrips();
        testRawStringsSurvive();
        testDecodeFailures();
        testDigest();
        testLoweringContextHash();
        testCombinedT1T2();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
