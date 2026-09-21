package deal.semantic.ir;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * The single operation-contract snapshot canonicalizer of
 * {@code deal.semantic-ir/1} (schema S2; foundation F8): the only
 * production implementation that maps {@link OperationContractSnapshot}
 * records (and every schema record they embed — kind payloads, semantic
 * IDs, descriptors, scalars, bindings, realizations, adapt-source refs,
 * tokens, layouts) onto the single {@link CanonicalJson} value model and
 * computes the pinned digest. The validator, dumper, and trace harness
 * consume canonicalization through this one component and the one
 * {@code CanonicalJson} facility — no consumer serializes for itself.
 *
 * <p>{@code canonicalDigest = SHA-256(canonical JSON bytes)} over exactly
 * {@code {version, opKind, resultType, operandTypes, selector?, payload,
 * failurePolicy, referencedSemanticIds}} — the eight pinned fields of the
 * snapshot record, with the optional {@code selector} rendered as an
 * explicit {@code null} when absent (S2 explicit-nulls rule). The
 * snapshot's carried {@code canonicalDigest} field is itself <em>not</em>
 * part of the digest input; {@code opId}, source coordinates, and trace
 * phase live on {@link SemanticOp}/{@link SourceOrigin} outside the
 * snapshot and never enter the digest, while behavior-referenced IDs
 * (class/function/binding/block/module …) are inside it.</p>
 *
 * <p>Pinned JSON shapes (all keys ASCII; the serializer sorts object
 * keys): closed enum values render as their names; descriptors render as
 * their canonical spec text ({@code "int"}, {@code "@src/app/User"},
 * {@code "(int,string)->boolean"}); scalars render as canonical JSON
 * scalars (decimal signed32, unique hex floats, explicit null); optional
 * record components render as explicit {@code null}s; semantic IDs render
 * as discriminated objects ({@code {"type":"module","path":"a.b"}}, …);
 * payloads render as one object per closed kind shape with the record
 * component names as keys. The parser inverts these shapes exactly and
 * returns a {@link SnapshotJsonRecord} whose enum positions carry raw
 * strings (no enum conversion at parse time).</p>
 */
public final class ContractSnapshotCanonicalizer {

    private ContractSnapshotCanonicalizer() {
        // Static utility; no instances.
    }

    // =========================================================================
    // Pinned snapshot field names
    // =========================================================================

    /** The pinned snapshot field name {@code "version"}. */
    public static final String FIELD_VERSION = "version";

    /** The pinned snapshot field name {@code "opKind"}. */
    public static final String FIELD_OP_KIND = "opKind";

    /** The pinned snapshot field name {@code "resultType"}. */
    public static final String FIELD_RESULT_TYPE = "resultType";

    /** The pinned snapshot field name {@code "operandTypes"}. */
    public static final String FIELD_OPERAND_TYPES = "operandTypes";

    /** The pinned snapshot field name {@code "selector"}. */
    public static final String FIELD_SELECTOR = "selector";

    /** The pinned snapshot field name {@code "payload"}. */
    public static final String FIELD_PAYLOAD = "payload";

    /** The pinned snapshot field name {@code "failurePolicy"}. */
    public static final String FIELD_FAILURE_POLICY = "failurePolicy";

    /** The pinned snapshot field name {@code "referencedSemanticIds"}. */
    public static final String FIELD_REFERENCED_SEMANTIC_IDS = "referencedSemanticIds";

    /** The exact eight pinned snapshot field names (the digest field set). */
    public static final List<String> SNAPSHOT_FIELDS = List.of(
        FIELD_VERSION, FIELD_OP_KIND, FIELD_RESULT_TYPE, FIELD_OPERAND_TYPES,
        FIELD_SELECTOR, FIELD_PAYLOAD, FIELD_FAILURE_POLICY,
        FIELD_REFERENCED_SEMANTIC_IDS);

    // =========================================================================
    // Snapshot canonicalization and digest
    // =========================================================================

    /**
     * Maps the snapshot onto the single canonical JSON value model. The
     * carried {@code canonicalDigest} field is not part of the mapping —
     * the digest is computed over the eight pinned fields only.
     *
     * @param snapshot the snapshot; non-null
     * @return the canonical JSON object
     */
    public static CanonicalJson.Value toJson(OperationContractSnapshot snapshot) {
        Objects.requireNonNull(snapshot, "snapshot must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e(FIELD_FAILURE_POLICY, CanonicalJson.str(snapshot.failurePolicy().name())),
            CanonicalJson.e(FIELD_OP_KIND, CanonicalJson.str(snapshot.opKind().name())),
            CanonicalJson.e(FIELD_OPERAND_TYPES, CanonicalJson.arr(
                snapshot.operandTypes().stream().map(d -> (CanonicalJson.Value) descriptorText(d)).toList())),
            CanonicalJson.e(FIELD_PAYLOAD, payloadJson(snapshot.payload())),
            CanonicalJson.e(FIELD_REFERENCED_SEMANTIC_IDS, CanonicalJson.arr(
                snapshot.referencedSemanticIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
            CanonicalJson.e(FIELD_RESULT_TYPE, resultTypeJson(snapshot.resultType())),
            CanonicalJson.e(FIELD_SELECTOR,
                snapshot.selector() == null ? CanonicalJson.nullValue()
                    : CanonicalJson.str(selectorName(snapshot.selector()))),
            CanonicalJson.e(FIELD_VERSION, CanonicalJson.intValue(snapshot.version())));
    }

    /**
     * Serializes the snapshot to its canonical JSON bytes (UTF-8, sorted
     * keys, explicit nulls).
     *
     * @param snapshot the snapshot; non-null
     * @return the canonical JSON bytes
     */
    public static byte[] serialize(OperationContractSnapshot snapshot) {
        return CanonicalJson.serializeBytes(toJson(snapshot));
    }

    /** Serializes the snapshot to canonical JSON text (debug/trace surface only). */
    public static String serializeText(OperationContractSnapshot snapshot) {
        return CanonicalJson.serializeText(toJson(snapshot));
    }

    /**
     * Computes the pinned digest: {@code SHA-256(canonical JSON bytes)}
     * over exactly {@code {version, opKind, resultType, operandTypes,
     * selector?, payload, failurePolicy, referencedSemanticIds}}. Changing
     * any behavior field changes the digest; changing only {@code opId},
     * source coordinates, or trace phase (fields that live outside the
     * snapshot) does not.
     *
     * @param snapshot the snapshot; non-null
     * @return the lowercase 64-character hex digest
     */
    public static String digest(OperationContractSnapshot snapshot) {
        return CanonicalJson.sha256Hex(serialize(snapshot));
    }

    /**
     * Recomputes the digest and reports whether it equals the snapshot's
     * carried {@code canonicalDigest} (R-DIGEST's recomputation, without
     * being a validator rule itself).
     *
     * @param snapshot the snapshot; non-null
     * @return true iff the carried digest equals the recomputed digest
     */
    public static boolean matchesCarriedDigest(OperationContractSnapshot snapshot) {
        return digest(snapshot).equals(snapshot.canonicalDigest());
    }

    // =========================================================================
    // General canonical JSON serialization (the single serializer entry)
    // =========================================================================

    /**
     * Serializes an arbitrary canonical JSON value to canonical JSON UTF-8
     * bytes through the single serializer of this component. This is the
     * general-value serialization entry every whole-document producer
     * (the dumper, the validator's digest recomputations) consumes: the
     * canonicalizer remains the one component that touches the
     * serializer, so whole documents and snapshots can never diverge in
     * encoding rules (S2; foundation F8).
     *
     * @param value the canonical JSON value; non-null
     * @return the canonical JSON bytes
     */
    public static byte[] serializeJson(CanonicalJson.Value value) {
        return CanonicalJson.serializeBytes(Objects.requireNonNull(value, "value must not be null"));
    }

    /**
     * Serializes an arbitrary canonical JSON value to canonical JSON text
     * (UTF-8; debug/observation surface only).
     *
     * @param value the canonical JSON value; non-null
     * @return the canonical JSON text
     */
    public static String serializeText(CanonicalJson.Value value) {
        return new String(serializeJson(value), java.nio.charset.StandardCharsets.UTF_8);
    }

    // =========================================================================
    // Parser (exact inverse)
    // =========================================================================

    /**
     * Parses a serialized snapshot back through the single canonical JSON
     * parser: the pinned field names and JSON value types are mapped into a
     * {@link SnapshotJsonRecord} whose enum positions carry raw strings.
     * No closed-enum, reserved-name, policy, boundary-assignment, or
     * profile validation happens here.
     *
     * @param utf8 the serialized snapshot bytes; non-null
     * @return the intermediate record
     * @throws SemanticIrTextDecodeException on malformed JSON, invalid
     *         UTF-8, a duplicate/unknown/missing field, a wrong value type,
     *         or a wrong version
     */
    public static SnapshotJsonRecord parseSnapshot(byte[] utf8) {
        CanonicalJson.Value value = CanonicalJson.parse(utf8);
        if (!(value instanceof CanonicalJson.Obj obj)) {
            throw new SemanticIrTextDecodeException(
                "the top-level snapshot value must be an object, got "
                    + jsonKindName(value));
        }
        return snapshotFromJson(obj);
    }

    /**
     * Parses a serialized snapshot text back through the single canonical
     * JSON parser.
     *
     * @param text the serialized snapshot text; non-null
     * @return the intermediate record
     * @throws SemanticIrTextDecodeException as in {@link #parseSnapshot(byte[])}
     */
    public static SnapshotJsonRecord parseSnapshot(String text) {
        return parseSnapshot(text.getBytes(java.nio.charset.StandardCharsets.UTF_8));
    }

    /** Maps the intermediate record back onto the canonical JSON value model. */
    public static CanonicalJson.Value toJson(SnapshotJsonRecord record) {
        Objects.requireNonNull(record, "record must not be null");
        if (!(record.payload() instanceof CanonicalJson.Obj)) {
            throw new IllegalArgumentException("SnapshotJsonRecord.payload must be a JSON object");
        }
        return CanonicalJson.obj(
            CanonicalJson.e(FIELD_FAILURE_POLICY, CanonicalJson.str(record.failurePolicy())),
            CanonicalJson.e(FIELD_OP_KIND, CanonicalJson.str(record.opKind())),
            CanonicalJson.e(FIELD_OPERAND_TYPES, CanonicalJson.arr(
                record.operandTypes().stream().map(v -> (CanonicalJson.Value) CanonicalJson.str(v)).toList())),
            CanonicalJson.e(FIELD_PAYLOAD, record.payload()),
            CanonicalJson.e(FIELD_REFERENCED_SEMANTIC_IDS,
                CanonicalJson.arr(record.referencedSemanticIds())),
            CanonicalJson.e(FIELD_RESULT_TYPE,
                record.resultType() == null ? CanonicalJson.nullValue()
                    : CanonicalJson.str(record.resultType())),
            CanonicalJson.e(FIELD_SELECTOR,
                record.selector() == null ? CanonicalJson.nullValue()
                    : CanonicalJson.str(record.selector())),
            CanonicalJson.e(FIELD_VERSION, CanonicalJson.intValue(record.version())));
    }

    /** Serializes the intermediate record to canonical JSON bytes. */
    public static byte[] serialize(SnapshotJsonRecord record) {
        return CanonicalJson.serializeBytes(toJson(record));
    }

    /** Serializes the intermediate record to canonical JSON text (debug/trace surface only). */
    public static String serializeText(SnapshotJsonRecord record) {
        return CanonicalJson.serializeText(toJson(record));
    }

    private static SnapshotJsonRecord snapshotFromJson(CanonicalJson.Obj obj) {
        for (String key : knownKeys(obj)) {
            if (!SNAPSHOT_FIELDS.contains(key)) {
                throw new SemanticIrTextDecodeException(
                    "unknown snapshot field \"" + key + "\" (pinned field set is "
                        + SNAPSHOT_FIELDS + ")");
            }
        }
        int version = expectInt(field(obj, FIELD_VERSION), FIELD_VERSION);
        if (version != OperationContractSnapshot.VERSION) {
            throw new SemanticIrTextDecodeException(
                "version mismatch: expected " + OperationContractSnapshot.VERSION
                    + " in deal.semantic-ir/1, got " + version);
        }
        String opKind = expectString(field(obj, FIELD_OP_KIND), FIELD_OP_KIND);
        String resultType = expectStringOrNull(field(obj, FIELD_RESULT_TYPE), FIELD_RESULT_TYPE);
        CanonicalJson.Arr operandTypes = expectArray(field(obj, FIELD_OPERAND_TYPES),
            FIELD_OPERAND_TYPES);
        List<String> operandTypeTexts = new ArrayList<>();
        for (int i = 0; i < operandTypes.items().size(); i++) {
            operandTypeTexts.add(expectString(operandTypes.items().get(i),
                FIELD_OPERAND_TYPES + "[" + i + "]"));
        }
        String selector = expectStringOrNull(field(obj, FIELD_SELECTOR), FIELD_SELECTOR);
        CanonicalJson.Value payload = field(obj, FIELD_PAYLOAD);
        if (!(payload instanceof CanonicalJson.Obj)) {
            throw new SemanticIrTextDecodeException(
                "the \"" + FIELD_PAYLOAD + "\" field must be an object, got "
                    + jsonKindName(payload));
        }
        String failurePolicy = expectString(field(obj, FIELD_FAILURE_POLICY), FIELD_FAILURE_POLICY);
        CanonicalJson.Arr referenced = expectArray(
            field(obj, FIELD_REFERENCED_SEMANTIC_IDS), FIELD_REFERENCED_SEMANTIC_IDS);
        for (int i = 0; i < referenced.items().size(); i++) {
            if (!(referenced.items().get(i) instanceof CanonicalJson.Obj)) {
                throw new SemanticIrTextDecodeException(
                    "the " + FIELD_REFERENCED_SEMANTIC_IDS + "[" + i
                        + "] entry must be a semantic-ID object, got "
                        + jsonKindName(referenced.items().get(i)));
            }
        }
        return new SnapshotJsonRecord(version, opKind, resultType,
            List.copyOf(operandTypeTexts), selector, payload, failurePolicy,
            List.copyOf(referenced.items()));
    }

    private static List<String> knownKeys(CanonicalJson.Obj obj) {
        List<String> keys = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            keys.add(entry.key());
        }
        return keys;
    }

    private static CanonicalJson.Value field(CanonicalJson.Obj obj, String name) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(name)) {
                return entry.value();
            }
        }
        throw new SemanticIrTextDecodeException(
            "missing snapshot field \"" + name + "\" (pinned field set is "
                + SNAPSHOT_FIELDS + ")");
    }

    private static int expectInt(CanonicalJson.Value value, String field) {
        if (value instanceof CanonicalJson.Int i) {
            return i.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + field + "\" field must be a canonical signed32 integer, got "
                + jsonKindName(value));
    }

    private static String expectString(CanonicalJson.Value value, String field) {
        if (value instanceof CanonicalJson.Str s) {
            return s.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + field + "\" field must be a string, got " + jsonKindName(value));
    }

    private static String expectStringOrNull(CanonicalJson.Value value, String field) {
        if (value instanceof CanonicalJson.Null) {
            return null;
        }
        return expectString(value, field);
    }

    private static CanonicalJson.Arr expectArray(CanonicalJson.Value value, String field) {
        if (value instanceof CanonicalJson.Arr a) {
            return a;
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + field + "\" field must be an array, got " + jsonKindName(value));
    }

    /** The canonical JSON kind name of a value (decode-failure messages). */
    public static String jsonKindName(CanonicalJson.Value value) {
        return switch (value) {
            case CanonicalJson.Null ignored -> "null";
            case CanonicalJson.Bool b -> "boolean (" + b.value() + ")";
            case CanonicalJson.Int i -> "integer (" + i.value() + ")";
            case CanonicalJson.Num n -> "number";
            case CanonicalJson.Str s -> "string (\"" + s.value() + "\")";
            case CanonicalJson.Arr a -> "array (" + a.items().size() + " items)";
            case CanonicalJson.Obj o -> "object (" + o.entries().size() + " entries)";
        };
    }

    // =========================================================================
    // Shared shape mappings (the single production implementation)
    // =========================================================================

    /** Renders a runtime descriptor as its canonical spec text (parent D6). */
    public static CanonicalJson.Str descriptorText(RuntimeDescriptor descriptor) {
        return CanonicalJson.str(Objects.requireNonNull(descriptor, "descriptor must not be null")
            .canonicalSpecText());
    }

    /** Renders an op result type: descriptor text, internal sentinel name, or explicit null. */
    public static CanonicalJson.Value resultTypeJson(OpResultType resultType) {
        if (resultType == null) {
            return CanonicalJson.nullValue();
        }
        if (resultType instanceof RuntimeDescriptor descriptor) {
            return descriptorText(descriptor);
        }
        if (resultType instanceof InternalResultType internal) {
            return CanonicalJson.str(internal.name());
        }
        throw new IllegalArgumentException("unknown result type: " + resultType.getClass());
    }

    /** Renders a canonical scalar. */
    public static CanonicalJson.Value scalarJson(ScalarValue scalar) {
        Objects.requireNonNull(scalar, "scalar must not be null");
        return switch (scalar) {
            case ScalarValue.Null ignored -> CanonicalJson.nullValue();
            case ScalarValue.Boolean b -> CanonicalJson.bool(b.value());
            case ScalarValue.Int i -> CanonicalJson.intValue(i.value());
            case ScalarValue.Number n -> CanonicalJson.number(n.value());
            case ScalarValue.String s -> CanonicalJson.str(s.value());
        };
    }

    /** Renders a semantic ID as its pinned discriminated object. */
    public static CanonicalJson.Value semanticIdJson(SemanticId id) {
        Objects.requireNonNull(id, "id must not be null");
        return switch (id) {
            case ModuleId m -> CanonicalJson.obj(
                CanonicalJson.e("path", CanonicalJson.str(m.path())),
                CanonicalJson.e("type", CanonicalJson.str("module")));
            case ClassId c -> CanonicalJson.obj(
                CanonicalJson.e("modulePath", CanonicalJson.str(c.modulePath())),
                CanonicalJson.e("name", CanonicalJson.str(c.name())),
                CanonicalJson.e("type", CanonicalJson.str("class")));
            case FunctionId f -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(f.id(), "FunctionId")),
                CanonicalJson.e("type", CanonicalJson.str("function")));
            case BindingId b -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(b.id(), "BindingId")),
                CanonicalJson.e("type", CanonicalJson.str("binding")));
            case ValueId v -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(v.id(), "ValueId")),
                CanonicalJson.e("type", CanonicalJson.str("value")));
            case AnchorId a -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(a.id(), "AnchorId")),
                CanonicalJson.e("type", CanonicalJson.str("anchor")));
            case BlockId b -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(b.id(), "BlockId")),
                CanonicalJson.e("type", CanonicalJson.str("block")));
            case OpId o -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(o.id(), "OpId")),
                CanonicalJson.e("modulePath", CanonicalJson.str(o.module().path())),
                CanonicalJson.e("type", CanonicalJson.str("op")));
            case ClassFactoryId c -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(c.id(), "ClassFactoryId")),
                CanonicalJson.e("type", CanonicalJson.str("classFactory")));
            case FunctionAllocationIdentity f -> CanonicalJson.obj(
                CanonicalJson.e("id", idValue(f.id(), "FunctionAllocationIdentity")),
                CanonicalJson.e("type", CanonicalJson.str("functionAllocation")));
            case AsyncTokenId.Canonical c -> CanonicalJson.obj(
                CanonicalJson.e("owner", CanonicalJson.str(c.owner().name())),
                CanonicalJson.e("tokenId", idValue(c.tokenId(), "tokenId")),
                CanonicalJson.e("type", CanonicalJson.str("tokenCanonical")));
            case AsyncTokenId.Alias a -> CanonicalJson.obj(
                CanonicalJson.e("linkKind", CanonicalJson.str(a.linkKind().name())),
                CanonicalJson.e("referent", semanticIdJson(a.referent())),
                CanonicalJson.e("tokenId", idValue(a.tokenId(), "tokenId")),
                CanonicalJson.e("type", CanonicalJson.str("tokenAlias")));
        };
    }

    /** Renders a boundary realization as its pinned discriminated object. */
    public static CanonicalJson.Value realizationJson(BoundaryRealization realization) {
        Objects.requireNonNull(realization, "realization must not be null");
        return switch (realization) {
            case BoundaryRealization.RuntimeValidation r -> CanonicalJson.obj(
                CanonicalJson.e("checkId", CanonicalJson.str(r.checkId())),
                CanonicalJson.e("type", CanonicalJson.str("runtimeValidation")));
            case BoundaryRealization.RepresentationProof p -> CanonicalJson.obj(
                CanonicalJson.e("proofKind", CanonicalJson.str(p.proofKind())),
                CanonicalJson.e("type", CanonicalJson.str("representationProof")));
        };
    }

    /** Renders a function execution binding as its pinned discriminated object. */
    public static CanonicalJson.Value bindingJson(FunctionExecutionBinding binding) {
        Objects.requireNonNull(binding, "binding must not be null");
        return switch (binding) {
            case FunctionExecutionBinding.LoweredBody b -> CanonicalJson.obj(
                CanonicalJson.e("blockId", semanticIdJson(b.blockId())),
                CanonicalJson.e("functionId", semanticIdJson(b.functionId())),
                CanonicalJson.e("type", CanonicalJson.str("loweredBody")));
            case FunctionExecutionBinding.AdapterBinding b -> CanonicalJson.obj(
                CanonicalJson.e("adaptOpId", semanticIdJson(b.adaptOpId())),
                CanonicalJson.e("captureMode", CanonicalJson.str(b.captureMode().name())),
                CanonicalJson.e("sourceRef", sourceRefJson(b.sourceRef())),
                CanonicalJson.e("sourceSignature", descriptorText(b.sourceSignature())),
                CanonicalJson.e("targetSignature", descriptorText(b.targetSignature())),
                CanonicalJson.e("type", CanonicalJson.str("adapter")));
            case FunctionExecutionBinding.HostFunction b -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(b.descriptor())),
                CanonicalJson.e("exportName", CanonicalJson.str(b.exportName())),
                CanonicalJson.e("hostModuleId", semanticIdJson(b.hostModuleId())),
                CanonicalJson.e("type", CanonicalJson.str("hostFunction")));
            case FunctionExecutionBinding.HostFunctionValue b -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(b.descriptor())),
                CanonicalJson.e("hostModuleId", semanticIdJson(b.hostModuleId())),
                CanonicalJson.e("materializingBoundaryOpId",
                    semanticIdJson(b.materializingBoundaryOpId())),
                CanonicalJson.e("type", CanonicalJson.str("hostFunctionValue")));
            case FunctionExecutionBinding.ExternalFunction b -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(b.descriptor())),
                CanonicalJson.e("executionOwner", CanonicalJson.str(b.executionOwner().name())),
                CanonicalJson.e("exportName", CanonicalJson.str(b.exportName())),
                CanonicalJson.e("moduleId", semanticIdJson(b.moduleId())),
                CanonicalJson.e("type", CanonicalJson.str("externalFunction")));
            case FunctionExecutionBinding.IntrinsicFunction b -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(b.descriptor())),
                CanonicalJson.e("intrinsicKind", CanonicalJson.str(b.kind().name())),
                CanonicalJson.e("type", CanonicalJson.str("intrinsicFunction")));
        };
    }

    /** Renders a call callee reference as its pinned discriminated object. */
    public static CanonicalJson.Value calleeJson(KindPayload.CallCallee callee) {
        Objects.requireNonNull(callee, "callee must not be null");
        return switch (callee) {
            case KindPayload.CallCallee.Static s -> CanonicalJson.obj(
                CanonicalJson.e("binding", bindingJson(s.binding())),
                CanonicalJson.e("type", CanonicalJson.str("static")));
            case KindPayload.CallCallee.Indirect i -> CanonicalJson.obj(
                CanonicalJson.e("callee", semanticIdJson(i.callee())),
                CanonicalJson.e("type", CanonicalJson.str("indirect")));
            case KindPayload.CallCallee.Dynamic d -> CanonicalJson.obj(
                CanonicalJson.e("callee", semanticIdJson(d.callee())),
                CanonicalJson.e("type", CanonicalJson.str("dynamic")));
        };
    }

    /** Renders the dynamic return-boundary set as its pinned three-entry object. */
    public static CanonicalJson.Value dynamicReturnBoundaryJson(
            KindPayload.DynamicReturnBoundary boundary) {
        Objects.requireNonNull(boundary, "boundary must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("dealBodyBoundaryOpId",
                semanticIdJson(boundary.dealBodyBoundaryOpId())),
            CanonicalJson.e("externalBoundaryOpId",
                semanticIdJson(boundary.externalBoundaryOpId())),
            CanonicalJson.e("hostBoundaryOpId", semanticIdJson(boundary.hostBoundaryOpId())));
    }

    /** Renders an adapter source reference as its pinned discriminated object. */
    public static CanonicalJson.Value sourceRefJson(AdaptSourceRef sourceRef) {
        Objects.requireNonNull(sourceRef, "sourceRef must not be null");
        return switch (sourceRef) {
            case AdaptSourceRef.SharedCell s -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(s.binding())),
                CanonicalJson.e("generation", idValue(s.generation(), "generation")),
                CanonicalJson.e("type", CanonicalJson.str("sharedCell")));
            case AdaptSourceRef.Thunk t -> CanonicalJson.obj(
                CanonicalJson.e("blockId", semanticIdJson(t.blockId())),
                CanonicalJson.e("capturedBindings", CanonicalJson.arr(
                    t.capturedBindings().stream().map(ContractSnapshotCanonicalizer::bindingGenerationJson).toList())),
                CanonicalJson.e("type", CanonicalJson.str("thunk")));
            case AdaptSourceRef.Value v -> CanonicalJson.obj(
                CanonicalJson.e("type", CanonicalJson.str("value")),
                CanonicalJson.e("value", semanticIdJson(v.value())));
        };
    }

    /** Renders a binding generation reference. */
    public static CanonicalJson.Value bindingGenerationJson(BindingGeneration generation) {
        Objects.requireNonNull(generation, "generation must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("binding", semanticIdJson(generation.binding())),
            CanonicalJson.e("generation", idValue(generation.generation(), "generation")));
    }

    /** Renders a binding immutability proof. */
    public static CanonicalJson.Value immutabilityProofJson(BindingImmutabilityProof proof) {
        Objects.requireNonNull(proof, "proof must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("binding", semanticIdJson(proof.binding())),
            CanonicalJson.e("generation", idValue(proof.generation(), "generation")));
    }

    /** Renders an external async-linkage record. */
    public static CanonicalJson.Value externalAsyncLinkJson(ExternalAsyncLink link) {
        Objects.requireNonNull(link, "link must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("calleeModuleId", semanticIdJson(link.calleeModuleId())),
            CanonicalJson.e("calleeTokenId", semanticIdJson(link.calleeTokenId())),
            CanonicalJson.e("exportName", CanonicalJson.str(link.exportName())));
    }

    /** Renders a class layout. */
    public static CanonicalJson.Value layoutJson(ClassLayout layout) {
        Objects.requireNonNull(layout, "layout must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("classId", semanticIdJson(layout.classId())),
            CanonicalJson.e("fields", CanonicalJson.arr(
                layout.fields().stream().map(ContractSnapshotCanonicalizer::fieldLayoutJson).toList())));
    }

    /** Renders one class field layout entry. */
    public static CanonicalJson.Value fieldLayoutJson(ClassLayout.FieldLayout field) {
        Objects.requireNonNull(field, "field must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("defaultOwner", CanonicalJson.str(field.defaultOwner().name())),
            CanonicalJson.e("descriptor", descriptorText(field.descriptor())),
            CanonicalJson.e("name", CanonicalJson.str(field.name())),
            CanonicalJson.e("required", CanonicalJson.bool(field.required())));
    }

    /** Renders one {@code TABLE_NEW} entry. */
    public static CanonicalJson.Value tableEntryJson(KindPayload.TableEntry entry) {
        Objects.requireNonNull(entry, "entry must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("key", CanonicalJson.str(entry.key())),
            CanonicalJson.e("value", semanticIdJson(entry.value())));
    }

    /** Renders one {@code CLASS_NEW} provided field. */
    public static CanonicalJson.Value providedFieldJson(KindPayload.ProvidedField field) {
        Objects.requireNonNull(field, "field must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("name", CanonicalJson.str(field.name())),
            CanonicalJson.e("valueOpId", semanticIdJson(field.valueOpId())));
    }

    /** Renders one {@code CLASS_NEW} field boundary. */
    public static CanonicalJson.Value fieldBoundaryJson(KindPayload.FieldBoundary boundary) {
        Objects.requireNonNull(boundary, "boundary must not be null");
        return CanonicalJson.obj(
            CanonicalJson.e("boundaryOpId", semanticIdJson(boundary.boundaryOpId())),
            CanonicalJson.e("field", CanonicalJson.str(boundary.field())),
            CanonicalJson.e("kind", CanonicalJson.str(boundary.kind().name())));
    }

    /** Renders a closed selector as its raw enum name. */
    public static String selectorName(ClosedSelector selector) {
        Objects.requireNonNull(selector, "selector must not be null");
        if (selector instanceof UnarySelector u) {
            return u.name();
        }
        if (selector instanceof BinarySelector b) {
            return b.name();
        }
        if (selector instanceof StdlibFunctionId s) {
            return s.name();
        }
        throw new IllegalArgumentException("unknown selector: " + selector.getClass());
    }

    private static CanonicalJson.Int idValue(long id, String what) {
        if (id > Integer.MAX_VALUE) {
            throw new IllegalArgumentException(
                what + " " + id + " exceeds the canonical JSON signed32 integer range");
        }
        return CanonicalJson.intValue((int) id);
    }


    // =========================================================================
    // Closed kind-payload shapes (one JSON object per SemanticOpKind)
    // =========================================================================

    /**
     * Renders the closed kind payload as its pinned JSON object: one
     * object per {@link SemanticOpKind} with the record component names as
     * keys, enum values as names, descriptors as canonical spec text,
     * semantic IDs as discriminated objects, and optional components as
     * explicit nulls. The single production payload mapping — the dumper
     * and validator consume it through this component only.
     *
     * @param payload the payload; non-null
     * @return the pinned JSON object
     */
    public static CanonicalJson.Value payloadJson(KindPayload payload) {
        Objects.requireNonNull(payload, "payload must not be null");
        return switch (payload) {
            case KindPayload.ConstPayload p -> CanonicalJson.obj(
                CanonicalJson.e("value", scalarJson(p.value())));
            case KindPayload.UnaryPayload p -> CanonicalJson.obj(
                CanonicalJson.e("selector", CanonicalJson.str(p.selector().name())));
            case KindPayload.BinaryPayload p -> CanonicalJson.obj(
                CanonicalJson.e("innerDescriptor", p.innerDescriptor() == null
                    ? CanonicalJson.nullValue() : descriptorText(p.innerDescriptor())),
                CanonicalJson.e("selector", CanonicalJson.str(p.selector().name())),
                CanonicalJson.e("side", p.side() == null
                    ? CanonicalJson.nullValue() : CanonicalJson.str(p.side().name())));
            case KindPayload.StringConcatPayload p -> CanonicalJson.obj(
                CanonicalJson.e("fragments", CanonicalJson.arr(
                    p.fragments().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())));
            case KindPayload.ArrayNewPayload p -> CanonicalJson.obj(
                CanonicalJson.e("elementBoundaryOpIds", CanonicalJson.arr(
                    p.elementBoundaryOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("elementDescriptor", descriptorText(p.elementDescriptor())),
                CanonicalJson.e("values", CanonicalJson.arr(
                    p.values().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())));
            case KindPayload.TableNewPayload p -> CanonicalJson.obj(
                CanonicalJson.e("entries", CanonicalJson.arr(
                    p.entries().stream().map(ContractSnapshotCanonicalizer::tableEntryJson).toList())));
            case KindPayload.ArrayLengthPayload p -> CanonicalJson.obj(
                CanonicalJson.e("arrayValue", semanticIdJson(p.arrayValue())));
            case KindPayload.MemberReadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("key", CanonicalJson.str(p.key())),
                CanonicalJson.e("table", semanticIdJson(p.table())));
            case KindPayload.MemberWritePayload p -> CanonicalJson.obj(
                CanonicalJson.e("key", CanonicalJson.str(p.key())),
                CanonicalJson.e("table", semanticIdJson(p.table())),
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.MemberDeletePayload p -> CanonicalJson.obj(
                CanonicalJson.e("key", CanonicalJson.str(p.key())),
                CanonicalJson.e("table", semanticIdJson(p.table())));
            case KindPayload.IndexNormalizePayload p -> CanonicalJson.obj(
                CanonicalJson.e("currentLength", semanticIdJson(p.currentLength())),
                CanonicalJson.e("mode", CanonicalJson.str(p.mode().name())),
                CanonicalJson.e("rawKey", semanticIdJson(p.rawKey())));
            case KindPayload.IndexReadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("container", semanticIdJson(p.container())),
                CanonicalJson.e("elementBoundaryOpId", semanticIdJson(p.elementBoundaryOpId())),
                CanonicalJson.e("slot", semanticIdJson(p.slot())));
            case KindPayload.IndexWritePayload p -> CanonicalJson.obj(
                CanonicalJson.e("container", semanticIdJson(p.container())),
                CanonicalJson.e("slot", semanticIdJson(p.slot())),
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.IndexDeletePayload p -> CanonicalJson.obj(
                CanonicalJson.e("container", semanticIdJson(p.container())),
                CanonicalJson.e("slot", semanticIdJson(p.slot())));
            case KindPayload.OptionalReadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(p.descriptor())),
                CanonicalJson.e("present", CanonicalJson.bool(p.present())),
                CanonicalJson.e("value", p.value() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.value())));
            case KindPayload.HasFieldPayload p -> CanonicalJson.obj(
                CanonicalJson.e("key", CanonicalJson.str(p.key())),
                CanonicalJson.e("receiver", semanticIdJson(p.receiver())));
            case KindPayload.BoundaryPayload p -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(p.descriptor())),
                CanonicalJson.e("input", semanticIdJson(p.input())),
                CanonicalJson.e("kind", CanonicalJson.str(p.kind().name())),
                CanonicalJson.e("realization", realizationJson(p.realization())));
            case KindPayload.BindingAllocPayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(p.binding())),
                CanonicalJson.e("cellKind", CanonicalJson.str(p.cellKind().name())),
                CanonicalJson.e("generation", idValue(p.generation(), "generation")),
                CanonicalJson.e("mutable", CanonicalJson.bool(p.mutable())),
                CanonicalJson.e("scope", semanticIdJson(p.scope())));
            case KindPayload.BindingInitPayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(p.binding())),
                CanonicalJson.e("generation", idValue(p.generation(), "generation")),
                CanonicalJson.e("value", p.value() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.value())));
            case KindPayload.BindingLoadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(p.binding())),
                CanonicalJson.e("generation", idValue(p.generation(), "generation")));
            case KindPayload.BindingStorePayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(p.binding())),
                CanonicalJson.e("generation", idValue(p.generation(), "generation")),
                CanonicalJson.e("value", p.value() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.value())));
            case KindPayload.RecursiveGroupInitPayload p -> CanonicalJson.obj(
                CanonicalJson.e("bindings", CanonicalJson.arr(
                    p.bindings().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("functions", CanonicalJson.arr(
                    p.functions().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())));
            case KindPayload.ClosureNewPayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", bindingJson(p.binding())),
                CanonicalJson.e("captures", CanonicalJson.arr(
                    p.captures().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("function", semanticIdJson(p.function())),
                CanonicalJson.e("signature", descriptorText(p.signature())));
            case KindPayload.FunctionAdaptPayload p -> CanonicalJson.obj(
                CanonicalJson.e("mode", CanonicalJson.str(p.mode().name())),
                CanonicalJson.e("proof", p.proof() == null
                    ? CanonicalJson.nullValue() : immutabilityProofJson(p.proof())),
                CanonicalJson.e("source", sourceRefJson(p.source())),
                CanonicalJson.e("sourceSignature", descriptorText(p.sourceSignature())),
                CanonicalJson.e("targetSignature", descriptorText(p.targetSignature())));
            case KindPayload.AssignPayload p -> CanonicalJson.obj(
                CanonicalJson.e("childOps", CanonicalJson.arr(
                    p.childOps().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("targetKind", CanonicalJson.str(p.targetKind().name())));
            case KindPayload.DeletePayload p -> CanonicalJson.obj(
                CanonicalJson.e("childOps", CanonicalJson.arr(
                    p.childOps().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("targetKind", CanonicalJson.str(p.targetKind().name())));
            case KindPayload.CallPayload p -> CanonicalJson.obj(
                CanonicalJson.e("bodyBlock", p.bodyBlock() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.bodyBlock())),
                CanonicalJson.e("callee", calleeJson(p.callee())),
                CanonicalJson.e("dynamicReturnBoundary", p.dynamicReturnBoundary() == null
                    ? CanonicalJson.nullValue() : dynamicReturnBoundaryJson(p.dynamicReturnBoundary())),
                CanonicalJson.e("externalEntryRef", p.externalEntryRef() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.externalEntryRef())),
                CanonicalJson.e("mode", CanonicalJson.str(p.mode().name())),
                CanonicalJson.e("parameterBoundaryOpIds", CanonicalJson.arr(
                    p.parameterBoundaryOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("returnBoundaryOpId", p.returnBoundaryOpId() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.returnBoundaryOpId())),
                CanonicalJson.e("signature", descriptorText(p.signature())));
            case KindPayload.ExternalEntryPayload p -> CanonicalJson.obj(
                CanonicalJson.e("async", CanonicalJson.bool(p.async())),
                CanonicalJson.e("completionDescriptor", p.completionDescriptor() == null
                    ? CanonicalJson.nullValue() : descriptorText(p.completionDescriptor())),
                CanonicalJson.e("exportName", CanonicalJson.str(p.exportName())),
                CanonicalJson.e("function", semanticIdJson(p.function())),
                CanonicalJson.e("returnBoundaryOpId", semanticIdJson(p.returnBoundaryOpId())),
                CanonicalJson.e("signature", descriptorText(p.signature())));
            case KindPayload.CallbackInvokePayload p -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(p.descriptor())),
                CanonicalJson.e("function", semanticIdJson(p.function())),
                CanonicalJson.e("parameterBoundaryOpIds", CanonicalJson.arr(
                    p.parameterBoundaryOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("returnBoundaryOpId", semanticIdJson(p.returnBoundaryOpId())));
            case KindPayload.IntrinsicCallPayload p -> CanonicalJson.obj(
                CanonicalJson.e("input", semanticIdJson(p.input())),
                CanonicalJson.e("kind", CanonicalJson.str(p.kind().name())));
            case KindPayload.StdlibCallPayload p -> CanonicalJson.obj(
                CanonicalJson.e("args", CanonicalJson.arr(
                    p.args().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("effectCapability", CanonicalJson.str(p.effectCapability().name())),
                CanonicalJson.e("function", CanonicalJson.str(p.function().name())));
            case KindPayload.AsyncStartPayload p -> CanonicalJson.obj(
                CanonicalJson.e("callee", calleeJson(p.callee())),
                CanonicalJson.e("completionDescriptor", descriptorText(p.completionDescriptor())),
                CanonicalJson.e("externalAsyncLink", p.externalAsyncLink() == null
                    ? CanonicalJson.nullValue() : externalAsyncLinkJson(p.externalAsyncLink())),
                CanonicalJson.e("hostOperationLabel", p.hostOperationLabel() == null
                    ? CanonicalJson.nullValue() : CanonicalJson.str(p.hostOperationLabel())),
                CanonicalJson.e("parameterBoundaryMode",
                    CanonicalJson.str(p.parameterBoundaryMode().name())),
                CanonicalJson.e("parameterBoundaryOpIds", CanonicalJson.arr(
                    p.parameterBoundaryOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("returnBoundaryOpId", p.returnBoundaryOpId() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.returnBoundaryOpId())),
                CanonicalJson.e("source", CanonicalJson.str(p.source().name())));
            case KindPayload.AwaitPayload p -> CanonicalJson.obj(
                CanonicalJson.e("completionBoundaryOpId", semanticIdJson(p.completionBoundaryOpId())),
                CanonicalJson.e("completionDescriptor", descriptorText(p.completionDescriptor())),
                CanonicalJson.e("token", semanticIdJson(p.token())));
            case KindPayload.BranchPayload p -> CanonicalJson.obj(
                CanonicalJson.e("alternateBlock", p.alternateBlock() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.alternateBlock())),
                CanonicalJson.e("condition", semanticIdJson(p.condition())),
                CanonicalJson.e("selectedBlock", semanticIdJson(p.selectedBlock())),
                CanonicalJson.e("selector", CanonicalJson.str(p.selector().name())));
            case KindPayload.LoopPayload p -> CanonicalJson.obj(
                CanonicalJson.e("bodyBlock", semanticIdJson(p.bodyBlock())),
                CanonicalJson.e("condition", semanticIdJson(p.condition())),
                CanonicalJson.e("initBlock", p.initBlock() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.initBlock())),
                CanonicalJson.e("selector", CanonicalJson.str(p.selector().name())),
                CanonicalJson.e("updateBlock", p.updateBlock() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.updateBlock())));
            case KindPayload.ForEachPayload p -> CanonicalJson.obj(
                CanonicalJson.e("binding", semanticIdJson(p.binding())),
                CanonicalJson.e("body", semanticIdJson(p.body())),
                CanonicalJson.e("generation", idValue(p.generation(), "generation")),
                CanonicalJson.e("iterable", semanticIdJson(p.iterable())),
                CanonicalJson.e("mode", CanonicalJson.str(p.mode().name())));
            case KindPayload.TryCatchPayload p -> CanonicalJson.obj(
                CanonicalJson.e("catchBinding", semanticIdJson(p.catchBinding())),
                CanonicalJson.e("catchBlock", semanticIdJson(p.catchBlock())),
                CanonicalJson.e("tryBlock", semanticIdJson(p.tryBlock())));
            case KindPayload.ThrowPayload p -> CanonicalJson.obj(
                CanonicalJson.e("errorValue", semanticIdJson(p.errorValue())));
            case KindPayload.ReturnPayload p -> CanonicalJson.obj(
                CanonicalJson.e("enclosingInvocationOpId", semanticIdJson(p.enclosingInvocationOpId())),
                CanonicalJson.e("function", semanticIdJson(p.function())),
                CanonicalJson.e("returnBoundaryOpId", semanticIdJson(p.returnBoundaryOpId())),
                CanonicalJson.e("value", p.value() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.value())));
            case KindPayload.BreakPayload p -> CanonicalJson.obj(
                CanonicalJson.e("loopId", semanticIdJson(p.loopId())));
            case KindPayload.ContinuePayload p -> CanonicalJson.obj(
                CanonicalJson.e("loopId", semanticIdJson(p.loopId())));
            case KindPayload.DiscardPayload p -> CanonicalJson.obj(
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.ClassDefaultPayload p -> CanonicalJson.obj(
                CanonicalJson.e("classId", semanticIdJson(p.classId())),
                CanonicalJson.e("defaultBlock", semanticIdJson(p.defaultBlock())),
                CanonicalJson.e("field", CanonicalJson.str(p.field())));
            case KindPayload.ClassNewPayload p -> CanonicalJson.obj(
                CanonicalJson.e("classDefaultOpIds", CanonicalJson.arr(
                    p.classDefaultOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("classFactoryRef", p.classFactoryRef() == null
                    ? CanonicalJson.nullValue() : semanticIdJson(p.classFactoryRef())),
                CanonicalJson.e("classId", semanticIdJson(p.classId())),
                CanonicalJson.e("defaultOwner", CanonicalJson.str(p.defaultOwner().name())),
                CanonicalJson.e("fieldBoundaries", CanonicalJson.arr(
                    p.fieldBoundaries().stream().map(ContractSnapshotCanonicalizer::fieldBoundaryJson).toList())),
                CanonicalJson.e("layout", layoutJson(p.layout())),
                CanonicalJson.e("providedFields", CanonicalJson.arr(
                    p.providedFields().stream().map(ContractSnapshotCanonicalizer::providedFieldJson).toList())));
            case KindPayload.ClassFactoryPayload p -> CanonicalJson.obj(
                CanonicalJson.e("callerOpRef", semanticIdJson(p.callerOpRef())),
                CanonicalJson.e("classDefaultOpIds", CanonicalJson.arr(
                    p.classDefaultOpIds().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("classId", semanticIdJson(p.classId())));
            case KindPayload.FieldReadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("classId", semanticIdJson(p.classId())),
                CanonicalJson.e("classValue", semanticIdJson(p.classValue())),
                CanonicalJson.e("field", CanonicalJson.str(p.field())));
            case KindPayload.FieldWritePayload p -> CanonicalJson.obj(
                CanonicalJson.e("classId", semanticIdJson(p.classId())),
                CanonicalJson.e("classValue", semanticIdJson(p.classValue())),
                CanonicalJson.e("field", CanonicalJson.str(p.field())),
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.FieldDeletePayload p -> CanonicalJson.obj(
                CanonicalJson.e("classId", semanticIdJson(p.classId())),
                CanonicalJson.e("classValue", semanticIdJson(p.classValue())),
                CanonicalJson.e("field", CanonicalJson.str(p.field())));
            case KindPayload.JsonFromClassPayload p -> CanonicalJson.obj(
                CanonicalJson.e("jsonString", semanticIdJson(p.jsonString())),
                CanonicalJson.e("layout", layoutJson(p.layout())));
            case KindPayload.JsonToClassPayload p -> CanonicalJson.obj(
                CanonicalJson.e("classValue", semanticIdJson(p.classValue())),
                CanonicalJson.e("layout", layoutJson(p.layout())));
            case KindPayload.ModuleInitPayload p -> CanonicalJson.obj(
                CanonicalJson.e("imports", CanonicalJson.arr(
                    p.imports().stream().map(ContractSnapshotCanonicalizer::semanticIdJson).toList())),
                CanonicalJson.e("initBlock", semanticIdJson(p.initBlock())),
                CanonicalJson.e("module", semanticIdJson(p.module())));
            case KindPayload.ModuleImportPayload p -> CanonicalJson.obj(
                CanonicalJson.e("kind", CanonicalJson.str(p.kind().name())),
                CanonicalJson.e("rawSpecifier", CanonicalJson.str(p.rawSpecifier())),
                CanonicalJson.e("resolvedModule", semanticIdJson(p.resolvedModule())));
            case KindPayload.ExportReadPayload p -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(p.descriptor())),
                CanonicalJson.e("module", semanticIdJson(p.module())),
                CanonicalJson.e("name", CanonicalJson.str(p.name())),
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.ExportPublishPayload p -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", descriptorText(p.descriptor())),
                CanonicalJson.e("module", semanticIdJson(p.module())),
                CanonicalJson.e("name", CanonicalJson.str(p.name())),
                CanonicalJson.e("value", semanticIdJson(p.value())));
            case KindPayload.EntryInvokePayload p -> CanonicalJson.obj(
                CanonicalJson.e("mainFunction", semanticIdJson(p.mainFunction())),
                CanonicalJson.e("module", semanticIdJson(p.module())));
        };
    }

    // =========================================================================
    // Unit/project validation text protocol (T6's validator text surface)
    // =========================================================================

    /**
     * The parsed project text of the validator's text surface:
     * {@code {semanticProfile, entryModule, modules}} — the project-level
     * positions carried as raw strings.
     *
     * @param semanticProfile the raw project semantic-profile name; non-null
     * @param entryModule     the entry module path; non-null
     * @param modules         the parsed raw units in serialized order; non-null
     */
    public record ParsedProject(String semanticProfile, String entryModule,
                                List<RawUnit> modules) {

        public ParsedProject {
            Objects.requireNonNull(semanticProfile, "semanticProfile must not be null");
            Objects.requireNonNull(entryModule, "entryModule must not be null");
            modules = List.copyOf(Objects.requireNonNull(modules, "modules must not be null"));
        }
    }

    /**
     * Parses canonical validation text through the single parser. No
     * framing, closed-enum, or profile validation happens here beyond the
     * JSON value model itself — those are the validator's rules (T6).
     *
     * @param text the canonical JSON text; non-null
     * @return the parsed value tree
     * @throws SemanticIrTextDecodeException on malformed JSON (the single
     *         parser's transport-level rejection)
     */
    public static CanonicalJson.Value parseValidationText(String text) {
        return CanonicalJson.parse(text);
    }

    /**
     * Decodes a unit text object into the raw unit record: the pinned
     * field names and JSON value types are mapped into
     * {@link RawUnit}; every closed enum position (profile, capabilities,
     * construct names, op kinds, payload leaves, bindings, tokens) is
     * carried as a raw string — no enum conversion at parse time, so
     * out-of-set and reserved names survive byte-intact and reach the
     * validator's rule checks.
     *
     * @param obj the unit text object; non-null
     * @return the raw unit
     * @throws SemanticIrTextDecodeException on a pinned framing/
     *         field/value-type/version mismatch (transport-level, never
     *         E6005)
     */
    public static RawUnit parseUnit(CanonicalJson.Obj obj) {
        checkKeys(obj, "formatVersion", "semanticProfile", "moduleId", "interfaceHash",
            "loweringContextHash", "requiredCapabilities", "constructCoverage",
            "functionBindings", "ops");
        String formatVersion = requireString(obj, "formatVersion");
        if (!LoweredModuleUnit.FORMAT_VERSION.equals(formatVersion)) {
            throw new SemanticIrTextDecodeException(
                "formatVersion mismatch: expected \"" + LoweredModuleUnit.FORMAT_VERSION
                    + "\", got \"" + formatVersion + "\"");
        }
        String modulePath = requireString(obj, "moduleId");
        try {
            new ModuleId(modulePath);
        } catch (IllegalArgumentException e) {
            throw new SemanticIrTextDecodeException("invalid moduleId \"" + modulePath + "\"");
        }
        String semanticProfile = requireString(obj, "semanticProfile");
        String interfaceHash = requireString(obj, "interfaceHash");
        String loweringContextHash = requireString(obj, "loweringContextHash");

        List<String> capabilities = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(obj, "requiredCapabilities").items()) {
            capabilities.add(requireStringValue(item, "requiredCapabilities entry"));
        }
        List<RawCoverage> coverage = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(obj, "constructCoverage").items()) {
            if (!(item instanceof CanonicalJson.Obj row)) {
                throw new SemanticIrTextDecodeException(
                    "constructCoverage entries must be objects, got " + jsonKindName(item));
            }
            checkKeys(row, "construct", "opKinds");
            List<String> kinds = new ArrayList<>();
            for (CanonicalJson.Value kind : requireArray(row, "opKinds").items()) {
                kinds.add(requireStringValue(kind, "constructCoverage opKinds entry"));
            }
            coverage.add(new RawCoverage(requireString(row, "construct"), kinds));
        }
        List<RawBinding> bindings = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(obj, "functionBindings").items()) {
            if (!(item instanceof CanonicalJson.Obj entry)) {
                throw new SemanticIrTextDecodeException(
                    "functionBindings entries must be objects, got " + jsonKindName(item));
            }
            checkKeys(entry, "allocationId", "binding");
            long allocationId = requireInt(entry, "allocationId");
            CanonicalJson.Value bindingValue = entryValue(entry, "binding");
            if (!(bindingValue instanceof CanonicalJson.Obj binding)) {
                throw new SemanticIrTextDecodeException(
                    "functionBindings \"binding\" must be an object, got "
                        + jsonKindName(bindingValue));
            }
            bindings.add(bindingFromText(allocationId, binding));
        }
        List<RawOp> ops = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(obj, "ops").items()) {
            if (!(item instanceof CanonicalJson.Obj op)) {
                throw new SemanticIrTextDecodeException(
                    "ops entries must be objects, got " + jsonKindName(item));
            }
            ops.add(opFromText(op));
        }
        return new RawUnit(modulePath, semanticProfile, interfaceHash, loweringContextHash,
            capabilities, coverage, bindings, ops);
    }

    /**
     * Decodes a project text object ({@code {semanticProfile, entryModule,
     * modules}}) into its raw records with the entry-module framing check.
     *
     * @param obj the project text object; non-null
     * @return the parsed project
     * @throws SemanticIrTextDecodeException on a framing mismatch
     */
    public static ParsedProject parseProject(CanonicalJson.Obj obj) {
        checkKeys(obj, "semanticProfile", "entryModule", "modules");
        String projectProfile = requireString(obj, "semanticProfile");
        String entryModule = requireString(obj, "entryModule");
        CanonicalJson.Arr modulesArr = requireArray(obj, "modules");
        List<RawUnit> modules = new ArrayList<>();
        for (int i = 0; i < modulesArr.items().size(); i++) {
            CanonicalJson.Value item = modulesArr.items().get(i);
            if (!(item instanceof CanonicalJson.Obj unitObj)) {
                throw new SemanticIrTextDecodeException(
                    "modules[" + i + "] must be a unit object, got " + jsonKindName(item));
            }
            modules.add(parseUnit(unitObj));
        }
        boolean hasEntry = false;
        for (RawUnit unit : modules) {
            if (entryModule.equals(unit.modulePath())) {
                hasEntry = true;
                break;
            }
        }
        if (!hasEntry) {
            throw new SemanticIrTextDecodeException(
                "entryModule \"" + entryModule + "\" must be present in the project modules");
        }
        return new ParsedProject(projectProfile, entryModule, modules);
    }

    /** Maps a raw unit onto the single canonical JSON value model (the text surface's transport). */
    public static CanonicalJson.Value toJson(RawUnit unit) {
        List<CanonicalJson.Value> capabilities = new ArrayList<>();
        for (String capability : unit.requiredCapabilities()) {
            capabilities.add(CanonicalJson.str(capability));
        }
        List<CanonicalJson.Value> coverage = new ArrayList<>();
        for (RawCoverage row : unit.coverage()) {
            List<CanonicalJson.Value> kinds = new ArrayList<>();
            for (String kind : row.opKinds()) {
                kinds.add(CanonicalJson.str(kind));
            }
            coverage.add(CanonicalJson.obj(
                CanonicalJson.e("construct", CanonicalJson.str(row.construct())),
                CanonicalJson.e("opKinds", CanonicalJson.arr(kinds))));
        }
        List<CanonicalJson.Value> bindings = new ArrayList<>();
        for (RawBinding binding : unit.bindings()) {
            bindings.add(CanonicalJson.obj(
                CanonicalJson.e("allocationId", CanonicalJson.intValue((int) binding.allocationId())),
                CanonicalJson.e("binding", bindingJson(binding))));
        }
        List<CanonicalJson.Value> ops = new ArrayList<>();
        for (RawOp op : unit.ops()) {
            ops.add(opJson(op));
        }
        return CanonicalJson.obj(
            CanonicalJson.e("formatVersion", CanonicalJson.str(LoweredModuleUnit.FORMAT_VERSION)),
            CanonicalJson.e("semanticProfile", CanonicalJson.str(unit.semanticProfile())),
            CanonicalJson.e("moduleId", CanonicalJson.str(unit.modulePath())),
            CanonicalJson.e("interfaceHash", CanonicalJson.str(unit.interfaceHash())),
            CanonicalJson.e("loweringContextHash", CanonicalJson.str(unit.loweringContextHash())),
            CanonicalJson.e("requiredCapabilities", CanonicalJson.arr(capabilities)),
            CanonicalJson.e("constructCoverage", CanonicalJson.arr(coverage)),
            CanonicalJson.e("functionBindings", CanonicalJson.arr(bindings)),
            CanonicalJson.e("ops", CanonicalJson.arr(ops)));
    }

    /** Maps an executable project onto the project text protocol value model. */
    public static CanonicalJson.Value toJson(ExecutableLoweredProject project) {
        List<CanonicalJson.Value> modules = new ArrayList<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            modules.add(toJson(RawUnit.fromTyped(unit)));
        }
        return CanonicalJson.obj(
            CanonicalJson.e("semanticProfile",
                CanonicalJson.str(project.semanticProfile().name())),
            CanonicalJson.e("entryModule", CanonicalJson.str(project.entryModule().path())),
            CanonicalJson.e("modules", CanonicalJson.arr(modules)));
    }

    /**
     * Recomputes the contract digest over the raw 8-field snapshot object
     * (R-DIGEST's recomputation): {@code SHA-256(canonical JSON bytes)} of
     * exactly the eight pinned snapshot fields.
     *
     * @param snapshot the raw 8-field snapshot object (no canonicalDigest); non-null
     * @return the lowercase 64-character hex digest
     */
    public static String recomputeSnapshotDigest(CanonicalJson.Obj snapshot) {
        return CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(snapshot));
    }

    private static CanonicalJson.Value bindingJson(RawBinding binding) {
        return switch (binding.shape()) {
            case "loweredBody" -> CanonicalJson.obj(
                CanonicalJson.e("type", CanonicalJson.str("loweredBody")));
            case "adapter" -> CanonicalJson.obj(
                CanonicalJson.e("captureMode", CanonicalJson.str(binding.captureMode())),
                CanonicalJson.e("targetSignature", CanonicalJson.str(binding.targetSignature())),
                CanonicalJson.e("type", CanonicalJson.str("adapter")));
            case "hostFunction" -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", CanonicalJson.str(binding.descriptor())),
                CanonicalJson.e("exportName", CanonicalJson.str(binding.exportName())),
                CanonicalJson.e("hostModuleId", moduleIdJson(binding.modulePath())),
                CanonicalJson.e("type", CanonicalJson.str("hostFunction")));
            case "hostFunctionValue" -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", CanonicalJson.str(binding.descriptor())),
                CanonicalJson.e("hostModuleId", moduleIdJson(binding.modulePath())),
                CanonicalJson.e("materializingBoundaryOpId", binding.materializingBoundaryOpId() == null
                    ? CanonicalJson.nullValue()
                    : semanticIdJson(binding.materializingBoundaryOpId())),
                CanonicalJson.e("type", CanonicalJson.str("hostFunctionValue")));
            case "externalFunction" -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", CanonicalJson.str(binding.descriptor())),
                CanonicalJson.e("executionOwner", CanonicalJson.str(binding.executionOwner())),
                CanonicalJson.e("exportName", CanonicalJson.str(binding.exportName())),
                CanonicalJson.e("moduleId", moduleIdJson(binding.modulePath())),
                CanonicalJson.e("type", CanonicalJson.str("externalFunction")));
            case "intrinsicFunction" -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", CanonicalJson.str(binding.descriptor())),
                CanonicalJson.e("intrinsicKind", CanonicalJson.str(binding.intrinsicKind())),
                CanonicalJson.e("type", CanonicalJson.str("intrinsicFunction")));
            default -> CanonicalJson.obj(
                CanonicalJson.e("type", CanonicalJson.str(binding.shape())));
        };
    }

    private static RawBinding bindingFromText(long allocationId, CanonicalJson.Obj binding) {
        String shape = requireString(binding, "type");
        String modulePath = null;
        String exportName = null;
        String executionOwner = null;
        String captureMode = null;
        String descriptor = null;
        String targetSignature = null;
        OpId materializingBoundaryOpId = null;
        String intrinsicKind = null;
        switch (shape) {
            case "loweredBody" -> {
                // functionId + blockId; no enum positions the rules consult.
            }
            case "adapter" -> {
                captureMode = requireString(binding, "captureMode");
                targetSignature = requireString(binding, "targetSignature");
            }
            case "hostFunction" -> {
                modulePath = modulePathOf(requireObject(binding, "hostModuleId"));
                exportName = requireString(binding, "exportName");
                descriptor = requireString(binding, "descriptor");
            }
            case "hostFunctionValue" -> {
                modulePath = modulePathOf(requireObject(binding, "hostModuleId"));
                descriptor = requireString(binding, "descriptor");
                CanonicalJson.Value materializing = entryValue(binding, "materializingBoundaryOpId");
                if (materializing instanceof CanonicalJson.Obj materializingObj) {
                    materializingBoundaryOpId = parseOpId(materializingObj);
                } else if (!(materializing instanceof CanonicalJson.Null)) {
                    throw new SemanticIrTextDecodeException(
                        "functionBindings \"materializingBoundaryOpId\" must be null or an "
                            + "op-id object, got " + jsonKindName(materializing));
                }
            }
            case "externalFunction" -> {
                modulePath = modulePathOf(requireObject(binding, "moduleId"));
                exportName = requireString(binding, "exportName");
                executionOwner = requireString(binding, "executionOwner");
                descriptor = requireString(binding, "descriptor");
            }
            case "intrinsicFunction" -> {
                descriptor = requireString(binding, "descriptor");
                intrinsicKind = requireString(binding, "intrinsicKind");
            }
            default -> {
                // An unknown binding shape tag is an R-ENUM position —
                // carry it through as the shape string.
            }
        }
        return new RawBinding(allocationId, shape, modulePath, exportName, executionOwner,
            captureMode, descriptor, targetSignature, materializingBoundaryOpId,
            intrinsicKind);
    }

    private static CanonicalJson.Value opJson(RawOp op) {
        List<CanonicalJson.Value> operands = new ArrayList<>();
        for (ValueId value : op.operands()) {
            operands.add(semanticIdJson(value));
        }
        List<CanonicalJson.Value> operandTypes = new ArrayList<>();
        for (String type : op.operandTypes()) {
            operandTypes.add(CanonicalJson.str(type));
        }
        CanonicalJson.Value result;
        if (op.resultValue() != null) {
            result = semanticIdJson(op.resultValue());
        } else if (op.resultToken() != null) {
            result = semanticIdJson(op.resultToken());
        } else {
            result = CanonicalJson.nullValue();
        }
        List<CanonicalJson.Entry> contractEntries = new ArrayList<>(op.snapshot().entries());
        contractEntries.add(CanonicalJson.e("canonicalDigest",
            CanonicalJson.str(op.canonicalDigest())));
        return CanonicalJson.obj(
            CanonicalJson.e("opId", semanticIdJson(op.opId())),
            CanonicalJson.e("kind", CanonicalJson.str(op.kind())),
            CanonicalJson.e("origin", originJson(op)),
            CanonicalJson.e("result", result),
            CanonicalJson.e("resultType", op.resultType() == null
                ? CanonicalJson.nullValue() : CanonicalJson.str(op.resultType())),
            CanonicalJson.e("operands", CanonicalJson.arr(operands)),
            CanonicalJson.e("operandTypes", CanonicalJson.arr(operandTypes)),
            CanonicalJson.e("payload", op.payload()),
            CanonicalJson.e("failurePolicy", CanonicalJson.str(op.failurePolicy())),
            CanonicalJson.e("contract", CanonicalJson.obj(contractEntries)));
    }

    private static CanonicalJson.Value originJson(RawOp op) {
        // The raw model carries the parent-op link only; the remaining
        // origin coordinates render as pinned neutral synthetic values
        // (the validation protocol does not consult them).
        return CanonicalJson.obj(
            CanonicalJson.e("sourceId", CanonicalJson.str("semantic-ir")),
            CanonicalJson.e("span", CanonicalJson.obj(
                CanonicalJson.e("file", CanonicalJson.str("semantic-ir")),
                CanonicalJson.e("startLine", CanonicalJson.intValue(1)),
                CanonicalJson.e("startColumn", CanonicalJson.intValue(1)),
                CanonicalJson.e("endLine", CanonicalJson.intValue(1)),
                CanonicalJson.e("endColumn", CanonicalJson.intValue(1)),
                CanonicalJson.e("startScalarOffset", CanonicalJson.intValue(-1)),
                CanonicalJson.e("endScalarOffset", CanonicalJson.intValue(-1)))),
            CanonicalJson.e("kind", CanonicalJson.str("SYNTHETIC")),
            CanonicalJson.e("anchorId", CanonicalJson.obj(
                CanonicalJson.e("id", CanonicalJson.intValue(0)),
                CanonicalJson.e("type", CanonicalJson.str("anchor")))),
            CanonicalJson.e("parentOpId", op.parentOpId() == null
                ? CanonicalJson.nullValue()
                : semanticIdJson(op.parentOpId())));
    }

    private static RawOp opFromText(CanonicalJson.Obj op) {
        checkKeys(op, "opId", "kind", "origin", "result", "resultType", "operands",
            "operandTypes", "payload", "failurePolicy", "contract");
        OpId opId = parseOpId(requireObject(op, "opId"));
        String kind = requireString(op, "kind");
        String failurePolicy = requireString(op, "failurePolicy");

        CanonicalJson.Obj origin = requireObject(op, "origin");
        checkKeys(origin, "sourceId", "span", "kind", "anchorId", "parentOpId");
        OpId parentOpId = null;
        CanonicalJson.Value parent = entryValue(origin, "parentOpId");
        if (!(parent instanceof CanonicalJson.Null)) {
            parentOpId = parseOpId(requireObjectValue(parent, "origin.parentOpId"));
        }

        ValueId resultValue = null;
        AsyncTokenId resultToken = null;
        CanonicalJson.Value result = entryValue(op, "result");
        if (result instanceof CanonicalJson.Obj resultObj) {
            switch (requireString(resultObj, "type")) {
                case "value" -> resultValue = parseValueId(resultObj);
                case "tokenCanonical", "tokenAlias" -> resultToken = parseToken(resultObj);
                default -> throw new SemanticIrTextDecodeException(
                    "op result type tag \"" + requireString(resultObj, "type")
                        + "\" is not a closed semantic-id shape");
            }
        } else if (!(result instanceof CanonicalJson.Null)) {
            throw new SemanticIrTextDecodeException(
                "op result must be null or a semantic-id object, got " + jsonKindName(result));
        }

        String resultType = null;
        CanonicalJson.Value resultTypeValue = entryValue(op, "resultType");
        if (resultTypeValue instanceof CanonicalJson.Str str) {
            resultType = str.value();
        } else if (!(resultTypeValue instanceof CanonicalJson.Null)) {
            throw new SemanticIrTextDecodeException(
                "op resultType must be null or a string, got " + jsonKindName(resultTypeValue));
        }

        List<ValueId> operands = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(op, "operands").items()) {
            operands.add(parseValueId(requireObjectValue(item, "operands entry")));
        }
        List<String> operandTypes = new ArrayList<>();
        for (CanonicalJson.Value item : requireArray(op, "operandTypes").items()) {
            operandTypes.add(requireStringValue(item, "operandTypes entry"));
        }
        if (operands.size() != operandTypes.size()) {
            throw new SemanticIrTextDecodeException(
                "operands (" + operands.size() + ") and operandTypes ("
                    + operandTypes.size() + ") must have the same length");
        }

        CanonicalJson.Obj payload = requireObject(op, "payload");

        CanonicalJson.Obj contract = requireObject(op, "contract");
        checkKeys(contract, "version", "opKind", "resultType", "operandTypes", "selector",
            "payload", "failurePolicy", "referencedSemanticIds", "canonicalDigest");
        if (requireInt(contract, "version") != OperationContractSnapshot.VERSION) {
            throw new SemanticIrTextDecodeException(
                "contract version mismatch: expected " + OperationContractSnapshot.VERSION);
        }
        String canonicalDigest = requireString(contract, "canonicalDigest");
        List<CanonicalJson.Entry> snapshotEntries = new ArrayList<>();
        for (CanonicalJson.Entry entry : contract.entries()) {
            if (!"canonicalDigest".equals(entry.key())) {
                snapshotEntries.add(entry);
            }
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(snapshotEntries);
        String selector = null;
        CanonicalJson.Value selectorValue = entryValue(snapshot, "selector");
        if (selectorValue instanceof CanonicalJson.Str str) {
            selector = str.value();
        } else if (!(selectorValue instanceof CanonicalJson.Null)) {
            throw new SemanticIrTextDecodeException(
                "contract selector must be null or a string, got "
                    + jsonKindName(selectorValue));
        }
        return new RawOp(opId, kind, failurePolicy, parentOpId, resultValue, resultToken,
            resultType, operands, operandTypes, payload, selector, canonicalDigest, snapshot);
    }

    // =========================================================================
    // Text protocol framing helpers (pinned field sets, raw-string preservation)
    // =========================================================================

    /**
     * Enforces the pinned object framing: exactly the pinned field set —
     * every present key must be pinned and every pinned key must be
     * present. Any deviation is a transport-level decode failure.
     *
     * @param obj    the object; non-null
     * @param pinned the pinned field names; non-null
     */
    public static void checkKeys(CanonicalJson.Obj obj, String... pinned) {
        Set<String> set = new LinkedHashSet<>(List.of(pinned));
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (!set.contains(entry.key())) {
                throw new SemanticIrTextDecodeException(
                    "unknown field \"" + entry.key() + "\" (pinned field set is "
                        + List.of(pinned) + ")");
            }
        }
        for (String key : pinned) {
            if (!hasKey(obj, key)) {
                throw new SemanticIrTextDecodeException(
                    "missing field \"" + key + "\" (pinned field set is " + List.of(pinned) + ")");
            }
        }
    }

    /** True iff the object carries the given key. */
    public static boolean hasKey(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return true;
            }
        }
        return false;
    }

    /** The value of a pinned key (decode failure when absent). */
    public static CanonicalJson.Value entryValue(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        throw new SemanticIrTextDecodeException("missing field \"" + key + "\"");
    }

    /** The string value of a pinned key. */
    public static String requireString(CanonicalJson.Obj obj, String key) {
        return requireStringValue(entryValue(obj, key), key);
    }

    /** A string value or a decode failure. */
    public static String requireStringValue(CanonicalJson.Value value, String what) {
        if (value instanceof CanonicalJson.Str str) {
            return str.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + what + "\" field must be a string, got " + jsonKindName(value));
    }

    /** The signed32 integer value of a pinned key. */
    public static int requireInt(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = entryValue(obj, key);
        if (value instanceof CanonicalJson.Int i) {
            return i.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + key + "\" field must be a canonical signed32 integer, got "
                + jsonKindName(value));
    }

    /** The array value of a pinned key. */
    public static CanonicalJson.Arr requireArray(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = entryValue(obj, key);
        if (value instanceof CanonicalJson.Arr arr) {
            return arr;
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + key + "\" field must be an array, got " + jsonKindName(value));
    }

    /** The object value of a pinned key. */
    public static CanonicalJson.Obj requireObject(CanonicalJson.Obj obj, String key) {
        return requireObjectValue(entryValue(obj, key), key);
    }

    /** An object value or a decode failure. */
    public static CanonicalJson.Obj requireObjectValue(CanonicalJson.Value value, String what) {
        if (value instanceof CanonicalJson.Obj obj) {
            return obj;
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + what + "\" field must be an object, got " + jsonKindName(value));
    }

    /** The pinned module semantic-id object for a module path. */
    public static CanonicalJson.Value moduleIdJson(String modulePath) {
        return CanonicalJson.obj(
            CanonicalJson.e("path", CanonicalJson.str(modulePath)),
            CanonicalJson.e("type", CanonicalJson.str("module")));
    }

    /** The module path carried by a module semantic-id object. */
    public static String modulePathOf(CanonicalJson.Obj moduleIdObj) {
        return requireString(moduleIdObj, "path");
    }

    /** Parses an op semantic-id object. */
    public static OpId parseOpId(CanonicalJson.Obj obj) {
        String type = requireString(obj, "type");
        if (!"op".equals(type)) {
            throw new SemanticIrTextDecodeException(
                "expected an op semantic-id object, got type \"" + type + "\"");
        }
        return new OpId(new ModuleId(requireString(obj, "modulePath")), requireInt(obj, "id"));
    }

    /** Parses a value semantic-id object. */
    public static ValueId parseValueId(CanonicalJson.Obj obj) {
        String type = requireString(obj, "type");
        if (!"value".equals(type)) {
            throw new SemanticIrTextDecodeException(
                "expected a value semantic-id object, got type \"" + type + "\"");
        }
        return new ValueId(requireInt(obj, "id"));
    }

    /** Parses a token semantic-id object (recursive alias referents). */
    public static AsyncTokenId parseToken(CanonicalJson.Obj obj) {
        return switch (requireString(obj, "type")) {
            case "tokenCanonical" -> new AsyncTokenId.Canonical(requireInt(obj, "tokenId"),
                parseTokenOwner(requireString(obj, "owner")));
            case "tokenAlias" -> new AsyncTokenId.Alias(requireInt(obj, "tokenId"),
                parseToken(requireObject(obj, "referent")),
                parseLinkKind(requireString(obj, "linkKind")));
            default -> throw new SemanticIrTextDecodeException(
                "expected a token semantic-id object, got type \"" + requireString(obj, "type")
                    + "\"");
        };
    }

    private static AsyncTokenOwner parseTokenOwner(String raw) {
        try {
            return AsyncTokenOwner.valueOf(raw);
        } catch (IllegalArgumentException e) {
            throw new SemanticIrTextDecodeException(
                "unknown async token owner \"" + raw + "\"");
        }
    }

    private static AsyncLinkKind parseLinkKind(String raw) {
        try {
            return AsyncLinkKind.valueOf(raw);
        } catch (IllegalArgumentException e) {
            throw new SemanticIrTextDecodeException(
                "unknown async link kind \"" + raw + "\"");
        }
    }

    /** The raw string of a payload field, or {@code null} when absent or JSON null. */
    public static String optionalString(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = payloadValue(obj, key);
        if (value == null || value instanceof CanonicalJson.Null) {
            return null;
        }
        if (value instanceof CanonicalJson.Str str) {
            return str.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + key + "\" field must be a string or null, got " + jsonKindName(value));
    }

    /** The value of a payload field, or {@code null} when absent. */
    public static CanonicalJson.Value payloadValue(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }

    /** The boolean of a payload field (decode failure on absence/wrong type). */
    public static boolean isTrue(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = payloadValue(obj, key);
        if (value instanceof CanonicalJson.Bool bool) {
            return bool.value();
        }
        throw new SemanticIrTextDecodeException(
            "the \"" + key + "\" field must be a boolean, got " + jsonKindName(value));
    }

    /** Parses an ordered op-id list payload field (empty when absent). */
    public static List<OpId> parseOpIdList(CanonicalJson.Obj obj, String key) {
        List<OpId> result = new ArrayList<>();
        CanonicalJson.Value value = payloadValue(obj, key);
        if (value == null) {
            return result;
        }
        if (!(value instanceof CanonicalJson.Arr arr)) {
            throw new SemanticIrTextDecodeException(
                "the \"" + key + "\" field must be an array, got " + jsonKindName(value));
        }
        for (CanonicalJson.Value item : arr.items()) {
            result.add(parseOpId(requireObjectValue(item, key + " entry")));
        }
        return result;
    }

    /** Parses an optional op-id payload field ({@code null} when absent or JSON null). */
    public static OpId parseOptionalOpId(CanonicalJson.Obj obj, String key) {
        CanonicalJson.Value value = payloadValue(obj, key);
        if (value == null || value instanceof CanonicalJson.Null) {
            return null;
        }
        return parseOpId(requireObjectValue(value, key));
    }
}
