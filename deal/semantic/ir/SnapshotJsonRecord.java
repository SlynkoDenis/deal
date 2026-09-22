package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * The intermediate record produced by the single canonical JSON parser for
 * an {@link OperationContractSnapshot} text (schema S2; the versioned-text
 * transport T6's validator text surface consumes).
 *
 * <p>The parser maps the snapshot schema's pinned field names and JSON
 * value types into this record; every closed enum position carries a
 * <b>raw string</b> — {@code opKind}, {@code selector}, and
 * {@code failurePolicy} are never converted to enum members, so
 * out-of-set and reserved names (e.g. a reserved policy name such as
 * {@code EXTERNAL_PARAMETER}, a reserved boundary name, or any open
 * name) survive the parse byte-intact and reach
 * the validator's rule checks (R-ENUM/R-RESERVED-NAME). The parser performs
 * no closed-enum, reserved-name, policy, boundary-assignment, or profile
 * validation — those are the validator's rules (T6).</p>
 *
 * <p>{@code resultType} is the raw canonical descriptor text
 * ({@code RuntimeDescriptor.canonicalSpecText()}, e.g. {@code "int"},
 * {@code "(int,string)->boolean"}) or a raw internal sentinel name
 * ({@code "INTERNAL_MISSING"}/{@code "INTERNAL_ASYNC"}), or {@code null}
 * for the none slot (JSON {@code null}, distinct from the string
 * {@code "null"} — the null descriptor). {@code payload} stays a generic
 * canonical JSON object (the 55 closed kind shapes are validated by the
 * validator, not the parser), which preserves every leaf enum string and
 * every number byte-exactly for re-serialization.
 * {@code referencedSemanticIds} is the ordered list of generic JSON
 * objects (the semantic-ID shapes).</p>
 *
 * @param version               the parsed snapshot version; exactly
 *                              {@link OperationContractSnapshot#VERSION}
 *                              (any other value is a decode failure)
 * @param opKind                the raw operation-kind name; non-null
 * @param resultType            the raw result-type text, or {@code null}
 * @param operandTypes          the raw operand descriptor texts in order; non-null
 * @param selector              the raw selector name, or {@code null}
 * @param payload               the raw payload object; non-null
 * @param failurePolicy         the raw failure-policy name; non-null
 * @param referencedSemanticIds the ordered raw semantic-ID objects; non-null
 */
public record SnapshotJsonRecord(
    int version,
    String opKind,
    String resultType,
    List<String> operandTypes,
    String selector,
    CanonicalJson.Value payload,
    String failurePolicy,
    List<CanonicalJson.Value> referencedSemanticIds
) {

    public SnapshotJsonRecord(int version, String opKind, String resultType,
                             List<String> operandTypes, String selector,
                             CanonicalJson.Value payload, String failurePolicy,
                             List<CanonicalJson.Value> referencedSemanticIds) {
        this.version = version;
        this.opKind = Objects.requireNonNull(opKind, "opKind must not be null");
        this.resultType = resultType;
        this.operandTypes = List.copyOf(Objects.requireNonNull(operandTypes, "operandTypes must not be null"));
        this.selector = selector;
        this.payload = Objects.requireNonNull(payload, "payload must not be null");
        this.failurePolicy = Objects.requireNonNull(failurePolicy, "failurePolicy must not be null");
        this.referencedSemanticIds = List.copyOf(Objects.requireNonNull(referencedSemanticIds,
            "referencedSemanticIds must not be null"));
    }
}
