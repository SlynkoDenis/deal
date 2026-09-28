package deal.semantic.ir;

import deal.diagnostics.DiagnosticCode;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The structured boundary-failure projection of the closed failure-policy
 * rows (ISSUE-0233 design D3):
 * {@code {policy, code, message, expected, actual, metadata…, cause?}}.
 *
 * <p>The executor never selects message text. Every failure is built with
 * {@link #fromRow(FailurePolicyRow, int, String, String, Map,
 * BoundaryFailure)} from the pinned {@link FailureContractRegistry} row:
 * {@code policy} is the row's policy, {@code code} the row's fixed
 * DEAL-visible code, {@code message} the row's pinned template
 * instantiated with the canonical placeholders ({@code {expected}} from
 * {@code expected}, {@code {actual}} from {@code actual}, and the row's
 * metadata keys from {@code metadata}), {@code expected} the canonical
 * expected descriptor text (or the element descriptor for E8003), and
 * {@code actual} the canonical actual-kind token
 * ({@link ActualKind#canonicalToken}) or a pinned int-path refinement
 * ({@code NaN}, {@code infinity}, {@code non-integer number} — the spec
 * pinned check order has no canonical-kind member for them), and
 * {@code cause} the leaf failure where the row pins one (E8003). A
 * template whose placeholder stays unbound after instantiation fails
 * closed ({@link BoundaryExecutor.Defect}) — a broken projection never
 * renders.</p>
 */
public record BoundaryFailure(
    FailurePolicyId policy,
    DiagnosticCode code,
    String message,
    String expected,
    String actual,
    Map<String, String> metadata,
    BoundaryFailure cause
) {

    public BoundaryFailure {
        Objects.requireNonNull(policy, "policy must not be null");
        Objects.requireNonNull(code, "code must not be null");
        Objects.requireNonNull(message, "message must not be null");
        Objects.requireNonNull(metadata, "metadata must not be null");
        metadata = Collections.unmodifiableMap(new LinkedHashMap<>(metadata));
    }

    /**
     * Instantiates one pinned template of a registry row into a
     * {@code BoundaryFailure} — the only failure-construction surface the
     * executor uses. The message is the selected template with
     * {@code {expected}}, {@code {actual}}, and the metadata keys
     * substituted; no other content is ever added.
     *
     * @param row           the registry row owning the projection; non-null
     * @param templateIndex the row's template list position
     * @param expected      the canonical expected text, or {@code null} when
     *                      the template has no {@code {expected}}
     *                      placeholder
     * @param actual        the canonical actual text, or {@code null} when
     *                      the template has no {@code {actual}} placeholder
     * @param metadata      the row's pinned metadata values
     *                      ({@code index}, {@code oneBasedIndex},
     *                      {@code fieldPath}); may be empty, never null
     * @param cause         the leaf failure, or {@code null}
     * @return the structured failure whose {@code policy} is the row's
     * @throws NullPointerException     if {@code row} is null
     * @throws IndexOutOfBoundsException if {@code templateIndex} is outside
     *                                   the row's template list
     * @throws BoundaryExecutor.Defect  if a placeholder stays unbound after
     *                                  instantiation (fail closed)
     */
    public static BoundaryFailure fromRow(FailurePolicyRow row, int templateIndex,
                                          String expected, String actual,
                                          Map<String, String> metadata,
                                          BoundaryFailure cause) {
        Objects.requireNonNull(row, "row must not be null");
        List<String> templates = row.templates();
        if (templates.isEmpty() || templateIndex < 0 || templateIndex >= templates.size()) {
            throw new IllegalArgumentException(
                "template index " + templateIndex + " is outside the pinned templates of "
                    + row.policy());
        }
        String message = instantiate(templates.get(templateIndex), expected, actual, metadata);
        return new BoundaryFailure(row.policy(), row.code(), message, expected, actual,
            metadata == null ? new LinkedHashMap<>() : metadata, cause);
    }

    /**
     * Instantiates one pinned template of a registry row under an explicit
     * DEAL-visible code — the multi-code rows' second projection
     * ({@code BYTES_WRITE}: the bounds template carries the row's own
     * E8012, the value-range template the pinned E8013). The message is
     * the selected template, single-sourced from the registry row; only
     * the code differs.
     *
     * @param row           the registry row owning the projection; non-null
     * @param templateIndex the row's template list position
     * @param code          the pinned DEAL-visible code of this template; non-null
     * @param expected      the canonical expected text, or {@code null}
     * @param actual        the canonical actual text, or {@code null}
     * @param metadata      the row's pinned metadata values; may be empty, never null
     * @param cause         the leaf failure, or {@code null}
     * @return the structured failure whose {@code policy} is the row's
     * @throws NullPointerException     if {@code row} or {@code code} is null
     * @throws IndexOutOfBoundsException if {@code templateIndex} is outside
     *                                   the row's template list
     * @throws BoundaryExecutor.Defect  if a placeholder stays unbound after
     *                                  instantiation (fail closed)
     */
    public static BoundaryFailure fromRowWithCode(FailurePolicyRow row, int templateIndex,
                                                  DiagnosticCode code, String expected,
                                                  String actual,
                                                  Map<String, String> metadata,
                                                  BoundaryFailure cause) {
        Objects.requireNonNull(row, "row must not be null");
        Objects.requireNonNull(code, "code must not be null");
        List<String> templates = row.templates();
        if (templates.isEmpty() || templateIndex < 0 || templateIndex >= templates.size()) {
            throw new IllegalArgumentException(
                "template index " + templateIndex + " is outside the pinned templates of "
                    + row.policy());
        }
        String message = instantiate(templates.get(templateIndex), expected, actual, metadata);
        return new BoundaryFailure(row.policy(), code, message, expected, actual,
            metadata == null ? new LinkedHashMap<>() : metadata, cause);
    }

    /** Substitutes the canonical placeholders; an unbound placeholder is a defect. */
    private static String instantiate(String template, String expected, String actual,
                                      Map<String, String> metadata) {
        String message = template;
        if (expected != null) {
            message = message.replace("{expected}", expected);
        }
        if (actual != null) {
            message = message.replace("{actual}", actual);
        }
        if (metadata != null) {
            for (Map.Entry<String, String> entry : metadata.entrySet()) {
                message = message.replace("{" + entry.getKey() + "}", entry.getValue());
            }
        }
        if (message.indexOf('{') >= 0 || message.indexOf('}') >= 0) {
            throw new BoundaryExecutor.Defect(
                "an uninstantiated placeholder remains in the pinned template: \""
                    + message + "\"");
        }
        return message;
    }
}
