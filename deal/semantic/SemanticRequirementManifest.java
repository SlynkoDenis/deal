package deal.semantic;

import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOpKind;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * One implementation module's semantic requirement manifest (foundation
 * F3; parent canonical surfaces):
 *
 * <pre>{@code
 * SemanticRequirementManifest {
 *   moduleId,
 *   capabilities: Set<SemanticCapability>,                    // closed set, exactly the S4 capability order when iterated
 *   constructCoverage: Map<ConstructKind, [SemanticOpKind]>,  // enum-keyed; recorded over the module's reachable constructs
 *   bytesBearing: boolean,                                    // plan-time routing marker; exactly scan.bytesInContainer || scan.bytesValue
 * }
 * }</pre>
 *
 * <p>Produced by {@link LoweringSupport} in {@code CheckedProjectInput}
 * dependency order — one immutable manifest per implementation module.
 * The capability set is closed: only {@link SemanticCapability} values
 * appear (the enum admits no open member), every manifest claims
 * {@code FOUNDATION_VALUES} by construction (F3: every implementation
 * module claims it), and {@code STDLIB_TIME_CONFLICT} is the inert
 * routing marker no manifest claims since K7 (the superseded four-part
 * line trigger and its planning claim are retired); the closed
 * capability set, the empty-evidence catalog row, the planner's
 * time-conflict reroute, and the validator's empty-evidence rule stay
 * in the tree as inert surfaces. The
 * {@code bytesBearing} marker is the step-1 bytes guard (ISSUE-0574,
 * parent S1b): a fixed per-module boolean set by
 * {@link LoweringSupport} exactly from {@code scan.bytesInContainer ||
 * scan.bytesValue} (the same triggers as the unchanged
 * {@code CONTAINERS_AND_STRINGS} claim arm — the claim stays the
 * construct-ownership fact, the marker is the plan-time routing fact
 * planner rule 2b consumes), serialized as the {@code bytesBearing}
 * key of the canonical JSON. A bytes-bearing module routes
 * {@code LEGACY} in every purpose and is never common-lowerable — no
 * capability, registry entry, registry hash, or
 * {@code deal.semantic-ir/1} schema member changes.
 * The {@code constructCoverage} rows are recorded over the module's
 * reachable constructs from the closed construct→op detector table (S4):
 * each row's op-kind list is exactly {@link ConstructKind#mappedOpKinds()}
 * verbatim — enforced at construction, never reinterpreted — and the
 * {@code std/time.nowMillis} row is an ordinary recorded row since K7
 * (its produced {@code STDLIB_CALL}/boundary ops evidence it; S1). At
 * lowering start the unit producer copies these rows onto the unit's own
 * enum-keyed {@code constructCoverage} field — the validator's pinned
 * R-COVERAGE fact (S1/S6).</p>
 *
 * <p>Determinism: capabilities iterate in {@code SemanticCapability}
 * declaration order ({@code EnumSet}) and coverage rows iterate in
 * {@code ConstructKind} declaration order ({@code EnumMap});
 * {@link #toCanonicalJson()} serializes through the single canonical JSON
 * facility (S2), so repeated computation yields byte-identical manifests.
 * The record is immutable and carries no AST node, checker fact, or
 * identity-keyed map.</p>
 *
 * @param moduleId          the implementation module identity; non-null
 * @param capabilities      the closed capability claims; non-null,
 *                          non-empty, contains {@code FOUNDATION_VALUES}
 * @param constructCoverage the enum-keyed reachable-construct rows; non-null
 * @param bytesBearing      the plan-time bytes-bearing marker (ISSUE-0574
 *                          rule 2b): exactly the module scan's
 *                          {@code bytesInContainer || bytesValue}
 */
public record SemanticRequirementManifest(
    ModuleId moduleId,
    Set<SemanticCapability> capabilities,
    Map<ConstructKind, List<SemanticOpKind>> constructCoverage,
    boolean bytesBearing
) {

    public SemanticRequirementManifest {
        Objects.requireNonNull(moduleId, "moduleId must not be null");
        Objects.requireNonNull(capabilities, "capabilities must not be null");
        if (capabilities.isEmpty()) {
            throw new IllegalArgumentException("a manifest carries at least one capability");
        }
        if (!capabilities.contains(SemanticCapability.FOUNDATION_VALUES)) {
            throw new IllegalArgumentException(
                "every implementation module claims FOUNDATION_VALUES (foundation F3); "
                    + "a manifest without it is a producer defect");
        }
        EnumSet<SemanticCapability> capabilitiesCopy = EnumSet.noneOf(SemanticCapability.class);
        capabilitiesCopy.addAll(capabilities);
        capabilities = Collections.unmodifiableSet(capabilitiesCopy);

        Objects.requireNonNull(constructCoverage, "constructCoverage must not be null");
        Map<ConstructKind, List<SemanticOpKind>> coverageCopy = new EnumMap<>(ConstructKind.class);
        for (Map.Entry<ConstructKind, List<SemanticOpKind>> entry : constructCoverage.entrySet()) {
            Objects.requireNonNull(entry.getKey(), "constructCoverage keys must not be null");
            Objects.requireNonNull(entry.getValue(), "constructCoverage values must not be null");
            if (!entry.getValue().equals(entry.getKey().mappedOpKinds())) {
                throw new IllegalArgumentException(
                    "constructCoverage rows carry the closed construct\u2192op detector "
                        + "table's mapped op kinds verbatim (S4): row " + entry.getKey()
                        + " must be exactly " + entry.getKey().mappedOpKinds()
                        + ", got " + entry.getValue());
            }
            coverageCopy.put(entry.getKey(), List.copyOf(entry.getValue()));
        }
        constructCoverage = Collections.unmodifiableMap(coverageCopy);
    }

    /**
     * The single canonical JSON mapping of this manifest (capabilities in
     * {@code SemanticCapability} declaration order, coverage rows keyed by
     * {@code ConstructKind} name, module id through the canonicalizer's
     * semantic-ID mapping) — the deterministic serialization repeated
     * builds compare for byte-identity (F3).
     *
     * @return the canonical JSON object
     */
    public CanonicalJson.Value toCanonicalJson() {
        List<CanonicalJson.Value> caps = new ArrayList<>();
        for (SemanticCapability capability : capabilities) {
            caps.add(CanonicalJson.str(capability.name()));
        }
        List<CanonicalJson.Entry> coverageEntries = new ArrayList<>();
        for (Map.Entry<ConstructKind, List<SemanticOpKind>> entry : constructCoverage.entrySet()) {
            List<CanonicalJson.Value> kinds = new ArrayList<>();
            for (SemanticOpKind kind : entry.getValue()) {
                kinds.add(CanonicalJson.str(kind.name()));
            }
            coverageEntries.add(CanonicalJson.e(entry.getKey().name(),
                CanonicalJson.arr(kinds)));
        }
        return CanonicalJson.obj(
            CanonicalJson.e("bytesBearing", CanonicalJson.bool(bytesBearing)),
            CanonicalJson.e("capabilities", CanonicalJson.arr(caps)),
            CanonicalJson.e("constructCoverage", CanonicalJson.obj(coverageEntries)),
            CanonicalJson.e("moduleId",
                ContractSnapshotCanonicalizer.semanticIdJson(moduleId)));
    }

    /**
     * The deterministic canonical JSON text of this manifest (UTF-8, the
     * single canonical JSON facility) — byte-identical across repeated
     * computation over the same checked project (F3 determinism).
     *
     * @return the canonical JSON text
     */
    public String canonicalText() {
        return CanonicalJson.serializeText(toCanonicalJson());
    }
}
