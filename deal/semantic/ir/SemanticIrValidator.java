package deal.semantic.ir;

import deal.diagnostics.CompilerDiagnostic;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The closed {@code deal.semantic-ir/1} validator (schema S6; foundation
 * admission gate): rejects exactly the objective's closed 14-condition
 * rule set and nothing else, on both pinned surfaces —
 *
 * <ul>
 *   <li>the <b>typed record surface</b>:
 *       {@link #validate(LoweredModuleUnit, ComparisonFacts)} and
 *       {@link #validate(ExecutableLoweredProject, ComparisonFacts)} over
 *       T2's closed schema records; and</li>
 *   <li>the <b>canonical-JSON text surface</b>:
 *       {@link #validateText(String, ComparisonFacts)}, the pinned
 *       invalid-IR injection route: the text is decoded through T3's
 *       single parser ({@link CanonicalJson#parse}) into intermediate
 *       records whose closed enum positions carry raw strings, and the
 *       <em>same</em> 14 rules run on both surfaces (one rule engine, two
 *       converters — a typed converter extracting enum names and payload
 *       JSON through {@link ContractSnapshotCanonicalizer#payloadJson}
 *       and {@link ContractSnapshotCanonicalizer#toJson}, and a text
 *       converter extracting the same raw names from the serialized
 *       unit/project).</li>
 * </ul>
 *
 * <p>The 14 rules reject exactly the S6 list (rule order fixed as the S6
 * enumeration order, deterministic across runs):</p>
 *
 * <pre>{@code
 * R-COVERAGE, R-ENUM, R-CAPABILITY, R-POLICY-KIND, R-BOUNDARY-TRIPLE,
 * R-ELIDED-PLACEMENT, R-FUNCTION-BINDING, R-EXTERNAL-ENTRY, R-ALIAS-CYCLE,
 * R-TOKEN-REUSE, R-PRIVATE-STEP, R-RESERVED-NAME, R-DIGEST, R-PROFILE
 * }</pre>
 *
 * <p>Deterministic first-failure order: modules in dependency order
 * (outer), then the 14 rules in the pinned enumeration order, then — for
 * each rule — the unit's ops in op order (inner). A single closed position
 * dispatches to exactly one rule, pinned by S6's negative list:</p>
 *
 * <ul>
 *   <li>an op-kind value outside the closed 55 → {@code R-PRIVATE-STEP}
 *       (a consumer-private semantic step);</li>
 *   <li>an out-of-set {@code StdlibFunctionId} value → {@code R-ENUM}
 *       (the stdlib selector reservation list is empty since
 *       {@code TIME_NOW_MILLIS} became the 21st member, so
 *       {@code R-RESERVED-NAME} covers only the reserved
 *       {@code FailurePolicyId} names);</li>
 *   <li>a {@code FailurePolicyId} value among
 *       {@code EXTERNAL_PARAMETER}/{@code EXTERNAL_RETURN}/
 *       {@code STDLIB_PARAMETER}/{@code STDLIB_RETURN} →
 *       {@code R-RESERVED-NAME}, any other out-of-set value →
 *       {@code R-ENUM};</li>
 *   <li>a {@code BoundaryKind} value — including the reserved
 *       {@code BYTE_ELEMENT_ASSIGNMENT}/{@code C_FFI_TO_DEAL}/
 *       {@code DEAL_TO_C_FFI} — outside the closed 25 → {@code R-ENUM};</li>
 *   <li>every other closed enum position (selectors, modes, control
 *       selectors, capture modes, index/iteration modes, async sources)
 *       → {@code R-ENUM};</li>
 *   <li>a unit {@code semanticProfile} other than {@code DEAL_V1_2_INT32}
 *       → {@code R-PROFILE} (a non-{@code DEAL_V1_2_INT32} unit, S6's
 *       first sub-condition — including the {@code LEGACY_SAFE_INT} name
 *       injected through text).</li>
 * </ul>
 *
 * <p>The structural checks the parent's resource-limit sentence names
 * (ownership cycles, bad dominance, invalid exits, stale generations,
 * unresolvable bindings, missing boundaries) are <em>not</em> part of
 * this closed set — they are the construct epics' production-time checks
 * (ISSUE-0233..0236). Every rejection is E6005 with a
 * {@link LoweringFailureDetail} built by T5's
 * {@link FailureContractRegistry} (code {@code E6005}, phase
 * {@code BACKEND_LOWERING}); a text-surface decode failure raises
 * {@link SemanticIrTextDecodeException} — a transport-level rejection,
 * never E6005 and never a validator rule.</p>
 *
 * <p>The unit text protocol (produced by {@link #toUnitText(LoweredModuleUnit)},
 * consumed by {@link #validateText(String, ComparisonFacts)}) carries the
 * validator's pinned input — the unit's validation-relevant fields with
 * their record component names as pinned keys; the ops' payloads and
 * contracts render through T3's single snapshot/payload mappings. The
 * project text protocol is
 * {@code {semanticProfile, entryModule, modules:[unit…]}}.</p>
 */
public final class SemanticIrValidator {

    private SemanticIrValidator() {
        // Static surface; no instances.
    }

    // =========================================================================
    // Pinned rule set (S6 enumeration order)
    // =========================================================================

    /** The R-COVERAGE rule: an uncovered reachable AST kind. */
    public static final String R_COVERAGE = "R-COVERAGE";

    /** The R-ENUM rule: an open or reserved enum value in a closed position. */
    public static final String R_ENUM = "R-ENUM";

    /** The R-CAPABILITY rule: a claimed capability without a required operation
     *  (an empty S4 evidence set is unsatisfiable by construction and is
     *  rejected — {@code STDLIB_TIME_CONFLICT}, never valid IR). */
    public static final String R_CAPABILITY = "R-CAPABILITY";

    /** The R-POLICY-KIND rule: a failure policy not allowed for its selector/kind. */
    public static final String R_POLICY_KIND = "R-POLICY-KIND";

    /** The R-BOUNDARY-TRIPLE rule: a boundary triple outside the closed boundary-assignment table
     *  (including a body-local creation-op return cell that violates its closed conditions). */
    public static final String R_BOUNDARY_TRIPLE = "R-BOUNDARY-TRIPLE";

    /** The R-ELIDED-PLACEMENT rule: ELIDED_BY_ADAPTER outside an adapter-over-async task. */
    public static final String R_ELIDED_PLACEMENT = "R-ELIDED-PLACEMENT";

    /**
     * The R-FUNCTION-BINDING rule: a function-typed result ValueId or a
     * function-typed {@code HOST_TO_DEAL} crossing input without exactly
     * one registration — including the closed {@code HostFunctionValue}
     * correlation (ISSUE-0531): the materializing crossing op id must
     * name exactly the producing host crossing whose input identity keys
     * the registration and whose checked descriptor the registration
     * carries — and the closed {@code DynamicFunctionValue} correlation
     * (ISSUE-0673): the registered producing op id must name an op of
     * the unit whose result identity is the registration key and whose
     * result descriptor is the registered descriptor.
     */
    public static final String R_FUNCTION_BINDING = "R-FUNCTION-BINDING";

    /** The R-EXTERNAL-ENTRY rule: a SHARED_BODY ExternalFunction without a recorded EXTERNAL_ENTRY. */
    public static final String R_EXTERNAL_ENTRY = "R-EXTERNAL-ENTRY";

    /** The R-ALIAS-CYCLE rule: an alias-token cycle. */
    public static final String R_ALIAS_CYCLE = "R-ALIAS-CYCLE";

    /** The R-TOKEN-REUSE rule: a token consumed twice. */
    public static final String R_TOKEN_REUSE = "R-TOKEN-REUSE";

    /** The R-PRIVATE-STEP rule: a consumer-private semantic step. */
    public static final String R_PRIVATE_STEP = "R-PRIVATE-STEP";

    /** The R-RESERVED-NAME rule: a reserved selector or policy name. */
    public static final String R_RESERVED_NAME = "R-RESERVED-NAME";

    /** The R-DIGEST rule: a bad contract digest. */
    public static final String R_DIGEST = "R-DIGEST";

    /** The R-PROFILE rule: a profile/interface mismatch. */
    public static final String R_PROFILE = "R-PROFILE";

    /** The closed 14-condition rule set in the pinned S6 enumeration order. */
    public static final List<String> RULES = List.of(
        R_COVERAGE, R_ENUM, R_CAPABILITY, R_POLICY_KIND, R_BOUNDARY_TRIPLE,
        R_ELIDED_PLACEMENT, R_FUNCTION_BINDING, R_EXTERNAL_ENTRY, R_ALIAS_CYCLE,
        R_TOKEN_REUSE, R_PRIVATE_STEP, R_RESERVED_NAME, R_DIGEST, R_PROFILE);

    /** The only admitted unit profile name (S1). */
    public static final String ADMITTED_PROFILE = "DEAL_V1_2_INT32";

    // =========================================================================
    // Comparison facts (validator contract Input)
    // =========================================================================

    /**
     * The lowering-context comparison facts (schema S6 validator contract
     * Input): the interface index digest, the semantic profile, and the
     * invocation's capability-registry hash. R-PROFILE compares the unit's
     * {@code interfaceHash} against {@code interfaceIndexDigest} and the
     * unit's {@code loweringContextHash} against
     * {@code LoweringContextHash.of(semanticProfile, capabilityRegistryHash)}
     * recomputed from these facts.
     *
     * @param interfaceIndexDigest   the interface index digest the unit was
     *                               checked against; non-null
     * @param semanticProfile        the invocation's semantic profile; non-null
     * @param capabilityRegistryHash the invocation's capability-registry
     *                               digest (hex string, carried verbatim); non-null
     */
    public record ComparisonFacts(String interfaceIndexDigest, SemanticProfile semanticProfile,
                                  String capabilityRegistryHash) {

        public ComparisonFacts {
            Objects.requireNonNull(interfaceIndexDigest, "interfaceIndexDigest must not be null");
            Objects.requireNonNull(semanticProfile, "semanticProfile must not be null");
            Objects.requireNonNull(capabilityRegistryHash, "capabilityRegistryHash must not be null");
        }
    }

    // =========================================================================
    // Public surface
    // =========================================================================

    /**
     * Validates one unit on the typed record surface. Returns empty on
     * pass and exactly one E6005 diagnostic naming the first failing rule
     * on failure. No mutation; deterministic single pass.
     *
     * <p>Cross-unit obligations (a {@code SHARED_BODY}
     * {@code ExternalFunction} binding or an {@code externalEntryRef}
     * naming another module) are checked at project level by
     * {@link #validate(ExecutableLoweredProject, ComparisonFacts)}; a
     * unit-level validation treats foreign-module references as
     * indeterminate and skips them.</p>
     *
     * @param unit  the unit; non-null
     * @param facts the comparison facts; non-null
     * @return empty on pass, otherwise the first E6005
     */
    public static Optional<CompilerDiagnostic> validate(LoweredModuleUnit unit, ComparisonFacts facts) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(facts, "facts must not be null");
        RawUnit raw = RawUnit.fromTyped(unit);
        Optional<CompilerDiagnostic> failure = validateUnit(raw, facts, Map.of());
        if (failure.isPresent()) {
            return failure;
        }
        return checkClassDeclarationLayout(unit, raw, facts);
    }

    /**
     * Validates a complete executable project on the typed record surface:
     * every module in dependency (map insertion) order, plus the
     * cross-unit checks (R-EXTERNAL-ENTRY resolution across the complete
     * implementation closure). Returns empty on pass and exactly one E6005
     * naming the first failing rule on failure.
     *
     * @param project the project; non-null
     * @param facts   the comparison facts; non-null
     * @return empty on pass, otherwise the first E6005
     */
    public static Optional<CompilerDiagnostic> validate(ExecutableLoweredProject project,
                                                        ComparisonFacts facts) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(facts, "facts must not be null");
        Map<String, RawUnit> closure = new LinkedHashMap<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            RawUnit raw = RawUnit.fromTyped(unit);
            closure.put(raw.modulePath(), raw);
        }
        for (RawUnit unit : closure.values()) {
            Optional<CompilerDiagnostic> failure = validateUnit(unit, facts, closure);
            if (failure.isPresent()) {
                return failure;
            }
        }
        return Optional.empty();
    }

    /**
     * Validates canonical {@code deal.semantic-ir/1} text — a serialized
     * unit (the {@link #toUnitText(LoweredModuleUnit)} protocol) or a
     * serialized project ({@code {semanticProfile, entryModule, modules}})
     * — through the single parser with closed enum positions carried as
     * raw strings, running exactly the same closed 14 rules.
     *
     * @param canonicalJson the canonical unit/project JSON text; non-null
     * @param facts         the comparison facts; non-null
     * @return empty on pass, otherwise the first E6005
     * @throws SemanticIrTextDecodeException on malformed JSON, a pinned
     *         framing/field/value-type/version mismatch, or an
     *         unresolvable entry module (transport-level, never E6005)
     */
    public static Optional<CompilerDiagnostic> validateText(String canonicalJson, ComparisonFacts facts) {
        Objects.requireNonNull(canonicalJson, "canonicalJson must not be null");
        Objects.requireNonNull(facts, "facts must not be null");
        CanonicalJson.Value value = ContractSnapshotCanonicalizer.parseValidationText(canonicalJson);
        if (!(value instanceof CanonicalJson.Obj obj)) {
            throw new SemanticIrTextDecodeException(
                "the top-level validation text must be an object, got "
                    + ContractSnapshotCanonicalizer.jsonKindName(value));
        }
        if (ContractSnapshotCanonicalizer.hasKey(obj, "modules")) {
            return validateProjectText(obj, facts);
        }
        if (ContractSnapshotCanonicalizer.hasKey(obj, "moduleId")) {
            return validateUnit(ContractSnapshotCanonicalizer.parseUnit(obj), facts, Map.of());
        }
        throw new SemanticIrTextDecodeException(
            "the top-level validation text must be a unit (\"moduleId\") or a project "
                + "(\"modules\") object");
    }

    /**
     * Serializes a unit to its canonical validation text — the pinned
     * text-surface protocol consumed by {@link #validateText(String, ComparisonFacts)}.
     * The mapping flows through the single canonicalizer.
     *
     * @param unit the unit; non-null
     * @return the deterministic canonical JSON text (UTF-8, sorted keys)
     */
    public static String toUnitText(LoweredModuleUnit unit) {
        Objects.requireNonNull(unit, "unit must not be null");
        return CanonicalJson.serializeText(
            ContractSnapshotCanonicalizer.toJson(RawUnit.fromTyped(unit)));
    }

    /**
     * Serializes a project to its canonical validation text
     * ({@code {semanticProfile, entryModule, modules}}).
     *
     * @param project the project; non-null
     * @return the deterministic canonical JSON text
     */
    public static String toProjectText(ExecutableLoweredProject project) {
        Objects.requireNonNull(project, "project must not be null");
        return CanonicalJson.serializeText(ContractSnapshotCanonicalizer.toJson(project));
    }

    private static Optional<CompilerDiagnostic> validateProjectText(CanonicalJson.Obj obj,
                                                                    ComparisonFacts facts) {
        ContractSnapshotCanonicalizer.ParsedProject project =
            ContractSnapshotCanonicalizer.parseProject(obj);
        Map<String, RawUnit> closure = new LinkedHashMap<>();
        for (RawUnit unit : project.modules()) {
            closure.put(unit.modulePath(), unit);
        }
        if (!ADMITTED_PROFILE.equals(project.semanticProfile())) {
            return fail(closure.get(project.entryModule()), facts, R_PROFILE,
                SemanticCapability.FOUNDATION_VALUES,
                origin(R_PROFILE, "project semanticProfile \"" + project.semanticProfile()
                    + "\" is not DEAL_V1_2_INT32"));
        }
        for (RawUnit unit : closure.values()) {
            Optional<CompilerDiagnostic> failure = validateUnit(unit, facts, closure);
            if (failure.isPresent()) {
                return failure;
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // Rule engine
    // =========================================================================

    /**
     * Validates one raw unit against the closed 14 rules in the pinned
     * order: the S6 rule enumeration order (outer), then op order within
     * each rule (inner). {@code closure} is the project module map for
     * cross-unit resolution (empty for unit-level validation).
     */
    private static Optional<CompilerDiagnostic> validateUnit(RawUnit unit, ComparisonFacts facts,
                                                             Map<String, RawUnit> closure) {
        Optional<CompilerDiagnostic> failure;
        failure = checkCoverage(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkEnum(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkCapability(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkPolicyKind(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkBoundaryTriple(unit, facts, closure);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkElidedPlacement(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkFunctionBinding(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkExternalEntry(unit, facts, closure);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkAliasCycle(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkTokenReuse(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkPrivateStep(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkReservedName(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkDigest(unit, facts);
        if (failure.isPresent()) {
            return failure;
        }
        return checkProfile(unit, facts);
    }

    private static Optional<CompilerDiagnostic> fail(RawUnit unit, ComparisonFacts facts,
                                                     String rule, SemanticCapability capability,
                                                     String origin) {
        LoweringFailureDetail detail = new LoweringFailureDetail(unit.modulePath(), capability,
            rule, facts.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION, origin);
        return Optional.of(FailureContractRegistry.e6005(detail));
    }

    private static String origin(String rule, String what) {
        return "SemanticIrValidator " + rule + " (" + what + ")";
    }

    // -- R-COVERAGE ------------------------------------------------------------

    /**
     * The typed-surface layout tie of the {@code CLASS_DECLARATION}
     * row's layout-only R-COVERAGE waiver (ISSUE-0511): the waiver is
     * admitted only when the layout record the row is satisfied by was
     * actually produced. The raw model carries no layouts
     * ({@link RawUnit}), so the tie is checked on the typed unit after
     * the closed rule engine passes: when the
     * {@code CLASS_DECLARATION} row is recorded, no op of the mapped
     * kinds ({@code CLASS_DEFAULT}/{@code CLASS_FACTORY}/
     * {@code EXPORT_PUBLISH}) was produced, and
     * {@code unit.classLayouts()} is empty, the row is satisfied by
     * nothing — a layout-only class must still have its layout record —
     * and R-COVERAGE fails.
     */
    private static Optional<CompilerDiagnostic> checkClassDeclarationLayout(
            LoweredModuleUnit unit, RawUnit raw, ComparisonFacts facts) {
        if (!unit.constructCoverage().containsKey(ConstructKind.CLASS_DECLARATION)) {
            return Optional.empty();
        }
        Set<SemanticOpKind> mapped =
            new LinkedHashSet<>(ConstructKind.CLASS_DECLARATION.mappedOpKinds());
        for (SemanticOp op : unit.ops()) {
            if (mapped.contains(op.kind())) {
                return Optional.empty();
            }
        }
        if (!unit.classLayouts().isEmpty()) {
            return Optional.empty();
        }
        return fail(raw, facts, R_COVERAGE, SemanticCapability.FOUNDATION_VALUES,
            origin(R_COVERAGE, "construct " + ConstructKind.CLASS_DECLARATION.name()
                + " recorded in constructCoverage with no produced op of any mapped kind "
                + "and no class layout record (a layout-only class must still have its "
                + "layout)"));
    }

    private static Optional<CompilerDiagnostic> checkCoverage(RawUnit unit, ComparisonFacts facts) {
        for (RawCoverage row : unit.coverage()) {
            ConstructKind construct = enumByName(ConstructKind.class, row.construct());
            if (construct == null) {
                // R-ENUM owns an out-of-set construct name.
                continue;
            }
            Set<SemanticOpKind> obligation = new LinkedHashSet<>();
            for (String kindName : row.opKinds()) {
                SemanticOpKind kind = enumByName(SemanticOpKind.class, kindName);
                if (kind != null) {
                    obligation.add(kind);
                }
            }
            boolean produced = false;
            for (RawOp op : unit.ops()) {
                SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
                if (kind != null && obligation.contains(kind)) {
                    produced = true;
                    break;
                }
            }
            if (!produced) {
                // ISSUE-0231..0239 row-extension consumption: the
                // CLASS_DECLARATION row's required common form begins with
                // "layout" — a class layout is unit data
                // (unit.classLayouts), never an op. A no-default
                // non-exported (layout-only) class therefore produces no
                // CLASS_DEFAULT/CLASS_FACTORY op, and the row is satisfied
                // by the produced layout record; the op-bearing shapes
                // (defaulted/exported classes) evidence the row through
                // the produced CLASS_DEFAULT/CLASS_FACTORY ops. No vacuous
                // op is invented for the layout-only shape. The raw model
                // carries no layouts, so the waiver's layout record is
                // tied on the typed surface (checkClassDeclarationLayout):
                // a recorded row with no mapped op and no layout record
                // still fails R-COVERAGE.
                if (construct == ConstructKind.CLASS_DECLARATION) {
                    continue;
                }
                return fail(unit, facts, R_COVERAGE, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_COVERAGE, "construct " + row.construct()
                        + " recorded in constructCoverage with no produced op of any mapped kind"));
            }
        }
        return Optional.empty();
    }

    // -- R-ENUM ----------------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkEnum(RawUnit unit, ComparisonFacts facts) {
        // Unit-level closed positions.
        for (String capability : unit.requiredCapabilities()) {
            if (enumByName(SemanticCapability.class, capability) == null) {
                return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ENUM, "open value \"" + capability
                        + "\" in a closed SemanticCapability position"));
            }
        }
        for (RawCoverage row : unit.coverage()) {
            if (enumByName(ConstructKind.class, row.construct()) == null) {
                return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ENUM, "open value \"" + row.construct()
                        + "\" in a closed ConstructKind position"));
            }
        }
        for (RawBinding binding : unit.bindings()) {
            Optional<CompilerDiagnostic> bindingFailure = checkBindingEnum(unit, facts, binding);
            if (bindingFailure.isPresent()) {
                return bindingFailure;
            }
        }
        // Per-op closed positions in op order.
        for (RawOp op : unit.ops()) {
            Optional<CompilerDiagnostic> opFailure = checkOpEnum(unit, facts, op);
            if (opFailure.isPresent()) {
                return opFailure;
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkBindingEnum(RawUnit unit, ComparisonFacts facts,
                                                                 RawBinding binding) {
        Set<String> shapes = Set.of("loweredBody", "adapter", "hostFunction",
            "hostFunctionValue", "externalFunction", "intrinsicFunction",
            "dynamicFunctionValue");
        if (!shapes.contains(binding.shape())) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.shape()
                    + "\" in a closed FunctionExecutionBinding shape position"));
        }
        if (binding.captureMode() != null
                && enumByName(CaptureMode.class, binding.captureMode()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.captureMode()
                    + "\" in a closed CaptureMode position"));
        }
        if (binding.intrinsicKind() != null
                && enumByName(IntrinsicKind.class, binding.intrinsicKind()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.intrinsicKind()
                    + "\" in a closed IntrinsicKind position"));
        }
        if ("intrinsicFunction".equals(binding.shape())
                && (binding.intrinsicKind() == null || binding.descriptor() == null)) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "the intrinsicFunction binding " + binding.allocationId()
                    + " carries no intrinsic kind and descriptor text (the closed shape "
                    + "position is its kind plus its declared signature)"));
        }
        if ("dynamicFunctionValue".equals(binding.shape())
                && (binding.materializingBoundaryOpId() == null
                    || binding.descriptor() == null)) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "the dynamicFunctionValue binding " + binding.allocationId()
                    + " carries no producing op id and descriptor text (the closed shape "
                    + "position is the producing op plus the materialized descriptor)"));
        }
        if (binding.executionOwner() != null
                && enumByName(ExternalExecutionOwner.class, binding.executionOwner()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.executionOwner()
                    + "\" in a closed ExternalExecutionOwner position"));
        }
        if (binding.descriptor() != null && parseDescriptorQuiet(binding.descriptor()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.descriptor()
                    + "\" in a closed descriptor position"));
        }
        if (binding.targetSignature() != null
                && parseDescriptorQuiet(binding.targetSignature()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + binding.targetSignature()
                    + "\" in a closed descriptor position"));
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkOpEnum(RawUnit unit, ComparisonFacts facts,
                                                            RawOp op) {
        SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
        // Snapshot selector (a closed selector position).
        if (op.selector() != null) {
            if (kind == SemanticOpKind.UNARY) {
                if (enumByName(UnarySelector.class, op.selector()) == null) {
                    return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_ENUM, "open value \"" + op.selector()
                            + "\" in a closed UnarySelector position"));
                }
            } else if (kind == SemanticOpKind.BINARY) {
                if (enumByName(BinarySelector.class, op.selector()) == null) {
                    return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_ENUM, "open value \"" + op.selector()
                            + "\" in a closed BinarySelector position"));
                }
            } else if (kind == SemanticOpKind.STDLIB_CALL) {
                if (enumByName(StdlibFunctionId.class, op.selector()) == null
                        && !StdlibFunctionId.RESERVED_NAMES.contains(op.selector())) {
                    return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_ENUM, "open value \"" + op.selector()
                            + "\" in a closed StdlibFunctionId position"));
                }
            } else if (kind != null) {
                return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ENUM, "selector \"" + op.selector()
                        + "\" on a non-selector-carrying kind " + kind.name()));
            }
        }
        // Failure-policy positions (op-level and snapshot-level).
        if (policyOutOfSet(op.failurePolicy())) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + op.failurePolicy()
                    + "\" in a closed FailurePolicyId position"));
        }
        String snapshotPolicy = optionalString(op.snapshot(), "failurePolicy");
        if (snapshotPolicy != null && policyOutOfSet(snapshotPolicy)) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + snapshotPolicy
                    + "\" in a closed FailurePolicyId position"));
        }
        // Result type: descriptor text or closed internal sentinel.
        if (op.resultType() != null && parseResultType(op.resultType()) == null
                && enumByName(InternalResultType.class, op.resultType()) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + op.resultType()
                    + "\" in a closed result-type position"));
        }
        // Operand descriptor texts.
        for (String operandType : op.operandTypes()) {
            if (parseDescriptorQuiet(operandType) == null) {
                return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ENUM, "open value \"" + operandType
                        + "\" in a closed descriptor position"));
            }
        }
        // Result token closed positions (owner, link kinds along the chain).
        if (op.resultToken() != null) {
            Optional<String> tokenFailure = tokenEnumFailure(op.resultToken());
            if (tokenFailure.isPresent()) {
                return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ENUM, "open value \"" + tokenFailure.get()
                        + "\" in a closed token position"));
            }
        }
        // Payload closed positions and descriptor texts.
        return checkPayloadEnum(unit, facts, op);
    }

    /** An out-of-set non-reserved failure-policy name (reserved names dispatch to R-RESERVED-NAME). */
    private static boolean policyOutOfSet(String raw) {
        return enumByName(FailurePolicyId.class, raw) == null
            && !FailurePolicyId.RESERVED_NAMES.contains(raw);
    }

    /** Validates the closed enum positions along an alias token chain; returns the offending raw value. */
    private static Optional<String> tokenEnumFailure(AsyncTokenId token) {
        if (token instanceof AsyncTokenId.Alias alias) {
            if (enumByName(AsyncLinkKind.class, alias.linkKind().name()) == null) {
                return Optional.of(alias.linkKind().name());
            }
            return tokenEnumFailure(alias.referent());
        }
        if (token instanceof AsyncTokenId.Canonical canonical) {
            if (enumByName(AsyncTokenOwner.class, canonical.owner().name()) == null) {
                return Optional.of(canonical.owner().name());
            }
        }
        return Optional.empty();
    }

    /**
     * Walks the closed enum and descriptor positions of one kind payload
     * (the pinned {@link ContractSnapshotCanonicalizer#payloadJson} keys).
     */
    private static Optional<CompilerDiagnostic> checkPayloadEnum(RawUnit unit,
                                                                 ComparisonFacts facts,
                                                                 RawOp op) {
        CanonicalJson.Obj payload = op.payload();
        Optional<CompilerDiagnostic> failure;
        switch (op.kind()) {
            case "UNARY" -> {
                failure = checkSlotEnum(unit, facts, "selector", optionalString(payload, "selector"),
                    UnarySelector.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "BINARY" -> {
                failure = checkSlotEnum(unit, facts, "selector", optionalString(payload, "selector"),
                    BinarySelector.class);
                if (failure.isPresent()) {
                    return failure;
                }
                String side = optionalString(payload, "side");
                if (side != null) {
                    failure = checkSlotEnum(unit, facts, "side", side, NullableSide.class);
                    if (failure.isPresent()) {
                        return failure;
                    }
                }
                failure = checkSlotDescriptor(unit, facts, "innerDescriptor",
                    optionalString(payload, "innerDescriptor"));
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "ARRAY_NEW" -> {
                failure = checkSlotDescriptor(unit, facts, "elementDescriptor",
                    optionalString(payload, "elementDescriptor"));
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "INDEX_NORMALIZE" -> {
                failure = checkSlotEnum(unit, facts, "mode", optionalString(payload, "mode"),
                    IndexMode.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "BOUNDARY" -> {
                failure = checkSlotEnum(unit, facts, "kind", optionalString(payload, "kind"),
                    BoundaryKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotDescriptor(unit, facts, "descriptor",
                    optionalString(payload, "descriptor"));
                if (failure.isPresent()) {
                    return failure;
                }
                CanonicalJson.Value realization = payloadValue(payload, "realization");
                if (realization instanceof CanonicalJson.Obj realizationObj) {
                    String realizationType = optionalString(realizationObj, "type");
                    if (!"runtimeValidation".equals(realizationType)
                            && !"representationProof".equals(realizationType)) {
                        return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                            origin(R_ENUM, "open value \"" + realizationType
                                + "\" in a closed BoundaryRealization position"));
                    }
                }
            }
            case "BINDING_ALLOC" -> {
                failure = checkSlotEnum(unit, facts, "cellKind", optionalString(payload, "cellKind"),
                    BindingCellKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "CLOSURE_NEW" -> {
                failure = checkSlotDescriptor(unit, facts, "signature",
                    optionalString(payload, "signature"));
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkNestedBindingShape(unit, facts, payload, "binding");
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "FUNCTION_ADAPT" -> {
                failure = checkSlotEnum(unit, facts, "mode", optionalString(payload, "mode"),
                    CaptureMode.class);
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotDescriptor(unit, facts, "sourceSignature",
                    optionalString(payload, "sourceSignature"));
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotDescriptor(unit, facts, "targetSignature",
                    optionalString(payload, "targetSignature"));
                if (failure.isPresent()) {
                    return failure;
                }
                CanonicalJson.Value source = payloadValue(payload, "source");
                if (source instanceof CanonicalJson.Obj sourceObj) {
                    String sourceType = optionalString(sourceObj, "type");
                    if (!"sharedCell".equals(sourceType) && !"thunk".equals(sourceType)
                            && !"value".equals(sourceType)) {
                        return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                            origin(R_ENUM, "open value \"" + sourceType
                                + "\" in a closed AdaptSourceRef position"));
                    }
                }
            }
            case "ASSIGN" -> {
                failure = checkSlotEnum(unit, facts, "targetKind",
                    optionalString(payload, "targetKind"), AssignTargetKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "DELETE" -> {
                failure = checkSlotEnum(unit, facts, "targetKind",
                    optionalString(payload, "targetKind"), DeleteTargetKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "CALL" -> {
                failure = checkSlotEnum(unit, facts, "mode", optionalString(payload, "mode"),
                    CallMode.class);
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotDescriptor(unit, facts, "signature",
                    optionalString(payload, "signature"));
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkCalleeEnum(unit, facts, payload);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "INTRINSIC_CALL" -> {
                failure = checkSlotEnum(unit, facts, "kind", optionalString(payload, "kind"),
                    IntrinsicKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "STDLIB_CALL" -> {
                String function = optionalString(payload, "function");
                if (function != null && enumByName(StdlibFunctionId.class, function) == null
                        && !StdlibFunctionId.RESERVED_NAMES.contains(function)) {
                    return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_ENUM, "open value \"" + function
                            + "\" in a closed StdlibFunctionId position"));
                }
                failure = checkSlotEnum(unit, facts, "effectCapability",
                    optionalString(payload, "effectCapability"), SemanticCapability.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "ASYNC_START" -> {
                failure = checkSlotEnum(unit, facts, "source", optionalString(payload, "source"),
                    AsyncStartSource.class);
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotEnum(unit, facts, "parameterBoundaryMode",
                    optionalString(payload, "parameterBoundaryMode"), ParameterBoundaryMode.class);
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkSlotDescriptor(unit, facts, "completionDescriptor",
                    optionalString(payload, "completionDescriptor"));
                if (failure.isPresent()) {
                    return failure;
                }
                failure = checkCalleeEnum(unit, facts, payload);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "BRANCH", "LOOP" -> {
                failure = checkSlotEnum(unit, facts, "selector", optionalString(payload, "selector"),
                    ControlSelector.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "FOR_EACH" -> {
                failure = checkSlotEnum(unit, facts, "mode", optionalString(payload, "mode"),
                    IterationMode.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "CLASS_NEW" -> {
                failure = checkSlotEnum(unit, facts, "defaultOwner",
                    optionalString(payload, "defaultOwner"), DefaultOwner.class);
                if (failure.isPresent()) {
                    return failure;
                }
                CanonicalJson.Value fieldBoundaries = payloadValue(payload, "fieldBoundaries");
                if (fieldBoundaries instanceof CanonicalJson.Arr boundaries) {
                    for (CanonicalJson.Value item : boundaries.items()) {
                        if (!(item instanceof CanonicalJson.Obj boundary)) {
                            continue;
                        }
                        failure = checkSlotEnum(unit, facts, "fieldBoundaries.kind",
                            optionalString(boundary, "kind"), BoundaryKind.class);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                }
            }
            case "MODULE_IMPORT" -> {
                failure = checkSlotEnum(unit, facts, "kind", optionalString(payload, "kind"),
                    ModuleImportKind.class);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            case "EXPORT_READ", "EXPORT_PUBLISH" -> {
                failure = checkSlotDescriptor(unit, facts, "descriptor",
                    optionalString(payload, "descriptor"));
                if (failure.isPresent()) {
                    return failure;
                }
            }
            default -> {
                // Unknown op kinds are R-PRIVATE-STEP's position; their
                // payloads carry no walkable closed slots.
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkCalleeEnum(RawUnit unit, ComparisonFacts facts,
                                                                CanonicalJson.Obj payload) {
        CanonicalJson.Value calleeValue = payloadValue(payload, "callee");
        if (!(calleeValue instanceof CanonicalJson.Obj callee)) {
            return Optional.empty();
        }
        String calleeType = optionalString(callee, "type");
        if (!"static".equals(calleeType) && !"indirect".equals(calleeType)
                && !"dynamic".equals(calleeType)) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + calleeType
                    + "\" in a closed CallCallee position"));
        }
        if ("static".equals(calleeType)) {
            return checkNestedBindingShape(unit, facts, callee, "binding");
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkNestedBindingShape(RawUnit unit,
                                                                        ComparisonFacts facts,
                                                                        CanonicalJson.Obj owner,
                                                                        String key) {
        CanonicalJson.Value bindingValue = owner == null ? null : payloadValue(owner, key);
        if (!(bindingValue instanceof CanonicalJson.Obj binding)) {
            return Optional.empty();
        }
        String shape = optionalString(binding, "type");
        if (!"loweredBody".equals(shape) && !"adapter".equals(shape)
                && !"hostFunction".equals(shape) && !"hostFunctionValue".equals(shape)
                && !"externalFunction".equals(shape)) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + shape
                    + "\" in a closed FunctionExecutionBinding shape position"));
        }
        String captureMode = optionalString(binding, "captureMode");
        if (captureMode != null && enumByName(CaptureMode.class, captureMode) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + captureMode
                    + "\" in a closed CaptureMode position"));
        }
        String executionOwner = optionalString(binding, "executionOwner");
        if (executionOwner != null
                && enumByName(ExternalExecutionOwner.class, executionOwner) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + executionOwner
                    + "\" in a closed ExternalExecutionOwner position"));
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkSlotEnum(RawUnit unit, ComparisonFacts facts,
                                                              String position, String raw,
                                                              Class<? extends Enum<?>> closed) {
        if (raw != null && enumByName(closed, raw) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + raw + "\" in a closed " + position
                    + " position"));
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkSlotDescriptor(RawUnit unit,
                                                                    ComparisonFacts facts,
                                                                    String position, String raw) {
        if (raw != null && parseDescriptorQuiet(raw) == null) {
            return fail(unit, facts, R_ENUM, SemanticCapability.FOUNDATION_VALUES,
                origin(R_ENUM, "open value \"" + raw + "\" in a closed " + position
                    + " position"));
        }
        return Optional.empty();
    }

    // -- R-CAPABILITY ----------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkCapability(RawUnit unit, ComparisonFacts facts) {
        Set<SemanticOpKind> produced = new LinkedHashSet<>();
        for (RawOp op : unit.ops()) {
            SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
            if (kind != null) {
                produced.add(kind);
            }
        }
        for (String capabilityName : unit.requiredCapabilities()) {
            SemanticCapability capability = enumByName(SemanticCapability.class, capabilityName);
            if (capability == null) {
                continue; // R-ENUM owns an out-of-set capability name.
            }
            List<CapabilityRequirementCatalog.RequiredOperation> required =
                CapabilityRequirementCatalog.requiredOperations(capability);
            if (required.isEmpty()) {
                // An empty S4 evidence set is unsatisfiable by construction:
                // the unit can never contain a required operation, so the
                // claim is rejected — STDLIB_TIME_CONFLICT is a routing
                // marker only and is never valid IR (S4).
                return fail(unit, facts, R_CAPABILITY, capability,
                    origin(R_CAPABILITY, "claimed capability " + capabilityName
                        + " without a required operation (the S4 catalog defines no "
                        + "required operation for " + capabilityName
                        + " — a routing marker only, never valid IR)"));
            }
            for (CapabilityRequirementCatalog.RequiredOperation requiredOp : required) {
                boolean satisfied = false;
                for (SemanticOpKind kind : requiredOp.kinds()) {
                    if (produced.contains(kind)) {
                        satisfied = true;
                        break;
                    }
                }
                if (!satisfied) {
                    return fail(unit, facts, R_CAPABILITY, capability,
                        origin(R_CAPABILITY, "claimed capability " + capabilityName
                            + " without a required operation (" + requiredOp.verbatim() + ")"));
                }
            }
        }
        return Optional.empty();
    }

    // -- R-POLICY-KIND ---------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkPolicyKind(RawUnit unit, ComparisonFacts facts) {
        for (RawOp op : unit.ops()) {
            SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
            if (kind == null) {
                continue; // R-PRIVATE-STEP owns an out-of-set op kind.
            }
            FailurePolicyId policy = enumByName(FailurePolicyId.class, op.failurePolicy());
            if (policy == null) {
                continue; // R-ENUM/R-RESERVED-NAME owns an out-of-set or reserved policy.
            }
            Optional<CompilerDiagnostic> failure = policyForOp(unit, facts, op, kind, policy);
            if (failure.isPresent()) {
                return failure;
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> policyForOp(RawUnit unit, ComparisonFacts facts,
                                                            RawOp op, SemanticOpKind kind,
                                                            FailurePolicyId policy) {
        return switch (kind) {
            case UNARY -> {
                UnarySelector selector = enumByName(UnarySelector.class, op.selector());
                if (selector == null) {
                    yield Optional.empty(); // R-ENUM owns the selector.
                }
                yield requirePolicy(unit, facts, op, policy, unaryPolicy(selector),
                    selector.name());
            }
            case BINARY -> {
                BinarySelector selector = enumByName(BinarySelector.class, op.selector());
                if (selector == null) {
                    yield Optional.empty();
                }
                FailurePolicyId expected = binaryPolicy(selector);
                yield requirePolicy(unit, facts, op, policy, expected, selector.name());
            }
            case STDLIB_CALL -> {
                StdlibFunctionId function = enumByName(StdlibFunctionId.class,
                    optionalString(op.payload(), "function"));
                if (function == null) {
                    yield Optional.empty();
                }
                yield requirePolicy(unit, facts, op, policy, stdlibPolicy(function),
                    function.name());
            }
            case INTRINSIC_CALL -> {
                IntrinsicKind intrinsic = enumByName(IntrinsicKind.class,
                    optionalString(op.payload(), "kind"));
                if (intrinsic == null) {
                    yield Optional.empty();
                }
                yield requirePolicy(unit, facts, op, policy, intrinsicPolicy(intrinsic),
                    intrinsic.name());
            }
            case THROW ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.THROW_TRANSFER, "THROW");
            case CLASS_FACTORY ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.CLASS_CONSTRUCTION,
                    "CLASS_FACTORY");
            case INDEX_NORMALIZE ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.NO_DEAL_FAILURE,
                    "INDEX_NORMALIZE");
            case JSON_FROM_CLASS ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.JSON_FROM_NULL,
                    "JSON_FROM_CLASS");
            case JSON_TO_CLASS ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.JSON_TO_ERROR,
                    "JSON_TO_CLASS");
            case EXTERNAL_ENTRY ->
                requirePolicy(unit, facts, op, policy, FailurePolicyId.NO_DEAL_FAILURE,
                    "EXTERNAL_ENTRY");
            case LOOP -> {
                ControlSelector selector = enumByName(ControlSelector.class,
                    optionalString(op.payload(), "selector"));
                if (selector != null && selector != ControlSelector.WHILE
                        && selector != ControlSelector.FOR) {
                    yield fail(unit, facts, R_POLICY_KIND, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_POLICY_KIND, "ControlSelector " + selector.name()
                            + " not allowed for LOOP (WHILE|FOR only)"));
                }
                yield requirePolicy(unit, facts, op, policy, FailurePolicyId.NO_DEAL_FAILURE,
                    "LOOP");
            }
            case BOUNDARY -> {
                // A BOUNDARY op's policy is the boundary-assignment table's
                // domain (R-BOUNDARY-TRIPLE), not this rule's.
                yield Optional.empty();
            }
            default -> {
                if (allowedPolicies(kind).contains(policy)) {
                    yield Optional.empty();
                }
                yield fail(unit, facts, R_POLICY_KIND, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_POLICY_KIND, "policy " + policy.name() + " not allowed for kind "
                        + kind.name()));
            }
        };
    }

    private static Optional<CompilerDiagnostic> requirePolicy(RawUnit unit, ComparisonFacts facts,
                                                              RawOp op, FailurePolicyId actual,
                                                              FailurePolicyId expected, String what) {
        if (actual != expected) {
            return fail(unit, facts, R_POLICY_KIND, SemanticCapability.FOUNDATION_VALUES,
                origin(R_POLICY_KIND, "policy " + actual.name() + " not allowed for " + what
                    + " (expected " + expected.name() + ")"));
        }
        return Optional.empty();
    }

    /**
     * The closed selector→policy rule for {@code UNARY} (parent
     * "selector→policy is fixed"): {@code INT32_NEG} →
     * {@code INT32_RESULT}; {@code NUMBER_NEG} and {@code BOOL_NOT} →
     * {@code NO_DEAL_FAILURE}. This method is the single source of the
     * assignment: the value-semantics primitive's row projection and the
     * lowerer's policy stamping read this table (never a copy), and the
     * gate cross-check asserts the primitive's rows agree with it for
     * every unary selector.
     */
    public static FailurePolicyId unaryPolicy(UnarySelector selector) {
        return selector == UnarySelector.INT32_NEG
            ? FailurePolicyId.INT32_RESULT : FailurePolicyId.NO_DEAL_FAILURE;
    }

    /**
     * The closed selector→policy table for {@code BINARY} (parent
     * "selector→policy is fixed"): {@code INT32_ADD/SUB/MUL} →
     * {@code INT32_RESULT}; {@code INT32_DIV_TRUNC/MOD_TRUNC} →
     * {@code INT32_DIVISOR_THEN_RESULT}; {@code INT32_POW} →
     * {@code INT32_EXPONENT_THEN_RESULT}; every {@code NUMBER_*} arithmetic
     * incl. {@code NUMBER_POW_IEEE} and every {@code INT32_*}/{@code NUMBER_*}
     * comparison → {@code NO_DEAL_FAILURE}. This method is the single
     * source of the assignment: the value-semantics primitive's row
     * projection and the lowerer's policy stamping read this table (never
     * a copy), and the gate cross-check asserts the primitive's rows agree
     * with it for every covered selector.
     */
    public static FailurePolicyId binaryPolicy(BinarySelector selector) {
        return switch (selector) {
            case INT32_ADD, INT32_SUB, INT32_MUL -> FailurePolicyId.INT32_RESULT;
            case INT32_DIV_TRUNC, INT32_MOD_TRUNC -> FailurePolicyId.INT32_DIVISOR_THEN_RESULT;
            case INT32_POW -> FailurePolicyId.INT32_EXPONENT_THEN_RESULT;
            case NUMBER_ADD, NUMBER_SUB, NUMBER_MUL, NUMBER_DIV_IEEE, NUMBER_MOD_FLOOR,
                 NUMBER_POW_IEEE, INT32_EQ, INT32_NE, INT32_LT, INT32_LE, INT32_GT, INT32_GE,
                 NUMBER_EQ, NUMBER_NE, NUMBER_LT, NUMBER_LE, NUMBER_GT, NUMBER_GE,
                 STRING_EQ, STRING_NE, STRING_LT, STRING_LE, STRING_GT, STRING_GE,
                 BOOLEAN_EQ, BOOLEAN_NE, NULL_EQ, NULL_NE, NULLABLE_EQ, NULLABLE_NE,
                 NULLABLE_NULL_EQ, NULLABLE_NULL_NE, REFERENCE_EQ, REFERENCE_NE,
                 BYTES_EQ, BYTES_NE ->
                FailurePolicyId.NO_DEAL_FAILURE;
        };
    }

    /**
     * The closed intrinsic→policy rule for {@code INTRINSIC_CALL} (parent
     * operation table): {@code INT_CONVERT} → {@code INT_CONVERSION};
     * {@code NUMBER_CONVERT} → {@code NUMBER_CONVERSION}. This method is
     * the single source of the assignment: the lowerer's policy stamping
     * reads it (never a copy).
     */
    public static FailurePolicyId intrinsicPolicy(IntrinsicKind intrinsic) {
        Objects.requireNonNull(intrinsic, "intrinsic must not be null");
        return intrinsic == IntrinsicKind.INT_CONVERT
            ? FailurePolicyId.INT_CONVERSION : FailurePolicyId.NUMBER_CONVERSION;
    }

    /**
     * The closed stdlib algorithm→policy table for {@code STDLIB_CALL}
     * (parent "Standard-library operation table"):
     * {@code CONSOLE_LOG}/{@code CONSOLE_ERROR} →
     * {@code INFRASTRUCTURE_ONLY}; {@code STRING_LENGTH} →
     * {@code INT32_RESULT}; {@code JSON_PARSE} →
     * {@code JSON_PARSE_SYNTAX}; {@code JSON_STRINGIFY} →
     * {@code JSON_TO_ERROR}; {@code MATH_SQRT} →
     * {@code SQRT_NEGATIVE}; {@code MATH_ABS_INT} and
     * {@code TIME_NOW_MILLIS} → {@code INT32_RESULT} (the declared
     * {@code int} return boundary is the single terminal of the
     * target-clock read, K7); every other id → {@code NO_DEAL_FAILURE}.
     * This method is the single source of the assignment: the lowerer's
     * {@code STDLIB_CALL} policy stamping reads this table (never a
     * copy) — exactly like the landed {@code unaryPolicy}/
     * {@code binaryPolicy}/{@code intrinsicPolicy} accessors.
     */
    public static FailurePolicyId stdlibPolicy(StdlibFunctionId function) {
        return switch (function) {
            case CONSOLE_LOG, CONSOLE_ERROR -> FailurePolicyId.INFRASTRUCTURE_ONLY;
            case STRING_LENGTH -> FailurePolicyId.INT32_RESULT;
            case STRING_SUBSTRING, STRING_CONTAINS, STRING_STARTS_WITH, STRING_ENDS_WITH,
                 STRING_REPLACE, STRING_SPLIT, STRING_TRIM, TABLE_KEYS, MATH_FLOOR, MATH_CEIL,
                 MATH_ABS_NUMBER, MATH_MIN_INT, MATH_MAX_INT -> FailurePolicyId.NO_DEAL_FAILURE;
            case JSON_PARSE -> FailurePolicyId.JSON_PARSE_SYNTAX;
            case JSON_STRINGIFY -> FailurePolicyId.JSON_TO_ERROR;
            case MATH_SQRT -> FailurePolicyId.SQRT_NEGATIVE;
            case MATH_ABS_INT, TIME_NOW_MILLIS -> FailurePolicyId.INT32_RESULT;
        };
    }

    /** The closed per-kind allowed failure-policy sets (parent operation rows). */
    private static Set<FailurePolicyId> allowedPolicies(SemanticOpKind kind) {
        return switch (kind) {
            case ARRAY_LENGTH -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.INT32_RESULT);
            case OPTIONAL_READ -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.TYPE_DESCRIPTOR);
            case ASYNC_START -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.ASYNC_OPERATION_HANDLE);
            case AWAIT -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.ASYNC_COMPLETION);
            case FOR_EACH -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.TYPE_DESCRIPTOR);
            case CLASS_NEW -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.CLASS_CONSTRUCTION);
            case MODULE_IMPORT -> Set.of(FailurePolicyId.NO_DEAL_FAILURE,
                FailurePolicyId.HOST_LOAD);
            default -> Set.of(FailurePolicyId.NO_DEAL_FAILURE);
        };
    }

    // -- R-BOUNDARY-TRIPLE -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkBoundaryTriple(RawUnit unit,
                                                                    ComparisonFacts facts,
                                                                    Map<String, RawUnit> closure) {
        // Direction (a): every BOUNDARY op's (kind, descriptor, policy)
        // triple against the closed boundary-assignment table.
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) != SemanticOpKind.BOUNDARY) {
                continue;
            }
            Optional<String> failure = cellOfBoundary(unit, op, closure);
            if (failure.isPresent()) {
                return fail(unit, facts, R_BOUNDARY_TRIPLE, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_BOUNDARY_TRIPLE, failure.get()));
            }
        }
        // Direction (b): every invocation shape's referenced boundary ids
        // and pinned counts (the table's cells).
        for (RawOp op : unit.ops()) {
            SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
            if (kind == null) {
                continue;
            }
            Optional<String> failure = switch (kind) {
                case CALL -> checkCallCells(unit, op, closure);
                case ASYNC_START -> checkAsyncStartCells(unit, op, closure);
                case CALLBACK_INVOKE -> checkCallbackCells(unit, op);
                case AWAIT -> checkAwaitCells(unit, op);
                case EXTERNAL_ENTRY -> checkEntryCells(unit, op);
                case CLASS_NEW -> checkClassNewCells(unit, op);
                case ARRAY_NEW -> checkArrayNewCells(unit, op);
                case INDEX_READ -> checkIndexReadCells(unit, op);
                default -> Optional.empty();
            };
            if (failure.isPresent()) {
                return fail(unit, facts, R_BOUNDARY_TRIPLE, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_BOUNDARY_TRIPLE, failure.get()));
            }
        }
        return Optional.empty();
    }

    /** The descriptor-kind rule: TYPE_DESCRIPTOR, FUNCTION_SIGNATURE for function descriptors. */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    /** True iff the boundary's policy equals the descriptor-kind rule for its descriptor. */
    private static boolean matchesDescriptorKind(RuntimeDescriptor descriptor, FailurePolicyId policy) {
        return policy == descriptorKindPolicy(descriptor);
    }

    /**
     * The closed boundary-assignment table cell for one BOUNDARY op:
     * returns empty on a matching cell and a failure description otherwise.
     */
    private static Optional<String> cellOfBoundary(RawUnit unit, RawOp boundary,
                                                   Map<String, RawUnit> closure) {
        BoundaryKind kind = enumByName(BoundaryKind.class,
            optionalString(boundary.payload(), "kind"));
        if (kind == null) {
            return Optional.empty(); // R-ENUM owns an out-of-set boundary kind.
        }
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (descriptor == null) {
            return Optional.empty(); // R-ENUM owns a malformed descriptor.
        }
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        if (policy == null) {
            return Optional.empty(); // R-ENUM/R-RESERVED-NAME owns the policy.
        }
        switch (kind) {
            case ARRAY_LITERAL_ELEMENT -> {
                if (policy != FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR) {
                    return Optional.of("ARRAY_LITERAL_ELEMENT boundary must carry "
                        + "ARRAY_ELEMENT_DESCRIPTOR, got " + policy.name());
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.ARRAY_NEW) {
                    return Optional.of("ARRAY_LITERAL_ELEMENT boundary outside an ARRAY_NEW");
                }
                return Optional.empty();
            }
            case ARRAY_ELEMENT_READ -> {
                if (policy != FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR) {
                    return Optional.of("ARRAY_ELEMENT_READ boundary must carry "
                        + "ARRAY_READ_INDEX_THEN_DESCRIPTOR, got " + policy.name());
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.INDEX_READ) {
                    return Optional.of("ARRAY_ELEMENT_READ boundary outside an INDEX_READ");
                }
                return Optional.empty();
            }
            case ARRAY_ELEMENT_ASSIGNMENT -> {
                if (policy != FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT) {
                    return Optional.of("ARRAY_ELEMENT_ASSIGNMENT boundary must carry "
                        + "ARRAY_WRITE_BOUNDS_THEN_ELEMENT, got " + policy.name());
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.ASSIGN
                        || !"ARRAY_SLOT".equals(optionalString(parent.payload(), "targetKind"))) {
                    return Optional.of("ARRAY_ELEMENT_ASSIGNMENT boundary outside an ASSIGN"
                        + " ARRAY_SLOT chain");
                }
                return Optional.empty();
            }
            case ARRAY_ELEMENT_DELETE -> {
                if (policy != FailurePolicyId.ARRAY_DELETE_BOUNDS) {
                    return Optional.of("ARRAY_ELEMENT_DELETE boundary must carry "
                        + "ARRAY_DELETE_BOUNDS, got " + policy.name());
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.DELETE
                        || !"ARRAY_SLOT".equals(optionalString(parent.payload(), "targetKind"))) {
                    return Optional.of("ARRAY_ELEMENT_DELETE boundary outside a DELETE"
                        + " ARRAY_SLOT chain");
                }
                return Optional.empty();
            }
            case JSON_FROM_FIELD -> {
                return policy == FailurePolicyId.JSON_FROM_NULL
                    ? Optional.empty()
                    : Optional.of("JSON_FROM_FIELD boundary must carry JSON_FROM_NULL, got "
                        + policy.name());
            }
            case JSON_TO_FIELD -> {
                return policy == FailurePolicyId.JSON_TO_ERROR
                    ? Optional.empty()
                    : Optional.of("JSON_TO_FIELD boundary must carry JSON_TO_ERROR, got "
                        + policy.name());
            }
            case ASYNC_COMPLETION -> {
                if (policy != FailurePolicyId.ASYNC_COMPLETION) {
                    return Optional.of("the completion position carries policy "
                        + policy.name() + ", expected ASYNC_COMPLETION");
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.AWAIT
                        || !boundary.opId().equals(
                            parseOptionalOpId(parent.payload(), "completionBoundaryOpId"))) {
                    return Optional.of("an ASYNC_COMPLETION boundary outside the single AWAIT "
                        + "completion position");
                }
                return Optional.empty();
            }
            case CLASS_LITERAL_FIELD, CLASS_DEFAULT_FIELD -> {
                if (!matchesDescriptorKind(descriptor, policy)) {
                    return Optional.of(kind.name() + " boundary policy " + policy.name()
                        + " violates the descriptor-kind rule");
                }
                RawOp parent = resolveParent(boundary, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.CLASS_NEW
                        || !classNewHasBoundary(parent, boundary.opId(), kind)) {
                    return Optional.of(kind.name() + " boundary outside a CLASS_NEW field list");
                }
                return Optional.empty();
            }
            case VARIABLE_DECLARATION, VARIABLE_ASSIGNMENT, CLASS_FIELD_ASSIGNMENT,
                 UNTYPED_CLASS_INPUT, OPTIONAL_FIELD_READ, CONTEXTUAL_TABLE_READ,
                 IMPORTED_MEMBER_READ, MODULE_EXPORT -> {
                return matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of(kind.name() + " boundary policy " + policy.name()
                        + " violates the descriptor-kind rule");
            }
            case FUNCTION_PARAMETER, FUNCTION_RETURN, STDLIB_PARAMETER, STDLIB_RETURN,
                 EXTERNAL_PARAMETER, EXTERNAL_RETURN, HOST_TO_DEAL, DEAL_TO_HOST -> {
                RawOp invocation = resolveEnclosingInvocation(boundary, unit, closure);
                if (invocation == null) {
                    return Optional.of(kind.name() + " boundary outside any invocation shape");
                }
                return invocationCell(unit, invocation, boundary, closure);
            }
        }
        return Optional.empty();
    }

    /** Resolves a boundary's enclosing invocation: its parent, or the RETURN's enclosing invocation. */
    private static RawOp resolveEnclosingInvocation(RawOp boundary, RawUnit unit,
                                                    Map<String, RawUnit> closure) {
        RawOp parent = resolveParent(boundary, unit, closure);
        if (parent == null) {
            return null;
        }
        if (enumByName(SemanticOpKind.class, parent.kind()) == SemanticOpKind.RETURN) {
            OpId enclosing = parseOptionalOpId(parent.payload(), "enclosingInvocationOpId");
            if (enclosing == null) {
                return null;
            }
            return resolveOp(enclosing, unit, closure);
        }
        return parent;
    }

    private static Optional<String> invocationCell(RawUnit unit, RawOp invocation, RawOp boundary,
                                                   Map<String, RawUnit> closure) {
        SemanticOpKind invocationKind =
            enumByName(SemanticOpKind.class, invocation.kind());
        if (invocationKind == null) {
            return Optional.empty(); // R-PRIVATE-STEP owns the parent's kind.
        }
        return switch (invocationKind) {
            case CALL -> callCell(unit, invocation, boundary, closure);
            case ASYNC_START -> asyncCell(unit, invocation, boundary, closure);
            case CALLBACK_INVOKE -> callbackCell(unit, invocation, boundary);
            case STDLIB_CALL -> stdlibCell(boundary);
            case EXTERNAL_ENTRY -> entryCell(unit, invocation, boundary);
            case CLASS_NEW -> classNewCell(unit, invocation, boundary);
            case CLOSURE_NEW, RECURSIVE_GROUP_INIT ->
                bodyLocalReturnCell(unit, invocation, boundary, closure);
            case CLASS_FACTORY, INTRINSIC_CALL ->
                Optional.of("a boundary parented to " + invocationKind.name()
                    + " is outside the closed table (zero boundary children)");
            default -> Optional.of("a boundary parented to " + invocationKind.name()
                + " is outside the closed table");
        };
    }

    /**
     * The body-local return cell of the closed boundary-assignment table
     * (ISSUE-0635; design sources
     * {@code project-lowering-entry-and-registration-seeds} D9 and the
     * body-invocation identity contract, and
     * {@code semantic-ir-construct-coverage-cutover} K12's lowering side):
     * a body with no statically materialized invocation names its
     * function-value creation op ({@code CLOSURE_NEW} or
     * {@code RECURSIVE_GROUP_INIT}) as its {@code RETURN}'s enclosing
     * invocation, because the creation op took over the body's reserved
     * invocation identity. The cell admits exactly one
     * {@code FUNCTION_RETURN} boundary per body:
     *
     * <ol>
     *   <li>the boundary is parented to the body's {@code RETURN} and
     *       equals that {@code RETURN}'s {@code returnBoundaryOpId};</li>
     *   <li>the creation-op match holds: a {@code CLOSURE_NEW} identity
     *       allocates the returning function; a
     *       {@code RECURSIVE_GROUP_INIT} identity publishes it as a
     *       member;</li>
     *   <li>the body has no assigned invocation shape: no statically
     *       materialized invocation op of the closure names the boundary
     *       as its return boundary (a dynamic call's recorded cells are
     *       not a statically materialized invocation, so a body reached
     *       only through its value keeps the cell);</li>
     *   <li>it is the body's single return boundary: every {@code RETURN}
     *       of the same function names it;</li>
     *   <li>the boundary is {@code FUNCTION_RETURN} under the
     *       descriptor-kind rule on the allocated function's declared
     *       return descriptor ({@code CLOSURE_NEW} carries the signature;
     *       the group publication carries no per-member signature, so the
     *       group arm pins the descriptor-kind rule and the member
     *       identity).</li>
     * </ol>
     *
     * @param unit      the boundary's unit; non-null
     * @param creation  the creation op the {@code RETURN} names; non-null
     * @param boundary  the boundary op under check; non-null
     * @param closure   the project closure units by module path; non-null
     * @return empty on a matching cell, otherwise a failure description
     */
    private static Optional<String> bodyLocalReturnCell(RawUnit unit, RawOp creation,
                                                        RawOp boundary,
                                                        Map<String, RawUnit> closure) {
        RawOp parent = resolveParent(boundary, unit, closure);
        if (parent == null
                || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.RETURN) {
            return Optional.of("the body-local return boundary must be parented to the "
                + "body's RETURN");
        }
        OpId returnBoundary = parseOptionalOpId(parent.payload(), "returnBoundaryOpId");
        if (returnBoundary == null || !boundary.opId().equals(returnBoundary)) {
            return Optional.of("the body-local boundary must be the RETURN's "
                + "returnBoundaryOpId");
        }
        FunctionId function = parseFunctionId(parent.payload(), "function");
        if (function == null) {
            return Optional.empty(); // R-ENUM owns a malformed function position.
        }
        SemanticOpKind creationKind = enumByName(SemanticOpKind.class, creation.kind());
        if (creationKind == SemanticOpKind.CLOSURE_NEW) {
            FunctionId allocated = parseFunctionId(creation.payload(), "function");
            if (allocated == null) {
                return Optional.empty();
            }
            if (!allocated.equals(function)) {
                return Optional.of("the body-local identity must be the CLOSURE_NEW of the "
                    + "returning function (the creation op allocates another body)");
            }
        } else if (!groupFunctionIds(creation).contains(function)) {
            return Optional.of("the body-local identity must be the RECURSIVE_GROUP_INIT "
                + "publishing the returning function (the group names another member "
                + "set)");
        }
        for (RawUnit owner : unitsOf(unit, closure)) {
            for (RawOp candidate : owner.ops()) {
                if (staticallyMaterializes(candidate, boundary.opId())) {
                    return Optional.of("a body-local identity on a body with an assigned "
                        + "invocation shape (the statically materialized invocation op "
                        + "must carry the reserved identity)");
                }
            }
        }
        for (RawOp candidate : unit.ops()) {
            if (enumByName(SemanticOpKind.class, candidate.kind()) != SemanticOpKind.RETURN) {
                continue;
            }
            FunctionId returned = parseFunctionId(candidate.payload(), "function");
            if (returned == null || !returned.equals(function)) {
                continue;
            }
            OpId candidateBoundary = parseOptionalOpId(candidate.payload(),
                "returnBoundaryOpId");
            if (!boundary.opId().equals(candidateBoundary)) {
                return Optional.of("the body's single return boundary (two return "
                    + "boundaries for one body)");
            }
        }
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (policy == null || descriptor == null) {
            return Optional.empty(); // R-ENUM/R-POLICY-KIND own those positions.
        }
        if (!isKind(boundary, BoundaryKind.FUNCTION_RETURN)) {
            return Optional.of("the body-local return boundary must be FUNCTION_RETURN");
        }
        if (!matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the body-local FUNCTION_RETURN boundary must check the "
                + "allocated function's declared return descriptor under the "
                + "descriptor-kind rule");
        }
        RuntimeDescriptor.Func signature = parseFuncQuiet(optionalString(creation.payload(),
            "signature"));
        if (signature != null && !signature.returnType().equals(descriptor)) {
            return Optional.of("the body-local FUNCTION_RETURN boundary must check the "
                + "allocated function's declared return descriptor");
        }
        return Optional.empty();
    }

    /**
     * Whether one op is a statically materialized invocation of a body
     * whose return boundary is the given boundary op id — the witness of
     * an assigned invocation shape (a {@code CALL}/{@code ASYNC_START} of
     * a non-dynamic callee, a {@code CALLBACK_INVOKE}, or an
     * {@code EXTERNAL_ENTRY}). A dynamic callee's recorded return cells
     * are not a statically materialized invocation.
     */
    private static boolean staticallyMaterializes(RawOp op, OpId boundaryOpId) {
        SemanticOpKind kind = enumByName(SemanticOpKind.class, op.kind());
        if (kind == null) {
            return false;
        }
        return switch (kind) {
            case CALL, ASYNC_START -> !isDynamicCallee(op)
                && boundaryOpId.equals(parseOptionalOpId(op.payload(),
                    "returnBoundaryOpId"));
            case CALLBACK_INVOKE, EXTERNAL_ENTRY -> boundaryOpId.equals(
                parseOptionalOpId(op.payload(), "returnBoundaryOpId"));
            default -> false;
        };
    }

    /** The unit and its closure units (one iterable set of op owners). */
    private static List<RawUnit> unitsOf(RawUnit unit, Map<String, RawUnit> closure) {
        List<RawUnit> units = new ArrayList<>();
        units.add(unit);
        if (closure != null) {
            for (Map.Entry<String, RawUnit> entry : closure.entrySet()) {
                if (entry.getValue() != null
                        && !entry.getKey().equals(unit.modulePath())) {
                    units.add(entry.getValue());
                }
            }
        }
        return units;
    }

    /** Parses a payload's function-id position ({@code null} when absent/malformed). */
    private static FunctionId parseFunctionId(CanonicalJson.Obj payload, String key) {
        CanonicalJson.Value value = payloadValue(payload, key);
        if (!(value instanceof CanonicalJson.Obj idObj)) {
            return null;
        }
        return parseFunctionIdObject(idObj);
    }

    /** Parses one function semantic-id object ({@code null} when malformed). */
    private static FunctionId parseFunctionIdObject(CanonicalJson.Obj idObj) {
        CanonicalJson.Value id = payloadValue(idObj, "id");
        if (!(id instanceof CanonicalJson.Int number)) {
            return null;
        }
        return new FunctionId(number.value());
    }

    /** The member function ids of a {@code RECURSIVE_GROUP_INIT} payload. */
    private static List<FunctionId> groupFunctionIds(RawOp group) {
        CanonicalJson.Value value = payloadValue(group.payload(), "functions");
        if (!(value instanceof CanonicalJson.Arr functions)) {
            return List.of();
        }
        List<FunctionId> ids = new ArrayList<>();
        for (CanonicalJson.Value item : functions.items()) {
            if (item instanceof CanonicalJson.Obj obj) {
                FunctionId id = parseFunctionIdObject(obj);
                if (id != null) {
                    ids.add(id);
                }
            }
        }
        return ids;
    }

    private static Optional<String> callCell(RawUnit unit, RawOp call, RawOp boundary,
                                             Map<String, RawUnit> closure) {
        CallMode mode = enumByName(CallMode.class, optionalString(call.payload(), "mode"));
        if (mode == null) {
            return Optional.empty(); // R-ENUM owns the mode.
        }
        RuntimeDescriptor.Func signature = parseFuncQuiet(optionalString(call.payload(), "signature"));
        if (signature == null) {
            return Optional.empty(); // R-ENUM owns the signature.
        }
        List<OpId> params = parseOpIdList(call.payload(), "parameterBoundaryOpIds");
        OpId ret = parseOptionalOpId(call.payload(), "returnBoundaryOpId");
        int index = params.indexOf(boundary.opId());
        boolean isReturn = boundary.opId().equals(ret);
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (isDynamicCallee(call)) {
            // The dynamic set replaces the single return id: a boundary is
            // "part of" the invocation when it is a parameter boundary or
            // one of the three recorded return cells.
            return dynamicCallCell(call, boundary, mode, signature, index, isReturn, policy,
                descriptor);
        }
        if (recordsDynamicReturnBoundary(call)) {
            return Optional.of("only a DYNAMIC callee records the dynamic return-boundary set");
        }
        if (!isReturn && index < 0) {
            return Optional.of("boundary not part of the invocation's parameter/return lists");
        }
        return switch (mode) {
            case DIRECT -> directCallCell(call, boundary, signature, index, isReturn, policy,
                descriptor);
            case HOST -> hostCallCell(call, boundary, signature, index, isReturn, policy,
                descriptor);
            case INDIRECT -> {
                BindingInfo binding = resolveCalleeBinding(unit, call, closure);
                if (binding == null) {
                    yield Optional.empty(); // unresolvable callee: indeterminate.
                }
                yield switch (binding.shape()) {
                    case "loweredBody" -> directCallCell(call, boundary, signature, index,
                        isReturn, policy, descriptor);
                    case "adapter" -> adapterCallCell(call, boundary, signature, index,
                        isReturn, policy, descriptor);
                    case "hostFunction", "hostFunctionValue" -> hostCallCell(call, boundary,
                        signature, index, isReturn, policy, descriptor);
                    case "externalFunction" -> externalCallCell(call, boundary, signature, index,
                        isReturn, policy, descriptor, binding.executionOwner());
                    default -> Optional.empty();
                };
            }
            case EXTERNAL -> {
                BindingInfo binding = resolveCalleeBinding(unit, call, closure);
                if (binding == null || !"externalFunction".equals(binding.shape())) {
                    yield Optional.empty();
                }
                yield externalCallCell(call, boundary, signature, index, isReturn, policy,
                    descriptor, binding.executionOwner());
            }
        };
    }

    /**
     * The DYNAMIC-callee arm of the closed table (ISSUE-0531): the
     * recorded return-boundary set replaces the single
     * {@code returnBoundaryOpId}, and each recorded cell must carry the
     * closed cell of its runtime resolution class —
     * {@code FUNCTION_RETURN} (DEAL body, executed by the callee's
     * source RETURN), {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN}
     * (host, executed by the call op), or {@code EXTERNAL_RETURN}
     * (retained-ABI external, executed by the call op). A
     * {@code SHARED_BODY} external resolution executes zero caller-side
     * return boundaries (the callee's RETURN under its
     * {@code EXTERNAL_ENTRY} runs the single {@code EXTERNAL_RETURN} in
     * the callee unit), so the set records no entry for it. Parameter
     * boundaries of a dynamically resolved site are selected by the
     * runtime resolution as well and stay outside the return-boundary
     * reconciliation.
     */
    private static Optional<String> dynamicCallCell(RawOp call, RawOp boundary, CallMode mode,
                                                    RuntimeDescriptor.Func signature, int index,
                                                    boolean isReturn, FailurePolicyId policy,
                                                    RuntimeDescriptor descriptor) {
        if (mode != CallMode.INDIRECT) {
            return Optional.of("a DYNAMIC callee is admissible only under CallMode INDIRECT");
        }
        KindPayload.DynamicReturnBoundary recorded = parseDynamicReturnBoundary(call);
        if (recorded == null) {
            return Optional.empty(); // checkCallCells owns the record-presence defect.
        }
        isReturn = isReturn
            || boundary.opId().equals(recorded.dealBodyBoundaryOpId())
            || boundary.opId().equals(recorded.hostBoundaryOpId())
            || boundary.opId().equals(recorded.externalBoundaryOpId());
        if (!isReturn) {
            if (index >= 0) {
                return Optional.empty(); // parameters: runtime-selected boundary family.
            }
            return Optional.of("boundary not part of the invocation's parameter/return lists");
        }
        if (boundary.opId().equals(recorded.dealBodyBoundaryOpId())) {
            if (!isKind(boundary, BoundaryKind.FUNCTION_RETURN)) {
                return Optional.of("the DYNAMIC CALL's DEAL-body return boundary must be "
                    + "FUNCTION_RETURN");
            }
            if (!signature.returnType().equals(descriptor)
                    || !matchesDescriptorKind(descriptor, policy)) {
                return Optional.of("the DYNAMIC CALL's DEAL-body FUNCTION_RETURN boundary must "
                    + "check the declared return descriptor under the descriptor-kind rule");
            }
            return Optional.empty();
        }
        if (boundary.opId().equals(recorded.hostBoundaryOpId())) {
            if (!isKind(boundary, BoundaryKind.HOST_TO_DEAL)
                    || policy != FailurePolicyId.HOST_SYNC_RETURN
                    || !signature.returnType().equals(descriptor)) {
                return Optional.of("the DYNAMIC CALL's host return boundary must be "
                    + "HOST_TO_DEAL + HOST_SYNC_RETURN on the declared return descriptor");
            }
            return Optional.empty();
        }
        if (boundary.opId().equals(recorded.externalBoundaryOpId())) {
            if (!isKind(boundary, BoundaryKind.EXTERNAL_RETURN)
                    || !signature.returnType().equals(descriptor)
                    || !matchesDescriptorKind(descriptor, policy)) {
                return Optional.of("the DYNAMIC CALL's retained-ABI return boundary must be "
                    + "EXTERNAL_RETURN under the descriptor-kind rule on the declared return "
                    + "descriptor");
            }
            return Optional.empty();
        }
        return Optional.of("boundary not part of the invocation's parameter/return lists");
    }

    private static Optional<String> directCallCell(RawOp call, RawOp boundary,
                                                   RuntimeDescriptor.Func signature, int index,
                                                   boolean isReturn, FailurePolicyId policy,
                                                   RuntimeDescriptor descriptor) {
        if (isReturn) {
            if (!isKind(boundary, BoundaryKind.FUNCTION_RETURN)) {
                return Optional.of("the return boundary of a body call must be FUNCTION_RETURN");
            }
            if (!signature.returnType().equals(descriptor)
                    || !matchesDescriptorKind(descriptor, policy)) {
                return Optional.of("the FUNCTION_RETURN boundary of a body call must check the "
                    + "declared return descriptor under the descriptor-kind rule");
            }
            return Optional.empty();
        }
        if (index >= signature.paramTypes().size()) {
            return Optional.of("parameter boundary index " + index + " outside the signature");
        }
        if (!isKind(boundary, BoundaryKind.FUNCTION_PARAMETER)) {
            return Optional.of("parameter boundaries of a body call must be FUNCTION_PARAMETER");
        }
        if (!signature.paramTypes().get(index).equals(descriptor)
                || !matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the FUNCTION_PARAMETER boundary " + index + " must check the "
                + "declared parameter descriptor under the descriptor-kind rule");
        }
        return Optional.empty();
    }

    private static Optional<String> hostCallCell(RawOp call, RawOp boundary,
                                                 RuntimeDescriptor.Func signature, int index,
                                                 boolean isReturn, FailurePolicyId policy,
                                                 RuntimeDescriptor descriptor) {
        if (isReturn) {
            if (!isKind(boundary, BoundaryKind.HOST_TO_DEAL)
                    || policy != FailurePolicyId.HOST_SYNC_RETURN
                    || !signature.returnType().equals(descriptor)) {
                return Optional.of("the sync return of a host call must be HOST_TO_DEAL + "
                    + "HOST_SYNC_RETURN on the declared return descriptor");
            }
            return Optional.empty();
        }
        if (index >= signature.paramTypes().size()
                || !isKind(boundary, BoundaryKind.DEAL_TO_HOST)
                || policy != FailurePolicyId.HOST_PARAMETER
                || !signature.paramTypes().get(index).equals(descriptor)) {
            return Optional.of("host-call parameters must be DEAL_TO_HOST + HOST_PARAMETER on "
                + "the declared parameter descriptor");
        }
        return Optional.empty();
    }

    private static Optional<String> adapterCallCell(RawOp call, RawOp boundary,
                                                    RuntimeDescriptor.Func signature, int index,
                                                    boolean isReturn, FailurePolicyId policy,
                                                    RuntimeDescriptor descriptor) {
        if (isReturn) {
            // The source kind is not recorded on the adapter binding; every
            // per-source return cell of the closed table is admissible.
            if (isKind(boundary, BoundaryKind.FUNCTION_RETURN)) {
                return signature.returnType().equals(descriptor)
                        && matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of("the adapter FUNCTION_RETURN boundary must check the "
                        + "declared return descriptor under the descriptor-kind rule");
            }
            if (isKind(boundary, BoundaryKind.HOST_TO_DEAL)) {
                return policy == FailurePolicyId.HOST_SYNC_RETURN
                        && signature.returnType().equals(descriptor)
                    ? Optional.empty()
                    : Optional.of("the adapter host-source return must be HOST_TO_DEAL + "
                        + "HOST_SYNC_RETURN on the declared return descriptor");
            }
            if (isKind(boundary, BoundaryKind.EXTERNAL_RETURN)) {
                return signature.returnType().equals(descriptor)
                        && matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of("the adapter external-source return must be EXTERNAL_RETURN "
                        + "under the descriptor-kind rule on the declared return descriptor");
            }
            return Optional.of("the adapter return boundary kind is outside the closed table");
        }
        if (index >= signature.paramTypes().size()) {
            return Optional.of("parameter boundary index " + index + " outside the target signature");
        }
        if (!isKind(boundary, BoundaryKind.FUNCTION_PARAMETER)) {
            return Optional.of("adapter parameter boundaries must be FUNCTION_PARAMETER");
        }
        if (!signature.paramTypes().get(index).equals(descriptor)
                || !matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the adapter's xN target-signature FUNCTION_PARAMETER boundary "
                + index + " must check the declared parameter descriptor under the "
                + "descriptor-kind rule");
        }
        return Optional.empty();
    }

    private static Optional<String> externalCallCell(RawOp call, RawOp boundary,
                                                     RuntimeDescriptor.Func signature, int index,
                                                     boolean isReturn, FailurePolicyId policy,
                                                     RuntimeDescriptor descriptor,
                                                     String executionOwner) {
        if (isReturn) {
            if ("SHARED_BODY".equals(executionOwner)) {
                return Optional.of("a SHARED_BODY external call has no caller-side return "
                    + "boundary (the callee RETURN runs the single EXTERNAL_RETURN)");
            }
            if (!isKind(boundary, BoundaryKind.EXTERNAL_RETURN)
                    || !signature.returnType().equals(descriptor)
                    || !matchesDescriptorKind(descriptor, policy)) {
                return Optional.of("the RETAINED_ABI return boundary must be EXTERNAL_RETURN "
                    + "under the descriptor-kind rule on the declared return descriptor");
            }
            return Optional.empty();
        }
        if (index >= signature.paramTypes().size()) {
            return Optional.of("parameter boundary index " + index + " outside the signature");
        }
        if (!isKind(boundary, BoundaryKind.EXTERNAL_PARAMETER)) {
            return Optional.of("external-call parameters must be EXTERNAL_PARAMETER");
        }
        if (!signature.paramTypes().get(index).equals(descriptor)
                || !matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the EXTERNAL_PARAMETER boundary " + index + " must check the "
                + "declared parameter descriptor under the descriptor-kind rule");
        }
        return Optional.empty();
    }

    private static Optional<String> asyncCell(RawUnit unit, RawOp start, RawOp boundary,
                                              Map<String, RawUnit> closure) {
        AsyncStartSource source =
            enumByName(AsyncStartSource.class, optionalString(start.payload(), "source"));
        if (source == null) {
            return Optional.empty();
        }
        ParameterBoundaryMode mode = enumByName(ParameterBoundaryMode.class,
            optionalString(start.payload(), "parameterBoundaryMode"));
        if (mode == null) {
            return Optional.empty();
        }
        RuntimeDescriptor completion = parseDescriptorQuiet(
            optionalString(start.payload(), "completionDescriptor"));
        if (completion == null) {
            return Optional.empty();
        }
        List<OpId> params = parseOpIdList(start.payload(), "parameterBoundaryOpIds");
        OpId ret = parseOptionalOpId(start.payload(), "returnBoundaryOpId");
        int index = params.indexOf(boundary.opId());
        boolean isReturn = boundary.opId().equals(ret);
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        BindingInfo binding = resolveCalleeBinding(unit, start, closure);
        if (binding == null) {
            if (isDynamicCallee(start)) {
                return dynamicAsyncCell(start, boundary, source, completion, index, isReturn,
                    ret != null, policy, descriptor);
            }
            return Optional.empty();
        }
        if (!isReturn && index < 0) {
            return Optional.of("boundary not part of the ASYNC_START parameter/return lists");
        }
        return switch (binding.shape()) {
            case "loweredBody" -> {
                if (isReturn) {
                    yield isKind(boundary, BoundaryKind.FUNCTION_RETURN)
                            && completion.equals(descriptor)
                            && matchesDescriptorKind(descriptor, policy)
                        ? Optional.empty()
                        : Optional.of("the DEAL_BODY task return must be FUNCTION_RETURN under "
                            + "the descriptor-kind rule on the declared return descriptor");
                }
                yield isKind(boundary, BoundaryKind.FUNCTION_PARAMETER)
                        && matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of("the DEAL_BODY parameter boundary must be FUNCTION_PARAMETER "
                        + "under the descriptor-kind rule");
            }
            case "adapter" -> {
                if (isReturn) {
                    yield Optional.of("the outer adapter-over-async task runs zero return "
                        + "boundaries (delegation)");
                }
                RuntimeDescriptor.Func target = parseFuncQuiet(binding.targetSignature());
                if (target == null) {
                    yield Optional.empty();
                }
                yield index < target.paramTypes().size()
                        && isKind(boundary, BoundaryKind.FUNCTION_PARAMETER)
                        && target.paramTypes().get(index).equals(descriptor)
                        && matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of("the adapter-over-async xN target-signature "
                        + "FUNCTION_PARAMETER boundary " + index + " must check the declared "
                        + "parameter descriptor under the descriptor-kind rule");
            }
            case "hostFunction", "hostFunctionValue" -> {
                if (isReturn) {
                    yield Optional.of("ASYNC_START(HOST) runs zero return boundaries");
                }
                yield isKind(boundary, BoundaryKind.DEAL_TO_HOST)
                        && policy == FailurePolicyId.HOST_PARAMETER
                    ? Optional.empty()
                    : Optional.of("ASYNC_START(HOST) parameters must be DEAL_TO_HOST + "
                        + "HOST_PARAMETER");
            }
            case "externalFunction" -> {
                if (isReturn) {
                    yield Optional.of("ASYNC_START(EXTERNAL) runs zero caller-side return "
                        + "boundaries (the callee task runs the single FUNCTION_RETURN)");
                }
                yield isKind(boundary, BoundaryKind.EXTERNAL_PARAMETER)
                        && matchesDescriptorKind(descriptor, policy)
                    ? Optional.empty()
                    : Optional.of("ASYNC_START(EXTERNAL) parameters must be EXTERNAL_PARAMETER "
                        + "under the descriptor-kind rule");
            }
            default -> Optional.empty();
        };
    }

    /**
     * The DYNAMIC-callee arm of the ASYNC_START cells (ISSUE-0531): the
     * recorded {@code source} is the closed {@code DEAL_BODY} projection
     * (the only resolution whose caller-recorded return boundary
     * executes) and the recorded return boundary is that resolution's
     * single {@code FUNCTION_RETURN} task cell; the runtime derives the
     * effective source from the resolved binding exactly like
     * {@code CALL(INDIRECT)}, and HOST/EXTERNAL/adapter-over-async
     * resolutions execute zero caller-side return boundaries.
     */
    private static Optional<String> dynamicAsyncCell(RawOp start, RawOp boundary,
                                                     AsyncStartSource source,
                                                     RuntimeDescriptor completion, int index,
                                                     boolean isReturn, boolean returnRecorded,
                                                     FailurePolicyId policy,
                                                     RuntimeDescriptor descriptor) {
        if (!returnRecorded) {
            return Optional.empty(); // checkAsyncStartCells owns the record-presence defect.
        }
        if (source != AsyncStartSource.DEAL_BODY) {
            return Optional.of("a DYNAMIC ASYNC_START records source DEAL_BODY (the only "
                + "resolution whose caller-recorded return boundary executes); the runtime "
                + "derives the effective source from the resolved binding");
        }
        if (!isReturn) {
            if (index >= 0) {
                return Optional.empty(); // parameters: runtime-selected boundary family.
            }
            return Optional.of("boundary not part of the ASYNC_START parameter/return lists");
        }
        return isKind(boundary, BoundaryKind.FUNCTION_RETURN)
                && completion.equals(descriptor)
                && matchesDescriptorKind(descriptor, policy)
            ? Optional.empty()
            : Optional.of("the DYNAMIC ASYNC_START's recorded task return boundary must be "
                + "FUNCTION_RETURN under the descriptor-kind rule on the completion "
                + "descriptor");
    }

    private static Optional<String> callbackCell(RawUnit unit, RawOp callback, RawOp boundary) {
        RuntimeDescriptor.Func descriptor = parseFuncQuiet(
            optionalString(callback.payload(), "descriptor"));
        if (descriptor == null) {
            return Optional.empty();
        }
        List<OpId> params = parseOpIdList(callback.payload(), "parameterBoundaryOpIds");
        OpId ret = parseOptionalOpId(callback.payload(), "returnBoundaryOpId");
        int index = params.indexOf(boundary.opId());
        boolean isReturn = boundary.opId().equals(ret);
        if (!isReturn && index < 0) {
            return Optional.of("boundary not part of the CALLBACK_INVOKE parameter/return lists");
        }
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor boundaryDescriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (isReturn) {
            return isKind(boundary, BoundaryKind.DEAL_TO_HOST)
                    && descriptor.returnType().equals(boundaryDescriptor)
                    && matchesDescriptorKind(boundaryDescriptor, policy)
                ? Optional.empty()
                : Optional.of("the callback return must be DEAL_TO_HOST under the "
                    + "descriptor-kind rule on the declared return descriptor");
        }
        return index < descriptor.paramTypes().size()
                && isKind(boundary, BoundaryKind.HOST_TO_DEAL)
                && descriptor.paramTypes().get(index).equals(boundaryDescriptor)
                && matchesDescriptorKind(boundaryDescriptor, policy)
            ? Optional.empty()
            : Optional.of("callback parameters must be HOST_TO_DEAL under the descriptor-kind "
                + "rule on the declared parameter descriptor");
    }

    private static Optional<String> stdlibCell(RawOp boundary) {
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (!isKind(boundary, BoundaryKind.STDLIB_PARAMETER)
                && !isKind(boundary, BoundaryKind.STDLIB_RETURN)) {
            return Optional.of("a boundary parented to STDLIB_CALL must be STDLIB_PARAMETER "
                + "or STDLIB_RETURN");
        }
        return matchesDescriptorKind(descriptor, policy)
            ? Optional.empty()
            : Optional.of("STDLIB_PARAMETER/STDLIB_RETURN boundaries use the descriptor-kind rule");
    }

    private static Optional<String> entryCell(RawUnit unit, RawOp entry, RawOp boundary) {
        RuntimeDescriptor.Func signature = parseFuncQuiet(optionalString(entry.payload(), "signature"));
        if (signature == null) {
            return Optional.empty();
        }
        OpId ret = parseOptionalOpId(entry.payload(), "returnBoundaryOpId");
        if (!boundary.opId().equals(ret)) {
            return Optional.of("boundary not the EXTERNAL_ENTRY's return boundary");
        }
        boolean async = isTrue(entry.payload(), "async");
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (async) {
            return isKind(boundary, BoundaryKind.FUNCTION_RETURN)
                    && signature.returnType().equals(descriptor)
                    && matchesDescriptorKind(descriptor, policy)
                ? Optional.empty()
                : Optional.of("the async EXTERNAL_ENTRY return must be FUNCTION_RETURN under "
                    + "the descriptor-kind rule on the declared return descriptor");
        }
        return isKind(boundary, BoundaryKind.EXTERNAL_RETURN)
                && signature.returnType().equals(descriptor)
                && matchesDescriptorKind(descriptor, policy)
            ? Optional.empty()
            : Optional.of("the sync EXTERNAL_ENTRY return must be EXTERNAL_RETURN under the "
                + "descriptor-kind rule on the declared return descriptor");
    }

    private static Optional<String> classNewCell(RawUnit unit, RawOp classNew, RawOp boundary) {
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        Optional<BoundaryKind> fieldKind = classNewBoundaryKind(classNew, boundary.opId());
        if (fieldKind.isEmpty()) {
            return Optional.of("boundary not a CLASS_NEW field boundary");
        }
        return matchesDescriptorKind(descriptor, policy)
            ? Optional.empty()
            : Optional.of("CLASS_LITERAL_FIELD/CLASS_DEFAULT_FIELD boundaries use the "
                + "descriptor-kind rule");
    }

    private static Optional<BoundaryKind> classNewBoundaryKind(RawOp classNew, OpId boundaryOpId) {
        CanonicalJson.Value value = payloadValue(classNew.payload(), "fieldBoundaries");
        if (!(value instanceof CanonicalJson.Arr boundaries)) {
            return Optional.empty();
        }
        for (CanonicalJson.Value item : boundaries.items()) {
            if (!(item instanceof CanonicalJson.Obj boundary)) {
                continue;
            }
            OpId id = parseOptionalOpId(boundary, "boundaryOpId");
            if (boundaryOpId.equals(id)) {
                BoundaryKind kind = enumByName(BoundaryKind.class,
                    optionalString(boundary, "kind"));
                if (kind == BoundaryKind.CLASS_LITERAL_FIELD
                        || kind == BoundaryKind.CLASS_DEFAULT_FIELD) {
                    return Optional.of(kind);
                }
                return Optional.empty();
            }
        }
        return Optional.empty();
    }

    private static boolean classNewHasBoundary(RawOp classNew, OpId boundaryOpId,
                                               BoundaryKind kind) {
        return classNewBoundaryKind(classNew, boundaryOpId).map(k -> k == kind).orElse(false);
    }

    // Direction (b): invocation-shape referenced-boundary and count checks.

    private static Optional<String> checkCallCells(RawUnit unit, RawOp call,
                                                   Map<String, RawUnit> closure) {
        CallMode mode = enumByName(CallMode.class, optionalString(call.payload(), "mode"));
        if (mode == null) {
            return Optional.empty();
        }
        RuntimeDescriptor.Func signature = parseFuncQuiet(optionalString(call.payload(), "signature"));
        if (signature == null) {
            return Optional.empty();
        }
        List<OpId> params = parseOpIdList(call.payload(), "parameterBoundaryOpIds");
        if (params.size() != signature.paramTypes().size()) {
            return Optional.of("CALL parameter boundaries (" + params.size()
                + ") must match the signature parameters (" + signature.paramTypes().size() + ")");
        }
        for (OpId param : params) {
            RawOp resolved = resolveOp(param, unit, closure);
            if (resolved == null) {
                return Optional.of("parameter boundary " + param + " does not resolve");
            }
            if (enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("parameter boundary " + param + " is not a BOUNDARY op");
            }
        }
        OpId ret = parseOptionalOpId(call.payload(), "returnBoundaryOpId");
        KindPayload.DynamicReturnBoundary dynamic = parseDynamicReturnBoundary(call);
        boolean dynamicCallee = isDynamicCallee(call);
        if (dynamicCallee) {
            if (dynamic == null) {
                return Optional.of("a DYNAMIC callee must record its dynamic return-boundary "
                    + "set (dealBodyBoundaryOpId, hostBoundaryOpId, externalBoundaryOpId)");
            }
            if (mode != CallMode.INDIRECT) {
                return Optional.of("a DYNAMIC callee is admissible only under CallMode "
                    + "INDIRECT");
            }
            if (ret != null) {
                return Optional.of("a DYNAMIC CALL records no single returnBoundaryOpId (the "
                    + "dynamic return-boundary set replaces it)");
            }
            return checkDynamicReturnCells(unit, call, dynamic, signature, closure);
        }
        if (recordsDynamicReturnBoundary(call)) {
            return Optional.of("only a DYNAMIC callee records the dynamic return-boundary set");
        }
        BindingInfo binding = resolveCalleeBinding(unit, call, closure);
        boolean sharedBodyExternal = binding != null
            && "externalFunction".equals(binding.shape())
            && "SHARED_BODY".equals(binding.executionOwner());
        if (sharedBodyExternal) {
            if (ret != null) {
                return Optional.of("a SHARED_BODY external CALL must carry no caller-side "
                    + "return boundary");
            }
            return Optional.empty();
        }
        if (mode == CallMode.EXTERNAL && binding == null) {
            return Optional.empty();
        }
        if (ret == null) {
            return Optional.of("the CALL must carry its single return boundary");
        }
        RawOp resolved = resolveOp(ret, unit, closure);
        if (resolved == null
                || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
            return Optional.of("return boundary " + ret + " does not resolve to a BOUNDARY op");
        }
        return Optional.empty();
    }

    /**
     * The DYNAMIC CALL's per-class return-cell checks (direction (b),
     * ISSUE-0531): each recorded entry must resolve to the BOUNDARY op
     * carrying the closed cell of its runtime resolution class — the
     * DEAL-body cell a FUNCTION_RETURN checking the declared return
     * descriptor under the descriptor-kind rule and parented to a
     * RETURN naming the CALL, the host cell HOST_TO_DEAL +
     * HOST_SYNC_RETURN on the declared return descriptor, and the
     * retained-ABI cell EXTERNAL_RETURN under the descriptor-kind rule
     * on the declared return descriptor — so the runtime selection can
     * never execute a cell whose actual kind/owner contradicts the
     * selection's pinned kind/owner. The three entries must be
     * mutually distinct.
     */
    private static Optional<String> checkDynamicReturnCells(RawUnit unit, RawOp call,
                                                            KindPayload.DynamicReturnBoundary dynamic,
                                                            RuntimeDescriptor.Func signature,
                                                            Map<String, RawUnit> closure) {
        OpId dealEntry = dynamic.dealBodyBoundaryOpId();
        OpId hostEntry = dynamic.hostBoundaryOpId();
        OpId externalEntry = dynamic.externalBoundaryOpId();
        if (dealEntry.equals(hostEntry) || dealEntry.equals(externalEntry)
                || hostEntry.equals(externalEntry)) {
            return Optional.of("the DYNAMIC CALL's three dynamic return-boundary entries must "
                + "be mutually distinct");
        }
        Optional<String> deal = dynamicDealReturnCell(unit, call, dealEntry, signature, closure);
        if (deal.isPresent()) {
            return deal;
        }
        Optional<String> host = dynamicHostReturnCell(unit, call, hostEntry, signature, closure);
        if (host.isPresent()) {
            return host;
        }
        return dynamicExternalReturnCell(unit, call, externalEntry, signature, closure);
    }

    /** A resolved recorded dynamic return entry: the BOUNDARY op, or the resolution failure. */
    private record ResolvedDynamicEntry(RawOp boundary, String failure) {

        static ResolvedDynamicEntry of(RawUnit unit, OpId entry,
                                       Map<String, RawUnit> closure) {
            RawOp resolved = resolveOp(entry, unit, closure);
            if (resolved == null) {
                if (closure.isEmpty()
                        && !entry.module().path().equals(unit.modulePath())) {
                    return new ResolvedDynamicEntry(null, null); // unit-level: indeterminate.
                }
                return new ResolvedDynamicEntry(null,
                    "dynamic return boundary " + entry + " does not resolve");
            }
            if (enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return new ResolvedDynamicEntry(null,
                    "dynamic return boundary " + entry + " is not a BOUNDARY op");
            }
            return new ResolvedDynamicEntry(resolved, null);
        }
    }

    /** The DEAL-body cell of a DYNAMIC CALL (direction (b)). */
    private static Optional<String> dynamicDealReturnCell(RawUnit unit, RawOp call, OpId entry,
                                                          RuntimeDescriptor.Func signature,
                                                          Map<String, RawUnit> closure) {
        ResolvedDynamicEntry resolved = ResolvedDynamicEntry.of(unit, entry, closure);
        if (resolved.failure() != null) {
            return Optional.of(resolved.failure());
        }
        if (resolved.boundary() == null) {
            return Optional.empty(); // unit-level: foreign-module entries are indeterminate.
        }
        RawOp boundary = resolved.boundary();
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (!isKind(boundary, BoundaryKind.FUNCTION_RETURN)) {
            return Optional.of("the DYNAMIC CALL's DEAL-body return boundary must be "
                + "FUNCTION_RETURN");
        }
        if (!signature.returnType().equals(descriptor)
                || !matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the DYNAMIC CALL's DEAL-body FUNCTION_RETURN boundary must "
                + "check the declared return descriptor under the descriptor-kind rule");
        }
        RawOp parent = resolveParent(boundary, unit, closure);
        if (parent == null
                || enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.RETURN
                || !call.opId().equals(parseOptionalOpId(parent.payload(),
                    "enclosingInvocationOpId"))) {
            return Optional.of("the DYNAMIC CALL's DEAL-body return boundary must be parented "
                + "to a RETURN naming the CALL");
        }
        return Optional.empty();
    }

    /** The host cell of a DYNAMIC CALL (direction (b)). */
    private static Optional<String> dynamicHostReturnCell(RawUnit unit, RawOp call, OpId entry,
                                                          RuntimeDescriptor.Func signature,
                                                          Map<String, RawUnit> closure) {
        ResolvedDynamicEntry resolved = ResolvedDynamicEntry.of(unit, entry, closure);
        if (resolved.failure() != null) {
            return Optional.of(resolved.failure());
        }
        if (resolved.boundary() == null) {
            return Optional.empty();
        }
        RawOp boundary = resolved.boundary();
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (!isKind(boundary, BoundaryKind.HOST_TO_DEAL)
                || policy != FailurePolicyId.HOST_SYNC_RETURN
                || !signature.returnType().equals(descriptor)) {
            return Optional.of("the DYNAMIC CALL's host return boundary must be HOST_TO_DEAL "
                + "+ HOST_SYNC_RETURN on the declared return descriptor");
        }
        return Optional.empty();
    }

    /** The retained-ABI external cell of a DYNAMIC CALL (direction (b)). */
    private static Optional<String> dynamicExternalReturnCell(RawUnit unit, RawOp call,
                                                              OpId entry,
                                                              RuntimeDescriptor.Func signature,
                                                              Map<String, RawUnit> closure) {
        ResolvedDynamicEntry resolved = ResolvedDynamicEntry.of(unit, entry, closure);
        if (resolved.failure() != null) {
            return Optional.of(resolved.failure());
        }
        if (resolved.boundary() == null) {
            return Optional.empty();
        }
        RawOp boundary = resolved.boundary();
        FailurePolicyId policy = enumByName(FailurePolicyId.class, boundary.failurePolicy());
        RuntimeDescriptor descriptor = parseDescriptorQuiet(
            optionalString(boundary.payload(), "descriptor"));
        if (!isKind(boundary, BoundaryKind.EXTERNAL_RETURN)
                || !signature.returnType().equals(descriptor)
                || !matchesDescriptorKind(descriptor, policy)) {
            return Optional.of("the DYNAMIC CALL's retained-ABI return boundary must be "
                + "EXTERNAL_RETURN under the descriptor-kind rule on the declared return "
                + "descriptor");
        }
        return Optional.empty();
    }

    private static Optional<String> checkAsyncStartCells(RawUnit unit, RawOp start,
                                                         Map<String, RawUnit> closure) {
        ParameterBoundaryMode mode = enumByName(ParameterBoundaryMode.class,
            optionalString(start.payload(), "parameterBoundaryMode"));
        if (mode == null) {
            return Optional.empty();
        }
        List<OpId> params = parseOpIdList(start.payload(), "parameterBoundaryOpIds");
        BindingInfo binding = resolveCalleeBinding(unit, start, closure);
        if (mode == ParameterBoundaryMode.ELIDED_BY_ADAPTER) {
            if (!params.isEmpty()) {
                return Optional.of("the nested source ASYNC_START of an adapter-over-async task "
                    + "runs zero parameter boundaries (ELIDED_BY_ADAPTER)");
            }
        } else if (binding != null && !"loweredBody".equals(binding.shape())) {
            int expected = expectedParamCount(binding);
            if (expected >= 0 && params.size() != expected) {
                return Optional.of("ASYNC_START parameter boundaries (" + params.size()
                    + ") must match the resolved signature parameters (" + expected + ")");
            }
        }
        for (OpId param : params) {
            RawOp resolved = resolveOp(param, unit, closure);
            if (resolved == null) {
                return Optional.of("parameter boundary " + param + " does not resolve");
            }
            if (enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("parameter boundary " + param + " is not a BOUNDARY op");
            }
        }
        OpId ret = parseOptionalOpId(start.payload(), "returnBoundaryOpId");
        if (binding == null) {
            if (isDynamicCallee(start)) {
                if (ret == null) {
                    return Optional.of("a DYNAMIC ASYNC_START must record its DEAL_BODY task "
                        + "return boundary (the DEAL_BODY resolution executes exactly one "
                        + "FUNCTION_RETURN; host/external/adapter resolutions execute zero "
                        + "caller-side return boundaries)");
                }
                RawOp resolved = resolveOp(ret, unit, closure);
                if (resolved == null) {
                    if (closure.isEmpty()
                            && !ret.module().path().equals(unit.modulePath())) {
                        return Optional.empty(); // unit-level: foreign entries indeterminate.
                    }
                    return Optional.of("return boundary " + ret + " does not resolve");
                }
                if (enumByName(SemanticOpKind.class, resolved.kind())
                        != SemanticOpKind.BOUNDARY) {
                    return Optional.of("return boundary " + ret
                        + " does not resolve to a BOUNDARY op");
                }
                RuntimeDescriptor completion = parseDescriptorQuiet(
                    optionalString(start.payload(), "completionDescriptor"));
                if (completion == null) {
                    return Optional.empty(); // R-ENUM owns a malformed completion descriptor.
                }
                FailurePolicyId policy = enumByName(FailurePolicyId.class,
                    resolved.failurePolicy());
                RuntimeDescriptor descriptor = parseDescriptorQuiet(
                    optionalString(resolved.payload(), "descriptor"));
                if (!isKind(resolved, BoundaryKind.FUNCTION_RETURN)
                        || !completion.equals(descriptor)
                        || !matchesDescriptorKind(descriptor, policy)) {
                    return Optional.of("the DYNAMIC ASYNC_START's recorded task return "
                        + "boundary must be FUNCTION_RETURN under the descriptor-kind rule "
                        + "on the completion descriptor");
                }
                RawOp parent = resolveParent(resolved, unit, closure);
                if (parent == null
                        || enumByName(SemanticOpKind.class, parent.kind())
                            != SemanticOpKind.RETURN
                        || !start.opId().equals(parseOptionalOpId(parent.payload(),
                            "enclosingInvocationOpId"))) {
                    return Optional.of("the DYNAMIC ASYNC_START's recorded task return "
                        + "boundary must be parented to a RETURN naming the ASYNC_START");
                }
            }
            return Optional.empty();
        }
        boolean expectsReturn = "loweredBody".equals(binding.shape());
        if (expectsReturn) {
            if (ret == null) {
                return Optional.of("ASYNC_START(DEAL_BODY) must carry its body-task return "
                    + "boundary");
            }
            RawOp resolved = resolveOp(ret, unit, closure);
            if (resolved == null
                    || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("return boundary " + ret + " does not resolve to a BOUNDARY op");
            }
        } else if (ret != null) {
            return Optional.of("this ASYNC_START resolution runs zero return boundaries");
        }
        return Optional.empty();
    }

    private static int expectedParamCount(BindingInfo binding) {
        switch (binding.shape()) {
            case "adapter" -> {
                RuntimeDescriptor.Func target = parseFuncQuiet(binding.targetSignature());
                return target == null ? -1 : target.paramTypes().size();
            }
            case "hostFunction", "hostFunctionValue", "externalFunction" -> {
                RuntimeDescriptor.Func descriptor = parseFuncQuiet(binding.descriptor());
                return descriptor == null ? -1 : descriptor.paramTypes().size();
            }
            default -> {
                return -1;
            }
        }
    }

    private static Optional<String> checkCallbackCells(RawUnit unit, RawOp callback) {
        RuntimeDescriptor.Func descriptor = parseFuncQuiet(
            optionalString(callback.payload(), "descriptor"));
        if (descriptor == null) {
            return Optional.empty();
        }
        List<OpId> params = parseOpIdList(callback.payload(), "parameterBoundaryOpIds");
        if (params.size() != descriptor.paramTypes().size()) {
            return Optional.of("CALLBACK_INVOKE parameter boundaries (" + params.size()
                + ") must match the descriptor parameters (" + descriptor.paramTypes().size()
                + ")");
        }
        for (OpId param : params) {
            RawOp resolved = resolveOp(param, unit, Map.of());
            if (resolved == null
                    || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("parameter boundary " + param + " does not resolve to a "
                    + "BOUNDARY op");
            }
        }
        OpId ret = parseOptionalOpId(callback.payload(), "returnBoundaryOpId");
        if (ret == null) {
            return Optional.of("CALLBACK_INVOKE must carry its single return boundary");
        }
        RawOp resolved = resolveOp(ret, unit, Map.of());
        if (resolved == null
                || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
            return Optional.of("return boundary " + ret + " does not resolve to a BOUNDARY op");
        }
        return Optional.empty();
    }

    private static Optional<String> checkAwaitCells(RawUnit unit, RawOp await) {
        OpId completion = parseOptionalOpId(await.payload(), "completionBoundaryOpId");
        if (completion == null) {
            return Optional.of("AWAIT must carry its single completion boundary");
        }
        RawOp resolved = resolveOp(completion, unit, Map.of());
        if (resolved == null
                || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
            return Optional.of("completion boundary " + completion + " does not resolve to a "
                + "BOUNDARY op");
        }
        return Optional.empty();
    }

    private static Optional<String> checkEntryCells(RawUnit unit, RawOp entry) {
        OpId ret = parseOptionalOpId(entry.payload(), "returnBoundaryOpId");
        if (ret == null) {
            return Optional.of("EXTERNAL_ENTRY must carry its single return boundary");
        }
        RawOp resolved = resolveOp(ret, unit, Map.of());
        if (resolved == null
                || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
            return Optional.of("return boundary " + ret + " does not resolve to a BOUNDARY op");
        }
        return Optional.empty();
    }

    private static Optional<String> checkClassNewCells(RawUnit unit, RawOp classNew) {
        CanonicalJson.Value value = payloadValue(classNew.payload(), "fieldBoundaries");
        if (!(value instanceof CanonicalJson.Arr boundaries)) {
            return Optional.empty();
        }
        for (CanonicalJson.Value item : boundaries.items()) {
            if (!(item instanceof CanonicalJson.Obj boundary)) {
                continue;
            }
            OpId id = parseOptionalOpId(boundary, "boundaryOpId");
            if (id == null) {
                return Optional.of("a CLASS_NEW field boundary entry without a boundary op id");
            }
            RawOp resolved = resolveOp(id, unit, Map.of());
            if (resolved == null
                    || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("field boundary " + id + " does not resolve to a BOUNDARY op");
            }
            BoundaryKind kind = enumByName(BoundaryKind.class, optionalString(boundary, "kind"));
            if (kind != BoundaryKind.CLASS_LITERAL_FIELD && kind != BoundaryKind.CLASS_DEFAULT_FIELD) {
                return Optional.of("a CLASS_NEW field boundary entry must carry "
                    + "CLASS_LITERAL_FIELD or CLASS_DEFAULT_FIELD, got "
                    + optionalString(boundary, "kind"));
            }
        }
        return Optional.empty();
    }

    private static Optional<String> checkArrayNewCells(RawUnit unit, RawOp arrayNew) {
        CanonicalJson.Value valuesValue = payloadValue(arrayNew.payload(), "values");
        CanonicalJson.Value boundariesValue = payloadValue(arrayNew.payload(), "elementBoundaryOpIds");
        if (!(valuesValue instanceof CanonicalJson.Arr values)
                || !(boundariesValue instanceof CanonicalJson.Arr boundaries)) {
            return Optional.empty();
        }
        if (values.items().size() != boundaries.items().size()) {
            return Optional.of("ARRAY_NEW element boundaries must match the element count");
        }
        for (CanonicalJson.Value item : boundaries.items()) {
            if (!(item instanceof CanonicalJson.Obj boundaryObj)) {
                return Optional.of("ARRAY_NEW element boundary entry is not an op id object");
            }
            OpId id = parseOpId(boundaryObj);
            RawOp resolved = resolveOp(id, unit, Map.of());
            if (resolved == null
                    || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
                return Optional.of("element boundary " + id + " does not resolve to a BOUNDARY op");
            }
        }
        return Optional.empty();
    }

    private static Optional<String> checkIndexReadCells(RawUnit unit, RawOp indexRead) {
        OpId boundary = parseOptionalOpId(indexRead.payload(), "elementBoundaryOpId");
        if (boundary == null) {
            return Optional.of("INDEX_READ must carry its element boundary");
        }
        RawOp resolved = resolveOp(boundary, unit, Map.of());
        if (resolved == null
                || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.BOUNDARY) {
            return Optional.of("element boundary " + boundary + " does not resolve to a BOUNDARY op");
        }
        return Optional.empty();
    }

    // Shared resolution helpers for the boundary rule.

    /** True iff the invocation's callee reference is the closed {@code dynamic} shape. */
    private static boolean isDynamicCallee(RawOp invocation) {
        CanonicalJson.Value calleeValue = payloadValue(invocation.payload(), "callee");
        if (!(calleeValue instanceof CanonicalJson.Obj callee)) {
            return false;
        }
        return "dynamic".equals(optionalString(callee, "type"));
    }

    /**
     * Parses the recorded dynamic return-boundary set of a CALL
     * ({@code null} when absent or malformed — the per-cell and
     * record-presence defects then fall to the rule arms that own them).
     */
    private static KindPayload.DynamicReturnBoundary parseDynamicReturnBoundary(RawOp call) {
        CanonicalJson.Value value = payloadValue(call.payload(), "dynamicReturnBoundary");
        if (!(value instanceof CanonicalJson.Obj record)) {
            return null;
        }
        OpId deal = parseRecordOpId(record, "dealBodyBoundaryOpId");
        OpId host = parseRecordOpId(record, "hostBoundaryOpId");
        OpId external = parseRecordOpId(record, "externalBoundaryOpId");
        if (deal == null || host == null || external == null) {
            return null;
        }
        return new KindPayload.DynamicReturnBoundary(deal, host, external);
    }

    /**
     * True iff the CALL payload carries a non-null
     * {@code dynamicReturnBoundary} value — presence, not parse success:
     * the pinned exclusivity 'only a DYNAMIC callee records the dynamic
     * return-boundary set' fires for a non-Dynamic callee even when the
     * recorded object is malformed (the canonical rendering carries an
     * absent record as JSON {@code null}).
     */
    private static boolean recordsDynamicReturnBoundary(RawOp call) {
        CanonicalJson.Value value = payloadValue(call.payload(), "dynamicReturnBoundary");
        return value != null && !(value instanceof CanonicalJson.Null);
    }

    /** Parses one op-id entry of a payload record object ({@code null} when absent/malformed). */
    private static OpId parseRecordOpId(CanonicalJson.Obj record, String key) {
        CanonicalJson.Value value = payloadValue(record, key);
        if (!(value instanceof CanonicalJson.Obj idObj)) {
            return null;
        }
        try {
            return parseOpId(idObj);
        } catch (RuntimeException e) {
            return null;
        }
    }

    /** Parses a BOUNDARY payload's input identity ({@code null} when absent/malformed). */
    private static ValueId parseBoundaryInput(RawOp boundary) {
        CanonicalJson.Value value = payloadValue(boundary.payload(), "input");
        if (!(value instanceof CanonicalJson.Obj inputObj)) {
            return null;
        }
        try {
            return parseValueId(inputObj);
        } catch (RuntimeException e) {
            return null;
        }
    }

    /** The callee binding resolved like CALL(INDIRECT)/ASYNC_START: static inline or via functionBindings. */
    private static BindingInfo resolveCalleeBinding(RawUnit unit, RawOp invocation,
                                                    Map<String, RawUnit> closure) {
        CanonicalJson.Value calleeValue = payloadValue(invocation.payload(), "callee");
        if (!(calleeValue instanceof CanonicalJson.Obj callee)) {
            return null;
        }
        String type = optionalString(callee, "type");
        if ("static".equals(type)) {
            CanonicalJson.Value bindingValue = payloadValue(callee, "binding");
            if (bindingValue instanceof CanonicalJson.Obj binding) {
                return BindingInfo.fromJson(binding);
            }
            return null;
        }
        if ("indirect".equals(type)) {
            CanonicalJson.Value calleeIdValue = payloadValue(callee, "callee");
            if (!(calleeIdValue instanceof CanonicalJson.Obj calleeObj)) {
                return null;
            }
            ValueId calleeId = parseValueId(calleeObj);
            for (RawBinding binding : unit.bindings()) {
                if (binding.allocationId() == calleeId.id()) {
                    return BindingInfo.fromBinding(binding);
                }
            }
            return null;
        }
        return null;
    }

    /** The resolved binding shape plus the closed owner/mode positions. */
    private record BindingInfo(String shape, String executionOwner, String targetSignature,
                               String descriptor, String exportName) {

        static BindingInfo fromJson(CanonicalJson.Obj binding) {
            return new BindingInfo(optionalString(binding, "type"),
                optionalString(binding, "executionOwner"),
                optionalString(binding, "targetSignature"),
                optionalString(binding, "descriptor"),
                optionalString(binding, "exportName"));
        }

        static BindingInfo fromBinding(RawBinding binding) {
            return new BindingInfo(binding.shape(), binding.executionOwner(),
                binding.targetSignature(), binding.descriptor(), binding.exportName());
        }
    }

    private static RawOp resolveParent(RawOp op, RawUnit unit, Map<String, RawUnit> closure) {
        return op.parentOpId() == null ? null : resolveOp(op.parentOpId(), unit, closure);
    }

    private static RawOp resolveOp(OpId opId, RawUnit unit, Map<String, RawUnit> closure) {
        RawUnit owner = opId.module().path().equals(unit.modulePath())
            ? unit : closure.get(opId.module().path());
        if (owner == null) {
            return null;
        }
        for (RawOp op : owner.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    private static boolean isKind(RawOp op, BoundaryKind kind) {
        return enumByName(BoundaryKind.class, optionalString(op.payload(), "kind")) == kind;
    }

    // -- R-ELIDED-PLACEMENT -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkElidedPlacement(RawUnit unit,
                                                                     ComparisonFacts facts) {
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) != SemanticOpKind.ASYNC_START) {
                continue;
            }
            ParameterBoundaryMode mode = enumByName(ParameterBoundaryMode.class,
                optionalString(op.payload(), "parameterBoundaryMode"));
            if (mode == null || mode != ParameterBoundaryMode.ELIDED_BY_ADAPTER) {
                continue;
            }
            RawOp parent = resolveParent(op, unit, Map.of());
            if (parent == null) {
                return fail(unit, facts, R_ELIDED_PLACEMENT, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ELIDED_PLACEMENT, "ELIDED_BY_ADAPTER with no parent op"));
            }
            if (enumByName(SemanticOpKind.class, parent.kind()) != SemanticOpKind.ASYNC_START) {
                return fail(unit, facts, R_ELIDED_PLACEMENT, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ELIDED_PLACEMENT, "ELIDED_BY_ADAPTER parented to "
                        + parent.kind() + ", not the outer ASYNC_START of an adapter-over-async task"));
            }
            BindingInfo binding = resolveCalleeBinding(unit, parent, Map.of());
            if (binding == null || !"adapter".equals(binding.shape())) {
                return fail(unit, facts, R_ELIDED_PLACEMENT, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_ELIDED_PLACEMENT, "ELIDED_BY_ADAPTER outside the nested source "
                        + "ASYNC_START of an adapter-over-async task (the outer op's callee "
                        + "does not resolve to an AdapterBinding)"));
            }
        }
        return Optional.empty();
    }

    // -- R-FUNCTION-BINDING -----------------------------------------------------

    private static Optional<CompilerDiagnostic> checkFunctionBinding(RawUnit unit,
                                                                     ComparisonFacts facts) {
        for (RawOp op : unit.ops()) {
            if (op.resultValue() == null || op.resultType() == null) {
                continue;
            }
            RuntimeDescriptor resultType = parseDescriptorQuiet(op.resultType());
            if (!(resultType instanceof RuntimeDescriptor.Func)) {
                continue;
            }
            long id = op.resultValue().id();
            long matches = 0;
            for (RawBinding binding : unit.bindings()) {
                if (binding.allocationId() == id) {
                    matches++;
                }
            }
            if (matches != 1) {
                return fail(unit, facts, R_FUNCTION_BINDING, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "function-typed result ValueId " + id
                        + " without exactly one FunctionExecutionBinding"));
            }
        }
        // ISSUE-0531 reconciliation — callback-delivered and host-response
        // materialized function identities. Direction (i): every
        // HostFunctionValue registration's correlation id must resolve to
        // its producing host crossing (a function-typed HOST_TO_DEAL
        // boundary op carrying the registered key as its input identity
        // and the registered descriptor as its checked descriptor).
        for (RawBinding binding : unit.bindings()) {
            if (!"hostFunctionValue".equals(binding.shape())) {
                continue;
            }
            if (binding.materializingBoundaryOpId() == null) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the HostFunctionValue registration key "
                        + binding.allocationId() + " carries no materializingBoundaryOpId "
                        + "(the correlation id naming its producing host crossing)"));
            }
            RawOp crossing = null;
            for (RawOp op : unit.ops()) {
                if (op.opId().equals(binding.materializingBoundaryOpId())) {
                    crossing = op;
                    break;
                }
            }
            if (crossing == null
                    || enumByName(SemanticOpKind.class, crossing.kind()) != SemanticOpKind.BOUNDARY
                    || enumByName(BoundaryKind.class, optionalString(crossing.payload(), "kind"))
                        != BoundaryKind.HOST_TO_DEAL) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the HostFunctionValue registration key "
                        + binding.allocationId() + " names materializingBoundaryOpId "
                        + binding.materializingBoundaryOpId() + ", which does not resolve to "
                        + "a HOST_TO_DEAL boundary op of the unit"));
            }
            RuntimeDescriptor descriptor = parseDescriptorQuiet(
                optionalString(crossing.payload(), "descriptor"));
            if (!(descriptor instanceof RuntimeDescriptor.Func)
                    || !descriptor.canonicalSpecText().equals(binding.descriptor())) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the HostFunctionValue registration key "
                        + binding.allocationId() + " descriptor does not equal its "
                        + "materializing crossing's function descriptor"));
            }
            ValueId input = parseBoundaryInput(crossing);
            if (input == null || input.id() != binding.allocationId()) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the HostFunctionValue registration key "
                        + binding.allocationId() + " materializing crossing does not carry "
                        + "the registered allocation identity as its input"));
            }
        }
        // Direction (ii): every function-typed HOST_TO_DEAL crossing (a
        // CALLBACK_INVOKE parameter or a host call's sync return)
        // registers exactly one HostFunctionValue binding keyed by the
        // crossing's input allocation identity, with
        // materializingBoundaryOpId naming the producing crossing op and
        // the registration descriptor equal to the crossing's checked
        // descriptor. The runtime resolves later calls through the same
        // identity on exactly that registration — a missing correlation
        // is invalid IR.
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) != SemanticOpKind.BOUNDARY) {
                continue;
            }
            if (enumByName(BoundaryKind.class, optionalString(op.payload(), "kind"))
                    != BoundaryKind.HOST_TO_DEAL) {
                continue;
            }
            RuntimeDescriptor descriptor = parseDescriptorQuiet(
                optionalString(op.payload(), "descriptor"));
            if (!(descriptor instanceof RuntimeDescriptor.Func)) {
                continue;
            }
            ValueId input = parseBoundaryInput(op);
            if (input == null) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the function-typed HOST_TO_DEAL crossing op "
                        + op.opId() + " carries no input allocation identity"));
            }
            long matches = 0;
            for (RawBinding binding : unit.bindings()) {
                if (binding.allocationId() == input.id()
                        && "hostFunctionValue".equals(binding.shape())
                        && op.opId().equals(binding.materializingBoundaryOpId())
                        && descriptor.canonicalSpecText().equals(binding.descriptor())) {
                    matches++;
                }
            }
            if (matches != 1) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the function-typed HOST_TO_DEAL crossing op "
                        + op.opId() + " materializing input identity " + input
                        + " has no matching HostFunctionValue registration (exactly one "
                        + "registration keyed by the crossing input with "
                        + "materializingBoundaryOpId == the crossing op and the crossing's "
                        + "descriptor)"));
            }
        }
        // Direction (iii): the dynamic-function-value materialization
        // correlation. A DynamicFunctionValue registration names no
        // statically known class, so its producing op is the single
        // correlation channel: the named op must exist in the unit, its
        // result identity must be the registration key, and its result
        // descriptor must equal the registered descriptor. A missing
        // correlation is invalid IR.
        for (RawBinding binding : unit.bindings()) {
            if (!"dynamicFunctionValue".equals(binding.shape())) {
                continue;
            }
            if (binding.materializingBoundaryOpId() == null) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the DynamicFunctionValue registration key "
                        + binding.allocationId() + " carries no materializingBoundaryOpId "
                        + "(the correlation id naming its producing op)"));
            }
            RawOp producing = null;
            for (RawOp op : unit.ops()) {
                if (op.opId().equals(binding.materializingBoundaryOpId())) {
                    producing = op;
                    break;
                }
            }
            if (producing == null) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the DynamicFunctionValue registration key "
                        + binding.allocationId() + " names materializingBoundaryOpId "
                        + binding.materializingBoundaryOpId() + ", which does not resolve "
                        + "to an op of the unit"));
            }
            if (producing.resultValue() == null
                    || producing.resultValue().id() != binding.allocationId()) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the DynamicFunctionValue registration key "
                        + binding.allocationId() + " materializing op "
                        + binding.materializingBoundaryOpId() + " does not carry the "
                        + "registered allocation identity as its result"));
            }
            RuntimeDescriptor descriptor = parseDescriptorQuiet(producing.resultType());
            if (!(descriptor instanceof RuntimeDescriptor.Func)
                    || !descriptor.canonicalSpecText().equals(binding.descriptor())) {
                return fail(unit, facts, R_FUNCTION_BINDING,
                    SemanticCapability.FOUNDATION_VALUES,
                    origin(R_FUNCTION_BINDING, "the DynamicFunctionValue registration key "
                        + binding.allocationId() + " descriptor does not equal its "
                        + "producing op's result descriptor"));
            }
        }
        return Optional.empty();
    }

    // -- R-EXTERNAL-ENTRY -------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkExternalEntry(RawUnit unit,
                                                                   ComparisonFacts facts,
                                                                   Map<String, RawUnit> closure) {
        for (RawBinding binding : unit.bindings()) {
            if (!"externalFunction".equals(binding.shape())
                    || !"SHARED_BODY".equals(binding.executionOwner())) {
                continue;
            }
            Optional<CompilerDiagnostic> failure = externalEntryFor(unit, facts, closure,
                binding.modulePath(), binding.exportName());
            if (failure.isPresent()) {
                return failure;
            }
        }
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) != SemanticOpKind.CALL) {
                continue;
            }
            OpId ref = parseOptionalOpId(op.payload(), "externalEntryRef");
            if (ref == null) {
                continue;
            }
            BindingInfo binding = resolveCalleeBinding(unit, op, closure);
            String exportName = binding == null ? null : binding.exportName();
            if (exportName == null) {
                continue;
            }
            RawUnit target = ref.module().path().equals(unit.modulePath())
                ? unit : closure.get(ref.module().path());
            if (target == null) {
                if (closure.isEmpty()) {
                    continue; // unit-level: foreign-module references are indeterminate.
                }
                return fail(unit, facts, R_EXTERNAL_ENTRY, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_EXTERNAL_ENTRY, "externalEntryRef " + ref + " names a module "
                        + "outside the implementation closure"));
            }
            RawOp resolved = null;
            for (RawOp candidate : target.ops()) {
                if (candidate.opId().equals(ref)) {
                    resolved = candidate;
                    break;
                }
            }
            if (resolved == null
                    || enumByName(SemanticOpKind.class, resolved.kind()) != SemanticOpKind.EXTERNAL_ENTRY
                    || !exportName.equals(optionalString(resolved.payload(), "exportName"))) {
                return fail(unit, facts, R_EXTERNAL_ENTRY, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_EXTERNAL_ENTRY, "externalEntryRef " + ref + " does not resolve to "
                        + "a recorded EXTERNAL_ENTRY for export \"" + exportName + "\""));
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> externalEntryFor(RawUnit unit, ComparisonFacts facts,
                                                                 Map<String, RawUnit> closure,
                                                                 String modulePath, String exportName) {
        RawUnit target = modulePath.equals(unit.modulePath())
            ? unit : closure.get(modulePath);
        if (target == null) {
            if (closure.isEmpty()) {
                return Optional.empty(); // unit-level: foreign-module bindings are indeterminate.
            }
            return fail(unit, facts, R_EXTERNAL_ENTRY, SemanticCapability.FOUNDATION_VALUES,
                origin(R_EXTERNAL_ENTRY, "SHARED_BODY ExternalFunction export \"" + exportName
                    + "\" names module \"" + modulePath + "\" outside the implementation closure"));
        }
        for (RawOp op : target.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) == SemanticOpKind.EXTERNAL_ENTRY
                    && exportName.equals(optionalString(op.payload(), "exportName"))) {
                return Optional.empty();
            }
        }
        return fail(unit, facts, R_EXTERNAL_ENTRY, SemanticCapability.FOUNDATION_VALUES,
            origin(R_EXTERNAL_ENTRY, "SHARED_BODY ExternalFunction export \"" + exportName
                + "\" in module \"" + modulePath
                + "\" without a recorded EXTERNAL_ENTRY in the callee unit"));
    }

    // -- R-ALIAS-CYCLE ----------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkAliasCycle(RawUnit unit, ComparisonFacts facts) {
        // Collect every token the unit references (op results, AWAIT payload
        // tokens, ASYNC_START external links) and their referent closures.
        Map<Long, Long> edges = new LinkedHashMap<>(); // alias tokenId -> referent tokenId
        List<AsyncTokenId> collected = new ArrayList<>();
        for (RawOp op : unit.ops()) {
            collectTokens(op, collected);
        }
        Set<Long> nodes = new LinkedHashSet<>();
        for (AsyncTokenId token : collected) {
            collectTokenNodes(token, nodes, edges);
        }
        // DFS cycle detection over token identities in deterministic order.
        Map<Long, Integer> color = new LinkedHashMap<>(); // 0=white, 1=gray, 2=black
        List<Long> order = new ArrayList<>(nodes);
        for (Long node : order) {
            if (color.getOrDefault(node, 0) == 0) {
                Optional<Long> cycle = dfsCycle(node, edges, color);
                if (cycle.isPresent()) {
                    return fail(unit, facts, R_ALIAS_CYCLE, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_ALIAS_CYCLE, "alias token cycle over token identity "
                            + cycle.get()));
                }
            }
        }
        return Optional.empty();
    }

    private static void collectTokens(RawOp op, List<AsyncTokenId> collected) {
        if (op.resultToken() != null) {
            collected.add(op.resultToken());
        }
        if (enumByName(SemanticOpKind.class, op.kind()) == SemanticOpKind.AWAIT) {
            CanonicalJson.Value tokenValue = payloadValue(op.payload(), "token");
            if (tokenValue instanceof CanonicalJson.Obj tokenObj) {
                collected.add(parseToken(tokenObj));
            }
        }
        if (enumByName(SemanticOpKind.class, op.kind()) == SemanticOpKind.ASYNC_START) {
            CanonicalJson.Value linkValue = payloadValue(op.payload(), "externalAsyncLink");
            if (linkValue instanceof CanonicalJson.Obj link) {
                CanonicalJson.Value calleeToken = payloadValue(link, "calleeTokenId");
                if (calleeToken instanceof CanonicalJson.Obj tokenObj) {
                    collected.add(parseToken(tokenObj));
                }
            }
        }
    }

    private static void collectTokenNodes(AsyncTokenId token, Set<Long> nodes,
                                          Map<Long, Long> edges) {
        nodes.add(token.tokenId());
        if (token instanceof AsyncTokenId.Alias alias) {
            nodes.add(alias.referent().tokenId());
            edges.putIfAbsent(alias.tokenId(), alias.referent().tokenId());
            collectTokenNodes(alias.referent(), nodes, edges);
        }
    }

    private static Optional<Long> dfsCycle(Long node, Map<Long, Long> edges,
                                           Map<Long, Integer> color) {
        color.put(node, 1);
        Long next = edges.get(node);
        if (next != null) {
            int nextColor = color.getOrDefault(next, 0);
            if (nextColor == 1) {
                return Optional.of(next);
            }
            if (nextColor == 0) {
                Optional<Long> cycle = dfsCycle(next, edges, color);
                if (cycle.isPresent()) {
                    return cycle;
                }
            }
        }
        color.put(node, 2);
        return Optional.empty();
    }

    // -- R-TOKEN-REUSE ----------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkTokenReuse(RawUnit unit, ComparisonFacts facts) {
        List<AsyncTokenId> consumed = new ArrayList<>();
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) != SemanticOpKind.AWAIT) {
                continue;
            }
            CanonicalJson.Value tokenValue = payloadValue(op.payload(), "token");
            if (!(tokenValue instanceof CanonicalJson.Obj tokenObj)) {
                continue;
            }
            AsyncTokenId token = parseToken(tokenObj);
            for (AsyncTokenId prior : consumed) {
                if (prior.equals(token)) {
                    return fail(unit, facts, R_TOKEN_REUSE, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_TOKEN_REUSE, "token " + token.tokenId()
                            + " consumed twice (one AWAIT per token)"));
                }
            }
            consumed.add(token);
        }
        return Optional.empty();
    }

    // -- R-PRIVATE-STEP ---------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkPrivateStep(RawUnit unit, ComparisonFacts facts) {
        for (RawCoverage row : unit.coverage()) {
            for (String kindName : row.opKinds()) {
                if (enumByName(SemanticOpKind.class, kindName) == null) {
                    return fail(unit, facts, R_PRIVATE_STEP, SemanticCapability.FOUNDATION_VALUES,
                        origin(R_PRIVATE_STEP, "consumer-private op kind \"" + kindName
                            + "\" in a constructCoverage row"));
                }
            }
        }
        for (RawOp op : unit.ops()) {
            if (enumByName(SemanticOpKind.class, op.kind()) == null) {
                return fail(unit, facts, R_PRIVATE_STEP, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_PRIVATE_STEP, "consumer-private op kind \"" + op.kind() + "\""));
            }
            String snapshotKind = optionalString(op.snapshot(), "opKind");
            if (snapshotKind != null && enumByName(SemanticOpKind.class, snapshotKind) == null) {
                return fail(unit, facts, R_PRIVATE_STEP, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_PRIVATE_STEP, "consumer-private op kind \"" + snapshotKind
                        + "\" in the contract snapshot"));
            }
        }
        return Optional.empty();
    }

    // -- R-RESERVED-NAME --------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkReservedName(RawUnit unit,
                                                                  ComparisonFacts facts) {
        for (RawOp op : unit.ops()) {
            if (op.selector() != null && StdlibFunctionId.RESERVED_NAMES.contains(op.selector())) {
                return fail(unit, facts, R_RESERVED_NAME, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_RESERVED_NAME, "reserved selector name \"" + op.selector() + "\""));
            }
            String function = enumByName(SemanticOpKind.class, op.kind()) == SemanticOpKind.STDLIB_CALL
                ? optionalString(op.payload(), "function") : null;
            if (function != null && StdlibFunctionId.RESERVED_NAMES.contains(function)) {
                return fail(unit, facts, R_RESERVED_NAME, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_RESERVED_NAME, "reserved selector name \"" + function + "\""));
            }
            if (op.failurePolicy() != null
                    && FailurePolicyId.RESERVED_NAMES.contains(op.failurePolicy())) {
                return fail(unit, facts, R_RESERVED_NAME, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_RESERVED_NAME, "reserved policy name \"" + op.failurePolicy()
                        + "\" in a FailurePolicyId position"));
            }
            String snapshotPolicy = optionalString(op.snapshot(), "failurePolicy");
            if (snapshotPolicy != null && FailurePolicyId.RESERVED_NAMES.contains(snapshotPolicy)) {
                return fail(unit, facts, R_RESERVED_NAME, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_RESERVED_NAME, "reserved policy name \"" + snapshotPolicy
                        + "\" in a FailurePolicyId position"));
            }
        }
        return Optional.empty();
    }

    // -- R-DIGEST ---------------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkDigest(RawUnit unit, ComparisonFacts facts) {
        for (RawOp op : unit.ops()) {
            String recomputed = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(op.snapshot());
            if (!recomputed.equals(op.canonicalDigest())) {
                return fail(unit, facts, R_DIGEST, SemanticCapability.FOUNDATION_VALUES,
                    origin(R_DIGEST, "recomputed digest " + recomputed
                        + " differs from canonicalDigest " + op.canonicalDigest()));
            }
        }
        return Optional.empty();
    }

    // -- R-PROFILE --------------------------------------------------------------

    private static Optional<CompilerDiagnostic> checkProfile(RawUnit unit, ComparisonFacts facts) {
        if (!ADMITTED_PROFILE.equals(unit.semanticProfile())) {
            return fail(unit, facts, R_PROFILE, SemanticCapability.FOUNDATION_VALUES,
                origin(R_PROFILE, "semanticProfile \"" + unit.semanticProfile()
                    + "\" is not DEAL_V1_2_INT32"));
        }
        if (!facts.interfaceIndexDigest().equals(unit.interfaceHash())) {
            return fail(unit, facts, R_PROFILE, SemanticCapability.FOUNDATION_VALUES,
                origin(R_PROFILE, "interfaceHash \"" + unit.interfaceHash()
                    + "\" differs from the interface index digest"));
        }
        String expectedHash = LoweringContextHash.of(facts.semanticProfile(),
            facts.capabilityRegistryHash());
        if (!expectedHash.equals(unit.loweringContextHash())) {
            return fail(unit, facts, R_PROFILE, SemanticCapability.FOUNDATION_VALUES,
                origin(R_PROFILE, "loweringContextHash \"" + unit.loweringContextHash()
                    + "\" differs from SHA-256(canonical JSON {semanticProfile, "
                    + "capabilityRegistryHash}) recomputed from the comparison facts"));
        }
        return Optional.empty();
    }

    // =========================================================================
    // Small shared helpers
    // =========================================================================

    @SuppressWarnings("unchecked")
    private static String optionalString(CanonicalJson.Obj obj, String key) {
        return ContractSnapshotCanonicalizer.optionalString(obj, key);
    }

    private static CanonicalJson.Value payloadValue(CanonicalJson.Obj obj, String key) {
        return ContractSnapshotCanonicalizer.payloadValue(obj, key);
    }

    private static boolean isTrue(CanonicalJson.Obj obj, String key) {
        return ContractSnapshotCanonicalizer.isTrue(obj, key);
    }

    private static OpId parseOpId(CanonicalJson.Obj obj) {
        return ContractSnapshotCanonicalizer.parseOpId(obj);
    }

    private static ValueId parseValueId(CanonicalJson.Obj obj) {
        return ContractSnapshotCanonicalizer.parseValueId(obj);
    }

    private static AsyncTokenId parseToken(CanonicalJson.Obj obj) {
        return ContractSnapshotCanonicalizer.parseToken(obj);
    }

    private static List<OpId> parseOpIdList(CanonicalJson.Obj obj, String key) {
        return ContractSnapshotCanonicalizer.parseOpIdList(obj, key);
    }

    private static OpId parseOptionalOpId(CanonicalJson.Obj obj, String key) {
        return ContractSnapshotCanonicalizer.parseOptionalOpId(obj, key);
    }

    @SuppressWarnings("unchecked")
    private static <E extends Enum<E>> E enumByName(Class<?> type, String name) {
        if (name == null) {
            return null;
        }
        try {
            return (E) Enum.valueOf((Class<E>) type, name);
        } catch (IllegalArgumentException e) {
            return null;
        }
    }

    private static RuntimeDescriptor parseDescriptorQuiet(String text) {
        if (text == null) {
            return null;
        }
        try {
            return RuntimeDescriptor.parseCanonicalText(text);
        } catch (SemanticIrTextDecodeException e) {
            return null;
        }
    }

    private static RuntimeDescriptor.Func parseFuncQuiet(String text) {
        RuntimeDescriptor descriptor = parseDescriptorQuiet(text);
        return descriptor instanceof RuntimeDescriptor.Func func ? func : null;
    }

    /** Result type text → descriptor (internal sentinels and malformed texts yield null). */
    private static RuntimeDescriptor parseResultType(String raw) {
        if (raw == null || "INTERNAL_MISSING".equals(raw) || "INTERNAL_ASYNC".equals(raw)) {
            return null;
        }
        return parseDescriptorQuiet(raw);
    }

}
