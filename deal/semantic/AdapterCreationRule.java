package deal.semantic;

import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The closed {@code FUNCTION_ADAPT} creation-rule position classifier of
 * the BINDINGS capability (ISSUE-0449 creation-rule child, sequencing
 * item 6; design B6, parent D15 "Creation rule (closed)"), plus the
 * closed position set over {@link BoundaryKind}: for every
 * function-typed value flow the lowerer classifies the position by
 * checker facts ({@code CheckResult.typeMap},
 * {@link Types#equals(Type, Type)} / {@link Types#isAssignable(Type,
 * Type)}) before choosing any shape.
 *
 * <p><b>The closed creation rule (B6, exactly).</b></p>
 * <ul>
 *   <li><b>Exact signature</b> — identical async marker, identical
 *       return type, identical parameter lists
 *       ({@code Types.equals}) — the value is stored directly; no
 *       {@code FUNCTION_ADAPT} ({@link Disposition#DIRECT_STORE} — the
 *       direct-store flow is this child's production).</li>
 *   <li><b>Assignable-but-not-exact</b> — identical async marker,
 *       identical return type, {@code M <= N} with exactly equal leading
 *       M parameter types and {@code M < N} — exactly one adaptation
 *       candidate ({@link Disposition#ADAPT}): the candidate carries the
 *       derived source signature (the source expression's checked type),
 *       the target signature (the declared binding signature), the
 *       recorded proof fact for the shape-map child (B7), the prepared
 *       wiring point (the adapted position's own
 *       {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
 *       boundary chain into which the adapter result will be wired as
 *       its direct input — B9's creation-wiring target), and the
 *       producer facts the registry child's host/external
 *       materialization seam supplies when the source is a host/external
 *       function value ({@code HostFunction}/{@code HostFunctionValue}/
 *       {@code ExternalFunction} are admissible adaptation sources per
 *       the same rule, {@code docs/spec-v1.2.md:1078-1082}). This child
 *       emits no {@code FUNCTION_ADAPT} op and chooses no mode — mode
 *       selection, payload construction, and emission are the shape-map
 *       child's obligations, so every emitted adapter carries its
 *       closed-map mode from birth.</li>
 *   <li><b>Non-assignable</b> — never reaches lowering from checked
 *       source (E3001/E5004 are frontend rejections); a value whose
 *       runtime signature can differ from its static claim
 *       (host-materialized) fails the position's own
 *       {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
 *       boundary via the descriptor-kind rule →
 *       {@code FUNCTION_SIGNATURE} E8010 — that boundary op and its
 *       executed check are E4's machinery; this child classifies the
 *       position ({@link Disposition#NON_ASSIGNABLE}) and records the
 *       failure expectation.</li>
 * </ul>
 *
 * <p><b>Typed boundary positions never adapt.</b> The classifier admits
 * no adaptation arm for any position other than
 * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}: every other
 * {@link BoundaryKind} — parameter, return, host/external/callback
 * parameter/return, array/table/class element, JSON, and every other
 * kind — maps to {@link PositionKind#TYPED_BOUNDARY} with
 * {@link Disposition#BOUNDARY_DIRECT} (direct value flow into the
 * position's boundary slot — the wiring E4's boundary producer
 * consumes). The boundary's function-descriptor cell
 * ({@code FUNCTION_SIGNATURE}, descriptor-kind rule) and the
 * exact-signature E8010 rejection for any mismatch including
 * {@code M < N} before any invocation are realized by E4's closed
 * boundary-assignment table and machinery (the pinned
 * {@code jvm-fv-sig-check-return-error} behavior), not by this epic —
 * the classifier records the expectation only, never substitutes a
 * static projection for the executed check.</p>
 *
 * <p><b>After a direct-store commit</b> the function identity is an
 * ordinary function value: loads, reads, argument passing, and returns
 * preserve allocation identity, and any later typed-boundary crossing
 * is an ordinary {@code FUNCTION_SIGNATURE} check — exact-signature
 * pass when the descriptor matches, E8010 on a mismatch at that
 * boundary (realized by E4's boundary machinery).</p>
 *
 * <p><b>Determinism.</b> The classifier is a pure function over its
 * facts: the same position facts always produce an equal
 * classification record, so repeated lowering records identical
 * classification lists in walk order (byte-identical lowering's
 * classification half).</p>
 */
public final class AdapterCreationRule {

    /**
     * The closed creation-rule position kinds: the two variable
     * positions (the only positions whose classification can admit the
     * adaptation arm) and the typed-boundary position (never adapts).
     */
    public enum PositionKind {

        /** A {@code let} initializer ({@code VARIABLE_DECLARATION}). */
        VARIABLE_INITIALIZER,

        /** An assignment target ({@code VARIABLE_ASSIGNMENT}). */
        VARIABLE_ASSIGNMENT_TARGET,

        /** Every other {@link BoundaryKind} — never adapts. */
        TYPED_BOUNDARY
    }

    /**
     * The closed classification dispositions of the creation rule
     * (B6/D15): what the lowerer does at the position before choosing
     * any shape.
     */
    public enum Disposition {

        /** Exact signature — store the value directly; no {@code FUNCTION_ADAPT}. */
        DIRECT_STORE,

        /** Assignable-but-not-exact — exactly one adaptation candidate. */
        ADAPT,

        /**
         * Non-assignable — never reaches lowering from checked source
         * (E3001/E5004 frontend); a host-materialized wrong signature
         * fails the position's own boundary (E4's machinery) and the
         * classifier records that failure expectation.
         */
        NON_ASSIGNABLE,

        /** The position is not function-typed — the creation rule does not apply. */
        NOT_FUNCTION_FLOW,

        /** A typed boundary position — direct flow only; never adapts. */
        BOUNDARY_DIRECT
    }

    /**
     * The prepared wiring point of an adaptation candidate (B6/B9's
     * creation-wiring target): the adapted position's own
     * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} boundary
     * chain into which the adapter result will be wired as its direct
     * input — the {@code VARIABLE_DECLARATION} boundary op for an
     * annotated declaration, the {@code VARIABLE_ASSIGNMENT} boundary op
     * for an assignment target, or the {@code BINDING_INIT} op for an
     * inferred declaration (no boundary op exists there — B9).
     */
    public enum WiringTargetKind {

        /** The position's own {@code VARIABLE_DECLARATION} boundary op. */
        VARIABLE_DECLARATION_BOUNDARY,

        /** The position's own {@code VARIABLE_ASSIGNMENT} boundary op. */
        VARIABLE_ASSIGNMENT_BOUNDARY,

        /** The inferred declaration's {@code BINDING_INIT} op (no boundary). */
        BINDING_INIT
    }

    /**
     * One prepared wiring point: the op id plus its closed chain-role
     * tag.
     */
    public record WiringPoint(OpId opId, WiringTargetKind targetKind) {

        public WiringPoint {
            Objects.requireNonNull(opId, "opId must not be null");
            Objects.requireNonNull(targetKind, "targetKind must not be null");
        }
    }

    /**
     * The recorded failure expectation of a classified position: the
     * closed {@code FUNCTION_SIGNATURE} E8010 projection the position's
     * boundary raises when the executed check fails. The boundary op
     * and its executed check are E4's machinery — this record is the
     * classification-level expectation only, never a substitution for
     * the executed check (the {@code jvm-fv-sig-check-return-error}
     * behavior is driven by the integration child through E4's
     * realization component).
     *
     * @param code            the closed visible-error code ({@code E8010})
     * @param policy          the closed failure policy
     *                        ({@code FUNCTION_SIGNATURE})
     * @param boundaryKind    the boundary whose check raises the failure
     * @param messageTemplate the canonical primary template from the
     *                        closed failure-contract registry
     */
    public record FailureExpectation(String code, FailurePolicyId policy,
                                     BoundaryKind boundaryKind,
                                     String messageTemplate) {

        public FailureExpectation {
            Objects.requireNonNull(code, "code must not be null");
            Objects.requireNonNull(policy, "policy must not be null");
            Objects.requireNonNull(boundaryKind, "boundaryKind must not be null");
            Objects.requireNonNull(messageTemplate, "messageTemplate must not be null");
        }
    }

    /**
     * One derived adaptation candidate of an assignable-but-not-exact
     * position (B6): the derived source/target signature pair (which
     * re-derives as assignable-but-not-exact), the recorded proof fact
     * for the shape-map child (present exactly when the source is a
     * binding identifier whose dominant incarnation carries the
     * conservative {@code BindingImmutabilityProof} — B7), the prepared
     * wiring point, and the registry child's producer facts when the
     * source is a host/external function value (T4 seam). This child
     * emits no {@code FUNCTION_ADAPT} and chooses no mode — the
     * candidate is the position fact the shape-map child consumes.
     */
    public record AdaptationCandidate(
            RuntimeDescriptor.Func sourceSignature,
            RuntimeDescriptor.Func targetSignature,
            Optional<BindingImmutabilityProof> proof,
            WiringPoint wiringPoint,
            Optional<FunctionBindingRegistry.FunctionValueMaterialization> producerFacts) {

        public AdaptationCandidate {
            Objects.requireNonNull(sourceSignature, "sourceSignature must not be null");
            Objects.requireNonNull(targetSignature, "targetSignature must not be null");
            Objects.requireNonNull(proof, "proof must not be null");
            Objects.requireNonNull(wiringPoint, "wiringPoint must not be null");
            Objects.requireNonNull(producerFacts, "producerFacts must not be null");
        }

        /**
         * The closed pair re-derivation (B6/{@code ADAPTER_PAIR}):
         * identical async marker, identical return type, {@code M <= N}
         * with exactly equal leading M parameter types and {@code M < N}.
         *
         * @return {@code true} iff the candidate's signature pair
         *         re-derives as assignable-but-not-exact
         */
        public boolean reDerivesAsAssignableButNotExact() {
            return assignableButNotExact(sourceSignature, targetSignature);
        }
    }

    /**
     * One classified position: the closed position kind, the boundary
     * kind of the position's boundary chain, the closed disposition,
     * the single adaptation candidate (exactly when the disposition is
     * {@code ADAPT}), and the recorded failure expectation (exactly
     * when the classification records one).
     */
    public record PositionClassification(
            PositionKind positionKind,
            BoundaryKind boundaryKind,
            Disposition disposition,
            Optional<AdaptationCandidate> candidate,
            Optional<FailureExpectation> failureExpectation) {

        public PositionClassification {
            Objects.requireNonNull(positionKind, "positionKind must not be null");
            Objects.requireNonNull(boundaryKind, "boundaryKind must not be null");
            Objects.requireNonNull(disposition, "disposition must not be null");
            Objects.requireNonNull(candidate, "candidate must not be null");
            Objects.requireNonNull(failureExpectation, "failureExpectation must not be null");
            if (candidate.isPresent() != (disposition == Disposition.ADAPT)) {
                throw new IllegalArgumentException(
                    "a position classification carries its candidate exactly when the "
                        + "disposition is ADAPT; got " + disposition + " with candidate="
                        + candidate.isPresent());
            }
        }
    }

    /**
     * The creation-rule child's complete fact surface of one module
     * lowering: the position classifications in walk order (one per
     * classified function-typed position). Partial on a failed walk,
     * complete on success.
     */
    public record CreationRuleFacts(List<PositionClassification> classifications) {

        /** The empty fact set (the failure-path and off-mode value). */
        public static CreationRuleFacts empty() {
            return new CreationRuleFacts(List.of());
        }

        public CreationRuleFacts {
            Objects.requireNonNull(classifications, "classifications must not be null");
            classifications = List.copyOf(classifications);
        }

        /**
         * The recorded classifications with exactly the given
         * disposition, in record order.
         *
         * @param disposition the closed disposition; non-null
         * @return the matching classifications
         */
        public List<PositionClassification> ofDisposition(Disposition disposition) {
            Objects.requireNonNull(disposition, "disposition must not be null");
            List<PositionClassification> matches = new ArrayList<>();
            for (PositionClassification classification : classifications) {
                if (classification.disposition() == disposition) {
                    matches.add(classification);
                }
            }
            return matches;
        }

        /**
         * The recorded adaptation candidates in record order (exactly
         * the {@code ADAPT} classifications' candidates).
         *
         * @return the candidates
         */
        public List<AdaptationCandidate> candidates() {
            List<AdaptationCandidate> candidates = new ArrayList<>();
            for (PositionClassification classification : classifications) {
                classification.candidate().ifPresent(candidates::add);
            }
            return candidates;
        }
    }

    private AdapterCreationRule() {
        // Static closed classifier; no instances.
    }

    // =========================================================================
    // The closed position set (B6: the only adaptation positions)
    // =========================================================================

    /**
     * The closed position-kind map over the 27 {@link BoundaryKind}
     * values: {@code VARIABLE_DECLARATION} → {@code VARIABLE_INITIALIZER},
     * {@code VARIABLE_ASSIGNMENT} → {@code VARIABLE_ASSIGNMENT_TARGET},
     * and every other kind → {@code TYPED_BOUNDARY}. The map is total
     * and closed — an unknown kind cannot be expressed and there is no
     * fallback member.
     *
     * @param kind the closed boundary kind; non-null
     * @return the position kind
     */
    public static PositionKind positionKindOf(BoundaryKind kind) {
        Objects.requireNonNull(kind, "kind must not be null");
        return switch (kind) {
            case VARIABLE_DECLARATION -> PositionKind.VARIABLE_INITIALIZER;
            case VARIABLE_ASSIGNMENT -> PositionKind.VARIABLE_ASSIGNMENT_TARGET;
            case CLASS_FIELD_ASSIGNMENT, ARRAY_ELEMENT_ASSIGNMENT, BYTE_ELEMENT_ASSIGNMENT,
                 ARRAY_ELEMENT_READ, BYTE_ELEMENT_READ,
                 ARRAY_ELEMENT_DELETE, ARRAY_LITERAL_ELEMENT, FUNCTION_PARAMETER,
                 FUNCTION_RETURN, ASYNC_COMPLETION, CLASS_LITERAL_FIELD, CLASS_DEFAULT_FIELD,
                 UNTYPED_CLASS_INPUT, OPTIONAL_FIELD_READ, CONTEXTUAL_TABLE_READ,
                 IMPORTED_MEMBER_READ, MODULE_EXPORT, HOST_TO_DEAL, DEAL_TO_HOST,
                 STDLIB_PARAMETER, STDLIB_RETURN, EXTERNAL_PARAMETER, EXTERNAL_RETURN,
                 JSON_FROM_FIELD, JSON_TO_FIELD -> PositionKind.TYPED_BOUNDARY;
        };
    }

    /**
     * True exactly for the two variable positions — the only positions
     * whose classification admits the adaptation arm (B6: boundaries
     * never adapt).
     *
     * @param kind the closed boundary kind; non-null
     * @return {@code true} iff the kind is a variable position
     */
    public static boolean variablePosition(BoundaryKind kind) {
        return positionKindOf(kind) != PositionKind.TYPED_BOUNDARY;
    }

    /**
     * True iff the position's classification admits the adaptation arm:
     * {@code VARIABLE_DECLARATION} and {@code VARIABLE_ASSIGNMENT} only
     * (B6 — the classifier admits no adaptation arm for any other
     * {@link BoundaryKind}).
     *
     * @param kind the closed boundary kind; non-null
     * @return {@code true} iff the kind admits adaptation
     */
    public static boolean admitsAdaptation(BoundaryKind kind) {
        return variablePosition(kind);
    }

    // =========================================================================
    // The closed creation-rule decision
    // =========================================================================

    /**
     * The closed variable-position decision (B6/D15) over checker facts:
     * exact signature → {@link Disposition#DIRECT_STORE};
     * assignable-but-not-exact → {@link Disposition#ADAPT};
     * non-assignable → {@link Disposition#NON_ASSIGNABLE}; a
     * non-function-typed target → {@link Disposition#NOT_FUNCTION_FLOW}.
     *
     * @param sourceType the source expression's checked type; non-null
     * @param targetType the declared/inferred binding type; non-null
     * @return the closed disposition
     */
    public static Disposition variableDisposition(Type sourceType, Type targetType) {
        Objects.requireNonNull(sourceType, "sourceType must not be null");
        Objects.requireNonNull(targetType, "targetType must not be null");
        if (!(targetType instanceof Type.Func targetFunc)) {
            return Disposition.NOT_FUNCTION_FLOW;
        }
        if (!(sourceType instanceof Type.Func sourceFunc)) {
            return Disposition.NON_ASSIGNABLE;
        }
        if (Types.equals(sourceFunc, targetFunc)) {
            return Disposition.DIRECT_STORE;
        }
        if (Types.isAssignable(sourceFunc, targetFunc)) {
            return Disposition.ADAPT;
        }
        return Disposition.NON_ASSIGNABLE;
    }

    /**
     * The closed assignable-but-not-exact re-derivation over checked
     * function types (B6/{@code ADAPTER_PAIR}): identical async marker,
     * identical return type, {@code M <= N} with exactly equal leading M
     * parameter types and {@code M < N}.
     *
     * @param source the source function type; non-null
     * @param target the target function type; non-null
     * @return {@code true} iff the pair is assignable-but-not-exact
     */
    public static boolean assignableButNotExact(Type.Func source, Type.Func target) {
        Objects.requireNonNull(source, "source must not be null");
        Objects.requireNonNull(target, "target must not be null");
        if (source.isAsync() != target.isAsync()) {
            return false;
        }
        if (!Types.equals(source.returnType(), target.returnType())) {
            return false;
        }
        int sourceCount = source.paramTypes().size();
        int targetCount = target.paramTypes().size();
        if (sourceCount >= targetCount) {
            return false;
        }
        for (int i = 0; i < sourceCount; i++) {
            if (!Types.equals(source.paramTypes().get(i), target.paramTypes().get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * The closed assignable-but-not-exact re-derivation over
     * {@link RuntimeDescriptor.Func} signatures (the candidate's
     * signatures): identical async marker, identical return type,
     * {@code M <= N} with exactly equal leading M parameter types and
     * {@code M < N}.
     *
     * @param source the source signature; non-null
     * @param target the target signature; non-null
     * @return {@code true} iff the pair is assignable-but-not-exact
     */
    public static boolean assignableButNotExact(RuntimeDescriptor.Func source,
                                                RuntimeDescriptor.Func target) {
        Objects.requireNonNull(source, "source must not be null");
        Objects.requireNonNull(target, "target must not be null");
        if (source.isAsync() != target.isAsync()) {
            return false;
        }
        if (!source.returnType().equals(target.returnType())) {
            return false;
        }
        int sourceCount = source.paramTypes().size();
        int targetCount = target.paramTypes().size();
        if (sourceCount >= targetCount) {
            return false;
        }
        for (int i = 0; i < sourceCount; i++) {
            if (!source.paramTypes().get(i).equals(target.paramTypes().get(i))) {
                return false;
            }
        }
        return true;
    }

    // =========================================================================
    // Position classification
    // =========================================================================

    /**
     * Classifies one function-typed position of the closed position set:
     * the two variable positions run the closed variable decision (B6 —
     * exact → direct store, assignable-but-not-exact → one adaptation
     * candidate with the derived signatures, the proof fact, the wiring
     * point, and the producer facts; non-assignable → the recorded
     * E8010 failure expectation); every other position is a typed
     * boundary (never adapts — direct flow with the recorded E8010
     * expectation for any function-typed mismatch including
     * {@code M < N}).
     *
     * @param kind          the closed boundary kind of the position's
     *                      boundary chain; non-null
     * @param sourceType    the source expression's checked type; non-null
     * @param targetType    the declared/inferred binding type (variable
     *                      positions) or the position's checked
     *                      descriptor type (boundary positions); non-null
     * @param proof         the recorded proof fact of the source binding
     *                      (variable positions; absent for
     *                      non-binding sources); non-null, ignored for
     *                      boundary positions
     * @param wiringPoint   the prepared wiring point (variable
     *                      positions); non-null, ignored for boundary
     *                      positions
     * @param producerFacts the registry child's producer facts of a
     *                      host/external function-value source (absent
     *                      otherwise); non-null, ignored for boundary
     *                      positions
     * @return the closed classification
     */
    public static PositionClassification classify(BoundaryKind kind, Type sourceType,
                                                  Type targetType,
                                                  Optional<BindingImmutabilityProof> proof,
                                                  WiringPoint wiringPoint,
                                                  Optional<FunctionBindingRegistry
                                                      .FunctionValueMaterialization>
                                                      producerFacts) {
        Objects.requireNonNull(kind, "kind must not be null");
        if (variablePosition(kind)) {
            return classifyVariablePosition(kind, sourceType, targetType, proof,
                wiringPoint, producerFacts);
        }
        return classifyBoundaryPosition(kind, sourceType, targetType);
    }

    /**
     * The closed variable-position classification (B6): the closed
     * decision plus, for the {@code ADAPT} arm, the single derived
     * adaptation candidate — the source signature from the source
     * expression's checked type, the target signature from the declared
     * binding signature, the recorded proof fact for the shape-map
     * child (B7), the prepared wiring point, and the producer facts of
     * a host/external source (the registry child's T4 seam) — and, for
     * the {@code NON_ASSIGNABLE} arm, the recorded
     * {@code FUNCTION_SIGNATURE} E8010 failure expectation at the
     * position's own boundary.
     *
     * @param kind          exactly {@code VARIABLE_DECLARATION} or
     *                      {@code VARIABLE_ASSIGNMENT}; non-null
     * @param sourceType    the source expression's checked type; non-null
     * @param targetType    the declared/inferred binding type; non-null
     * @param proof         the recorded proof fact of the source binding
     *                      (absent for non-binding sources); non-null
     * @param wiringPoint   the prepared wiring point; non-null
     * @param producerFacts the producer facts of a host/external
     *                      function-value source (absent otherwise);
     *                      non-null
     * @return the closed variable-position classification
     * @throws IllegalArgumentException if {@code kind} is not a variable
     *                                  position
     */
    public static PositionClassification classifyVariablePosition(
            BoundaryKind kind, Type sourceType, Type targetType,
            Optional<BindingImmutabilityProof> proof, WiringPoint wiringPoint,
            Optional<FunctionBindingRegistry.FunctionValueMaterialization> producerFacts) {
        Objects.requireNonNull(kind, "kind must not be null");
        Objects.requireNonNull(sourceType, "sourceType must not be null");
        Objects.requireNonNull(targetType, "targetType must not be null");
        Objects.requireNonNull(proof, "proof must not be null");
        Objects.requireNonNull(wiringPoint, "wiringPoint must not be null");
        Objects.requireNonNull(producerFacts, "producerFacts must not be null");
        PositionKind positionKind = positionKindOf(kind);
        if (positionKind == PositionKind.TYPED_BOUNDARY) {
            throw new IllegalArgumentException("the variable-position classifier admits "
                + "exactly VARIABLE_DECLARATION and VARIABLE_ASSIGNMENT; got " + kind);
        }
        Disposition disposition = variableDisposition(sourceType, targetType);
        return switch (disposition) {
            case ADAPT -> {
                if (sourceType instanceof Type.Func sourceFunc
                        && targetType instanceof Type.Func targetFunc
                        && !assignableButNotExact(sourceFunc, targetFunc)) {
                    throw new IllegalStateException("the ADAPT arm requires an "
                        + "assignable-but-not-exact pair; got source "
                        + sourceFunc.paramTypes() + " target " + targetFunc.paramTypes()
                        + " (producer defect)");
                }
                AdaptationCandidate candidate = new AdaptationCandidate(
                    funcDescriptorOf(sourceType), funcDescriptorOf(targetType), proof,
                    wiringPoint, producerFacts);
                yield new PositionClassification(positionKind, kind, disposition,
                    Optional.of(candidate), Optional.empty());
            }
            case NON_ASSIGNABLE -> new PositionClassification(positionKind, kind,
                disposition, Optional.empty(), Optional.of(e8010Expectation(kind)));
            default -> new PositionClassification(positionKind, kind, disposition,
                Optional.empty(), Optional.empty());
        };
    }

    /**
     * The closed typed-boundary-position classification (B6):
     * {@link Disposition#BOUNDARY_DIRECT} always — the classifier admits
     * no adaptation arm for any {@link BoundaryKind} other than
     * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} — with
     * the recorded {@code FUNCTION_SIGNATURE} E8010 failure expectation
     * for a function-typed position whose source/target pair is any
     * mismatch including {@code M < N} (the executed rejection is E4's
     * boundary machinery — the closed boundary-assignment table's
     * descriptor-kind rule — pinned by the
     * {@code jvm-fv-sig-check-return-error} behavior; this classifier
     * records the expectation only).
     *
     * @param kind       a boundary kind other than the two variable
     *                   positions; non-null
     * @param sourceType the source value's checked type; non-null
     * @param targetType the position's checked descriptor type; non-null
     * @return the closed boundary-position classification
     * @throws IllegalArgumentException if {@code kind} is a variable
     *                                  position
     */
    public static PositionClassification classifyBoundaryPosition(BoundaryKind kind,
                                                                  Type sourceType,
                                                                  Type targetType) {
        Objects.requireNonNull(kind, "kind must not be null");
        Objects.requireNonNull(sourceType, "sourceType must not be null");
        Objects.requireNonNull(targetType, "targetType must not be null");
        if (variablePosition(kind)) {
            throw new IllegalArgumentException("the boundary-position classifier admits "
                + "every BoundaryKind except VARIABLE_DECLARATION and "
                + "VARIABLE_ASSIGNMENT; got " + kind);
        }
        boolean expectation = targetType instanceof Type.Func
            && !Types.equals(sourceType, targetType);
        return new PositionClassification(PositionKind.TYPED_BOUNDARY, kind,
            Disposition.BOUNDARY_DIRECT, Optional.empty(),
            expectation ? Optional.of(e8010Expectation(kind)) : Optional.empty());
    }

    // =========================================================================
    // Derivation and expectation helpers
    // =========================================================================

    /**
     * The single descriptor producer of the classifier (the verbatim D2
     * table): the source/target signatures the adaptation candidate
     * carries derive from the checked types through exactly
     * {@link DescriptorService#describe(Type)}. A defect is a
     * producer-defect failure — never an invented signature.
     */
    private static RuntimeDescriptor.Func funcDescriptorOf(Type type) {
        try {
            return (RuntimeDescriptor.Func) DescriptorService.describe(type);
        } catch (DescriptorService.Defect defect) {
            throw new IllegalStateException("the creation-rule classifier derives "
                + "function signatures from checked types through DescriptorService "
                + "only: " + defect.getMessage(), defect);
        }
    }

    /**
     * The recorded {@code FUNCTION_SIGNATURE} E8010 failure expectation
     * at the given position's boundary: the closed code, policy, and
     * canonical primary message template come from the closed
     * failure-contract registry's {@code FUNCTION_SIGNATURE} row — the
     * same row E4's boundary machinery executes. This is the
     * classification-level expectation only; the boundary op and its
     * executed check are E4's.
     *
     * @param boundaryKind the position's boundary kind; non-null
     * @return the recorded expectation
     */
    public static FailureExpectation e8010Expectation(BoundaryKind boundaryKind) {
        Objects.requireNonNull(boundaryKind, "boundaryKind must not be null");
        deal.semantic.ir.FailurePolicyRow row =
            FailureContractRegistry.row(FailurePolicyId.FUNCTION_SIGNATURE);
        if (row.code() == null || row.template() == null) {
            throw new IllegalStateException("the closed FUNCTION_SIGNATURE row pins the "
                + "E8010 code and the canonical template; a broken row is a producer "
                + "defect");
        }
        return new FailureExpectation(row.code().code(), FailurePolicyId.FUNCTION_SIGNATURE,
            boundaryKind, row.template());
    }
}
