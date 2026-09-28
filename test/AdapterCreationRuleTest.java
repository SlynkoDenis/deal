package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.AdapterCreationRule;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The creation-rule child's tests (ISSUE-0449 sequencing item 6): the
 * closed {@code FUNCTION_ADAPT} creation-rule position classification
 * (B6) and its direct flows — exact-signature initializer/assignment
 * positions store the value directly with no {@code FUNCTION_ADAPT};
 * assignable-but-not-exact positions classify to exactly one
 * adaptation candidate with the derived source/target signatures, the
 * recorded proof fact (B7), the prepared wiring point, and the
 * producer facts of host/external sources (the registry child's T4
 * seam); typed boundary positions never adapt. Driven through the
 * child's public lowering entry point
 * ({@link SemanticLowerer#lowerModuleCreationRuleCore}) — the
 * group-core walk (the same walk the registry and proof children
 * populate, B5/B7) with the classification active.
 *
 * <p><b>Zero-emission boundary.</b> Every unit this child produces
 * contains zero {@code FUNCTION_ADAPT} ops (mode selection, payload
 * construction, and emission are the shape-map child's obligations) and
 * the classification is purely observational: the same checked module
 * lowers byte-identically through the proof child and this child.
 * Boundary-op production and execution stay E4's; the recorded
 * {@code FUNCTION_SIGNATURE} E8010 expectations are classification
 * facts only — the executed boundary rejection (the pinned
 * {@code jvm-fv-sig-check-return-error} behavior, whose retained-side
 * fixture stays green as the gate's authority) is driven by the
 * integration child through E4's machinery.</p>
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>an exact-signature initializer and an exact-signature
 *       assignment each lower with zero {@code FUNCTION_ADAPT} and a
 *       direct store (the boundary input and the commit operand are
 *       the source value itself);</li>
 *   <li>an assignable-but-not-exact initializer and assignment each
 *       classify to exactly one adaptation candidate whose
 *       source/target signature pair re-derives as
 *       assignable-but-not-exact, with the position's wiring point
 *       naming the adapted position's own
 *       {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
 *       boundary op and the proof fact recorded — combined with the
 *       proof child (fails if the proof module is broken);</li>
 *   <li>a binding source defeated by an assignment records no proof
 *       fact in its candidate (combined with the proof child);</li>
 *   <li>non-assignable pairs are frontend rejections (E5004/E3001) and
 *       never reach lowering from checked source; the classifier's
 *       closed {@code NON_ASSIGNABLE} arm records the
 *       {@code FUNCTION_SIGNATURE} E8010 failure expectation at the
 *       position's own boundary;</li>
 *   <li>the position classifier admits no adaptation arm for any
 *       {@link BoundaryKind} other than
 *       {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} —
 *       asserted over the classifier's closed position set (all 25
 *       kinds); a mismatched function-typed pair at any boundary
 *       position — {@code M < N} included — classifies
 *       {@code BOUNDARY_DIRECT} with the E8010 expectation recorded;</li>
 *   <li>the pinned return shape's structural facts: a
 *       {@code FUNCTION_RETURN} position returning {@code (int)=>int}
 *       across a declared {@code (a:int,b:int)=>int} return admits no
 *       adaptation arm, classifies {@code BOUNDARY_DIRECT}, and records
 *       the E8010 {@code FUNCTION_SIGNATURE} expectation (the boundary
 *       op, its function-descriptor cell, and the executed E8010 belong
 *       to E4's machinery — this child asserts the structural facts
 *       only);</li>
 *   <li>a function-typed array element position with an {@code M < N}
 *       value lowers with zero adapters and direct flow into the
 *       position's {@code ARRAY_ELEMENT_ASSIGNMENT} boundary slot
 *       (checker-admitted arity extension at the element position; the
 *       executed rejection is the boundary machinery's);</li>
 *   <li>an exact-signature direct store of a {@code CLOSURE_NEW}
 *       result — combined with the closure child (fails if the closure
 *       module is broken);</li>
 *   <li>a host/external import-read source classifies to one candidate
 *       whose producer facts come from the registry child's
 *       materialization seam (the candidate records the facts; the
 *       closed-map mode is the shape-map child's decision);</li>
 *   <li>repeated lowering yields identical classification records and
 *       byte-identical unit dumps (the classification is purely
 *       observational).</li>
 * </ul>
 */
public class AdapterCreationRuleTest {

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
    // Fixed invocation facts
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new ExternalModuleInterface(MODULE, ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Checked-source slices and the entry-point driver
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver("test.deal", null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check("test.deal", symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(),
            "the slice checks cleanly: " + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of("test.deal"), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    private static SemanticLowerer.CreationRuleCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleCreationRuleCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /**
     * A lowered-and-validated result for the named test, or {@code null}
     * when the frontend or the lowering failed (already recorded).
     */
    private static SemanticLowerer.CreationRuleCoreResult loweredResult(String source,
                                                                        String what) {
        SemanticLowerer.CreationRuleCoreResult result = lowerSlice(source);
        if (result == null) {
            return null;
        }
        check(result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers to a validated unit: "
                + (result.lowering() == null ? "null" : result.lowering().diagnostics()));
        if (result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** The produced ops of exactly the named boundary kind. */
    private static List<SemanticOp> boundariesOfKind(List<SemanticOp> ops,
                                                     BoundaryKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && op.payload() instanceof KindPayload.BoundaryPayload payload
                    && payload.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** The classification records of exactly the named boundary kind. */
    private static List<AdapterCreationRule.PositionClassification> classificationsOf(
            AdapterCreationRule.CreationRuleFacts facts, BoundaryKind kind) {
        List<AdapterCreationRule.PositionClassification> matches = new ArrayList<>();
        for (AdapterCreationRule.PositionClassification classification
                : facts.classifications()) {
            if (classification.boundaryKind() == kind) {
                matches.add(classification);
            }
        }
        return matches;
    }

    /** The binding-core facts record of the declared name (exactly one). */
    private static SemanticLowerer.BindingCoreBinding fact(
            SemanticLowerer.BindingCoreFacts facts, String name) {
        List<SemanticLowerer.BindingCoreBinding> matches = new ArrayList<>();
        for (SemanticLowerer.BindingCoreBinding binding : facts.bindings()) {
            if (binding.name().equals(name)) {
                matches.add(binding);
            }
        }
        check(matches.size() == 1, "exactly one BindingId registered for '" + name
            + "'; got " + matches.size());
        return matches.size() == 1 ? matches.get(0) : null;
    }

    /** The op id of a listed child op (the ASSIGN/DELETE chain surface). */
    private static SemanticOp opOf(List<SemanticOp> ops, OpId opId) {
        for (SemanticOp op : ops) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        fail("op " + opId + " not found in the produced op list");
        return null;
    }

    /** The closed assignable-but-not-exact checked pair for classifier-level tests. */
    private static final Type.Func SOURCE_M1 =
        Types.func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE);
    private static final Type.Func TARGET_N2 =
        Types.func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE), Type.Int.INSTANCE);

    // =========================================================================
    // Tests
    // =========================================================================

    /**
     * An exact-signature initializer: the value is stored directly —
     * the boundary input and the INIT operand are the source value
     * itself, zero {@code FUNCTION_ADAPT} ops exist, and the position
     * classifies {@code DIRECT_STORE}.
     */
    static void testExactSignatureInitializerStoresDirectly() {
        System.out.println("-- exact-signature initializer: direct store, zero adapters --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let g: (y: int) => null = inner;
            }
            """, "the exact-signature initializer slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit");

        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        if (inner == null || g == null) {
            return;
        }
        // The single load of inner publishes the value the store consumes.
        List<SemanticOp> loads = ofKind(ops, SemanticOpKind.BINDING_LOAD);
        check(loads.size() == 1, "exactly one BINDING_LOAD (of inner); got " + loads.size());
        if (loads.size() != 1) {
            return;
        }
        ValueId sourceValue = (ValueId) loads.get(0).result();
        check(loads.get(0).payload() instanceof KindPayload.BindingLoadPayload loadPayload
                && loadPayload.binding().equals(inner.binding()),
            "the load names inner's binding (the hoisted module function's cell)");

        // The declaration boundary takes the source value directly.
        List<SemanticOp> declarations = boundariesOfKind(ops,
            BoundaryKind.VARIABLE_DECLARATION);
        check(declarations.size() == 1,
            "exactly one VARIABLE_DECLARATION boundary; got " + declarations.size());
        if (declarations.size() == 1) {
            KindPayload.BoundaryPayload boundary =
                (KindPayload.BoundaryPayload) declarations.get(0).payload();
            check(boundary.input().equals(sourceValue),
                "the declaration boundary's input is the source value itself (direct "
                    + "flow into the position's boundary slot)");
            check(boundary.descriptor() instanceof RuntimeDescriptor.Func func
                    && func.paramTypes().size() == 1
                    && func.returnType() instanceof RuntimeDescriptor.Null,
                "the boundary checks g's declared (y:int) => null signature");
        }
        // The INIT commits the source value directly (no intermediate op).
        SemanticOp init = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload payload
                    && payload.binding().equals(g.binding())) {
                init = op;
            }
        }
        check(init != null, "g's BINDING_INIT exists");
        if (init != null) {
            KindPayload.BindingInitPayload payload =
                (KindPayload.BindingInitPayload) init.payload();
            check(payload.value().equals(sourceValue),
                "g's INIT operand is the source value itself (direct store)");
        }
        // The position classification: DIRECT_STORE, no candidate.
        List<AdapterCreationRule.PositionClassification> classifications =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        check(classifications.size() == 1,
            "exactly one VARIABLE_DECLARATION classification; got " + classifications.size());
        if (classifications.size() == 1) {
            AdapterCreationRule.PositionClassification classification = classifications.get(0);
            check(classification.disposition()
                    == AdapterCreationRule.Disposition.DIRECT_STORE,
                "the position classifies DIRECT_STORE (exact signature)");
            check(classification.candidate().isEmpty(),
                "no adaptation candidate exists for an exact position");
            check(classification.failureExpectation().isEmpty(),
                "no failure expectation exists for an exact position");
        }
    }

    /**
     * An exact-signature assignment: the VARIABLE chain stores the
     * value directly — the assignment boundary input and the
     * BINDING_STORE operand are the source value itself, zero
     * {@code FUNCTION_ADAPT} ops, and the position classifies
     * {@code DIRECT_STORE}.
     */
    static void testExactSignatureAssignmentStoresDirectly() {
        System.out.println("-- exact-signature assignment: direct store, zero adapters --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let g: (y: int) => null = inner;
              g = inner;
            }
            """, "the exact-signature assignment slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit");

        // The VARIABLE assignment chain: [valueOp, boundaryOp, commitOp].
        SemanticOp assign = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.ASSIGN)) {
            if (op.payload() instanceof KindPayload.AssignPayload payload
                    && payload.targetKind() == deal.semantic.ir.AssignTargetKind.VARIABLE) {
                assign = op;
            }
        }
        check(assign != null, "the VARIABLE ASSIGN chain exists");
        if (assign == null) {
            return;
        }
        KindPayload.AssignPayload chain = (KindPayload.AssignPayload) assign.payload();
        check(chain.childOps().size() == 3,
            "the VARIABLE chain is [valueOp, boundaryOp, commitOp]; got "
                + chain.childOps().size());
        if (chain.childOps().size() != 3) {
            return;
        }
        SemanticOp valueOp = opOf(ops, chain.childOps().get(0));
        SemanticOp boundary = opOf(ops, chain.childOps().get(1));
        SemanticOp commit = opOf(ops, chain.childOps().get(2));
        check(valueOp != null && valueOp.kind() == SemanticOpKind.BINDING_LOAD,
            "the value child is the BINDING_LOAD of f");
        if (valueOp == null || boundary == null || commit == null) {
            return;
        }
        ValueId sourceValue = (ValueId) valueOp.result();
        check(boundary.kind() == SemanticOpKind.BOUNDARY
                && boundary.payload() instanceof KindPayload.BoundaryPayload boundaryPayload
                && boundaryPayload.kind() == BoundaryKind.VARIABLE_ASSIGNMENT
                && boundaryPayload.input().equals(sourceValue),
            "the assignment boundary's input is the source value itself (direct flow "
                + "into the position's boundary slot)");
        check(commit.kind() == SemanticOpKind.BINDING_STORE
                && commit.payload() instanceof KindPayload.BindingStorePayload storePayload
                && storePayload.value().equals(sourceValue),
            "the BINDING_STORE operand is the source value itself (direct store)");

        // Both positions classify DIRECT_STORE.
        List<AdapterCreationRule.PositionClassification> initializer =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        List<AdapterCreationRule.PositionClassification> assignment =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_ASSIGNMENT);
        check(initializer.size() == 1
                && initializer.get(0).disposition()
                    == AdapterCreationRule.Disposition.DIRECT_STORE,
            "the initializer position classifies DIRECT_STORE");
        check(assignment.size() == 1
                && assignment.get(0).disposition()
                    == AdapterCreationRule.Disposition.DIRECT_STORE,
            "the assignment position classifies DIRECT_STORE");
    }

    /**
     * An assignable-but-not-exact initializer: exactly one adaptation
     * candidate — the derived source/target signature pair re-derives
     * as assignable-but-not-exact, the wiring point names the adapted
     * position's own {@code VARIABLE_DECLARATION} boundary op, and the
     * proof fact of the unassigned source binding is recorded
     * (combined with the proof child — fails if the proof module is
     * broken). Zero {@code FUNCTION_ADAPT} ops (emission is the
     * shape-map child's).
     */
    static void testAssignableButNotExactInitializerClassifiesOneCandidate() {
        System.out.println("-- assignable-but-not-exact initializer: one candidate, "
            + "derived pair, wiring point, proof fact --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let g: (a: int, b: int) => null = inner;
            }
            """, "the arity-extension initializer slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit (this child emits no adapter)");

        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        if (inner == null) {
            return;
        }
        List<AdapterCreationRule.PositionClassification> classifications =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        check(classifications.size() == 1,
            "exactly one VARIABLE_DECLARATION classification; got " + classifications.size());
        if (classifications.size() != 1) {
            return;
        }
        AdapterCreationRule.PositionClassification classification = classifications.get(0);
        check(classification.disposition() == AdapterCreationRule.Disposition.ADAPT,
            "the position classifies ADAPT (assignable-but-not-exact)");
        check(classification.candidate().isPresent(),
            "exactly one adaptation candidate is recorded");
        if (classification.candidate().isEmpty()) {
            return;
        }
        AdapterCreationRule.AdaptationCandidate candidate = classification.candidate().get();
        check(candidate.sourceSignature().canonicalSpecText().equals("(int)->null"),
            "the source signature derives from the source expression's checked type "
                + "(x:int) => null; got " + candidate.sourceSignature().canonicalSpecText());
        check(candidate.targetSignature().canonicalSpecText().equals("(int,int)->null"),
            "the target signature derives from the declared binding signature "
                + "(a:int,b:int) => null; got " + candidate.targetSignature().canonicalSpecText());
        check(candidate.reDerivesAsAssignableButNotExact(),
            "the candidate's source/target pair re-derives as assignable-but-not-exact "
                + "(identical async marker, identical return type, M=1 <= N=2 with equal "
                + "leading parameter and M < N)");
        check(candidate.wiringPoint().targetKind()
                == AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY,
            "the wiring point names the adapted position's own VARIABLE_DECLARATION "
                + "boundary chain");
        List<SemanticOp> declarations = boundariesOfKind(ops,
            BoundaryKind.VARIABLE_DECLARATION);
        check(declarations.size() == 1
                && declarations.get(0).opId().equals(candidate.wiringPoint().opId()),
            "the wiring point's op id is the position's VARIABLE_DECLARATION boundary op");
        check(candidate.proof().isPresent(),
            "the proof fact of the unassigned source binding is recorded for the "
                + "shape-map child (B7)");
        if (candidate.proof().isPresent()) {
            check(candidate.proof().get().binding().equals(inner.binding())
                    && candidate.proof().get().generation() == 0,
                "the proof fact names the source binding's dominant {binding, generation} "
                    + "= {inner, 0}");
        }
        // Combined with the proof child: the proof surface agrees.
        check(result.proofFacts().proven(inner.binding(), 0),
            "the proof surface proves {inner, 0} (the proof child's derivation)");
    }

    /**
     * An assignable-but-not-exact assignment: exactly one adaptation
     * candidate whose wiring point names the adapted position's own
     * {@code VARIABLE_ASSIGNMENT} boundary op; zero
     * {@code FUNCTION_ADAPT} ops.
     */
    static void testAssignableButNotExactAssignmentClassifiesOneCandidate() {
        System.out.println("-- assignable-but-not-exact assignment: one candidate, "
            + "VARIABLE_ASSIGNMENT wiring point --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let g: (a: int, b: int) => null = inner;
              g = inner;
            }
            """, "the arity-extension assignment slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit");

        List<AdapterCreationRule.PositionClassification> assignment =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_ASSIGNMENT);
        check(assignment.size() == 1,
            "exactly one VARIABLE_ASSIGNMENT classification; got " + assignment.size());
        if (assignment.size() != 1) {
            return;
        }
        AdapterCreationRule.PositionClassification classification = assignment.get(0);
        check(classification.disposition() == AdapterCreationRule.Disposition.ADAPT
                && classification.candidate().isPresent(),
            "the assignment position classifies ADAPT with exactly one candidate");
        if (classification.candidate().isEmpty()) {
            return;
        }
        AdapterCreationRule.AdaptationCandidate candidate = classification.candidate().get();
        check(candidate.sourceSignature().canonicalSpecText().equals("(int)->null")
                && candidate.targetSignature().canonicalSpecText().equals("(int,int)->null"),
            "the candidate's derived pair is ((int) => null, (int,int) => null)");
        check(candidate.reDerivesAsAssignableButNotExact(),
            "the candidate's pair re-derives as assignable-but-not-exact");
        check(candidate.wiringPoint().targetKind()
                == AdapterCreationRule.WiringTargetKind.VARIABLE_ASSIGNMENT_BOUNDARY,
            "the wiring point names the adapted position's own VARIABLE_ASSIGNMENT "
                + "boundary chain");
        List<SemanticOp> assignmentBoundaries = boundariesOfKind(ops,
            BoundaryKind.VARIABLE_ASSIGNMENT);
        check(assignmentBoundaries.size() == 1
                && assignmentBoundaries.get(0).opId().equals(candidate.wiringPoint().opId()),
            "the wiring point's op id is the position's VARIABLE_ASSIGNMENT boundary op");
        check(candidate.proof().isPresent(),
            "the unassigned source binding's proof fact is recorded");
        // The initializer of the same slice also classifies ADAPT with
        // its own wiring point (one candidate per position).
        List<AdapterCreationRule.PositionClassification> initializer =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        check(initializer.size() == 1
                && initializer.get(0).disposition() == AdapterCreationRule.Disposition.ADAPT
                && initializer.get(0).candidate().isPresent()
                && initializer.get(0).candidate().get().wiringPoint().targetKind()
                    == AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY,
            "the initializer position keeps its own candidate and its own "
                + "VARIABLE_DECLARATION wiring point (exactly one candidate per "
                + "adapted position)");
    }

    /**
     * A binding source defeated by an assignment: the candidate records
     * no proof fact (B7 — an unproven binding is the shape-map child's
     * SHARED_CELL arm; the mode decision is the shape-map child's), and
     * the proof surface agrees (combined with the proof child).
     */
    static void testAssignedBindingSourceCandidateCarriesNoProofFact() {
        System.out.println("-- assigned binding source: candidate carries no proof fact --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let f: (y: int) => null = inner;
              f = f;
              let g: (a: int, b: int) => null = f;
            }
            """, "the assigned-source slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        check(ofKind(unit.ops(), SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit");

        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        if (f == null) {
            return;
        }
        // Two declaration positions classify: f's exact initializer
        // (DIRECT_STORE) and g's arity-extension initializer (ADAPT).
        List<AdapterCreationRule.PositionClassification> classifications =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        check(classifications.size() == 2,
            "exactly two VARIABLE_DECLARATION classifications (f's and g's); got "
                + classifications.size());
        AdapterCreationRule.PositionClassification adapted = null;
        int direct = 0;
        for (AdapterCreationRule.PositionClassification classification : classifications) {
            if (classification.disposition() == AdapterCreationRule.Disposition.DIRECT_STORE) {
                direct++;
            }
            if (classification.disposition() == AdapterCreationRule.Disposition.ADAPT) {
                adapted = classification;
            }
        }
        check(direct == 1 && adapted != null,
            "exactly one DIRECT_STORE classification (f's exact initializer) and one "
                + "ADAPT classification (g's initializer)");
        if (adapted != null && adapted.candidate().isPresent()) {
            check(adapted.candidate().get().proof().isEmpty(),
                "the candidate records no proof fact — the body assignment defeated the "
                    + "source binding's proof (conservative, B7)");
        } else {
            fail("g's ADAPT classification carries its candidate");
        }
        check(!result.proofFacts().proven(f.binding(), 0),
            "the proof surface agrees: {f, 0} carries no proof after the assignment");
        check(!result.proofFacts().assignments().isEmpty(),
            "the proof surface records the resolved assignment fact of f = f");
    }

    /**
     * Non-assignable pairs never reach lowering from checked source
     * (E5004/E3001 frontend rejections), and the classifier's closed
     * {@code NON_ASSIGNABLE} arm records the
     * {@code FUNCTION_SIGNATURE} E8010 failure expectation at the
     * position's own boundary (the executed check is E4's machinery).
     */
    static void testNonAssignablePairsAreFrontendRejectedAndExpectationRecorded() {
        System.out.println("-- non-assignable pairs: frontend rejection plus the recorded "
            + "E8010 expectation --");

        // The reverse-arity slice: the checker rejects it (E5004), so no
        // such position reaches lowering from checked source.
        LexResult lex = new Lexer("""
            function wide(a: int, b: int): null {}
            function main(): null {
              let g: (x: int) => null = wide;
            }
            """, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        NameResolver nr = new NameResolver("test.deal", null);
        SymbolTable symTable = nr.resolve(parse.program());
        CheckResult checked = TypeChecker.check("test.deal", symTable, nr, parse.program());
        boolean frontendRejected = checked.hasErrors()
            && checked.diagnostics().stream().anyMatch(
                diagnostic -> diagnostic.code().equals(
                        deal.diagnostics.DiagnosticCode.E5004.code())
                    || diagnostic.code().equals(
                        deal.diagnostics.DiagnosticCode.E3001.code()));
        check(frontendRejected,
            "the reverse-arity initializer is a frontend rejection (E5004/E3001): "
                + checked.diagnostics());

        // The classifier's closed NON_ASSIGNABLE arm over the same pair.
        AdapterCreationRule.PositionClassification reverse =
            AdapterCreationRule.classifyVariablePosition(BoundaryKind.VARIABLE_DECLARATION,
                TARGET_N2, SOURCE_M1, Optional.empty(),
                new AdapterCreationRule.WiringPoint(new OpId(MODULE, 7001L),
                    AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY),
                Optional.empty());
        check(reverse.disposition() == AdapterCreationRule.Disposition.NON_ASSIGNABLE,
            "the reverse pair classifies NON_ASSIGNABLE");
        check(reverse.candidate().isEmpty(),
            "a non-assignable position records no adaptation candidate");
        check(reverse.failureExpectation().isPresent()
                && reverse.failureExpectation().get().code().equals("E8010")
                && reverse.failureExpectation().get().policy()
                    == FailurePolicyId.FUNCTION_SIGNATURE
                && reverse.failureExpectation().get().boundaryKind()
                    == BoundaryKind.VARIABLE_DECLARATION,
            "the non-assignable position records the E8010 FUNCTION_SIGNATURE failure "
                + "expectation at the position's own boundary (the executed check is "
                + "E4's machinery)");

        // A non-function source into a function-typed position: the same
        // closed arm (a host-materialized wrong signature fails the
        // position's own boundary via the descriptor-kind rule).
        AdapterCreationRule.PositionClassification nonFunction =
            AdapterCreationRule.classifyVariablePosition(BoundaryKind.VARIABLE_ASSIGNMENT,
                Type.Int.INSTANCE, TARGET_N2, Optional.empty(),
                new AdapterCreationRule.WiringPoint(new OpId(MODULE, 7002L),
                    AdapterCreationRule.WiringTargetKind.VARIABLE_ASSIGNMENT_BOUNDARY),
                Optional.empty());
        check(nonFunction.disposition() == AdapterCreationRule.Disposition.NON_ASSIGNABLE
                && nonFunction.failureExpectation().isPresent(),
            "a non-function source into a function-typed position classifies "
                + "NON_ASSIGNABLE with the recorded expectation");

        // A non-function-typed position stays outside the creation
        // rule's window.
        AdapterCreationRule.PositionClassification ordinary =
            AdapterCreationRule.classifyVariablePosition(BoundaryKind.VARIABLE_DECLARATION,
                Type.Int.INSTANCE, Type.Int.INSTANCE, Optional.empty(),
                new AdapterCreationRule.WiringPoint(new OpId(MODULE, 7003L),
                    AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY),
                Optional.empty());
        check(ordinary.disposition() == AdapterCreationRule.Disposition.NOT_FUNCTION_FLOW
                && ordinary.failureExpectation().isEmpty(),
            "a non-function-typed position classifies NOT_FUNCTION_FLOW (the "
                + "creation rule's window)");
    }

    /**
     * The classifier's closed position set: no adaptation arm exists
     * for any {@link BoundaryKind} other than
     * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} —
     * asserted over all 27 closed kinds (the two bytes element cells of
     * ISSUE-0626 included); a mismatched function-typed
     * pair (including {@code M < N}) at every boundary position
     * classifies {@code BOUNDARY_DIRECT} with the recorded E8010
     * expectation, and an exact pair records none.
     */
    static void testClassifierClosedPositionSetNeverAdaptsOutsideVariablePositions() {
        System.out.println("-- closed position set: boundaries never adapt (all 27 "
            + "BoundaryKinds) --");

        int variableKinds = 0;
        int boundaryKinds = 0;
        for (BoundaryKind kind : BoundaryKind.values()) {
            boolean variable = kind == BoundaryKind.VARIABLE_DECLARATION
                || kind == BoundaryKind.VARIABLE_ASSIGNMENT;
            AdapterCreationRule.PositionKind positionKind =
                AdapterCreationRule.positionKindOf(kind);
            check(AdapterCreationRule.admitsAdaptation(kind) == variable,
                "admitsAdaptation(" + kind + ") is " + variable + " (the classifier "
                    + "admits no adaptation arm for any other BoundaryKind)");
            if (variable) {
                variableKinds++;
                check(positionKind == (kind == BoundaryKind.VARIABLE_DECLARATION
                        ? AdapterCreationRule.PositionKind.VARIABLE_INITIALIZER
                        : AdapterCreationRule.PositionKind.VARIABLE_ASSIGNMENT_TARGET),
                    "positionKindOf(" + kind + ") maps to the variable position kind");
            } else {
                boundaryKinds++;
                check(positionKind == AdapterCreationRule.PositionKind.TYPED_BOUNDARY,
                    "positionKindOf(" + kind + ") maps to TYPED_BOUNDARY");
                // An M < N function-typed pair at the boundary position:
                // direct flow plus the recorded E8010 expectation.
                AdapterCreationRule.PositionClassification mismatch =
                    AdapterCreationRule.classifyBoundaryPosition(kind, SOURCE_M1, TARGET_N2);
                check(mismatch.disposition()
                        == AdapterCreationRule.Disposition.BOUNDARY_DIRECT,
                    kind + " with an M < N pair classifies BOUNDARY_DIRECT (never "
                        + "adapts)");
                check(mismatch.candidate().isEmpty(),
                    kind + " records no adaptation candidate");
                check(mismatch.failureExpectation().isPresent()
                        && mismatch.failureExpectation().get().code().equals("E8010")
                        && mismatch.failureExpectation().get().policy()
                            == FailurePolicyId.FUNCTION_SIGNATURE
                        && mismatch.failureExpectation().get().boundaryKind() == kind,
                    kind + " records the E8010 FUNCTION_SIGNATURE expectation at the "
                        + "position's own boundary (the executed rejection is E4's "
                        + "closed boundary-assignment table)");
                // An exact pair at the same boundary: direct flow, no
                // expectation (the exact-signature pass is the boundary
                // machinery's).
                AdapterCreationRule.PositionClassification exact =
                    AdapterCreationRule.classifyBoundaryPosition(kind, TARGET_N2, TARGET_N2);
                check(exact.disposition() == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                        && exact.failureExpectation().isEmpty(),
                    kind + " with an exact pair classifies BOUNDARY_DIRECT with no "
                        + "recorded expectation");
            }
        }
        check(variableKinds == 2 && boundaryKinds == 25,
            "the closed position set counts 2 variable positions and 25 typed boundary "
                + "positions; got " + variableKinds + "/" + boundaryKinds);
    }

    /**
     * The pinned return shape's structural facts
     * ({@code jvm-fv-sig-check-return-error}: returning {@code (int)=>int}
     * across a declared {@code (a:int,b:int)=>int} return): the
     * {@code FUNCTION_RETURN} position admits no adaptation arm,
     * classifies {@code BOUNDARY_DIRECT}, and records the E8010
     * {@code FUNCTION_SIGNATURE} expectation — this child asserts the
     * structural facts only (the boundary op, its function-descriptor
     * cell, and the executed E8010 before any invocation belong to E4's
     * machinery; the executed assertion is the integration child's T9
     * with the declared in-branch prerequisite, and the retained
     * fixture stays green as the retained-side authority).
     */
    static void testPinnedReturnBoundaryShapeStructuralFacts() {
        System.out.println("-- pinned return shape: structural facts only (no adapt "
            + "arm, recorded E8010 expectation) --");

        check(!AdapterCreationRule.admitsAdaptation(BoundaryKind.FUNCTION_RETURN),
            "FUNCTION_RETURN admits no adaptation arm (boundaries never adapt)");
        AdapterCreationRule.PositionClassification classification =
            AdapterCreationRule.classifyBoundaryPosition(BoundaryKind.FUNCTION_RETURN,
                SOURCE_M1, TARGET_N2);
        check(classification.positionKind() == AdapterCreationRule.PositionKind.TYPED_BOUNDARY
                && classification.disposition()
                    == AdapterCreationRule.Disposition.BOUNDARY_DIRECT,
            "the (int)=>int value across the declared (a:int,b:int)=>int return "
                + "classifies BOUNDARY_DIRECT — direct flow into the return position's "
                + "boundary slot, zero adapters");
        check(classification.candidate().isEmpty(),
            "no adaptation candidate exists for the return position");
        check(classification.failureExpectation().isPresent(),
            "the E8010 FUNCTION_SIGNATURE failure expectation is recorded for the "
                + "mismatch (M < N included) before any invocation — the executed "
                + "rejection is E4's closed boundary-assignment table");
        if (classification.failureExpectation().isPresent()) {
            AdapterCreationRule.FailureExpectation expectation =
                classification.failureExpectation().get();
            check(expectation.code().equals("E8010")
                    && expectation.policy() == FailurePolicyId.FUNCTION_SIGNATURE
                    && expectation.boundaryKind() == BoundaryKind.FUNCTION_RETURN,
                "the recorded expectation names E8010, FUNCTION_SIGNATURE, and the "
                    + "FUNCTION_RETURN boundary");
            String canonicalTemplate =
                FailureContractRegistry.row(FailurePolicyId.FUNCTION_SIGNATURE).template();
            check(expectation.messageTemplate().equals(canonicalTemplate),
                "the recorded expectation carries the registry's canonical primary "
                    + "template: " + canonicalTemplate);
        }
    }

    /**
     * A function-typed array element position with an {@code M < N}
     * value (checker-admitted arity extension at the element position):
     * the unit contains zero adapters and the value flows directly into
     * the position's {@code ARRAY_ELEMENT_ASSIGNMENT} boundary slot;
     * the position classifies {@code BOUNDARY_DIRECT} with the E8010
     * expectation recorded (the executed rejection is the boundary
     * machinery's — {@code ARRAY_WRITE_BOUNDS_THEN_ELEMENT} first, then
     * the element's descriptor-kind cell). The exact array literal
     * element position of the same slice classifies
     * {@code BOUNDARY_DIRECT} with no expectation.
     */
    static void testArrayElementPositionsFlowDirectlyWithZeroAdapters() {
        System.out.println("-- array element positions: direct flow into the boundary "
            + "slot, zero adapters --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function wide(a: int, b: int): null {}
            function main(): null {
              let arr: ((a: int, b: int) => null)[] = [wide];
              arr[0] = inner;
            }
            """, "the array-element slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit (boundary positions never adapt)");

        // The ARRAY_SLOT assignment chain:
        // [containerOp, keyOp, valueOp, lengthOp, normalizeOp, boundaryOp, commitOp].
        SemanticOp assign = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.ASSIGN)) {
            if (op.payload() instanceof KindPayload.AssignPayload payload
                    && payload.targetKind() == deal.semantic.ir.AssignTargetKind.ARRAY_SLOT) {
                assign = op;
            }
        }
        check(assign != null, "the ARRAY_SLOT ASSIGN chain exists");
        if (assign == null) {
            return;
        }
        KindPayload.AssignPayload chain = (KindPayload.AssignPayload) assign.payload();
        check(chain.childOps().size() == 7,
            "the ARRAY_SLOT chain carries its 7 children; got " + chain.childOps().size());
        if (chain.childOps().size() != 7) {
            return;
        }
        SemanticOp valueOp = opOf(ops, chain.childOps().get(2));
        SemanticOp elementBoundary = opOf(ops, chain.childOps().get(5));
        check(valueOp != null && valueOp.kind() == SemanticOpKind.BINDING_LOAD,
            "the value child is the BINDING_LOAD of f (the M < N source)");
        if (valueOp == null || elementBoundary == null) {
            return;
        }
        ValueId sourceValue = (ValueId) valueOp.result();
        check(elementBoundary.kind() == SemanticOpKind.BOUNDARY
                && elementBoundary.payload() instanceof KindPayload.BoundaryPayload payload
                && payload.kind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                && payload.input().equals(sourceValue),
            "the ARRAY_ELEMENT_ASSIGNMENT boundary's input is the M < N value itself — "
                + "direct flow into the position's boundary slot, zero adapters");

        // The classifications: the element assignment is a typed
        // boundary position (never adapts) with the recorded E8010
        // expectation; the array literal element is exact-direct.
        List<AdapterCreationRule.PositionClassification> elementAssignments =
            classificationsOf(result.creationFacts(), BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT);
        check(elementAssignments.size() == 1,
            "exactly one ARRAY_ELEMENT_ASSIGNMENT classification; got "
                + elementAssignments.size());
        if (elementAssignments.size() == 1) {
            AdapterCreationRule.PositionClassification classification =
                elementAssignments.get(0);
            check(classification.disposition()
                    == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                    && classification.candidate().isEmpty(),
                "the element position classifies BOUNDARY_DIRECT with no candidate "
                    + "(typed boundary positions never adapt)");
            check(classification.failureExpectation().isPresent()
                    && classification.failureExpectation().get().boundaryKind()
                        == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT,
                "the M < N element position records the E8010 expectation at the "
                    + "element boundary (the executed rejection is the boundary "
                    + "machinery's)");
        }
        List<AdapterCreationRule.PositionClassification> literalElements =
            classificationsOf(result.creationFacts(), BoundaryKind.ARRAY_LITERAL_ELEMENT);
        check(literalElements.size() == 1
                && literalElements.get(0).disposition()
                    == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                && literalElements.get(0).failureExpectation().isEmpty(),
            "the exact-signature array literal element position classifies "
                + "BOUNDARY_DIRECT with no recorded expectation");
        // The direct flow of the literal element into its boundary slot.
        SemanticOp arrayNew = ofKind(ops, SemanticOpKind.ARRAY_NEW).get(0);
        KindPayload.ArrayNewPayload arrayPayload =
            (KindPayload.ArrayNewPayload) arrayNew.payload();
        check(arrayPayload.values().size() == 1
                && arrayPayload.elementBoundaryOpIds().size() == 1,
            "the ARRAY_NEW carries one element value and one element boundary");
        if (arrayPayload.values().size() == 1
                && arrayPayload.elementBoundaryOpIds().size() == 1) {
            SemanticOp literalBoundary = opOf(ops, arrayPayload.elementBoundaryOpIds().get(0));
            check(literalBoundary != null
                    && literalBoundary.payload() instanceof KindPayload.BoundaryPayload
                        literalPayload
                    && literalPayload.kind() == BoundaryKind.ARRAY_LITERAL_ELEMENT
                    && literalPayload.input().equals(arrayPayload.values().get(0)),
                "the array literal element's value flows directly into its "
                    + "ARRAY_LITERAL_ELEMENT boundary slot");
        }
    }

    /**
     * An exact-signature direct store of a {@code CLOSURE_NEW} result
     * (combined with the closure child — fails if the closure module is
     * broken): zero adapters, the declaration boundary input and the
     * INIT operand are the closure's allocation identity itself, and
     * the position classifies {@code DIRECT_STORE}.
     */
    static void testClosureNewExactSignatureDirectStore() {
        System.out.println("-- CLOSURE_NEW exact-signature direct store --");

        SemanticLowerer.CreationRuleCoreResult result = loweredResult("""
            function main(): null {
              let h: () => null = function(): null {
              };
            }
            """, "the closure direct-store slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "zero FUNCTION_ADAPT ops in the unit");

        List<SemanticOp> closureNews = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closureNews.size() == 2,
            "exactly two CLOSURE_NEW ops (main + the function expression); got "
                + closureNews.size());
        if (closureNews.size() != 2) {
            return;
        }
        // The expression's result is the INIT-fed value: h's INIT
        // operand names the expression's CLOSURE_NEW result.
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (h == null) {
            return;
        }
        SemanticOp hInit = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload payload
                    && payload.binding().equals(h.binding())) {
                hInit = op;
            }
        }
        check(hInit != null, "h's BINDING_INIT exists");
        if (hInit == null) {
            return;
        }
        KindPayload.BindingInitPayload initPayload =
            (KindPayload.BindingInitPayload) hInit.payload();
        check(initPayload.value() instanceof ValueId valueId
                && ofKind(ops, SemanticOpKind.CLOSURE_NEW).stream()
                    .anyMatch(op -> op.result().equals(valueId)),
            "h's INIT operand is a CLOSURE_NEW result — the closure's allocation "
                + "identity stored directly");
        ValueId closureValue = (ValueId) initPayload.value();
        List<SemanticOp> declarations = boundariesOfKind(ops,
            BoundaryKind.VARIABLE_DECLARATION);
        check(declarations.size() == 1
                && ((KindPayload.BoundaryPayload) declarations.get(0).payload())
                    .input().equals(closureValue),
            "the declaration boundary's input is the CLOSURE_NEW result itself "
                + "(direct flow)");
        // The registry: the closure's allocation identity is a key.
        check(unit.functionBindings().containsKey(
                new FunctionAllocationIdentity(closureValue.id())),
            "the CLOSURE_NEW result identity is a functionBindings key (the registry "
                + "child's registration)");
        // The classification: DIRECT_STORE, no candidate.
        List<AdapterCreationRule.PositionClassification> classifications =
            classificationsOf(result.creationFacts(), BoundaryKind.VARIABLE_DECLARATION);
        check(classifications.size() == 1
                && classifications.get(0).disposition()
                    == AdapterCreationRule.Disposition.DIRECT_STORE
                && classifications.get(0).candidate().isEmpty(),
            "the position classifies DIRECT_STORE for the exact CLOSURE_NEW store");
    }

    /**
     * A host/external import-read source: the registry child's
     * materialization seam records the producer facts, and the
     * candidate of an assignable-but-not-exact position over that
     * source records those facts (the candidate records the producer
     * facts supplied by the T4 seam; the closed-map mode — the
     * non-identifier member-read arm → {@code REEVALUATE_THUNK} — is
     * the shape-map child's decision).
     */
    static void testHostExternalCandidateRecordsProducerFacts() {
        System.out.println("-- host/external import-read source: candidate records the "
            + "T4 producer facts --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(1001L);
        RuntimeDescriptor.Func exportDescriptor = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Int.INSTANCE);
        ModuleId hostModule = new ModuleId("host1");
        FunctionBindingRegistry.FunctionValueMaterialization materialization =
            registry.registerHostOrExternalImport(identity,
                new KindPayload.MemberReadPayload(new ValueId(9001L), "g"),
                new FunctionBindingRegistry.FunctionValueImportFacts(hostModule, null, "g",
                    exportDescriptor),
                null);
        check(materialization.source()
                == FunctionBindingRegistry.FunctionValueMaterializationSource.HOST_EXPORT,
            "the seam classifies the site as a HOST_EXPORT materialization");
        check(registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.HostFunction host
                && host.hostModuleId().equals(hostModule)
                && host.exportName().equals("g")
                && host.descriptor().equals(exportDescriptor),
            "the registry holds the HostFunction registration keyed by the produced "
                + "allocation identity");

        AdapterCreationRule.PositionClassification classification =
            AdapterCreationRule.classifyVariablePosition(BoundaryKind.VARIABLE_DECLARATION,
                SOURCE_M1, TARGET_N2, Optional.empty(),
                new AdapterCreationRule.WiringPoint(new OpId(MODULE, 7004L),
                    AdapterCreationRule.WiringTargetKind.VARIABLE_DECLARATION_BOUNDARY),
                Optional.of(materialization));
        check(classification.disposition() == AdapterCreationRule.Disposition.ADAPT
                && classification.candidate().isPresent(),
            "a host/external function-value source is an admissible adaptation "
                + "candidate per the same rule (docs/spec-v1.2.md:1078-1082)");
        if (classification.candidate().isPresent()) {
            AdapterCreationRule.AdaptationCandidate candidate =
                classification.candidate().get();
            check(candidate.producerFacts().isPresent()
                    && candidate.producerFacts().get().equals(materialization),
                "the candidate records the producer facts supplied by the registry "
                    + "child's materialization seam");
            check(candidate.proof().isEmpty(),
                "an import-read source records no proof fact (a non-identifier "
                    + "member-read source — the shape-map child's closed-map decision)");
            check(candidate.reDerivesAsAssignableButNotExact(),
                "the candidate's pair re-derives as assignable-but-not-exact");
        }
    }

    /**
     * Repeated lowering yields identical classification records and
     * byte-identical unit dumps (the classification is purely
     * observational — deterministic byte-identical lowering's
     * classification half).
     */
    static void testRepeatedLoweringYieldsIdenticalClassificationsAndUnits() {
        System.out.println("-- repeated lowering: identical classifications and "
            + "byte-identical units --");

        String source = """
            function inner(x: int): null {}
            function wide(a: int, b: int): null {}
            function main(): null {
              let h: (y: int) => null = inner;
              let arr: ((a: int, b: int) => null)[] = [wide];
              arr[0] = inner;
              let adapted: (a: int, b: int) => null = inner;
              adapted = inner;
            }
            """;
        SemanticLowerer.CreationRuleCoreResult first = loweredResult(source,
            "the determinism slice (first lowering)");
        SemanticLowerer.CreationRuleCoreResult second = loweredResult(source,
            "the determinism slice (second lowering)");
        if (first == null || second == null) {
            return;
        }
        check(first.creationFacts().classifications()
                .equals(second.creationFacts().classifications()),
            "the two runs record identical classification lists (walk order)");
        check(first.creationFacts().candidates().size() == 2,
            "the slice produces exactly two adaptation candidates (the adapted "
                + "initializer and the adapted assignment); got "
                + first.creationFacts().candidates().size());
        check(ofKind(first.lowering().unit().ops(), SemanticOpKind.FUNCTION_ADAPT).isEmpty()
                && ofKind(second.lowering().unit().ops(), SemanticOpKind.FUNCTION_ADAPT)
                    .isEmpty(),
            "zero FUNCTION_ADAPT ops in either run's unit");
        byte[] firstDump = SemanticIrDumper.dumpModule(first.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.lowering().unit());
        check(Arrays.equals(firstDump, secondDump),
            "two runs produce byte-identical unit dumps");

        // Cross-child byte identity: the classification is purely
        // observational — the proof child's walk and this child's walk
        // emit byte-identical units for the same checked module.
        CheckedSlice slice = checkSlice(source);
        if (slice != null) {
            SemanticLowerer.ImmutabilityCoreResult proofRun =
                SemanticLowerer.lowerModuleImmutabilityCore(moduleOf(slice),
                    SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
                    SemanticIdAllocator.over(List.of(MODULE)));
            check(proofRun != null && !proofRun.lowering().hasErrors()
                    && proofRun.lowering().unit() != null,
                "the proof child lowers the same module to a validated unit");
            if (proofRun != null && !proofRun.lowering().hasErrors()
                    && proofRun.lowering().unit() != null) {
                byte[] proofDump = SemanticIrDumper.dumpModule(proofRun.lowering().unit());
                check(Arrays.equals(firstDump, proofDump),
                    "the creation-rule walk and the proof walk emit byte-identical units "
                        + "(the classification changes no emitted op)");
                check(ofKind(proofRun.lowering().unit().ops(),
                        SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
                    "the proof child's unit also contains zero FUNCTION_ADAPT ops");
            }
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Adapter Creation Rule Test (ISSUE-0449 creation-rule "
            + "child) ===\n");

        testExactSignatureInitializerStoresDirectly();
        testExactSignatureAssignmentStoresDirectly();
        testAssignableButNotExactInitializerClassifiesOneCandidate();
        testAssignableButNotExactAssignmentClassifiesOneCandidate();
        testAssignedBindingSourceCandidateCarriesNoProofFact();
        testNonAssignablePairsAreFrontendRejectedAndExpectationRecorded();
        testClassifierClosedPositionSetNeverAdaptsOutsideVariablePositions();
        testPinnedReturnBoundaryShapeStructuralFacts();
        testArrayElementPositionsFlowDirectlyWithZeroAdapters();
        testClosureNewExactSignatureDirectStore();
        testHostExternalCandidateRecordsProducerFacts();
        testRepeatedLoweringYieldsIdenticalClassificationsAndUnits();

        System.out.println("\nAdapter creation rule: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
