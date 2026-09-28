package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.AdapterCreationRule;
import deal.semantic.AdapterShapeMap;
import deal.semantic.AdapterThunkConstruction;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.DescriptorService;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.ModuleRoute;
import deal.semantic.ModuleRoutePlan;
import deal.semantic.SemanticLowerer;
import deal.semantic.Target;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The epic's integration verification task (ISSUE-0452, sequencing item
 * 9 — the decomposition tail): a fixed corpus of function-typed
 * initializer/assignment positions lowered end to end through the
 * shared lowering pipeline the earlier children built (checked source →
 * {@link SemanticLowerer#lowerModuleValidationCore} → the closed
 * 14-condition schema validator → the address-chain protocol → the
 * control-flow validator → the B9 production-time rule set), asserted
 * against every integration criterion — and the executed
 * boundary-position E8010 drive through E4's boundary machinery
 * (declared in-branch prerequisite), without invoking any adapter.
 *
 * <p><b>The fixed corpus.</b> One checked implementation module whose
 * function-typed positions cover the creation rule and the closed
 * shape map end to end:</p>
 * <ul>
 *   <li>exact-signature initializer and assignment positions
 *       ({@code exactA} — direct store, zero adapters);</li>
 *   <li>assignable-but-not-exact initializer and assignment positions
 *       over a plain reassignable binding ({@code sc1}, {@code sc2 =}
 *       — {@code SHARED_CELL} with {@code SharedCell {BindingId,
 *       generation}}, zero creation evaluation);</li>
 *   <li>a non-identifier composite source position ({@code thunkSrc}
 *       — {@code REEVALUATE_THUNK} with a detached thunk block), plus
 *       the non-identifier call-result source through the shape-map
 *       child's IR-level seam (a {@code CALL} op returning a function —
 *       the pinned {@code jvm-fv-return-function-value} shape — wrapped
 *       by {@link AdapterThunkConstruction});</li>
 *   <li>host and external import member-read sources
 *       ({@code REEVALUATE_THUNK} — the non-identifier arm, no VALUE
 *       carve-out) exercised through the registry child's IR-level
 *       materialization seam over the pinned
 *       {@code deal.semantic-ir/1} schema records, registering the
 *       {@code HostFunction}/{@code ExternalFunction} bindings;</li>
 *   <li>a function-expression source ({@code ve} — {@code VALUE} over
 *       the {@code CLOSURE_NEW} result);</li>
 *   <li>a proved binding source ({@code vp} — {@code VALUE} over the
 *       single proved load with the recorded proof naming that
 *       binding/generation);</li>
 *   <li>typed boundary positions — an exact-signature array literal
 *       element and an {@code M < N} array element assignment (direct
 *       flow into the position's boundary slot, zero adapters) plus
 *       the pinned return shape of {@code jvm-fv-sig-check-return-error}
 *       (a {@code (int)=>int} closure returned across a declared
 *       {@code (a:int,b:int)=>int} return) whose no-adapt facts the
 *       classifier records and whose executed rejection runs through
 *       E4's {@link BoundaryExecutor}.</li>
 * </ul>
 *
 * <p><b>In-epic assertions (self-contained over T1-T8).</b> Mode
 * selection matches the closed shape map at every corpus position
 * (exactly one mode per adapted position, the correct arm each);
 * payload construction matches B8 for every mode; exact-signature
 * positions store directly (the unit's {@code FUNCTION_ADAPT} count
 * equals the adapted-position count); boundary positions never adapt
 * (direct flow into the position's boundary slot, zero adapters);
 * creation-wiring (every adapter result is the direct input of exactly
 * its own position's {@code VARIABLE_DECLARATION}/
 * {@code VARIABLE_ASSIGNMENT} boundary chain and of no other
 * {@code BOUNDARY} op); registry uniqueness (exactly one
 * {@code FunctionExecutionBinding} per producing allocation, the
 * {@code HostFunction}/{@code ExternalFunction} seam registrations
 * included; R-FUNCTION-BINDING stays green); the B9 rule set passes;
 * repeated lowering is byte-identical; and the cell-kind iff holds —
 * every incarnation's cell kind equals the closed derivation over the
 * three capture reference sets plus the pinned special cases.</p>
 *
 * <p><b>Executed boundary-position E8010 drive (E4's machinery, the
 * declared in-branch prerequisite).</b> The drive targets the pinned
 * cell — kind {@code FUNCTION_RETURN}, function descriptor, policy
 * {@code FUNCTION_SIGNATURE} per the closed boundary-assignment table
 * (descriptor-kind rule), realized as
 * {@link BoundaryRealization.RuntimeValidation} executing the closed
 * exact-signature check over {@link RuntimeDescriptor.Func} through
 * {@link BoundaryExecutor#execute}. The drive unit carries the pinned
 * return shape over the pinned schema records — a {@code CLOSURE_NEW}
 * producing the returned {@code (int)->int} function identity with its
 * registered {@code LoweredBody}, the {@code RETURN} op naming the
 * boundary, and the {@code FUNCTION_RETURN} boundary whose direct
 * input is that identity — and zero {@code FUNCTION_ADAPT} ops. The
 * executed check asserts the exact E8010 record (code E8010, the
 * registry template instantiated with expected {@code (int,int)->int}
 * and actual {@code (int)->int}), the failure origin (the return
 * boundary op named by the {@code RETURN} payload), and the
 * pre-invocation ordering evidence (the returned function identity is
 * never invoked — zero invocation ops consume it — so the rejection
 * precedes any invocation of the returned value); the negative control
 * executes the same cell with an exact-signature
 * {@code (int,int)->int} value and passes. The executed check is the
     * executor's comparator, never a static
     * {@link FailureContractRegistry} lookup; the drive fails (never skips)
     * when the realization component is absent or misbehaves.</p>
 *
 * <p><b>No adapter invocation.</b> The corpus and the drive invoke no
 * adapter: no {@code CALL}/{@code CALLBACK_INVOKE}/{@code ASYNC_START}
 * op resolves an {@code AdapterBinding}, and the test asserts the
 * absence of any adapter-invocation execution evidence.
 * Invocation-observable adapter behavior ({@code SHARED_CELL}
 * retargeting, thunk per-invoke re-evaluation, the N-argument
 * projection with trailing drop, invocation-time E8010) remains E7's
 * verification and is not exercised here.</p>
 *
 * <p><b>Fail-if-broken.</b> A broken binding core fails the
 * incarnations/generations assertions, a broken closure module fails
 * the {@code CLOSURE_NEW}/captures assertions, a broken registry or
 * seam fails uniqueness, a broken proof analysis fails the
 * proved-binding fixture, a broken creation rule fails the exact-store
 * or boundary assertions, a broken shape map fails the per-position
 * mode assertions, a broken validation module fails the B9 pass, and a
 * broken boundary comparator fails the executed E8010 drive or its
 * negative control.</p>
 */
public class BindingsIntegrationVerificationTest {

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
                List.of(), List.of(), List.of(),
                InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    /** The corpus source signature {@code (int)->null} ({@code inner}, {@code retarget}, ...). */
    private static final RuntimeDescriptor.Func INNER_SIG = (RuntimeDescriptor.Func)
        DescriptorService.describe(
            new Type.Func(List.of(Type.Int.INSTANCE), Type.Null.INSTANCE));
    /** The corpus two-argument signature {@code (int,int)->null} ({@code wide}). */
    private static final RuntimeDescriptor.Func WIDE_SIG = (RuntimeDescriptor.Func)
        DescriptorService.describe(
            new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                Type.Null.INSTANCE));
    /** The pinned return shape's returned signature {@code (int)->int}. */
    private static final RuntimeDescriptor.Func RETURNED_SIG = (RuntimeDescriptor.Func)
        DescriptorService.describe(
            new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE));
    /** The pinned return shape's declared signature {@code (int,int)->int}. */
    private static final RuntimeDescriptor.Func DECLARED_SIG = (RuntimeDescriptor.Func)
        DescriptorService.describe(
            new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                Type.Int.INSTANCE));
    /** The declared function's own signature {@code ()->(int,int)->int}. */
    private static final RuntimeDescriptor.Func DECLARED_FN_SIG =
        new RuntimeDescriptor.Func(List.of(), DECLARED_SIG);

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Source-level driver (the validation entry point: checked → lower → validate)
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the corpus parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the corpus resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(),
            "the corpus checks cleanly: " + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    private static SemanticLowerer.ValidationCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleValidationCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /** A lowered, schema/chain/control-flow/B9-validated unit for the named slice. */
    private static SemanticLowerer.ValidationCoreResult validatedResult(String source,
                                                                        String what) {
        SemanticLowerer.ValidationCoreResult result = lowerSlice(source);
        if (result == null) {
            return null;
        }
        check(result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers through the complete pipeline to a validated unit: "
                + (result.lowering() == null ? "null" : result.lowering().diagnostics()));
        if (result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    // =========================================================================
    // Unit helpers
    // =========================================================================

    /** The produced ops of exactly the named kind, in unit order. */
    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** The produced FUNCTION_ADAPT ops in unit order. */
    private static List<SemanticOp> adaptersOf(List<SemanticOp> ops) {
        return ofKind(ops, SemanticOpKind.FUNCTION_ADAPT);
    }

    /** The produced BOUNDARY ops of exactly the named boundary kind. */
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

    /** The unit op with the given op id, or null when absent. */
    private static SemanticOp opOf(List<SemanticOp> ops, OpId opId) {
        for (SemanticOp op : ops) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        fail("op " + opId + " not found in the produced op list");
        return null;
    }

    /** The BINDING_ALLOC op of exactly the given {binding, generation}. */
    private static SemanticOp allocOf(List<SemanticOp> ops, BindingId binding,
                                      long generation) {
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_ALLOC
                    && op.payload() instanceof KindPayload.BindingAllocPayload payload
                    && payload.binding().equals(binding)
                    && payload.generation() == generation) {
                return op;
            }
        }
        return null;
    }

    /** Every BINDING_LOAD op naming exactly the given {binding, generation}. */
    private static List<SemanticOp> loadsOf(List<SemanticOp> ops, BindingId binding,
                                            long generation) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_LOAD
                    && op.payload() instanceof KindPayload.BindingLoadPayload payload
                    && payload.binding().equals(binding)
                    && payload.generation() == generation) {
                matches.add(op);
            }
        }
        return matches;
    }

    /** The first op index in the unit op list (identity by op id). */
    private static int indexOf(List<SemanticOp> ops, OpId opId) {
        for (int i = 0; i < ops.size(); i++) {
            if (ops.get(i).opId().equals(opId)) {
                return i;
            }
        }
        return -1;
    }

    /** The single FUNCTION_ADAPT payload of the op. */
    private static KindPayload.FunctionAdaptPayload adaptPayload(SemanticOp op) {
        if (op == null || !(op.payload() instanceof KindPayload.FunctionAdaptPayload payload)) {
            fail("expected a FUNCTION_ADAPT op carrying its FunctionAdaptPayload");
            return null;
        }
        return payload;
    }

    /** The number of unit BOUNDARY ops whose input equals the value. */
    private static int boundaryConsumers(List<SemanticOp> ops, ValueId value) {
        int consumers = 0;
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && op.payload() instanceof KindPayload.BoundaryPayload payload
                    && value.equals(payload.input())) {
                consumers++;
            }
        }
        return consumers;
    }

    /** The number of unit ops whose operands contain the value. */
    private static int operandConsumers(List<SemanticOp> ops, ValueId value) {
        int consumers = 0;
        for (SemanticOp op : ops) {
            if (op.operands().contains(value)) {
                consumers++;
            }
        }
        return consumers;
    }

    /** The number of unit ops parented to the given op. */
    private static int childrenOf(List<SemanticOp> ops, OpId parent) {
        int children = 0;
        for (SemanticOp op : ops) {
            if (op.origin().parentOpId() != null
                    && op.origin().parentOpId().equals(parent)) {
                children++;
            }
        }
        return children;
    }

    /** The unit's invocation ops ({@code CALL}/{@code CALLBACK_INVOKE}/{@code ASYNC_START}). */
    private static List<SemanticOp> invocationOps(List<SemanticOp> ops) {
        List<SemanticOp> invocations = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.CALL
                    || op.kind() == SemanticOpKind.CALLBACK_INVOKE
                    || op.kind() == SemanticOpKind.ASYNC_START) {
                invocations.add(op);
            }
        }
        return invocations;
    }

    /** The recorded wiring target of the adapter with the given identity. */
    private static OpId emissionWiringTargetOf(SemanticLowerer.ValidationCoreResult result,
                                               ValueId adapterIdentity) {
        for (SemanticLowerer.AdapterEmission emission : result.shapeMapFacts().emissions()) {
            if (emission.adapterIdentity().equals(adapterIdentity)) {
                return emission.wiringTargetOpId();
            }
        }
        fail("no emission fact records the adapter identity " + adapterIdentity);
        return null;
    }

    /** The ordered op members of the named block from the body table. */
    private static List<SemanticOp> blockOpsOf(SemanticLowerer.ValidationCoreResult result,
                                               BlockId block, List<SemanticOp> ops) {
        if (result.lowering().table() == null) {
            fail("the produced body table is present");
            return List.of();
        }
        List<OpId> ids = result.lowering().table().blockOps().get(block);
        if (ids == null) {
            fail("the produced table records the block " + block);
            return List.of();
        }
        List<SemanticOp> members = new ArrayList<>();
        for (OpId id : ids) {
            SemanticOp op = opOf(ops, id);
            if (op != null) {
                members.add(op);
            }
        }
        return members;
    }

    // =========================================================================
    // The fixed corpus
    // =========================================================================

    /**
     * The fixed corpus: the exact-signature pair ({@code exactA}),
     * the reassignable-binding SHARED_CELL pair ({@code sc1},
     * {@code sc2 = retarget}), the non-identifier composite
     * REEVALUATE_THUNK position ({@code thunkSrc}), the
     * function-expression VALUE position ({@code ve}), the
     * proved-binding VALUE position ({@code vp}), the direct stores
     * ({@code retarget}, {@code sc2}, {@code proved} declarations and
     * the exact assignments), and the typed boundary positions (the
     * exact array literal element {@code [wide]} and the {@code M < N}
     * array element assignment {@code arr[0] = inner}).
     */
    private static String corpusSource() {
        return """
            function inner(x: int): null {}

            function wide(a: int, b: int): null {}

            function main(): null {
              let exactA: (x: int) => null = inner;
              exactA = inner;

              let retarget: (x: int) => null = inner;
              retarget = inner;
              let sc1: (a: int, b: int) => null = retarget;
              let sc2: (a: int, b: int) => null = wide;
              sc2 = retarget;

              let thunkSrc: (a: int, b: int) => null = (retarget = inner);

              let ve: (a: int, b: int) => null = function(x: int): null {};

              let proved: (x: int) => null = inner;
              let vp: (a: int, b: int) => null = proved;

              let arr: ((a: int, b: int) => null)[] = [wide];
              arr[0] = inner;
            }
            """;
    }

    // =========================================================================
    // 1. The end-to-end pipeline and byte-identical repetition
    // =========================================================================

    static void testCorpusLowersThroughTheCompletePipeline() {
        System.out.println("-- the corpus lowers through the complete pipeline and "
            + "repeats byte-identically --");

        SemanticLowerer.ValidationCoreResult first = validatedResult(corpusSource(),
            "the integration corpus (first lowering)");
        SemanticLowerer.ValidationCoreResult second = validatedResult(corpusSource(),
            "the integration corpus (second lowering)");
        if (first == null || second == null) {
            return;
        }
        LoweredModuleUnit unit = first.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).size() == 5,
            "the corpus emits exactly five FUNCTION_ADAPT ops (sc1, sc2's assignment, "
                + "thunkSrc, ve, vp); got " + ofKind(ops, SemanticOpKind.FUNCTION_ADAPT).size());
        check(first.creationFacts().candidates().size() == 5,
            "the creation-rule facts record exactly five adaptation candidates (one "
                + "per emitted adapter)");
        check(first.creationFacts().ofDisposition(
                AdapterCreationRule.Disposition.DIRECT_STORE).size() == 7,
            "the creation-rule facts record seven DIRECT_STORE classifications (exactA "
                + "declaration, exactA assignment, retarget declaration, retarget "
                + "assignment, the thunk-source inner assignment, sc2 declaration, "
                + "proved declaration)");
        check(first.creationFacts().ofDisposition(
                AdapterCreationRule.Disposition.BOUNDARY_DIRECT).size() == 2,
            "the creation-rule facts record two BOUNDARY_DIRECT classifications (the "
                + "array literal element and the array element assignment)");
        check(first.shapeMapFacts().emissions().size() == 5,
            "the emission fact surface carries one record per emitted adapter");

        // Byte-identical repeated lowering (dump text and fact surfaces).
        byte[] firstDump = SemanticIrDumper.dumpModule(first.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.lowering().unit());
        check(Arrays.equals(firstDump, secondDump),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dump text");
        check(first.creationFacts().equals(second.creationFacts()),
            "repeated lowering records identical classification facts");
        check(first.shapeMapFacts().equals(second.shapeMapFacts()),
            "repeated lowering records identical emission facts");
        check(first.bindingFacts().equals(second.bindingFacts()),
            "repeated lowering records identical binding facts");
        String dumpText = new String(firstDump, StandardCharsets.UTF_8);
        check(dumpText.contains("\"formatVersion\":\"deal.semantic-ir/1\""),
            "the dump carries the pinned deal.semantic-ir/1 format version");
    }

    // =========================================================================
    // 2. Exact-signature positions: direct store, zero adapters
    // =========================================================================

    static void testExactSignaturePositionsStoreDirectly() {
        System.out.println("-- exact-signature initializer/assignment positions store "
            + "directly (zero FUNCTION_ADAPT) --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding exactA = fact(result.bindingFacts(), "exactA");
        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding wide = fact(result.bindingFacts(), "wide");
        SemanticLowerer.BindingCoreBinding sc2 = fact(result.bindingFacts(), "sc2");
        if (exactA == null || inner == null || wide == null || sc2 == null) {
            return;
        }

        // exactA's declaration: ALLOC → [load of inner] → boundary → INIT;
        // the boundary input and the INIT operand are the source identity
        // itself (no adapter).
        SemanticOp exactAAlloc = allocOf(ops, exactA.binding(), 0);
        check(exactAAlloc != null, "exactA's BINDING_ALLOC exists");
        SemanticOp exactAInit = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload payload
                    && payload.binding().equals(exactA.binding())) {
                exactAInit = op;
            }
        }
        check(exactAInit != null, "exactA's BINDING_INIT exists");
        if (exactAInit == null) {
            return;
        }
        KindPayload.BindingInitPayload initPayload =
            (KindPayload.BindingInitPayload) exactAInit.payload();
        List<SemanticOp> exactABoundaries = new ArrayList<>();
        for (SemanticOp op : boundariesOfKind(ops, BoundaryKind.VARIABLE_DECLARATION)) {
            if (op.payload() instanceof KindPayload.BoundaryPayload payload
                    && initPayload.value().equals(payload.input())) {
                exactABoundaries.add(op);
            }
        }
        check(exactABoundaries.size() == 3,
            "three VARIABLE_DECLARATION boundaries consume the shared inner identity "
                + "(exactA's, retarget's, and proved's declarations — loads publish "
                + "the function identity, so the direct store feeds the same identity "
                + "to every exact position); got " + exactABoundaries.size());
        check(initPayload.value() instanceof ValueId value
                && value.equals(innerIdentityOf(ops, inner)),
            "exactA's INIT commits the source function identity itself (the load of "
                + "inner), never an adapter identity");
        check(adaptersOf(ops).stream().noneMatch(adapter -> adapter.result()
                instanceof ValueId identity && identity.equals(initPayload.value())),
            "no adapter identity equals exactA's stored value (zero adapters at the "
                + "exact position)");
        for (SemanticOp boundary : exactABoundaries) {
            check(boundary.payload() instanceof KindPayload.BoundaryPayload payload
                    && payload.descriptor() instanceof RuntimeDescriptor.Func declared
                    && declared.equals(INNER_SIG),
                "the declaration boundary consuming the direct-store value checks the "
                    + "exact declared signature " + INNER_SIG.canonicalSpecText());
        }

        // exactA = inner: the variable ASSIGN chain [load, boundary, store];
        // the boundary input is the source identity, the store commits it.
        SemanticOp exactAAssign = variableAssignOf(ops, exactA.binding());
        check(exactAAssign != null, "exactA's variable ASSIGN chain exists");
        if (exactAAssign != null) {
            KindPayload.AssignPayload chain = (KindPayload.AssignPayload) exactAAssign.payload();
            check(chain.childOps().size() == 3,
                "the exact assignment chain carries its 3 children [value, boundary, "
                    + "commit]");
            if (chain.childOps().size() == 3) {
                SemanticOp valueOp = opOf(ops, chain.childOps().get(0));
                SemanticOp boundaryOp = opOf(ops, chain.childOps().get(1));
                SemanticOp commitOp = opOf(ops, chain.childOps().get(2));
                check(valueOp != null && valueOp.kind() == SemanticOpKind.BINDING_LOAD,
                    "the exact assignment's value child is the source BINDING_LOAD "
                        + "(never an adapter)");
                check(boundaryOp != null && boundaryOp.payload()
                        instanceof KindPayload.BoundaryPayload boundary
                        && boundary.kind() == BoundaryKind.VARIABLE_ASSIGNMENT
                        && valueOp != null && boundary.input().equals(valueOp.result()),
                    "the VARIABLE_ASSIGNMENT boundary's input is the source identity "
                        + "itself — direct store, zero adapters");
                check(commitOp != null && commitOp.payload()
                        instanceof KindPayload.BindingStorePayload store
                        && store.binding().equals(exactA.binding())
                        && valueOp != null && store.value().equals(valueOp.result()),
                    "the BINDING_STORE commit writes the source identity");
            }
        }

        // sc2's declaration is exact over wide (both (int,int)->null):
        // the boundary input is wide's identity, never an adapter result.
        SemanticOp sc2Init = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload payload
                    && payload.binding().equals(sc2.binding())) {
                sc2Init = op;
            }
        }
        check(sc2Init != null, "sc2's BINDING_INIT exists");
        if (sc2Init != null) {
            KindPayload.BindingInitPayload sc2InitPayload =
                (KindPayload.BindingInitPayload) sc2Init.payload();
            check(sc2InitPayload.value() instanceof ValueId value
                    && value.equals(innerIdentityOf(ops, wide)),
                "sc2's exact initializer commits wide's identity directly (zero "
                    + "adapters at the exact position)");
        }

        // The total adapter count equals the adapted-position count —
        // the exact positions contribute zero adapters.
        check(adaptersOf(ops).size() == 5,
            "the total FUNCTION_ADAPT count (5) equals the number of adapted corpus "
                + "positions (sc1, sc2's assignment, thunkSrc, ve, vp)");
    }

    /** The function identity the loads of the named binding publish (one load). */
    private static ValueId innerIdentityOf(List<SemanticOp> ops,
                                           SemanticLowerer.BindingCoreBinding binding) {
        List<SemanticOp> loads = loadsOf(ops, binding.binding(), 0);
        // Module functions are referenced through loads; the first load's
        // result is the identity every consumer shares.
        return loads.isEmpty() ? null : (ValueId) loads.get(0).result();
    }

    /** The VARIABLE-target ASSIGN chain committing to the given binding. */
    private static SemanticOp variableAssignOf(List<SemanticOp> ops, BindingId binding) {
        for (SemanticOp op : ops) {
            if (op.kind() != SemanticOpKind.ASSIGN) {
                continue;
            }
            KindPayload.AssignPayload chain = (KindPayload.AssignPayload) op.payload();
            if (chain.targetKind() != deal.semantic.ir.AssignTargetKind.VARIABLE
                    || chain.childOps().isEmpty()) {
                continue;
            }
            SemanticOp commit = opOf(ops, chain.childOps().get(chain.childOps().size() - 1));
            if (commit != null && commit.payload() instanceof KindPayload.BindingStorePayload
                    store && store.binding().equals(binding)) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // 3. SHARED_CELL: reassignable binding sources at initializer and assignment
    // =========================================================================

    static void testSharedCellInitializerAndAssignmentPositions() {
        System.out.println("-- SHARED_CELL: reassignable binding source at initializer "
            + "and assignment positions, zero creation evaluation --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding retarget = fact(result.bindingFacts(), "retarget");
        SemanticLowerer.BindingCoreBinding sc1 = fact(result.bindingFacts(), "sc1");
        SemanticLowerer.BindingCoreBinding sc2 = fact(result.bindingFacts(), "sc2");
        if (retarget == null || sc1 == null || sc2 == null) {
            return;
        }

        Map<CaptureMode, Integer> modeCounts = new EnumMap<>(CaptureMode.class);
        for (SemanticOp adapter : adaptersOf(ops)) {
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null) {
                continue;
            }
            modeCounts.merge(payload.mode(), 1, Integer::sum);
        }
        check(modeCounts.getOrDefault(CaptureMode.SHARED_CELL, 0) == 2,
            "two SHARED_CELL adapters (sc1's initializer and sc2's assignment); got "
                + modeCounts.get(CaptureMode.SHARED_CELL));

        // sc1: the adapter directly follows sc1's ALLOC (zero evaluation
        // between them), SharedCell names {retarget, 0}, zero operands,
        // no proof, and the boundary observes the adapter identity.
        SemanticOp sc1Alloc = allocOf(ops, sc1.binding(), 0);
        SemanticOp sc1Adapter = null;
        for (SemanticOp adapter : adaptersOf(ops)) {
            if (adapter.result() instanceof ValueId identity
                    && boundaryConsumers(ops, identity) == 1
                    && boundaryOpFor(ops, identity) != null
                    && boundaryOpFor(ops, identity).payload()
                        instanceof KindPayload.BoundaryPayload payload
                    && payload.kind() == BoundaryKind.VARIABLE_DECLARATION
                    && payload.input().equals(identity)) {
                for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
                    if (op.payload() instanceof KindPayload.BindingInitPayload initPayload
                            && initPayload.binding().equals(sc1.binding())
                            && initPayload.value().equals(identity)) {
                        sc1Adapter = adapter;
                    }
                }
            }
        }
        check(sc1Adapter != null, "sc1's initializer adapter exists (wired into sc1's "
            + "declaration boundary and INIT)");
        if (sc1Adapter == null) {
            return;
        }
        check(sc1Alloc != null && indexOf(ops, sc1Adapter.opId()) == indexOf(ops,
                sc1Alloc.opId()) + 1,
            "the adapter directly follows sc1's ALLOC — zero evaluation at creation");
        KindPayload.FunctionAdaptPayload sc1Payload = adaptPayload(sc1Adapter);
        if (sc1Payload != null) {
            check(sc1Payload.mode() == CaptureMode.SHARED_CELL,
                "sc1's adapter mode is SHARED_CELL (an unproven reassignable binding "
                    + "source — the map's fallback arm)");
            check(sc1Payload.source() instanceof AdaptSourceRef.SharedCell shared
                    && shared.binding().equals(retarget.binding())
                    && shared.generation() == 0,
                "sc1's source is SharedCell naming the dominant {binding, generation} "
                    + "= {retarget, 0}");
            check(sc1Adapter.operands().isEmpty() && sc1Payload.proof() == null,
                "sc1's creation performs zero evaluation: zero operands, zero loads, "
                    + "no proof");
            check(sc1Payload.sourceSignature().equals(INNER_SIG)
                    && sc1Payload.targetSignature().equals(WIDE_SIG),
                "sc1's pair is {source (int)->null, target (int,int)->null} — the "
                    + "assignable-but-not-exact pair");
        }
        SemanticOp sc1Boundary = boundaryOpFor(ops, (ValueId) sc1Adapter.result());
        check(sc1Boundary != null
                && ((KindPayload.BoundaryPayload) sc1Boundary.payload()).descriptor()
                    .equals(sc1Payload != null ? sc1Payload.targetSignature() : null),
            "sc1's declaration boundary checks the target signature (exact-signature "
                + "pass-through of the adapter value)");
        FunctionExecutionBinding sc1Binding =
            unit.functionBindings().get(new FunctionAllocationIdentity(
                ((ValueId) sc1Adapter.result()).id()));
        check(sc1Binding instanceof FunctionExecutionBinding.AdapterBinding adapterBinding
                && adapterBinding.adaptOpId().equals(sc1Adapter.opId())
                && adapterBinding.captureMode() == CaptureMode.SHARED_CELL,
            "the registry holds sc1's AdapterBinding {adaptOpId, SHARED_CELL, ...}");

        // sc2 = retarget: the ASSIGN chain's value child is the adapter
        // itself; the boundary observes the adapter identity; the store
        // commits it. SharedCell names {retarget, 0}; zero evaluation.
        SemanticOp sc2Assign = variableAssignOf(ops, sc2.binding());
        check(sc2Assign != null, "sc2's variable ASSIGN chain exists");
        if (sc2Assign == null) {
            return;
        }
        KindPayload.AssignPayload chain = (KindPayload.AssignPayload) sc2Assign.payload();
        check(chain.childOps().size() == 3,
            "the adapted assignment chain carries its 3 children [adapter, boundary, "
                + "commit]");
        if (chain.childOps().size() != 3) {
            return;
        }
        SemanticOp valueOp = opOf(ops, chain.childOps().get(0));
        SemanticOp boundaryOp = opOf(ops, chain.childOps().get(1));
        SemanticOp commitOp = opOf(ops, chain.childOps().get(2));
        check(valueOp != null && valueOp.kind() == SemanticOpKind.FUNCTION_ADAPT,
            "the adapted assignment's value child is the FUNCTION_ADAPT op itself");
        check(valueOp != null && valueOp.result() instanceof ValueId adapterIdentity
                && boundaryOp != null && boundaryOp.payload()
                    instanceof KindPayload.BoundaryPayload boundary
                && boundary.kind() == BoundaryKind.VARIABLE_ASSIGNMENT
                && boundary.input().equals(adapterIdentity),
            "the VARIABLE_ASSIGNMENT boundary's input is the adapter identity — the "
                + "adapter result is the direct input of exactly its own assignment "
                + "boundary chain");
        check(valueOp != null && valueOp.result() instanceof ValueId adapterIdentity
                && commitOp != null && commitOp.payload()
                    instanceof KindPayload.BindingStorePayload store
                && store.binding().equals(sc2.binding()) && store.value()
                    .equals(adapterIdentity),
            "the BINDING_STORE commit writes the adapter identity (the commit of the "
                + "adapted assignment)");
        KindPayload.FunctionAdaptPayload sc2Payload = adaptPayload(valueOp);
        if (sc2Payload != null) {
            check(sc2Payload.mode() == CaptureMode.SHARED_CELL
                    && sc2Payload.source() instanceof AdaptSourceRef.SharedCell shared
                    && shared.binding().equals(retarget.binding())
                    && shared.generation() == 0,
                "sc2's assignment adapter is SHARED_CELL over SharedCell {retarget, 0}");
            check(valueOp.operands().isEmpty() && sc2Payload.proof() == null,
                "sc2's assignment creation performs zero evaluation: zero operands, "
                    + "zero loads, no proof");
        }

        // Zero creation evaluation across the whole unit: no BINDING_LOAD
        // of retarget exists anywhere (the SHARED_CELL arm performs no
        // creation load; its invocation load is E7's).
        check(loadsOf(ops, retarget.binding(), 0).isEmpty(),
            "zero BINDING_LOAD ops of retarget exist — SHARED_CELL creation "
                + "evaluates nothing (the generation-checked load is the invoking "
                + "op's, E7)");
    }

    /** The BOUNDARY op whose input equals the value, or null. */
    private static SemanticOp boundaryOpFor(List<SemanticOp> ops, ValueId value) {
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && op.payload() instanceof KindPayload.BoundaryPayload payload
                    && value.equals(payload.input())) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // 4. REEVALUATE_THUNK: composite source + IR-level call-result seam
    // =========================================================================

    static void testReevaluateThunkCompositeAndCallResultSources() {
        System.out.println("-- REEVALUATE_THUNK: composite source (thunk block, "
            + "generation-pinned captures) + the IR-level call-result seam --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding retarget = fact(result.bindingFacts(), "retarget");
        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding thunkSrc = fact(result.bindingFacts(), "thunkSrc");
        if (retarget == null || inner == null || thunkSrc == null) {
            return;
        }

        Map<CaptureMode, Integer> modeCounts = new EnumMap<>(CaptureMode.class);
        for (SemanticOp adapter : adaptersOf(ops)) {
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null) {
                continue;
            }
            modeCounts.merge(payload.mode(), 1, Integer::sum);
        }
        check(modeCounts.getOrDefault(CaptureMode.REEVALUATE_THUNK, 0) == 1,
            "one REEVALUATE_THUNK adapter (thunkSrc's composite source); got "
                + modeCounts.get(CaptureMode.REEVALUATE_THUNK));

        SemanticOp thunkAdapter = null;
        for (SemanticOp adapter : adaptersOf(ops)) {
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload != null && payload.mode() == CaptureMode.REEVALUATE_THUNK) {
                thunkAdapter = adapter;
            }
        }
        check(thunkAdapter != null, "thunkSrc's REEVALUATE_THUNK adapter exists");
        if (thunkAdapter == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(thunkAdapter);
        if (payload == null) {
            return;
        }
        check(payload.source() instanceof AdaptSourceRef.Thunk thunk,
            "the source is a Thunk {BlockId, capturedBindings} record");
        if (!(payload.source() instanceof AdaptSourceRef.Thunk thunk)) {
            return;
        }
        check(thunk.capturedBindings().equals(List.of(
                new BindingGeneration(retarget.binding(), 0),
                new BindingGeneration(inner.binding(), 0))),
            "the capturedBindings pin [retarget, inner] — the thunk's free bindings, "
                + "generation-pinned, first-reference order (the assignment target "
                + "first, then the RHS reference)");
        check(thunkAdapter.operands().isEmpty() && payload.proof() == null,
            "thunk creation performs zero evaluation: zero operands, zero loads, no "
                + "proof");

        // Zero evaluation at creation: the adapter directly follows
        // thunkSrc's ALLOC; the source ops live only inside the thunk block.
        SemanticOp thunkSrcAlloc = allocOf(ops, thunkSrc.binding(), 0);
        check(thunkSrcAlloc != null
                && indexOf(ops, thunkAdapter.opId()) == indexOf(ops, thunkSrcAlloc.opId()) + 1,
            "the adapter directly follows thunkSrc's ALLOC — zero evaluation between "
                + "them");
        List<SemanticOp> thunkOps = blockOpsOf(result, thunk.blockId(), ops);
        check(thunkOps.size() == 4,
            "the thunk block wraps the four ordered source ops [RHS load, "
                + "VARIABLE_ASSIGNMENT boundary, BINDING_STORE commit, ASSIGN]; got "
                + thunkOps.size());
        if (thunkOps.size() == 4) {
            check(thunkOps.get(0).kind() == SemanticOpKind.BINDING_LOAD
                    && thunkOps.get(0).payload() instanceof KindPayload.BindingLoadPayload
                        loadPayload
                    && loadPayload.binding().equals(inner.binding())
                    && loadPayload.generation() == 0,
                "the thunk's first op is the RHS BINDING_LOAD of {inner, 0}");
            check(thunkOps.get(1).kind() == SemanticOpKind.BOUNDARY
                    && thunkOps.get(1).payload() instanceof KindPayload.BoundaryPayload
                        boundary
                    && boundary.kind() == BoundaryKind.VARIABLE_ASSIGNMENT,
                "the thunk's second op is the inner assignment's VARIABLE_ASSIGNMENT "
                    + "boundary");
            check(thunkOps.get(2).kind() == SemanticOpKind.BINDING_STORE
                    && thunkOps.get(2).payload() instanceof KindPayload.BindingStorePayload
                        store
                    && store.binding().equals(retarget.binding()) && store.generation() == 0,
                "the thunk's third op is the BINDING_STORE commit of {retarget, 0}");
            check(thunkOps.get(3).kind() == SemanticOpKind.ASSIGN
                    && thunkOps.get(3).payload() instanceof KindPayload.AssignPayload
                        chain
                    && chain.targetKind() == deal.semantic.ir.AssignTargetKind.VARIABLE,
                "the thunk's fourth op is the inner ASSIGN chain op");
            check(thunkOps.get(3).result() instanceof ValueId sourceValue
                    && thunkOps.get(2).payload() instanceof KindPayload.BindingStorePayload
                        storePayload
                    && sourceValue.equals(storePayload.value())
                    && sourceValue.equals(thunkOps.get(0).result()),
                "the inner ASSIGN produces the committed source function identity "
                    + "(the store's value = the load's result — identity "
                    + "preservation); the adapter itself carries zero operands "
                    + "(creation evaluates nothing)");
        }
        if (result.lowering().table() != null) {
            check(result.lowering().table().opBlocks().get(thunkOps.get(0).opId())
                    .equals(thunk.blockId()),
                "the source load's block membership is exactly the thunk block");
        }

        // The call-result source through the shape-map child's IR-level
        // seam (the pinned jvm-fv-return-function-value shape): a CALL op
        // whose result is a function maps to REEVALUATE_THUNK and the
        // thunk builder wraps the ordered call op with its captures.
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.CALL,
                Optional.empty()) == CaptureMode.REEVALUATE_THUNK,
            "a call-result source maps to REEVALUATE_THUNK (the closed "
                + "non-identifier arm)");
        BlockId callThunkBlock = new BlockId(9001L);
        ValueId calleeValue = new ValueId(9101L);
        ValueId callResult = new ValueId(9102L);
        BindingGeneration callCapture = new BindingGeneration(new BindingId(43L), 0);
        SemanticOp call = irValueOp(new OpId(MODULE, 9201L), SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Indirect(calleeValue), INNER_SIG,
                List.of(), null, null, null, null),
            callResult, INNER_SIG, List.of(calleeValue), List.of(INNER_SIG));
        AdaptSourceRef.Thunk callThunk = AdapterThunkConstruction.buildThunk(callThunkBlock,
            List.of(call), List.of(callCapture));
        check(callThunk.blockId().equals(callThunkBlock)
                && callThunk.capturedBindings().equals(List.of(callCapture)),
            "the call-result source wraps into Thunk {blockId, [capture]}");
        check(AdapterThunkConstruction.producedValueOf(List.of(call)).equals(callResult),
            "the thunk's produced value is the call's function-typed result");
    }

    /** Builds one IR-level op over the pinned schema (test construction only). */
    private static SemanticOp irValueOp(OpId opId, SemanticOpKind kind, KindPayload payload,
                                        ValueId result, RuntimeDescriptor resultType,
                                        List<ValueId> operands,
                                        List<RuntimeDescriptor> operandTypes) {
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, operandTypes, null,
            payload, FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder");
        SourceOrigin origin = new SourceOrigin(SOURCE_ID, new SourceSpan(SOURCE_ID, 1, 1, 1, 1),
            SourceOriginKind.USER, new AnchorId(opId.id()), null);
        return new SemanticOp(opId, kind, origin, result, resultType, operands,
            operandTypes, payload, FailurePolicyId.NO_DEAL_FAILURE, contract);
    }

    // =========================================================================
    // 5. Host/external import reads: the registry seam, REEVALUATE_THUNK
    // =========================================================================

    static void testHostExternalImportReadsThroughRegistrySeam() {
        System.out.println("-- host/external import reads: the registry seam, "
            + "REEVALUATE_THUNK (no VALUE carve-out), HostFunction/ExternalFunction "
            + "registrations --");

        RuntimeDescriptor.Func exportDescriptor = WIDE_SIG;
        ModuleId hostModule = new ModuleId("host1");
        ModuleId calleeModule = new ModuleId("callee");

        // --- Host export member read ---
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity hostIdentity = new FunctionAllocationIdentity(1001L);
        FunctionBindingRegistry.FunctionValueMaterialization hostMaterialization =
            registry.registerHostOrExternalImport(hostIdentity,
                new KindPayload.MemberReadPayload(new ValueId(9001L), "g"),
                new FunctionBindingRegistry.FunctionValueImportFacts(hostModule, null, "g",
                    exportDescriptor),
                null);
        check(hostMaterialization.source()
                == FunctionBindingRegistry.FunctionValueMaterializationSource.HOST_EXPORT,
            "the seam classifies the host read as a HOST_EXPORT materialization");
        check(registry.bindings().get(hostIdentity)
                instanceof FunctionExecutionBinding.HostFunction hostFunction
                && hostFunction.hostModuleId().equals(hostModule)
                && hostFunction.exportName().equals("g")
                && hostFunction.descriptor().equals(exportDescriptor),
            "the seam registers exactly one HostFunction {hostModuleId, exportName, "
                + "descriptor} for the host export read");
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.MEMBER_READ,
                Optional.of(hostMaterialization)) == CaptureMode.REEVALUATE_THUNK,
            "the host import read maps to REEVALUATE_THUNK with the producer facts "
                + "present — no VALUE carve-out for import reads");

        // The thunk wraps the IR-level member-read ops over the pinned schema:
        // the import-alias receiver load, then the MEMBER_READ.
        BlockId hostThunkBlock = new BlockId(7001L);
        ValueId aliasLoad = new ValueId(7101L);
        ValueId hostValue = new ValueId(7102L);
        BindingGeneration aliasCapture = new BindingGeneration(new BindingId(42L), 0);
        SemanticOp receiverLoad = irValueOp(new OpId(MODULE, 7201L),
            SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(aliasCapture.binding(), 0),
            aliasLoad, RuntimeDescriptor.Table.INSTANCE, List.of(), List.of());
        SemanticOp memberRead = irValueOp(new OpId(MODULE, 7202L),
            SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(aliasLoad, "g"),
            hostValue, exportDescriptor, List.of(aliasLoad),
            List.of(RuntimeDescriptor.Table.INSTANCE));
        AdaptSourceRef.Thunk hostThunk = AdapterThunkConstruction.buildThunk(hostThunkBlock,
            List.of(receiverLoad, memberRead), List.of(aliasCapture));
        check(hostThunk.blockId().equals(hostThunkBlock)
                && hostThunk.capturedBindings().equals(List.of(aliasCapture)),
            "the host read wraps into Thunk {blockId, [import-alias capture]} — "
                + "generation-pinned, first-reference order");
        check(AdapterThunkConstruction.producedValueOf(List.of(receiverLoad, memberRead))
                .equals(hostValue),
            "the host thunk's produced value is the member read's function-typed result");

        // --- External (cross-module) import member read ---
        FunctionAllocationIdentity externalIdentity = new FunctionAllocationIdentity(1002L);
        String externalHash = "a".repeat(64);
        ModuleRoutePlan sharedPlan = new ModuleRoutePlan(Target.LUAJIT,
            Map.of(calleeModule, ModuleRoute.SHARED), Set.of(), Set.of(), List.of(),
            externalHash, "plan-" + externalHash.substring(0, 16));
        FunctionBindingRegistry.FunctionValueMaterialization externalMaterialization =
            registry.registerHostOrExternalImport(externalIdentity,
                new KindPayload.MemberReadPayload(new ValueId(9002L), "g"),
                new FunctionBindingRegistry.FunctionValueImportFacts(null, calleeModule,
                    "g", exportDescriptor),
                sharedPlan);
        check(externalMaterialization.source()
                == FunctionBindingRegistry.FunctionValueMaterializationSource.EXTERNAL_IMPORT,
            "the seam classifies the cross-module read as an EXTERNAL_IMPORT "
                + "materialization");
        check(registry.bindings().get(externalIdentity)
                instanceof FunctionExecutionBinding.ExternalFunction externalFunction
                && externalFunction.moduleId().equals(calleeModule)
                && externalFunction.exportName().equals("g")
                && externalFunction.descriptor().equals(exportDescriptor)
                && externalFunction.executionOwner()
                    == deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY,
            "the seam registers exactly one ExternalFunction with executionOwner "
                + "SHARED_BODY for a shared-routed callee");
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.MEMBER_READ,
                Optional.of(externalMaterialization)) == CaptureMode.REEVALUATE_THUNK,
            "the external import read maps to REEVALUATE_THUNK — the same closed "
                + "non-identifier arm, never a target-derived special case");

        // A retained-ABI callee records RETAINED_ABI (route facts only —
        // the mode never comes from the route).
        FunctionAllocationIdentity retainedIdentity = new FunctionAllocationIdentity(1003L);
        FunctionBindingRegistry.FunctionValueMaterialization retainedMaterialization =
            registry.registerHostOrExternalImport(retainedIdentity,
                new KindPayload.MemberReadPayload(new ValueId(9003L), "g"),
                new FunctionBindingRegistry.FunctionValueImportFacts(null, calleeModule,
                    "g", exportDescriptor),
                new ModuleRoutePlan(Target.LUAJIT, Map.of(calleeModule, ModuleRoute.LEGACY),
                    Set.of(), Set.of(), List.of(), "b".repeat(64),
                    "plan-" + "b".repeat(16)));
        check(registry.bindings().get(retainedIdentity)
                instanceof FunctionExecutionBinding.ExternalFunction externalFunction
                && externalFunction.executionOwner()
                    == deal.semantic.ir.ExternalExecutionOwner.RETAINED_ABI,
            "a retained-ABI callee registers ExternalFunction with executionOwner "
                + "RETAINED_ABI");
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.EXPORT_READ,
                Optional.of(retainedMaterialization)) == CaptureMode.REEVALUATE_THUNK,
            "an export-read materialization maps to the same non-identifier arm");

        // Registry uniqueness at the seam: a duplicate registration of
        // the same producing allocation is rejected fail closed (never
        // overwritten) — exactly one binding per identity.
        check(registry.size() == 3,
            "the seam registry holds exactly one binding per producing allocation "
                + "(3 registrations for 3 identities); got " + registry.size());
        boolean duplicateRejected = false;
        try {
            registry.registerHostOrExternalImport(hostIdentity,
                new KindPayload.MemberReadPayload(new ValueId(9004L), "g"),
                new FunctionBindingRegistry.FunctionValueImportFacts(hostModule, null, "g",
                    exportDescriptor),
                null);
        } catch (IllegalStateException expected) {
            duplicateRejected = true;
        }
        check(duplicateRejected,
            "a duplicate-key seam registration is rejected fail closed (never "
                + "overwritten)");
    }

    // =========================================================================
    // 6. VALUE over the function expression and the proved binding
    // =========================================================================

    static void testValueOverFunctionExpression() {
        System.out.println("-- VALUE: function-expression source over the CLOSURE_NEW "
            + "result --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding ve = fact(result.bindingFacts(), "ve");
        if (ve == null) {
            return;
        }

        SemanticOp veAdapter = null;
        for (SemanticOp adapter : adaptersOf(ops)) {
            for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
                if (op.payload() instanceof KindPayload.BindingInitPayload payload
                        && payload.binding().equals(ve.binding())
                        && payload.value().equals(adapter.result())) {
                    veAdapter = adapter;
                }
            }
        }
        check(veAdapter != null, "ve's VALUE adapter exists (wired into ve's INIT)");
        if (veAdapter == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(veAdapter);
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.VALUE,
            "ve's adapter mode is VALUE (a function expression is a materialized "
                + "function-value operand)");
        check(payload.source() instanceof AdaptSourceRef.Value value,
            "the source is Value {ValueId}");
        if (!(payload.source() instanceof AdaptSourceRef.Value value)) {
            return;
        }
        SemanticOp producing = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.CLOSURE_NEW)) {
            if (op.result().equals(value.value())) {
                producing = op;
            }
        }
        check(producing != null
                && producing.payload() instanceof KindPayload.ClosureNewPayload closure
                && closure.signature().equals(INNER_SIG),
            "the Value operand is the function expression's CLOSURE_NEW result with "
                + "signature (int)->null");
        check(veAdapter.operands().size() == 1
                && veAdapter.operands().get(0).equals(value.value()),
            "creation completes the operand exactly once: the adapter's single operand "
                + "is the retained closure identity");
        check(payload.proof() == null,
            "no proof is present — the payload's proof is present iff VALUE's operand "
                + "is a binding load (B8), and this operand is a closure result");
        check(operandConsumers(ops, value.value()) == 1,
            "the closure identity is consumed exactly once in the creation flow (the "
                + "adapter's operand)");

        // The boundary observes the adapter identity; the INIT commits it.
        SemanticOp veBoundary = boundaryOpFor(ops, (ValueId) veAdapter.result());
        check(veBoundary != null && veBoundary.payload()
                instanceof KindPayload.BoundaryPayload boundary
                && boundary.kind() == BoundaryKind.VARIABLE_DECLARATION
                && boundary.descriptor().equals(payload.targetSignature()),
            "ve's declaration boundary checks the target signature and observes the "
                + "adapter identity (exact-signature pass-through)");
        FunctionExecutionBinding binding =
            unit.functionBindings().get(new FunctionAllocationIdentity(value.value().id()));
        check(binding instanceof FunctionExecutionBinding.LoweredBody,
            "the closure identity registers exactly one LoweredBody binding");
    }

    static void testValueOverProvedBinding() {
        System.out.println("-- VALUE: proved binding over the single proved load with "
            + "the recorded proof --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding proved = fact(result.bindingFacts(), "proved");
        SemanticLowerer.BindingCoreBinding vp = fact(result.bindingFacts(), "vp");
        if (proved == null || vp == null) {
            return;
        }

        check(result.proofFacts().proven(proved.binding(), 0),
            "proved carries its conservative BindingImmutabilityProof (never "
                + "assigned)");
        SemanticOp vpAdapter = null;
        for (SemanticOp adapter : adaptersOf(ops)) {
            for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
                if (op.payload() instanceof KindPayload.BindingInitPayload payload
                        && payload.binding().equals(vp.binding())
                        && payload.value().equals(adapter.result())) {
                    vpAdapter = adapter;
                }
            }
        }
        check(vpAdapter != null, "vp's VALUE adapter exists (wired into vp's INIT)");
        if (vpAdapter == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(vpAdapter);
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.VALUE,
            "vp's adapter mode is VALUE (a binding with the recorded proof)");
        check(payload.proof() != null
                && payload.proof().binding().equals(proved.binding())
                && payload.proof().generation() == 0,
            "the proof is present naming exactly {proved, 0} — the binding/generation "
                + "of the proved load");
        check(payload.source() instanceof AdaptSourceRef.Value value
                && vpAdapter.operands().size() == 1
                && vpAdapter.operands().get(0).equals(value.value()),
            "the Value operand is the single proved load's result — creation "
                + "completes the load exactly once");
        if (!(payload.source() instanceof AdaptSourceRef.Value value)) {
            return;
        }
        List<SemanticOp> provedLoads = loadsOf(ops, proved.binding(), 0);
        check(provedLoads.size() == 1,
            "exactly one BINDING_LOAD of proved exists (the single proved load at "
                + "creation); got " + provedLoads.size());
        if (provedLoads.size() == 1) {
            check(provedLoads.get(0).result().equals(value.value()),
                "the operand is the proved load's result — the retained proved "
                    + "function identity");
            check(provedLoads.get(0).operands().isEmpty(),
                "the proved load is an ordinary generation-checked load (no operand)");
        }
        check(operandConsumers(ops, value.value()) == 1,
            "the proved load's result is consumed exactly once (the adapter's "
                + "operand)");
        // The VALUE operand load is not a capture reference: proved stays
        // DIRECT (B2 — the cell-kind test asserts the full iff).
        check(proved.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "proved stays DIRECT (the VALUE operand load is not a capture reference)");
        SemanticOp vpBoundary = boundaryOpFor(ops, (ValueId) vpAdapter.result());
        check(vpBoundary != null && vpBoundary.payload()
                instanceof KindPayload.BoundaryPayload boundary
                && boundary.kind() == BoundaryKind.VARIABLE_DECLARATION
                && boundary.descriptor().equals(payload.targetSignature()),
            "vp's declaration boundary checks the target signature and observes the "
                + "adapter identity");
    }

    // =========================================================================
    // 7. Boundary positions never adapt (direct flow; pinned return shape)
    // =========================================================================

    static void testBoundaryPositionsNeverAdapt() {
        System.out.println("-- boundary positions never adapt: direct flow into the "
            + "boundary slot, zero adapters --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");

        // The ARRAY_SLOT assignment chain [container, key, value, length,
        // normalize, boundary, commit]: the M < N source value flows
        // directly into the ARRAY_ELEMENT_ASSIGNMENT boundary slot.
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
            "the value child is the BINDING_LOAD of inner (the M < N source)");
        if (valueOp != null && elementBoundary != null) {
            check(elementBoundary.kind() == SemanticOpKind.BOUNDARY
                    && elementBoundary.payload() instanceof KindPayload.BoundaryPayload
                        payload
                    && payload.kind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                    && payload.input().equals(valueOp.result()),
                "the ARRAY_ELEMENT_ASSIGNMENT boundary's input is the M < N value "
                    + "itself — direct flow into the position's boundary slot, zero "
                    + "adapters");
        }

        // The array literal element: the exact-signature value flows
        // directly into its ARRAY_LITERAL_ELEMENT boundary slot.
        SemanticOp arrayNew = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.ARRAY_NEW)) {
            if (op.payload() instanceof KindPayload.ArrayNewPayload payload
                    && !payload.values().isEmpty()) {
                arrayNew = op;
            }
        }
        check(arrayNew != null, "the ARRAY_NEW carries the literal element");
        if (arrayNew != null) {
            KindPayload.ArrayNewPayload arrayPayload =
                (KindPayload.ArrayNewPayload) arrayNew.payload();
            check(arrayPayload.values().size() == 1
                    && arrayPayload.elementBoundaryOpIds().size() == 1,
                "the ARRAY_NEW carries one element value and one element boundary");
            if (arrayPayload.values().size() == 1
                    && arrayPayload.elementBoundaryOpIds().size() == 1) {
                SemanticOp literalBoundary =
                    opOf(ops, arrayPayload.elementBoundaryOpIds().get(0));
                check(literalBoundary != null && literalBoundary.payload()
                        instanceof KindPayload.BoundaryPayload literalPayload
                        && literalPayload.kind() == BoundaryKind.ARRAY_LITERAL_ELEMENT
                        && literalPayload.input().equals(arrayPayload.values().get(0)),
                    "the array literal element's value flows directly into its "
                        + "ARRAY_LITERAL_ELEMENT boundary slot");
            }
        }

        // No adapter result feeds any boundary position: every adapter's
        // boundary consumer is exactly its own VARIABLE_DECLARATION/
        // VARIABLE_ASSIGNMENT chain (the wiring test), so the two typed
        // boundary positions contribute zero adapters.
        for (SemanticOp adapter : adaptersOf(ops)) {
            check(adapter.result() instanceof ValueId identity
                    && boundaryConsumers(ops, identity) == 1
                    && boundaryOpFor(ops, identity).payload()
                        instanceof KindPayload.BoundaryPayload payload
                    && (payload.kind() == BoundaryKind.VARIABLE_DECLARATION
                        || payload.kind() == BoundaryKind.VARIABLE_ASSIGNMENT),
                "adapter " + adapter.opId() + " feeds only its own VARIABLE_* "
                    + "boundary chain — zero adapters at typed boundary positions");
        }

        // Classifications: the exact array literal element records
        // BOUNDARY_DIRECT with no expectation; the M < N element records
        // the E8010 expectation at the element boundary.
        List<AdapterCreationRule.PositionClassification> literalElements =
            new ArrayList<>();
        List<AdapterCreationRule.PositionClassification> elementAssignments =
            new ArrayList<>();
        for (AdapterCreationRule.PositionClassification classification
                : result.creationFacts().classifications()) {
            if (classification.boundaryKind() == BoundaryKind.ARRAY_LITERAL_ELEMENT) {
                literalElements.add(classification);
            }
            if (classification.boundaryKind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT) {
                elementAssignments.add(classification);
            }
        }
        check(literalElements.size() == 1
                && literalElements.get(0).disposition()
                    == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                && literalElements.get(0).candidate().isEmpty()
                && literalElements.get(0).failureExpectation().isEmpty(),
            "the exact-signature array literal element classifies BOUNDARY_DIRECT "
                + "with no candidate and no expectation");
        check(elementAssignments.size() == 1
                && elementAssignments.get(0).disposition()
                    == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                && elementAssignments.get(0).candidate().isEmpty()
                && elementAssignments.get(0).failureExpectation().isPresent()
                && elementAssignments.get(0).failureExpectation().get().code()
                    .equals("E8010")
                && elementAssignments.get(0).failureExpectation().get().policy()
                    == FailurePolicyId.FUNCTION_SIGNATURE,
            "the M < N array element assignment classifies BOUNDARY_DIRECT with the "
                + "recorded E8010 FUNCTION_SIGNATURE expectation (the executed "
                + "rejection is the boundary machinery's)");

        // The pinned return shape's no-adapt facts (jvm-fv-sig-check-return-error):
        // FUNCTION_RETURN admits no adaptation arm; the (int)=>int value
        // across the declared (a:int,b:int)=>int return classifies
        // BOUNDARY_DIRECT with the E8010 expectation carrying the
        // registry's canonical template; the exact pair records none.
        check(!AdapterCreationRule.admitsAdaptation(BoundaryKind.FUNCTION_RETURN),
            "FUNCTION_RETURN admits no adaptation arm (boundaries never adapt)");
        AdapterCreationRule.PositionClassification returnMismatch =
            AdapterCreationRule.classifyBoundaryPosition(BoundaryKind.FUNCTION_RETURN,
                new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE),
                new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                    Type.Int.INSTANCE));
        check(returnMismatch.disposition() == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                && returnMismatch.candidate().isEmpty(),
            "the (int)=>int value across the declared (a:int,b:int)=>int return "
                + "classifies BOUNDARY_DIRECT with no adaptation candidate — the "
                + "value flows directly into the return position's boundary slot");
        check(returnMismatch.failureExpectation().isPresent()
                && returnMismatch.failureExpectation().get().code().equals("E8010")
                && returnMismatch.failureExpectation().get().policy()
                    == FailurePolicyId.FUNCTION_SIGNATURE
                && returnMismatch.failureExpectation().get().boundaryKind()
                    == BoundaryKind.FUNCTION_RETURN
                && returnMismatch.failureExpectation().get().messageTemplate().equals(
                    FailureContractRegistry.row(FailurePolicyId.FUNCTION_SIGNATURE)
                        .template()),
            "the M < N return position records the E8010 FUNCTION_SIGNATURE "
                + "expectation at the FUNCTION_RETURN boundary with the registry's "
                + "canonical template");
        AdapterCreationRule.PositionClassification returnExact =
            AdapterCreationRule.classifyBoundaryPosition(BoundaryKind.FUNCTION_RETURN,
                new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                    Type.Int.INSTANCE),
                new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                    Type.Int.INSTANCE));
        check(returnExact.disposition() == AdapterCreationRule.Disposition.BOUNDARY_DIRECT
                && returnExact.failureExpectation().isEmpty(),
            "an exact-signature pair at the FUNCTION_RETURN boundary records no "
                + "expectation (the exact-signature pass is the boundary "
                + "machinery's)");

        if (inner == null || valueOp == null || valueOp.result() == null) {
            return;
        }
        // The array element assignment's source load is inner's identity:
        // a later typed-boundary crossing of an ordinary function value
        // (identity preserved through loads) is an ordinary
        // FUNCTION_SIGNATURE check — here the value crosses directly.
        check(valueOp != null && valueOp.result().equals(
                loadsOf(ops, inner.binding(), 0).get(0).result()),
            "the M < N element value is inner's identity itself (loads preserve "
                + "identity — no adapter intervenes)");
    }

    // =========================================================================
    // 8. Creation wiring: adapter results into exactly their own position's chain
    // =========================================================================

    static void testCreationWiring() {
        System.out.println("-- creation wiring: every adapter result is the direct "
            + "input of exactly its own position's boundary chain --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        for (SemanticOp adapter : adaptersOf(ops)) {
            check(adapter.result() instanceof ValueId,
                "the adapter publishes a value identity");
            check(childrenOf(ops, adapter.opId()) == 0,
                "adapter " + adapter.opId() + " parents zero ops (the adapter adds no "
                    + "second boundary)");
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null || !(adapter.result() instanceof ValueId identity)) {
                continue;
            }
            check(boundaryConsumers(ops, identity) == 1,
                "the adapter result is the direct input of exactly one BOUNDARY op "
                    + "(its own position's chain); got "
                    + boundaryConsumers(ops, identity));
            SemanticOp boundary = boundaryOpFor(ops, identity);
            if (boundary == null) {
                continue;
            }
            check(boundary.payload() instanceof KindPayload.BoundaryPayload boundaryPayload
                    && (boundaryPayload.kind() == BoundaryKind.VARIABLE_DECLARATION
                        || boundaryPayload.kind() == BoundaryKind.VARIABLE_ASSIGNMENT),
                "the consuming boundary is exactly the adapted position's own "
                    + "VARIABLE_DECLARATION/VARIABLE_ASSIGNMENT boundary chain");
            OpId wiringTarget = emissionWiringTargetOf(result, identity);
            check(wiringTarget != null && boundary.opId().equals(wiringTarget),
                "the boundary op equals the recorded wiring target (the creation-rule "
                    + "child's prepared point)");
            check(boundary.payload() instanceof KindPayload.BoundaryPayload boundaryPayload
                    && boundaryPayload.descriptor().equals(payload.targetSignature()),
                "the position's boundary checks the adapter's target signature — the "
                    + "exact-signature pass-through");
            // The adapter feeds no other BOUNDARY op of any kind (the
            // NO_ADAPTER_AT_BOUNDARY production-time check validated the
            // unit — asserted here op-by-op).
            for (SemanticOp op : ops) {
                if (op == boundary || op.kind() != SemanticOpKind.BOUNDARY) {
                    continue;
                }
                check(!(op.payload() instanceof KindPayload.BoundaryPayload other
                        && identity.equals(other.input())),
                    "adapter " + adapter.opId() + " feeds no BOUNDARY op other than "
                        + "its own position's chain");
            }
        }
    }

    // =========================================================================
    // 9. Registry uniqueness
    // =========================================================================

    static void testRegistryUniqueness() {
        System.out.println("-- registry uniqueness: exactly one binding per producing "
            + "allocation, no duplicates/orphans --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        // Five closures (inner, wide, main, the function expression) and
        // five adapters — ten registrations, one per producing allocation.
        check(ofKind(ops, SemanticOpKind.CLOSURE_NEW).size() == 4,
            "the corpus produces four CLOSURE_NEW ops (inner, wide, main, the "
                + "function expression)");
        check(unit.functionBindings().size() == 11,
            "the unit's registry holds exactly eleven bindings (4 LoweredBody + 5 "
                + "AdapterBinding + the two producer-less intrinsic seeds, "
                + "ISSUE-0632); got " + unit.functionBindings().size());
        Set<Long> keys = new java.util.HashSet<>();
        int loweredBodies = 0;
        int adapterBindings = 0;
        int intrinsicSeeds = 0;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            check(keys.add(entry.getKey().id()),
                "the registry keys are distinct (no duplicate registrations)");
            if (entry.getValue() instanceof FunctionExecutionBinding.LoweredBody) {
                loweredBodies++;
            }
            if (entry.getValue() instanceof FunctionExecutionBinding.AdapterBinding) {
                adapterBindings++;
            }
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction) {
                intrinsicSeeds++;
            }
        }
        check(loweredBodies == 4 && adapterBindings == 5 && intrinsicSeeds == 2,
            "the registry holds 4 LoweredBody, 5 AdapterBinding, and 2 IntrinsicFunction "
                + "registrations; got " + loweredBodies + "/" + adapterBindings + "/"
                + intrinsicSeeds);

        // Every CLOSURE_NEW result resolves to exactly one LoweredBody;
        // every FUNCTION_ADAPT result resolves to exactly one
        // AdapterBinding (the R-FUNCTION-BINDING schema rule ran green
        // through the pipeline — asserted here op-by-op).
        for (SemanticOp closure : ofKind(ops, SemanticOpKind.CLOSURE_NEW)) {
            check(closure.result() instanceof ValueId identity
                    && unit.functionBindings().get(
                        new FunctionAllocationIdentity(identity.id()))
                        instanceof FunctionExecutionBinding.LoweredBody body
                    && closure.payload() instanceof KindPayload.ClosureNewPayload payload
                    && body.functionId().equals(payload.function())
                    && body.blockId().equals(payload.binding().blockId()),
                "CLOSURE_NEW " + closure.opId() + " registers exactly one LoweredBody "
                    + "keyed by its allocation identity");
        }
        for (SemanticOp adapter : adaptersOf(ops)) {
            check(adapter.result() instanceof ValueId identity
                    && unit.functionBindings().get(
                        new FunctionAllocationIdentity(identity.id()))
                        instanceof FunctionExecutionBinding.AdapterBinding binding
                    && binding.adaptOpId().equals(adapter.opId()),
                "FUNCTION_ADAPT " + adapter.opId() + " registers exactly one "
                    + "AdapterBinding keyed by its allocation identity");
        }
        // No orphan entries: every non-seed key is a producing op's result
        // identity, and every seed key is a producer-less intrinsic
        // registration whose producing position is its seed BINDING_INIT
        // (ISSUE-0632).
        for (FunctionAllocationIdentity key : unit.functionBindings().keySet()) {
            if (unit.functionBindings().get(key)
                    instanceof FunctionExecutionBinding.IntrinsicFunction) {
                int seedInits = 0;
                for (SemanticOp op : ops) {
                    if (op.kind() == SemanticOpKind.BINDING_INIT
                            && op.payload() instanceof KindPayload.BindingInitPayload init
                            && init.value().id() == key.id()) {
                        seedInits++;
                    }
                }
                check(seedInits == 1, "the intrinsic seed key " + key + " is produced by "
                    + "exactly one seed BINDING_INIT; got " + seedInits);
                continue;
            }
            boolean produced = false;
            for (SemanticOp op : ops) {
                if (op.result() instanceof ValueId value && value.id() == key.id()
                        && (op.kind() == SemanticOpKind.CLOSURE_NEW
                            || op.kind() == SemanticOpKind.FUNCTION_ADAPT)) {
                    produced = true;
                }
            }
            check(produced, "registry key " + key + " is a producing op's result "
                + "identity (no orphan registrations)");
        }
    }

    // =========================================================================
    // 10. Cell-kind iff across the corpus
    // =========================================================================

    static void testCellKindIff() {
        System.out.println("-- cell-kind iff: every incarnation equals the closed "
            + "derivation over the three capture reference sets --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        // Recompute the closed derivation from the unit's own three
        // capture reference sets: (1) every CLOSURE_NEW captures entry,
        // (2) every REEVALUATE_THUNK capturedBindings entry, (3) every
        // FUNCTION_ADAPT(SHARED_CELL) SharedCell source reference — plus
        // the pinned special cases (incarnation.pinnedSharedCell).
        SemanticLowerer.CellKindDerivation derivation =
            new SemanticLowerer.CellKindDerivation();
        for (SemanticOp closure : ofKind(ops, SemanticOpKind.CLOSURE_NEW)) {
            if (!(closure.payload() instanceof KindPayload.ClosureNewPayload payload)) {
                continue;
            }
            for (BindingGeneration capture : payload.captures()) {
                for (SemanticLowerer.BindingCoreBinding binding
                        : result.bindingFacts().bindings()) {
                    if (!binding.binding().equals(capture.binding())) {
                        continue;
                    }
                    for (SemanticLowerer.BindingCoreIncarnation incarnation
                            : binding.incarnations()) {
                        derivation.registerCaptureReference(incarnation);
                    }
                }
            }
        }
        for (SemanticOp adapter : adaptersOf(ops)) {
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null) {
                continue;
            }
            if (payload.source() instanceof AdaptSourceRef.Thunk thunk) {
                for (BindingGeneration capture : thunk.capturedBindings()) {
                    derivation.registerCaptureReference(
                        incarnationOf(result, capture.binding(), capture.generation()));
                }
            }
            if (payload.source() instanceof AdaptSourceRef.SharedCell shared) {
                derivation.registerCaptureReference(
                    incarnationOf(result, shared.binding(), shared.generation()));
            }
        }

        // The expected kinds over the recomputed derivation.
        for (SemanticLowerer.BindingCoreBinding binding
                : result.bindingFacts().bindings()) {
            for (SemanticLowerer.BindingCoreIncarnation incarnation
                    : binding.incarnations()) {
                BindingCellKind expected = derivation.cellKindOf(incarnation);
                check(incarnation.cellKind() == expected,
                    binding.name() + "/generation " + incarnation.generation()
                        + " carries the derived cell kind " + expected + "; got "
                        + incarnation.cellKind());
                SemanticOp alloc = allocOf(ops, binding.binding(),
                    incarnation.generation());
                if (alloc == null) {
                    // FOR_EACH/group incarnations have no ALLOC payload
                    // (pinned special cases); the corpus has none.
                    continue;
                }
                check(alloc.payload() instanceof KindPayload.BindingAllocPayload
                        payload && payload.cellKind() == expected,
                    binding.name() + "'s BINDING_ALLOC payload carries the final "
                        + "derived kind " + expected);
            }
        }

        // The pinned expectations over the three arms:
        // inner — closure-captured by main's body and thunk-captured;
        // wide — closure-captured by main's body;
        // retarget — thunk-captured and SharedCell-referenced twice;
        // every other corpus binding stays DIRECT.
        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding wide = fact(result.bindingFacts(), "wide");
        SemanticLowerer.BindingCoreBinding retarget = fact(result.bindingFacts(), "retarget");
        SemanticLowerer.BindingCoreBinding exactA = fact(result.bindingFacts(), "exactA");
        SemanticLowerer.BindingCoreBinding sc1 = fact(result.bindingFacts(), "sc1");
        SemanticLowerer.BindingCoreBinding sc2 = fact(result.bindingFacts(), "sc2");
        SemanticLowerer.BindingCoreBinding thunkSrc = fact(result.bindingFacts(), "thunkSrc");
        SemanticLowerer.BindingCoreBinding ve = fact(result.bindingFacts(), "ve");
        SemanticLowerer.BindingCoreBinding proved = fact(result.bindingFacts(), "proved");
        SemanticLowerer.BindingCoreBinding vp = fact(result.bindingFacts(), "vp");
        if (inner != null && wide != null && retarget != null && exactA != null
                && sc1 != null && sc2 != null && thunkSrc != null && ve != null
                && proved != null && vp != null) {
            check(inner.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                "inner is SHARED_CELL (closure-captured by main's body and "
                    + "thunk-captured by thunkSrc)");
            check(wide.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                "wide is SHARED_CELL (closure-captured by main's body)");
            check(retarget.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
                "retarget is SHARED_CELL (the SharedCell adapter references and the "
                    + "thunk capture)");
            check(exactA.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "exactA stays DIRECT (reassigned but never captured — reassignability "
                    + "alone never forces SHARED_CELL)");
            check(sc1.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                    && sc2.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                    && thunkSrc.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                    && ve.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                    && vp.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "sc1/sc2/thunkSrc/ve/vp stay DIRECT (adapter results are ordinary "
                    + "values, not capture references)");
            check(proved.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
                "proved stays DIRECT (the VALUE operand load is not a capture "
                    + "reference)");
        }
    }

    /** The incarnation fact of exactly the named {binding, generation} pair. */
    private static SemanticLowerer.BindingCoreIncarnation incarnationOf(
            SemanticLowerer.ValidationCoreResult result, BindingId binding,
            long generation) {
        for (SemanticLowerer.BindingCoreBinding candidate
                : result.bindingFacts().bindings()) {
            if (!candidate.binding().equals(binding)) {
                continue;
            }
            for (SemanticLowerer.BindingCoreIncarnation incarnation
                    : candidate.incarnations()) {
                if (incarnation.generation() == generation) {
                    return incarnation;
                }
            }
        }
        fail("no incarnation fact records {binding " + binding + ", generation "
            + generation + "}");
        return null;
    }

    // =========================================================================
    // 11. No adapter invocation
    // =========================================================================

    static void testNoAdapterInvocation() {
        System.out.println("-- no adapter invocation: zero invocation ops resolve an "
            + "AdapterBinding --");

        SemanticLowerer.ValidationCoreResult result = validatedResult(corpusSource(),
            "the integration corpus");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        List<SemanticOp> invocations = invocationOps(ops);
        check(invocations.isEmpty(),
            "the corpus unit contains zero CALL/CALLBACK_INVOKE/ASYNC_START ops — no "
                + "invocation op exists that could resolve an AdapterBinding; got "
                + invocations.size());
        for (SemanticOp adapter : adaptersOf(ops)) {
            check(adapter.result() instanceof ValueId identity
                    && operandConsumers(ops, identity) == 0,
                "no unit op takes the adapter identity as an operand (the adapter "
                    + "identity is consumed only through its boundary chain — never "
                    + "invoked)");
        }
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.AdapterBinding) {
                check(invocations.isEmpty(),
                    "no invocation op resolves the AdapterBinding " + entry.getKey()
                        + " (invocation-observable adapter behavior remains E7's "
                        + "verification and is not exercised here)");
            }
        }
    }

    // =========================================================================
    // 12. The executed boundary-position E8010 drive (E4's machinery)
    // =========================================================================

    /**
     * The executed drive over the pinned cell — kind
     * {@code FUNCTION_RETURN}, function descriptor, policy
     * {@code FUNCTION_SIGNATURE}, realized as
     * {@code RuntimeValidation(checkId)} — through
     * {@link BoundaryExecutor#execute}: the exact E8010 record for the
     * {@code M < N} mismatch, the failure origin at the return boundary
     * op, the pre-invocation ordering evidence (the returned function
     * identity is never invoked), and the negative control (an
     * exact-signature value passes). The drive units carry the pinned
     * return shape over the pinned schema records — a {@code CLOSURE_NEW}
     * producing the returned identity with its registered
     * {@code LoweredBody}, the {@code RETURN} op naming the boundary, and
     * the {@code FUNCTION_RETURN} boundary whose direct input is that
     * identity — and zero {@code FUNCTION_ADAPT} ops. The executed check
     * is the executor's comparator, never a static registry lookup or
     * the retained fixture alone.
     */
    static void testExecutedReturnBoundaryE8010Drive() {
        System.out.println("-- executed boundary-position E8010 drive: FUNCTION_RETURN "
            + "+ FUNCTION_SIGNATURE through BoundaryExecutor --");

        // --- Drive unit A: the pinned return shape (M < N mismatch). ---
        DriveUnit driveA = driveUnit(RETURNED_SIG, DECLARED_SIG);
        check(SemanticIrValidator.validate(driveA.unit(), driveA.facts()).isEmpty(),
            "the pinned-return-shape drive unit validates (the FUNCTION_RETURN + "
                + "function descriptor + FUNCTION_SIGNATURE cell is a validator-"
                + "accepted cell)");
        check(ofKind(driveA.unit().ops(), SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "the drive unit carries zero FUNCTION_ADAPT ops — the return position "
                + "never adapts");

        // The executed cell facts come from the unit's own boundary op
        // payload — never a static registry substitution.
        KindPayload.BoundaryPayload cell = (KindPayload.BoundaryPayload)
            driveA.boundaryOp().payload();
        check(cell.kind() == BoundaryKind.FUNCTION_RETURN,
            "the executed cell's kind is FUNCTION_RETURN");
        check(cell.descriptor() instanceof RuntimeDescriptor.Func declared
                && declared.equals(DECLARED_SIG),
            "the executed cell checks the declared function descriptor "
                + DECLARED_SIG.canonicalSpecText());
        check(driveA.boundaryOp().failurePolicy() == FailurePolicyId.FUNCTION_SIGNATURE,
            "the executed cell's policy is FUNCTION_SIGNATURE (the descriptor-kind "
                + "rule for function descriptors)");
        check(cell.realization() instanceof BoundaryRealization.RuntimeValidation
                validation && "return-check".equals(validation.checkId()),
            "the executed cell is realized as RuntimeValidation(checkId) — the "
                + "physical runtime check");

        // Execute the closed exact-signature check over RuntimeDescriptor.Func.
        BoundaryOutcome outcome = BoundaryExecutor.execute(
            driveA.boundaryOp().failurePolicy(), cell.descriptor(),
            BoundaryValueView.ofFunction(RETURNED_SIG), BoundaryContext.none(),
            cell.realization());
        check(outcome instanceof BoundaryOutcome.Fail,
            "the executed check rejects the (int)->int value across the declared "
                + "(int,int)->int return (M < N raises before any invocation); got "
                + outcome);
        if (outcome instanceof BoundaryOutcome.Fail failOutcome) {
            deal.semantic.ir.BoundaryFailure failure = failOutcome.failure();
            check(failure.policy() == FailurePolicyId.FUNCTION_SIGNATURE
                    && failure.code() == DiagnosticCode.E8010,
                "the executed failure record is the registry row's: policy "
                    + "FUNCTION_SIGNATURE, code E8010");
            check(("function signature mismatch: expected (int,int)->int, got "
                    + "(int)->int").equals(failure.message()),
                "the message instantiates the canonical template with expected "
                    + "(int,int)->int and actual (int)->int; got [" + failure.message()
                    + "]");
            check("(int,int)->int".equals(failure.expected()),
                "the expected field is the declared (a:int,b:int)=>int descriptor");
            check("(int)->int".equals(failure.actual()),
                "the actual field is the returned (int)=>int signature");
            check(failure.metadata().isEmpty() && failure.cause() == null,
                "the record carries no metadata and no cause");
            // The message matches the registry row's pinned template
            // instantiation (the registry row is the expected pin; the
            // check itself was executed by the executor).
            check(failure.message().equals(FailureContractRegistry
                    .row(FailurePolicyId.FUNCTION_SIGNATURE).template()
                    .replace("{expected}", "(int,int)->int")
                    .replace("{actual}", "(int)->int")),
                "the executed message equals the registry template instantiation "
                    + "(the row is the expected pin, never the executed check)");
        }

        // The failure origin is the return boundary op: the op named by
        // the RETURN payload's returnBoundaryOpId.
        KindPayload.ReturnPayload returnPayload =
            (KindPayload.ReturnPayload) driveA.returnOp().payload();
        check(returnPayload.returnBoundaryOpId().equals(driveA.boundaryOp().opId()),
            "the failing boundary op is exactly the op the RETURN payload names as "
                + "its return boundary (the failure origin is the return boundary "
                + "op)");
        check(driveA.boundaryOp().origin().parentOpId() != null
                && driveA.boundaryOp().origin().parentOpId().equals(driveA.returnOp().opId()),
            "the return boundary op is the RETURN op's child (D13: RETURN runs the "
                + "single return boundary)");

        // Ordering evidence: the rejection is raised at the return
        // boundary before any invocation of the returned identity.
        check(driveA.returnedIdentity().equals(cell.input()),
            "the returned function identity flows directly into the return "
                + "boundary slot (the boundary op's input is the identity itself — "
                + "no adapter intervenes)");
        check(driveA.returnedIdentity().equals(returnPayload.value()),
            "the RETURN payload's value is the returned function identity");
        List<SemanticOp> invocations = invocationOps(driveA.unit().ops());
        check(invocations.size() == 1,
            "the drive unit carries exactly one invocation op (the enclosing "
                + "CALL(DIRECT) of the declared function); got " + invocations.size());
        boolean returnedInvoked = false;
        for (SemanticOp invocation : invocations) {
            if (invocation.payload() instanceof KindPayload.CallPayload callPayload
                    && callPayload.callee() instanceof KindPayload.CallCallee.Indirect
                        indirect
                    && indirect.callee().equals(driveA.returnedIdentity())) {
                returnedInvoked = true;
            }
            check(!invocation.operands().contains(driveA.returnedIdentity()),
                "no invocation op carries the returned identity as an operand");
        }
        check(!returnedInvoked,
            "no CALL/CALLBACK_INVOKE/ASYNC_START op resolves the returned function "
                + "identity — the returned function is never invoked, so the E8010 "
                + "rejection at the return boundary precedes any invocation");
        for (SemanticOp invocation : invocations) {
            check(!(invocation.payload() instanceof KindPayload.CallPayload callPayload
                    && callPayload.callee() instanceof KindPayload.CallCallee.Static
                        staticCallee
                    && staticCallee.binding()
                        instanceof FunctionExecutionBinding.AdapterBinding),
                "no invocation op of the drive resolves an AdapterBinding (the "
                    + "enclosing CALL(DIRECT) resolves the declared function's "
                    + "LoweredBody — the adapter is never invoked)");
        }
        check(ofKind(driveA.unit().ops(), SemanticOpKind.CALLBACK_INVOKE).isEmpty()
                && ofKind(driveA.unit().ops(), SemanticOpKind.ASYNC_START).isEmpty(),
            "the drive unit carries no CALLBACK_INVOKE/ASYNC_START op at all");
        // The returned closure's body block has no executed op member in
        // the drive unit: the only unit references to the returned body
        // block are the CLOSURE_NEW's LoweredBody registration and the
        // registry entry — no op executes that block in the flow, so its
        // body ops never execute before the boundary rejection.
        check(driveA.returnedBodyBlock() != null,
            "the returned closure's LoweredBody names its body block");
        boolean returnedBodyExecuted = false;
        for (SemanticOp op : driveA.unit().ops()) {
            if (op.payload() instanceof KindPayload.ClosureNewPayload closure
                    && closure.binding().blockId().equals(driveA.returnedBodyBlock())) {
                returnedBodyExecuted = true;
            }
        }
        check(returnedBodyExecuted,
            "the unit carries the CLOSURE_NEW LoweredBody registration of the "
                + "returned body block but no executed op of that block — its body "
                + "ops never execute before the boundary rejection");

        // --- Drive unit B: the negative control (exact-signature value). ---
        DriveUnit driveB = driveUnit(DECLARED_SIG, DECLARED_SIG);
        check(SemanticIrValidator.validate(driveB.unit(), driveB.facts()).isEmpty(),
            "the negative-control drive unit validates");
        check(ofKind(driveB.unit().ops(), SemanticOpKind.FUNCTION_ADAPT).isEmpty(),
            "the negative-control drive unit carries zero FUNCTION_ADAPT ops");
        KindPayload.BoundaryPayload exactCell =
            (KindPayload.BoundaryPayload) driveB.boundaryOp().payload();
        BoundaryValueView exactView = BoundaryValueView.ofFunction(DECLARED_SIG);
        BoundaryOutcome exactOutcome = BoundaryExecutor.execute(
            driveB.boundaryOp().failurePolicy(), exactCell.descriptor(), exactView,
            BoundaryContext.none(), exactCell.realization());
        check(exactOutcome instanceof BoundaryOutcome.Pass pass
                && pass.value() == exactView,
            "the negative control: the same executed check with an exact-signature "
                + "(int,int)->int value passes with the same value — a comparator "
                + "that always fails, or one that wrongly accepts M < N, fails this "
                + "test");

        // The drive is the executed check, never the retained fixture
        // alone: the boundary op was built over the pinned schema from
        // the pinned descriptors, validated, and executed cell-by-cell.
        check(driveA.boundaryOp().kind() == SemanticOpKind.BOUNDARY
                && driveA.boundaryOp().failurePolicy()
                    == FailurePolicyId.FUNCTION_SIGNATURE,
            "the drive executed the BOUNDARY op's FUNCTION_SIGNATURE cell "
                + "cell-by-cell through BoundaryExecutor");
    }

    /** One drive unit: the pinned return shape over the pinned schema records. */
    private record DriveUnit(LoweredModuleUnit unit,
                             SemanticIrValidator.ComparisonFacts facts,
                             ValueId returnedIdentity, SemanticOp boundaryOp,
                             SemanticOp returnOp, BlockId returnedBodyBlock) {
    }

    /** The module of the drive units (schema-validated, corpus-independent). */
    private static final ModuleId DRIVE_MOD = new ModuleId("mod.drive");
    private static final String DRIVE_IFACE = "interface-digest-drive";
    private static final String DRIVE_REGISTRY = "capability-registry-hash-drive";
    private static final SemanticIrValidator.ComparisonFacts DRIVE_FACTS =
        new SemanticIrValidator.ComparisonFacts(DRIVE_IFACE,
            SemanticProfile.DEAL_V1_2_INT32, DRIVE_REGISTRY);

    private static int driveOp = 1;
    private static int driveVal = 1;

    /**
     * Builds the pinned-return-shape drive unit over the pinned
     * {@code deal.semantic-ir/1} schema records: a {@code CLOSURE_NEW}
     * producing the returned function identity ({@code returnedSignature})
     * with its registered {@code LoweredBody}; the {@code RETURN} op
     * whose value is that identity and whose payload names the return
     * boundary op; the {@code FUNCTION_RETURN} {@code BOUNDARY} op
     * checking the declared function descriptor ({@code declaredSignature})
     * under {@code FUNCTION_SIGNATURE} with
     * {@code RuntimeValidation("return-check")}, whose direct input is the
     * returned identity; and the enclosing {@code CALL(DIRECT)} of the
     * declared function. Zero {@code FUNCTION_ADAPT} ops.
     */
    private static DriveUnit driveUnit(RuntimeDescriptor.Func returnedSignature,
                                       RuntimeDescriptor.Func declaredSignature) {
        OpId closureOp = new OpId(DRIVE_MOD, driveOp++);
        OpId returnOpId = new OpId(DRIVE_MOD, driveOp++);
        OpId boundaryOpId = new OpId(DRIVE_MOD, driveOp++);
        OpId callOpId = new OpId(DRIVE_MOD, driveOp++);
        ValueId returnedIdentity = new ValueId(driveVal++);
        BlockId returnedBody = new BlockId(driveOp++);
        FunctionId returnedFunction = new FunctionId(driveOp++);
        BlockId declaredBody = new BlockId(driveOp++);
        FunctionId declaredFunction = new FunctionId(driveOp++);

        List<SemanticOp> ops = new ArrayList<>();
        ops.add(driveOpWith(closureOp, SemanticOpKind.CLOSURE_NEW,
            new KindPayload.ClosureNewPayload(returnedFunction, returnedSignature, List.of(),
                new FunctionExecutionBinding.LoweredBody(returnedFunction, returnedBody)),
            returnedIdentity, returnedSignature, List.of(), List.of(),
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(driveOpWith(boundaryOpId, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN,
                declaredSignature, returnedIdentity,
                new BoundaryRealization.RuntimeValidation("return-check")),
            null, null, List.of(returnedIdentity), List.of(returnedSignature),
            FailurePolicyId.FUNCTION_SIGNATURE, returnOpId));
        ops.add(driveOpWith(returnOpId, SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(returnedIdentity, returnedFunction, callOpId,
                boundaryOpId),
            null, null, List.of(returnedIdentity), List.of(returnedSignature),
            FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(driveOpWith(callOpId, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.DIRECT,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(declaredFunction,
                        declaredBody)),
                new RuntimeDescriptor.Func(List.of(), declaredSignature),
                List.of(), boundaryOpId, null, declaredBody, null),
            new ValueId(driveVal++), null, List.of(), List.of(),
            FailurePolicyId.NO_DEAL_FAILURE, null));

        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>();
        bindings.put(new FunctionAllocationIdentity(returnedIdentity.id()),
            new FunctionExecutionBinding.LoweredBody(returnedFunction, returnedBody));
        LoweredModuleUnit unit = new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, DRIVE_MOD, DRIVE_IFACE,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, DRIVE_REGISTRY),
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            bindings, ops);
        SemanticOp boundaryOp = opOf(ops, boundaryOpId);
        SemanticOp returnOp = opOf(ops, returnOpId);
        return new DriveUnit(unit, DRIVE_FACTS, returnedIdentity, boundaryOp, returnOp,
            returnedBody);
    }

    /** Builds one drive-unit op over the pinned schema (test construction only). */
    private static SemanticOp driveOpWith(OpId id, SemanticOpKind kind, KindPayload payload,
                                          SemanticValue result, OpResultType resultType,
                                          List<ValueId> operands,
                                          List<RuntimeDescriptor> operandTypes,
                                          FailurePolicyId policy, OpId parent) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, operandTypes, selector,
            payload, policy, List.of(), "placeholder");
        contract = new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(),
            ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(id, kind,
            new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
                SourceOriginKind.SYNTHETIC, new AnchorId(0), parent),
            result, resultType, operands, operandTypes, payload, policy, contract);
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Bindings Integration Verification (ISSUE-0452, "
            + "sequencing item 9) ===\n");

        testCorpusLowersThroughTheCompletePipeline();
        testExactSignaturePositionsStoreDirectly();
        testSharedCellInitializerAndAssignmentPositions();
        testReevaluateThunkCompositeAndCallResultSources();
        testHostExternalImportReadsThroughRegistrySeam();
        testValueOverFunctionExpression();
        testValueOverProvedBinding();
        testBoundaryPositionsNeverAdapt();
        testCreationWiring();
        testRegistryUniqueness();
        testCellKindIff();
        testNoAdapterInvocation();
        testExecutedReturnBoundaryE8010Drive();

        System.out.println("\nBindings integration verification: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
