package deal.test;

import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
import deal.ast.CallExpr;
import deal.ast.ExpressionNode;
import deal.ast.IdentifierExpr;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.MemberAccessExpr;
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
import deal.semantic.AdapterShapeMap;
import deal.semantic.AdapterThunkConstruction;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The shape-map child's tests (ISSUE-0450 sequencing item 7): the
 * closed mode shape map (B7) and per-mode capture-mode payload
 * construction (B8), with every {@code FUNCTION_ADAPT} op emitted from
 * birth carrying its closed-map mode and payload — wired as the direct
 * input of exactly the adapted position's own
 * {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT} boundary
 * chain, fresh stable adapter identities, {@code AdapterBinding}
 * registration through the registry child's seam, the host/external
 * import-read arm pinned through the registry child's materialization
 * seam (T4), and the final cell-kind derivation completing the closed
 * B2 iff. Driven through the child's public lowering entry point
 * ({@link SemanticLowerer#lowerModuleShapeMapCore}) — the group-core
 * walk with the creation-rule classification, the proof analysis, and
 * the shape-map production active.
 *
 * <p><b>Coverage.</b></p>
 * <ul>
 *   <li>the closed map: a plain reassignable binding source →
 *       {@code SHARED_CELL} with {@code SharedCell} naming the dominant
 *       {@code {binding, generation}}; a proved binding source →
 *       {@code VALUE} over the single proved load with the proof
 *       present naming that binding/generation; a function-expression
 *       source → {@code VALUE} over the {@code CLOSURE_NEW} result; an
 *       intrinsic source → {@code VALUE} over the intrinsic
 *       function-value identity; call-result/member-read/conditional/
 *       conversion sources → {@code REEVALUATE_THUNK} (the closed
 *       non-identifier arm — classified at the checker-fact level and
 *       wrapped at the IR level);</li>
 *   <li>the host/external import read → {@code REEVALUATE_THUNK} (no
 *       VALUE) — exercised through the registry child's materialization
 *       seam: the seam's producer facts for the member-read op feed the
 *       map and the thunk wraps the IR-level member-read op (combined
 *       with T4 — fails if the seam breaks);</li>
 *   <li>emission from birth: every {@code FUNCTION_ADAPT} op the child
 *       produces carries its closed-map mode and per-mode payload (one
 *       adapter per {@code ADAPT}-classified position; no provisional
 *       or non-map mode exists);</li>
 *   <li>zero evaluation at creation: SHARED_CELL and REEVALUATE_THUNK
 *       positions contain no source evaluation in the creation flow —
 *       the source ops appear only inside the thunk block for
 *       REEVALUATE_THUNK and no {@code BINDING_LOAD} of the shared
 *       binding precedes the adapter for SHARED_CELL; VALUE's operand
 *       appears exactly once in the unit as the adapter's operand;</li>
 *   <li>identity: two adaptation positions produce two distinct
 *       adapter allocation identities, each with exactly one
 *       registered {@code AdapterBinding}; loads preserve the adapter
 *       identity (the {@code FunctionAllocationIdentity} contract);</li>
 *   <li>wiring: every adapter result is the direct input of exactly
 *       its own position's {@code VARIABLE_DECLARATION}/
 *       {@code VARIABLE_ASSIGNMENT} boundary chain and of no other
 *       {@code BOUNDARY} op; adapter creation emits zero
 *       {@code BOUNDARY} ops (the adapter adds no second boundary —
 *       the N target-signature parameter-boundary checks belong to the
 *       invoking op, E7);</li>
 *   <li>cell-kind iff across all three capture kinds: a
 *       closure-captured incarnation {@code SHARED_CELL} (closure
 *       child), a thunk-captured incarnation {@code SHARED_CELL}, a
 *       SHARED_CELL-adapter-referenced incarnation
 *       {@code SHARED_CELL}, an uncaptured incarnation
 *       {@code DIRECT}, a VALUE-adapted proved binding stays
 *       {@code DIRECT} unless otherwise captured, the pinned special
 *       cases stay {@code SHARED_CELL}, and the derivation never
 *       downgrades;</li>
 *   <li>negatives: a proof-less binding never receives VALUE; the
 *       mode-selection seam accepts checker facts only (no
 *       target/route/emitter input in its interface);</li>
 *   <li>combined: a corpus covering all three modes using the
 *       binding-core generations, the closure child's function values,
 *       the registry child's registration and seam, the proof child's
 *       records, and the creation-rule child's classification/wiring —
 *       any break in an earlier module fails the corpus — plus
 *       byte-identical repeated lowering.</li>
 * </ul>
 *
 * <p>No invocation execution is built or verified here: generation-
 * checked loads, thunk re-execution with {@code ADAPTER_THUNK_STEP}
 * children, source-signature checks, the N-argument projection with
 * trailing drop, and the per-source-kind single return boundary are
 * E7's (ISSUE-0236); the payloads this child builds are the exact
 * inputs E7's protocol consumes.</p>
 */
public class AdapterShapeMapPayloadTest {

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

    private static final RuntimeDescriptor.Func INT_TO_NULL = new RuntimeDescriptor.Func(
        List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Null.INSTANCE);
    private static final RuntimeDescriptor.Func INT_INT_TO_NULL = new RuntimeDescriptor.Func(
        List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
        RuntimeDescriptor.Null.INSTANCE);

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

    private static SemanticLowerer.ShapeMapCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleShapeMapCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /** A lowered-and-validated result for the named test, or null when broken. */
    private static SemanticLowerer.ShapeMapCoreResult loweredResult(String source,
                                                                    String what) {
        SemanticLowerer.ShapeMapCoreResult result = lowerSlice(source);
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

    /** The produced FUNCTION_ADAPT ops in unit order. */
    private static List<SemanticOp> adaptersOf(List<SemanticOp> ops) {
        return ofKind(ops, SemanticOpKind.FUNCTION_ADAPT);
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

    /** The unit op with the given op id. */
    private static SemanticOp opOf(List<SemanticOp> ops, OpId opId) {
        for (SemanticOp op : ops) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        fail("op " + opId + " not found in the produced op list");
        return null;
    }

    /** The BINDING_LOAD op naming exactly the given {binding, generation}. */
    private static SemanticOp loadOf(List<SemanticOp> ops, BindingId binding, long generation) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_LOAD
                    && op.payload() instanceof KindPayload.BindingLoadPayload payload
                    && payload.binding().equals(binding)
                    && payload.generation() == generation) {
                matches.add(op);
            }
        }
        return matches.isEmpty() ? null : matches.get(0);
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

    /** The first op index in the unit op list (identity by op id). */
    private static int indexOf(List<SemanticOp> ops, OpId opId) {
        for (int i = 0; i < ops.size(); i++) {
            if (ops.get(i).opId().equals(opId)) {
                return i;
            }
        }
        return -1;
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

    /** The created block-membership record of the thunk block (op order). */
    private static List<SemanticOp> blockOpsOf(StructuredBodyTable table, BlockId block,
                                               List<SemanticOp> ops) {
        List<OpId> ids = table.blockOps().get(block);
        if (ids == null) {
            fail("the produced table records the thunk block " + block);
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

    /** The recorded wiring target of the adapter with the given identity. */
    private static OpId emissionWiringTargetOf(SemanticLowerer.ShapeMapCoreResult result,
                                               ValueId adapterIdentity) {
        for (SemanticLowerer.AdapterEmission emission : result.shapeMapFacts().emissions()) {
            if (emission.adapterIdentity().equals(adapterIdentity)) {
                return emission.wiringTargetOpId();
            }
        }
        fail("no emission fact records the adapter identity " + adapterIdentity);
        return null;
    }

    /** The single FUNCTION_ADAPT payload of the op. */
    private static KindPayload.FunctionAdaptPayload adaptPayload(SemanticOp op) {
        if (op == null || !(op.payload() instanceof KindPayload.FunctionAdaptPayload payload)) {
            fail("expected a FUNCTION_ADAPT op carrying its FunctionAdaptPayload");
            return null;
        }
        return payload;
    }

    // =========================================================================
    // The mode map (B7) and payload construction (B8)
    // =========================================================================

    /**
     * A plain reassignable binding source: the map's SHARED_CELL arm —
     * an assignment in the enclosing scope defeated the source
     * binding's proof, so the adaptation is SHARED_CELL over
     * {@code SharedCell {binding, generation}} naming the dominant
     * incarnation, zero operands, zero evaluation at creation, and the
     * shared incarnation joins the B2 derivation (SHARED_CELL).
     */
    static void testSharedCellBindingWithoutProof() {
        System.out.println("-- SHARED_CELL: proof-less binding source, zero evaluation --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let f: (x: int) => null = inner;
              f = f;
              let h: (a: int, b: int) => null = f;
            }
            """, "the SHARED_CELL slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding h = fact(result.bindingFacts(), "h");
        if (f == null || h == null) {
            return;
        }

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 1,
            "exactly one FUNCTION_ADAPT op (h's position — f = f is exact); got "
                + adapters.size());
        if (adapters.size() != 1) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(adapters.get(0));
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.SHARED_CELL,
            "the adapter's mode is SHARED_CELL (a proof-less binding source — B7)");
        check(payload.source() instanceof AdaptSourceRef.SharedCell shared
                && shared.binding().equals(f.binding()) && shared.generation() == 0,
            "the source is SharedCell naming the dominant {binding, generation} = {f, 0}");
        check(adapters.get(0).operands().isEmpty() && payload.proof() == null,
            "zero operands, zero loads, no proof at creation (B8 SHARED_CELL)");

        // Zero evaluation: no op between h's ALLOC and the adapter (no
        // BINDING_LOAD of f precedes the adapter in the creation flow).
        SemanticOp hAlloc = allocOf(ops, h.binding(), 0);
        check(hAlloc != null, "h's BINDING_ALLOC exists");
        if (hAlloc != null) {
            int allocIndex = indexOf(ops, hAlloc.opId());
            int adaptIndex = indexOf(ops, adapters.get(0).opId());
            check(adaptIndex == allocIndex + 1,
                "the adapter directly follows h's ALLOC — zero evaluation between them; "
                    + "got alloc@" + allocIndex + " adapt@" + adaptIndex);
        }
        // The only BINDING_LOAD of f is the `f = f` chain's RHS load
        // (a different position's flow — this position evaluated nothing).
        List<SemanticOp> loads = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_LOAD
                    && op.payload() instanceof KindPayload.BindingLoadPayload loadPayload
                    && loadPayload.binding().equals(f.binding())) {
                loads.add(op);
            }
        }
        check(loads.size() == 1,
            "exactly one BINDING_LOAD of f exists (the `f = f` RHS load); got "
                + loads.size());

        // The boundary observes the exact-signature adapter value; the
        // INIT commits the adapter identity. (f's own exact-store
        // declaration boundary also exists — the assertion targets h's
        // boundary through the wiring target.)
        SemanticOp hBoundary = null;
        for (SemanticOp op : boundariesOfKind(ops, BoundaryKind.VARIABLE_DECLARATION)) {
            if (op.payload() instanceof KindPayload.BoundaryPayload boundary
                    && boundary.input().equals(adapters.get(0).result())) {
                hBoundary = op;
            }
        }
        check(hBoundary != null,
            "the VARIABLE_DECLARATION boundary's input is the adapter identity "
                + "(exact-signature pass-through)");
        check(hBoundary != null
                && ((KindPayload.BoundaryPayload) hBoundary.payload()).descriptor()
                    .equals(payload.targetSignature()),
            "the declaration boundary checks the target signature "
                + payload.targetSignature().canonicalSpecText());
        SemanticOp init = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload initPayload
                    && initPayload.binding().equals(h.binding())) {
                init = op;
            }
        }
        check(init != null && ((KindPayload.BindingInitPayload) init.payload()).value()
                .equals(adapters.get(0).result()),
            "h's BINDING_INIT commits the adapter identity");

        // The SharedCell arm upgrades f's incarnation to SHARED_CELL (B2).
        check(f.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "f's incarnation is SHARED_CELL (the FUNCTION_ADAPT(SHARED_CELL) SharedCell "
                + "source reference is a capture reference)");
        SemanticOp fAlloc = allocOf(ops, f.binding(), 0);
        check(fAlloc != null
                && ((KindPayload.BindingAllocPayload) fAlloc.payload()).cellKind()
                    == BindingCellKind.SHARED_CELL,
            "f's BINDING_ALLOC payload carries the final SHARED_CELL kind");

        // The registry: the adapter identity registers one AdapterBinding.
        FunctionExecutionBinding binding =
            unit.functionBindings().get(new FunctionAllocationIdentity(
                ((ValueId) adapters.get(0).result()).id()));
        check(binding instanceof FunctionExecutionBinding.AdapterBinding adapterBinding
                && adapterBinding.adaptOpId().equals(adapters.get(0).opId())
                && adapterBinding.captureMode() == CaptureMode.SHARED_CELL
                && adapterBinding.sourceRef().equals(payload.source())
                && adapterBinding.sourceSignature().equals(payload.sourceSignature())
                && adapterBinding.targetSignature().equals(payload.targetSignature()),
            "the registry holds the AdapterBinding {adaptOpId, SHARED_CELL, SharedCell, "
                + "signatures} keyed by the adapter identity");
    }

    /**
     * A proved binding source: the map's VALUE-over-binding arm — the
     * single proved BINDING_LOAD at the proof's generation is the
     * operand, the proof is present naming that {binding, generation},
     * the load's result is the retained function identity, and the
     * proven binding stays DIRECT (the VALUE operand load is not a
     * capture reference — B2).
     */
    static void testValueOverProvedBindingLoad() {
        System.out.println("-- VALUE: proved binding over the single proved load --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
            }
            """, "the VALUE-over-binding slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        if (f == null || g == null) {
            return;
        }

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 1,
            "exactly one FUNCTION_ADAPT op (g's position); got " + adapters.size());
        if (adapters.size() != 1) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(adapters.get(0));
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.VALUE,
            "the adapter's mode is VALUE (a proved binding source — B7)");
        check(payload.proof() != null
                && payload.proof().binding().equals(f.binding())
                && payload.proof().generation() == 0,
            "the payload's proof names the loaded {binding, generation} = {f, 0}");
        check(payload.source() instanceof AdaptSourceRef.Value value
                && value.value().equals(adapters.get(0).operands().get(0)),
            "the source is Value{operand} — the single proved load's result");
        check(adapters.get(0).operands().size() == 1
                && adapters.get(0).operandTypes().equals(List.of(INT_TO_NULL)),
            "exactly one operand with the source signature (int)->null");

        // The operand is the single BINDING_LOAD at the proof's
        // generation; loads preserve the allocation identity (the load
        // publishes inner's CLOSURE_NEW identity).
        SemanticOp load = loadOf(ops, f.binding(), 0);
        check(load != null, "the single BINDING_LOAD of {f, 0} exists");
        if (load == null) {
            return;
        }
        ValueId operand = (ValueId) adapters.get(0).operands().get(0);
        check(operand.equals(load.result()),
            "the adapter's operand is the proved load's result (identity preservation)");
        check(ofKind(ops, SemanticOpKind.CLOSURE_NEW).stream()
                .anyMatch(op -> op.result().equals(operand)),
            "the load result is the CLOSURE_NEW allocation identity of the function "
                + "the cell holds");
        // The operand appears exactly once in the unit as the adapter's
        // operand (VALUE exactly-once).
        check(operandConsumers(ops, operand) == 1,
            "the VALUE operand appears exactly once in the unit as the adapter's operand");

        // VALUE's operand load is not a capture reference: f stays
        // DIRECT (no closure/thunk/SharedCell capture resolves to it).
        check(f.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "the VALUE-adapted proved binding f stays DIRECT (the operand load is not "
                + "a capture reference)");
        check(g.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "the adapted target g stays DIRECT (uncaptured)");

        // The registry registration agrees.
        FunctionExecutionBinding binding =
            unit.functionBindings().get(new FunctionAllocationIdentity(
                ((ValueId) adapters.get(0).result()).id()));
        check(binding instanceof FunctionExecutionBinding.AdapterBinding adapterBinding
                && adapterBinding.captureMode() == CaptureMode.VALUE
                && adapterBinding.sourceSignature().equals(INT_TO_NULL)
                && adapterBinding.targetSignature().equals(INT_INT_TO_NULL),
            "the AdapterBinding carries {VALUE, (int)->null, (int,int)->null}");
    }

    /**
     * A function-expression source: the map's VALUE arm over the
     * CLOSURE_NEW result — the operand is the expression's allocation
     * identity, no proof, exactly one operand, and the
     * creation-side CLOSURE_NEW evaluates exactly once at creation.
     */
    static void testValueOverFunctionExpression() {
        System.out.println("-- VALUE: function expression over the CLOSURE_NEW result --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult("""
            function main(): null {
              let m: (a: int, b: int) => null = function(x: int): null {};
            }
            """, "the VALUE-over-expression slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 1,
            "exactly one FUNCTION_ADAPT op; got " + adapters.size());
        if (adapters.size() != 1) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(adapters.get(0));
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.VALUE,
            "the adapter's mode is VALUE (a materialized function-expression operand)");
        check(payload.proof() == null,
            "no proof is recorded — the operand is a CLOSURE_NEW result, not a "
                + "binding load (B8)");
        check(payload.source() instanceof AdaptSourceRef.Value value
                && value.value().equals(adapters.get(0).operands().get(0)),
            "the source is Value{operand} — the CLOSURE_NEW result");
        check(adapters.get(0).operands().size() == 1
                && adapters.get(0).operandTypes().equals(List.of(INT_TO_NULL)),
            "exactly one operand with the expression's signature (int)->null");

        // The operand is the expression's CLOSURE_NEW result.
        ValueId operand = (ValueId) adapters.get(0).operands().get(0);
        List<SemanticOp> closures = ofKind(ops, SemanticOpKind.CLOSURE_NEW);
        check(closures.size() == 2,
            "two CLOSURE_NEW ops (main + the expression); got " + closures.size());
        int matching = 0;
        for (SemanticOp closure : closures) {
            if (closure.result().equals(operand)) {
                matching++;
            }
        }
        check(matching == 1,
            "exactly one CLOSURE_NEW publishes the operand identity (the expression's)");
        check(operandConsumers(ops, operand) == 1,
            "the VALUE operand appears exactly once in the unit as the adapter's operand");
    }

    /**
     * An intrinsic source: the map's VALUE arm over the first-class
     * intrinsic function value — the operand is the intrinsic
     * binding's seeded identity, no load of the intrinsic binding is
     * emitted (a first-class intrinsic value has no closed
     * FunctionExecutionBinding shape — B5), and no proof enters the
     * payload (the operand is not a binding load).
     */
    static void testValueOverIntrinsic() {
        System.out.println("-- VALUE: intrinsic int first-class function value --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult("""
            function main(): null {
              let n: (a: number, b: number) => int = int;
            }
            """, "the VALUE-over-intrinsic slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding intBinding = fact(result.bindingFacts(), "int");
        if (intBinding == null) {
            return;
        }

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 1,
            "exactly one FUNCTION_ADAPT op; got " + adapters.size());
        if (adapters.size() != 1) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(adapters.get(0));
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.VALUE,
            "the adapter's mode is VALUE (a first-class intrinsic function value — B7)");
        check(payload.proof() == null,
            "no proof enters the payload — the operand is the intrinsic identity, not "
                + "a binding load (B8)");
        check(adapters.get(0).operands().size() == 1
                && adapters.get(0).operandTypes().size() == 1
                && adapters.get(0).operandTypes().get(0)
                    instanceof RuntimeDescriptor.Func source
                && source.paramTypes().equals(List.of(RuntimeDescriptor.Number.INSTANCE))
                && source.returnType().equals(RuntimeDescriptor.Int.INSTANCE),
            "the operand type is the intrinsic's signature (number)->int");

        // The operand is the intrinsic binding's seeded identity (the
        // INIT operand at module-init top).
        SemanticOp intInit = null;
        for (SemanticOp op : ofKind(ops, SemanticOpKind.BINDING_INIT)) {
            if (op.payload() instanceof KindPayload.BindingInitPayload initPayload
                    && initPayload.binding().equals(intBinding.binding())) {
                intInit = op;
            }
        }
        check(intInit != null, "the intrinsic binding's BINDING_INIT exists");
        if (intInit == null) {
            return;
        }
        ValueId intrinsicIdentity =
            ((KindPayload.BindingInitPayload) intInit.payload()).value();
        check(intrinsicIdentity.equals(adapters.get(0).operands().get(0)),
            "the adapter's operand is the intrinsic binding's seeded function-value "
                + "identity");
        check(loadOf(ops, intBinding.binding(), 0) == null,
            "zero BINDING_LOAD of the intrinsic binding exists (no function-typed "
                + "load of a first-class intrinsic is emitted — B5)");
    }

    /**
     * The closed non-identifier arm: a call-result source, a
     * member-read source, a conditional source, and a conversion
     * source all classify {@code NON_IDENTIFIER_EXPRESSION} and map to
     * REEVALUATE_THUNK (no VALUE carve-out for any composite source).
     * The checked-slice halves run the checker-admitted positions
     * (call-result and member-read arity-extension initializers) — the
     * map classifies them from checker facts; the AST-shape halves
     * classify the conditional (`&&` binary) and conversion
     * (intrinsic-call) node shapes (a function-typed conditional/
     * conversion value cannot arise from checked v1.2 source — the
     * closed map still assigns the arm, so the arm assignment is the
     * total-map property).
     */
    static void testCompositeSourcesMapToReevaluateThunk() {
        System.out.println("-- REEVALUATE_THUNK: call/member-read/conditional/conversion "
            + "sources (closed non-identifier arm) --");

        // The checker-admitted call-result position: picker() returns
        // (x:int)=>null into (a:int,b:int)=>null — ADAPT by the creation
        // rule; the map's arm is the closed non-identifier arm.
        CheckedSlice callSlice = checkSlice("""
            function picker(): (x: int) => null {
              let f: (x: int) => null = inner;
              return f;
            }
            function inner(x: int): null {}
            function main(): null {
              let h: (a: int, b: int) => null = picker();
            }
            """);
        if (callSlice == null) {
            return;
        }
        ExpressionNode callSource = null;
        for (deal.ast.StatementNode statement : callSlice.program().statements()) {
            if (statement instanceof deal.ast.FunctionDeclaration function
                    && "main".equals(function.name())
                    && function.body().statements().get(0)
                        instanceof deal.ast.VariableDeclaration declaration) {
                callSource = declaration.initializer();
            }
        }
        check(callSource instanceof CallExpr,
            "the call-result source is the CallExpr picker()");
        if (callSource != null) {
            AdapterShapeMap.SourceShape shape = AdapterShapeMap.sourceShapeOf(callSource,
                name -> callSlice.checks().symbolTable().resolve(name));
            check(shape == AdapterShapeMap.SourceShape.NON_IDENTIFIER_EXPRESSION,
                "a call-result source classifies NON_IDENTIFIER_EXPRESSION");
            check(AdapterShapeMap.selectMode(shape, Optional.empty())
                    == CaptureMode.REEVALUATE_THUNK,
                "a call-result source maps to REEVALUATE_THUNK (the closed "
                    + "non-identifier arm)");
            check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.CALL,
                    Optional.empty()) == CaptureMode.REEVALUATE_THUNK,
                "the produced-source map maps a CALL result to REEVALUATE_THUNK");
        }

        // The checker-admitted member-read position: t.pick with type
        // (x:int)=>null into (a:int,b:int)=>null.
        CheckedSlice memberSlice = checkSlice("""
            function inner(x: int): null {}
            function main(): null {
              let t = { pick: inner };
              let h: (a: int, b: int) => null = t.pick;
            }
            """);
        if (memberSlice == null) {
            return;
        }
        ExpressionNode memberSource = null;
        for (deal.ast.StatementNode statement : memberSlice.program().statements()) {
            if (statement instanceof deal.ast.FunctionDeclaration function
                    && "main".equals(function.name())
                    && function.body().statements().get(1)
                        instanceof deal.ast.VariableDeclaration declaration) {
                memberSource = declaration.initializer();
            }
        }
        check(memberSource instanceof MemberAccessExpr,
            "the member-read source is the MemberAccessExpr t.pick");
        if (memberSource != null) {
            AdapterShapeMap.SourceShape shape = AdapterShapeMap.sourceShapeOf(memberSource,
                name -> memberSlice.checks().symbolTable().resolve(name));
            check(shape == AdapterShapeMap.SourceShape.NON_IDENTIFIER_EXPRESSION,
                "a member-read source classifies NON_IDENTIFIER_EXPRESSION");
            check(AdapterShapeMap.selectMode(shape, Optional.empty())
                    == CaptureMode.REEVALUATE_THUNK,
                "a member-read source maps to REEVALUATE_THUNK (the closed "
                    + "non-identifier arm)");
            check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.MEMBER_READ,
                    Optional.empty()) == CaptureMode.REEVALUATE_THUNK,
                "the produced-source map maps a MEMBER_READ result to REEVALUATE_THUNK");
        }

        // The conditional node shape (&&) — a composite source.
        BinaryExpr conditional = new BinaryExpr(null,
            new LiteralExpr(null, new LiteralValue.BooleanLiteral(false)),
            BinaryOp.AND, new LiteralExpr(null, new LiteralValue.BooleanLiteral(false)));
        AdapterShapeMap.SourceShape conditionalShape = AdapterShapeMap.sourceShapeOf(
            conditional, name -> null);
        check(conditionalShape == AdapterShapeMap.SourceShape.NON_IDENTIFIER_EXPRESSION,
            "a conditional (logical binary) source classifies NON_IDENTIFIER_EXPRESSION");
        check(AdapterShapeMap.selectMode(conditionalShape, Optional.empty())
                == CaptureMode.REEVALUATE_THUNK,
            "a conditional source maps to REEVALUATE_THUNK (the closed non-identifier "
                + "arm — the total map assigns the arm to every composite source)");

        // The conversion node shape (an intrinsic call expression) — a
        // composite source.
        CallExpr conversion = new CallExpr(null,
            new IdentifierExpr(null, "int"),
            List.of(new LiteralExpr(null, new LiteralValue.IntLiteral(1))));
        AdapterShapeMap.SourceShape conversionShape = AdapterShapeMap.sourceShapeOf(
            conversion, name -> null);
        check(conversionShape == AdapterShapeMap.SourceShape.NON_IDENTIFIER_EXPRESSION,
            "a conversion (intrinsic call) source classifies NON_IDENTIFIER_EXPRESSION");
        check(AdapterShapeMap.selectMode(conversionShape, Optional.empty())
                == CaptureMode.REEVALUATE_THUNK,
            "a conversion source maps to REEVALUATE_THUNK (the closed non-identifier "
                + "arm — the total map assigns the arm to every composite source)");
    }

    /**
     * The REEVALUATE_THUNK payload construction (B8): a source-level
     * composite (assignment-expression) position lowers one adapter
     * whose source is {@code Thunk {blockId, capturedBindings}} — the
     * thunk block wraps the source expression's ordered
     * source-lowering ops (the RHS load, the assignment boundary, the
     * store commit, and the ASSIGN chain op), the
     * {@code capturedBindings} pin the thunk's free bindings
     * generation-pinned in first-reference order (the assignment target
     * first, then the RHS reference), zero evaluation happens at the
     * creation site (the source ops live only inside the thunk block),
     * and the thunk-captured incarnation joins the B2 derivation
     * (SHARED_CELL).
     */
    static void testReevaluateThunkPayloadConstruction() {
        System.out.println("-- REEVALUATE_THUNK: thunk block wraps the ordered source "
            + "ops with generation-pinned captures --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult("""
            function inner(x: int): null {}
            function main(): null {
              let s: (x: int) => null = inner;
              let k: (a: int, b: int) => null = (s = inner);
            }
            """, "the REEVALUATE_THUNK assignment-expression slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding s = fact(result.bindingFacts(), "s");
        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding k = fact(result.bindingFacts(), "k");
        if (s == null || inner == null || k == null) {
            return;
        }

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 1,
            "exactly one FUNCTION_ADAPT op (k's position — s = inner inside k's "
                + "initializer is exact and unadapted); got " + adapters.size());
        if (adapters.size() != 1) {
            return;
        }
        KindPayload.FunctionAdaptPayload payload = adaptPayload(adapters.get(0));
        if (payload == null) {
            return;
        }
        check(payload.mode() == CaptureMode.REEVALUATE_THUNK,
            "the adapter's mode is REEVALUATE_THUNK (a non-identifier composite "
                + "source — B7)");
        check(adapters.get(0).operands().isEmpty() && payload.proof() == null,
            "zero operands, zero evaluation, no proof at creation (B8 "
                + "REEVALUATE_THUNK)");
        check(payload.source() instanceof AdaptSourceRef.Thunk thunk,
            "the source is a Thunk {BlockId, capturedBindings} record");
        if (!(payload.source() instanceof AdaptSourceRef.Thunk thunk)) {
            return;
        }
        check(thunk.capturedBindings().equals(List.of(
                new BindingGeneration(s.binding(), 0),
                new BindingGeneration(inner.binding(), 0))),
            "the capturedBindings pin [s, inner] — the thunk's free bindings, "
                + "generation-pinned, first-reference order (the assignment target "
                + "first, then the RHS reference); got "
                + thunk.capturedBindings());

        // Zero evaluation: no op between k's ALLOC and the adapter; the
        // source ops live only inside the thunk block.
        SemanticOp kAlloc = allocOf(ops, k.binding(), 0);
        check(kAlloc != null, "k's BINDING_ALLOC exists");
        if (kAlloc != null) {
            int allocIndex = indexOf(ops, kAlloc.opId());
            int adaptIndex = indexOf(ops, adapters.get(0).opId());
            check(adaptIndex == allocIndex + 1,
                "the adapter directly follows k's ALLOC — zero evaluation between them; "
                    + "got alloc@" + allocIndex + " adapt@" + adaptIndex);
        }
        check(result.lowering().table() != null, "the block-membership table is produced");
        if (result.lowering().table() == null) {
            return;
        }
        List<SemanticOp> thunkOps = blockOpsOf(result.lowering().table(), thunk.blockId(),
            ops);
        check(thunkOps.size() == 4,
            "the thunk block wraps the four ordered source ops [RHS load, "
                + "VARIABLE_ASSIGNMENT boundary, BINDING_STORE commit, ASSIGN]; got "
                + thunkOps.size());
        if (thunkOps.size() == 4) {
            check(thunkOps.get(0).kind() == SemanticOpKind.BINDING_LOAD
                    && thunkOps.get(0).payload()
                        instanceof KindPayload.BindingLoadPayload loadPayload
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
                    && thunkOps.get(2).payload()
                        instanceof KindPayload.BindingStorePayload store
                    && store.binding().equals(s.binding())
                    && store.generation() == 0,
                "the thunk's third op is the BINDING_STORE commit of {s, 0}");
            check(thunkOps.get(3).kind() == SemanticOpKind.ASSIGN
                    && thunkOps.get(3).payload() instanceof KindPayload.AssignPayload
                        chain
                    && chain.targetKind()
                        == deal.semantic.ir.AssignTargetKind.VARIABLE,
                "the thunk's fourth op is the inner ASSIGN chain op");
            check(thunkOps.get(3).result() != null
                    && thunkOps.get(3).resultType() instanceof RuntimeDescriptor.Func,
                "the inner ASSIGN produces the function-typed source value (the "
                    + "committed function identity)");
        }
        // The source ops are members of exactly the thunk block — no
        // source op exists in the creation flow outside it.
        check(result.lowering().table().opBlocks().get(thunkOps.get(0).opId())
                .equals(thunk.blockId()),
            "the source load's block membership is exactly the thunk block");

        // The thunk-captured incarnation joins the B2 derivation.
        check(s.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "the thunk-captured incarnation s is SHARED_CELL (the thunk capture arm "
                + "of B2)");
        SemanticOp sAlloc = allocOf(ops, s.binding(), 0);
        check(sAlloc != null
                && ((KindPayload.BindingAllocPayload) sAlloc.payload()).cellKind()
                    == BindingCellKind.SHARED_CELL,
            "s's BINDING_ALLOC payload carries the final SHARED_CELL kind");
    }

    /**
     * The host/external import-read arm, pinned through the registry
     * child's materialization seam (T4): the seam's producer facts for
     * the member-read op feed the map, the arm is the same closed
     * non-identifier arm — REEVALUATE_THUNK, no VALUE carve-out — and
     * the thunk builder wraps the IR-level member-read op over the
     * pinned {@code deal.semantic-ir/1} schema with the import-alias
     * receiver pinned as a generation-pinned capture (combined with T4
     * — fails if the seam breaks).
     */
    static void testHostExternalImportReadMapsToReevaluateThunk() {
        System.out.println("-- host/external import read: REEVALUATE_THUNK (no VALUE) "
            + "through the T4 materialization seam --");

        // The registry child's seam records the producer facts of the
        // host export read `host.g` (the member-read op materializes the
        // function value; this child produces no member-read op path —
        // the seam consumes the IR-level facts).
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(1001L);
        RuntimeDescriptor.Func exportDescriptor = INT_INT_TO_NULL;
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

        // The map over the produced source: the producer facts feed the
        // map; the arm is the closed non-identifier arm — no VALUE
        // carve-out for import reads even though the read materialized a
        // function value with a registry binding.
        CaptureMode mode = AdapterShapeMap.selectModeOverProducedSource(
            SemanticOpKind.MEMBER_READ, Optional.of(materialization));
        check(mode == CaptureMode.REEVALUATE_THUNK,
            "a host/external import read maps to REEVALUATE_THUNK with the producer "
                + "facts present (no VALUE carve-out for import reads)");
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.EXPORT_READ,
                Optional.of(materialization)) == CaptureMode.REEVALUATE_THUNK,
            "an export-read materialization maps to the same non-identifier arm");

        // The thunk wraps the IR-level member-read op (constructed over
        // the pinned schema — the producing op the values epic emits):
        // the receiver load of the import alias, then the MEMBER_READ.
        BlockId thunkBlock = new BlockId(7001L);
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
            hostValue, INT_INT_TO_NULL, List.of(aliasLoad),
            List.of(RuntimeDescriptor.Table.INSTANCE));
        AdaptSourceRef.Thunk thunk = AdapterThunkConstruction.buildThunk(thunkBlock,
            List.of(receiverLoad, memberRead), List.of(aliasCapture));
        check(thunk.blockId().equals(thunkBlock),
            "the thunk wraps the IR-level member-read op in the fresh block");
        check(thunk.capturedBindings().equals(List.of(aliasCapture)),
            "the thunk's capturedBindings pin the import-alias receiver {host, 0} — "
                + "generation-pinned, first-reference order");
        check(AdapterThunkConstruction.producedValueOf(List.of(receiverLoad, memberRead))
                .equals(hostValue),
            "the thunk's produced value is the member read's function-typed result");
        check(AdapterThunkConstruction.blockMembershipOf(thunkBlock,
                List.of(receiverLoad, memberRead))
                .get(thunkBlock).equals(List.of(receiverLoad.opId(), memberRead.opId())),
            "the IR-level block-membership record wraps the two ordered ops");
        // The same arm holds for a materialization the seam classifies
        // as a cross-module import (EXTERNAL_IMPORT) — the mode never
        // comes from target-derived facts.
        check(AdapterShapeMap.selectModeOverProducedSource(SemanticOpKind.MEMBER_READ,
                Optional.of(new FunctionBindingRegistry.FunctionValueMaterialization(
                    identity,
                    FunctionBindingRegistry.FunctionValueMaterializationSource.EXTERNAL_IMPORT,
                    new ModuleId("callee"), "g", exportDescriptor,
                    SemanticOpKind.MEMBER_READ, null)))
                == CaptureMode.REEVALUATE_THUNK,
            "an external-import materialization maps to the same closed non-identifier "
                + "arm (never a target-derived special case)");
    }

    /**
     * The thunk builder's IR-level surface over the pinned
     * {@code deal.semantic-ir/1} schema: a call-result source (a
     * {@code CALL} op whose result is a function value — the pinned
     * {@code jvm-fv-return-function-value} shape) wraps into a
     * {@code Thunk {BlockId, capturedBindings}} with the ordered
     * source-lowering op and generation-pinned captures, and the
     * builder fails closed on every malformed input (empty op list, a
     * non-function-typed produced value, a duplicate capture, a
     * duplicate op id) — never a silently invalid thunk.
     */
    static void testIrLevelThunkBuilderWrapsCallResultAndFailsClosed() {
        System.out.println("-- IR-level thunk builder: call-result wrap + fail-closed "
            + "negatives --");

        RuntimeDescriptor.Func sourceSignature = INT_TO_NULL;
        BlockId thunkBlock = new BlockId(8001L);
        ValueId calleeValue = new ValueId(8101L);
        ValueId callResult = new ValueId(8102L);
        BindingGeneration capture = new BindingGeneration(new BindingId(43L), 0);
        // The call-result source op: an indirect CALL whose return
        // value is a function (the pinned return-function-value shape).
        SemanticOp call = irValueOp(new OpId(MODULE, 8201L), SemanticOpKind.CALL,
            new KindPayload.CallPayload(deal.semantic.ir.CallMode.INDIRECT,
                new KindPayload.CallCallee.Indirect(calleeValue), INT_TO_NULL,
                List.of(), null, null, null, null),
            callResult, INT_TO_NULL, List.of(calleeValue), List.of(INT_TO_NULL));
        AdaptSourceRef.Thunk thunk = AdapterThunkConstruction.buildThunk(thunkBlock,
            List.of(call), List.of(capture));
        check(thunk.blockId().equals(thunkBlock)
                && thunk.capturedBindings().equals(List.of(capture)),
            "the call-result source wraps into Thunk {blockId, [capture]}");
        check(AdapterThunkConstruction.producedValueOf(List.of(call)).equals(callResult),
            "the thunk's produced value is the call's function-typed result");

        // Fail-closed negatives.
        boolean emptyRejected = false;
        try {
            AdapterThunkConstruction.buildThunk(new BlockId(8002L), List.of(), List.of());
        } catch (IllegalArgumentException expected) {
            emptyRejected = true;
        }
        check(emptyRejected, "an empty op list fails closed");

        boolean nonFunctionRejected = false;
        try {
            SemanticOp nonFunction = irValueOp(new OpId(MODULE, 8202L),
                SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new deal.semantic.ir.ScalarValue.Int(1)),
                new ValueId(8103L), RuntimeDescriptor.Int.INSTANCE, List.of(), List.of());
            AdapterThunkConstruction.buildThunk(new BlockId(8003L), List.of(nonFunction),
                List.of());
        } catch (IllegalArgumentException expected) {
            nonFunctionRejected = true;
        }
        check(nonFunctionRejected,
            "a non-function-typed produced value fails closed (the source is "
                + "function-typed)");

        boolean duplicateCaptureRejected = false;
        try {
            AdapterThunkConstruction.buildThunk(new BlockId(8004L), List.of(call),
                List.of(capture, capture));
        } catch (IllegalArgumentException expected) {
            duplicateCaptureRejected = true;
        }
        check(duplicateCaptureRejected,
            "a duplicate capturedBindings entry fails closed (captures are ordered "
                + "by first reference with one entry per binding)");

        boolean duplicateOpRejected = false;
        try {
            AdapterThunkConstruction.buildThunk(new BlockId(8005L),
                List.of(call, call), List.of(capture));
        } catch (IllegalArgumentException expected) {
            duplicateOpRejected = true;
        }
        check(duplicateOpRejected, "a duplicate source op fails closed");
    }

    /** Builds one IR-level op over the pinned schema (test construction only). */    /** Builds one IR-level op over the pinned schema (test construction only). */
    private static SemanticOp irValueOp(OpId opId, SemanticOpKind kind, KindPayload payload,
                                        ValueId result, RuntimeDescriptor resultType,
                                        List<ValueId> operands,
                                        List<RuntimeDescriptor> operandTypes) {
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, operandTypes, null,
            payload, FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder");
        SourceOrigin origin = new SourceOrigin("test.deal",
            new SourceSpan("test.deal", 1, 1, 1, 1), SourceOriginKind.USER,
            new AnchorId(opId.id()), null);
        return new SemanticOp(opId, kind, origin, result, resultType, operands,
            operandTypes, payload, FailurePolicyId.NO_DEAL_FAILURE, contract);
    }

    /**
     * Emission from birth (per corpus position): every
     * {@code FUNCTION_ADAPT} op the child produces carries its
     * closed-map mode and per-mode payload — one adapter per
     * {@code ADAPT}-classified position, no provisional or non-map
     * mode, and the emission facts agree with the recomputed map.
     */
    static void testEmissionFromBirthAndWiring() {
        System.out.println("-- emission from birth + creation wiring (corpus "
            + "positions) --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult(corpusSource(),
            "the corpus slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 6,
            "the corpus emits exactly six FUNCTION_ADAPT ops (g, h, k-decl, k-assign, "
                + "m, n); got " + adapters.size());
        check(result.shapeMapFacts().emissions().size() == adapters.size(),
            "the emission fact surface carries one record per emitted adapter; got "
                + result.shapeMapFacts().emissions().size());
        // One adapter per ADAPT-classified position (the creation-rule
        // child's classifications drive the emission).
        check(result.creationFacts().candidates().size() == 6,
            "the creation-rule facts record exactly six adaptation candidates (one "
                + "per emitted adapter); got "
                + result.creationFacts().candidates().size());

        // No adapter result feeds any BOUNDARY op other than its own
        // position's VARIABLE_DECLARATION/VARIABLE_ASSIGNMENT boundary
        // chain, and adapter creation emits zero BOUNDARY ops (children).
        for (SemanticOp adapter : adapters) {
            check(adapter.result() instanceof ValueId,
                "the adapter publishes a value identity");
            check(childrenOf(ops, adapter.opId()) == 0,
                "adapter " + adapter.opId() + " parents zero ops (no BOUNDARY child — "
                    + "the adapter adds no second boundary)");
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null) {
                continue;
            }
            check(payload.mode() != null && (payload.mode() == CaptureMode.VALUE
                    || payload.mode() == CaptureMode.SHARED_CELL
                    || payload.mode() == CaptureMode.REEVALUATE_THUNK),
                "adapter " + adapter.opId() + " carries a closed-map mode "
                    + payload.mode());
            check(payload.source() instanceof AdaptSourceRef,
                "adapter " + adapter.opId() + " carries its closed source reference "
                    + "from birth");
            ValueId adapterIdentity = (ValueId) adapter.result();
            int boundaryFeeds = boundaryConsumers(ops, adapterIdentity);
            check(boundaryFeeds >= 1,
                "the adapter result is the direct input of at least its own "
                    + "position's boundary chain; got " + boundaryFeeds);
            for (SemanticOp op : ops) {
                if (!(op.kind() == SemanticOpKind.BOUNDARY
                        && op.payload() instanceof KindPayload.BoundaryPayload boundary
                        && adapterIdentity.equals(boundary.input()))) {
                    continue;
                }
                if (op.opId().equals(emissionWiringTargetOf(result, adapterIdentity))) {
                    // The direct wiring: exactly the adapted position's
                    // own boundary chain.
                    check(boundary.kind() == BoundaryKind.VARIABLE_DECLARATION
                            || boundary.kind() == BoundaryKind.VARIABLE_ASSIGNMENT,
                        "the direct input of adapter " + adapter.opId() + " is its "
                            + "own VARIABLE_DECLARATION/VARIABLE_ASSIGNMENT boundary "
                            + "chain (got " + boundary.kind() + ")");
                    continue;
                }
                // Any other boundary whose input carries the adapter
                // identity is a post-commit crossing of the ordinary
                // identity-preserving function value (a load published
                // the identity — the FunctionAllocationIdentity
                // contract); the boundary kind stays a typed-boundary
                // crossing with the FUNCTION_SIGNATURE policy, never an
                // adaptation wiring.
                check(boundary.kind() == BoundaryKind.VARIABLE_DECLARATION
                        || boundary.kind() == BoundaryKind.VARIABLE_ASSIGNMENT,
                    "a non-wiring boundary crossing the adapter identity is an "
                        + "ordinary variable-boundary crossing (got " + boundary.kind()
                        + " for adapter " + adapter.opId() + ")");
                check(op.failurePolicy() == FailurePolicyId.FUNCTION_SIGNATURE,
                    "the later crossing checks FUNCTION_SIGNATURE (the ordinary "
                        + "typed-boundary policy)");
            }
        }

        // The emission facts' wiring targets are the position's own
        // boundary ops (the creation-rule child's wiring points).
        for (SemanticLowerer.AdapterEmission emission : result.shapeMapFacts().emissions()) {
            SemanticOp wiring = opOf(ops, emission.wiringTargetOpId());
            check(wiring != null && wiring.kind() == SemanticOpKind.BOUNDARY
                    && wiring.payload() instanceof KindPayload.BoundaryPayload boundary
                    && boundary.input().equals(emission.adapterIdentity()),
                "the emission's wiring target is the position's own boundary op with "
                    + "input = the adapter identity");
        }
    }

    /**
     * Identity: the corpus' six adaptation positions produce six
     * distinct adapter allocation identities, each with exactly one
     * registered AdapterBinding; loads preserve the adapter identity
     * (the exact-signature `p = g` load publishes g's adapter
     * identity), and the adapter identities are fresh per creation and
     * stable for the run (the FunctionAllocationIdentity contract).
     */
    static void testAdapterIdentityFreshPerCreationStableAcrossLoads() {
        System.out.println("-- identity: fresh per creation, one AdapterBinding each, "
            + "loads preserve --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult(corpusSource(),
            "the identity corpus slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        if (g == null) {
            return;
        }

        List<SemanticOp> adapters = adaptersOf(ops);
        check(adapters.size() == 6, "six adapters in the corpus; got " + adapters.size());
        if (adapters.size() != 6) {
            return;
        }
        java.util.Set<Long> identities = new java.util.HashSet<>();
        for (SemanticOp adapter : adapters) {
            check(adapter.result() instanceof ValueId identity
                    && identities.add(identity.id()),
                "adapter " + adapter.opId() + " publishes a fresh allocation identity "
                    + "distinct from every earlier adapter");
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new FunctionAllocationIdentity(((ValueId) adapter.result()).id()));
            check(binding instanceof FunctionExecutionBinding.AdapterBinding adapterBinding
                    && adapterBinding.adaptOpId().equals(adapter.opId()),
                "each adapter identity registers exactly one AdapterBinding naming its "
                    + "producing op");
        }
        check(unit.functionBindings().size() == 13,
            "the registry holds exactly thirteen bindings: five bodies (inner, even, "
                + "odd, main, the function expression) + six adapters + the two "
                + "producer-less intrinsic seeds (ISSUE-0632); got "
                + unit.functionBindings().size());

        // Loads preserve the adapter identity: `let p: (a,b) => null = g;`
        // is an exact direct store whose load publishes g's adapter
        // identity (the committed adapter value).
        List<SemanticOp> gAdapters = new ArrayList<>();
        for (SemanticOp adapter : adapters) {
            if (adapter.opId().equals(gPositionAdapter(ops, g))) {
                gAdapters.add(adapter);
            }
        }
        check(gAdapters.size() == 1, "g's position adapter found");
        if (gAdapters.size() == 1) {
            ValueId gAdapterIdentity = (ValueId) gAdapters.get(0).result();
            SemanticOp load = loadOf(ops, g.binding(), 0);
            check(load != null && load.result().equals(gAdapterIdentity),
                "the load of g publishes g's adapter identity (loads preserve "
                    + "identity — the FunctionAllocationIdentity contract)");
        }
    }

    /** The adapter op of the declaration of the named binding in the corpus unit. */
    private static OpId gPositionAdapter(List<SemanticOp> ops,
                                         SemanticLowerer.BindingCoreBinding g) {
        // g's declaration adapter is the VALUE adapter whose proof names
        // {f, 0}: found through the INIT operand chain — the adapter
        // whose result is g's INIT operand.
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.binding().equals(g.binding())) {
                ValueId committed = init.value();
                for (SemanticOp adapter : ops) {
                    if (adapter.kind() == SemanticOpKind.FUNCTION_ADAPT
                            && committed.equals(adapter.result())) {
                        return adapter.opId();
                    }
                }
            }
        }
        fail("g's declaration adapter not found");
        return null;
    }

    /**
     * The cell-kind iff across all three capture kinds (B2 completed by
     * construction): closure-captured (inner — the closure child's
     * arm), thunk-captured (t), SHARED_CELL-adapter-referenced (f),
     * uncaptured DIRECT (g/m/n/p), VALUE-adapted proven binding stays
     * DIRECT (g before any capture), group members stay SHARED_CELL
     * (pinned — even/odd), and the derivation never downgrades
     * (pinned special cases keep SHARED_CELL).
     */
    static void testCellKindIffAcrossAllThreeCaptureArms() {
        System.out.println("-- cell-kind iff: closure + thunk + SharedCell arms, "
            + "pinned cases, no downgrade --");

        SemanticLowerer.ShapeMapCoreResult result = loweredResult(corpusSource(),
            "the cell-kind corpus slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        SemanticLowerer.BindingCoreBinding inner = fact(result.bindingFacts(), "inner");
        SemanticLowerer.BindingCoreBinding f = fact(result.bindingFacts(), "f");
        SemanticLowerer.BindingCoreBinding g = fact(result.bindingFacts(), "g");
        SemanticLowerer.BindingCoreBinding s = fact(result.bindingFacts(), "s");
        SemanticLowerer.BindingCoreBinding m = fact(result.bindingFacts(), "m");
        SemanticLowerer.BindingCoreBinding n = fact(result.bindingFacts(), "n");
        SemanticLowerer.BindingCoreBinding p = fact(result.bindingFacts(), "p");
        SemanticLowerer.BindingCoreBinding even = fact(result.bindingFacts(), "even");
        SemanticLowerer.BindingCoreBinding odd = fact(result.bindingFacts(), "odd");
        if (inner == null || f == null || g == null || s == null || m == null
                || n == null || p == null || even == null || odd == null) {
            return;
        }
        check(inner.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "inner is SHARED_CELL (closure-captured: main's body captures the "
                + "module function — the closure child's arm)");
        check(f.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "f is SHARED_CELL (the SHARED_CELL-adapter SharedCell source reference — "
                + "this child's adapter arm)");
        check(s.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "s is SHARED_CELL (thunk-captured: the REEVALUATE_THUNK capturedBindings "
                + "entry — this child's thunk arm)");
        check(g.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "g stays DIRECT (the VALUE operand load of f is not a capture reference "
                + "and g is otherwise uncaptured)");
        check(m.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                && n.incarnations().get(0).cellKind() == BindingCellKind.DIRECT
                && p.incarnations().get(0).cellKind() == BindingCellKind.DIRECT,
            "m/n/p stay DIRECT (VALUE-adapted and uncaptured)");
        check(even.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL
                && odd.incarnations().get(0).cellKind() == BindingCellKind.SHARED_CELL,
            "the group members stay SHARED_CELL (the pinned special case — the closed "
                + "group payload records no cell-kind field)");

        // The ALLOC payloads carry the final kinds (the derivation's
        // single emission path applied to every BINDING_ALLOC).
        for (String name : List.of("inner", "f", "s")) {
            SemanticLowerer.BindingCoreBinding binding = fact(result.bindingFacts(), name);
            if (binding == null) {
                continue;
            }
            SemanticOp alloc = allocOf(ops, binding.binding(), 0);
            check(alloc != null
                    && ((KindPayload.BindingAllocPayload) alloc.payload()).cellKind()
                        == BindingCellKind.SHARED_CELL,
                name + "'s BINDING_ALLOC payload carries the final SHARED_CELL kind");
        }
        SemanticOp gAlloc = allocOf(ops, g.binding(), 0);
        check(gAlloc != null
                && ((KindPayload.BindingAllocPayload) gAlloc.payload()).cellKind()
                    == BindingCellKind.DIRECT,
            "g's BINDING_ALLOC payload carries DIRECT");

        // The derivation never downgrades: a pinned-shared incarnation
        // keeps SHARED_CELL through cellKindOf (the derivation's only
        // emission path).
        SemanticLowerer.CellKindDerivation derivation =
            new SemanticLowerer.CellKindDerivation();
        SemanticLowerer.BindingCoreIncarnation pinned = new SemanticLowerer
            .BindingCoreIncarnation(0, new BlockId(1L), BindingCellKind.DIRECT, true,
            SemanticLowerer.BindingProducer.BINDING_ALLOC, true);
        check(derivation.cellKindOf(pinned) == BindingCellKind.SHARED_CELL,
            "a pinned-shared incarnation derives SHARED_CELL (no downgrade)");
        SemanticLowerer.BindingCoreIncarnation ordinary = new SemanticLowerer
            .BindingCoreIncarnation(0, new BlockId(2L), BindingCellKind.DIRECT, true,
            SemanticLowerer.BindingProducer.BINDING_ALLOC, false);
        check(derivation.cellKindOf(ordinary) == BindingCellKind.DIRECT,
            "an unpinned, uncaptured incarnation derives DIRECT");
        derivation.registerCaptureReference(ordinary);
        check(derivation.cellKindOf(ordinary) == BindingCellKind.SHARED_CELL,
            "a registered capture reference upgrades DIRECT to SHARED_CELL");
    }

    /**
     * Negative: a proof-less binding never receives VALUE — the map's
     * fallback arm is SHARED_CELL, the binding-load surface agrees, and
     * the proof-guard rejects a proof for a non-binding shape.
     */
    static void testNegativeProofLessBindingNeverValue() {
        System.out.println("-- negative: proof-less binding never VALUE --");

        check(AdapterShapeMap.selectMode(AdapterShapeMap.SourceShape.BINDING_REFERENCE,
                Optional.empty()) == CaptureMode.SHARED_CELL,
            "selectMode(BINDING_REFERENCE, no proof) is SHARED_CELL — the map's "
                + "fallback arm");
        check(AdapterShapeMap.selectMode(AdapterShapeMap.SourceShape.BINDING_REFERENCE,
                Optional.of(new deal.semantic.ir.BindingImmutabilityProof(
                    new BindingId(1L), 0))) == CaptureMode.VALUE,
            "selectMode(BINDING_REFERENCE, proof) is VALUE — the proof is the only "
                + "admission of VALUE for a binding");
        check(AdapterShapeMap.selectModeOverBindingLoad(Optional.empty())
                == CaptureMode.SHARED_CELL,
            "the binding-load surface agrees: an unproven load is SHARED_CELL");
        boolean guardFired = false;
        try {
            AdapterShapeMap.selectMode(AdapterShapeMap.SourceShape.FUNCTION_EXPRESSION,
                Optional.of(new deal.semantic.ir.BindingImmutabilityProof(
                    new BindingId(2L), 0)));
        } catch (IllegalArgumentException expected) {
            guardFired = true;
        }
        check(guardFired,
            "a proof for a non-binding shape fails closed (never silently ignored)");
    }

    /**
     * The mode-selection seam accepts checker facts only: its public
     * surface carries no target, route, or emitter parameter type (the
     * interface contract of B7).
     */
    static void testModeSelectionSeamAcceptsCheckerFactsOnly() {
        System.out.println("-- mode-selection seam: checker facts only --");

        for (Method method : AdapterShapeMap.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(method.getModifiers())) {
                continue;
            }
            for (Class<?> parameter : method.getParameterTypes()) {
                String name = parameter.getName();
                boolean forbidden = name.contains("Target") || name.contains("Route")
                    || name.contains("Emitter") || name.contains("Backend")
                    || name.contains("Plan");
                check(!forbidden,
                    "the seam's public surface carries no target/route/emitter "
                        + "parameter: " + method.toGenericString());
            }
        }
        try {
            Method selectMode = AdapterShapeMap.class.getMethod("selectMode",
                AdapterShapeMap.SourceShape.class, Optional.class);
            check(selectMode != null, "selectMode(SourceShape, Optional) exists");
            Method produced = AdapterShapeMap.class.getMethod("selectModeOverProducedSource",
                SemanticOpKind.class, Optional.class);
            check(produced != null, "selectModeOverProducedSource(SemanticOpKind, "
                + "Optional) exists");
            Method bindingLoad = AdapterShapeMap.class.getMethod("selectModeOverBindingLoad",
                Optional.class);
            check(bindingLoad != null, "selectModeOverBindingLoad(Optional) exists");
        } catch (NoSuchMethodException defect) {
            fail("the closed mode-map surface is missing: " + defect.getMessage());
        }
    }

    /**
     * The combined corpus (all three modes over the earlier children's
     * production): binding-core generations, the closure child's
     * function values and captures, the registry child's one-to-one
     * registration (closures, group members, adapters), the proof
     * child's records (f defeated after g), and the creation-rule
     * child's classification/wiring — any break in an earlier module
     * fails the corpus. Byte-identical repeated lowering.
     */
    static void testCombinedCorpusAllModesAndRepeatedLowering() {
        System.out.println("-- combined corpus: all three modes, registry one-to-one, "
            + "byte-identical repetition --");

        String source = corpusSource();
        SemanticLowerer.ShapeMapCoreResult first = loweredResult(source,
            "the corpus (first lowering)");
        SemanticLowerer.ShapeMapCoreResult second = loweredResult(source,
            "the corpus (second lowering)");
        if (first == null || second == null) {
            return;
        }
        LoweredModuleUnit unit = first.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        // Modes per corpus position (emission from birth).
        Map<CaptureMode, Integer> modeCounts = new java.util.EnumMap<>(CaptureMode.class);
        for (SemanticOp adapter : adaptersOf(ops)) {
            KindPayload.FunctionAdaptPayload payload = adaptPayload(adapter);
            if (payload == null) {
                continue;
            }
            modeCounts.merge(payload.mode(), 1, Integer::sum);
        }
        check(modeCounts.getOrDefault(CaptureMode.VALUE, 0) == 3,
            "three VALUE adapters (g over the proved load, m over the CLOSURE_NEW "
                + "result, n over the intrinsic identity); got "
                + modeCounts.get(CaptureMode.VALUE));
        check(modeCounts.getOrDefault(CaptureMode.SHARED_CELL, 0) == 1,
            "one SHARED_CELL adapter (h over the reassigned f); got "
                + modeCounts.get(CaptureMode.SHARED_CELL));
        check(modeCounts.getOrDefault(CaptureMode.REEVALUATE_THUNK, 0) == 2,
            "two REEVALUATE_THUNK adapters (k's declaration and k's assignment over "
                + "the (s = inner) composite source); got "
                + modeCounts.get(CaptureMode.REEVALUATE_THUNK));

        // Registry one-to-one: every function-typed result resolves to
        // exactly one binding (the schema validator already ran green on
        // the unit); the adapter keys are distinct and each has exactly
        // one registration.
        java.util.Set<Long> adapterKeys = new java.util.HashSet<>();
        int adapterBindings = 0;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.AdapterBinding) {
                adapterBindings++;
                check(adapterKeys.add(entry.getKey().id()),
                    "the adapter registration keys are distinct");
            }
        }
        check(adapterBindings == 6,
            "six AdapterBinding registrations; got " + adapterBindings);

        // The classifications agree with the emissions (the
        // creation-rule child's wiring points feed this child's wiring).
        check(first.creationFacts().candidates().size() == 6,
            "six adaptation candidates (one per emitted adapter)");
        int matchedWiring = 0;
        for (deal.semantic.AdapterCreationRule.AdaptationCandidate candidate
                : first.creationFacts().candidates()) {
            for (SemanticLowerer.AdapterEmission emission
                    : first.shapeMapFacts().emissions()) {
                if (emission.wiringTargetOpId().equals(candidate.wiringPoint().opId())
                        && candidate.reDerivesAsAssignableButNotExact()) {
                    matchedWiring++;
                }
            }
        }
        check(matchedWiring == 6,
            "every candidate's wiring point matches one emission's wiring target (the "
                + "creation-rule child's prepared points are consumed); got "
                + matchedWiring);

        // Byte-identical repeated lowering.
        byte[] firstDump = SemanticIrDumper.dumpModule(first.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.lowering().unit());
        check(Arrays.equals(firstDump, secondDump),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dumps");
        check(first.shapeMapFacts().emissions().equals(second.shapeMapFacts().emissions()),
            "repeated lowering records identical emission facts");
    }

    /** The fixed combined-corpus source over the earlier children's production. */
    private static String corpusSource() {
        return """
            function inner(x: int): null {}
            function even(): null {
              let oddRef: () => null = odd;
            }
            function odd(): null {
              let evenRef: () => null = even;
            }
            function main(): null {
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
              f = f;
              let h: (a: int, b: int) => null = f;
              let s: (x: int) => null = inner;
              let k: (a: int, b: int) => null = (s = inner);
              k = (s = inner);
              let m: (a: int, b: int) => null = function(x: int): null {};
              let n: (a: number, b: number) => int = int;
              let p: (a: int, b: int) => null = g;
            }
            """;
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Adapter Shape Map / Payload Test (ISSUE-0450 shape-map "
            + "child) ===\n");

        testSharedCellBindingWithoutProof();
        testValueOverProvedBindingLoad();
        testValueOverFunctionExpression();
        testValueOverIntrinsic();
        testCompositeSourcesMapToReevaluateThunk();
        testReevaluateThunkPayloadConstruction();
        testHostExternalImportReadMapsToReevaluateThunk();
        testIrLevelThunkBuilderWrapsCallResultAndFailsClosed();
        testEmissionFromBirthAndWiring();
        testAdapterIdentityFreshPerCreationStableAcrossLoads();
        testCellKindIffAcrossAllThreeCaptureArms();
        testNegativeProofLessBindingNeverValue();
        testModeSelectionSeamAcceptsCheckerFactsOnly();
        testCombinedCorpusAllModesAndRepeatedLowering();

        System.out.println("\nAdapter shape map / payload: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
