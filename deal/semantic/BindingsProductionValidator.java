package deal.semantic;

import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The B9 production-time structural validation of the BINDINGS
 * capability (ISSUE-0451 validation child; design B9): the closed rule
 * set {@code GROUP_SHAPE}, {@code CAPTURE_RESOLUTION},
 * {@code BINDING_GENERATION_RESOLUTION}, {@code BINDING_INIT_ONCE},
 * {@code INIT_DOMINATES_LOAD}, {@code ADAPTER_PAIR},
 * {@code ADAPTER_SOURCE_SHAPE}, {@code REGISTRY_ONE_TO_ONE}, and
 * {@code NO_ADAPTER_AT_BOUNDARY} over one validated
 * {@link LoweredModuleUnit} plus its produced
 * {@link StructuredBodyTable} — the production walk is the membership
 * authority (the walk owns the block map and runs these checks with
 * it). Every rejection is E6005 with the rule identifier, module,
 * capability {@code BINDINGS}, profile/version, and source origin via
 * the {@link FailureContractRegistry} {@link LoweringFailureDetail}
 * carrier — never a new diagnostic code. The closed 14-condition
 * schema validator ({@code deal.semantic.ir.SemanticIrValidator}) is
 * unchanged and keeps running on both surfaces; these rules are the
 * production-site realization of the structural checks the closed
 * schema page deferred to the construct epics.
 *
 * <p><b>The one uniform resolution context (R1-R4).</b> All three
 * resolution-backed rules ({@code BINDING_GENERATION_RESOLUTION},
 * {@code CAPTURE_RESOLUTION}, {@code INIT_DOMINATES_LOAD}) resolve
 * {@code {binding, generation}} references and binding captures over
 * the same model:</p>
 *
 * <ul>
 *   <li><b>R1 — plain/structured sites.</b> A site resolves against the
 *       producing allocations of its own block and every block
 *       dominating the site through structured edges (ancestor blocks
 *       transitively, with the intra-{@code LOOP} edges: the init
 *       block's ops dominate the condition evaluation, which dominates
 *       the body block's ops, which dominate the update block's ops —
 *       the {@code control-flow-structures} C-D4 placement contract is
 *       the Basis input).</li>
 *   <li><b>R2 — detached function-body sites.</b> A site inside a
 *       {@code LoweredFunction.body} resolves against the body's own
 *       subgraph (R1 within it) or exactly its
 *       {@code LoweredFunction.captures} list, whose entries resolve
 *       at the detaching op's creation site recursively along the
 *       detaching chain.</li>
 *   <li><b>R3 — thunk sites.</b> A site inside a
 *       {@code Thunk.blockId} resolves against the thunk block's own
 *       subgraph or exactly its generation-pinned
 *       {@code capturedBindings}, resolved at the
 *       {@code FUNCTION_ADAPT} creation site.</li>
 *   <li><b>R4 — default-block sites.</b> A site inside a
 *       {@code CLASS_DEFAULT.defaultBlock} resolves against the
 *       default block's own subgraph plus module-level bindings; any
 *       further free reference is ISSUE-0238's boundary and this epic
 *       validates nothing further (it admits the module-level arm and
 *       skips the rest).</li>
 * </ul>
 *
 * <p>Payload references carried on a {@code FUNCTION_ADAPT} op itself
 * ({@code SharedCell}, {@code proof}, and the thunk's
 * {@code capturedBindings} entries) resolve at the
 * {@code FUNCTION_ADAPT} creation site, never against the detached
 * thunk block. Generation equality is checked at every chain step.</p>
 *
 * <p><b>Determinism and purity.</b> {@link #validate} reads the unit
 * and the table and mutates neither; repeated validation of the same
 * inputs yields the same first rejection. The first-failure order is
 * fixed: {@code GROUP_SHAPE}, {@code CAPTURE_RESOLUTION},
 * {@code BINDING_GENERATION_RESOLUTION}, {@code BINDING_INIT_ONCE},
 * {@code INIT_DOMINATES_LOAD}, {@code ADAPTER_PAIR},
 * {@code ADAPTER_SOURCE_SHAPE}, {@code REGISTRY_ONE_TO_ONE},
 * {@code NO_ADAPTER_AT_BOUNDARY}; within each rule the unit's ops in
 * unit order decide the first defect.</p>
 *
 * <p><b>Cell-kind invariant (B2 iff).</b> {@link #deriveCellKinds}
 * exposes the closed cell-kind derivation — the pinned special cases
 * ({@code FOR_EACH} iteration bindings and for-let per-iteration
 * incarnations) plus the union of the three capture reference sets
 * (closure captures, thunk {@code capturedBindings} entries,
 * {@code FUNCTION_ADAPT(SHARED_CELL)} {@code SharedCell} sources) —
 * the surface the corpus asserts the emitted {@code BINDING_ALLOC}
 * payload kinds against. It is an invariant assertion over the emitted
 * units, not a new validator rule (the closed schema validator is
 * unchanged).</p>
 */
public final class BindingsProductionValidator {

    /** The group-shape rule (B9): member lists, registrations, no member ALLOC/INIT. */
    public static final String GROUP_SHAPE = "GROUP_SHAPE";

    /** The capture-resolution rule (B9 R1-R4): closure/thunk captures resolve along the chain. */
    public static final String CAPTURE_RESOLUTION = "CAPTURE_RESOLUTION";

    /** The generation-resolution rule (B9): every {@code {binding, generation}} reference resolves. */
    public static final String BINDING_GENERATION_RESOLUTION = "BINDING_GENERATION_RESOLUTION";

    /**
     * The init-once rule (B9): one INIT per source-declaration
     * incarnation; no INIT on a pinned-write cell; and the
     * {@code MODULE_IMPORT} completion agreement — the payload's explicit
     * alias-cell list names exactly the unit's import-alias allocations,
     * once each.
     */
    public static final String BINDING_INIT_ONCE = "BINDING_INIT_ONCE";

    /** The init-dominates-load rule (B9): loads only; stores are exempt. */
    public static final String INIT_DOMINATES_LOAD = "INIT_DOMINATES_LOAD";

    /** The adapter-pair rule (B9/B6): the pair re-derives as assignable-but-not-exact. */
    public static final String ADAPTER_PAIR = "ADAPTER_PAIR";

    /**
     * The adapter-source-shape rule (B9/B8): mode↔source shape, proof iff
     * VALUE-over-binding — with the closed VALUE-over-intrinsic exemption
     * (ISSUE-0674): the seeded conversion intrinsic's identity is the
     * intrinsic function value itself, so a VALUE operand that is a
     * seed-admitted {@code IntrinsicFunction} key published only by
     * identity-preserving loads of the seeded binding is admissible with
     * or without its proof (a present proof must name the seeded
     * binding/generation).
     */
    public static final String ADAPTER_SOURCE_SHAPE = "ADAPTER_SOURCE_SHAPE";

    /**
     * The registry one-to-one rule (B9/B5): one registration per producing
     * allocation, plus the producer-less intrinsic-seed clause set
     * (admission, converse, and the pinned declared signature of the two
     * conversion intrinsics) and the dynamic-materialization clause set
     * (ISSUE-0674): a {@code DynamicFunctionValue} key is admissible
     * exactly when the op its record names produces that key identity and
     * the key carries no static producing position (no closure, group,
     * adapt, or export-read production, no function-typed
     * {@code HOST_TO_DEAL} crossing input, and no producer-less seed
     * {@code BINDING_INIT} operand; a member read with a function-typed
     * result is one of the dynamic producer arms, so it is not a static
     * position). The producer-less test
     * carries the identity-preserving-load exclusion: a load whose result
     * identity is an already-allocated identity of the cell it names (that
     * cell's {@code BINDING_INIT} carries it) is not a producing position,
     * while a load naming a cell whose init carries another identity (a
     * parameter, catch, or iteration cell, or a dynamically allocated
     * identity tracked into a later cell) is — the exclusion is per
     * publishing op and closed (ISSUE-0675): an identity any load of which
     * does not republish a carrying cell is a producing position even when
     * another load over the same identity preserves it, so a dynamically
     * allocated identity tracked into a later cell is never mistaken for a
     * producer-less seed operand. An alias declaration's re-publication of
     * the seed write into its own cell makes its alias loads
     * identity-preserving too (ISSUE-0676 J1's alias-load refinement).
     */
    public static final String REGISTRY_ONE_TO_ONE = "REGISTRY_ONE_TO_ONE";

    /** The no-adapter-at-boundary rule (B9/B6): the adapter result wires into its own position only. */
    public static final String NO_ADAPTER_AT_BOUNDARY = "NO_ADAPTER_AT_BOUNDARY";

    private BindingsProductionValidator() {
        // Static surface; no instances.
    }

    // =========================================================================
    // Public surfaces
    // =========================================================================

    /**
     * Validates one unit plus its block-membership table against the
     * B9 rule set. Returns empty on pass and exactly one E6005
     * diagnostic naming the first failing rule on failure. No
     * mutation; deterministic; linear in ops plus block edges and
     * capture chains.
     *
     * @param unit  the lowered module unit; non-null
     * @param table the block-membership table of the unit; non-null
     * @return empty on pass, otherwise the first E6005
     */
    public static Optional<CompilerDiagnostic> validate(LoweredModuleUnit unit,
                                                        StructuredBodyTable table) {
        return validate(unit, table, PinnedWriteFacts.empty());
    }

    /**
     * Validates one unit plus its block-membership table plus the
     * walk's pinned-write binding facts against the B9 rule set.
     * {@link PinnedWriteFacts} carries the two checker-fact arms the
     * unit payload cannot express — parameter bindings and import
     * aliases ({@code BINDING_INIT_ONCE} consumes them; the catch,
     * group-member, and {@code FOR_EACH} arms are unit-derivable).
     * Returns empty on pass and exactly one E6005 diagnostic naming
     * the first failing rule on failure. No mutation; deterministic;
     * linear in ops plus block edges and capture chains.
     *
     * @param unit  the lowered module unit; non-null
     * @param table the block-membership table of the unit; non-null
     * @param facts the walk's pinned-write binding facts; non-null
     * @return empty on pass, otherwise the first E6005
     */
    public static Optional<CompilerDiagnostic> validate(LoweredModuleUnit unit,
                                                        StructuredBodyTable table,
                                                        PinnedWriteFacts facts) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(facts, "facts must not be null");
        Model model = Model.build(unit, table, facts);

        Optional<CompilerDiagnostic> failure = checkGroupShape(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkCaptureResolution(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkBindingGenerationResolution(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkBindingInitOnce(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkInitDominatesLoad(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkAdapterPair(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkAdapterSourceShape(model);
        if (failure.isPresent()) {
            return failure;
        }
        failure = checkRegistryOneToOne(model);
        if (failure.isPresent()) {
            return failure;
        }
        return checkNoAdapterAtBoundary(model);
    }

    /**
     * The walk's pinned-write binding facts supplied to the validator
     * ({@code BINDING_INIT_ONCE}'s two checker-fact arms). The unit
     * payload alone cannot distinguish a parameter ALLOC from a local
     * ALLOC (both {@code mutable=true}, generation 0, body-root block)
     * or an import-alias ALLOC from an intrinsic ALLOC (both
     * module-region {@code mutable=false} ALLOCs) — the walk owns the
     * checker facts and supplies them here. The remaining pinned
     * initializing writes (catch binding, group member,
     * {@code FOR_EACH} iteration binding) are unit-derivable and need
     * no fact arm.
     */
    public record PinnedWriteFacts(Set<BindingId> parameters, Set<BindingId> importAliases) {

        /** The empty fact set (the non-walk validation surface's default). */
        public static PinnedWriteFacts empty() {
            return new PinnedWriteFacts(Set.of(), Set.of());
        }

        public PinnedWriteFacts {
            Objects.requireNonNull(parameters, "parameters must not be null");
            Objects.requireNonNull(importAliases, "importAliases must not be null");
            parameters = Set.copyOf(parameters);
            importAliases = Set.copyOf(importAliases);
        }
    }

    /** One derived cell kind of an incarnation (the {@link #deriveCellKinds} row). */
    public record DerivedCellKind(IncarnationKey key, BindingCellKind kind) {
    }

    /** The incarnation key of the cell-kind derivation: binding, generation, block scope. */
    public record IncarnationKey(BindingId binding, long generation, BlockId scope) {
    }

    /**
     * Derives the closed B2 cell kind of every producing allocation
     * incarnation of the unit: {@code SHARED_CELL} iff the incarnation
     * is a pinned special case ({@code FOR_EACH} iteration binding or a
     * for-let per-iteration incarnation) or any capture reference of
     * the union of the three closed capture sets (closure captures,
     * thunk {@code capturedBindings} entries,
     * {@code FUNCTION_ADAPT(SHARED_CELL)} {@code SharedCell} sources)
     * resolves to it; {@code DIRECT} otherwise. Group members derive
     * {@code SHARED_CELL} by construction (B2: SCC mutual capture).
     * The result is the corpus-side invariant assertion surface — not
     * a validator rule; the emitted {@code BINDING_ALLOC} payload
     * kinds must equal exactly this derivation.
     *
     * @param unit  the lowered module unit; non-null
     * @param table the block-membership table of the unit; non-null
     * @return the derived kinds in producing-allocation order
     */
    public static List<DerivedCellKind> deriveCellKinds(LoweredModuleUnit unit,
                                                        StructuredBodyTable table) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Model model = Model.build(unit, table, PinnedWriteFacts.empty());
        List<DerivedCellKind> derived = new ArrayList<>();
        // The for-let per-iteration detection: a binding with both a
        // generation-0 incarnation and a generation-1 incarnation is
        // the pinned two-incarnation shape — its generation-1
        // incarnation is always SHARED_CELL (B1/B2).
        Set<BindingId> perIterationBindings = new LinkedHashSet<>();
        for (List<Allocation> allocations : model.allocationsByBinding.values()) {
            boolean hasGen0 = false;
            boolean hasGen1 = false;
            for (Allocation allocation : allocations) {
                if (allocation.generation == 0) {
                    hasGen0 = true;
                } else if (allocation.generation == 1) {
                    hasGen1 = true;
                }
            }
            if (hasGen0 && hasGen1) {
                for (Allocation allocation : allocations) {
                    if (allocation.generation == 1
                            && allocation.op.payload()
                                instanceof KindPayload.BindingAllocPayload alloc) {
                        perIterationBindings.add(alloc.binding());
                    }
                }
            }
        }
        for (SemanticOp op : model.unit.ops()) {
            switch (op.payload()) {
                case KindPayload.BindingAllocPayload alloc -> {
                    IncarnationKey key = new IncarnationKey(alloc.binding(),
                        alloc.generation(), alloc.scope());
                    boolean special = alloc.generation() == 1
                        && perIterationBindings.contains(alloc.binding());
                    derived.add(new DerivedCellKind(key,
                        special || model.captured(key) ? BindingCellKind.SHARED_CELL
                            : BindingCellKind.DIRECT));
                }
                case KindPayload.ForEachPayload forEach -> {
                    BlockId scope = model.blockOf(op.opId());
                    if (scope == null) {
                        scope = forEach.body();
                    }
                    derived.add(new DerivedCellKind(new IncarnationKey(forEach.binding(),
                        forEach.generation(), scope), BindingCellKind.SHARED_CELL));
                }
                case KindPayload.RecursiveGroupInitPayload group -> {
                    for (BindingId binding : group.bindings()) {
                        BlockId scope = model.blockOf(op.opId());
                        derived.add(new DerivedCellKind(
                            new IncarnationKey(binding, 0, scope),
                            BindingCellKind.SHARED_CELL));
                    }
                }
                default -> {
                    // No producing-allocation payload.
                }
            }
        }
        return derived;
    }

    // =========================================================================
    // E6005 construction (registry-owned; no hand-crafted message)
    // =========================================================================

    private static Optional<CompilerDiagnostic> fail(Model model, String rule, String what) {
        LoweringFailureDetail detail = new LoweringFailureDetail(
            model.unit.moduleId().path(),
            SemanticCapability.BINDINGS,
            rule,
            model.unit.semanticProfile(),
            LoweredModuleUnit.FORMAT_VERSION,
            "BindingsProductionValidator " + rule + " (" + what + ")");
        return Optional.of(FailureContractRegistry.e6005(detail));
    }

    // =========================================================================
    // The per-pass deterministic model of unit + table
    // =========================================================================

    /** One producing allocation of one binding incarnation. */
    private record Allocation(SemanticOp op, long generation, BlockId block) {
    }

    /** One resolved capture: the producing allocation op plus its generation. */
    private record ResolvedCapture(SemanticOp op, long generation) {
    }

    /** The resolution outcome of one {@code {binding, generation}} reference. */
    private record Resolution(SemanticOp allocation, boolean outOfScope) {
    }

    /** One initializing write of an incarnation. */
    private record Write(SemanticOp op) {
    }

    /** The {@code {binding, generation}} key of INIT/ALLOC payloads. */
    private record BindingSite(BindingId binding, long generation) {
    }

    private static final class Model {

        final LoweredModuleUnit unit;
        final StructuredBodyTable table;
        final Map<OpId, SemanticOp> opById = new LinkedHashMap<>();
        final Map<OpId, BlockId> blockOfOp = new LinkedHashMap<>();
        final Map<BlockId, List<SemanticOp>> opsInBlock = new LinkedHashMap<>();
        final Map<OpId, Integer> indexInBlock = new LinkedHashMap<>();
        /** The child blocks per structure op (control positions, payload order). */
        final Map<OpId, List<BlockId>> controlChildren = new LinkedHashMap<>();
        /** The parent block of every control child block. */
        final Map<BlockId, BlockId> parentBlock = new LinkedHashMap<>();
        /** The intra-LOOP sequencing edges (init→body, body→update). */
        final Map<BlockId, List<BlockId>> intraLoopEdges = new LinkedHashMap<>();
        /** The region root of every block of the table. */
        final Map<BlockId, BlockId> regionRoot = new LinkedHashMap<>();
        /** The blocks of every region in deterministic order (root first). */
        final Map<BlockId, List<BlockId>> regionBlocks = new LinkedHashMap<>();
        /** The blocks whose ops dominate a block's ops within its region. */
        final Map<BlockId, Set<BlockId>> dominators = new LinkedHashMap<>();
        /** The function-body region roots. */
        final Set<BlockId> functionRoots = new LinkedHashSet<>();
        /** The thunk region roots. */
        final Set<BlockId> thunkRoots = new LinkedHashSet<>();
        /** The default-block region roots. */
        final Set<BlockId> defaultRoots = new LinkedHashSet<>();
        /** The module-init region root. */
        final BlockId moduleRoot;
        /** The detaching op of every function-body region root. */
        final Map<BlockId, SemanticOp> detachingOfFunction = new LinkedHashMap<>();
        /** The detaching op of every thunk region root (the FUNCTION_ADAPT op). */
        final Map<BlockId, SemanticOp> detachingOfThunk = new LinkedHashMap<>();
        /** The detaching op of every default-block region root (the CLASS_DEFAULT op). */
        final Map<BlockId, SemanticOp> detachingOfDefault = new LinkedHashMap<>();
        /** The captures list of every function-body region root (LoweredFunction record). */
        final Map<BlockId, List<BindingId>> capturesOfRegion = new LinkedHashMap<>();
        /** The pinned captures of every thunk region root. */
        final Map<BlockId, List<BindingGeneration>> thunkCapturesOfRegion =
            new LinkedHashMap<>();
        /** Every producing allocation of every binding, in unit op order. */
        final Map<BindingId, List<Allocation>> allocationsByBinding = new LinkedHashMap<>();
        /** The INIT ops per {@code {binding, generation}}. */
        final Map<BindingSite, List<SemanticOp>> initsBySite = new LinkedHashMap<>();
        /** The ALLOC ops per {@code {binding, generation}}. */
        final Map<BindingSite, List<SemanticOp>> allocsBySite = new LinkedHashMap<>();
        /** The member bodies per group op (declaration order). */
        final Map<OpId, List<BlockId>> memberBodies = new LinkedHashMap<>();
        /** The registry entry per LoweredBody function id. */
        final Map<FunctionId, Map.Entry<FunctionAllocationIdentity,
            FunctionExecutionBinding>> registryByFunction = new LinkedHashMap<>();
        /** The MODULE_IMPORT ops in unit op order (the import-alias completions). */
        final List<SemanticOp> moduleImports = new ArrayList<>();
        /**
         * The MODULE_IMPORT completions per named alias cell, in unit op
         * order (the payload's explicit alias-cell list is the
         * alias&#8596;import join; the declaration-order positional
         * pairing is superseded). A cell with zero entries is named by no
         * completion; a cell with two entries is doubly named — both are
         * producer defects ({@code BINDING_INIT_ONCE}'s completion
         * agreement arm).
         */
        final Map<BindingId, List<SemanticOp>> completionsByCell = new LinkedHashMap<>();
        /** The no-INIT module-region ALLOCs in unit op order (the import aliases). */
        final List<SemanticOp> aliasAllocs = new ArrayList<>();
        /** The walk's pinned parameter bindings (BINDING_INIT_ONCE's checker-fact arm). */
        final Set<BindingId> parameters;
        /** The walk's pinned import-alias bindings (BINDING_INIT_ONCE's checker-fact arm). */
        final Set<BindingId> importAliases;
        /** The LOOP op of every LOOP child block (init/body/update → the op). */
        final Map<BlockId, SemanticOp> loopOfBlock = new LinkedHashMap<>();

        Model(LoweredModuleUnit unit, StructuredBodyTable table, BlockId moduleRoot,
              PinnedWriteFacts facts) {
            this.unit = unit;
            this.table = table;
            this.moduleRoot = moduleRoot;
            this.parameters = facts.parameters();
            this.importAliases = facts.importAliases();
        }

        /** The block an op is a member of (or null for module-level kinds). */
        BlockId blockOf(OpId opId) {
            return blockOfOp.get(opId);
        }

        static Model build(LoweredModuleUnit unit, StructuredBodyTable table,
                           PinnedWriteFacts facts) {
            BlockId moduleRoot = unit.moduleInit().initBlock();
            Model model = new Model(unit, table, moduleRoot, facts);
            for (SemanticOp op : unit.ops()) {
                model.opById.put(op.opId(), op);
            }
            for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
                List<SemanticOp> ops = new ArrayList<>();
                for (OpId opId : entry.getValue()) {
                    SemanticOp op = model.opById.get(opId);
                    if (op == null) {
                        continue; // defensive; the control-flow validator owns membership
                    }
                    ops.add(op);
                    model.blockOfOp.put(opId, entry.getKey());
                    model.indexInBlock.put(opId, ops.size() - 1);
                }
                model.opsInBlock.put(entry.getKey(), ops);
            }
            // Control positions and intra-LOOP edges.
            for (Map.Entry<BlockId, List<SemanticOp>> entry : model.opsInBlock.entrySet()) {
                for (SemanticOp op : entry.getValue()) {
                    List<BlockId> children = controlChildrenOf(op);
                    model.controlChildren.put(op.opId(), children);
                    for (BlockId child : children) {
                        model.parentBlock.put(child, entry.getKey());
                    }
                    if (op.kind() == SemanticOpKind.LOOP
                            && op.payload() instanceof KindPayload.LoopPayload loop) {
                        if (loop.initBlock() != null) {
                            model.loopOfBlock.put(loop.initBlock(), op);
                        }
                        model.loopOfBlock.put(loop.bodyBlock(), op);
                        if (loop.updateBlock() != null) {
                            model.loopOfBlock.put(loop.updateBlock(), op);
                        }
                        if (loop.initBlock() != null && loop.bodyBlock() != null) {
                            model.intraLoopEdges.computeIfAbsent(loop.initBlock(),
                                k -> new ArrayList<>()).add(loop.bodyBlock());
                        }
                        if (loop.updateBlock() != null && loop.bodyBlock() != null) {
                            model.intraLoopEdges.computeIfAbsent(loop.bodyBlock(),
                                k -> new ArrayList<>()).add(loop.updateBlock());
                        }
                    }
                }
            }
            // Region roots.
            Set<BlockId> roots = new LinkedHashSet<>();
            roots.add(moduleRoot);
            for (LoweredFunction function : unit.functions().values()) {
                roots.add(function.body());
                model.functionRoots.add(function.body());
                model.capturesOfRegion.put(function.body(), function.captures());
            }
            for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
                if (binding instanceof FunctionExecutionBinding.LoweredBody body
                        && !roots.contains(body.blockId())) {
                    roots.add(body.blockId());
                    model.functionRoots.add(body.blockId());
                    model.capturesOfRegion.putIfAbsent(body.blockId(), List.of());
                }
            }
            for (SemanticOp op : unit.ops()) {
                if (op.payload() instanceof KindPayload.FunctionAdaptPayload adapt) {
                    if (adapt.source() instanceof AdaptSourceRef.Thunk thunk) {
                        roots.add(thunk.blockId());
                        model.thunkRoots.add(thunk.blockId());
                        model.thunkCapturesOfRegion.put(thunk.blockId(),
                            thunk.capturedBindings());
                        model.detachingOfThunk.put(thunk.blockId(), op);
                    }
                } else if (op.payload() instanceof KindPayload.ClassDefaultPayload def) {
                    roots.add(def.defaultBlock());
                    model.defaultRoots.add(def.defaultBlock());
                    model.detachingOfDefault.put(def.defaultBlock(), op);
                }
            }
            // Region assignment: every table block reaches a root through
            // the parent chain (the control-flow validator's block tree
            // guarantees acyclicity); unreachable blocks are their own
            // region roots.
            for (BlockId block : table.blockOps().keySet()) {
                if (model.regionRoot.containsKey(block)) {
                    continue;
                }
                List<BlockId> path = new ArrayList<>();
                BlockId current = block;
                while (!model.regionRoot.containsKey(current)) {
                    path.add(current);
                    BlockId parent = model.parentBlock.get(current);
                    if (parent == null) {
                        break;
                    }
                    current = parent;
                }
                BlockId root = model.regionRoot.get(current);
                if (root == null) {
                    root = current;
                }
                for (BlockId onPath : path) {
                    model.regionRoot.put(onPath, root);
                }
                model.regionRoot.putIfAbsent(current, root);
            }
            for (BlockId root : roots) {
                model.regionRoot.putIfAbsent(root, root);
            }
            for (BlockId block : table.blockOps().keySet()) {
                BlockId root = model.regionRoot.get(block);
                if (root == null) {
                    root = block;
                    model.regionRoot.put(block, root);
                }
                model.regionBlocks.computeIfAbsent(root, k -> new ArrayList<>()).add(block);
            }
            // Roots that list no member block still own a region.
            for (BlockId root : roots) {
                model.regionBlocks.computeIfAbsent(root, k -> new ArrayList<>());
            }
            // Dominators within each region: structured child edges plus
            // the intra-LOOP sequencing edges. dominators[X] = the blocks
            // whose ops dominate X's ops (the blocks X is reachable from).
            for (Map.Entry<BlockId, List<BlockId>> entry
                    : model.regionBlocks.entrySet()) {
                BlockId root = entry.getKey();
                Set<BlockId> region = new LinkedHashSet<>(entry.getValue());
                region.add(root);
                Map<BlockId, Set<BlockId>> reachable = new LinkedHashMap<>();
                for (BlockId block : region) {
                    Set<BlockId> reach = new LinkedHashSet<>();
                    List<BlockId> queue = new ArrayList<>(model.edgesOf(block, region));
                    while (!queue.isEmpty()) {
                        BlockId next = queue.remove(0);
                        if (reach.add(next)) {
                            queue.addAll(model.edgesOf(next, region));
                        }
                    }
                    reachable.put(block, reach);
                }
                for (BlockId block : region) {
                    Set<BlockId> dominating = new LinkedHashSet<>();
                    for (Map.Entry<BlockId, Set<BlockId>> source : reachable.entrySet()) {
                        if (source.getValue().contains(block)) {
                            dominating.add(source.getKey());
                        }
                    }
                    model.dominators.put(block, dominating);
                }
            }
            // Producing allocations.
            for (SemanticOp op : unit.ops()) {
                switch (op.payload()) {
                    case KindPayload.BindingAllocPayload alloc -> {
                        model.registerAllocation(alloc.binding(), op, alloc.generation());
                        model.allocsBySite.computeIfAbsent(new BindingSite(alloc.binding(),
                            alloc.generation()), k -> new ArrayList<>()).add(op);
                    }
                    case KindPayload.ForEachPayload forEach ->
                        model.registerAllocation(forEach.binding(), op, forEach.generation());
                    case KindPayload.RecursiveGroupInitPayload group -> {
                        List<BlockId> bodies = new ArrayList<>();
                        for (FunctionId functionId : group.functions()) {
                            LoweredFunction function = unit.functions().get(functionId);
                            if (function == null) {
                                continue; // GROUP_SHAPE rejects this first
                            }
                            bodies.add(function.body());
                        }
                        model.memberBodies.put(op.opId(), bodies);
                        for (BindingId binding : group.bindings()) {
                            model.registerAllocation(binding, op, 0);
                        }
                    }
                    case KindPayload.BindingInitPayload init ->
                        model.initsBySite.computeIfAbsent(new BindingSite(init.binding(),
                            init.generation()), k -> new ArrayList<>()).add(op);
                    default -> {
                        // No binding payload.
                    }
                }
                if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                    model.moduleImports.add(op);
                    if (op.payload()
                            instanceof KindPayload.ModuleImportPayload importPayload) {
                        for (BindingId cell : importPayload.aliasCells()) {
                            model.completionsByCell
                                .computeIfAbsent(cell, k -> new ArrayList<>()).add(op);
                        }
                    }
                }
            }
            for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                    : unit.functionBindings().entrySet()) {
                if (entry.getValue() instanceof FunctionExecutionBinding.LoweredBody body) {
                    model.registryByFunction.put(body.functionId(), entry);
                }
            }
            // The import-alias ALLOCs: module-region ALLOCs with no INIT
            // (module-level function names and intrinsics always carry
            // their INITs in the full walk).
            BlockId moduleRegionRoot = model.regionRoot.get(moduleRoot);
            for (SemanticOp op : unit.ops()) {
                if (!(op.payload() instanceof KindPayload.BindingAllocPayload alloc)) {
                    continue;
                }
                BlockId block = model.blockOf(op.opId());
                if (block == null) {
                    continue;
                }
                BlockId root = model.regionRoot.get(block);
                if (root != null && root.equals(moduleRegionRoot)
                        && !model.initsBySite.containsKey(
                            new BindingSite(alloc.binding(), alloc.generation()))) {
                    model.aliasAllocs.add(op);
                }
            }
            // Detaching ops of function-body regions: the CLOSURE_NEW whose
            // LoweredBody names the root block, or the RECURSIVE_GROUP_INIT
            // whose members include the root block.
            for (SemanticOp op : unit.ops()) {
                if (op.payload() instanceof KindPayload.ClosureNewPayload closure
                        && model.functionRoots.contains(closure.binding().blockId())) {
                    model.detachingOfFunction.putIfAbsent(closure.binding().blockId(), op);
                } else if (op.payload()
                        instanceof KindPayload.RecursiveGroupInitPayload group) {
                    for (FunctionId functionId : group.functions()) {
                        LoweredFunction function = unit.functions().get(functionId);
                        if (function != null) {
                            model.detachingOfFunction.putIfAbsent(function.body(), op);
                        }
                    }
                }
            }
            return model;
        }

        void registerAllocation(BindingId binding, SemanticOp op, long generation) {
            BlockId block = blockOf(op.opId());
            allocationsByBinding.computeIfAbsent(binding, k -> new ArrayList<>())
                .add(new Allocation(op, generation, block));
        }

        static List<BlockId> controlChildrenOf(SemanticOp op) {
            List<BlockId> children = new ArrayList<>(2);
            switch (op.kind()) {
                case BRANCH -> {
                    KindPayload.BranchPayload payload = (KindPayload.BranchPayload) op.payload();
                    children.add(payload.selectedBlock());
                    if (payload.alternateBlock() != null) {
                        children.add(payload.alternateBlock());
                    }
                }
                case LOOP -> {
                    KindPayload.LoopPayload payload = (KindPayload.LoopPayload) op.payload();
                    if (payload.initBlock() != null) {
                        children.add(payload.initBlock());
                    }
                    children.add(payload.bodyBlock());
                    if (payload.updateBlock() != null) {
                        children.add(payload.updateBlock());
                    }
                }
                case FOR_EACH -> children.add(((KindPayload.ForEachPayload) op.payload()).body());
                case TRY_CATCH -> {
                    KindPayload.TryCatchPayload payload =
                        (KindPayload.TryCatchPayload) op.payload();
                    children.add(payload.tryBlock());
                    children.add(payload.catchBlock());
                }
                default -> {
                    // No control-tree child positions.
                }
            }
            return children;
        }

        /** The edges out of one block within one region (deterministic order). */
        List<BlockId> edgesOf(BlockId block, Set<BlockId> region) {
            List<BlockId> edges = new ArrayList<>();
            List<SemanticOp> ops = opsInBlock.get(block);
            if (ops != null) {
                for (SemanticOp op : ops) {
                    for (BlockId child : controlChildren.getOrDefault(op.opId(), List.of())) {
                        if (region.contains(child)) {
                            edges.add(child);
                        }
                    }
                }
            }
            for (BlockId next : intraLoopEdges.getOrDefault(block, List.of())) {
                if (region.contains(next)) {
                    edges.add(next);
                }
            }
            return edges;
        }

        /** The blocks whose producing allocations a site in {@code block} can resolve against. */
        Set<BlockId> visibleBlocks(BlockId block) {
            Set<BlockId> visible = new LinkedHashSet<>();
            visible.add(block);
            visible.addAll(dominators.getOrDefault(block, Set.of()));
            return visible;
        }

        /** The visible producing allocations of one binding at a site (any generation). */
        List<Allocation> visibleAllocations(BindingId binding, BlockId site) {
            List<Allocation> result = new ArrayList<>();
            Set<BlockId> visible = visibleBlocks(site);
            for (Allocation allocation : allocationsByBinding.getOrDefault(binding, List.of())) {
                if (allocation.block != null && visible.contains(allocation.block)) {
                    result.add(allocation);
                }
            }
            return result;
        }

        /** The visible producing allocations of one {@code {binding, generation}} at a site. */
        List<Allocation> visibleAllocations(BindingId binding, long generation, BlockId site) {
            List<Allocation> result = new ArrayList<>();
            for (Allocation allocation : visibleAllocations(binding, site)) {
                if (allocation.generation == generation) {
                    result.add(allocation);
                }
            }
            return result;
        }

        /** The module-region producing allocations of one {@code {binding, generation}}. */
        List<Allocation> moduleAllocations(BindingId binding, long generation) {
            List<Allocation> result = new ArrayList<>();
            BlockId moduleRegionRoot = regionRoot.get(moduleRoot);
            for (Allocation allocation : allocationsByBinding.getOrDefault(binding, List.of())) {
                if (allocation.block == null) {
                    continue;
                }
                BlockId root = regionRoot.get(allocation.block);
                if (root != null && root.equals(moduleRegionRoot)
                        && allocation.generation == generation) {
                    result.add(allocation);
                }
            }
            return result;
        }

        /** The module-region producing allocations of one binding (any generation). */
        List<Allocation> moduleAllocations(BindingId binding) {
            List<Allocation> result = new ArrayList<>();
            BlockId moduleRegionRoot = regionRoot.get(moduleRoot);
            for (Allocation allocation : allocationsByBinding.getOrDefault(binding, List.of())) {
                if (allocation.block == null) {
                    continue;
                }
                BlockId root = regionRoot.get(allocation.block);
                if (root != null && root.equals(moduleRegionRoot)) {
                    result.add(allocation);
                }
            }
            return result;
        }

        /**
         * The dominant incarnation of one binding at a site: the unique
         * maximal visible producing allocation under block dominance
         * (the innermost/latest one). Multiple maxima or none → empty.
         */
        Optional<Allocation> dominantAllocation(BindingId binding, BlockId site) {
            return dominantAmong(visibleAllocations(binding, site));
        }

        /** The unique maximal candidate under the within-region dominance order. */
        Optional<Allocation> dominantAmong(List<Allocation> candidates) {
            if (candidates.isEmpty()) {
                return Optional.empty();
            }
            List<Allocation> maxima = new ArrayList<>();
            for (Allocation candidate : candidates) {
                boolean maximal = true;
                for (Allocation other : candidates) {
                    if (candidate == other) {
                        continue;
                    }
                    if (candidate.block.equals(other.block)) {
                        maximal = false;
                        break;
                    }
                    Set<BlockId> candidateDominators =
                        dominators.getOrDefault(candidate.block, Set.of());
                    if (candidateDominators.contains(other.block)) {
                        // other ≺ candidate (other's ops dominate the
                        // candidate's): the candidate is later — still a
                        // maximal candidate relative to the other.
                        continue;
                    }
                    Set<BlockId> otherDominators =
                        dominators.getOrDefault(other.block, Set.of());
                    if (otherDominators.contains(candidate.block)) {
                        // candidate ≺ other: the candidate is earlier/outer
                        // — not the dominant incarnation.
                        maximal = false;
                        break;
                    }
                }
                if (maximal) {
                    maxima.add(candidate);
                }
            }
            if (maxima.size() != 1) {
                return Optional.empty();
            }
            return Optional.of(maxima.get(0));
        }

        /**
         * The producing allocations of one binding a capture at a site
         * may resolve to: the dominance-visible allocations minus the
         * same {@code LOOP}'s body-block incarnations when the site sits
         * in that {@code LOOP}'s init or update block. The body block is
         * a nested scope of the loop header — its per-iteration
         * incarnation (B1: the generation-1 body-top ALLOC) is out of
         * lexical scope at header sites, so an update-block or
         * condition-re-production capture resolves to the generation-0
         * counter (B1/B2: the counter incarnation is {@code DIRECT}
         * unless a closure in the condition/update captures it;
         * update/condition captures target the generation-0 counter,
         * never the per-iteration incarnation).
         */
        List<Allocation> captureCandidates(BindingId binding, BlockId site) {
            List<Allocation> candidates = new ArrayList<>(visibleAllocations(binding, site));
            SemanticOp loop = loopOfBlock.get(site);
            if (loop != null && loop.payload() instanceof KindPayload.LoopPayload payload
                    && !payload.bodyBlock().equals(site)) {
                BlockId bodyBlock = payload.bodyBlock();
                candidates.removeIf(allocation ->
                    allocation.block != null && allocation.block.equals(bodyBlock));
            }
            return candidates;
        }

        /** The dominant capture candidate of one binding at a site. */
        Optional<Allocation> dominantCaptureAllocation(BindingId binding, BlockId site) {
            return dominantAmong(captureCandidates(binding, site));
        }

        /**
         * Resolves one binding capture at a detaching op's creation site
         * under the uniform context (R1-R4), recursively along the
         * detaching chain. Empty on zero or multiple producing
         * allocations (or a generation mismatch at a chain step).
         */
        Optional<ResolvedCapture> resolveCaptureBinding(BindingId binding, SemanticOp siteOp) {
            BlockId site = blockOf(siteOp.opId());
            if (site == null) {
                return Optional.empty();
            }
            BlockId root = regionRoot.get(site);
            if (root == null) {
                return Optional.empty();
            }
            if (root.equals(moduleRoot)) {
                return dominantCaptureAllocation(binding, site)
                    .map(allocation -> new ResolvedCapture(allocation.op,
                        allocation.generation));
            }
            if (functionRoots.contains(root)) {
                List<Allocation> candidates = captureCandidates(binding, site);
                if (!candidates.isEmpty()) {
                    return dominantCaptureAllocation(binding, site)
                        .map(allocation -> new ResolvedCapture(allocation.op,
                            allocation.generation));
                }
                if (!capturesOfRegion.getOrDefault(root, List.of()).contains(binding)) {
                    return Optional.empty();
                }
                SemanticOp detaching = detachingOfFunction.get(root);
                if (detaching == null) {
                    return Optional.empty();
                }
                return resolveCaptureBinding(binding, detaching);
            }
            if (thunkRoots.contains(root)) {
                List<Allocation> candidates = captureCandidates(binding, site);
                if (!candidates.isEmpty()) {
                    return dominantCaptureAllocation(binding, site)
                        .map(allocation -> new ResolvedCapture(allocation.op,
                            allocation.generation));
                }
                BindingGeneration entry = null;
                for (BindingGeneration pinned
                        : thunkCapturesOfRegion.getOrDefault(root, List.of())) {
                    if (pinned.binding().equals(binding)) {
                        entry = pinned;
                        break;
                    }
                }
                if (entry == null) {
                    return Optional.empty();
                }
                SemanticOp detaching = detachingOfThunk.get(root);
                if (detaching == null) {
                    return Optional.empty();
                }
                Optional<ResolvedCapture> resolved = resolveCaptureBinding(binding, detaching);
                if (resolved.isEmpty() || resolved.get().generation != entry.generation()) {
                    return Optional.empty();
                }
                return resolved;
            }
            if (defaultRoots.contains(root)) {
                List<Allocation> candidates = captureCandidates(binding, site);
                if (!candidates.isEmpty()) {
                    return dominantCaptureAllocation(binding, site)
                        .map(allocation -> new ResolvedCapture(allocation.op,
                            allocation.generation));
                }
                SemanticOp detaching = detachingOfDefault.get(root);
                BlockId moduleSite = detaching == null ? null : blockOf(detaching.opId());
                if (moduleSite != null) {
                    List<Allocation> moduleCandidates = new ArrayList<>();
                    Set<BlockId> visibleBlocks = visibleBlocks(moduleSite);
                    for (Allocation allocation : moduleAllocations(binding)) {
                        if (visibleBlocks.contains(allocation.block)) {
                            moduleCandidates.add(allocation);
                        }
                    }
                    Optional<Allocation> dominant = dominantAmong(moduleCandidates);
                    if (dominant.isPresent()) {
                        return dominant.map(allocation -> new ResolvedCapture(
                            allocation.op, allocation.generation));
                    }
                }
                // An enclosing-region free reference: ISSUE-0238's boundary.
                return Optional.empty();
            }
            return dominantCaptureAllocation(binding, site)
                .map(allocation -> new ResolvedCapture(allocation.op,
                    allocation.generation));
        }

        /**
         * Resolves one {@code {binding, generation}} reference carried by
         * an op under the uniform context (R1-R4). {@code outOfScope}
         * marks a default-block enclosing-region reference (ISSUE-0238's
         * boundary — this epic validates nothing further there).
         */
        Resolution resolveReference(BindingId binding, long generation, SemanticOp carrier) {
            BlockId site = blockOf(carrier.opId());
            if (site == null) {
                return new Resolution(null, false);
            }
            BlockId root = regionRoot.get(site);
            if (root == null) {
                return new Resolution(null, false);
            }
            if (root.equals(moduleRoot)) {
                List<Allocation> matches = visibleAllocations(binding, generation, site);
                return matches.size() == 1
                    ? new Resolution(matches.get(0).op, false) : new Resolution(null, false);
            }
            if (functionRoots.contains(root)) {
                List<Allocation> matches = visibleAllocations(binding, generation, site);
                if (matches.size() == 1) {
                    return new Resolution(matches.get(0).op, false);
                }
                if (matches.size() > 1) {
                    return new Resolution(null, false);
                }
                if (!capturesOfRegion.getOrDefault(root, List.of()).contains(binding)) {
                    return new Resolution(null, false);
                }
                SemanticOp detaching = detachingOfFunction.get(root);
                if (detaching == null) {
                    return new Resolution(null, false);
                }
                Optional<ResolvedCapture> resolved = resolveCaptureBinding(binding, detaching);
                if (resolved.isEmpty() || resolved.get().generation != generation) {
                    return new Resolution(null, false);
                }
                return new Resolution(resolved.get().op, false);
            }
            if (thunkRoots.contains(root)) {
                List<Allocation> matches = visibleAllocations(binding, generation, site);
                if (matches.size() == 1) {
                    return new Resolution(matches.get(0).op, false);
                }
                if (matches.size() > 1) {
                    return new Resolution(null, false);
                }
                BindingGeneration entry = null;
                for (BindingGeneration pinned
                        : thunkCapturesOfRegion.getOrDefault(root, List.of())) {
                    if (pinned.binding().equals(binding)) {
                        entry = pinned;
                        break;
                    }
                }
                if (entry == null || entry.generation() != generation) {
                    return new Resolution(null, false);
                }
                SemanticOp detaching = detachingOfThunk.get(root);
                if (detaching == null) {
                    return new Resolution(null, false);
                }
                Optional<ResolvedCapture> resolved = resolveCaptureBinding(binding, detaching);
                if (resolved.isEmpty() || resolved.get().generation != generation) {
                    return new Resolution(null, false);
                }
                return new Resolution(resolved.get().op, false);
            }
            if (defaultRoots.contains(root)) {
                List<Allocation> matches = visibleAllocations(binding, generation, site);
                if (matches.size() == 1) {
                    return new Resolution(matches.get(0).op, false);
                }
                if (matches.size() > 1) {
                    return new Resolution(null, false);
                }
                List<Allocation> moduleMatches = moduleAllocations(binding, generation);
                if (moduleMatches.size() == 1) {
                    return new Resolution(moduleMatches.get(0).op, false);
                }
                if (moduleMatches.size() > 1) {
                    return new Resolution(null, false);
                }
                return new Resolution(null, true);
            }
            List<Allocation> matches = visibleAllocations(binding, generation, site);
            return matches.size() == 1
                ? new Resolution(matches.get(0).op, false) : new Resolution(null, false);
        }

        /** The initializing write of a resolved producing allocation, or null. */
        Write initializingWrite(Allocation allocation) {
            Write write = switch (allocation.op.payload()) {
                case KindPayload.BindingAllocPayload alloc -> allocWrite(alloc, allocation);
                case KindPayload.ForEachPayload forEach -> new Write(allocation.op);
                case KindPayload.RecursiveGroupInitPayload group -> new Write(allocation.op);
                default -> null;
            };
            return write;
        }

        /** The initializing write of an ALLOC-backed incarnation. */
        Write allocWrite(KindPayload.BindingAllocPayload alloc, Allocation allocation) {
            BindingSite site = new BindingSite(alloc.binding(), alloc.generation());
            List<SemanticOp> inits = initsBySite.get(site);
            if (inits != null && inits.size() == 1) {
                return new Write(inits.get(0));
            }
            BlockId block = allocation.block;
            if (block == null) {
                return null;
            }
            BlockId root = regionRoot.get(block);
            if (functionRoots.contains(root) && root.equals(block)) {
                // A parameter: the synthetic parameter-transfer entry
                // node immediately after the ALLOC at the body entry.
                return new Write(allocation.op);
            }
            if (isCatchBlock(block)) {
                // A catch binding: the synthetic catch-entry node
                // immediately after the ALLOC at the catch entry.
                return new Write(allocation.op);
            }
            if (root != null && root.equals(regionRoot.get(moduleRoot))) {
                // An import alias: the unique MODULE_IMPORT completion
                // whose payload names this allocation in its explicit
                // alias-cell list (the declared alias&#8596;import join
                // supersedes the declaration-order positional pairing).
                // A cell named by no completion or by two fails closed —
                // BINDING_INIT_ONCE's completion agreement arm rejects
                // the unit first; the null here stays defensive.
                List<SemanticOp> completions = completionsByCell.get(alloc.binding());
                if (completions != null && completions.size() == 1) {
                    return new Write(completions.get(0));
                }
                return null;
            }
            return null;
        }

        boolean isCatchBlock(BlockId block) {
            for (SemanticOp op : unit.ops()) {
                if (op.payload() instanceof KindPayload.TryCatchPayload payload
                        && payload.catchBlock().equals(block)) {
                    return true;
                }
            }
            return false;
        }

        /** True iff a write's completion precedes a site op (same block after, or dominating block). */
        boolean writeDominates(Write write, SemanticOp site) {
            if (write.op == null) {
                return false;
            }
            BlockId siteBlock = blockOf(site.opId());
            if (siteBlock == null) {
                return false;
            }
            BlockId writeBlock = blockOf(write.op.opId());
            if (writeBlock == null) {
                return false;
            }
            if (writeBlock.equals(siteBlock)) {
                Integer writeIndex = indexInBlock.get(write.op.opId());
                Integer siteIndex = indexInBlock.get(site.opId());
                return writeIndex != null && siteIndex != null && siteIndex > writeIndex;
            }
            Set<BlockId> siteDominators = dominators.getOrDefault(siteBlock, Set.of());
            return siteDominators.contains(writeBlock);
        }

        /** The op immediately after {@code op} in its block, or null. */
        SemanticOp nextOpInBlock(SemanticOp op) {
            BlockId block = blockOf(op.opId());
            if (block == null) {
                return null;
            }
            List<SemanticOp> ops = opsInBlock.get(block);
            Integer index = indexInBlock.get(op.opId());
            if (ops == null || index == null || index + 1 >= ops.size()) {
                return null;
            }
            return ops.get(index + 1);
        }

        /** True iff any capture reference of the three closed sets resolves to the key. */
        boolean captured(IncarnationKey key) {
            for (SemanticOp op : unit.ops()) {
                if (op.payload() instanceof KindPayload.ClosureNewPayload closure) {
                    for (BindingId binding : closure.captures()) {
                        Optional<ResolvedCapture> resolved = resolveCaptureBinding(binding, op);
                        if (resolved.isPresent() && resolvesTo(resolved.get(), key)) {
                            return true;
                        }
                    }
                }
                if (op.payload() instanceof KindPayload.FunctionAdaptPayload adapt) {
                    if (adapt.source() instanceof AdaptSourceRef.SharedCell shared) {
                        Resolution resolution = resolveReference(shared.binding(),
                            shared.generation(), op);
                        if (resolution.allocation != null
                                && allocationKeyOf(resolution.allocation) != null
                                && allocationKeyOf(resolution.allocation).equals(key)) {
                            return true;
                        }
                    }
                    if (adapt.source() instanceof AdaptSourceRef.Thunk thunk) {
                        for (BindingGeneration entry : thunk.capturedBindings()) {
                            Optional<ResolvedCapture> resolved =
                                resolveCaptureBinding(entry.binding(), op);
                            if (resolved.isPresent() && resolvesTo(resolved.get(), key)) {
                                return true;
                            }
                        }
                    }
                }
            }
            return false;
        }

        private boolean resolvesTo(ResolvedCapture resolved, IncarnationKey key) {
            if (resolved.generation != key.generation()) {
                return false;
            }
            IncarnationKey resolvedKey = allocationKeyOf(resolved.op);
            return resolvedKey != null && resolvedKey.equals(key);
        }

        private IncarnationKey allocationKeyOf(SemanticOp op) {
            return switch (op.payload()) {
                case KindPayload.BindingAllocPayload alloc -> {
                    BlockId block = blockOf(op.opId());
                    yield new IncarnationKey(alloc.binding(), alloc.generation(),
                        block != null ? block : alloc.scope());
                }
                case KindPayload.ForEachPayload forEach -> {
                    BlockId block = blockOf(op.opId());
                    yield new IncarnationKey(forEach.binding(), forEach.generation(),
                        block != null ? block : forEach.body());
                }
                default -> null;
            };
        }
    }

    // =========================================================================
    // GROUP_SHAPE
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkGroupShape(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.RecursiveGroupInitPayload group)) {
                continue;
            }
            List<BindingId> bindings = group.bindings();
            List<FunctionId> functions = group.functions();
            if (bindings.isEmpty()) {
                return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                    + " carries an empty bindings list");
            }
            if (functions.isEmpty()) {
                return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                    + " carries an empty functions list");
            }
            if (bindings.size() != functions.size()) {
                return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                    + " carries " + bindings.size() + " bindings and " + functions.size()
                    + " functions (the member lists must have the same length)");
            }
            for (FunctionId functionId : functions) {
                LoweredFunction function = model.unit.functions().get(functionId);
                if (function == null) {
                    return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                        + " member " + functionId + " has no LoweredFunction record");
                }
                Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> registry =
                    model.registryByFunction.get(functionId);
                if (registry == null) {
                    return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                        + " member " + functionId + " has no LoweredBody registration "
                        + "(exactly one per member, B5)");
                }
                FunctionExecutionBinding.LoweredBody body =
                    (FunctionExecutionBinding.LoweredBody) registry.getValue();
                if (!body.blockId().equals(function.body())) {
                    return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                        + " member " + functionId + " registration names block "
                        + body.blockId() + " but the member body is " + function.body());
                }
                int registrations = 0;
                for (FunctionExecutionBinding binding : model.unit.functionBindings()
                        .values()) {
                    if (binding instanceof FunctionExecutionBinding.LoweredBody lb
                            && lb.functionId().equals(functionId)) {
                        registrations++;
                    }
                }
                if (registrations != 1) {
                    return fail(model, GROUP_SHAPE, "the group op " + op.opId()
                        + " member " + functionId + " has " + registrations
                        + " LoweredBody registrations (exactly one per member, B5)");
                }
            }
            for (BindingId binding : bindings) {
                for (SemanticOp other : model.unit.ops()) {
                    if (other == op) {
                        continue;
                    }
                    if (other.payload() instanceof KindPayload.BindingAllocPayload alloc
                            && alloc.binding().equals(binding)) {
                        return fail(model, GROUP_SHAPE, "the group member binding " + binding
                            + " has a separate BINDING_ALLOC op " + other.opId()
                            + " (member cells are SHARED_CELL by construction, B2)");
                    }
                    if (other.payload() instanceof KindPayload.BindingInitPayload init
                            && init.binding().equals(binding)) {
                        return fail(model, GROUP_SHAPE, "the group member binding " + binding
                            + " has a separate BINDING_INIT op " + other.opId()
                            + " (members have no separate INIT, B1/B4)");
                    }
                }
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // CAPTURE_RESOLUTION
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkCaptureResolution(Model model) {
        Optional<CompilerDiagnostic> failure = checkFunctionCaptureResolution(model);
        if (failure.isPresent()) {
            return failure;
        }
        return checkThunkCaptureResolution(model);
    }

    private static Optional<CompilerDiagnostic> checkFunctionCaptureResolution(Model model) {
        for (LoweredFunction function : model.unit.functions().values()) {
            BlockId root = function.body();
            SemanticOp detaching = model.detachingOfFunction.get(root);
            // Every captures entry resolves at the detaching op's creation
            // site (a chain closing with zero or multiple producing
            // allocations is invalid).
            for (BindingId binding : function.captures()) {
                if (detaching == null) {
                    return fail(model, CAPTURE_RESOLUTION, "the body " + root + " of "
                        + function.functionId() + " has capture entries but no detaching "
                        + "op (the detaching chain cannot close)");
                }
                Optional<ResolvedCapture> resolved =
                    model.resolveCaptureBinding(binding, detaching);
                if (resolved.isEmpty()) {
                    return fail(model, CAPTURE_RESOLUTION, "the capture " + binding
                        + " of " + function.functionId() + " resolves to zero or multiple "
                        + "producing allocations at the detaching op's creation site");
                }
            }
            // Every free reference inside the body resolves own-region or
            // through exactly the captures list.
            List<BlockId> region = model.regionBlocks.getOrDefault(root, List.of());
            for (BlockId block : region) {
                List<SemanticOp> ops = model.opsInBlock.getOrDefault(block, List.of());
                for (SemanticOp op : ops) {
                    switch (op.payload()) {
                        case KindPayload.BindingLoadPayload load -> {
                            Optional<CompilerDiagnostic> membership =
                                captureMembership(model, function, load.binding(), op);
                            if (membership.isPresent()) {
                                return membership;
                            }
                        }
                        case KindPayload.BindingStorePayload store -> {
                            Optional<CompilerDiagnostic> membership =
                                captureMembership(model, function, store.binding(), op);
                            if (membership.isPresent()) {
                                return membership;
                            }
                        }
                        case KindPayload.FunctionAdaptPayload adapt -> {
                            Optional<CompilerDiagnostic> membership =
                                adaptPayloadMembership(model, function, adapt, op);
                            if (membership.isPresent()) {
                                return membership;
                            }
                        }
                        default -> {
                            // No binding reference.
                        }
                    }
                }
            }
        }
        // The CLOSURE_NEW payload surfaces: every payload capture entry
        // resolves at the op's creation site.
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.ClosureNewPayload closure)) {
                continue;
            }
            for (BindingId binding : closure.captures()) {
                Optional<ResolvedCapture> resolved =
                    model.resolveCaptureBinding(binding, op);
                if (resolved.isEmpty()) {
                    return fail(model, CAPTURE_RESOLUTION, "the CLOSURE_NEW capture "
                        + binding + " of op " + op.opId() + " resolves to zero or multiple "
                        + "producing allocations at the creation site");
                }
            }
        }
        return Optional.empty();
    }

    /** The own-region-or-captures membership check of one reference in a function body. */
    private static Optional<CompilerDiagnostic> captureMembership(Model model,
            LoweredFunction function, BindingId binding, SemanticOp carrier) {
        BlockId site = model.blockOf(carrier.opId());
        if (site == null) {
            return Optional.empty();
        }
        List<Allocation> own = model.visibleAllocations(binding, site);
        if (own.isEmpty() && !function.captures().contains(binding)) {
            return fail(model, CAPTURE_RESOLUTION, "the detached-body reference "
                + binding + " of op " + carrier.opId() + " is outside the captures "
                + "list of " + function.functionId());
        }
        return Optional.empty();
    }

    /** The SharedCell/proof payload references of an adapt op inside a function body. */
    private static Optional<CompilerDiagnostic> adaptPayloadMembership(Model model,
            LoweredFunction function, KindPayload.FunctionAdaptPayload adapt,
            SemanticOp carrier) {
        if (adapt.source() instanceof AdaptSourceRef.SharedCell shared) {
            Optional<CompilerDiagnostic> membership =
                captureMembership(model, function, shared.binding(), carrier);
            if (membership.isPresent()) {
                return membership;
            }
        }
        if (adapt.proof() != null) {
            Optional<CompilerDiagnostic> membership =
                captureMembership(model, function, adapt.proof().binding(), carrier);
            if (membership.isPresent()) {
                return membership;
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> checkThunkCaptureResolution(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.FunctionAdaptPayload adapt)
                    || !(adapt.source() instanceof AdaptSourceRef.Thunk thunk)) {
                continue;
            }
            // Every pinned entry resolves at the FUNCTION_ADAPT creation site.
            for (BindingGeneration entry : thunk.capturedBindings()) {
                Optional<ResolvedCapture> resolved =
                    model.resolveCaptureBinding(entry.binding(), op);
                if (resolved.isEmpty()) {
                    return fail(model, CAPTURE_RESOLUTION, "the thunk capture {"
                        + entry.binding() + ", " + entry.generation() + "} of op "
                        + op.opId() + " resolves to zero or multiple producing "
                        + "allocations at the creation site");
                }
            }
            // Every free reference inside the thunk block resolves through
            // exactly the pinned capturedBindings entries.
            List<BlockId> region = model.regionBlocks.getOrDefault(thunk.blockId(), List.of());
            for (BlockId block : region) {
                List<SemanticOp> ops = model.opsInBlock.getOrDefault(block, List.of());
                for (SemanticOp inner : ops) {
                    switch (inner.payload()) {
                        case KindPayload.BindingLoadPayload load -> {
                            Optional<CompilerDiagnostic> membership =
                                thunkMembership(model, thunk, load.binding(), inner);
                            if (membership.isPresent()) {
                                return membership;
                            }
                        }
                        case KindPayload.BindingStorePayload store -> {
                            Optional<CompilerDiagnostic> membership =
                                thunkMembership(model, thunk, store.binding(), inner);
                            if (membership.isPresent()) {
                                return membership;
                            }
                        }
                        case KindPayload.FunctionAdaptPayload innerAdapt -> {
                            if (innerAdapt.source() instanceof AdaptSourceRef.SharedCell
                                    shared) {
                                Optional<CompilerDiagnostic> membership =
                                    thunkMembership(model, thunk, shared.binding(), inner);
                                if (membership.isPresent()) {
                                    return membership;
                                }
                            }
                            if (innerAdapt.proof() != null) {
                                Optional<CompilerDiagnostic> membership = thunkMembership(
                                    model, thunk, innerAdapt.proof().binding(), inner);
                                if (membership.isPresent()) {
                                    return membership;
                                }
                            }
                        }
                        default -> {
                            // No binding reference.
                        }
                    }
                }
            }
        }
        return Optional.empty();
    }

    private static Optional<CompilerDiagnostic> thunkMembership(Model model,
            AdaptSourceRef.Thunk thunk, BindingId binding, SemanticOp carrier) {
        BlockId site = model.blockOf(carrier.opId());
        if (site == null) {
            return Optional.empty();
        }
        List<Allocation> own = model.visibleAllocations(binding, site);
        if (own.isEmpty()) {
            boolean pinned = false;
            for (BindingGeneration entry : thunk.capturedBindings()) {
                if (entry.binding().equals(binding)) {
                    pinned = true;
                    break;
                }
            }
            if (!pinned) {
                return fail(model, CAPTURE_RESOLUTION, "the thunk-block reference "
                    + binding + " of op " + carrier.opId() + " is outside the pinned "
                    + "capturedBindings of thunk " + thunk.blockId());
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // BINDING_GENERATION_RESOLUTION
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkBindingGenerationResolution(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            switch (op.payload()) {
                case KindPayload.BindingLoadPayload load -> {
                    Resolution resolution = model.resolveReference(load.binding(),
                        load.generation(), op);
                    if (resolution.allocation == null && !resolution.outOfScope) {
                        return fail(model, BINDING_GENERATION_RESOLUTION, "the load {"
                            + load.binding() + ", " + load.generation() + "} of op "
                            + op.opId() + " resolves to zero or multiple producing "
                            + "allocations with equal generation (stale/unresolvable)");
                    }
                }
                case KindPayload.BindingStorePayload store -> {
                    Resolution resolution = model.resolveReference(store.binding(),
                        store.generation(), op);
                    if (resolution.allocation == null && !resolution.outOfScope) {
                        return fail(model, BINDING_GENERATION_RESOLUTION, "the store {"
                            + store.binding() + ", " + store.generation() + "} of op "
                            + op.opId() + " resolves to zero or multiple producing "
                            + "allocations with equal generation (stale/unresolvable)");
                    }
                }
                case KindPayload.FunctionAdaptPayload adapt -> {
                    if (adapt.source() instanceof AdaptSourceRef.SharedCell shared) {
                        Resolution resolution = model.resolveReference(shared.binding(),
                            shared.generation(), op);
                        if (resolution.allocation == null && !resolution.outOfScope) {
                            return fail(model, BINDING_GENERATION_RESOLUTION,
                                "the SharedCell {" + shared.binding() + ", "
                                    + shared.generation() + "} of op " + op.opId()
                                    + " resolves to zero or multiple producing "
                                    + "allocations with equal generation "
                                    + "(stale/unresolvable)");
                        }
                    }
                    if (adapt.proof() != null) {
                        Resolution resolution = model.resolveReference(
                            adapt.proof().binding(), adapt.proof().generation(), op);
                        if (resolution.allocation == null && !resolution.outOfScope) {
                            return fail(model, BINDING_GENERATION_RESOLUTION,
                                "the proof {" + adapt.proof().binding() + ", "
                                    + adapt.proof().generation() + "} of op " + op.opId()
                                    + " resolves to zero or multiple producing "
                                    + "allocations with equal generation "
                                    + "(stale/unresolvable)");
                        }
                    }
                    if (adapt.source() instanceof AdaptSourceRef.Thunk thunk) {
                        for (BindingGeneration entry : thunk.capturedBindings()) {
                            Resolution resolution = model.resolveReference(
                                entry.binding(), entry.generation(), op);
                            if (resolution.allocation == null && !resolution.outOfScope) {
                                return fail(model, BINDING_GENERATION_RESOLUTION,
                                    "the thunk capture {" + entry.binding() + ", "
                                        + entry.generation() + "} of op " + op.opId()
                                        + " resolves to zero or multiple producing "
                                        + "allocations with equal generation "
                                        + "(stale/unresolvable)");
                            }
                        }
                    }
                }
                default -> {
                    // No generation-bearing reference.
                }
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // BINDING_INIT_ONCE
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkBindingInitOnce(Model model) {
        for (Map.Entry<BindingSite, List<SemanticOp>> entry
                : model.initsBySite.entrySet()) {
            List<SemanticOp> inits = entry.getValue();
            if (inits.size() != 1) {
                return fail(model, BINDING_INIT_ONCE, "the incarnation {"
                    + entry.getKey().binding() + ", " + entry.getKey().generation()
                    + "} has " + inits.size() + " BINDING_INIT ops (exactly one per "
                    + "source-declaration incarnation)");
            }
            SemanticOp init = inits.get(0);
            List<SemanticOp> allocs = model.allocsBySite.get(entry.getKey());
            if (allocs == null || allocs.size() != 1) {
                return fail(model, BINDING_INIT_ONCE, "the INIT of {" + entry.getKey()
                    .binding() + ", " + entry.getKey().generation() + "} has no unique "
                    + "producing BINDING_ALLOC (a cell written by another pinned "
                    + "initializing write — a FOR_EACH iteration binding or a group "
                    + "member — never carries a BINDING_INIT)");
            }
            SemanticOp alloc = allocs.get(0);
            BlockId initBlock = model.blockOf(init.opId());
            BlockId allocBlock = model.blockOf(alloc.opId());
            if (initBlock == null || allocBlock == null || !initBlock.equals(allocBlock)) {
                return fail(model, BINDING_INIT_ONCE, "the INIT of {" + entry.getKey()
                    .binding() + ", " + entry.getKey().generation() + "} sits in block "
                    + initBlock + " but its producing ALLOC sits in block " + allocBlock
                    + " (the INIT must be on the incarnation's block's path)");
            }
            if (model.parameters.contains(entry.getKey().binding())) {
                return fail(model, BINDING_INIT_ONCE, "the INIT of {" + entry.getKey()
                    .binding() + ", " + entry.getKey().generation()
                    + "} targets a parameter cell (the synthetic parameter-transfer "
                    + "entry write is the invoking machinery's pinned initializing "
                    + "write — a parameter never carries a BINDING_INIT)");
            }
            if (model.importAliases.contains(entry.getKey().binding())) {
                return fail(model, BINDING_INIT_ONCE, "the INIT of {" + entry.getKey()
                    .binding() + ", " + entry.getKey().generation()
                    + "} targets an import-alias cell (the MODULE_IMPORT op's "
                    + "completion write is the pinned initializing write — an import "
                    + "alias never carries a BINDING_INIT)");
            }
            for (SemanticOp other : model.unit.ops()) {
                if (other.payload() instanceof KindPayload.TryCatchPayload payload
                        && payload.catchBinding().equals(entry.getKey().binding())) {
                    return fail(model, BINDING_INIT_ONCE, "the INIT of {" + entry.getKey()
                        .binding() + ", " + entry.getKey().generation()
                        + "} targets a catch binding's cell (the catch-entry write is "
                        + "TRY_CATCH's pinned initializing write)");
                }
            }
        }
        return checkAliasCompletionAgreement(model);
    }

    /**
     * The import-alias completion agreement (the explicit-cell-list
     * discipline of {@code ModuleImportPayload.aliasCells}). The payload's
     * ordered cell list is the declared alias&#8596;import join: every
     * named cell must be an import-alias allocation of the unit, every
     * import-alias allocation must be named by exactly one
     * {@code MODULE_IMPORT} completion, and one cell never carries two
     * completions — including two resolved modules (a cell is registered
     * under exactly one module) or two kinds (a completion's
     * {@code ModuleImportKind} equals its registration entry's kind).
     * This is the completion-write half of {@code BINDING_INIT_ONCE}: the
     * completion is the pinned initializing write of the alias cell, so
     * the write exists exactly once in each direction. The agreement is
     * enforced for every unit a walk with the modules arm produced (at
     * least one completion); a unit with zero completions comes from the
     * intermediate class/binding windows, which lower module ASTs without
     * resolved import facts and carry no alias-cell recording surface.
     */
    private static Optional<CompilerDiagnostic> checkAliasCompletionAgreement(Model model) {
        if (model.moduleImports.isEmpty()) {
            // The modules arm did not run for this unit: the intermediate
            // class/binding windows lower module ASTs without resolved
            // import facts and emit no completion, so the unit carries no
            // alias-cell recording surface and its aliases stay inert
            // exactly as before this slice. The agreement below is the
            // property of every unit a walk with the modules arm produced
            // (at least one completion).
            return Optional.empty();
        }
        Set<BindingId> aliases = new LinkedHashSet<>();
        for (SemanticOp op : model.aliasAllocs) {
            aliases.add(((KindPayload.BindingAllocPayload) op.payload()).binding());
        }
        aliases.addAll(model.importAliases);
        Map<BindingId, SemanticOp> completions = new LinkedHashMap<>();
        Map<ModuleId, ModuleImportKind> entryKinds = new LinkedHashMap<>();
        for (SemanticOp op : model.moduleImports) {
            if (!(op.payload() instanceof KindPayload.ModuleImportPayload payload)) {
                continue; // the closed kind mapping guarantees this; defensive
            }
            ModuleImportKind entryKind = entryKinds.putIfAbsent(payload.resolvedModule(),
                payload.kind());
            if (entryKind != null && entryKind != payload.kind()) {
                return fail(model, BINDING_INIT_ONCE, "the MODULE_IMPORT completion of "
                    + payload.resolvedModule() + " carries the kind " + payload.kind()
                    + " but the module's registration entry kind is " + entryKind
                    + " (a completion's kind equals its entry's kind)");
            }
            for (BindingId cell : payload.aliasCells()) {
                if (!aliases.contains(cell)) {
                    return fail(model, BINDING_INIT_ONCE, "the MODULE_IMPORT op "
                        + op.opId() + " of " + payload.resolvedModule() + " names the cell "
                        + cell + " which is not an import-alias allocation of the unit "
                        + "(a completion names import-alias cells only)");
                }
                SemanticOp previous = completions.putIfAbsent(cell, op);
                if (previous != null) {
                    KindPayload.ModuleImportPayload previousPayload =
                        (KindPayload.ModuleImportPayload) previous.payload();
                    if (!previousPayload.resolvedModule().equals(payload.resolvedModule())) {
                        return fail(model, BINDING_INIT_ONCE, "the cell " + cell
                            + " is named by the MODULE_IMPORT completions of two modules ("
                            + previousPayload.resolvedModule() + " and "
                            + payload.resolvedModule()
                            + "; a cell is registered under exactly one module)");
                    }
                    return fail(model, BINDING_INIT_ONCE, "the cell " + cell
                        + " is named by two MODULE_IMPORT completions (exactly one pinned "
                        + "initializing write per import-alias allocation)");
                }
            }
        }
        for (BindingId alias : aliases) {
            if (!completions.containsKey(alias)) {
                return fail(model, BINDING_INIT_ONCE, "the import-alias allocation " + alias
                    + " is named by no MODULE_IMPORT completion (the completion write is "
                    + "the import alias's pinned initializing write)");
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // INIT_DOMINATES_LOAD
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkInitDominatesLoad(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.BindingLoadPayload load)) {
                continue;
            }
            Resolution resolution = model.resolveReference(load.binding(),
                load.generation(), op);
            if (resolution.outOfScope) {
                continue; // ISSUE-0238's boundary; nothing further is validated
            }
            if (resolution.allocation == null) {
                continue; // BINDING_GENERATION_RESOLUTION rejected this first
            }
            Allocation allocation = null;
            for (Allocation candidate : model.allocationsByBinding.getOrDefault(
                    load.binding(), List.of())) {
                if (candidate.op == resolution.allocation) {
                    allocation = candidate;
                    break;
                }
            }
            if (allocation == null) {
                return fail(model, INIT_DOMINATES_LOAD, "the load {" + load.binding() + ", "
                    + load.generation() + "} of op " + op.opId() + " resolves to an "
                    + "unknown producing allocation");
            }
            Write write = model.initializingWrite(allocation);
            if (write == null) {
                return fail(model, INIT_DOMINATES_LOAD, "the load {" + load.binding() + ", "
                    + load.generation() + "} of op " + op.opId() + " names an "
                    + "incarnation with no initializing write (an uninitialized cell "
                    + "has no defined read)");
            }
            Set<String> visited = new LinkedHashSet<>();
            if (!loadValid(model, allocation, write, load.binding(), load.generation(), op,
                    false, visited)) {
                return fail(model, INIT_DOMINATES_LOAD, "the load {" + load.binding() + ", "
                    + load.generation() + "} of op " + op.opId() + " is not dominated by "
                    + "its incarnation's initializing write (a load dominated only by "
                    + "the producing ALLOC reads an uninitialized cell)");
            }
        }
        return Optional.empty();
    }

    /**
     * The INIT_DOMINATES_LOAD validity rule (B9 arms 1-3 plus the three
     * terminating arms) at one site: arm 1 inline dominance over the
     * structured block graph (intra-LOOP edges included), arm 2
     * own-region dominance inside a detached block's own subgraph, and
     * arm 3 creation-site dominance transitively along the detaching
     * chain terminated by the size-1 SCC own-name arm, the group
     * publication arm, and the module-init completion arm (incl.
     * per-construction default blocks).
     */
    private static boolean loadValid(Model model, Allocation allocation,
                                     Write write, BindingId binding, long generation,
                                     SemanticOp site, boolean viaChain,
                                     Set<String> visited) {
        BlockId siteBlock = model.blockOf(site.opId());
        if (siteBlock == null) {
            return false;
        }
        BlockId root = model.regionRoot.get(siteBlock);
        if (root == null) {
            return false;
        }
        if (root.equals(model.moduleRoot)) {
            // Arm 1 at a plain/structured site: the write must dominate.
            // At a chain step the module-init-completion arm terminates
            // the recursion when the write sits in the module region
            // (bodies/thunks/defaults execute only after init completes).
            return model.writeDominates(write, site)
                || viaChain && moduleCompletion(model, write);
        }
        if (model.functionRoots.contains(root)) {
            if (allocation.block != null
                    && (model.regionBlocks.getOrDefault(root, List.of())
                        .contains(allocation.block) || root.equals(allocation.block))) {
                // Arm 2: the incarnation's own region contains the site.
                return model.writeDominates(write, site);
            }
            // Arm 3: a captured detached load.
            if (ownNameTerminates(model, root, binding, generation)) {
                return true;
            }
            if (groupPublicationTerminates(model, allocation, root)) {
                return true;
            }
            if (moduleCompletion(model, write)) {
                return true;
            }
            String key = root + "|" + allocation.op.opId().id() + "|"
                + binding.id() + "|" + generation;
            if (!visited.add(key)) {
                return false; // a detaching chain cycle
            }
            SemanticOp detaching = model.detachingOfFunction.get(root);
            if (detaching == null) {
                return false;
            }
            return loadValid(model, allocation, write, binding, generation, detaching,
                true, visited);
        }
        if (model.thunkRoots.contains(root)) {
            if (allocation.block != null
                    && (model.regionBlocks.getOrDefault(root, List.of())
                        .contains(allocation.block) || root.equals(allocation.block))) {
                return model.writeDominates(write, site);
            }
            if (groupPublicationTerminates(model, allocation, root)) {
                return true;
            }
            if (moduleCompletion(model, write)) {
                return true;
            }
            String key = root + "|" + allocation.op.opId().id() + "|"
                + binding.id() + "|" + generation;
            if (!visited.add(key)) {
                return false;
            }
            SemanticOp detaching = model.detachingOfThunk.get(root);
            if (detaching == null) {
                return false;
            }
            return loadValid(model, allocation, write, binding, generation, detaching,
                true, visited);
        }
        if (model.defaultRoots.contains(root)) {
            if (allocation.block != null
                    && (model.regionBlocks.getOrDefault(root, List.of())
                        .contains(allocation.block) || root.equals(allocation.block))) {
                return model.writeDominates(write, site);
            }
            if (allocation.block != null && model.regionRoot.get(allocation.block) != null
                    && model.regionRoot.get(allocation.block)
                        .equals(model.regionRoot.get(model.moduleRoot))) {
                // The module-level arm: default execution happens only at
                // construction sites after module init completes.
                return true;
            }
            // An enclosing-region free reference: ISSUE-0238's boundary.
            return true;
        }
        // Any other region root (e.g., a CALL body block): plain dominance
        // within that region.
        return model.writeDominates(write, site);
    }

    /**
     * The size-1 SCC own-name terminating arm: the load is of the
     * declared function's own name inside its own body, the detaching
     * op is {@code CLOSURE_NEW(f)} at the declaration, and
     * {@code BINDING_INIT(f)} is the declaration's immediate commit
     * after it (B4) — no call can observe the half-published value.
     */
    private static boolean ownNameTerminates(Model model, BlockId root, BindingId binding,
                                             long generation) {
        SemanticOp detaching = model.detachingOfFunction.get(root);
        if (detaching == null || detaching.kind() != SemanticOpKind.CLOSURE_NEW) {
            return false;
        }
        SemanticValue result = detaching.result();
        if (!(result instanceof ValueId closureValue)) {
            return false;
        }
        SemanticOp next = model.nextOpInBlock(detaching);
        if (next == null || next.kind() != SemanticOpKind.BINDING_INIT) {
            return false;
        }
        KindPayload.BindingInitPayload init =
            (KindPayload.BindingInitPayload) next.payload();
        return init.binding().equals(binding) && init.generation() == generation
            && init.value() != null && init.value().equals(closureValue);
    }

    /**
     * The group-publication terminating arm: the load is of a member
     * binding inside a member body of the producing
     * {@code RECURSIVE_GROUP_INIT} — the publication phase is attached
     * to the group op's own completion and precedes every member-body
     * execution.
     */
    private static boolean groupPublicationTerminates(Model model, Allocation allocation,
                                                      BlockId root) {
        if (!(allocation.op.payload() instanceof KindPayload.RecursiveGroupInitPayload)) {
            return false;
        }
        List<BlockId> bodies = model.memberBodies.get(allocation.op.opId());
        return bodies != null && bodies.contains(root);
    }

    /** The module-init completion terminating arm (incl. per-construction defaults). */
    private static boolean moduleCompletion(Model model, Write write) {
        if (write == null || write.op == null) {
            return false;
        }
        BlockId block = model.blockOf(write.op.opId());
        if (block == null) {
            return false;
        }
        BlockId root = model.regionRoot.get(block);
        return root != null && root.equals(model.regionRoot.get(model.moduleRoot));
    }

    // =========================================================================
    // ADAPTER_PAIR
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkAdapterPair(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.FunctionAdaptPayload adapt)) {
                continue;
            }
            if (!AdapterCreationRule.assignableButNotExact(adapt.sourceSignature(),
                    adapt.targetSignature())) {
                return fail(model, ADAPTER_PAIR, "the FUNCTION_ADAPT op " + op.opId()
                    + " pair " + adapt.sourceSignature().canonicalSpecText() + " → "
                    + adapt.targetSignature().canonicalSpecText() + " does not re-derive "
                    + "as assignable-but-not-exact (identical async marker, identical "
                    + "return type, M <= N with exactly equal leading M parameter types "
                    + "and M < N)");
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // ADAPTER_SOURCE_SHAPE
    // =========================================================================

    private static Optional<CompilerDiagnostic> checkAdapterSourceShape(Model model) {
        ProductionFacts facts = null;
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.FunctionAdaptPayload adapt)) {
                continue;
            }
            CaptureMode mode = adapt.mode();
            AdaptSourceRef source = adapt.source();
            boolean shapeMatches = switch (mode) {
                case SHARED_CELL -> source instanceof AdaptSourceRef.SharedCell;
                case REEVALUATE_THUNK -> source instanceof AdaptSourceRef.Thunk;
                case VALUE -> source instanceof AdaptSourceRef.Value;
            };
            if (!shapeMatches) {
                return fail(model, ADAPTER_SOURCE_SHAPE, "the FUNCTION_ADAPT op "
                    + op.opId() + " mode " + mode + " carries the source shape "
                    + source.getClass().getSimpleName() + " (mode must match the source "
                    + "shape: SHARED_CELL↔SharedCell, REEVALUATE_THUNK↔Thunk, "
                    + "VALUE↔Value)");
            }
            if (mode == CaptureMode.VALUE) {
                if (op.operands().size() != 1) {
                    return fail(model, ADAPTER_SOURCE_SHAPE, "the VALUE adapter op "
                        + op.opId() + " carries " + op.operands().size()
                        + " operands (VALUE carries exactly one operand)");
                }
                ValueId operand = op.operands().get(0);
                if (facts == null) {
                    facts = productionFacts(model);
                }
                // The VALUE-over-intrinsic exemption (the intrinsic-load
                // refinement): the adapted declaration's operand is the
                // seeded intrinsic identity itself — the shape map's
                // intrinsic arm wires the identity, never a load of a user
                // binding — so a value-position load of the same intrinsic
                // elsewhere in the unit (an identity-preserving load of the
                // seeded binding) does not turn it into a load operand. The
                // exemption is closed to that operand shape: a proof
                // recorded for it must name the seeded binding/generation,
                // and every other VALUE operand keeps the landed proof
                // rule.
                if (seedAdmittedIntrinsicKey(model, facts, operand.id())) {
                    BindingSite seeded = facts.seedInitsOf().get(operand.id());
                    if (adapt.proof() != null
                            && (seeded == null
                                || !adapt.proof().binding().equals(seeded.binding())
                                || adapt.proof().generation() != seeded.generation())) {
                        return fail(model, ADAPTER_SOURCE_SHAPE, "the VALUE adapter op "
                            + op.opId() + " over the seeded intrinsic identity " + operand
                            + " carries proof {" + adapt.proof().binding() + ", "
                            + adapt.proof().generation() + "} naming no seeded binding/"
                            + "generation (a proof over the intrinsic function value must "
                            + "name the seeded binding/generation)");
                    }
                    continue;
                }
                List<SemanticOp> producingLoads = new ArrayList<>();
                List<SemanticOp> producingOthers = new ArrayList<>();
                for (SemanticOp other : model.unit.ops()) {
                    if (other.result() instanceof ValueId value && value.equals(operand)) {
                        if (other.kind() == SemanticOpKind.BINDING_LOAD) {
                            producingLoads.add(other);
                        } else {
                            producingOthers.add(other);
                        }
                    }
                }
                if (producingLoads.isEmpty()) {
                    if (adapt.proof() != null) {
                        return fail(model, ADAPTER_SOURCE_SHAPE, "the VALUE adapter op "
                            + op.opId() + " carries a proof over a non-load operand "
                            + "(proof is present iff VALUE's operand is a binding load)");
                    }
                } else if (adapt.proof() == null) {
                    // A pure binding-load operand without its proof is
                    // VALUE-over-binding without the recorded proof; an
                    // operand a closure also publishes is an ordinary
                    // identity-preservation flow (loads publish the cell's
                    // tracked identity), so a mixed production set is not
                    // proof-requiring at this level.
                    if (producingOthers.isEmpty()) {
                        return fail(model, ADAPTER_SOURCE_SHAPE, "the VALUE adapter op "
                            + op.opId() + " carries a binding-load operand " + operand
                            + " without its proof (VALUE over a binding is admissible "
                            + "only with the recorded BindingImmutabilityProof naming "
                            + "the loaded binding/generation)");
                    }
                } else {
                    // Identity preservation: a load publishes the cell's
                    // tracked function identity, so several bindings
                    // holding the same identity produce loads with the
                    // same result — the proof must name at least one of
                    // the loaded {binding, generation} pairs.
                    boolean proofMatches = false;
                    for (SemanticOp producingLoad : producingLoads) {
                        KindPayload.BindingLoadPayload candidate =
                            (KindPayload.BindingLoadPayload) producingLoad.payload();
                        if (adapt.proof().binding().equals(candidate.binding())
                                && adapt.proof().generation() == candidate.generation()) {
                            proofMatches = true;
                            break;
                        }
                    }
                    if (!proofMatches) {
                        return fail(model, ADAPTER_SOURCE_SHAPE, "the VALUE adapter op "
                            + op.opId() + " over the binding-load operand " + operand
                            + " carries proof {" + adapt.proof().binding() + ", "
                            + adapt.proof().generation() + "} naming no producing load "
                            + "(the proof must name the loaded binding/generation)");
                    }
                }
            } else {
                if (!op.operands().isEmpty()) {
                    return fail(model, ADAPTER_SOURCE_SHAPE, "the " + mode + " adapter op "
                        + op.opId() + " carries " + op.operands().size()
                        + " operands (SHARED_CELL/REEVALUATE_THUNK carry no operand)");
                }
                if (adapt.proof() != null) {
                    return fail(model, ADAPTER_SOURCE_SHAPE, "the " + mode + " adapter op "
                        + op.opId() + " carries a proof (SHARED_CELL/REEVALUATE_THUNK "
                        + "carry no proof)");
                }
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // REGISTRY_ONE_TO_ONE
    // =========================================================================

    /**
     * The producing-position facts of one unit: the shared input of the
     * {@code REGISTRY_ONE_TO_ONE} clauses and of the
     * {@code ADAPTER_SOURCE_SHAPE} VALUE-over-intrinsic exemption.
     *
     * @param closureProductions    CLOSURE_NEW results per key
     * @param adaptProductions      FUNCTION_ADAPT results per key
     * @param groupProductions      RECURSIVE_GROUP_INIT member identities per key
     * @param memberReadProductions member-read result identities per key
     * @param exportReadProductions EXPORT_READ value identities per key
     * @param boundaryInputs        every HOST_TO_DEAL crossing input per key
     * @param functionBoundaryInputs the function-typed HOST_TO_DEAL crossing inputs per key
     * @param seedInits             the producer-less seed BINDING_INITs per operand identity
     * @param seedInitsOf           the {@code {binding, generation}} of the seed init of an
     *                              init operand identity (the first, diagnostic-order entry)
     * @param preservedCells        the cell an identity-preserving load of a seeded identity
     *                              reads (that identity's seeded binding/generation)
     * @param preservedInits        the BINDING_INITs landing on a preserved cell per identity
     *                              (the seed write; the other inits over the identity are the
     *                              declaration's re-publications of it)
     * @param producingValues       every identity produced by an op of the unit under the
     *                              identity-preserving-load exclusion
     */
    private record ProductionFacts(
            Map<Long, Integer> closureProductions,
            Map<Long, Integer> adaptProductions,
            Map<Long, Integer> groupProductions,
            Map<Long, Integer> memberReadProductions,
            Map<Long, Integer> exportReadProductions,
            Map<Long, Integer> boundaryInputs,
            Map<Long, Integer> functionBoundaryInputs,
            Map<Long, Integer> seedInits,
            Map<Long, BindingSite> seedInitsOf,
            Map<Long, BindingSite> preservedCells,
            Map<Long, Integer> preservedInits,
            Set<Long> producingValues) {

        /** The DEAL-op production count of one key (closure, adapt, group, and read positions). */
        int dealProductions(long key) {
            return closureProductions.getOrDefault(key, 0)
                + adaptProductions.getOrDefault(key, 0)
                + groupProductions.getOrDefault(key, 0)
                + memberReadProductions.getOrDefault(key, 0)
                + exportReadProductions.getOrDefault(key, 0);
        }

        /**
         * The static producing positions of a key whose registration is
         * {@code DynamicFunctionValue}: a closure, group, or adapt
         * production or an {@code EXPORT_READ} value. A member read with a
         * function-typed result is one of the dynamic producer arms (the
         * read allocates the identity the dynamic record keys), so it is
         * not a static producing position.
         */
        int staticProductions(long key) {
            return closureProductions.getOrDefault(key, 0)
                + adaptProductions.getOrDefault(key, 0)
                + groupProductions.getOrDefault(key, 0)
                + exportReadProductions.getOrDefault(key, 0);
        }
    }

    /**
     * The producing positions of the unit's identities. The producer-less
     * test of the intrinsic-seed clauses carries the identity-preserving
     * load exclusion (the intrinsic-load refinement): a
     * {@code BINDING_LOAD} whose result identity is an already-allocated
     * identity of the cell it names — the cell's {@code BINDING_INIT}
     * carries that identity — is not a producing position; the load
     * republishes an identity the cell already holds. The exclusion is
     * closed: every non-load op result stays a producing position (a
     * closure, adapt, group, read, or call production of the seeded
     * identity also stays one), and a load naming a cell whose init carries
     * another identity (a parameter, catch, or iteration cell, or a
     * dynamically allocated identity tracked into a later cell) stays one,
     * so the seeded operand's seed clause fails closed for them while the
     * seeded identity's alias loads (the alias declaration's
     * re-publication) stay identity-preserving. The seed writes of an
     * identity a preserved load publishes are the inits landing on the
     * loaded (seeded) cell: a later {@code BINDING_INIT} storing the same
     * identity into another binding's cell is the declaration's
     * re-publication of the one seed write, not a second seed write.
     */
    private static ProductionFacts productionFacts(Model model) {
        // Production counts per key: CLOSURE_NEW results, FUNCTION_ADAPT
        // results, group members, member/export reads, and HOST_TO_DEAL
        // boundary inputs (the producing host crossing).
        Map<Long, Integer> closureProductions = new LinkedHashMap<>();
        Map<Long, Integer> adaptProductions = new LinkedHashMap<>();
        Map<Long, Integer> groupProductions = new LinkedHashMap<>();
        Map<Long, Integer> memberReadProductions = new LinkedHashMap<>();
        Map<Long, Integer> exportReadProductions = new LinkedHashMap<>();
        Map<Long, Integer> boundaryInputs = new LinkedHashMap<>();
        Map<Long, Integer> functionBoundaryInputs = new LinkedHashMap<>();
        // Every value identity produced by an op that is not a
        // BINDING_LOAD: the seed init candidates' operand test (a seed
        // init's operand is the result of no op other than an
        // identity-preserving load of that init's own cell).
        Set<Long> nonLoadProducedValues = new LinkedHashSet<>();
        List<SemanticOp> loads = new ArrayList<>();
        for (SemanticOp op : model.unit.ops()) {
            switch (op.kind()) {
                case CLOSURE_NEW -> {
                    if (op.result() instanceof ValueId value) {
                        closureProductions.merge(value.id(), 1, Integer::sum);
                    }
                }
                case FUNCTION_ADAPT -> {
                    if (op.result() instanceof ValueId value) {
                        adaptProductions.merge(value.id(), 1, Integer::sum);
                    }
                }
                case MEMBER_READ -> {
                    if (op.result() instanceof ValueId value) {
                        memberReadProductions.merge(value.id(), 1, Integer::sum);
                    }
                }
                case EXPORT_READ -> {
                    if (op.payload() instanceof KindPayload.ExportReadPayload export) {
                        exportReadProductions.merge(export.value().id(), 1, Integer::sum);
                    }
                }
                case BOUNDARY -> {
                    // Only the producing host crossings count toward a
                    // HostFunctionValue key's exactly-one requirement:
                    // loads/reads/argument passing/returns preserve
                    // allocation identity, so a later crossing of the
                    // same identity through any other boundary kind is
                    // an ordinary identity-preserving flow, not a
                    // production.
                    if (op.payload() instanceof KindPayload.BoundaryPayload boundary
                            && boundary.kind() == BoundaryKind.HOST_TO_DEAL) {
                        boundaryInputs.merge(boundary.input().id(), 1, Integer::sum);
                        if (boundary.descriptor() instanceof RuntimeDescriptor.Func) {
                            functionBoundaryInputs.merge(boundary.input().id(), 1,
                                Integer::sum);
                        }
                    }
                }
                default -> {
                    // No producing position.
                }
            }
            if (op.result() instanceof ValueId produced) {
                if (op.kind() == SemanticOpKind.BINDING_LOAD) {
                    loads.add(op);
                } else {
                    nonLoadProducedValues.add(produced.id());
                }
            }
        }
        for (SemanticOp op : model.unit.ops()) {
            if (op.payload() instanceof KindPayload.RecursiveGroupInitPayload group) {
                for (FunctionId functionId : group.functions()) {
                    Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry =
                        model.registryByFunction.get(functionId);
                    if (entry != null) {
                        groupProductions.merge(entry.getKey().id(), 1, Integer::sum);
                    }
                }
            }
        }
        // The seed init candidates: a BINDING_INIT whose operand identity is
        // the result of no op other than an identity-preserving load of that
        // init's own cell.
        Map<Long, BindingSite> seedInitsOf = new LinkedHashMap<>();
        for (SemanticOp op : model.unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && !nonLoadProducedValues.contains(init.value().id())) {
                seedInitsOf.putIfAbsent(init.value().id(),
                    new BindingSite(init.binding(), init.generation()));
            }
        }
        // The identity-preserving loads: a BINDING_LOAD whose result
        // identity is an already-allocated identity of the cell it names —
        // the cell's BINDING_INIT carries that identity. The preservation
        // decision is per publishing op and closed (ISSUE-0675): a load
        // naming a cell whose init carries another identity (a parameter,
        // catch, or iteration cell, or a dynamically allocated identity
        // tracked into a later cell) is a producing position, even when
        // another load over the same identity preserves it — the exclusion
        // admits only identities every publishing load of which republishes
        // a cell's already-allocated identity. The alias declaration's
        // re-publication (a BINDING_INIT storing the seeded identity into
        // another binding's cell) makes the alias load read the seeded
        // identity, so the seed's alias loads stay identity-preserving
        // (J1's alias-load refinement) while the allocating load of a
        // dynamically allocated identity stays a producing position. The
        // loaded cell is recorded per identity when it is the identity's
        // candidate seed cell (the seed write's cell): a later BINDING_INIT
        // storing the same identity into another binding's cell is the
        // alias declaration's re-publication of the seed write, not a
        // second seed write.
        Map<BindingSite, Set<Long>> initOperandsByCell = new LinkedHashMap<>();
        for (SemanticOp op : model.unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init) {
                initOperandsByCell
                    .computeIfAbsent(new BindingSite(init.binding(), init.generation()),
                        cell -> new LinkedHashSet<>())
                    .add(init.value().id());
            }
        }
        Set<Long> producingValues = new LinkedHashSet<>(nonLoadProducedValues);
        Map<Long, BindingSite> preservedCells = new LinkedHashMap<>();
        for (SemanticOp op : loads) {
            if (!(op.result() instanceof ValueId produced)
                    || !(op.payload() instanceof KindPayload.BindingLoadPayload load)) {
                continue;
            }
            Set<Long> carried = initOperandsByCell.get(
                new BindingSite(load.binding(), load.generation()));
            if (carried == null || !carried.contains(produced.id())) {
                // The load allocates its own identity: the named cell's
                // init does not carry it (the producing position).
                producingValues.add(produced.id());
                continue;
            }
            BindingSite seed = seedInitsOf.get(produced.id());
            if (seed != null && seed.binding().equals(load.binding())
                    && seed.generation() == load.generation()) {
                preservedCells.putIfAbsent(produced.id(), seed);
            }
        }
        // The seed writes per producer-less init operand: one BINDING_INIT
        // per admitted seeded key, counted for the admission/converse
        // clauses below. The preserved inits are the writes landing on the
        // cell an identity-preserving load reads (the seeded binding's own
        // cell): the seed write of an identity a preserved load publishes
        // is exactly one of those, while a later BINDING_INIT storing the
        // same identity into another binding's cell is the alias
        // declaration's re-publication of the seed write, not a second
        // seed write.
        Map<Long, Integer> seedInits = new LinkedHashMap<>();
        Map<Long, Integer> preservedInits = new LinkedHashMap<>();
        for (SemanticOp op : model.unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && !producingValues.contains(init.value().id())) {
                seedInits.merge(init.value().id(), 1, Integer::sum);
                BindingSite seededCell = preservedCells.get(init.value().id());
                if (seededCell != null
                        && seededCell.binding().equals(init.binding())
                        && seededCell.generation() == init.generation()) {
                    preservedInits.merge(init.value().id(), 1, Integer::sum);
                }
            }
        }
        return new ProductionFacts(closureProductions, adaptProductions, groupProductions,
            memberReadProductions, exportReadProductions, boundaryInputs,
            functionBoundaryInputs, seedInits, seedInitsOf, preservedCells,
            preservedInits, producingValues);
    }

    /**
     * True iff the identity is a seed-admitted intrinsic key: the unit's
     * registration is an {@code IntrinsicFunction} carrying the kind's
     * pinned declared signature, exactly one seed {@code BINDING_INIT}
     * carries the identity as its operand, the identity contributes no
     * other producing position (no closure/adapt/group/read production and
     * no function-typed host crossing), and every op publishing it is an
     * identity-preserving load of the seeded binding (or no op publishes
     * it at all). The operand of such a key is the intrinsic function
     * value itself, never a load of a user binding.
     */
    private static boolean seedAdmittedIntrinsicKey(Model model, ProductionFacts facts,
                                                    long key) {
        if (facts.dealProductions(key) != 0
                || facts.functionBoundaryInputs().getOrDefault(key, 0) != 0
                || facts.seedInits().getOrDefault(key, 0) != 1
                || facts.producingValues().contains(key)) {
            return false;
        }
        return model.unit.functionBindings()
                .get(new FunctionAllocationIdentity(key))
                instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic
            && intrinsic.descriptor().equals(intrinsic.kind().declaredSignature());
    }

    private static Optional<CompilerDiagnostic> checkRegistryOneToOne(Model model) {
        ProductionFacts facts = productionFacts(model);
        Map<Long, Integer> boundaryInputs = facts.boundaryInputs();
        Map<Long, Integer> seedInits = facts.seedInits();
        // Every registry key is produced by exactly one producing
        // allocation (or one host crossing), or — for the producer-less
        // intrinsic seed — by exactly one seed BINDING_INIT and no other
        // producing position; a dynamic registration names its single
        // producing op and carries no static producing position.
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : model.unit.functionBindings().entrySet()) {
            long key = entry.getKey().id();
            int count = facts.dealProductions(key);
            if (entry.getValue() instanceof FunctionExecutionBinding.HostFunctionValue) {
                int boundaryCount = boundaryInputs.getOrDefault(key, 0);
                if (count != 0 || boundaryCount != 1) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the HostFunctionValue key "
                        + entry.getKey() + " is produced by " + count + " DEAL op(s) and "
                        + boundaryCount + " host crossing(s) (exactly one producing host "
                        + "crossing per HostFunctionValue registration)");
                }
            } else if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic) {
                // The intrinsic-seed admission (D13): a key whose binding
                // is IntrinsicFunction is admissible exactly when the
                // unit carries exactly one seed BINDING_INIT whose init
                // operand is that key and the key contributes no other
                // producing position (no closure/adapt/group/read
                // production and no host crossing). The seed write is the
                // BINDING_INIT of the seeded binding's own cell when an
                // identity-preserving load of the key publishes it: a
                // later BINDING_INIT storing the same identity into
                // another binding's cell is the declaration's
                // re-publication of the seed write and is not counted as
                // a second seed write.
                int seedCount = seedInits.getOrDefault(key, 0);
                int boundaryCount = boundaryInputs.getOrDefault(key, 0);
                BindingSite seededCell = facts.preservedCells().get(key);
                int seedWrites = seededCell == null ? seedCount
                    : facts.preservedInits().getOrDefault(key, 0);
                if (count != 0 || boundaryCount != 0 || seedWrites != 1) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the IntrinsicFunction key "
                        + entry.getKey() + " is produced by " + count + " producing op(s), "
                        + boundaryCount + " host crossing(s), and " + seedCount
                        + " seed BINDING_INIT(s) (exactly one seed BINDING_INIT whose init "
                        + "operand is that key, and no other producing position, per "
                        + "producer-less intrinsic registration)");
                }
                // The pinned declared signature: the closed (kind,
                // descriptor) pair of the registration.
                if (!intrinsic.descriptor().equals(intrinsic.kind().declaredSignature())) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the IntrinsicFunction key "
                        + entry.getKey() + " carries the pair (" + intrinsic.kind()
                        + ", " + intrinsic.descriptor().canonicalSpecText()
                        + ") which is not the kind's pinned declared signature ("
                        + intrinsic.kind().declaredSignature().canonicalSpecText() + ")");
                }
            } else if (entry.getValue() instanceof FunctionExecutionBinding.DynamicFunctionValue
                    dynamic) {
                // The dynamic-materialization admission: a key whose
                // binding is DynamicFunctionValue is admissible exactly
                // when the op its record names produces that key identity
                // and the key carries no static producing position (no
                // closure/group/adapt/export-read production, no
                // function-typed HOST_TO_DEAL crossing input, and no
                // producer-less seed BINDING_INIT operand). A member read
                // with a function-typed result is one of the dynamic
                // producer arms, not a static position.
                int staticCount = facts.staticProductions(key);
                int boundaryCount = facts.functionBoundaryInputs().getOrDefault(key, 0);
                int seedCount = seedInits.getOrDefault(key, 0);
                if (staticCount != 0 || boundaryCount != 0 || seedCount != 0) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the DynamicFunctionValue key "
                        + entry.getKey() + " is produced by " + staticCount + " static "
                        + "producing op(s) (a closure, group, adapt, or export-read "
                        + "production), " + boundaryCount + " function-typed host "
                        + "crossing(s), and " + seedCount + " seed BINDING_INIT(s) (a "
                        + "dynamic registration resolves its execution class from the "
                        + "materialized carrier at execution, so its key carries no static "
                        + "producing position)");
                }
                SemanticOp producing = null;
                for (SemanticOp op : model.unit.ops()) {
                    if (op.opId().equals(dynamic.materializingOpId())) {
                        producing = op;
                        break;
                    }
                }
                if (producing == null) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the DynamicFunctionValue key "
                        + entry.getKey() + " names materializing op "
                        + dynamic.materializingOpId() + ", which is no op of the unit (the "
                        + "recorded op is the registration's producing position)");
                }
                ValueId identity = producing.result() instanceof ValueId value ? value : null;
                if (identity == null || identity.id() != key) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the DynamicFunctionValue key "
                        + entry.getKey() + " names materializing op "
                        + dynamic.materializingOpId() + " whose result identity is not "
                        + "that key (the recorded op is the registration's producing "
                        + "position)");
                }
            } else {
                if (count != 1) {
                    return fail(model, REGISTRY_ONE_TO_ONE, "the key " + entry.getKey()
                        + " is produced by " + count + " producing op(s) (exactly one "
                        + "producing allocation per registration)");
                }
            }
        }
        // The converse clause: every BINDING_INIT whose init operand
        // identity is the result of no op of the unit (the
        // identity-preserving loads of the seeded binding excluded) must
        // be keyed by exactly one IntrinsicFunction registration in the
        // same unit and must not be any HOST_TO_DEAL crossing input — the
        // seed surface is the only admitted producer-less key.
        for (Map.Entry<Long, Integer> entry : seedInits.entrySet()) {
            FunctionAllocationIdentity identity =
                new FunctionAllocationIdentity(entry.getKey());
            if (boundaryInputs.getOrDefault(entry.getKey(), 0) != 0) {
                return fail(model, REGISTRY_ONE_TO_ONE, "the producer-less BINDING_INIT "
                    + "operand " + identity + " is a HOST_TO_DEAL crossing input (the "
                    + "seed surface is the only admitted producer-less key; a host-"
                    + "materialized function value registers a HostFunctionValue at "
                    + "its producing crossing)");
            }
            FunctionExecutionBinding binding = model.unit.functionBindings().get(identity);
            if (!(binding instanceof FunctionExecutionBinding.IntrinsicFunction)) {
                return fail(model, REGISTRY_ONE_TO_ONE, "the BINDING_INIT operand "
                    + identity + " is the result of no op of the unit and is keyed by "
                    + (binding == null ? "no registration" : ("the " + binding.getClass()
                        .getSimpleName() + " registration"))
                    + " (a producer-less init operand is admissible only under exactly one "
                    + "IntrinsicFunction registration)");
            }
            if (entry.getValue() != 1
                    && (facts.preservedCells().get(entry.getKey()) == null
                        || facts.preservedInits().getOrDefault(entry.getKey(), 0) != 1)) {
                return fail(model, REGISTRY_ONE_TO_ONE, "the producer-less init operand "
                    + identity + " carries " + entry.getValue() + " seed BINDING_INIT "
                    + "op(s) (exactly one seed init per admitted intrinsic key)");
            }
        }
        // Every producing allocation registers exactly one binding.
        for (SemanticOp op : model.unit.ops()) {
            switch (op.kind()) {
                case CLOSURE_NEW -> {
                    if (!(op.result() instanceof ValueId value)
                            || !(op.payload() instanceof KindPayload.ClosureNewPayload
                                closure)) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the CLOSURE_NEW op "
                            + op.opId() + " carries no function-typed result identity");
                    }
                    FunctionExecutionBinding binding =
                        model.unit.functionBindings().get(
                            new FunctionAllocationIdentity(value.id()));
                    if (binding == null) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the CLOSURE_NEW op "
                            + op.opId() + " has no registry entry keyed by its "
                            + "producing allocation identity (missing registration)");
                    }
                    if (!(binding instanceof FunctionExecutionBinding.LoweredBody body)
                            || !body.functionId().equals(closure.function())
                            || !body.blockId().equals(closure.binding().blockId())) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the CLOSURE_NEW op "
                            + op.opId() + " registration does not match its LoweredBody "
                            + "payload (a mismatched registration is invalid IR)");
                    }
                }
                case FUNCTION_ADAPT -> {
                    if (!(op.result() instanceof ValueId value)) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the FUNCTION_ADAPT op "
                            + op.opId() + " carries no result identity");
                    }
                    FunctionExecutionBinding binding =
                        model.unit.functionBindings().get(
                            new FunctionAllocationIdentity(value.id()));
                    if (binding == null) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the FUNCTION_ADAPT op "
                            + op.opId() + " has no registry entry keyed by its "
                            + "producing allocation identity (missing registration)");
                    }
                    if (!(binding instanceof FunctionExecutionBinding.AdapterBinding
                            adapter) || !adapter.adaptOpId().equals(op.opId())) {
                        return fail(model, REGISTRY_ONE_TO_ONE, "the FUNCTION_ADAPT op "
                            + op.opId() + " registration is not its AdapterBinding "
                            + "(a mismatched registration is invalid IR)");
                    }
                }
                default -> {
                    // No function-producing position of this kind.
                }
            }
        }
        // Every HOST_TO_DEAL boundary with a function-typed descriptor
        // registers exactly one HostFunctionValue at the producing
        // crossing.
        for (SemanticOp op : model.unit.ops()) {
            if (!(op.payload() instanceof KindPayload.BoundaryPayload boundary)) {
                continue;
            }
            if (boundary.kind() != BoundaryKind.HOST_TO_DEAL
                    || !(boundary.descriptor() instanceof RuntimeDescriptor.Func)) {
                continue;
            }
            FunctionExecutionBinding binding = model.unit.functionBindings().get(
                new FunctionAllocationIdentity(boundary.input().id()));
            if (!(binding instanceof FunctionExecutionBinding.HostFunctionValue value)
                    || !value.materializingBoundaryOpId().equals(op.opId())) {
                return fail(model, REGISTRY_ONE_TO_ONE, "the HOST_TO_DEAL boundary op "
                    + op.opId() + " materializing a function value has no matching "
                    + "HostFunctionValue registration (a function value materialized by "
                    + "a host crossing registers exactly one binding at the producing "
                    + "crossing)");
            }
        }
        return Optional.empty();
    }

    // =========================================================================
    // NO_ADAPTER_AT_BOUNDARY
    // =========================================================================

    /**
     * The creation-wiring rule (B9/B6): a constraint on the
     * {@code FUNCTION_ADAPT} op's direct output, not an identity-flow
     * restriction. The op immediately following the adapter in its own
     * block must be exactly the adapted position's own boundary chain —
     * a {@code VARIABLE_DECLARATION}/{@code VARIABLE_ASSIGNMENT}
     * boundary whose input is the adapter result followed immediately by
     * the chain's single commit (the declaration {@code BINDING_INIT} or
     * the assignment {@code BINDING_STORE}), or the inferred
     * declaration's {@code BINDING_INIT} committing the adapter result
     * directly (no boundary op exists there). A {@code FUNCTION_ADAPT}
     * result wired directly into the input of any other
     * {@code BOUNDARY} op — parameter, return, host/external/callback,
     * array/table/class element, JSON, and every other kind — is
     * invalid IR. After the commit the adapter identity is an ordinary
     * function value: loads/reads/passes/returns preserve it, so later
     * consumers of the same identity are ordinary flows and are never
     * this rule's concern.
     */
    private static Optional<CompilerDiagnostic> checkNoAdapterAtBoundary(Model model) {
        for (SemanticOp op : model.unit.ops()) {
            if (op.kind() != SemanticOpKind.FUNCTION_ADAPT
                    || !(op.result() instanceof ValueId adapterValue)) {
                continue;
            }
            SemanticOp next = model.nextOpInBlock(op);
            if (next == null) {
                return fail(model, NO_ADAPTER_AT_BOUNDARY, "the FUNCTION_ADAPT result "
                    + adapterValue + " of op " + op.opId() + " is the last op of its "
                    + "block (the adapter result must wire into the adapted position's "
                    + "own boundary chain immediately after the creation)");
            }
            if (next.kind() == SemanticOpKind.BINDING_INIT
                    && next.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value() != null && init.value().equals(adapterValue)) {
                // An inferred declaration: the result feeds its
                // BINDING_INIT directly (no boundary op exists).
                continue;
            }
            if (next.kind() != SemanticOpKind.BOUNDARY
                    || !(next.payload() instanceof KindPayload.BoundaryPayload boundary)
                    || !boundary.input().equals(adapterValue)) {
                return fail(model, NO_ADAPTER_AT_BOUNDARY, "the FUNCTION_ADAPT result "
                    + adapterValue + " of op " + op.opId() + " is not the direct input "
                    + "of the adapted position's own boundary chain (the op after the "
                    + "creation must be exactly the position's own "
                    + "VARIABLE_DECLARATION/VARIABLE_ASSIGNMENT boundary or the "
                    + "inferred declaration's BINDING_INIT)");
            }
            if (boundary.kind() != BoundaryKind.VARIABLE_DECLARATION
                    && boundary.kind() != BoundaryKind.VARIABLE_ASSIGNMENT) {
                return fail(model, NO_ADAPTER_AT_BOUNDARY, "the FUNCTION_ADAPT result "
                    + adapterValue + " of op " + op.opId() + " wires directly into a "
                    + boundary.kind() + " boundary op (an adapter result is the direct "
                    + "input of exactly the adapted position's own "
                    + "VARIABLE_DECLARATION/VARIABLE_ASSIGNMENT boundary chain)");
            }
            SemanticOp commit = model.nextOpInBlock(next);
            boolean committed = false;
            if (commit != null && commit.kind() == SemanticOpKind.BINDING_INIT
                    && commit.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value() != null && init.value().equals(adapterValue)) {
                committed = true;
            }
            if (commit != null && commit.kind() == SemanticOpKind.BINDING_STORE
                    && commit.payload() instanceof KindPayload.BindingStorePayload store
                    && store.value() != null && store.value().equals(adapterValue)) {
                committed = true;
            }
            if (!committed) {
                return fail(model, NO_ADAPTER_AT_BOUNDARY, "the FUNCTION_ADAPT result "
                    + adapterValue + " of op " + op.opId() + " wires into the "
                    + boundary.kind() + " boundary of op " + next.opId() + " but the "
                    + "chain's single commit (the declaration BINDING_INIT or the "
                    + "assignment BINDING_STORE) does not follow it immediately (the "
                    + "adapter result is the direct input of exactly the adapted "
                    + "position's own boundary chain)");
            }
        }
        return Optional.empty();
    }
}