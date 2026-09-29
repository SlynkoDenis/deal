package deal.codegen;

import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ChainOperandCompletion;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The session state shared byte-for-byte by the JVM and LuaJIT semantic
 * emitters: the closure registries and op indexes, the structural block
 * facts, the import and cell-kind facts, the body-state key cache, and
 * the emitted-text builder, together with the session-level queries both
 * emitters answer identically. The divergent members (naming rules such
 * as {@link #slot(ValueId)} and {@link #cell(BindingId, long)}, the
 * target-specific emission surface, and the target-specific payload
 * facts) stay in each emitter's own {@code Session}.
 */
public abstract class EmitterSessionBase {

    /** The session's primary validated unit (the project entry module). */
    protected final LoweredModuleUnit unit;
    /** The primary unit's produced block-membership table. */
    protected final StructuredBodyTable table;
    /**
     * The project-mode closure: every module's unit, table, and
     * class-factory registry (the single-unit session carries one
     * entry plus no registries). Ids are globally unique across the
     * project, so the combined artifact shares one slot/cell
     * namespace.
     */
    protected final Map<ModuleId, LoweredModuleUnit> units = new LinkedHashMap<>();
    protected final Map<ModuleId, StructuredBodyTable> tables = new LinkedHashMap<>();
    protected final Map<ModuleId, ClassFactoryRegistry> registries = new LinkedHashMap<>();
    /** The union class-layout resolution context (K-D11). */
    protected final Map<ClassId, ClassLayout> classLayouts = new LinkedHashMap<>();
    /** Each block id to its owning unit's membership table. */
    protected final Map<BlockId, StructuredBodyTable> blockTableOf = new LinkedHashMap<>();
    /** Each op id to its single membership block (the transfer-closure source). */
    protected final Map<OpId, BlockId> opBlock = new LinkedHashMap<>();
    protected final Map<OpId, SemanticOp> opsById = new HashMap<>();
    /**
     * The derived cell kind of every binding incarnation, keyed by
     * {@code {binding, generation}} (B2: the final kind is a property
     * of the <em>incarnation</em> — a for-let counter's generation-0
     * cell stays {@code DIRECT} while its captured per-iteration
     * generation-1 cell is {@code SHARED_CELL}; keying by binding
     * alone let the first ALLOC's kind shadow every later
     * incarnation). A missing entry is {@code DIRECT}.
     */
    protected final Map<BindingId, Map<Long, BindingCellKind>> cellKinds =
        new HashMap<>();
    /**
     * The function factory currently being emitted (null in the module
     * region and in the detached class-default/thunk emitters): its
     * {@code captures} name the factory parameters, so a reference to a
     * captured binding inside its body reads the capture itself (never
     * a target cell slot) and a nested creation passes the captured
     * cell along.
     */
    protected LoweredFunction currentFunction;

    /** The derived cell kind of one binding incarnation ({@code DIRECT} when unknown). */
    protected final BindingCellKind cellKindOf(BindingId binding, long generation) {
        Map<Long, BindingCellKind> generations = cellKinds.get(binding);
        if (generations == null) {
            return BindingCellKind.DIRECT;
        }
        return generations.getOrDefault(generation, BindingCellKind.DIRECT);
    }

    /** Registers one incarnation's derived cell kind (first emission wins). */
    protected final void registerCellKind(BindingId binding, long generation,
                                          BindingCellKind kind) {
        cellKinds.computeIfAbsent(binding, k -> new HashMap<>())
            .putIfAbsent(generation, kind);
    }

    /** The capture parameter name of one captured binding. */
    protected final String captureCell(BindingId binding) {
        return "c" + binding.id();
    }

    /**
     * True iff the function factory being emitted captures the binding
     * (its factory parameter is the body's binding source).
     */
    protected final boolean isCurrentCapture(BindingId binding) {
        return currentFunction != null && currentFunction.captureOf(binding) != null;
    }

    /**
     * The cell expression of one {@code {binding, generation}} reference
     * at the current emission context: the enclosing factory's capture
     * parameter when the binding is one of its captures, otherwise the
     * creation-site incarnation's cell.
     */
    protected final String cellSource(BindingId binding, long generation) {
        return isCurrentCapture(binding) ? captureCell(binding)
            : cell(binding, generation);
    }

    /**
     * One {@code CLOSURE_NEW}/group-member/general-invocation capture
     * argument: the enclosing factory's capture parameter when the
     * creating body captured the binding (the cell travels the chain),
     * otherwise the creation-site incarnation's cell (never a hard-coded
     * generation 0 — a for-let capture names the per-iteration
     * incarnation).
     */
    protected final String captureArg(BindingGeneration capture) {
        return cellSource(capture.binding(), capture.generation());
    }

    /**
     * Each op's owning module (the export-surface key): the module
     * whose unit carries the op, statically known at emission.
     */
    protected final Map<OpId, ModuleId> opModule = new HashMap<>();
    /** One lowered body's private-state keys (the invocation save/restore). */
    protected final Map<FunctionId, List<String>> bodyStateKeyCache = new HashMap<>();
    protected final Set<OpId> ownedChildren = new HashSet<>();
    /**
     * The payload-owned children only (closure computation excludes
     * them): the union of every registered unit's structural owners.
     */
    protected final Set<OpId> structuralOwned = new HashSet<>();
    /**
     * Each resolved import's closed kind, collected from the
     * session's own {@code MODULE_IMPORT} payloads (M6).
     */
    protected final Map<ModuleId, ModuleImportKind> importKinds = new LinkedHashMap<>();
    /** Ops the block walk skips (the entry delegation of a non-entry module). */
    protected final Set<OpId> skippedOps = new HashSet<>();
    protected final StringBuilder out = new StringBuilder();
    /** The enclosing TRY_CATCH depth (target-specific transfer signalling). */
    protected int tryDepth = 0;

    protected EmitterSessionBase(LoweredModuleUnit unit, StructuredBodyTable table) {
        this.unit = unit;
        this.table = table;
    }

    /** The target's slot name of one value. */
    protected abstract String slot(ValueId id);

    /** The target's cell name of one binding generation. */
    protected abstract String cell(BindingId id, long generation);

    /**
     * Marks the ENTRY_INVOKE delegation of one non-entry module as
     * skipped: the entry op and every op parented to it.
     */
    protected final void markSkippedEntryOps(LoweredModuleUnit moduleUnit) {
        for (SemanticOp op : moduleUnit.ops()) {
            if (op.kind() != SemanticOpKind.ENTRY_INVOKE) {
                continue;
            }
            skippedOps.add(op.opId());
            for (SemanticOp candidate : moduleUnit.ops()) {
                if (op.opId().equals(candidate.origin().parentOpId())) {
                    skippedOps.add(candidate.opId());
                }
            }
        }
    }

    /** Registers one module's unit/table/registry into the session closure. */
    protected final void registerUnit(LoweredModuleUnit moduleUnit,
                                      StructuredBodyTable moduleTable,
                                      ClassFactoryRegistry registry) {
        units.put(moduleUnit.moduleId(), moduleUnit);
        tables.put(moduleUnit.moduleId(), moduleTable);
        registries.put(moduleUnit.moduleId(), registry);
        classLayouts.putAll(moduleUnit.classLayouts());
        for (Map.Entry<BlockId, List<OpId>> entry : moduleTable.blockOps().entrySet()) {
            blockTableOf.put(entry.getKey(), moduleTable);
            for (OpId memberId : entry.getValue()) {
                opBlock.putIfAbsent(memberId, entry.getKey());
            }
        }
        for (SemanticOp op : moduleUnit.ops()) {
            opsById.put(op.opId(), op);
            opModule.put(op.opId(), moduleUnit.moduleId());
            if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                importKinds.putIfAbsent(payload.resolvedModule(), payload.kind());
            }
            if (op.kind() == SemanticOpKind.BINDING_ALLOC) {
                KindPayload.BindingAllocPayload payload =
                    (KindPayload.BindingAllocPayload) op.payload();
                registerCellKind(payload.binding(), payload.generation(),
                    payload.cellKind());
            }
            if (op.kind() == SemanticOpKind.FOR_EACH) {
                // B2: a FOR_EACH iteration binding is always
                // SHARED_CELL (the closed payload records no cell-kind
                // field): the iteration allocates a fresh iteration
                // cell, so a closure created in the body captures that
                // iteration's incarnation.
                KindPayload.ForEachPayload payload =
                    (KindPayload.ForEachPayload) op.payload();
                registerCellKind(payload.binding(), payload.generation(),
                    BindingCellKind.SHARED_CELL);
            }
            if (op.kind() == SemanticOpKind.RECURSIVE_GROUP_INIT) {
                // B2: every group member cell is SHARED_CELL by
                // construction (the closed payload records no
                // cell-kind field and members carry no separate
                // ALLOC) — the publication and the member-body
                // loads both resolve through this fact.
                KindPayload.RecursiveGroupInitPayload payload =
                    (KindPayload.RecursiveGroupInitPayload) op.payload();
                for (BindingId binding : payload.bindings()) {
                    registerCellKind(binding, 0, BindingCellKind.SHARED_CELL);
                }
            }
        }
        // Payload-owned children are emitted exactly once by their
        // owner arms; the block walk skips them (a double emission
        // would duplicate effects and events).
        java.util.Set<OpId> structural =
            ChainOperandCompletion.structuralOwners(moduleUnit);
        structuralOwned.addAll(structural);
        ownedChildren.addAll(structural);
        ChainOperandCompletion.registerChainOperandOwners(moduleUnit, structural,
            ownedChildren);
        // The nested source ASYNC_START of an adapter-over-async task
        // executes under its outer op's arm, never at its flat
        // block-list position (the oracle's UnitState rule).
        for (SemanticOp op : moduleUnit.ops()) {
            if (op.kind() == SemanticOpKind.ASYNC_START) {
                for (SemanticOp candidate : moduleUnit.ops()) {
                    if (candidate.kind() == SemanticOpKind.ASYNC_START
                            && op.opId().equals(candidate.origin().parentOpId())) {
                        ownedChildren.add(candidate.opId());
                    }
                }
            }
        }
    }

    /**
     * True iff the binding is a {@code TRY_CATCH} op's catch binding in
     * the closure: its cell is created and initialized by the
     * {@code TRY_CATCH} arm's catch-entry write, so the catch binding's
     * {@code BINDING_ALLOC} (the catch block's first op) must not reset
     * it.
     */
    protected final boolean isCatchBinding(BindingId binding) {
        for (LoweredModuleUnit moduleUnit : units.values()) {
            for (SemanticOp candidate : moduleUnit.ops()) {
                if (candidate.payload() instanceof KindPayload.TryCatchPayload tryCatch
                        && tryCatch.catchBinding().equals(binding)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The STDLIB_PARAMETER children in one-based declared order. */
    protected final List<SemanticOp> stdlibParamBoundaries(SemanticOp op) {
        List<SemanticOp> result = new ArrayList<>();
        for (SemanticOp candidate : opsById.values()) {
            if (candidate.kind() == SemanticOpKind.BOUNDARY
                    && op.opId().equals(candidate.origin().parentOpId())
                    && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                        == BoundaryKind.STDLIB_PARAMETER) {
                result.add(candidate);
            }
        }
        result.sort(java.util.Comparator.comparingLong(candidate ->
            candidate.opId().id()));
        return result;
    }

    /**
     * The pinned boundary child of one field op (K-D12): the child
     * parented to the field op with the closed boundary kind. A
     * missing child is a producer defect, fail closed before any
     * emission.
     */
    protected final SemanticOp boundaryChildOfKind(SemanticOp op, BoundaryKind kind) {
        for (SemanticOp candidate : opsById.values()) {
            if (candidate.kind() == SemanticOpKind.BOUNDARY
                    && op.opId().equals(candidate.origin().parentOpId())
                    && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                        == kind) {
                return candidate;
            }
        }
        throw new IllegalStateException(op.kind() + " " + op.opId() + " has no "
            + kind + " boundary child: the pinned field-op shape carries it "
            + "parented to the op (producer defect)");
    }

    /**
     * The OPTIONAL_READ op consuming this result value, or null — the
     * envelope shape of a missing-capable table member read.
     */
    protected final SemanticOp optionalReadOf(ValueId value) {
        for (SemanticOp candidate : opsById.values()) {
            if (candidate.kind() == SemanticOpKind.OPTIONAL_READ
                    && value.equals(((KindPayload.OptionalReadPayload) candidate.payload())
                        .value())) {
                return candidate;
            }
        }
        return null;
    }

    /**
     * The registered owner factory op of a SHARED_FACTORY CLASS_NEW,
     * resolved through the delivered per-module class-factory
     * registries (the one fact channel shared with the oracle and the
     * LuaJIT session): the owner module is the module whose registry
     * binds the construction entry, never the class descriptor
     * namespace.
     */
    protected final OpId factoryOpIdOf(SemanticOp op, KindPayload.ClassNewPayload payload) {
        OpId factoryOpId = ClassFactoryRegistry.ownerFactoryOp(registries,
            payload.classFactoryRef());
        if (factoryOpId == null) {
            throw new IllegalStateException("CLASS_NEW " + op.opId()
                + " classFactoryRef " + payload.classFactoryRef()
                + " resolves in no module's ClassFactoryRegistry in the closure"
                + " (producer defect)");
        }
        return factoryOpId;
    }

    /**
     * Whether one recorded DEAL-body cell is the call-owned form
     * (ISSUE-0677; design source
     * {@code function-typed-value-materialization-and-dispatch} M6): its
     * parent {@code RETURN} names no lowered body of the emitted closure
     * (the landing record shape). The callee-owned form's parent
     * {@code RETURN} names the callee body in the closure's function set,
     * and that body's own {@code RETURN} runs the cell.
     */
    protected final boolean callOwnedCell(SemanticOp cell) {
        OpId parentId = cell.origin() == null ? null : cell.origin().parentOpId();
        SemanticOp parent = parentId == null ? null : opsById.get(parentId);
        if (parent == null || parent.kind() != SemanticOpKind.RETURN
                || !(parent.payload()
                    instanceof KindPayload.ReturnPayload returned)) {
            return false;
        }
        for (LoweredModuleUnit moduleUnit : units.values()) {
            if (moduleUnit.functions().containsKey(returned.function())) {
                return false;
            }
        }
        return true;
    }

    /** Collects the transfer ops of a block recursively through structure payloads. */
    protected final void collectTransfers(BlockId block, List<SemanticOp> transfers) {
        // The block's owning membership table (a non-entry module's
        // factory body resolves against its own module table, exactly
        // like the block walk's own resolution).
        StructuredBodyTable ownerTable = blockTableOf.get(block);
        if (ownerTable == null) {
            ownerTable = table;
        }
        List<OpId> memberOps = ownerTable.blockOps().get(block);
        if (memberOps == null) {
            throw new IllegalStateException("block " + block + " has no membership row "
                + "in its owning unit's table (a malformed table — the production "
                + "validator rejects this)");
        }
        for (OpId opId : memberOps) {
            SemanticOp op = opsById.get(opId);
            switch (op.kind()) {
                case BREAK, CONTINUE, RETURN -> transfers.add(op);
                case BRANCH -> {
                    KindPayload.BranchPayload payload =
                        (KindPayload.BranchPayload) op.payload();
                    collectTransfers(payload.selectedBlock(), transfers);
                    if (payload.alternateBlock() != null) {
                        collectTransfers(payload.alternateBlock(), transfers);
                    }
                }
                case LOOP -> {
                    KindPayload.LoopPayload payload =
                        (KindPayload.LoopPayload) op.payload();
                    if (payload.initBlock() != null) {
                        collectTransfers(payload.initBlock(), transfers);
                    }
                    collectTransfers(payload.bodyBlock(), transfers);
                    if (payload.updateBlock() != null) {
                        collectTransfers(payload.updateBlock(), transfers);
                    }
                }
                case FOR_EACH -> {
                    KindPayload.ForEachPayload payload =
                        (KindPayload.ForEachPayload) op.payload();
                    collectTransfers(payload.body(), transfers);
                }
                case TRY_CATCH -> {
                    KindPayload.TryCatchPayload payload =
                        (KindPayload.TryCatchPayload) op.payload();
                    collectTransfers(payload.tryBlock(), transfers);
                    collectTransfers(payload.catchBlock(), transfers);
                }
                default -> {
                }
            }
        }
    }

    protected final SemanticOp stdlibReturnBoundary(SemanticOp op) {
        for (SemanticOp candidate : opsById.values()) {
            if (candidate.kind() == SemanticOpKind.BOUNDARY
                    && op.opId().equals(candidate.origin().parentOpId())
                    && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                        == BoundaryKind.STDLIB_RETURN) {
                return candidate;
            }
        }
        return null;
    }

    /** The class's CLASS_DEFAULT op of one field, or null (no declared default). */
    protected final SemanticOp classDefaultOpOf(ClassId classId, String field) {
        for (SemanticOp candidate : opsById.values()) {
            if (candidate.kind() != SemanticOpKind.CLASS_DEFAULT) {
                continue;
            }
            KindPayload.ClassDefaultPayload payload =
                (KindPayload.ClassDefaultPayload) candidate.payload();
            if (payload.classId().equals(classId) && payload.field().equals(field)) {
                return candidate;
            }
        }
        return null;
    }

    /** True iff the value slot is an op result in this unit. */
    protected final boolean hasProducer(ValueId valueId) {
        for (LoweredModuleUnit moduleUnit : units.values()) {
            for (SemanticOp op : moduleUnit.ops()) {
                if (valueId.equals(op.result())) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The private state of one lowered body's invocation (ISSUE-0654):
     * the value slots its ops produce or consume and its
     * {@code DIRECT} cells (parameters, locals, and per-iteration
     * cells) — the state an invocation owns. {@code SHARED_CELL}
     * state (a captured binding, a group function binding, a module
     * cell) is shared by identity and never saved or restored: a
     * closure holds the cell table itself.
     *
     * <p>The session carries one field per slot and cell (the emitted
     * bodies share the class' state), so a nested invocation of the
     * same body would otherwise overwrite the enclosing invocation's
     * own state: a recursive body (the
     * {@code modules/imported-recursive-export} shape) would re-read
     * its parameter cell and its half-computed slots after the nested
     * call returned. The invoking arm therefore saves the callee
     * body's private state before the invocation and restores it on
     * every path — the per-invocation semantics the semantic oracle
     * models with its cell overlays.</p>
     */
    protected final List<String> bodyStateKeys(FunctionId functionId) {
        List<String> cached = bodyStateKeyCache.get(functionId);
        if (cached != null) {
            return cached;
        }
        LoweredFunction function = null;
        for (LoweredModuleUnit moduleUnit : units.values()) {
            LoweredFunction candidate = moduleUnit.functions().get(functionId);
            if (candidate != null) {
                function = candidate;
                break;
            }
        }
        java.util.LinkedHashSet<String> keys = new java.util.LinkedHashSet<>();
        if (function != null) {
            collectBodyStateKeys(function.body(), keys, new java.util.HashSet<>());
        }
        List<String> result = List.copyOf(keys);
        bodyStateKeyCache.put(functionId, result);
        return result;
    }

    /** True iff the boundary input value is the chain's normalize slot. */
    protected final boolean slotEqualsChainSlot(ValueId input,
                                        SemanticOp chain) {
        for (OpId childId : chainChildOps(chain)) {
            SemanticOp child = opsById.get(childId);
            if (child.kind() == SemanticOpKind.INDEX_NORMALIZE
                    && input.equals(child.result())) {
                return true;
            }
        }
        return false;
    }

    /** The structure op whose payload references the given block, or null. */
    protected final SemanticOp structureReferencing(BlockId block) {
        for (SemanticOp op : opsById.values()) {
            switch (op.payload()) {
                case KindPayload.BranchPayload payload -> {
                    if (block.equals(payload.selectedBlock())
                            || block.equals(payload.alternateBlock())) {
                        return op;
                    }
                }
                case KindPayload.LoopPayload payload -> {
                    if (block.equals(payload.initBlock())
                            || block.equals(payload.bodyBlock())
                            || block.equals(payload.updateBlock())) {
                        return op;
                    }
                }
                case KindPayload.ForEachPayload payload -> {
                    if (block.equals(payload.body())) {
                        return op;
                    }
                }
                case KindPayload.TryCatchPayload payload -> {
                    if (block.equals(payload.tryBlock())
                            || block.equals(payload.catchBlock())) {
                        return op;
                    }
                }
                default -> {
                }
            }
        }
        return null;
    }

    protected final void collectBodyStateKeys(BlockId block, java.util.Set<String> keys,
                                      java.util.Set<BlockId> seen) {
        if (block == null || !seen.add(block)) {
            return;
        }
        StructuredBodyTable ownerTable = blockTableOf.get(block);
        List<OpId> opIds = ownerTable == null ? null : ownerTable.blockOps().get(block);
        if (opIds == null) {
            return;
        }
        for (OpId opId : opIds) {
            SemanticOp op = opsById.get(opId);
            if (op == null) {
                continue;
            }
            if (op.result() instanceof ValueId valueId) {
                keys.add(slot(valueId));
            }
            for (ValueId operand : op.operands()) {
                keys.add(slot(operand));
            }
            switch (op.payload()) {
                case KindPayload.BindingAllocPayload payload ->
                    addCellStateKey(keys, payload.binding(), payload.generation());
                case KindPayload.BindingInitPayload payload ->
                    addCellStateKey(keys, payload.binding(), payload.generation());
                case KindPayload.BindingLoadPayload payload ->
                    addCellStateKey(keys, payload.binding(), payload.generation());
                case KindPayload.BindingStorePayload payload ->
                    addCellStateKey(keys, payload.binding(), payload.generation());
                case KindPayload.RecursiveGroupInitPayload payload -> {
                    for (BindingId binding : payload.bindings()) {
                        addCellStateKey(keys, binding, 0);
                    }
                }
                case KindPayload.ClosureNewPayload payload -> {
                    for (BindingGeneration capture : payload.captures()) {
                        addCellStateKey(keys, capture.binding(),
                            capture.generation());
                    }
                }
                case KindPayload.ModuleImportPayload payload -> {
                    for (BindingId binding : payload.aliasCells()) {
                        addCellStateKey(keys, binding, 0);
                    }
                }
                case KindPayload.ForEachPayload payload -> {
                    addCellStateKey(keys, payload.binding(), payload.generation());
                    collectBodyStateKeys(payload.body(), keys, seen);
                }
                case KindPayload.TryCatchPayload payload -> {
                    addCellStateKey(keys, payload.catchBinding(), 0);
                    collectBodyStateKeys(payload.tryBlock(), keys, seen);
                    collectBodyStateKeys(payload.catchBlock(), keys, seen);
                }
                case KindPayload.BranchPayload payload -> {
                    collectBodyStateKeys(payload.selectedBlock(), keys, seen);
                    collectBodyStateKeys(payload.alternateBlock(), keys, seen);
                }
                case KindPayload.LoopPayload payload -> {
                    collectBodyStateKeys(payload.initBlock(), keys, seen);
                    collectBodyStateKeys(payload.bodyBlock(), keys, seen);
                    collectBodyStateKeys(payload.updateBlock(), keys, seen);
                }
                default -> {
                }
            }
        }
    }

    /**
     * The recorded callee-unit {@code EXTERNAL_ENTRY} of one
     * {@code SHARED_BODY} external call: resolved by the payload's
     * statically recorded {@code externalEntryRef} inside the callee
     * module's unit (ISSUE-0634's accumulation). A missing unit, a
     * ref outside the callee unit, a non-entry op, an async entry for
     * a sync call, or a divergent export name is a fail-closed
     * producer defect — never a silently missing invocation.
     */
    protected final SemanticOp resolveExternalEntry(SemanticOp op,
            KindPayload.CallPayload payload,
            FunctionExecutionBinding.ExternalFunction external,
            LoweredModuleUnit calleeUnit) {
        OpId entryRef = payload.externalEntryRef();
        if (entryRef == null) {
            throw new IllegalStateException("CALL " + op.opId()
                + " carries a SHARED_BODY external binding without a recorded"
                + " externalEntryRef (producer defect)");
        }
        SemanticOp entry = null;
        if (entryRef.module().equals(calleeUnit.moduleId())) {
            for (SemanticOp candidate : calleeUnit.ops()) {
                if (candidate.opId().equals(entryRef)) {
                    entry = candidate;
                    break;
                }
            }
        }
        if (entry == null || entry.kind() != SemanticOpKind.EXTERNAL_ENTRY) {
            throw new IllegalStateException("CALL " + op.opId()
                + "'s externalEntryRef " + entryRef + " does not resolve to a"
                + " recorded EXTERNAL_ENTRY of the callee module "
                + calleeUnit.moduleId() + " (producer defect)");
        }
        KindPayload.ExternalEntryPayload entryPayload =
            (KindPayload.ExternalEntryPayload) entry.payload();
        if (entryPayload.async() || !entryPayload.exportName()
                .equals(external.exportName())) {
            throw new IllegalStateException("CALL " + op.opId()
                + "'s externalEntryRef " + entryRef + " names the "
                + (entryPayload.async() ? "async" : "sync") + " entry of export '"
                + entryPayload.exportName() + "' but the binding names the sync"
                + " export '" + external.exportName() + "' (producer defect)");
        }
        return entry;
    }

    /** The committed value's static kind: its producing op's result type. */
    protected final RuntimeDescriptor producerResultType(SemanticValue value) {
        if (value instanceof ValueId valueId) {
            for (SemanticOp producer : opsById.values()) {
                if (valueId.equals(producer.result())
                        && producer.kind() != SemanticOpKind.ASSIGN
                        && producer.kind() != SemanticOpKind.DELETE
                        && producer.resultType() instanceof RuntimeDescriptor descriptor) {
                    return descriptor;
                }
            }
        }
        return RuntimeDescriptor.Int.INSTANCE;
    }

    protected final RuntimeDescriptor elementDescriptorOf(SemanticOp op) {
        KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) op.payload();
        for (SemanticOp producer : opsById.values()) {
            if (payload.iterable().equals(producer.result())) {
                if (producer.resultType() instanceof RuntimeDescriptor.Array array) {
                    return array.element();
                }
                return producer.resultType() instanceof RuntimeDescriptor descriptor
                    ? descriptor : RuntimeDescriptor.String.INSTANCE;
            }
        }
        return RuntimeDescriptor.String.INSTANCE;
    }

    /**
     * The callee unit's recorded async {@code EXTERNAL_ENTRY} of one
     * {@code ASYNC_START(EXTERNAL)}: resolved by the link's canonical
     * token (the entry op's own id by construction) inside the callee
     * module's unit. A missing module outside the session's closure, a
     * token naming no op, a non-entry op, a sync entry, or a divergent
     * export name is a fail-closed producer defect — the emitted entry
     * would otherwise name no method of the JVM artifact and no
     * dispatch key of the Lua chunk.
     */
    protected final SemanticOp resolveExternalAsyncEntry(SemanticOp op,
            ExternalAsyncLink link) {
        LoweredModuleUnit calleeUnit = units.get(link.calleeModuleId());
        if (calleeUnit == null) {
            throw new IllegalStateException("ASYNC_START " + op.opId()
                + " resolves the external callee module " + link.calleeModuleId()
                + " outside the session's closure (producer defect)");
        }
        OpId entryRef = new OpId(link.calleeModuleId(),
            link.calleeTokenId().tokenId());
        SemanticOp entry = opsById.get(entryRef);
        if (entry == null || entry.kind() != SemanticOpKind.EXTERNAL_ENTRY
                || !(entry.payload()
                    instanceof KindPayload.ExternalEntryPayload entryPayload)
                || !entryPayload.async()
                || !entryPayload.exportName().equals(link.exportName())) {
            throw new IllegalStateException("ASYNC_START " + op.opId()
                + " names the async external '" + link.calleeModuleId() + "'."
                + link.exportName() + " whose ExternalAsyncLink token "
                + entryRef + " resolves to no emitted async EXTERNAL_ENTRY"
                + " in the callee module (producer defect)");
        }
        return entry;
    }

    /**
     * The intrinsic kind of one value identity under the strict
     * identity-preserving-load predicate (the seed and adapter carrier
     * sites): the registration must be an {@code IntrinsicFunction} and
     * every op result publishing the identity must be a
     * {@code BINDING_LOAD} whose named cell's {@code BINDING_INIT}
     * carries the identity — the seed init's own cell, or an alias
     * cell whose init is the alias declaration's re-publication of the
     * same identity.
     */
    protected final IntrinsicKind intrinsicKindOf(ValueId valueId) {
        FunctionExecutionBinding registration = null;
        for (LoweredModuleUnit moduleUnit : units.values()) {
            FunctionExecutionBinding found = moduleUnit.functionBindings().get(
                new FunctionAllocationIdentity(valueId.id()));
            if (found != null) {
                registration = found;
                break;
            }
        }
        if (!(registration instanceof FunctionExecutionBinding.IntrinsicFunction
                intrinsic)) {
            return null;
        }
        for (LoweredModuleUnit moduleUnit : units.values()) {
            for (SemanticOp op : moduleUnit.ops()) {
                if (!valueId.equals(op.result())) {
                    continue;
                }
                if (op.kind() != SemanticOpKind.BINDING_LOAD
                        || !(op.payload() instanceof KindPayload.BindingLoadPayload
                            load)
                        || !isSeedInitOperand(valueId, load.binding(),
                            load.generation())) {
                    return null;
                }
            }
        }
        return intrinsic.kind();
    }

    /**
     * The structure ancestors of a block, innermost first (static). The
     * enclosing block of one structure op comes from *its own* unit's
     * membership table ({@code blockTableOf}): a callee unit's nested
     * blocks belong to the callee's table, never the entry module's, so
     * a transfer inside a cross-module callee body closes exactly the
     * structures it nests in.
     */
    protected final List<SemanticOp> structureAncestors(BlockId block) {
        List<SemanticOp> result = new ArrayList<>();
        BlockId current = block;
        while (current != null) {
            SemanticOp enclosing = structureReferencing(current);
            if (enclosing == null) {
                break;
            }
            result.add(enclosing);
            StructuredBodyTable ownerTable = blockTableOf.get(current);
            current = ownerTable == null ? null
                : ownerTable.opBlocks().get(enclosing.opId());
        }
        return result;
    }

    /**
     * True iff one {@code BINDING_INIT} of the cell carries the given
     * identity: the load republishes an identity the cell already
     * holds — the seed init's own write, or an alias declaration's
     * re-publication of it (the identity-preserving-load test).
     */
    protected final boolean isSeedInitOperand(ValueId identity, BindingId binding,
                                      long generation) {
        for (LoweredModuleUnit moduleUnit : units.values()) {
            for (SemanticOp op : moduleUnit.ops()) {
                if (op.kind() == SemanticOpKind.BINDING_INIT
                        && op.payload() instanceof KindPayload.BindingInitPayload
                            init
                        && identity.equals(init.value())
                        && init.binding().equals(binding)
                        && init.generation() == generation) {
                    return true;
                }
            }
        }
        return false;
    }

    /** A body-private cell key: {@code DIRECT} cells only (shared state stays shared). */
    protected final void addCellStateKey(java.util.Set<String> keys, BindingId binding,
                                 long generation) {
        if (cellKindOf(binding, generation) == BindingCellKind.SHARED_CELL) {
            return;
        }
        keys.add(cell(binding, generation));
    }

    protected final List<OpId> chainChildOps(SemanticOp chain) {
        return switch (chain.payload()) {
            case KindPayload.AssignPayload assign -> assign.childOps();
            case KindPayload.DeletePayload delete -> delete.childOps();
            default -> List.of();
        };
    }
}
