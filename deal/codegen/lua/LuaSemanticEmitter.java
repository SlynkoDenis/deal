package deal.codegen.lua;

import deal.ffi.FfiGeneratedModule;
import deal.ffi.FfiImportedClassPlanReference;
import deal.ffi.FfiImportedFunctionReference;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ChainOperandCompletion;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The shared LuaJIT emitter of the decomposition-tail integration
 * verification (ISSUE-0410): emits a real LuaJIT artifact from the
 * validated {@link LoweredModuleUnit} + {@link StructuredBodyTable} over
 * the EVALUATION_ORDER op set (assignment-delete-address-chains A-D8,
 * binary-comparison-selectors B-D6, and control-flow-structures C-D9):
 *
 * <ul>
 *   <li><b>Chains:</b> every chain child's result is materialized into a
 *       fresh local in payload order before the next child executes; the
 *       bounds check runs only from the boundary child's projection
 *       (never a target-side re-check that can raise twice); no
 *       receiver/key/RHS expression is re-emitted or re-evaluated; the
 *       retained {@code emitAssignment} double-evaluation shape
 *       ({@code LuaBackend.java:2366-2406}) never appears.</li>
 *   <li><b>Comparisons:</b> native {@code ==}/{@code ~=}/{@code <}/
 *       {@code <=}/{@code >}/{@code >=} realize the closed B-D2 table —
 *       IEEE semantics on numbers, scalar-lexicographic order on
 *       validated scalar strings (UTF-8 byte order equals code point
 *       order), native identity on tables/functions; missing compares as
 *       language null at both operand positions.</li>
 *   <li><b>Control flow:</b> no speculative execution; condition ops are
 *       emitted inside the loop structure and re-evaluated per
 *       iteration; the {@code FOR_EACH} iterable is materialized into a
 *       local once before the loop; the short-circuited block sits
 *       behind a guard so its effects cannot run when skipped; FOR's
 *       continue landing is before the update; block code follows the
 *       {@code StructuredBodyTable} membership; catches are limited to
 *       DEAL errors (an infrastructure failure is never caught or
 *       reified).</li>
 * </ul>
 *
 * <p>The artifact publishes its execution report on the dedicated trace
 * channel (stderr) through the
 * {@link deal.semantic.SemanticTraceProtocol} line grammar —
 * byte-identical to the semantic oracle's report — and writes real
 * console effect bytes to stdout. Every event carries the validated
 * operation's contract digest and structural parent, so the differential
 * harness validates each event against the exact IR op before the
 * three-way comparison: a duplicated evaluation, a wrong selector, or a
 * missing boundary fails even when printed output coincides.</p>
 */
public final class LuaSemanticEmitter {

    private LuaSemanticEmitter() {
    }

    /** Emits the complete LuaJIT module artifact for the validated unit. */
    public static String emitModule(LoweredModuleUnit unit, StructuredBodyTable table) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        return new Session(unit, table, true, true).emit();
    }

    /**
     * Emits the combined trace artifact of a validated executable
     * project (the cross-module CLASSES surface): one chunk carries the
     * prelude once, every module's function factories, adapter thunks,
     * and detached class-default functions, then each module's init walk
     * in dependency order (each under its own {@code __module} tag). A
     * caller's {@code CLASS_NEW(SHARED_FACTORY)} arm resolves the
     * owner's factory op and default blocks through the closure, so the
     * owner-side events carry the owner's module path and the factory's
     * cross-unit parent. Single-unit sessions are the singleton closure
     * of the same machinery.
     *
     * @param project    the validated executable closure; non-null
     * @param tables     each module's block-membership table; non-null
     * @param registries each module's class-factory registry; non-null
     * @return the combined artifact source text
     */
    public static String emitProject(ExecutableLoweredProject project,
                                     Map<ModuleId, StructuredBodyTable> tables,
                                     Map<ModuleId, ClassFactoryRegistry> registries) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        return new Session(project, tables, registries, true, null).emit();
    }

    /**
     * Emits the combined trace artifact of a validated executable
     * project with the compile's host declaration surface (ISSUE-0651;
     * the differential drive of the sync host call realization): the
     * trace-mode project session of {@link #emitProject} additionally
     * carries the declared map and the host-boundary prelude, so a
     * {@code MODULE_IMPORT(HOST)} emits its {@code __rt.load_host} load
     * in the trace walk and a host {@code CALL}/{@code CALLBACK_INVOKE}
     * arm resolves the loaded surface entry — the oracle-agreement drive
     * (“the oracle matches event-for-event in trace mode”) then
     * compares one event stream from the oracle and both targets.
     *
     * @param project            the validated executable closure; non-null
     * @param tables             each module's block-membership table;
     *                           non-null
     * @param registries         each module's class-factory registry;
     *                           non-null
     * @param declarationSurface the declaration surface covering every
     *                           declaration import of the compile; non-null
     * @return the combined trace artifact source text
     */
    public static String emitProject(ExecutableLoweredProject project,
                                     Map<ModuleId, StructuredBodyTable> tables,
                                     Map<ModuleId, ClassFactoryRegistry> registries,
                                     HostDeclarationSurface declarationSurface) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        Objects.requireNonNull(declarationSurface,
            "declarationSurface must not be null");
        return new Session(project, tables, registries, true,
            declarationSurface).emit();
    }

    /**
     * Emits the production LuaJIT project artifact for the validated
     * executable closure (ISSUE-0640;
     * {@code production-project-emission-and-atomic-cutover} P1/P3 and the
     * production LuaJIT emission contract;
     * {@code luajit-jvm-single-lowering-production-cutover} C2): the
     * combined project session of {@link #emitProject} with the
     * trace/terminal mode switched to production — exactly one Lua chunk
     * carries the whole closure (the prelude once, every module's function
     * factories, adapter thunks, detached class-default functions, and
     * per-class JSON plans, then each module's init walk in dependency
     * order). The conformance trace protocol is suppressed (no event
     * output and no {@code R|} terminal), an uncaught DEAL failure
     * publishes the retained {@code DEAL_ERROR_CODE: <code>} line on
     * stdout and exits 1, a non-DEAL failure rethrows, and success exits
     * silently. The chunk carries the module export-surface registry keyed
     * by module identity and returns the entry module's surface (the
     * retained-caller ABI); only the entry module's {@code ENTRY_INVOKE}
     * delegation runs (every non-entry {@code ENTRY_INVOKE} and its
     * delegated {@code CALL} stay skipped), so the entry {@code main}
     * executes exactly once per chunk execution.
     *
     * <p>The entry consumes only the validated project, the per-module
     * block-membership tables, the per-module class-factory registries, and
     * the host declaration surface: no AST, no checker result, no route
     * input, no extern-C generated-module map, and no identity index. The
     * declaration surface is the single source of the declared export map
     * the {@code MODULE_IMPORT(HOST)} load emits (ISSUE-0650;
     * {@code host-module-load-and-host-call-realization} H1 and the
     * host-load contract) — the function exports carry the canonical
     * runtime-descriptor text in declaration order and the class exports
     * their canonical class-descriptor text.</p>
     *
     * @param project            the validated executable closure; non-null
     * @param tables             each module's block-membership table;
     *                           non-null
     * @param registries         each module's class-factory registry;
     *                           non-null
     * @param declarationSurface the declaration surface covering every
     *                           declaration import of the compile; non-null
     * @return the production project artifact source text
     */
    public static String emitProductionProject(ExecutableLoweredProject project,
                                               Map<ModuleId, StructuredBodyTable> tables,
                                               Map<ModuleId, ClassFactoryRegistry> registries,
                                               HostDeclarationSurface declarationSurface) {
        return emitProductionProject(project, tables, registries,
            declarationSurface, null);
    }

    /**
     * Emits the FFI-capable production LuaJIT project artifact for the
     * validated executable closure (the extern-C admission slice): the
     * landed production project session plus the compile's FFI emission
     * input (the validated extern-C generated-module metadata and the
     * manifest-directory text). A session carrying the FFI emission
     * input emits, at the owning {@code MODULE_IMPORT} of an extern-C
     * declaration import, the landed generator's literals — one
     * provider binding per referenced alias, re-pointed at the chunk's
     * export-surface registry (never a {@code require} line), the
     * bindings literal, and the
     * {@code __exportSurfaces[<module>] = ... __rt.load_ffi(...)}
     * registry entry with the import statement's span triplet — so the
     * loaded module table becomes the import's namespace value. A
     * {@code MANIFEST_RELATIVE_PATH} loader text resolves against the
     * input's manifest directory through the pinned prefix-resolved
     * conversion. An extern-C import without generated metadata, an
     * unserializable generated module, and a wrapper-incapable provider
     * (a provider the artifact does not publish in the wrapper
     * convention before the binding position — a spec-stdlib module, a
     * declaration module whose load the emission emitted after that
     * position or never emitted, and any module outside the closure and
     * the declaration facts) each fail closed (an
     * {@link IllegalStateException} the production arm maps to E6005
     * {@code SHARED_EMITTER_COVERAGE} and stages nothing). A session
     * without the FFI emission input keeps the landed arm: an extern-C
     * declaration import emits its {@code MODULE_IMPORT} op with no
     * load, its loaded surface being the trace session's scenario seam.
     *
     * <p>No evaluator runs and no library opens during emission: the
     * generated-module contract carries compile-time metadata only, and
     * the emitted literals are byte-deterministic.</p>
     *
     * @param project            the validated executable closure; non-null
     * @param tables             each module's block-membership table;
     *                           non-null
     * @param registries         each module's class-factory registry;
     *                           non-null
     * @param declarationSurface the declaration surface covering every
     *                           declaration import of the compile;
     *                           non-null
     * @param ffiEmissionInput   the compile's FFI emission input, or
     *                           {@code null} for a session without an
     *                           FFI emission input
     * @return the production project artifact source text
     */
    public static String emitProductionProject(ExecutableLoweredProject project,
                                               Map<ModuleId, StructuredBodyTable> tables,
                                               Map<ModuleId, ClassFactoryRegistry> registries,
                                               HostDeclarationSurface declarationSurface,
                                               FfiEmissionInput ffiEmissionInput) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        Objects.requireNonNull(declarationSurface,
            "declarationSurface must not be null");
        return new Session(project, tables, registries, false,
            declarationSurface, ffiEmissionInput).emit();
    }

    /**
     * Emits the production LuaJIT module artifact for the validated unit
     * (ISSUE-0239 E10): the conformance trace protocol is suppressed, a
     * DEAL failure publishes the retained {@code DEAL_ERROR_CODE: <code>}
     * line on stdout and exits 1, the chunk returns its own module's
     * surface through the chunk-global per-module export-surface registry
     * (the retained-caller ABI surface, keyed by the module identity), and
     * the {@code ENTRY_INVOKE} delegation executes only for the entry
     * module.
     *
     * @param unit        the validated lowered module unit; non-null
     * @param table       the unit's produced block-membership table; non-null
     * @param entryModule whether this module is the selected entry module
     *                    (runs the {@code ENTRY_INVOKE} delegation)
     * @return the production artifact source text
     */
    public static String emitProductionModule(LoweredModuleUnit unit,
                                              StructuredBodyTable table,
                                              boolean entryModule) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        return new Session(unit, table, false, entryModule).emit();
    }

    // =========================================================================
    // Session
    // =========================================================================

    private static final class Session {
        final LoweredModuleUnit unit;
        final StructuredBodyTable table;
        /**
         * The project-mode closure: every module's unit, table, and
         * class-factory registry (the single-unit session carries one
         * entry plus no registries). Ids are globally unique across the
         * project, so the combined artifact shares one slot/cell
         * namespace.
         */
        final Map<ModuleId, LoweredModuleUnit> units = new LinkedHashMap<>();
        final Map<ModuleId, StructuredBodyTable> tables = new LinkedHashMap<>();
        final Map<ModuleId, ClassFactoryRegistry> registries = new LinkedHashMap<>();
        /** The union class-layout resolution context (K-D11). */
        final Map<ClassId, ClassLayout> classLayouts = new LinkedHashMap<>();
        /** Each block id → its owning unit's membership table. */
        final Map<BlockId, StructuredBodyTable> blockTableOf = new LinkedHashMap<>();
        /** Each op id → its single membership block (the transfer-closure source). */
        final Map<OpId, BlockId> opBlock = new LinkedHashMap<>();
        final Map<OpId, SemanticOp> opsById = new HashMap<>();
        final Map<BindingId, BindingCellKind> cellKinds = new HashMap<>();
        /**
         * Each op's owning module (the export-surface key): the module
         * whose unit carries the op, statically known at emission — the
         * surface key is the emitting module's identity, never a path
         * guess.
         */
        final Map<OpId, ModuleId> opModule = new HashMap<>();
        /** One lowered body's private-state keys (the invocation save/restore). */
        final Map<FunctionId, List<String>> bodyStateKeyCache = new HashMap<>();
        final java.util.Set<OpId> ownedChildren = new java.util.HashSet<>();
        /**
         * The payload-owned children only (closure computation excludes
         * them): the union of every registered unit's structural owners.
         */
        final java.util.Set<OpId> structuralOwned = new java.util.HashSet<>();
        /** Production mode: no trace protocol, DEAL_ERROR_CODE terminal. */
        final boolean trace;
        /**
         * Whether the session carries a whole validated closure (the
         * project entries) or one module (the per-unit entries). The
         * read's emit-time ownership guard applies to a project session
         * only: a COMPILED read whose owner module is not among the
         * session's units is a producer defect there (the one lowering
         * resolves every COMPILED import to a closure module), while a
         * per-unit session resolves the owner's published surface of the
         * same program at execution and never fails closed for a foreign
         * owner.
         */
        final boolean projectSession;
        /**
         * Each resolved import's closed kind, collected from the
         * session's own {@code MODULE_IMPORT} payloads (M6): the read's
         * module kind comes from the session's import facts, never a
         * path guess.
         */
        final Map<ModuleId, ModuleImportKind> importKinds = new LinkedHashMap<>();
        /**
         * The compile's host declaration surface (the declared-map source
         * of the {@code MODULE_IMPORT(HOST)} load): non-null in the
         * production project session, null in the trace/unit sessions.
         */
        final HostDeclarationSurface hostSurface;
        /**
         * The declared host classes of the compile's declaration surface by
         * canonical class identity (ISSUE-0624; K10): a host declaration
         * class construction resolves its declaring module — the
         * {@code __exportSurfaces} key whose loaded surface carries the
         * class's {@code <C>_defaults} entry — through this map, never from
         * a dotted-path derivation. Empty outside the host-aware project
         * sessions.
         */
        final Map<ClassId, ModuleId> hostClassModules = new LinkedHashMap<>();
        /**
         * The declared extern-C classes of the compile's declaration
         * surface by canonical class identity (ISSUE-0666; struct-plan
         * F1): a C-struct class construction resolves its declaring module
         * — the {@code __exportSurfaces} key whose loaded surface carries
         * the class's {@code <C>_plan} entry — through this map, never from
         * a dotted-path derivation. Empty outside the declaration-surface
         * sessions.
         */
        final Map<ClassId, ModuleId> ffiClassModules = new LinkedHashMap<>();
        /**
         * The compile's FFI emission input (the extern-C generated-module
         * metadata and the manifest-directory text): non-null exactly in
         * the FFI-capable production session, null in every other session
         * (the trace/unit entries and the landed production entry, whose
         * extern-C import keeps the landed no-op arm).
         */
        final FfiEmissionInput ffiInput;
        /**
         * The declaration modules whose load this session's walk already
         * emitted into the chunk-global {@code __exportSurfaces} registry
         * (the {@code load_host} and {@code load_ffi} loads, in emission
         * order). The provider-binding predicate admits a declaration
         * provider exactly when its load was emitted before the binding
         * position: the binding captures the registry entry by value, so
         * a load emitted later creates a second surface object the
         * captured binding never observes.
         */
        final java.util.Set<ModuleId> emittedDeclarationLoads =
            new java.util.LinkedHashSet<>();
        /** The per-session ordinal of the emitted FFI import locals. */
        int ffiImportCounter;
        /** The selected entry module runs the ENTRY_INVOKE delegation. */
        final boolean entryModule;
        /** Ops the block walk skips (the entry delegation of a non-entry module). */
        final java.util.Set<OpId> skippedOps = new java.util.HashSet<>();
        final StringBuilder out = new StringBuilder();
        /** The enclosing TRY_CATCH depth: transfers inside a pcall body
         *  must signal instead of goto/return (Lua closures cannot jump
         *  to the enclosing function's labels). */
        int tryDepth = 0;
        /** The function id of the factory currently being emitted (the
         *  per-function return-trampoline label suffix): every RETURN of
         *  the body jumps to the function's trampoline label — the last
         *  statement of the closure body — because a raw Lua return
         *  followed by a structure's closing label (a return inside a
         *  branch/loop/for-each block) or by the trampoline label itself
         *  (a top-level return before the tail) is invalid Lua. */
        FunctionId currentFunctionId = null;
        /** Structure ancestors are computed statically from the block tree
         *  per transfer (never a runtime-sensitive stack). */

        Session(LoweredModuleUnit unit, StructuredBodyTable table, boolean trace,
                boolean entryModule) {
            this.unit = unit;
            this.table = table;
            this.trace = trace;
            this.projectSession = false;
            this.hostSurface = null;
            this.ffiInput = null;
            this.entryModule = entryModule;
            registerUnit(unit, table, new ClassFactoryRegistry(Map.of()));
            if (!entryModule) {
                // A non-entry module never runs its ENTRY_INVOKE delegation
                // (the retained emitter invokes main() only from the entry
                // module): skip the entry op and its delegated CALL.
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() != SemanticOpKind.ENTRY_INVOKE) {
                        continue;
                    }
                    skippedOps.add(op.opId());
                    for (SemanticOp candidate : unit.ops()) {
                        if (op.opId().equals(candidate.origin().parentOpId())) {
                            skippedOps.add(candidate.opId());
                        }
                    }
                }
            }
        }

        /**
         * The project-mode session (the cross-module factory surface):
         * every module's unit, table, and class-factory registry in one
         * combined artifact — the CLASS_NEW(SHARED_FACTORY) arm resolves
         * the owner's factory op and default blocks through the closure.
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace) {
            this(project, tables, registries, trace, null);
        }

        /**
         * The project-mode session of the production project entry (and,
         * since ISSUE-0651, of the host-aware trace project entry): the
         * combined closure plus the compile's host declaration surface
         * (the declared-map source of the {@code MODULE_IMPORT(HOST)}
         * load). A trace-mode project session without the surface keeps
         * the landed no-op arm.
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                HostDeclarationSurface hostSurface) {
            this(project, tables, registries, trace, hostSurface, null);
        }

        /**
         * The FFI-capable production project session: the combined closure
         * plus the compile's host declaration surface (the declared-map
         * source of the {@code MODULE_IMPORT(HOST)} load and the extern-C
         * declaration-kind source) and the compile's FFI emission input
         * (the extern-C generated-module metadata of the emitted
         * {@code load_ffi} prelude and the manifest-directory text
         * resolving a manifest-relative loader text). A null FFI input is
         * a session without an FFI emission input; a non-null input
         * requires the declaration surface.
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                HostDeclarationSurface hostSurface, FfiEmissionInput ffiInput) {
            if (ffiInput != null && hostSurface == null) {
                throw new IllegalArgumentException(
                    "an FFI emission input requires the compile's host"
                        + " declaration surface (the extern-C declaration"
                        + " kind and the provider coverage both resolve through"
                        + " it — a producer defect)");
            }
            this.hostSurface = hostSurface;
            this.ffiInput = ffiInput;
            this.projectSession = true;
            this.unit = project.modules().get(project.entryModule());
            this.table = tables.get(project.entryModule());
            if (this.unit == null || this.table == null) {
                throw new IllegalArgumentException(
                    "the entry module is not in the executable closure");
            }
            this.trace = trace;
            this.entryModule = true;
            registerDeclarationClasses();
            for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                    : project.modules().entrySet()) {
                registerUnit(entry.getValue(), tables.get(entry.getKey()),
                    registries.getOrDefault(entry.getKey(),
                        new ClassFactoryRegistry(Map.of())));
                if (!entry.getKey().equals(project.entryModule())) {
                    // A non-entry module never runs its ENTRY_INVOKE
                    // delegation: skip the entry op and its delegated
                    // CALL in the combined walk.
                    for (SemanticOp op : entry.getValue().ops()) {
                        if (op.kind() != SemanticOpKind.ENTRY_INVOKE) {
                            continue;
                        }
                        skippedOps.add(op.opId());
                        for (SemanticOp candidate : entry.getValue().ops()) {
                            if (op.opId().equals(candidate.origin().parentOpId())) {
                                skippedOps.add(candidate.opId());
                            }
                        }
                    }
                }
            }
        }

        /**
         * Registers the compile's declared declaration classes (ISSUE-0624
         * K10 and ISSUE-0666; struct-plan F1): one entry per declaration
         * module class export, keyed by the canonical class identity
         * projected through the single {@link DescriptorService} producer —
         * the same identity the {@code CLASS_NEW} payloads and the field-op
         * payloads carry. A {@code HOST} declaration class resolves its
         * declaring module through {@link #hostClassModules} (the loaded
         * {@code <C>_defaults} entry's surface key), an {@code EXTERN_C}
         * declaration class through {@link #ffiClassModules} (the loaded
         * {@code <C>_plan} entry's surface key): one declaration kind per
         * module, so every class identity lands in exactly one map.
         */
        private void registerDeclarationClasses() {
            if (hostSurface == null) {
                return;
            }
            for (ModuleId declarationModule : hostSurface.moduleIds()) {
                HostDeclarationSurface.DeclarationFacts facts =
                    hostSurface.require(declarationModule);
                boolean externC = facts.kind()
                    == HostDeclarationSurface.DeclarationKind.EXTERN_C;
                for (Map.Entry<String, Type> export : facts.exports().entrySet()) {
                    if (!(export.getValue() instanceof Type.Class)) {
                        continue;
                    }
                    RuntimeDescriptor descriptor =
                        DescriptorService.describe(export.getValue());
                    if (descriptor instanceof RuntimeDescriptor.Class classDescriptor) {
                        if (externC) {
                            ffiClassModules.put(classDescriptor.classId(),
                                declarationModule);
                        } else {
                            hostClassModules.put(classDescriptor.classId(),
                                declarationModule);
                        }
                    }
                }
            }
        }

        /** Whether one class identity is a declared host class of the compile. */
        private boolean isHostClass(ClassId classId) {
            return hostClassModules.containsKey(classId);
        }

        /**
         * The emitted expression of one declared extern-C C-struct class's
         * loaded {@code <C>_plan} entry (ISSUE-0666; struct-plan F1): the
         * module's published surface entry — the module table
         * {@code __rt.load_ffi} returned, keyed by the class's declaration
         * name ({@code <C>_plan}, the runtime's own publication key) — read
         * back by the construction site. An absent surface or entry is a
         * fail-closed producer defect in the prelude helper, never a silent
         * default.
         */
        private String ffiPlanExpr(ClassId classId) {
            ModuleId declarationModule = ffiClassModules.get(classId);
            if (declarationModule == null) {
                throw new IllegalStateException("the class " + classId
                    + " is not a declared extern-C class of the compile's"
                    + " declaration surface (the class plan entry has exactly one"
                    + " source — a producer defect)");
            }
            return "__ffiClassPlan(" + luaString(declarationModule.path())
                + ", " + luaString(classId.name()) + ")";
        }

        /**
         * The emitted expression of one declared host class's loaded
         * {@code <C>_defaults} entry (K10): the module's published surface
         * entry — the module table {@code __rt.load_host} returned — read
         * back by the construction site. An absent surface or entry is a
         * fail-closed producer defect in the prelude helper, never a silent
         * default.
         */
        private String hostDefaultsExpr(ClassId classId) {
            ModuleId declarationModule = hostClassModules.get(classId);
            if (declarationModule == null) {
                throw new IllegalStateException("the class " + classId
                    + " is not a declared host class of the compile's declaration"
                    + " surface (the class defaults entry has exactly one source —"
                    + " a producer defect)");
            }
            return "__hostClassDefaults(" + luaString(declarationModule.path())
                + ", " + luaString(classId.name()) + ")";
        }

        /** Registers one module's unit/table/registry into the session closure. */
        private void registerUnit(LoweredModuleUnit moduleUnit,
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
                    cellKinds.putIfAbsent(payload.binding(), payload.cellKind());
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
                        cellKinds.put(binding, BindingCellKind.SHARED_CELL);
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

        // -- naming ---------------------------------------------------------------

        String slot(ValueId id) {
            return "S.v" + id.id();
        }

        String cell(BindingId id, long generation) {
            return "S.b" + id.id() + "g" + generation;
        }

        String label(BlockId id) {
            return "L" + id.id();
        }

        String loopExit(OpId loopOp) {
            return "X" + loopOp.id();
        }

        String loopCont(OpId loopOp) {
            return "Y" + loopOp.id();
        }

        String fnFactory(FunctionId id) {
            return "F" + id.id();
        }

        String returnLabel(FunctionId id) {
            return "__ret" + id.id();
        }

        // -- static kinds -----------------------------------------------------------

        /**
         * The static runtime kind of a descriptor for atomization/checks:
         * {@code null}, {@code bool}, {@code int}, {@code number},
         * {@code string}, {@code table}, {@code array}, {@code function},
         * {@code class}, {@code err}, or {@code nullable:&lt;inner&gt;}.
         */
        static String staticKind(RuntimeDescriptor descriptor) {
            if (descriptor == null) {
                return "ref";
            }
            if (descriptor instanceof RuntimeDescriptor.Null) {
                return "null";
            }
            if (descriptor instanceof RuntimeDescriptor.Boolean) {
                return "bool";
            }
            if (descriptor instanceof RuntimeDescriptor.Int) {
                return "int";
            }
            if (descriptor instanceof RuntimeDescriptor.Number) {
                return "number";
            }
            if (descriptor instanceof RuntimeDescriptor.String) {
                return "string";
            }
            if (descriptor instanceof RuntimeDescriptor.Table) {
                return "table";
            }
            if (descriptor instanceof RuntimeDescriptor.Array) {
                return "array";
            }
            if (descriptor instanceof RuntimeDescriptor.Func) {
                return "function";
            }
            if (descriptor instanceof RuntimeDescriptor.Class cls) {
                // The builtin Error class keeps the closed err atom
                // ({code, message}); user classes carry the class
                // identity tag (E5).
                return ClassId.ERROR.equals(cls.classId()) ? "err" : "class";
            }
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                return "nullable:" + staticKind(nullable.inner());
            }
            return "ref";
        }

        /** The prelude-side descriptor text for a boundary check. */
        static String descriptorText(RuntimeDescriptor descriptor) {
            if (descriptor instanceof RuntimeDescriptor.Null) {
                return "null";
            }
            if (descriptor instanceof RuntimeDescriptor.Boolean) {
                return "boolean";
            }
            if (descriptor instanceof RuntimeDescriptor.Int) {
                return "int";
            }
            if (descriptor instanceof RuntimeDescriptor.Number) {
                return "number";
            }
            if (descriptor instanceof RuntimeDescriptor.String) {
                return "string";
            }
            if (descriptor instanceof RuntimeDescriptor.Table) {
                return "table";
            }
            if (descriptor instanceof RuntimeDescriptor.Class cls) {
                return cls.classId().text();
            }
            if (descriptor instanceof RuntimeDescriptor.Array array) {
                return "array(" + descriptorText(array.element()) + ")";
            }
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                return "nullable(" + descriptorText(nullable.inner()) + ")";
            }
            if (descriptor instanceof RuntimeDescriptor.Func func) {
                StringBuilder params = new StringBuilder();
                for (RuntimeDescriptor param : func.paramTypes()) {
                    if (params.length() > 0) {
                        params.append(',');
                    }
                    params.append(descriptorText(param));
                }
                return "function(" + params + ";" + descriptorText(func.returnType()) + ")";
            }
            return "unknown";
        }

        /**
         * The emitted prelude boundary check of one descriptor over one
         * value: {@code __bcheck(desc, kind, value)} — plus, when the
         * descriptor carries a function position, the descriptor's
         * canonical spec text as the trailing argument, so the function
         * row can compare a host ABI wrapper's declared canonical
         * signature (the loaded host surface entry's own metadata — the
         * read value of ISSUE-0653's HOST read; the {@code desc}
         * spelling stays the DEAL carrier's internal text). The text of
         * every non-function check is emitted unchanged.
         */
        static String bcheckExpr(RuntimeDescriptor descriptor, String value) {
            return "__bcheck(" + bcheckArgs(descriptor, value) + ")";
        }

        /**
         * The argument list of one prelude boundary check: the descriptor
         * text, the static kind, the value, and — when the descriptor
         * carries a function position — the descriptor's canonical spec
         * text as the trailing argument. The text of every non-function
         * check is emitted unchanged.
         */
        static String bcheckArgs(RuntimeDescriptor descriptor, String value) {
            String args = luaString(descriptorText(descriptor)) + ", "
                + luaString(staticKind(descriptor)) + ", " + value;
            if (containsFunction(descriptor)) {
                args += ", " + luaString(descriptor.canonicalSpecText());
            }
            return args;
        }

        /** Whether one descriptor carries a function position (recursively). */
        static boolean containsFunction(RuntimeDescriptor descriptor) {
            return switch (descriptor) {
                case RuntimeDescriptor.Func ignored -> true;
                case RuntimeDescriptor.Nullable nullable ->
                    containsFunction(nullable.inner());
                case RuntimeDescriptor.Array array -> containsFunction(array.element());
                default -> false;
            };
        }

        // -- lua literals -----------------------------------------------------------

        static String luaString(String text) {
            StringBuilder sb = new StringBuilder();
            sb.append('"');
            for (int i = 0; i < text.length(); i++) {
                char c = text.charAt(i);
                switch (c) {
                    case '"' -> sb.append("\\\"");
                    case '\\' -> sb.append("\\\\");
                    case '\n' -> sb.append("\\n");
                    case '\t' -> sb.append("\\t");
                    case '\r' -> sb.append("\\r");
                    default -> {
                        if (c < 0x20) {
                            sb.append(String.format("\\%03d", (int) c));
                        } else {
                            sb.append(c);
                        }
                    }
                }
            }
            sb.append('"');
            return sb.toString();
        }

        static String luaNumber(double value) {
            if (Double.isNaN(value)) {
                return "(0/0)";
            }
            if (Double.isInfinite(value)) {
                return value > 0 ? "(1/0)" : "(-1/0)";
            }
            if (value == 0.0 && Double.doubleToRawLongBits(value) < 0) {
                return "-0x0.0p0";
            }
            return Double.toHexString(value);
        }

        // -- emission ----------------------------------------------------------------

        String emit() {
            out.append("-- deal.semantic-ir/1 shared LuaJIT artifact (ISSUE-0410 "
                + "decomposition tail)\n");
            // The shared run state (frames, sequence, allocation ids, the
            // async task registry and FIFO queue) is chunk-global: a
            // multi-module drive runs several artifacts in one process,
            // and the execution state is one — exactly the oracle's one
            // execution per run. __module stays chunk-local (every chunk
            // names its own module in its events).
            out.append("__frames = __frames or {}\n");
            // The function-id -> owning-module resolution of the dynamic
            // dispatch's DEAL_BODY class path (ISSUE-0658;
            // dynamic-call-shape-production-and-emission Y6): one
            // chunk-global row per lowered function of the closure, built
            // by the same walk that declares the function factories below.
            // A carrier whose function id has no row identifies no class
            // and the dynamic call fails closed at its origin.
            out.append("__fnModules = __fnModules or {}\n");
            out.append("__seq = __seq or 0\n");
            out.append("local __module\n");
            // The nesting-safe module save/restore stack of the
            // cross-module CLASS_FACTORY transfer: one push per transfer,
            // one pop per restore — a transfer nested inside another
            // (an owner default that constructs another module's class)
            // restores its own saved module, never the enclosing one's.
            out.append("local __modStack = {}\n");
            // The nesting-safe invocation-state stack (ISSUE-0654): one
            // push per re-entrant body invocation, one pop per restore — a
            // nested invocation of the same body (recursion) restores its
            // own saved private state, never the enclosing invocation's.
            // A chunk-level local, not a per-site Lua local: a `goto` (the
            // return trampolines) may never enter a local's scope; the
            // per-body active markers are shared across chunks like the
            // rest of the run state (a cross-chunk drive re-enters a body
            // through the export surface).
            out.append("local __svStack = {}\n");
            out.append("__bodyActive = __bodyActive or {}\n");
            out.append("__allocIds = __allocIds or {}\n");
            out.append("__allocNext = __allocNext or 1\n");
            // The mode flag of the prelude's console realization (M4): the
            // row invoker's single-effect write branches on it, so the
            // direct STDLIB_CALL arm and the cataloged callable share one
            // console realization in both modes. Chunk-local (like __module),
            // so a second chunk of one process never changes this chunk's
            // mode.
            out.append("local __traceMode = ").append(trace ? "true" : "false")
                .append("\n");
            out.append(PRELUDE);
            out.append(PRELUDE_ASYNC);
            out.append(JSON_PRELUDE);
            if (!trace) {
                // Production: the event helpers are no-ops.
                out.append("__ev = function() end\n");
                out.append("__normalizeEvent = function() end\n");
            }
            // The per-module export-surface registry (K15 item 1: the
            // module's namespace value): one surface per module of the
            // closure, keyed by the module identity (the dotted module
            // path), created idempotently before the module walks — the
            // registry is chunk-global and every surface keeps its
            // published entries, so a repeated deferred-main drive or a
            // second chunk of the same process never wipes a surface. It
            // is declared in both modes: every E7-lowered unit with
            // exports carries EXPORT_PUBLISH ops (SemanticLowerer's
            // emitE7Terminals) whose publication emission references the
            // registry — a trace-mode session over such a unit must emit
            // valid Lua too (production-only is the entry-surface return
            // terminal, not the declaration).
            out.append("__exportSurfaces = __exportSurfaces or {}\n");
            // The program-scoped cataloged-callable registry (M4): one
            // carrier per catalog row per module per program, so a read
            // before any surface population and the later whole-surface
            // population observe one callable object; chunk-global exactly
            // like the surface registry (a second chunk of the same
            // process resolves the same callables).
            out.append("__stdlibEntries = __stdlibEntries or {}\n");
            // The program-scoped intrinsic carriers (J2): one memoized
            // class-tagged carrier per intrinsic kind per program, so
            // every materialization of one intrinsic (a seed init, a load,
            // an adapter operand, a residual read) observes the identical
            // object and functions compare by reference identity;
            // chunk-global exactly like the surface and stdlib registries
            // (a second chunk of the same process resolves the same
            // carriers).
            out.append("__intrinsicCarriers = __intrinsicCarriers or {}\n");
            // The host-module loader of the chunk (ISSUE-0650, extended by
            // ISSUE-0668): a project chunk whose closure carries a HOST-kind
            // import (host or extern-C) requires the deployed runtime's landed
            // loaders and the host-boundary cells in both modes, independent
            // of whether the session carries the compile's declaration surface
            // — the trace project entry's loaded surface is the scenario
            // seam's, and its FFI arms (__hostParamCell/__hostProjectArg/
            // __hostReturnCell, __rt.class_plan_) reference only bound
            // helpers. A per-unit session keeps the landed gate (it carries
            // no closure and no declaration surface), and a host-free chunk
            // keeps its self-contained prelude.
            if (bindsHostRuntime()) {
                out.append("local __rt = require(\"deal.runtime\")\n");
                out.append(HOST_BOUNDARY_PRELUDE);
            }
            for (LoweredModuleUnit moduleUnit : units.values()) {
                String moduleKey = luaString(moduleUnit.moduleId().path());
                out.append("__exportSurfaces[").append(moduleKey)
                    .append("] = __exportSurfaces[").append(moduleKey)
                    .append("] or {}\n");
            }
            emitStdlibSurfacePopulation();
            // The host-driven callback dispatch table (CALLBACK_INVOKE):
            // a chunk-global in both modes — the per-unit dispatch entries
            // and the two host-seam helpers are the scenario host's
            // invocation surface.
            out.append("__callbacks = {}\n");
            out.append("__callbacks.__hostAtom = __hostAtom\n");
            out.append("__callbacks.__errtext = __errtext\n");
            // The async host seam defaults: the scenario host adapter
            // overrides both entries before any drive; an async host
            // operation without the override is a producer defect, never
            // a silent projection.
            out.append("__callbacks.__hostStartAsync = function(label, ...)\n");
            out.append("  error(\"an async host start has no deterministic host seam "
                + "(the scenario host drives it)\", 0)\n");
            out.append("end\n");
            out.append("__callbacks.__hostCompleteAsync = function(label)\n");
            out.append("  error(\"an async host completion has no deterministic host "
                + "seam (the scenario host drives it)\", 0)\n");
            out.append("end\n");
            // The host-driven async-entry dispatch table (async
            // EXTERNAL_ENTRY records): one entry per recorded async
            // export keyed by module#export; shared across chunks in a
            // multi-module drive (never wiped by a later chunk).
            out.append("__asyncEntries = __asyncEntries or {}\n");
            // The per-module MODULE_INIT lifecycle records (E8): chunk-
            // global like the rest of the run state (a multi-module drive
            // runs several artifacts in one process and each module
            // initializes once after its dependencies).
            out.append("__moduleStates = __moduleStates or {}\n");
            out.append("\n__module = ").append(luaString(unit.moduleId().path()))
                .append("\n");
            // One env table carries every slot and cell (LuaJIT's upvalue
            // limit never binds the function bodies).
            out.append("local S = {}\n");
            // Hoisted shared temps (goto can never jump into a local's
            // scope; every check/return temp is a top-level assignment).
            out.append("local __chk, __rvT, __rvcT, __okT, __resT, __terrT, "
                + "__cerrT, __wrappedT, __itT, __itnT, __elemT, __okB, __chkB, "
                + "__okD, __chkD, "
                + "__instT, __fT, __eT, __jokT, __jresT, __jpathT, __jactT, __hbT, "
                + "__dynC, __dynK, __dynM, __dynS, __dynSK, __dynA, __dynE\n");

            // Function factories first (capture cells are factory
            // arguments); the local names are pre-declared so bodies can
            // reference factories declared later in source order. The
            // detached class-default functions are pre-declared the same
            // way: a DEAL function body (or a re-executed thunk body)
            // reaches its CLASS_DEFAULT functions from the construction
            // sites emitted inside the factories, so a `local function`
            // declaration placed after the factories would leave every
            // such reference a nil global.
            List<String> factoryNames = new ArrayList<>();
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (LoweredFunction function : moduleUnit.functions().values()) {
                    factoryNames.add(fnFactory(function.functionId()));
                }
            }
            List<String> defaultNames = new ArrayList<>();
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        defaultNames.add(defaultFn(op.opId()));
                    }
                }
            }
            if (!factoryNames.isEmpty()) {
                out.append("local ").append(String.join(", ", factoryNames))
                    .append("\n");
            }
            if (!defaultNames.isEmpty()) {
                out.append("local ").append(String.join(", ", defaultNames))
                    .append("\n");
            }
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (LoweredFunction function : moduleUnit.functions().values()) {
                    emitFunctionFactory(function);
                    // The function-id -> owning-module resolution row of
                    // the dynamic dispatch's DEAL_BODY class path
                    // (ISSUE-0658; Y6): the same walk that declares the
                    // factory registers the function's owning module, so
                    // a dynamically invoked carrier establishes the
                    // callee's module context before its body runs.
                    out.append("__fnModules[")
                        .append(function.functionId().id()).append("] = ")
                        .append(luaString(moduleUnit.moduleId().path()))
                        .append("\n");
                }
            }

            // The REEVALUATE_THUNK re-executors: one detached thunk
            // function per FUNCTION_ADAPT op with a thunk source. The
            // thunk ops are members only of the detached thunk block (the
            // lowerer's single-membership rule), so the module walk never
            // executes them; each invocation re-executes them here.
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() != SemanticOpKind.FUNCTION_ADAPT) {
                        continue;
                    }
                    KindPayload.FunctionAdaptPayload payload =
                        (KindPayload.FunctionAdaptPayload) op.payload();
                    if (payload.source() instanceof AdaptSourceRef.Thunk thunk) {
                        emitThunkFunction(op, thunk.blockId());
                    }
                }
            }

            // The detached class-default functions (E5): one per
            // CLASS_DEFAULT op — the default block's ops (the default op
            // itself skipped) re-execute per invocation, returning the
            // block's final producing value (the op's result slot), so
            // every triggering construction gets a fresh default
            // (mutable defaults allocate freshly per attempt). The names
            // are the chunk-level locals pre-declared with the factory
            // names above: a construction inside a function body (or a
            // re-executed thunk body) emits its `pcall(D<opId>)` call into
            // the factory emitted before this block, so the assignment
            // form keeps that reference bound to the chunk-level local
            // instead of a nil global.
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        emitClassDefaultFunction(op);
                    }
                }
            }

            // The per-class JSON plans (E7/K-D8/K-D10): one plan per
            // class layout of the resolution context — declaration-order
            // fields with descriptor, optionality, static result kind,
            // and the per-field CLASS_DEFAULT child metadata the
            // JSON_FROM_CLASS walk consumes (the lowerer's per-site
            // JsonDefaultChildTable entry, derived from the unit: one
            // CLASS_DEFAULT op per (classId, field)).
            for (ClassLayout layout : classLayouts.values()) {
                emitJsonPlan(layout);
            }

            // The module-init blocks (the entry delegation included) in
            // dependency order inside one deferred-main wrapper so uncaught
            // DEAL failures publish the single R|failure terminal. Each
            // module's walk runs inside its MODULE_INIT envelope when the
            // unit carries the lowerer-produced op (E8: the op's START,
            // the payload init block nested under it, the SUCCESS terminal
            // publishing state:INITIALIZED, or the FAILURE terminal
            // recording FAILED(error) with no export publication); a
            // hand-built unit without the op runs the bare init block,
            // exactly the pre-envelope behavior. The walk is exposed as
            // the deferred-main entry (the scenario host drives it
            // explicitly under the defer flag — module initialization
            // before an async-entry invocation, or the entry module's walk
            // in a multi-module drive); the conformance artifact skips the
            // walk under the callback-only drive flag (the semantic
            // oracle's invokeCallback surface never runs the module-init
            // block).
            out.append("__dealMain = function()\n");
            out.append("  local __mainOk, __mainErr = pcall(function()\n");
            for (LoweredModuleUnit moduleUnit : units.values()) {
                out.append("  __module = ")
                    .append(luaString(moduleUnit.moduleId().path())).append("\n");
                SemanticOp moduleInitOp = moduleInitOpOf(moduleUnit);
                if (moduleInitOp == null) {
                    emitBlockOps(moduleUnit.moduleInit().initBlock());
                } else {
                    emitModuleInit(moduleInitOp);
                }
            }
            out.append("  end)\n");
            out.append("  if __mainOk then return true, nil end\n");
            out.append("  return false, __mainErr\n");
            out.append("end\n");
            out.append("if os.getenv(\"DEAL_DEFER_MAIN\") ~= \"1\" and "
                + "os.getenv(\"DEAL_CALLBACK_ONLY\") ~= \"1\" then\n");
            out.append("local __mainOk, __mainErr = __dealMain()\n");
            if (trace) {
                out.append("if __mainOk then\n");
                out.append("  io.stderr:write(\"R|success|null\\n\")\n");
                out.append("else\n");
                out.append("  io.stderr:write(\"R|failure|\"..__errtext(__mainErr)..\"\\n\")\n");
                out.append("end\n");
                out.append("io.stderr:flush()\n");
            } else {
                // Production terminal: a DEAL failure publishes the
                // retained DEAL_ERROR_CODE line on stdout and exits 1; a
                // non-DEAL failure rethrows; success returns the exports.
                out.append("if not __mainOk then\n");
                out.append("  if type(__mainErr) == \"table\" and __mainErr.__d then\n");
                out.append("    print(\"DEAL_ERROR_CODE: \"..__mainErr.code)\n");
                out.append("  else\n");
                out.append("    error(__mainErr, 0)\n");
                out.append("  end\n");
                out.append("  os.exit(1)\n");
                out.append("end\n");
            }
            out.append("end\n");

            // The host-driven callback dispatch entries (CALLBACK_INVOKE):
            // one per-unit entry per recorded invocation, defined after the
            // module-init walk in both modes (the block walk never runs the
            // unattached records themselves).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.CALLBACK_INVOKE) {
                        emitCallbackInvoke(op);
                    }
                }
            }

            // The host-driven async-entry dispatch entries (async
            // EXTERNAL_ENTRY): one entry per recorded async export of
            // every closure unit, keyed by module#export — the scenario
            // host adapter's invocation surface (the E6 dispatch-entry
            // pattern). The entry creates the callee's canonical task;
            // the drive flag makes the top-level scenario invocation drain
            // it and return the completion, while a cross-module caller
            // passes the drive flag false (its AWAIT drains). The
            // per-closure loop is the same shape the CALLBACK_INVOKE
            // entries above use: a non-entry module's async export is
            // reachable in the one artifact (ISSUE-0655,
            // cross-module-call-realization X2).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                            && ((KindPayload.ExternalEntryPayload) op.payload()).async()) {
                        emitAsyncEntry(op, moduleUnit);
                    }
                }
            }
            if (!trace) {
                // The retained-caller ABI: the artifact returns its own
                // module's export surface (the entry module's surface in
                // project mode, the single module's surface otherwise).
                out.append("return __exportSurfaces[")
                    .append(luaString(unit.moduleId().path())).append("]\n");
            }
            return out.toString();
        }

        /**
         * Whether the chunk carries the runtime binding and the host-boundary
         * prelude (ISSUE-0650, extended by ISSUE-0668 and ISSUE-0678): a
         * project session whose closure's op walk carries a HOST-kind import
         * (host or extern-C), read from the closure's own {@code MODULE_IMPORT}
         * ops — never from the session's declaration surface, so the trace
         * project entry without the compile's declaration surface binds the
         * runtime for its FFI arms exactly like the production project session
         * does — or a host-boundary cell of its own (the
         * {@code DEAL_TO_HOST}/{@code HOST_PARAMETER}/{@code HOST_TO_DEAL}/
         * {@code HOST_SYNC_RETURN} family), whose emitted checks are the host
         * prelude's: a spec-stdlib declared-function export read called as a
         * value carries the same host cell family (K2) without any host import,
         * so its chunk binds the helpers too.
         */
        private boolean bindsHostRuntime() {
            return projectSession && (hasHostImports() || hasHostCellBoundaries());
        }

        /**
         * Whether the session's op walk carries at least one host-boundary cell
         * (the family the host prelude's parameter/return checks realize).
         */
        private boolean hasHostCellBoundaries() {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() != SemanticOpKind.BOUNDARY
                            || !(op.payload()
                                instanceof KindPayload.BoundaryPayload boundary)) {
                        continue;
                    }
                    BoundaryKind kind = boundary.kind();
                    FailurePolicyId policy = op.failurePolicy();
                    if (kind == BoundaryKind.DEAL_TO_HOST || kind == BoundaryKind.HOST_TO_DEAL
                            || policy == FailurePolicyId.HOST_PARAMETER
                            || policy == FailurePolicyId.HOST_SYNC_RETURN) {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Whether the session's op walk carries at least one HOST-kind
         * import (host or extern-C).
         */
        private boolean hasHostImports() {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.MODULE_IMPORT
                            && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                                == ModuleImportKind.HOST) {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * The cataloged callable surfaces of the session's STDLIB imports
         * (M4/K15 item 1): one surface entry per catalog row of every
         * imported STDLIB module, in catalog order, created through the one
         * memoized accessor ({@code __stdlibEntry}) — the whole-surface
         * population and the read resolve the identical callable object per
         * row, and the surface is written only by this session-scoped
         * catalog memoization (never re-derived per read).
         */
        private void emitStdlibSurfacePopulation() {
            for (Map.Entry<ModuleId, ModuleImportKind> imported : importKinds.entrySet()) {
                if (imported.getValue() != ModuleImportKind.STDLIB) {
                    continue;
                }
                String modulePath = imported.getKey().path();
                List<StdlibFunctionCatalog.Entry> rows = stdlibRowsOf(modulePath);
                if (rows.isEmpty()) {
                    throw new IllegalStateException("the STDLIB import of module '"
                        + modulePath + "' resolves no closed catalog row (the catalog"
                        + " is the resolution authority — a producer defect)");
                }
                String key = luaString(modulePath);
                out.append("__exportSurfaces[").append(key).append("] = ")
                    .append("__exportSurfaces[").append(key).append("] or {}\n");
                for (StdlibFunctionCatalog.Entry row : rows) {
                    out.append("__exportSurfaces[").append(key).append("][")
                        .append(luaString(row.exportName())).append("] = ")
                        .append("__stdlibEntry(")
                        .append(stdlibRowArgs(row)).append(")\n");
                }
            }
        }

        /**
         * The closed catalog rows of one imported stdlib module, in catalog
         * order (the pinned declaration order of the one catalog authority);
         * an unimported or unknown module has none.
         */
        private static List<StdlibFunctionCatalog.Entry> stdlibRowsOf(String modulePath) {
            List<StdlibFunctionCatalog.Entry> rows = new ArrayList<>();
            for (StdlibFunctionCatalog.Entry row : StdlibFunctionCatalog.entries()) {
                if (row.modulePath().equals(modulePath)) {
                    rows.add(row);
                }
            }
            return rows;
        }

        /**
         * The one catalog row of one {@code (module path, export name)} pair,
         * or a producer defect: the lowering's STDLIB guard already rejects an
         * out-of-catalog member, so an emitted read always names a row.
         */
        private static StdlibFunctionCatalog.Entry stdlibRowOf(String modulePath,
                                                              String exportName) {
            return StdlibFunctionCatalog.lookup(modulePath, exportName)
                .orElseThrow(() -> new IllegalStateException("the STDLIB export read '"
                    + modulePath + "#" + exportName + "' resolves no closed catalog row"
                    + " (the catalog is the STDLIB kind's resolution authority — a"
                    + " producer defect)"));
        }

        /**
         * The interning argument list of one cataloged callable
         * ({@code __stdlibEntry(module, name, rowTag, signature, spec)}): the
         * row's declared descriptor text ({@code __sig}) and its canonical
         * spec text ({@code __csig}) — the row's declared signature, never
         * the reading site's.
         */
        private static String stdlibRowArgs(StdlibFunctionCatalog.Entry row) {
            return luaString(row.modulePath()) + ", " + luaString(row.exportName())
                + ", " + luaString(row.function().name()) + ", "
                + luaString(descriptorText(row.declaredDescriptor())) + ", "
                + luaString(row.declaredDescriptor().canonicalSpecText());
        }

        /**
         * Emits one detached class-default function: the default block's
         * ops in order (the CLASS_DEFAULT op itself skipped — its own
         * events are the triggering CLASS_NEW/CLASS_FACTORY arm's) and
         * the final producing value returned. The name is a pre-declared
         * chunk-level local (see the preamble): the assignment form keeps
         * the function reachable from every factory/construction body
         * emitted before this statement.
         */
        private void emitClassDefaultFunction(SemanticOp defaultOp) {
            KindPayload.ClassDefaultPayload payload =
                (KindPayload.ClassDefaultPayload) defaultOp.payload();
            StructuredBodyTable ownerTable = blockTableOf.get(payload.defaultBlock());
            List<OpId> ops = ownerTable == null
                ? null : ownerTable.blockOps().get(payload.defaultBlock());
            if (ops == null) {
                throw new IllegalStateException("the class-default block "
                    + payload.defaultBlock() + " has no membership row (producer defect)");
            }
            if (!(defaultOp.result() instanceof ValueId resultId)) {
                throw new IllegalStateException("CLASS_DEFAULT " + defaultOp.opId()
                    + " publishes no ValueId result (producer defect)");
            }
            out.append(defaultFn(defaultOp.opId())).append(" = function()\n");
            for (OpId opId : ops) {
                if (opId.equals(defaultOp.opId()) || ownedChildren.contains(opId)) {
                    continue;
                }
                emitOp(opsById.get(opId));
            }
            out.append("  return ").append(slot(resultId)).append("\n");
            out.append("end\n");
        }

        /** One detached class-default function name of a CLASS_DEFAULT op. */
        private String defaultFn(OpId defaultOp) {
            return "D" + defaultOp.id();
        }

        /**
         * Emits one detached thunk re-executor for a FUNCTION_ADAPT op
         * with a REEVALUATE_THUNK source: the thunk block's ops run in
         * order (payload-owned children included through their owner
         * arms) and the function returns the final producing op's result
         * — the source value the invocation consumes.
         */
        private void emitThunkFunction(SemanticOp adaptOp, BlockId block) {
            StructuredBodyTable ownerTable = blockTableOf.get(block);
            List<OpId> ops = ownerTable == null ? null : ownerTable.blockOps().get(block);
            if (ops == null) {
                throw new IllegalStateException("the adapter thunk block " + block
                    + " has no membership row (producer defect)");
            }
            out.append("local function ").append(thunkFn(adaptOp.opId())).append("()\n");
            emitBlockOps(block);
            ValueId produced = null;
            for (int i = ops.size() - 1; i >= 0; i--) {
                OpId opId = ops.get(i);
                if (ownedChildren.contains(opId)) {
                    continue;
                }
                SemanticOp op = opsById.get(opId);
                if (op != null && op.result() instanceof ValueId valueId) {
                    produced = valueId;
                }
                break;
            }
            if (produced == null) {
                throw new IllegalStateException("the adapter thunk block " + block
                    + " has no final producing value (producer defect)");
            }
            out.append("  return ").append(slot(produced)).append("\n");
            out.append("end\n");
        }

        /** One thunk re-executor name of an adapter op. */
        private String thunkFn(OpId adaptOp) {
            return "T" + adaptOp.id();
        }

        /** Emits one function factory: a closure over the passed capture cells. */
        private void emitFunctionFactory(LoweredFunction function) {
            FunctionId functionId = function.functionId();
            List<BindingId> captures = function.captures();
            StringBuilder params = new StringBuilder();
            for (BindingId captureId : captures) {
                if (params.length() > 0) {
                    params.append(", ");
                }
                params.append("c" + captureId.id());
            }
            out.append(fnFactory(functionId)).append(" = function(")
                .append(params).append(")\n");
            out.append("  return function(...)\n");
            out.append("    local __args = {...}\n");
            int argIndex = 1;
            List<OpId> bodyOps = tableOfFunction(function).blockOps().get(function.body());
            currentFunctionId = functionId;
            int paramCount = function.descriptor().paramTypes().size();
            for (int i = 0; i < paramCount && i < bodyOps.size(); i++) {
                SemanticOp op = opsById.get(bodyOps.get(i));
                if (op.kind() != SemanticOpKind.BINDING_ALLOC) {
                    break;
                }
                KindPayload.BindingAllocPayload payload =
                    (KindPayload.BindingAllocPayload) op.payload();
                BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                    BindingCellKind.DIRECT);
                out.append("    ").append(cell(payload.binding(), payload.generation())).append(" = ")
                    .append(kind == BindingCellKind.SHARED_CELL
                        ? "{__args[" + argIndex + "]}" : "__args[" + argIndex + "]")
                    .append("\n");
                argIndex++;
            }
            for (int i = paramCount; i < bodyOps.size(); i++) {
                if (ownedChildren.contains(bodyOps.get(i))) {
                    continue;
                }
                emitOp(opsById.get(bodyOps.get(i)));
            }
            // The function's return trampoline: every RETURN of the
            // body jumps here (a raw Lua return inside a structure block
            // would be followed by the structure's closing label, and a
            // trailing label after a raw top-level return is equally
            // invalid — one uniform trampoline keeps every shape valid).
            out.append("::").append(returnLabel(functionId)).append("::\n");
            out.append("  return __rvcT\n");
            out.append("  end\n");
            out.append("end\n");
            currentFunctionId = null;
        }

        /** The membership table of the unit owning one lowered function. */
        private StructuredBodyTable tableOfFunction(LoweredFunction function) {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                if (moduleUnit.functions().containsKey(function.functionId())) {
                    return tables.get(moduleUnit.moduleId());
                }
            }
            return table;
        }

        /** Emits the ops of one block inline. */
        private void emitBlockOps(BlockId block) {
            StructuredBodyTable ownerTable = blockTableOf.get(block);
            if (ownerTable == null) {
                ownerTable = table;
            }
            for (OpId opId : ownerTable.blockOps().get(block)) {
                if (ownedChildren.contains(opId)) {
                    continue;
                }
                if (skippedOps.contains(opId)) {
                    continue;
                }
                emitOp(opsById.get(opId));
            }
        }

        /** Emits a block's ops under a label section. */
        private void emitLabeledBlock(BlockId block) {
            out.append("::").append(label(block)).append("::\n");
            emitBlockOps(block);
        }

        // -- per-op emission ---------------------------------------------------------

        private void emitOp(SemanticOp op) {
            switch (op.kind()) {
                case CONST -> emitConst(op);
                case UNARY -> emitUnary(op);
                case BINARY -> emitBinary(op);
                case STRING_CONCAT -> emitConcat(op);
                case ARRAY_NEW -> emitArrayNew(op);
                case TABLE_NEW -> emitTableNew(op);
                case ARRAY_LENGTH -> emitArrayLength(op);
                case MEMBER_READ -> emitMemberRead(op);
                case MEMBER_WRITE -> emitMemberWrite(op);
                case MEMBER_DELETE -> emitMemberDelete(op);
                case INDEX_NORMALIZE -> emitNormalize(op);
                case INDEX_READ -> emitIndexRead(op);
                case INDEX_WRITE -> emitIndexWrite(op);
                case INDEX_DELETE -> emitIndexDelete(op);
                case OPTIONAL_READ -> emitOptionalRead(op);
                case HAS_FIELD -> emitHasField(op);
                case FIELD_READ -> emitFieldRead(op);
                case FIELD_WRITE -> emitFieldWrite(op);
                case FIELD_DELETE -> emitFieldDelete(op);
                case BOUNDARY -> emitFreeBoundary(op);
                case BINDING_ALLOC -> emitBindingAlloc(op);
                case BINDING_INIT -> emitBindingInit(op);
                case BINDING_LOAD -> emitBindingLoad(op);
                case BINDING_STORE -> emitBindingStore(op);
                case CLOSURE_NEW -> emitClosureNew(op);
                case RECURSIVE_GROUP_INIT -> emitRecursiveGroupInit(op);
                case FUNCTION_ADAPT -> emitFunctionAdapt(op);
                case CALLBACK_INVOKE -> emitCallbackInvoke(op);
                case ASYNC_START -> emitAsyncStart(op);
                case AWAIT -> emitAwait(op);
                case ASSIGN -> emitAssign(op);
                case DELETE -> emitDelete(op);
                case CALL -> emitCall(op);
                case INTRINSIC_CALL -> emitIntrinsic(op);
                case STDLIB_CALL -> emitStdlib(op);
                case BRANCH -> emitBranch(op);
                case LOOP -> emitLoop(op);
                case FOR_EACH -> emitForEach(op);
                case TRY_CATCH -> emitTryCatch(op);
                case THROW -> emitThrow(op);
                case RETURN -> emitReturn(op);
                case BREAK -> emitBreak(op);
                case CONTINUE -> emitContinue(op);
                case DISCARD -> emitDiscard(op);
                case MODULE_IMPORT -> emitModuleImport(op);
                case EXPORT_READ -> emitExportRead(op);
                case EXPORT_PUBLISH -> emitExportPublish(op);
                case EXTERNAL_ENTRY -> emitExternalEntryRecord(op);
                case ENTRY_INVOKE -> emitEntryInvoke(op);
                case MODULE_INIT -> emitModuleInit(op);
                case JSON_FROM_CLASS -> emitJsonFromClass(op);
                case JSON_TO_CLASS -> emitJsonToClass(op);
                case CLASS_NEW -> emitClassNew(op);
                case CLASS_DEFAULT -> throw new IllegalStateException("a CLASS_DEFAULT "
                    + "executes only under its triggering CLASS_NEW/CLASS_FACTORY "
                    + "(the detached default block's ops are the class-default "
                    + "function's; the block walk never runs the op itself)");
                case CLASS_FACTORY -> throw new IllegalStateException("a CLASS_FACTORY "
                    + "is a detached owner-module entry executed only under the "
                    + "triggering caller's CLASS_NEW (cross-unit parent) — the "
                    + "block walk never runs it)");
                default -> throw new IllegalStateException("op kind " + op.kind()
                    + " has no shared-LuaJIT emission in this decomposition-tail "
                    + "domain");
            }
        }

        private String opKey(OpId id) {
            return id.module().path() + "#" + id.id();
        }

        private String parentKey(OpId parent) {
            return parent == null ? "-" : opKey(parent);
        }

        private void emitStart(SemanticOp op) {
            out.append("__ev(").append(luaString(opKey(op.opId()))).append(", \"START\", ")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", {");
            for (int i = 0; i < op.operands().size(); i++) {
                if (i > 0) {
                    out.append(", ");
                }
                out.append("__atom(")
                    .append(luaString(staticKind(op.operandTypes().get(i))))
                    .append(", ").append(slot(op.operands().get(i))).append(")");
            }
            out.append("}, nil, nil)\n");
        }

        /** A boundary START event with its input atom. */
        /** START with the closed slot atom for the second operand (slot ops). */
        private void emitSlotOperandStart(SemanticOp op) {
            out.append("__ev(").append(luaString(opKey(op.opId()))).append(", \"START\", ")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", {");
            out.append("__atom(").append(luaString(staticKind(op.operandTypes().get(0))))
                .append(", ").append(slot(op.operands().get(0))).append(")");
            out.append(", __slotAtom(").append(slot(op.operands().get(1))).append(")");
            for (int i = 2; i < op.operands().size(); i++) {
                out.append(", __atom(")
                    .append(luaString(staticKind(op.operandTypes().get(i))))
                    .append(", ").append(slot(op.operands().get(i))).append(")");
            }
            out.append("}, nil, nil)\n");
        }

        private void emitBoundaryStart(SemanticOp boundary, String inputExpr,
                                       RuntimeDescriptor inputDescriptor) {
            out.append("__ev(").append(luaString(opKey(boundary.opId())))
                .append(", \"START\", \"BOUNDARY\", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId())))
                .append(", {__atom(").append(luaString(staticKind(inputDescriptor)))
                .append(", ").append(inputExpr).append(")}, nil, nil)\n");
        }

        private void emitBoundarySuccess(SemanticOp boundary, String valueExpr,
                                         RuntimeDescriptor descriptor) {
            out.append("__ev(").append(luaString(opKey(boundary.opId())))
                .append(", \"SUCCESS\", \"BOUNDARY\", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId())))
                .append(", {}, __atom(").append(luaString(staticKind(descriptor)))
                .append(", ").append(valueExpr).append("), nil)\n");
        }

        /** SUCCESS with the produced result atom. */
        private void emitResultSuccess(SemanticOp op, String valueExpr,
                                       RuntimeDescriptor resultDescriptor) {
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, __atom(").append(luaString(staticKind(resultDescriptor)))
                .append(", ").append(valueExpr).append("), nil)\n");
        }

        private void emitPlainSuccess(SemanticOp op) {
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, nil, nil)\n");
        }

        /** The raw SUCCESS emission of a structure closed by a transfer. */
        private void emitClosedSuccess(SemanticOp op) {
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, nil, nil)\n");
        }

        /** The structure op whose payload references the given block, or null. */
        private SemanticOp structureReferencing(BlockId block) {
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

        /**
         * The structure ancestors of a block, innermost first (static). The
         * enclosing block of one structure op comes from *its own* unit's
         * membership table ({@code blockTableOf}): a callee unit's nested
         * blocks belong to the callee's table, never the entry module's, so
         * a transfer inside a cross-module callee body closes exactly the
         * structures it nests in.
         */
        private List<SemanticOp> structureAncestors(BlockId block) {
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
         * A result SUCCESS event atomized by the value's own kind (the
         * deferred composite read: the pass-through admits a value whose
         * runtime variant need not match the read's internal result kind,
         * and the oracle's publish atomizes the value, never the kind).
         */
        private void emitResultSuccessAtom(SemanticOp op, String valueExpr) {
            RuntimeDescriptor resultDescriptor = (RuntimeDescriptor) op.resultType();
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, __rawArgAtom(")
                .append(luaString(staticKind(resultDescriptor))).append(", ")
                .append(valueExpr).append("), nil)\n");
        }

        /** Emits the transfer closures of the ancestors down to (and including)
         *  the target loop; stops at an enclosing TRY_CATCH when requested
         *  (its dispatch closes it). */
        private void emitTransferClosures(SemanticOp transferOp, SemanticOp targetLoop,
                                          boolean stopAtTry) {
            BlockId block = opBlock.get(transferOp.opId());
            for (SemanticOp ancestor : structureAncestors(block)) {
                if (stopAtTry && ancestor.kind() == SemanticOpKind.TRY_CATCH) {
                    return;
                }
                // The target loop itself is NOT closed here: a BREAK/CONTINUE
                // exits or re-enters it and its normal success line runs at
                // the loop exit (the oracle's loop wrapper emits it once).
                if (targetLoop != null && ancestor.opId().equals(targetLoop.opId())) {
                    return;
                }
                emitClosedSuccess(ancestor);
            }
        }

        private void emitFailureEvent(OpId id, String kindName, SemanticOp op,
                                      String errExpr) {
            out.append("__ev(").append(luaString(opKey(id))).append(", \"FAILURE\", ")
                .append(luaString(kindName)).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, nil, ").append(errExpr).append(")\n");
        }

        private String originOf(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                return "-";
            }
            return op.origin().sourceId() + ":" + span.startLine() + ":"
                + span.startColumn();
        }

        // -- ops ----------------------------------------------------------------

        private void emitConst(SemanticOp op) {
            KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
            String literal = switch (payload.value()) {
                case ScalarValue.Null ignored -> "nil";
                case ScalarValue.Boolean bool -> bool.value() ? "true" : "false";
                case ScalarValue.Int intValue -> String.valueOf(intValue.value());
                case ScalarValue.Number number -> luaNumber(number.value());
                case ScalarValue.String string -> luaString(string.value());
            };
            emitStart(op);
            out.append(slot((ValueId) op.result())).append(" = ").append(literal)
                .append("\n");
            emitResultSuccess(op, slot((ValueId) op.result()), op.resultType()
                instanceof RuntimeDescriptor descriptor ? descriptor : null);
        }

        private void emitUnary(SemanticOp op) {
            KindPayload.UnaryPayload payload = (KindPayload.UnaryPayload) op.payload();
            ValueId input = op.operands().get(0);
            emitStart(op);
            if (payload.selector() == deal.semantic.ir.UnarySelector.BOOL_NOT) {
                out.append(slot((ValueId) op.result())).append(" = not ")
                    .append(slot(input)).append("\n");
            } else {
                out.append(slot((ValueId) op.result())).append(" = __unary(")
                    .append(luaString(payload.selector().name())).append(", ")
                    .append(slot(input)).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op))).append(")\n");
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        private void emitBinary(SemanticOp op) {
            KindPayload.BinaryPayload payload = (KindPayload.BinaryPayload) op.payload();
            emitStart(op);
            boolean arithmetic = payload.selector().name().startsWith("INT32_")
                || payload.selector().name().startsWith("NUMBER_");
            boolean comparison = payload.selector().name().endsWith("_EQ")
                || payload.selector().name().endsWith("_NE")
                || payload.selector().name().endsWith("_LT")
                || payload.selector().name().endsWith("_LE")
                || payload.selector().name().endsWith("_GT")
                || payload.selector().name().endsWith("_GE");
            if (arithmetic && !comparison) {
                out.append(slot((ValueId) op.result())).append(" = __arith(")
                    .append(luaString(payload.selector().name())).append(", ")
                    .append(slot(op.operands().get(0))).append(", ")
                    .append(slot(op.operands().get(1))).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op))).append(")\n");
                emitResultSuccess(op, slot((ValueId) op.result()),
                    (RuntimeDescriptor) op.resultType());
                return;
            }
            out.append(slot((ValueId) op.result())).append(" = __cmp(")
                .append(luaString(payload.selector().name())).append(", ")
                .append(luaString(staticKind(op.operandTypes().get(0)))).append(", ")
                .append(slot(op.operands().get(0))).append(", ")
                .append(luaString(staticKind(op.operandTypes().get(1)))).append(", ")
                .append(slot(op.operands().get(1))).append(", ")
                .append(payload.side() == null ? "nil"
                    : luaString(payload.side().name())).append(")\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        private void emitConcat(SemanticOp op) {
            KindPayload.StringConcatPayload payload =
                (KindPayload.StringConcatPayload) op.payload();
            emitStart(op);
            StringBuilder expr = new StringBuilder();
            for (ValueId fragment : payload.fragments()) {
                if (expr.length() > 0) {
                    expr.append("..");
                }
                expr.append("(").append(slot(fragment)).append(" or \"\")");
            }
            out.append(slot((ValueId) op.result())).append(" = ")
                .append(expr.length() == 0 ? "\"\"" : expr).append("\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        private void emitArrayNew(SemanticOp op) {
            KindPayload.ArrayNewPayload payload = (KindPayload.ArrayNewPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = {__a = true, __n = ")
                .append(payload.values().size()).append("}\n");
            for (int i = 0; i < payload.values().size(); i++) {
                OpId boundaryId = payload.elementBoundaryOpIds().get(i);
                SemanticOp boundary = opsById.get(boundaryId);
                ValueId input = payload.values().get(i);
                emitBoundaryStart(boundary, slot(input), payload.elementDescriptor());
                out.append("__chk = ")
                    .append(bcheckExpr(payload.elementDescriptor(), slot(input)))
                    .append("\n");
                out.append(target).append("[").append(i + 1)
                    .append("] = __chk == nil and __NULL or __chk\n");
                out.append("__numKey(").append(target).append(", ")
                    .append(i + 1).append(", ").append(slot(input)).append(", ")
                    .append(isNumberKind(producerKind(input)) ? "true" : "false")
                    .append(")\n");
                emitBoundarySuccess(boundary, "__chk", payload.elementDescriptor());
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        private void emitTableNew(SemanticOp op) {
            KindPayload.TableNewPayload payload = (KindPayload.TableNewPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = {__t = true, __keys = {}, __order = {}}\n");
            for (KindPayload.TableEntry entry : payload.entries()) {
                out.append(target).append("[").append(luaString(entry.key()))
                    .append("] = ").append(slot(entry.value())).append("\n");
                out.append("__orderAdd(").append(target).append(", ")
                    .append(luaString(entry.key())).append(")\n");
                out.append("__numKey(").append(target).append(", ")
                    .append(luaString(entry.key())).append(", ")
                    .append(slot(entry.value())).append(", ")
                    .append(isNumberKind(producerKind(entry.value())) ? "true" : "false")
                    .append(")\n");
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        private void emitArrayLength(SemanticOp op) {
            KindPayload.ArrayLengthPayload payload =
                (KindPayload.ArrayLengthPayload) op.payload();
            emitStart(op);
            out.append(slot((ValueId) op.result())).append(" = ")
                .append(slot(payload.arrayValue())).append(".__n\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        private void emitMemberRead(SemanticOp op) {
            KindPayload.MemberReadPayload payload = (KindPayload.MemberReadPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = __member(").append(slot(payload.table()))
                .append(", ").append(luaString(payload.key())).append(")\n");
            SemanticOp boundary = boundaryChildOf(op);
            // The read-side variant materialization: the raw read's
            // declared descriptor decides whether an int-variant slot
            // value becomes a carrier (a number-typed read position) and
            // a number-variant slot value becomes a carrier (its slot
            // mark) — the closed value model's admitted variant. A
            // missing-capable read carries its contextual inner
            // descriptor on the consuming OPTIONAL_READ (the raw read's
            // own result type is the internal-missing marker), so the
            // envelope's present branch keeps the admitted variant too.
            SemanticOp optionalRead = optionalReadOf((ValueId) op.result());
            RuntimeDescriptor readDescriptor = boundary != null
                ? ((KindPayload.BoundaryPayload) boundary.payload()).descriptor()
                : (optionalRead != null
                    ? ((KindPayload.OptionalReadPayload) optionalRead.payload())
                        .descriptor()
                    : (op.resultType() instanceof RuntimeDescriptor descriptor
                        ? descriptor : null));
            out.append(target).append(" = __readVar(").append(slot(payload.table()))
                .append(", ").append(luaString(payload.key())).append(", ")
                .append(target).append(", ")
                .append(readDescriptor != null
                    && isNumberKind(staticKind(readDescriptor)) ? "true" : "false")
                .append(")\n");
            if (boundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                // Custom boundary START: the input atom renders the actual
                // value kind (the oracle's atomOf — a wrong-kind present
                // value atomizes as its own kind).
                out.append("__ev(").append(luaString(opKey(boundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(luaString(boundary.contract().canonicalDigest()))
                    .append(", ")
                    .append(luaString(parentKey(boundary.origin().parentOpId())))
                    .append(", {__rawArgAtom(")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(")}, nil, nil)\n");
                // A contextual composite value (ISSUE-0651): the function and
                // array carriers pass through — the consuming declared cell
                // carries the pinned E8010 projection at its own origin (the
                // corpus pins the call-origin failure for a wrong-kind
                // argument whose contextual read sits on the argument
                // expression); every other descriptor keeps the strict row.
                out.append("__okB, __chkB = ")
                    .append(defersContextualCheck(boundaryPayload.descriptor())
                        ? "true, " + target
                        : "pcall(__bcheck, "
                            + luaString(descriptorText(boundaryPayload.descriptor()))
                            + ", "
                            + luaString(staticKind(boundaryPayload.descriptor()))
                            + ", " + target + ")")
                    .append("\n");
                out.append("if not __okB then\n");
                out.append("  __chkB.o = ").append(luaString(originOf(boundary)))
                    .append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                out.append(target).append(" = __chkB\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    // The deferred composite read's SUCCESS atom renders
                    // the value's own kind (the pass-through left a
                    // possibly wrong-kind value in place; the oracle's
                    // atomOf uses the value's own kind too), and the op's
                    // own result SUCCESS renders the same value-aware atom
                    // (the read's internal result kind is not the value).
                    emitBoundarySuccessAtom(boundary, "__rawArgAtom("
                        + luaString(staticKind(boundaryPayload.descriptor()))
                        + ", " + target + ")");
                    emitResultSuccessAtom(op, target);
                } else {
                    emitBoundarySuccess(boundary, target,
                        boundaryPayload.descriptor());
                    emitResultSuccess(op, target,
                        (RuntimeDescriptor) op.resultType());
                }
                return;
            }
            // The OPTIONAL_READ envelope shape: the raw read publishes the
            // internal missing or the present value (present null included)
            // and its SUCCESS atom renders the actual value kind —
            // missing → "missing", null → "null", else the actual-kind
            // atom, exactly the oracle's publish (a wrong-kind present
            // value atomizes as its own kind, never the declared kind).
            RuntimeDescriptor inner = optionalRead == null
                ? null
                : ((KindPayload.OptionalReadPayload) optionalRead.payload()).descriptor();
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, __rawAtom(")
                .append(luaString(inner == null ? "ref" : "nullable:" + staticKind(inner)))
                .append(", ").append(target).append("), nil)\n");
        }

        /**
         * The OPTIONAL_READ op consuming this result value, or null — the
         * envelope shape of a missing-capable table member read.
         */
        private SemanticOp optionalReadOf(ValueId value) {
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
         * OPTIONAL_READ: the internal missing pre-maps to language null
         * before the present branch is validated (the closed table's
         * optional-read rule); the CONTEXTUAL_TABLE_READ boundary child
         * validates the pre-mapped result.
         */
        private void emitOptionalRead(SemanticOp op) {
            KindPayload.OptionalReadPayload payload =
                (KindPayload.OptionalReadPayload) op.payload();
            if (payload.value() == null) {
                emitStart(op);
            } else {
                // Custom START: the raw operand atom renders the actual
                // value kind (a wrong-kind present value atomizes as its
                // own kind, exactly the oracle's publish).
                out.append("__ev(").append(luaString(opKey(op.opId())))
                    .append(", \"START\", ").append(luaString(op.kind().name()))
                    .append(", ").append(luaString(op.contract().canonicalDigest()))
                    .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                    .append(", {__rawAtom(")
                    .append(luaString("nullable:" + staticKind(payload.descriptor())))
                    .append(", ").append(slot(payload.value()))
                    .append(")}, nil, nil)\n");
            }
            String target = slot((ValueId) op.result());
            if (payload.value() == null) {
                out.append(target).append(" = nil\n");
            } else {
                String source = slot(payload.value());
                out.append("if ").append(source).append(" == __MISSING then\n");
                out.append("  ").append(target).append(" = nil\n");
                out.append("else\n");
                out.append("  ").append(target).append(" = ").append(source).append("\n");
                out.append("end\n");
            }
            SemanticOp boundary = boundaryChildOf(op);
            if (boundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                // Custom boundary START: the input atom renders the
                // actual value kind (identical for a passing value,
                // actual-kind for a wrong-kind present value).
                out.append("__ev(").append(luaString(opKey(boundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(boundary.origin().parentOpId())))
                    .append(", {__rawAtom(")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(")}, nil, nil)\n");
                // The present branch is validated per the closed table's
                // optional-read rule; the boundary failure publishes the
                // boundary FAILURE and the op FAILURE events with the
                // boundary origin (a wrong present kind fails the
                // differential verdict even with coincidental output).
                // A composite contextual position (ISSUE-0651) — the
                // function and array carriers — passes through: the
                // consuming declared cell carries the pinned E8010
                // projection at its own origin (the corpus pins the
                // call-origin failure for a wrong-kind argument whose
                // contextual read sits on the argument expression),
                // exactly the oracle's identical deferral. Every other
                // descriptor keeps the strict row.
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    out.append("__okB, __chkB = true, ").append(target)
                        .append("\n");
                } else {
                    out.append("__okB, __chkB = pcall(__bcheck, ")
                        .append(luaString(descriptorText(boundaryPayload.descriptor())))
                        .append(", ")
                        .append(luaString(staticKind(boundaryPayload.descriptor())))
                        .append(", ").append(target).append(")\n");
                }
                out.append("if not __okB then\n");
                out.append("  __chkB.o = ").append(luaString(originOf(boundary)))
                    .append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                out.append(target).append(" = __chkB\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    emitBoundarySuccessAtom(boundary, "__rawArgAtom("
                        + luaString(staticKind(boundaryPayload.descriptor()))
                        + ", " + target + ")");
                    // The op's own result SUCCESS renders the value-aware
                    // atom too (the oracle's publish atomizes the value).
                    emitResultSuccessAtom(op, target);
                } else {
                    emitBoundarySuccess(boundary, target,
                        boundaryPayload.descriptor());
                    emitResultSuccess(op, target,
                        (RuntimeDescriptor) op.resultType());
                }
            } else {
                emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
            }
        }

        /** Whether one boundary descriptor is a function type (nullable unwrapped). */
        private boolean isFunctionDescriptor(RuntimeDescriptor descriptor) {
            RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                ? nullable.inner() : descriptor;
            return inner instanceof RuntimeDescriptor.Func;
        }

        /** Whether one boundary descriptor is an array type (nullable unwrapped). */
        private boolean isArrayDescriptor(RuntimeDescriptor descriptor) {
            RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                ? nullable.inner() : descriptor;
            return inner instanceof RuntimeDescriptor.Array;
        }

        /**
         * Whether one boundary descriptor is a composite value type whose
         * contextual read defers its shape check to the consuming declared
         * cell (ISSUE-0651: the function and array carriers).
         */
        private boolean defersContextualCheck(RuntimeDescriptor descriptor) {
            return isFunctionDescriptor(descriptor) || isArrayDescriptor(descriptor);
        }

        /**
         * HAS_FIELD: the presence boolean over one checked receiver key —
         * the member-read helper's present/absent split (present null
         * included is present; the class-instance half reads the
         * presence map of the E5 instances).
         */
        private void emitHasField(SemanticOp op) {
            KindPayload.HasFieldPayload payload =
                (KindPayload.HasFieldPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            if (isHostClassReceiver(op)) {
                // A declared host class instance (ISSUE-0624; K10): the
                // deployed construction carrier stores the declared fields
                // directly (an absent optional field is absent, a present
                // null is the deployed runtime's sentinel), so presence is
                // exactly the retained host representation's rule.
                out.append(target).append(" = (")
                    .append(slot(payload.receiver())).append("[")
                    .append(luaString(payload.key())).append("] ~= nil)\n");
                emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
                return;
            }
            out.append(target).append(" = (__member(").append(slot(payload.receiver()))
                .append(", ").append(luaString(payload.key())).append(") ~= __MISSING)\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * Whether one op's receiver operand is a declared host class
         * (ISSUE-0624; K10): the {@code HAS_FIELD} payload names no class
         * id, so the receiver's producing op (or, for an operand-carrying
         * op, its first operand type) resolves the checked descriptor — a
         * class-typed receiver whose identity is a declared host class of
         * the compile's declaration surface. A nullable wrap (an optional
         * class field read) is unwrapped first.
         */
        private boolean isHostClassReceiver(SemanticOp op) {
            RuntimeDescriptor descriptor = null;
            if (!op.operandTypes().isEmpty()) {
                descriptor = op.operandTypes().get(0);
            } else if (op.payload() instanceof KindPayload.HasFieldPayload payload) {
                for (SemanticOp producer : opsById.values()) {
                    if (payload.receiver().equals(producer.result())
                            && producer.resultType() instanceof RuntimeDescriptor
                                produced) {
                        descriptor = produced;
                        break;
                    }
                }
            }
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                descriptor = nullable.inner();
            }
            return descriptor instanceof RuntimeDescriptor.Class classDescriptor
                && isHostClass(classDescriptor.classId());
        }

        // =====================================================================
        // The class field ops (CLASSES step 8, E5): FIELD_READ is
        // presence-aware (missing → the OPTIONAL_FIELD_READ boundary's
        // pre-mapped language null; present null stays distinguishable
        // through the instance's presence map); FIELD_WRITE/FIELD_DELETE
        // are commit ops consuming the ASSIGN/DELETE chain's resolved
        // receiver and stored value — exactly one mutation, never a
        // re-evaluated source expression.
        // =====================================================================

        /**
         * FIELD_READ (K-D6): the nominal receiver boundary
         * ({@code UNTYPED_CLASS_INPUT}) runs first — a null receiver or a
         * foreign class identity fails its canonical E8001 projection —
         * then the presence-aware read (a missing field pre-maps to
         * language null; present null is the {@code __NULL} sentinel
         * converted to nil, never conflated with missing) goes through
         * the {@code OPTIONAL_FIELD_READ} boundary; SUCCESS publishes the
         * boundary-checked value.
         */
        private void emitFieldRead(SemanticOp op) {
            KindPayload.FieldReadPayload payload =
                (KindPayload.FieldReadPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            SemanticOp receiverBoundary =
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT);
            emitFieldBoundaryCheck(op, receiverBoundary, slot(payload.classValue()));
            out.append("__instT = __chkB\n");
            if (ClassId.ERROR.equals(payload.classId())) {
                // The builtin Error carrier (ISSUE-0619; K13 item 6): both
                // declared fields are always present, and the carrier names
                // them {@code code} and {@code m} — the read maps the
                // declared field to the carrier's own field.
                out.append("__rvT = __instT.")
                    .append(errorCarrierField(op, payload.field())).append("\n");
            } else if (isHostClass(payload.classId())) {
                // A declared host class instance (ISSUE-0624; K10): the
                // deployed construction carrier stores the declared fields
                // directly, so the presence-aware read is the field itself
                // (an absent optional field is nil) with the present-null
                // sentinel pre-mapped to the language null, exactly like the
                // in-project carrier's presence-map read.
                out.append("__rvT = __instT[").append(luaString(payload.field()))
                    .append("]\n");
                out.append("if __rvT == __NULL or __rvT == __rt.__NULL then "
                    + "__rvT = nil end\n");
            } else {
                // The presence-aware read: missing → nil before the boundary;
                // present (present null included) → the stored value.
                out.append("__rvT = nil\n");
                out.append("if __instT.__p[").append(luaString(payload.field()))
                    .append("] then\n");
                out.append("  __rvT = __instT.__f[").append(luaString(payload.field()))
                    .append("]\n");
                out.append("  if __rvT == __NULL then __rvT = nil end\n");
                out.append("end\n");
            }
            SemanticOp fieldBoundary =
                boundaryChildOfKind(op, BoundaryKind.OPTIONAL_FIELD_READ);
            emitFieldBoundaryCheck(op, fieldBoundary, "__rvT");
            out.append(target).append(" = __chkB\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * FIELD_WRITE (K-D6, the ASSIGN chain's commit child): the
         * receiver boundary runs over the resolved receiver slot, then the
         * field boundary ({@code CLASS_FIELD_ASSIGNMENT}) over the
         * resolved stored value — the store commits only after both pass
         * (a failed boundary commits nothing), and the published instance
         * carries the boundary-published value in the named field with
         * every other presence state unchanged.
         */
        private void emitFieldWrite(SemanticOp op) {
            KindPayload.FieldWritePayload payload =
                (KindPayload.FieldWritePayload) op.payload();
            emitStart(op);
            SemanticOp receiverBoundary =
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT);
            emitFieldBoundaryCheck(op, receiverBoundary, slot(payload.classValue()));
            out.append("__instT = __chkB\n");
            SemanticOp fieldBoundary =
                boundaryChildOfKind(op, BoundaryKind.CLASS_FIELD_ASSIGNMENT);
            emitFieldBoundaryCheck(op, fieldBoundary, slot(payload.value()));
            if (ClassId.ERROR.equals(payload.classId())) {
                // The builtin Error field write commits into the carrier's
                // own field (K13 item 6): the field boundary already ran the
                // declared string descriptor, so the committed value is the
                // written string.
                out.append("__instT.")
                    .append(errorCarrierField(op, payload.field()))
                    .append(" = __chkB\n");
            } else if (isHostClass(payload.classId())) {
                // A declared host class field write (ISSUE-0624; K10): the
                // commit stores the boundary-published value into the
                // deployed construction carrier's own field, the language
                // null as the deployed runtime's sentinel (the retained host
                // representation's present-null convention).
                out.append("__instT[").append(luaString(payload.field()))
                    .append("] = (__chkB == nil) and __rt.__NULL or __chkB\n");
            } else {
                out.append("__instT.__f[").append(luaString(payload.field()))
                    .append("] = (__chkB == nil) and __NULL or __chkB\n");
                out.append("__instT.__p[").append(luaString(payload.field()))
                    .append("] = true\n");
            }
            emitPlainSuccess(op);
        }

        /**
         * FIELD_DELETE (K-D6, the DELETE chain's commit child): the
         * receiver boundary runs over the resolved receiver slot, then
         * the named field's presence and value are cleared — deleting an
         * already-missing field is a no-op SUCCESS, and every other field
         * state is unchanged.
         */
        private void emitFieldDelete(SemanticOp op) {
            KindPayload.FieldDeletePayload payload =
                (KindPayload.FieldDeletePayload) op.payload();
            emitStart(op);
            if (ClassId.ERROR.equals(payload.classId())) {
                // A builtin Error field delete never reaches the IR: every
                // builtin Error field is required-present, and the checker
                // rejects {@code delete e.f} with E4004 — the arm stays a
                // fail-closed producer defect (K13 item 8).
                throw new IllegalStateException("FIELD_DELETE " + op.opId()
                    + " targets the builtin Error field '" + payload.field()
                    + "': every builtin Error field is required-present and the"
                    + " checker rejects the delete with E4004 — a fail-closed"
                    + " producer defect, never emitted");
            }
            SemanticOp receiverBoundary =
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT);
            emitFieldBoundaryCheck(op, receiverBoundary, slot(payload.classValue()));
            if (isHostClass(payload.classId())) {
                // A declared host class field delete (ISSUE-0624; K10): the
                // deployed construction carrier clears the direct field —
                // deleting an already-absent field is a no-op SUCCESS.
                out.append("__chkB[").append(luaString(payload.field()))
                    .append("] = nil\n");
                emitPlainSuccess(op);
                return;
            }
            out.append("__chkB.__p[").append(luaString(payload.field()))
                .append("] = nil\n");
            out.append("__chkB.__f[").append(luaString(payload.field()))
                .append("] = nil\n");
            emitPlainSuccess(op);
        }

        /**
         * The builtin Error carrier's field name for one declared field
         * (K13 item 6): {@code code} maps to the carrier's {@code code}
         * slot and {@code message} to its {@code m} slot; any other name is
         * a fail-closed producer defect (the declared field set is exactly
         * those two).
         */
        private static String errorCarrierField(SemanticOp op, String field) {
            return switch (field) {
                case "code" -> "code";
                case "message" -> "m";
                default -> throw new IllegalStateException(op.kind() + " " + op.opId()
                    + " names the builtin Error field '" + field + "': the builtin"
                    + " class declares exactly code and message — a fail-closed"
                    + " producer defect, never emitted");
            };
        }

        /**
         * The pinned boundary child of one field op (K-D12): the child
         * parented to the field op with the closed boundary kind. A
         * missing child is a producer defect, fail closed before any
         * emission.
         */
        private SemanticOp boundaryChildOfKind(SemanticOp op, BoundaryKind kind) {
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
         * One field-op boundary child: the START carries the input's
         * actual runtime atom (the raw atom — a null receiver renders
         * "null", never a heap index), the check runs, and the terminal
         * is the boundary SUCCESS with its published value or the two
         * FAILURE events (boundary then owner) with the boundary's own
         * origin.
         */
        private void emitFieldBoundaryCheck(SemanticOp owner, SemanticOp boundary,
                                            String inputExpr) {
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) boundary.payload();
            out.append("__ev(").append(luaString(opKey(boundary.opId())))
                .append(", \"START\", \"BOUNDARY\", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId())))
                .append(", {__rawAtom(")
                .append(luaString(staticKind(payload.descriptor()))).append(", ")
                .append(inputExpr).append(")}, nil, nil)\n");
            out.append("__okB, __chkB = pcall(__bcheck, ")
                .append(luaString(descriptorText(payload.descriptor()))).append(", ")
                .append(luaString(staticKind(payload.descriptor()))).append(", ")
                .append(inputExpr).append(")\n");
            out.append("if not __okB then\n");
            out.append("  __chkB.o = ").append(luaString(originOf(boundary)))
                .append("\n");
            emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                "__errtext(__chkB)");
            emitFailureEvent(owner.opId(), owner.kind().name(), owner,
                "__errtext(__chkB)");
            out.append("  error(__chkB, 0)\n");
            out.append("end\n");
            emitBoundarySuccess(boundary, "__chkB", payload.descriptor());
        }

        private void emitMemberWrite(SemanticOp op) {
            KindPayload.MemberWritePayload payload =
                (KindPayload.MemberWritePayload) op.payload();
            emitStart(op);
            out.append(slot(payload.table())).append("[")
                .append(luaString(payload.key())).append("] = ")
                .append(slot(payload.value())).append("\n");
            out.append("__orderAdd(").append(slot(payload.table())).append(", ")
                .append(luaString(payload.key())).append(")\n");
            out.append("__numKey(").append(slot(payload.table())).append(", ")
                .append(luaString(payload.key())).append(", ")
                .append(slot(payload.value())).append(", ")
                .append(isNumberKind(producerKind(payload.value())) ? "true" : "false")
                .append(")\n");
            emitPlainSuccess(op);
        }

        private void emitMemberDelete(SemanticOp op) {
            KindPayload.MemberDeletePayload payload =
                (KindPayload.MemberDeletePayload) op.payload();
            emitStart(op);
            out.append(slot(payload.table())).append("[")
                .append(luaString(payload.key())).append("] = nil\n");
            out.append("__orderRemove(").append(slot(payload.table())).append(", ")
                .append(luaString(payload.key())).append(")\n");
            emitPlainSuccess(op);
        }

        private void emitNormalize(SemanticOp op) {
            KindPayload.IndexNormalizePayload payload =
                (KindPayload.IndexNormalizePayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            switch (payload.mode()) {
                case ARRAY_READ, ARRAY_WRITE -> {
                    boolean write = payload.mode() == deal.semantic.ir.IndexMode.ARRAY_WRITE;
                    // The normalized index/length are numeric views: a
                    // runtime number carrier (the value model's variant
                    // representation) unwraps, a plain number passes
                    // through.
                    out.append(target).append(" = {slot = \"a\", i = __num(")
                        .append(slot(payload.rawKey())).append("), n = __num(")
                        .append(slot(payload.currentLength())).append("), a = ")
                        .append(write).append("}\n");
                }
                case TABLE_READ, TABLE_WRITE ->
                    out.append(target).append(" = {slot = \"t\", k = __num(")
                        .append(slot(payload.rawKey())).append(")}\n");
            }
            out.append("__normalizeEvent(")
                .append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(target).append(")\n");
        }

        private void emitIndexRead(SemanticOp op) {
            KindPayload.IndexReadPayload payload = (KindPayload.IndexReadPayload) op.payload();
            SemanticOp boundary = opsById.get(payload.elementBoundaryOpId());
            RuntimeDescriptor descriptor =
                ((KindPayload.BoundaryPayload) boundary.payload()).descriptor();
            boolean nullable = descriptor instanceof RuntimeDescriptor.Nullable;
            RuntimeDescriptor inner = nullable
                ? ((RuntimeDescriptor.Nullable) descriptor).inner() : descriptor;
            emitSlotOperandStart(op);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = __arrayRead(")
                .append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(opKey(boundary.opId()))).append(", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId()))).append(", ")
                .append(luaString(descriptorText(descriptor))).append(", ")
                .append(luaString(descriptorText(inner))).append(", ")
                .append(slot(payload.container())).append(", ")
                .append(slot(payload.slot())).append(", ")
                .append(nullable ? "true" : "false").append(", ")
                .append(isNumberKind(staticKind(inner)) ? "true" : "false")
                .append(", ")
                .append(luaString(originOf(op))).append(")\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        private void emitIndexWrite(SemanticOp op) {
            KindPayload.IndexWritePayload payload =
                (KindPayload.IndexWritePayload) op.payload();
            emitStart(op);
            String container = slot(payload.container());
            String slotName = slot(payload.slot());
            String value = slot(payload.value());
            String numberWriteFlag = isNumberKind(producerKind(payload.value()))
                ? "true" : "false";
            out.append("if ").append(slotName).append(".slot == \"a\" then\n");
            out.append("  if ").append(slotName).append(".i == ").append(slotName)
                .append(".n then\n");
            out.append("    ").append(container).append(".__n = ").append(container)
                .append(".__n + 1\n");
            out.append("  end\n");
            out.append("  ").append(container).append("[").append(slotName)
                .append(".i + 1] = ").append(value)
                .append(" == nil and __NULL or ").append(value).append("\n");
            out.append("  __numKey(").append(container).append(", ").append(slotName)
                .append(".i + 1, ").append(value).append(", ").append(numberWriteFlag)
                .append(")\n");
            out.append("else\n");
            out.append("  ").append(container).append("[").append(slotName)
                .append(".k] = ").append(value).append("\n");
            out.append("  __orderAdd(").append(container).append(", ").append(slotName)
                .append(".k)\n");
            out.append("  __numKey(").append(container).append(", ").append(slotName)
                .append(".k, ").append(value).append(", ").append(numberWriteFlag)
                .append(")\n");
            out.append("end\n");
            emitPlainSuccess(op);
        }

        private void emitIndexDelete(SemanticOp op) {
            KindPayload.IndexDeletePayload payload =
                (KindPayload.IndexDeletePayload) op.payload();
            emitStart(op);
            String container = slot(payload.container());
            String slotName = slot(payload.slot());
            out.append("if ").append(slotName).append(".slot == \"a\" then\n");
            out.append("  if ").append(slotName).append(".i < ").append(container)
                .append(".__n then\n");
            out.append("    ").append(container).append("[").append(slotName)
                .append(".i + 1] = nil\n");
            out.append("  end\n");
            out.append("else\n");
            out.append("  ").append(container).append("[").append(slotName)
                .append(".k] = nil\n");
            out.append("  __orderRemove(").append(container).append(", ")
                .append(slotName).append(".k)\n");
            out.append("end\n");
            emitPlainSuccess(op);
        }

        /**
         * A free BOUNDARY op: the prelude check over the payload input,
         * run under the boundary's own origin with the boundary's own
         * single FAILURE terminal — the parented arms' contract (no owner
         * terminal exists for an unparented boundary); the success
         * terminal is unchanged.
         */
        private void emitFreeBoundary(SemanticOp op) {
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"START\", \"BOUNDARY\", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, nil, nil)\n");
            out.append("__okB, __chk = pcall(__bcheck, ")
                .append(bcheckArgs(payload.descriptor(), slot(payload.input())))
                .append(")\n");
            out.append("if not __okB then\n");
            out.append("  __chk.o = ").append(luaString(originOf(op))).append("\n");
            emitFailureEvent(op.opId(), "BOUNDARY", op, "__errtext(__chk)");
            out.append("  error(__chk, 0)\n");
            out.append("end\n");
            if (op.result() instanceof ValueId valueId) {
                out.append(slot(valueId)).append(" = __chk\n");
                emitBoundarySuccess(op, slot(valueId), payload.descriptor());
            } else {
                emitBoundarySuccess(op, "__chk", payload.descriptor());
            }
        }

        private void emitBindingAlloc(SemanticOp op) {
            KindPayload.BindingAllocPayload payload =
                (KindPayload.BindingAllocPayload) op.payload();
            emitStart(op);
            if (isCatchBinding(payload.binding())) {
                // The catch binding's ALLOC sits at the catch block's entry
                // and its pinned initializing write is the TRY_CATCH arm's
                // catch-entry assignment, which runs before the catch block's
                // ops (the catch binding's cell carries the reified Error
                // value — ISSUE-0619's catch reification). A cell reset here
                // would clobber the caught value.
                emitPlainSuccess(op);
                return;
            }
            switch (payload.cellKind()) {
                case DIRECT -> out.append(cell(payload.binding(), payload.generation())).append(" = nil\n");
                case SHARED_CELL -> out.append(cell(payload.binding(), payload.generation())).append(" = {}\n");
            }
            emitPlainSuccess(op);
        }

        /**
         * True iff the binding is a {@code TRY_CATCH} op's catch binding in
         * the closure: its cell is created and initialized by the
         * {@code TRY_CATCH} arm's catch-entry write, so the catch binding's
         * {@code BINDING_ALLOC} (the catch block's first op) must not reset
         * it.
         */
        private boolean isCatchBinding(BindingId binding) {
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

        private void emitBindingInit(SemanticOp op) {
            KindPayload.BindingInitPayload payload =
                (KindPayload.BindingInitPayload) op.payload();
            emitStart(op);
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            String valueExpr = intrinsicCarrierExpr(payload.value());
            if (valueExpr == null) {
                valueExpr = hasProducer(payload.value())
                    ? slot(payload.value()) : exportPlaceholderCarrier();
            }
            if (kind == BindingCellKind.SHARED_CELL) {
                // In-place publication: the cell table's identity is held
                // by captures and adapters, so the commit writes the cell
                // slot (never a replacement — the oracle's Cell.value
                // mutation).
                out.append(cell(payload.binding(), payload.generation()))
                    .append("[1] = ").append(valueExpr).append("\n");
            } else {
                out.append(cell(payload.binding(), payload.generation()))
                    .append(" = ").append(valueExpr).append("\n");
            }
            emitPlainSuccess(op);
        }

        /** True iff the value slot is an op result in this unit. */
        private boolean hasProducer(ValueId valueId) {
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
         * The memoized intrinsic carrier expression of one value identity
         * (J2): the closed {@code IntrinsicFunction} registration of the
         * closure resolves the kind — never a spelling — and every op
         * result publishing the identity is an identity-preserving
         * {@code BINDING_LOAD} of the seed {@code BINDING_INIT}'s own cell
         * (or nothing publishes it, the seed's producer-less identity), so
         * an identity-preserving load of the seeded binding never replaces
         * the memoized carrier with a slot read. {@code null} when the
         * identity is not a registered intrinsic: every other value keeps
         * the landed {@code hasProducer} behavior (a closure identity has
         * its real creation op).
         */
        private String intrinsicCarrierExpr(ValueId valueId) {
            IntrinsicKind kind = intrinsicKindOf(valueId);
            return kind == null ? null : intrinsicAccessor(kind);
        }

        /**
         * The memoized intrinsic carrier expression of one identity whose
         * registration — the kind's only authority — resolves an intrinsic
         * kind (the residual export-read kind arm's rule), or {@code null}.
         */
        private String registeredIntrinsicCarrierExpr(ValueId valueId) {
            IntrinsicKind kind = registeredIntrinsicKindOf(valueId);
            return kind == null ? null : intrinsicAccessor(kind);
        }

        /** The registered intrinsic kind of one value identity, or null. */
        private IntrinsicKind registeredIntrinsicKindOf(ValueId valueId) {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                FunctionExecutionBinding found = moduleUnit.functionBindings().get(
                    new FunctionAllocationIdentity(valueId.id()));
                if (found instanceof FunctionExecutionBinding.IntrinsicFunction
                        intrinsic) {
                    return intrinsic.kind();
                }
                if (found != null) {
                    return null;
                }
            }
            return null;
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
        private IntrinsicKind intrinsicKindOf(ValueId valueId) {
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
         * True iff one {@code BINDING_INIT} of the cell carries the given
         * identity: the load republishes an identity the cell already
         * holds — the seed init's own write, or an alias declaration's
         * re-publication of it (the identity-preserving-load test).
         */
        private boolean isSeedInitOperand(ValueId identity, BindingId binding,
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

        /**
         * The deterministic placeholder expression of a site whose identity
         * resolves no intrinsic registration (the landed residual arm): a
         * fresh, per-site value carrying the landed opaque export view — the
         * oracle's {@code ()->number} projection — and the real carrier's
         * interface, so the landed function row admits it exactly as the
         * oracle's view does. Never the removed marker: the placeholder is a
         * real carrier surface.
         */
        private static String exportPlaceholderCarrier() {
            return "__intrinsicExport()";
        }

        /**
         * The memoized carrier accessor of one intrinsic kind: the kind
         * tag and the intrinsic's declared descriptor text and canonical
         * spec text — the only descriptor source (never a call site's or
         * an adapter target's).
         */
        private static String intrinsicAccessor(IntrinsicKind kind) {
            RuntimeDescriptor.Func declared = kind.declaredSignature();
            return "__intrinsicFn(" + luaString(kind.name()) + ", "
                + luaString(descriptorText(declared)) + ", "
                + luaString(declared.canonicalSpecText()) + ")";
        }

        private void emitBindingLoad(SemanticOp op) {
            KindPayload.BindingLoadPayload payload =
                (KindPayload.BindingLoadPayload) op.payload();
            emitStart(op);
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            out.append(slot((ValueId) op.result())).append(" = ")
                .append(kind == BindingCellKind.SHARED_CELL
                    ? cell(payload.binding(), payload.generation()) + "[1]" : cell(payload.binding(), payload.generation()))
                .append("\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        private void emitBindingStore(SemanticOp op) {
            KindPayload.BindingStorePayload payload =
                (KindPayload.BindingStorePayload) op.payload();
            emitStart(op);
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            if (kind == BindingCellKind.SHARED_CELL) {
                // In-place publication: captures and adapters hold the
                // cell table by identity (the oracle's Cell.value
                // mutation — never a replacement).
                out.append(cell(payload.binding(), payload.generation()))
                    .append("[1] = ").append(slot(payload.value())).append("\n");
            } else {
                out.append(cell(payload.binding(), payload.generation()))
                    .append(" = ").append(slot(payload.value())).append("\n");
            }
            emitPlainSuccess(op);
        }

        private void emitClosureNew(SemanticOp op) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            StringBuilder args = new StringBuilder();
            for (BindingId captureId : payload.captures()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(cell(captureId, 0));
            }
            out.append(target).append(" = {__fn = ").append(fnFactory(payload.function()))
                .append("(").append(args).append("), __sig = ")
                .append(luaString(descriptorText(payload.signature())))
                .append(", __csig = ")
                .append(luaString(payload.signature().canonicalSpecText()))
                .append(", __fid = ")
                .append(payload.function().id()).append("}\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * FUNCTION_ADAPT (E6, D15 creation): a wrapper function value
         * carrying the closed capture mode — VALUE retains the
         * creation-time source identity; SHARED_CELL records the
         * generation cell re-read per invocation (live reassignment
         * observed); REEVALUATE_THUNK records the detached thunk
         * re-executor. Creation evaluates no thunk and reads no binding
         * (VALUE's single operand already completed); the wrapper's
         * invocation (the {@code __fn} protocol) runs the D15 sequence at
         * every call site with the invoking op's origin.
         */
        private void emitFunctionAdapt(SemanticOp op) {
            KindPayload.FunctionAdaptPayload payload =
                (KindPayload.FunctionAdaptPayload) op.payload();
            // The VALUE operand's carrier expression: for the seeded
            // intrinsic identity no slot holds it before this creation, so
            // the START's operand atom and the wrapper's own field read the
            // one carrier expression (never a nil slot read).
            String valueExpr = payload.source() instanceof AdaptSourceRef.Value value
                ? adaptValueExpr(value) : null;
            emitAdaptStart(op, payload, valueExpr);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = {__mode = ");
            switch (payload.mode()) {
                case VALUE -> out.append("0");
                case SHARED_CELL -> out.append("1");
                case REEVALUATE_THUNK -> out.append("2");
            }
            out.append(", __m = ").append(payload.sourceSignature().paramTypes().size())
                .append(", __csrc = ")
                .append(luaString(payload.sourceSignature().canonicalSpecText()))
                .append(", __sig = ")
                .append(luaString(descriptorText(payload.targetSignature())))
                .append(", __csig = ")
                .append(luaString(payload.targetSignature().canonicalSpecText()))
                .append(", __fid = nil");
            switch (payload.source()) {
                case AdaptSourceRef.Value ignored ->
                    out.append(", __value = ").append(valueExpr);
                case AdaptSourceRef.SharedCell cell ->
                    out.append(", __cell = ")
                        .append(cell(cell.binding(), cell.generation()));
                case AdaptSourceRef.Thunk thunk ->
                    out.append(", __thunk = ").append(thunkFn(op.opId()));
            }
            out.append("}\n");
            out.append(target).append(".__fn = __adaptInvoke\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The carrier expression of one adapter VALUE source: the memoized
         * intrinsic carrier when the identity carries the seeded
         * {@code IntrinsicFunction} registration (J2), the operand's own
         * slot for a produced identity, and the landed placeholder otherwise.
         */
        private String adaptValueExpr(AdaptSourceRef.Value value) {
            String sourceExpr = intrinsicCarrierExpr(value.value());
            if (sourceExpr == null) {
                sourceExpr = hasProducer(value.value())
                    ? slot(value.value()) : exportPlaceholderCarrier();
            }
            return sourceExpr;
        }

        /**
         * The FUNCTION_ADAPT START (E6): the VALUE operand's atom is the
         * operand's own carrier expression ({@code valueExpr}) exactly when
         * the op records that operand (the oracle atomizes its operand list);
         * the SHARED_CELL and REEVALUATE_THUNK modes carry zero operand atoms
         * (their operands are empty by construction).
         */
        private void emitAdaptStart(SemanticOp op,
                KindPayload.FunctionAdaptPayload payload, String valueExpr) {
            out.append("__ev(").append(luaString(opKey(op.opId()))).append(", \"START\", ")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", {");
            if (valueExpr != null && !op.operands().isEmpty()) {
                out.append("__atom(")
                    .append(luaString(staticKind(payload.sourceSignature())))
                    .append(", ").append(valueExpr).append(")");
            }
            out.append("}, nil, nil)\n");
        }

        /**
         * RECURSIVE_GROUP_INIT (E8, atomic publication): phase 1
         * allocates every member's SHARED_CELL (a fresh table per
         * execution); phase 2 allocates every member identity into a
         * temporary — the per-member factory invocation over the member's
         * capture cells (the {@code CLOSURE_NEW} wrapper shape carrying
         * the exact signature); phase 3 publishes the member wrappers to
         * the member cells in declaration order in one ordered sequence.
         * The publication writes into the already-allocated cell tables
         * (never a replacement — a sibling's capture holds the cell
         * table by identity), and no member observes a partially
         * initialized group: no member body runs at group execution and
         * every identity is allocated before the first publication.
         */
        private void emitRecursiveGroupInit(SemanticOp op) {
            KindPayload.RecursiveGroupInitPayload payload =
                (KindPayload.RecursiveGroupInitPayload) op.payload();
            emitStart(op);
            for (BindingId binding : payload.bindings()) {
                out.append(cell(binding, 0)).append(" = {}\n");
            }
            for (int i = 0; i < payload.functions().size(); i++) {
                FunctionId functionId = payload.functions().get(i);
                LoweredFunction function = unit.functions().get(functionId);
                if (function == null) {
                    throw new IllegalStateException("group member " + functionId
                        + " has no LoweredFunction record (producer defect)");
                }
                StringBuilder args = new StringBuilder();
                for (BindingId captureId : function.captures()) {
                    if (args.length() > 0) {
                        args.append(", ");
                    }
                    args.append(cell(captureId, 0));
                }
                out.append(groupTemp(op, i)).append(" = {__fn = ")
                    .append(fnFactory(functionId)).append("(").append(args)
                    .append("), __sig = ")
                    .append(luaString(descriptorText(function.descriptor())))
                    .append(", __csig = ")
                    .append(luaString(function.descriptor().canonicalSpecText()))
                    .append(", __fid = ")
                    .append(functionId.id()).append("}\n");
            }
            for (int i = 0; i < payload.bindings().size(); i++) {
                out.append(cell(payload.bindings().get(i), 0)).append("[1] = ")
                    .append(groupTemp(op, i)).append("\n");
            }
            emitPlainSuccess(op);
        }

        /** One member identity temporary of the group op (S-table held). */
        private String groupTemp(SemanticOp op, int member) {
            return "S.__gv" + op.opId().id() + "_" + member;
        }

        private void emitAssign(SemanticOp op) {
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) op.payload();
            emitStart(op);
            out.append("__okT, __resT = pcall(function()\n");
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opsById.get(childId);
                emitChainOperandProducers(child);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    emitChainBoundary(child, (KindPayload.BoundaryPayload) child.payload(),
                        op);
                } else {
                    emitOp(child);
                }
            }
            out.append("end)\n");
            out.append("if not __okT then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            RuntimeDescriptor committedKind = producerResultType(op.result());
            emitResultSuccess(op, slot((ValueId) op.result()), committedKind);
        }

        /**
         * The static kind of one written value: its producing op's result
         * type (the same producer lookup {@link #producerResultType} uses,
         * ASSIGN/DELETE republishes skipped) — the exact typing rule the
         * oracle and the shared JVM runtime store for the value. Feeds the
         * container's {@code __numKey} mark so the JSON_STRINGIFY walker
         * spells a number-typed slot through the closed decimal spelling.
         */
        private String producerKind(ValueId value) {
            return staticKind(producerResultType(value));
        }

        /** A number-typed static kind (a nullable number included). */
        private static boolean isNumberKind(String kind) {
            return "number".equals(kind) || "nullable:number".equals(kind);
        }

        /** The committed value's static kind: its producing op's result type. */
        private RuntimeDescriptor producerResultType(deal.semantic.ir.SemanticValue value) {
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

        private void emitDelete(SemanticOp op) {
            KindPayload.DeletePayload payload = (KindPayload.DeletePayload) op.payload();
            emitStart(op);
            out.append("__okT, __resT = pcall(function()\n");
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opsById.get(childId);
                emitChainOperandProducers(child);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    emitChainBoundary(child, (KindPayload.BoundaryPayload) child.payload(),
                        op);
                } else {
                    emitOp(child);
                }
            }
            out.append("end)\n");
            out.append("if not __okT then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            emitPlainSuccess(op);
        }

        /**
         * A-D2 ("each child's operands complete before that child's
         * START"): the child's transitive operand-producing closure is
         * emitted at the child's position inside the chain — the
         * receiver/key/RHS operand effects interleave with the children
         * exactly as the hoisted-operand parity fixtures pin (an
         * operand's nested side-effecting argument completes before the
         * operand call's own effect, and the RHS operand effects run
         * only after the key child completed). The block walk skips
         * these ops (they are registered in the chain-owned set), so
         * each is emitted exactly once, here.
         */
        private void emitChainOperandProducers(SemanticOp child) {
            for (SemanticOp producer : ChainOperandCompletion.operandProducersOf(
                    child, unit, structuralOwned)) {
                emitOp(producer);
            }
        }

        /** A chain boundary child (bounds check only from its projection, A-D8). */
        private void emitChainBoundary(SemanticOp boundary,
                                       KindPayload.BoundaryPayload payload,
                                       SemanticOp chain) {
            String input = slot(payload.input());
            switch (payload.kind()) {
                case ARRAY_ELEMENT_ASSIGNMENT, ARRAY_ELEMENT_DELETE -> {
                    // __arrayBounds emits the boundary START/terminal events
                    // (the bounds check runs only from this projection); the
                    // delete boundary's input operand is the normalized slot.
                    if (payload.kind() == BoundaryKind.ARRAY_ELEMENT_DELETE
                            && slotEqualsChainSlot(payload.input(), chain)) {
                        out.append("__arrayBoundsSlot(")
                            .append(luaString(opKey(boundary.opId()))).append(", ")
                            .append(luaString(boundary.contract().canonicalDigest()))
                            .append(", ")
                            .append(luaString(parentKey(boundary.origin().parentOpId())))
                            .append(", ").append(chainSlotExpr(chain)).append(", ")
                            .append(chainLengthExpr(chain)).append(", ")
                            .append(payload.kind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                                ? "true" : "false").append(", ")
                            .append(luaString(originOf(boundary))).append(")\n");
                    } else {
                    out.append("__arrayBounds(")
                        .append(luaString(opKey(boundary.opId()))).append(", ")
                        .append(luaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(luaString(parentKey(boundary.origin().parentOpId())))
                        .append(", ").append(input).append(", ")
                        .append(chainSlotExpr(chain)).append(", ")
                        .append(chainLengthExpr(chain)).append(", ")
                        .append(luaString(descriptorText(payload.descriptor()))).append(", ")
                        .append(luaString(staticKind(payload.descriptor()))).append(", ")
                        .append(payload.kind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                            ? "true" : "false").append(", ")
                        .append(luaString(originOf(boundary))).append(")\n");
                    }
                }
                default -> {
                    emitBoundaryStart(boundary, input, payload.descriptor());
                    out.append("__chk = ")
                        .append(bcheckExpr(payload.descriptor(), input)).append("\n");
                    emitBoundarySuccess(boundary, "__chk", payload.descriptor());
                }
            }
        }

        /** True iff the boundary input value is the chain's normalize slot. */
        private boolean slotEqualsChainSlot(ValueId input, SemanticOp chain) {
            for (OpId childId : chainChildOps(chain)) {
                SemanticOp child = opsById.get(childId);
                if (child.kind() == SemanticOpKind.INDEX_NORMALIZE
                        && input.equals(child.result())) {
                    return true;
                }
            }
            return false;
        }

        /** The chain's normalize-slot local (found among its children). */
        private String chainSlotExpr(SemanticOp chain) {
            for (OpId childId : chainChildOps(chain)) {
                SemanticOp child = opsById.get(childId);
                if (child.kind() == SemanticOpKind.INDEX_NORMALIZE
                        && child.result() instanceof ValueId valueId) {
                    return slot(valueId);
                }
            }
            return "nil";
        }

        private String chainLengthExpr(SemanticOp chain) {
            for (OpId childId : chainChildOps(chain)) {
                SemanticOp child = opsById.get(childId);
                if (child.kind() == SemanticOpKind.ARRAY_LENGTH
                        && child.result() instanceof ValueId valueId) {
                    return slot(valueId);
                }
            }
            return "nil";
        }

        private List<OpId> chainChildOps(SemanticOp chain) {
            return switch (chain.payload()) {
                case KindPayload.AssignPayload assign -> assign.childOps();
                case KindPayload.DeletePayload delete -> delete.childOps();
                default -> List.of();
            };
        }

        /** The single BOUNDARY child parented to the given op, or null. */
        private SemanticOp boundaryChildOf(SemanticOp op) {
            for (SemanticOp candidate : opsById.values()) {
                if (candidate.kind() == SemanticOpKind.BOUNDARY
                        && op.opId().equals(candidate.origin().parentOpId())) {
                    return candidate;
                }
            }
            return null;
        }

        private void emitCall(SemanticOp op) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
            // A Dynamic callee resolves its execution class at execution
            // (ISSUE-0658; {@link #emitDynamicCall}) and has no
            // emission-time binding; every other callee resolves its
            // static binding here.
            FunctionExecutionBinding binding = payload.callee()
                    instanceof KindPayload.CallCallee.Dynamic
                ? null : callBinding(payload);
            emitStart(op);
            // The host arms (ISSUE-0651; host-module-load-and-host-call-
            // realization H3/H7 and the sync host call contract): the
            // loaded surface entry is invoked through the landed wrapper's
            // own `.f` calling convention with the trailing literal span
            // triplet, the declared parameter cells run at the call site
            // with the pinned E8010 projections, and every crossed value is
            // projected through the host-facing carrier set.
            if (binding instanceof FunctionExecutionBinding.HostFunction host) {
                emitHostCall(op, payload, host.hostModuleId(), host.exportName(),
                    true);
                return;
            }
            if (binding instanceof FunctionExecutionBinding.HostFunctionValue hostValue) {
                emitHostValueCall(op, payload, hostValue);
                return;
            }
            // The conversion intrinsic's value call (ISSUE-0679; design
            // source {@code conversion-intrinsic-function-values} J3/J4): the
            // seeded identity's registration is a boundary-shaped callable, so
            // the indirect arm runs the recorded host cell family and the one
            // conversion ladder at the call site with the invoking CALL op's
            // own context and kind.
            if (binding instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic) {
                emitIntrinsicValueCall(op, payload, intrinsic);
                return;
            }
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                emitBoundaryStart(boundary, slot(boundaryPayload.input()),
                    boundaryPayload.descriptor());
                out.append("__chk = ")
                    .append(bcheckExpr(boundaryPayload.descriptor(),
                        slot(boundaryPayload.input())))
                    .append("\n");
                emitBoundarySuccess(boundary, "__chk", boundaryPayload.descriptor());
            }
            if (payload.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                // The dynamic dispatch (ISSUE-0658): the recorded parameter
                // cells above are the class-independent family; the
                // carrier's own class tag selects the path.
                emitDynamicCall(op, payload, dynamic);
                String dynamicResult = slot((ValueId) op.result());
                out.append(dynamicResult).append(" = __resT\n");
                emitResultSuccess(op, dynamicResult,
                    (RuntimeDescriptor) op.resultType());
                return;
            }
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionId callee = body.functionId();
                    String savedState = emitInvocationStateSave(callee, op.opId());
                    out.append("table.insert(__frames, 1, ")
                        .append(luaString(String.valueOf(callee.id()))).append(")\n");
                    out.append("__okT, __resT = pcall(").append(fnFactory(callee))
                        .append("(");
                    LoweredFunction calleeFunction = unit.functions().get(callee);
                    List<BindingId> captures = calleeFunction == null
                        ? List.of() : calleeFunction.captures();
                    for (int i = 0; i < captures.size(); i++) {
                        if (i > 0) {
                            out.append(", ");
                        }
                        out.append(cell(captures.get(i), 0));
                    }
                    out.append(")");
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        out.append(", ");
                        SemanticOp boundary =
                            opsById.get(payload.parameterBoundaryOpIds().get(i));
                        out.append(slot(((KindPayload.BoundaryPayload) boundary.payload())
                            .input()));
                    }
                    out.append(")\n");
                    out.append("table.remove(__frames, 1)\n");
                    emitInvocationStateRestore(callee, savedState);
                    out.append("if not __okT then\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "__errtext(__resT)");
                    out.append("  error(__resT, 0)\n");
                    out.append("end\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    // The D15 invocation protocol: resolve the source per
                    // the recorded capture mode, the source-signature
                    // check (E8010 at this CALL's origin), then the
                    // source invocation with the leading M arguments
                    // only — every N target-signature parameter boundary
                    // already ran above. The adapter protocol pushes the
                    // source body's frame itself; the identical
                    // completion error propagates unchanged. An adapter
                    // whose recorded source is the seeded intrinsic
                    // identity runs the same order at this call site with
                    // the conversion ladder as its source invocation
                    // (ISSUE-0680; design source
                    // {@code conversion-intrinsic-function-values} J5).
                    if (adapterIntrinsicKind(adapter) != null) {
                        emitAdapterOverIntrinsicRun(op, payload, adapter);
                        break;
                    }
                    String adapterSlot =
                        slot((ValueId) opsById.get(adapter.adaptOpId()).result());
                    StringBuilder args = new StringBuilder();
                    for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                        if (args.length() > 0) {
                            args.append(", ");
                        }
                        SemanticOp boundary = opsById.get(boundaryId);
                        args.append(slot(((KindPayload.BoundaryPayload) boundary.payload())
                            .input()));
                    }
                    out.append("__okT, __resT = pcall(").append(adapterSlot)
                        .append(".__fn, ").append(adapterSlot).append(", ")
                        .append(luaString(originOf(op)));
                    if (args.length() > 0) {
                        out.append(", ").append(args);
                    }
                    out.append(")\n");
                    out.append("if not __okT then\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "__errtext(__resT)");
                    out.append("  error(__resT, 0)\n");
                    out.append("end\n");
                }
                case FunctionExecutionBinding.ExternalFunction external ->
                    emitExternalCall(op, payload, external);
                default -> throw new IllegalStateException("CALL " + op.opId()
                    + " resolves a binding outside the statically-resolved slice: "
                    + binding);
            }
            out.append(slot((ValueId) op.result())).append(" = __resT\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        /**
         * The {@code ExternalFunction(SHARED_BODY)} CALL arm (ISSUE-0654;
         * {@code cross-module-call-realization} X1/X4/X5 and the
         * cross-module sync call contract): the callee unit's recorded
         * {@code EXTERNAL_ENTRY} runs inside the one artifact under the
         * callee module's context, with the entry's trace events parented
         * to the caller's {@code CALL} op, and the callee body's
         * {@code RETURN} runs the callee's single {@code EXTERNAL_RETURN}
         * boundary. The caller publishes the returned value without
         * re-checking (its own {@code EXTERNAL_PARAMETER} cells ran
         * exactly once above); the module context is restored on success
         * and on failure.
         */
        private void emitExternalCall(SemanticOp op, KindPayload.CallPayload payload,
                                      FunctionExecutionBinding.ExternalFunction external) {
            if (external.executionOwner()
                    != deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " resolves the external binding " + external.moduleId() + "."
                    + external.exportName() + " with execution owner "
                    + external.executionOwner() + " (a RETAINED_ABI external has no"
                    + " production emission arm — producer defect)");
            }
            LoweredModuleUnit calleeUnit = units.get(external.moduleId());
            if (calleeUnit == null) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " resolves the external callee module " + external.moduleId()
                    + " outside the session's closure (producer defect)");
            }
            SemanticOp entry = resolveExternalEntry(op, payload, external, calleeUnit);
            KindPayload.ExternalEntryPayload entryPayload =
                (KindPayload.ExternalEntryPayload) entry.payload();
            LoweredFunction calleeFunction =
                calleeUnit.functions().get(entryPayload.function());
            if (calleeFunction == null) {
                throw new IllegalStateException("EXTERNAL_ENTRY " + entry.opId()
                    + " resolves the missing lowered function "
                    + entryPayload.function().id() + " (producer defect)");
            }
            String calleePath = calleeUnit.moduleId().path();
            emitModulePush();
            out.append("__module = ").append(luaString(calleePath)).append("\n");
            if (trace) {
                // The entry record's START parented to the triggering
                // caller CALL (the oracle's emitStartParented): no inputs
                // (the entry runs no parameter boundaries).
                out.append("__ev(").append(luaString(opKey(entry.opId())))
                    .append(", \"START\", \"EXTERNAL_ENTRY\", ")
                    .append(luaString(entry.contract().canonicalDigest()))
                    .append(", ").append(luaString(opKey(op.opId())))
                    .append(", {}, nil, nil)\n");
            }
            String savedState = emitInvocationStateSave(entryPayload.function(),
                op.opId());
            out.append("table.insert(__frames, 1, ")
                .append(luaString(String.valueOf(entryPayload.function().id())))
                .append(")\n");
            out.append("__okT, __resT = pcall(")
                .append(fnFactory(entryPayload.function())).append("(");
            List<BindingId> captures = calleeFunction.captures();
            for (int i = 0; i < captures.size(); i++) {
                if (i > 0) {
                    out.append(", ");
                }
                out.append(cell(captures.get(i), 0));
            }
            out.append(")");
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                out.append(", ").append(slot(
                    ((KindPayload.BoundaryPayload) boundary.payload()).input()));
            }
            out.append(")\n");
            out.append("table.remove(__frames, 1)\n");
            emitInvocationStateRestore(entryPayload.function(), savedState);
            out.append("if not __okT then\n");
            if (trace) {
                // The entry record's FAILURE under the callee module,
                // parented to the caller CALL (the oracle's
                // emitFailureParented).
                out.append("  __ev(").append(luaString(opKey(entry.opId())))
                    .append(", \"FAILURE\", \"EXTERNAL_ENTRY\", ")
                    .append(luaString(entry.contract().canonicalDigest()))
                    .append(", ").append(luaString(opKey(op.opId())))
                    .append(", {}, nil, __errtext(__resT))\n");
            }
            // Restore the caller's module before the caller's own
            // terminal: the entry events above carry the callee's module,
            // the caller's CALL FAILURE carries the caller's (the oracle's
            // own tagging).
            emitModulePop();
            if (trace) {
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__resT)");
            }
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            if (trace) {
                out.append("__ev(").append(luaString(opKey(entry.opId())))
                    .append(", \"SUCCESS\", \"EXTERNAL_ENTRY\", ")
                    .append(luaString(entry.contract().canonicalDigest()))
                    .append(", ").append(luaString(opKey(op.opId())))
                    .append(", {}, __atom(")
                    .append(luaString(staticKind(entryPayload.signature().returnType())))
                    .append(", __resT), nil)\n");
            }
            emitModulePop();
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
         * <p>The session carries one {@code S} table for every slot and
         * cell (the control-flow emission cannot bind them to Lua locals
         * — a {@code goto} never enters a local's scope), so a nested
         * invocation of the same body would otherwise overwrite the
         * enclosing invocation's own state: a recursive body (the
         * {@code modules/imported-recursive-export} shape) would re-read
         * its parameter cell and its half-computed slots after the nested
         * call returned. The invoking arm therefore saves the callee
         * body's private state before the invocation and restores it on
         * every path — the per-invocation semantics the semantic oracle
         * models with its cell overlays.</p>
         */
        private List<String> bodyStateKeys(FunctionId functionId) {
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

        private void collectBodyStateKeys(BlockId block, java.util.Set<String> keys,
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
                        for (BindingId binding : payload.captures()) {
                            addCellStateKey(keys, binding, 0);
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

        /** A body-private cell key: {@code DIRECT} cells only (shared state stays shared). */
        private void addCellStateKey(java.util.Set<String> keys, BindingId binding,
                                     long generation) {
            if (cellKinds.getOrDefault(binding, BindingCellKind.DIRECT)
                    == BindingCellKind.SHARED_CELL) {
                return;
            }
            keys.add(cell(binding, generation));
        }

        /**
         * The re-entrant invocation's private-state save, or {@code null}
         * when the callee body has no private state or is not already
         * active. The frame it pushes carries the previous active marker
         * and the saved state: only a nested invocation of the same body
         * (recursion) can overwrite the enclosing invocation's own state,
         * so only it saves and restores — a plain call keeps the flat
         * observable state the artifact's slots always had.
         */
        private String emitInvocationStateSave(FunctionId callee, OpId invocation) {
            List<String> keys = bodyStateKeys(callee);
            if (keys.isEmpty()) {
                return null;
            }
            long functionId = callee.id();
            out.append("__svStack[#__svStack + 1] = {__bodyActive[")
                .append(functionId).append("], ")
                .append(String.join(", ", keys)).append("}\n");
            out.append("__bodyActive[").append(functionId).append("] = true\n");
            return "__svStack[#__svStack]";
        }

        /** The matching re-entrant restore and pop, on every path. */
        private void emitInvocationStateRestore(FunctionId callee, String frame) {
            if (frame == null) {
                return;
            }
            List<String> keys = bodyStateKeys(callee);
            StringBuilder values = new StringBuilder();
            for (int i = 0; i < keys.size(); i++) {
                if (i > 0) {
                    values.append(", ");
                }
                values.append(frame).append("[").append(i + 2).append("]");
            }
            out.append("if ").append(frame).append("[1] then ")
                .append(String.join(", ", keys)).append(" = ")
                .append(values).append(" end\n");
            out.append("__bodyActive[").append(callee.id()).append("] = ")
                .append(frame).append("[1]\n");
            out.append("__svStack[#__svStack] = nil\n");
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
        private SemanticOp resolveExternalEntry(SemanticOp op,
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

        /**
         * The statically resolved execution binding of one CALL: the
         * inline Static binding or the unit's registered binding of an
         * Indirect callee identity (the same registration the semantic
         * oracle re-resolves at execution). A Dynamic callee is the
         * runtime-resolution slice (ISSUE-0531/ISSUE-0658): its execution
         * class is read from the resolved carrier at execution and the
         * emission-time binding is null ({@link #emitDynamicCall}).
         */
        private FunctionExecutionBinding callBinding(KindPayload.CallPayload payload) {
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                case KindPayload.CallCallee.Indirect indirect ->
                    unit.functionBindings().get(
                        new FunctionAllocationIdentity(indirect.callee().id()));
                case KindPayload.CallCallee.Dynamic ignored -> null;
            };
            if (binding == null
                    && !(payload.callee() instanceof KindPayload.CallCallee.Dynamic)) {
                throw new IllegalStateException("CALL " + payload
                    + " resolves no FunctionExecutionBinding (producer defect)");
            }
            return binding;
        }

        /**
         * The sync host call arm (ISSUE-0651;
         * {@code host-module-load-and-host-call-realization} H3/H7 and the
         * sync host call contract): the loaded surface entry is resolved
         * by {@code (hostModuleId, exportName)} — the resolved module
         * identity is the registry key, so no alias is needed and the
         * direct {@code CALL(HOST)}, the value-position
         * {@code CALL(INDIRECT)}, and a host callback all use the one
         * loaded entry — and invoked through the landed wrapper's
         * {@code .f} calling convention with the completed argument
         * values and the trailing literal span triplet.
         */
        private void emitHostCall(SemanticOp op, KindPayload.CallPayload payload,
                ModuleId hostModuleId, String exportName, boolean moduleEntry) {
            emitHostInvocation(op, payload,
                "__exportSurfaces[" + luaString(hostModuleId.path()) + "]["
                    + luaString(exportName) + "]",
                StdlibFunctionCatalog.lookup(hostModuleId.path(), exportName).orElse(null));
        }

        /**
         * The {@code HostFunctionValue} indirect call arm: the value
         * materialized at its producing host crossing is invoked through
         * the host-facing wrapper the crossing published — the loaded
         * surface's own calling convention ({@code .f} with the span
         * triplet), so the declared cells of the materialized function
         * type run exactly as the direct host call's do.
         */
        private void emitHostValueCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.HostFunctionValue hostValue) {
            SemanticOp crossing = opsById.get(hostValue.materializingBoundaryOpId());
            if (crossing == null
                    || !(crossing.payload() instanceof KindPayload.BoundaryPayload boundary)) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " names the materializing host crossing "
                    + hostValue.materializingBoundaryOpId()
                    + ", which is not a boundary op of the emitted closure"
                    + " (a producer defect)");
            }
            emitHostInvocation(op, payload, slot(boundary.input()));
        }

        /**
         * The invocation half of one host arm: the declared parameter
         * cells in one-based order (the loaded wrapper's own parameter
         * rule, so the pinned E8010 {@code parameter {i} type mismatch}
         * texts surface at the call origin), the host-facing projection of
         * each checked parameter (H7), the {@code .f} call with the span
         * triplet, and the declared return cell — every boundary child's
         * trace events (START, SUCCESS, FAILURE with the pinned projection)
         * surround the checks so the differential comparison against the
         * oracle stays event-for-event; production mode suppresses them
         * ({@code __ev} is a no-op).
         */
        private void emitHostInvocation(SemanticOp op, KindPayload.CallPayload payload,
                String target) {
            emitHostInvocation(op, payload, target, null);
        }

        private void emitHostInvocation(SemanticOp op, KindPayload.CallPayload payload,
                String target, StdlibFunctionCatalog.Entry catalogRow) {
            int argCount = emitHostParameterCells(op, payload);
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null
                ? null : opsById.get(payload.returnBoundaryOpId());
            if (catalogRow == null) {
                emitHostInvocationTail(op, target, argCount, returnBoundary);
            } else {
                emitStdlibCalleeInvocation(op, payload, target, catalogRow, argCount,
                    returnBoundary);
            }
            String result = slot((ValueId) op.result());
            out.append(result).append(" = __resT\n");
            emitResultSuccess(op, result, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The recorded host parameter cells of one host-shaped call (the
         * {@code DEAL_TO_HOST} + {@code HOST_PARAMETER} family): the loaded
         * wrapper's own parameter rule runs per declared position in one-based
         * order, so the pinned E8010 {@code parameter {i} type mismatch} texts
         * surface at the call origin, and each host-facing projection (H7)
         * lands in {@code __hbT[i]}. Returns the position count.
         */
        private int emitHostParameterCells(SemanticOp op, KindPayload.CallPayload payload) {
            out.append("__hbT = {}\n");
            int index = 1;
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String input = slot(boundaryPayload.input());
                String desc = boundaryPayload.descriptor().canonicalSpecText();
                String origin = luaString(originOf(boundary));
                emitBoundaryStart(boundary, input, boundaryPayload.descriptor());
                if (isFunctionPosition(boundaryPayload.descriptor())) {
                    out.append("__okB, __chkB = pcall(__hostFnParam, ")
                        .append(luaString(desc)).append(", ")
                        .append(luaString(innerFunctionText(boundaryPayload.descriptor())))
                        .append(", ").append(index).append(", ").append(input)
                        .append(", ").append(origin).append(")\n");
                } else {
                    out.append("__okB, __chkB = pcall(__hostParamCell, ")
                        .append(luaString(desc)).append(", ").append(index)
                        .append(", ").append(input).append(", ").append(origin)
                        .append(")\n");
                }
                out.append("if not __okB then\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                emitBoundarySuccessAtom(boundary, "__hostCellAtom("
                    + luaString(staticKind(boundaryPayload.descriptor()))
                    + ", __chkB)");
                out.append("__hbT[").append(index).append("] = __hostProjectArg(")
                    .append(luaString(desc)).append(", ")
                    .append(sourceTextOf(boundaryPayload.descriptor())).append(", __chkB)\n");
                index++;
            }
            return index - 1;
        }

        /**
         * The conversion intrinsic's value call (ISSUE-0679; design source
         * {@code conversion-intrinsic-function-values} J3/J4): the seeded
         * identity's registration is a boundary-shaped callable, so the
         * indirect arm runs exactly the recorded host cell family — one
         * {@code DEAL_TO_HOST} + {@code HOST_PARAMETER} cell per declared
         * parameter through the landed host parameter rule (the argument
         * domain the cells own; a null or wrong-kind argument is a
         * parameter-cell projection, never a conversion failure) — then the one
         * conversion ladder with the invoking CALL op's own context and kind
         * label (the pinned texts and the FAILURE event carry the invoking op),
         * then the recorded {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN}
         * cell at the call origin. One algorithm authority with the direct
         * {@code INTRINSIC_CALL} arm, whose kind label stays its own.
         */
        private void emitIntrinsicValueCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.IntrinsicFunction intrinsic) {
            int argCount = emitHostParameterCells(op, payload);
            if (argCount != intrinsic.descriptor().paramTypes().size()) {
                throw new IllegalStateException("the conversion intrinsic call "
                    + op.opId() + " records " + argCount + " parameter cell(s) for the '"
                    + intrinsic.kind() + "' intrinsic's "
                    + intrinsic.descriptor().paramTypes().size() + " declared "
                    + "parameter(s) (a producer defect)");
            }
            String helper = intrinsic.kind() == IntrinsicKind.INT_CONVERT
                ? "__intConv" : "__numConv";
            out.append("__resT = ").append(helper).append("(__hbT[1], ")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(staticKind(
                    intrinsic.descriptor().paramTypes().get(0))))
                .append(", ").append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(originOf(op))).append(")\n");
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null
                ? null : opsById.get(payload.returnBoundaryOpId());
            // The converted value is a plain chunk value (a DEAL int/number,
            // never a host carrier), admitted by the same general check the
            // direct arm's and the cataloged callable's recorded cells run.
            emitHostReturnCellRun(op, returnBoundary, "__atom");
            String result = slot((ValueId) op.result());
            out.append(result).append(" = __resT\n");
            emitResultSuccess(op, result, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The intrinsic kind of one adapter's statically fixed recorded
         * source, or {@code null} (ISSUE-0680; design source
         * {@code conversion-intrinsic-function-values} J5): a VALUE source
         * operand whose identity carries the seeded {@code IntrinsicFunction}
         * registration under the identity-preserving-load predicate — the
         * same resolution the adapter's creation operand publishes, so the
         * call site and the creation site agree on the source class, and an
         * operand of any other binding or class keeps the landed
         * {@code __adaptInvoke} protocol.
         */
        private IntrinsicKind adapterIntrinsicKind(
                FunctionExecutionBinding.AdapterBinding adapter) {
            if (!(adapter.sourceRef() instanceof AdaptSourceRef.Value value)) {
                return null;
            }
            return intrinsicKindOf(value.value());
        }

        /**
         * The one conversion ladder at one DEAL call site (ISSUE-0679 J4;
         * ISSUE-0680 for the adapter-over-intrinsic path): the closed kind's
         * conversion over the cell-admitted argument with the invoking op's
         * own context, kind label, and origin — the pinned texts and the
         * FAILURE event carry the invoking op. One algorithm authority with
         * the direct {@code INTRINSIC_CALL} arm, whose kind label stays its
         * own.
         */
        private void emitIntrinsicLadder(SemanticOp op, IntrinsicKind kind, String input,
                                         String indent) {
            String helper = kind == IntrinsicKind.INT_CONVERT ? "__intConv" : "__numConv";
            out.append(indent).append("__resT = ").append(helper).append("(")
                .append(input).append(", ").append(luaString(op.kind().name()))
                .append(", ")
                .append(luaString(staticKind(kind.declaredSignature().paramTypes().get(0))))
                .append(", ").append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(originOf(op))).append(")\n");
        }

        /**
         * The one conversion ladder inside a task closure (ISSUE-0680): the
         * task body's pcall over the closed kind's conversion with the
         * invoking op's own context and kind label; the closure re-raises
         * the captured conversion error unchanged, so a conversion failure
         * surfaces at the owning AWAIT exactly as the task protocol
         * prescribes (the async form's single completion position).
         */
        private void emitIntrinsicLadderPcall(SemanticOp op, IntrinsicKind kind,
                                              String input, String indent) {
            String helper = kind == IntrinsicKind.INT_CONVERT ? "__intConv" : "__numConv";
            out.append(indent).append("__okA, __resA = pcall(").append(helper)
                .append(", ").append(input).append(", ")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(staticKind(kind.declaredSignature().paramTypes().get(0))))
                .append(", ").append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(originOf(op))).append(")\n");
        }

        /**
         * The adapter-over-intrinsic invocation at a statically classified
         * call site (ISSUE-0680; design source
         * {@code conversion-intrinsic-function-values} J5): the landed D15
         * order with the seeded intrinsic identity as the recorded source —
         * (1) the source resolution per the recorded capture mode (VALUE
         * retains the memoized carrier the adapter creation published),
         * (2) the carried canonical spec checked against the recorded source
         * signature (the pinned E8010 at this CALL's origin), (3) the
         * leading-M argument projection over the recorded target-cell values,
         * (4) the one conversion ladder with the invoking CALL op's own
         * context and kind, and (5) the recorded {@code HOST_TO_DEAL} +
         * {@code HOST_SYNC_RETURN} cell — the source class is HOST, so the
         * call op runs exactly the cell the intrinsic's own indirect arm
         * records. The checked value is left in {@code __resT}.
         */
        private void emitAdapterOverIntrinsicRun(SemanticOp op,
                KindPayload.CallPayload payload,
                FunctionExecutionBinding.AdapterBinding adapter) {
            IntrinsicKind kind = adapterIntrinsicKind(adapter);
            if (kind == null) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " records an adapter whose source is not the seeded intrinsic "
                    + "identity (producer defect)");
            }
            RuntimeDescriptor.Func declared = kind.declaredSignature();
            String adapterSlot = slot((ValueId) opsById.get(adapter.adaptOpId()).result());
            String origin = originOf(op);
            out.append("__dynS = __adaptSource(").append(adapterSlot).append(")\n");
            out.append("__okB, __chkB = pcall(__fncheck, __dynS, ")
                .append(luaString(adapter.sourceSignature().canonicalSpecText()))
                .append(", ").append(luaString(origin)).append(")\n");
            out.append("if not __okB then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__chkB)");
            out.append("  error(__chkB, 0)\n");
            out.append("end\n");
            int m = adapter.sourceSignature().paramTypes().size();
            if (m != declared.paramTypes().size()
                    || m > payload.parameterBoundaryOpIds().size()) {
                throw new IllegalStateException("the adapter-over-intrinsic call "
                    + op.opId() + " projects " + m + " leading source argument(s) "
                    + "onto the '" + kind + "' intrinsic's "
                    + declared.paramTypes().size() + " declared parameter(s) with "
                    + payload.parameterBoundaryOpIds().size()
                    + " recorded target cell(s) (producer defect)");
            }
            SemanticOp leading = opsById.get(payload.parameterBoundaryOpIds().get(0));
            String input = slot(((KindPayload.BoundaryPayload) leading.payload()).input());
            emitIntrinsicLadder(op, kind, input, "");
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null
                ? null : opsById.get(payload.returnBoundaryOpId());
            emitHostReturnCellRun(op, returnBoundary, "__atom");
        }

        /**
         * The cataloged-callable sub-class of one host-shaped call: the read's
         * own registration resolved the closed catalog row, so the invocation is
         * the row's one invoker with the invoking call's own context — never the
         * loaded surface entry's {@code .f} — and the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell runs at the call
         * origin, exactly the direct {@code STDLIB_CALL} arm's observables and the
         * oracle's cataloged branch of {@code invokeResolvedHostRequest}.
         *
         * <p>The argument domain is the recorded {@code HOST_PARAMETER} cells'
         * host-facing projection: the closed catalog rows declare non-nullable
         * scalar/table parameter positions only, for which that projection is the
         * identity — a nullable, function, or class position is a fail-closed
         * producer defect, never a silently projected argument.</p>
         *
         * @param op              the invoking CALL op; non-null
         * @param payload         the CALL payload (its recorded parameter cells);
         *                        non-null
         * @param target          the surface entry expression (the cataloged
         *                        carrier); non-null
         * @param row             the resolved catalog row; non-null
         * @param argCount        the completed argument count; ≥0
         * @param returnBoundary  the recorded {@code HOST_TO_DEAL} cell, or null
         */
        private void emitStdlibCalleeInvocation(SemanticOp op,
                KindPayload.CallPayload payload, String target,
                StdlibFunctionCatalog.Entry row, int argCount, SemanticOp returnBoundary) {
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                RuntimeDescriptor descriptor = ((KindPayload.BoundaryPayload)
                    opsById.get(boundaryId).payload()).descriptor();
                if (isFunctionPosition(descriptor)
                        || descriptor instanceof RuntimeDescriptor.Class
                        || descriptor instanceof RuntimeDescriptor.Nullable) {
                    throw new IllegalStateException("the cataloged callable '"
                        + row.declaredDescriptor().canonicalSpecText() + "' arrives at "
                        + op.opId() + " with the parameter position "
                        + descriptor.canonicalSpecText() + ", whose host-facing "
                        + "projection is not the identity — a producer defect");
                }
            }
            out.append("if ").append(target).append(" ~= nil and ").append(target)
                .append(".__sid ~= nil then\n");
            out.append("  __resT = ").append(target).append(".__fn(")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(originOf(op)));
            for (int i = 1; i <= argCount; i++) {
                out.append(", __hbT[").append(i).append("]");
            }
            out.append(")\n");
            // The recorded cell's admission: the cataloged callable's result is a
            // plain chunk value, admitted by the same general check the direct
            // STDLIB_CALL arm's STDLIB_RETURN cell runs (its failures keep the
            // descriptor-kind projection), so a null-typed row's Lua nil is the
            // language null exactly as the oracle's NullValue is.
            emitHostReturnCellRun(op, returnBoundary, "__atom");
            out.append("else\n");
            emitHostInvocationTail(op, target, argCount, returnBoundary);
            out.append("end\n");
        }

        /**
         * The invocation tail of one host row (ISSUE-0658 extraction of
         * the landed ISSUE-0651 host arm): the {@code .f} call with the
         * host-projected parameters ({@code __hbT[1..argCount]}) and the
         * trailing literal span triplet, the wrapper-error projection,
         * and the declared return cell — the checked value is left in
         * {@code __resT}. Shared by the static host arms (target: the
         * loaded surface entry; cell: the payload's single
         * {@code HOST_TO_DEAL} child) and the dynamic dispatch's HOST
         * row (target: the carrier's own loaded surface entry; cell: the
         * recorded {@code HOST_TO_DEAL} cell of the dynamic
         * return-boundary set).
         */
        private void emitHostInvocationTail(SemanticOp op, String target, int argCount,
                                            SemanticOp returnBoundary) {
            String declaredReturn = returnBoundary == null ? null
                : ((KindPayload.BoundaryPayload) returnBoundary.payload())
                    .descriptor().canonicalSpecText();
            // The converged host-boundary call shape: the trailing literal
            // span triplet is how a boundary error reports the DEAL call
            // site byte-exact.
            out.append("__okT, __resT = pcall(").append(target).append(".f");
            for (int i = 1; i <= argCount; i++) {
                out.append(", __hbT[").append(i).append("]");
            }
            out.append(", ").append(spanTripletArgs(op)).append(")\n");
            out.append("if not __okT then\n");
            out.append("  __resT = __hostError(__resT, ")
                .append(luaString(originOf(op))).append(")\n");
            if (returnBoundary != null) {
                // The loaded wrapper runs the declared return rule itself,
                // so its return-cell failure surfaces inside the pcall:
                // the boundary child's FAILURE event carries the wrapper's
                // error, exactly the JVM arm's wrapper-error path.
                out.append("  if type(__resT) == \"table\" and __resT.code == \"E8010\""
                    + " and type(__resT.m) == \"string\" and string.find(__resT.m,"
                    + " \"return value 1 type mismatch\", 1, true) == 1 then\n");
                emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                    "__errtext(__resT)");
                out.append("  end\n");
            }
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            emitHostReturnCellRun(op, returnBoundary, "__hostCellAtom");
        }

        /**
         * The declared-return half of one host-shaped result: the call op runs
         * the recorded {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell on
         * the value left in {@code __resT} — the class-value carrier projection
         * (F4) first, then the boundary's START/SUCCESS atoms and the
         * descriptor check under the cell's own origin. Shared by the static
         * host arms' invocation tail and the dynamic dispatch's HOST row (the
         * landed host wrapper and the cataloged stdlib callable alike), so the
         * recorded cell runs exactly once per invocation on every HOST path.
         *
         * @param op              the invoking call op; non-null
         * @param returnBoundary  the recorded {@code HOST_TO_DEAL} cell, or
         *                        {@code null} for a call with no return cell;
         *                        the caller leaves the checked value in
         *                        {@code __resT}
         * @param atomizer        the prelude atom helper for the cell's
         *                        boundary atoms: the DEAL-null-aware host
         *                        atom for a loaded host surface value, the
         *                        general value atom for the cataloged stdlib
         *                        callable's result (a session without a host
         *                        declaration surface emits no host atom helper)
         */
        private void emitHostReturnCellRun(SemanticOp op, SemanticOp returnBoundary,
                                           String atomizer) {
            if (returnBoundary == null) {
                return;
            }
            boolean hostValue = "__hostCellAtom".equals(atomizer);
            KindPayload.BoundaryPayload cellPayload =
                (KindPayload.BoundaryPayload) returnBoundary.payload();
            String declaredReturn = cellPayload.descriptor().canonicalSpecText();
            // The class-value carrier projection (F4): on a class-typed
            // return the wrapper's loaded value is projected into the
            // chunk's class representation *before* the crossing's
            // events, so the boundary's START/SUCCESS atoms and the
            // program observe the one projected heap value — never the
            // wrapper's raw runtime value (the trace-identity rule).
            // A cataloged stdlib result is a plain chunk value: no
            // projection applies.
            if (hostValue && cellPayload.descriptor() instanceof RuntimeDescriptor.Class) {
                out.append("__resT = __hostDealProject(")
                    .append(luaString(declaredReturn)).append(", __resT, ")
                    .append(luaString(originOf(returnBoundary))).append(")\n");
            }
            // The boundary events' atoms are the DEAL-null-aware host
            // atom for a loaded host surface value (the deployed
            // runtime's null sentinel is the language null, so a null
            // return atomizes as "null" exactly like the oracle's
            // NullValue) and the general value atom for the cataloged
            // stdlib callable's result (whose session emits no host
            // helper).
            emitBoundaryStartAtom(returnBoundary, atomizer + "("
                + luaString(staticKind(cellPayload.descriptor())) + ", __resT)");
            if (hostValue) {
                out.append("__okB, __chkB = pcall(__hostReturnCell, ")
                    .append(luaString(declaredReturn)).append(", __resT, ")
                    .append(luaString(originOf(returnBoundary))).append(", false)\n");
            } else {
                out.append("__okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(declaredReturn)).append(", ")
                    .append(luaString(staticKind(cellPayload.descriptor())))
                    .append(", __resT)\n");
            }
            out.append("if not __okB then\n");
            if (!hostValue) {
                out.append("  __chkB.o = ")
                    .append(luaString(originOf(returnBoundary))).append("\n");
            }
            emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                "__errtext(__chkB)");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "__errtext(__chkB)");
            out.append("  error(__chkB, 0)\n");
            out.append("end\n");
            emitBoundarySuccessAtom(returnBoundary, atomizer + "("
                + luaString(staticKind(cellPayload.descriptor())) + ", __resT)");
            out.append("__resT = __chkB\n");
        }

        /**
         * The dynamic CALL arm (ISSUE-0658;
         * {@code dynamic-call-shape-production-and-emission} Y2/Y3/Y5/Y6
         * and the dynamic dispatch contract): the recorded parameter
         * cells ran once, left to right, before the dispatch (the
         * class-independent family); the carrier's own class tag then
         * selects exactly one class path — never the checked descriptor,
         * the callee spelling, or an argument value.
         *
         * <p>{@code DEAL_BODY} resolves the carrier's function id to its
         * owning module through the chunk-global {@code __fnModules}
         * table (built by the same walk that declares the function
         * factories), pushes the callee frame, switches the module
         * context, and invokes the carrier's own invoker
         * ({@code __unfn}); {@code ADAPTER} runs the landed D15 sequence
         * (the source value's own tag, the source-signature check, the
         * leading-M argument projection) and executes the cell the
         * source class selects — a DEAL-body source runs that body's own
         * {@code RETURN} cell; {@code HOST} invokes the loaded surface
         * entry through its host calling convention and runs the
         * recorded {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell
         * of the dynamic return-boundary set.</p>
         *
         * <p>Every other carrier — and an adapter whose D15 source value
         * identifies no executable class at this boundary — fails closed
         * with the pinned E8001 {@code expected function} projection
         * ({@code expected}/{@code actual}) at the call origin, exactly
         * the projection the materialization-site function row produces:
         * never a guessed path and never a silent no-op. The module
         * context and the frame stack are restored on success and on
         * failure; the checked value is left in {@code __resT}.</p>
         */
        private void emitDynamicCall(SemanticOp op, KindPayload.CallPayload payload,
                                     KindPayload.CallCallee.Dynamic callee) {
            KindPayload.DynamicReturnBoundary cells = payload.dynamicReturnBoundary();
            if (cells == null) {
                throw new IllegalStateException("the dynamic CALL " + op.opId()
                    + " records no DynamicReturnBoundary cell set (producer defect)");
            }
            SemanticOp hostCell = opsById.get(cells.hostBoundaryOpId());
            if (hostCell == null
                    || !(hostCell.payload() instanceof KindPayload.BoundaryPayload boundary)
                    || boundary.kind() != BoundaryKind.HOST_TO_DEAL) {
                throw new IllegalStateException("the dynamic CALL " + op.opId()
                    + " records the host return cell " + cells.hostBoundaryOpId()
                    + ", which is not a HOST_TO_DEAL boundary of the emitted closure"
                    + " (producer defect)");
            }
            String origin = luaString(originOf(op));
            // The recorded DEAL-body cell's closed form (ISSUE-0677; design
            // source {@code function-typed-value-materialization-and-dispatch}
            // M6): a call-owned record is executed by the invocation site on
            // the value the resolved body returned, after the body's own
            // RETURN ran the body's own cell; a callee-owned record is that
            // body's own cell and runs nothing here.
            SemanticOp recordedDealCell = opsById.get(cells.dealBodyBoundaryOpId());
            boolean callOwnedDealCell = recordedDealCell != null
                && callOwnedCell(recordedDealCell);
            StringBuilder argList = new StringBuilder();
            StringBuilder argTable = new StringBuilder();
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp parameter = opsById.get(boundaryId);
                String input = slot(((KindPayload.BoundaryPayload) parameter.payload())
                    .input());
                argList.append(", ").append(input);
                if (argTable.length() > 0) {
                    argTable.append(", ");
                }
                argTable.append(input);
            }
            out.append("__dynC = ").append(slot(callee.callee())).append("\n");
            out.append("__dynK = __dynClass(__dynC)\n");
            // DEAL_BODY: the carrier's function id resolves its owning
            // module; the frame and the module context are restored on
            // every path.
            out.append("if __dynK == \"DEAL_BODY\" then\n");
            out.append("  __dynM = __fnModules[__dynC.__fid]\n");
            out.append("  if __dynM == nil then\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  end\n");
            out.append("  __modStack[#__modStack + 1] = __module\n");
            out.append("  __module = __dynM\n");
            out.append("  table.insert(__frames, 1, tostring(__dynC.__fid))\n");
            out.append("  __okT, __resT = pcall(__unfn(__dynC)").append(argList)
                .append(")\n");
            out.append("  table.remove(__frames, 1)\n");
            out.append("  __module = __modStack[#__modStack]\n");
            out.append("  __modStack[#__modStack] = nil\n");
            out.append("  if not __okT then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("    error(__resT, 0)\n");
            out.append("  end\n");
            if (callOwnedDealCell) {
                emitRecordedCellRun(op, recordedDealCell, "__resT", "  ");
            }
            // ADAPTER: the landed D15 sequence; the source class selects
            // the return cell (a DEAL-body source runs its own body's
            // RETURN cell, and a call-owned recorded cell then runs at the
            // invocation site).
            out.append("elseif __dynK == \"ADAPTER\" then\n");
            out.append("  __dynS = __adaptSource(__dynC)\n");
            out.append("  __okB, __chkB = pcall(__fncheck, __dynS, __dynC.__csrc, ")
                .append(origin).append(")\n");
            out.append("  if not __okB then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__chkB)");
            out.append("    error(__chkB, 0)\n");
            out.append("  end\n");
            out.append("  __dynS = __chkB\n");
            out.append("  __dynSK = __dynClass(__dynS)\n");
            out.append("  if __dynSK == \"DEAL_BODY\" then\n");
            out.append("    __dynM = __fnModules[__dynS.__fid]\n");
            out.append("    if __dynM == nil then\n");
            out.append("      __dynC = __dynS\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("    end\n");
            out.append("    __modStack[#__modStack + 1] = __module\n");
            out.append("    __module = __dynM\n");
            out.append("    table.insert(__frames, 1, tostring(__dynS.__fid))\n");
            out.append("    __dynA = {").append(argTable).append("}\n");
            out.append("    __okT, __resT = pcall(__unfn(__dynS), unpack(__dynA, 1, ")
                .append("__dynC.__m))\n");
            out.append("    table.remove(__frames, 1)\n");
            out.append("    __module = __modStack[#__modStack]\n");
            out.append("    __modStack[#__modStack] = nil\n");
            out.append("    if not __okT then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("      error(__resT, 0)\n");
            out.append("    end\n");
            if (callOwnedDealCell) {
                emitRecordedCellRun(op, recordedDealCell, "__resT", "    ");
            }
            // The runtime adapter branch's intrinsic source (ISSUE-0680;
            // design source {@code conversion-intrinsic-function-values}
            // J5): the resolved source value is the memoized intrinsic
            // carrier, so the same D15 sequence runs here — the leading-M
            // recorded argument through the one conversion ladder with the
            // invoking CALL op's context and kind, then the recorded
            // HOST_TO_DEAL + HOST_SYNC_RETURN cell of the dynamic set (the
            // source class is HOST). Non-intrinsic source values keep the
            // landed fail-closed residue.
            out.append("  elseif __dynS.__it ~= nil then\n");
            if (payload.parameterBoundaryOpIds().isEmpty()) {
                // The leading-M projection of the runtime intrinsic source has
                // no argument to convert (the intrinsic declares one
                // parameter): the carrier fails closed at the call origin.
                out.append("    __dynC = __dynS\n");
                emitDynamicCarrierFailure(op, origin);
            } else {
                SemanticOp dynamicLeading =
                    opsById.get(payload.parameterBoundaryOpIds().get(0));
                String dynamicInput =
                    slot(((KindPayload.BoundaryPayload) dynamicLeading.payload()).input());
                out.append("    if __dynS.__it == \"INT_CONVERT\" then\n");
                emitIntrinsicLadder(op, IntrinsicKind.INT_CONVERT, dynamicInput,
                    "      ");
                out.append("    elseif __dynS.__it == \"NUMBER_CONVERT\" then\n");
                emitIntrinsicLadder(op, IntrinsicKind.NUMBER_CONVERT, dynamicInput,
                    "      ");
                out.append("    else\n");
                out.append("      __dynC = __dynS\n");
                emitDynamicCarrierFailure(op, origin);
                out.append("    end\n");
                emitHostReturnCellRun(op, hostCell, "__atom");
            }
            out.append("  else\n");
            out.append("    __dynC = __dynS\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  end\n");
            // HOST: the loaded surface entry (the carrier itself) and the
            // recorded HOST_TO_DEAL + HOST_SYNC_RETURN cell.
            out.append("elseif __dynK == \"HOST\" then\n");
            emitDynamicHostRow(op, payload, hostCell);
            // The fail-closed residue: no class is resolvable.
            out.append("else\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("end\n");
        }

        /**
         * The dynamic dispatch's HOST row: the carrier's own HOST sub-class
         * decides the path (never the checked descriptor). The conversion
         * intrinsic ({@code __it}) runs the closed kind's conversion ladder
         * with the invoking CALL op's own context and kind label — one
         * algorithm authority with the direct {@code INTRINSIC_CALL} arm
         * (ISSUE-0679; design source
         * {@code conversion-intrinsic-function-values} J3/J4). A loaded surface
         * entry is invoked through its host calling convention ({@code .f} with
         * the projected parameters and the trailing literal span triplet); the
         * cataloged stdlib callable ({@code __sid}) runs the closed catalog
         * row's one invoker with the invoking CALL op's context (the row
         * identity plus the op key, contract digest, parent key, and origin —
         * one algorithm authority with the direct {@code STDLIB_CALL} arm and
         * the read's callable), its failures projecting the CALL op's own
         * FAILURE event kind. Every sub-class then runs the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell exactly once at
         * the call origin (the oracle's {@code invokeResolvedHostRequest}
         * followed by {@code runBoundaryChild}). The checked value is left in
         * {@code __resT}.
         */
        private void emitDynamicHostRow(SemanticOp op, KindPayload.CallPayload payload,
                                        SemanticOp returnBoundary) {
            // The conversion intrinsic's sub-class (ISSUE-0679): the carrier's
            // own kind tag selects the one conversion ladder over the value the
            // recorded class-independent parameter cells admitted (the declared
            // parameter descriptor is the argument domain), with the invoking
            // CALL op's context and kind label; then the recorded cell admits
            // the converted value.
            if (payload.parameterBoundaryOpIds().size() == 1) {
                SemanticOp parameter = opsById.get(payload.parameterBoundaryOpIds().get(0));
                KindPayload.BoundaryPayload parameterPayload =
                    (KindPayload.BoundaryPayload) parameter.payload();
                String input = slot(parameterPayload.input());
                String declaredKind = luaString(staticKind(parameterPayload.descriptor()));
                out.append("  if __dynC.__it == \"INT_CONVERT\" then\n");
                out.append("    __resT = __intConv(").append(input)
                    .append(", ").append(luaString(op.kind().name())).append(", ")
                    .append(declaredKind).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op))).append(")\n");
                emitHostReturnCellRun(op, returnBoundary, "__atom");
                out.append("  elseif __dynC.__it == \"NUMBER_CONVERT\" then\n");
                out.append("    __resT = __numConv(").append(input)
                    .append(", ").append(luaString(op.kind().name())).append(", ")
                    .append(declaredKind).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op))).append(")\n");
                emitHostReturnCellRun(op, returnBoundary, "__atom");
                out.append("  elseif __dynC.__sid ~= nil then\n");
            } else {
                // No checker-valid program reaches an intrinsic carrier at a
                // site without the intrinsic's single declared parameter cell;
                // the tag still fails closed rather than guessing a conversion.
                out.append("  if __dynC.__it ~= nil then\n");
                emitDynamicCarrierFailure(op, luaString(originOf(op)));
                out.append("  elseif __dynC.__sid ~= nil then\n");
            }
            out.append("    __resT = __dynC.__fn(")
                .append(luaString(op.kind().name())).append(", ")
                .append(luaString(opKey(op.opId()))).append(", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(luaString(originOf(op)));
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp parameter = opsById.get(boundaryId);
                out.append(", ").append(slot(((KindPayload.BoundaryPayload)
                    parameter.payload()).input()));
            }
            out.append(")\n");
            emitHostReturnCellRun(op, returnBoundary, "__atom");
            out.append("  else\n");
            int index = 1;
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp parameter = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) parameter.payload();
                out.append("  __hbT[").append(index).append("] = __hostProjectArg(")
                    .append(luaString(boundaryPayload.descriptor().canonicalSpecText()))
                    .append(", ")
                    .append(sourceTextOf(boundaryPayload.descriptor())).append(", ")
                    .append(slot(boundaryPayload.input())).append(")\n");
                index++;
            }
            emitHostInvocationTail(op, "__dynC", index - 1, returnBoundary);
            out.append("  end\n");
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
        private boolean callOwnedCell(SemanticOp cell) {
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

        /**
         * The invocation site's execution of one call-owned recorded
         * DEAL-body cell (ISSUE-0677; the oracle's
         * {@code runBoundaryChild} over the recorded cell): the cell's START
         * event carries the input atom, the boundary check runs under the
         * cell's own origin, the SUCCESS terminal publishes the admitted
         * value, and a failure emits the cell's and the invocation op's
         * FAILURE events and raises. The cell is total on the admitted value
         * (an identical declared descriptor), so its check passes and only
         * its boundary events are observable.
         *
         * @param invocation the dynamic invocation op; non-null
         * @param cell       the recorded call-owned cell; non-null
         * @param valueSlot  the Lua slot holding the returned value; non-null
         * @param indent     the emitted block's indentation prefix; non-null
         */
        private void emitRecordedCellRun(SemanticOp invocation, SemanticOp cell,
                                         String valueSlot, String indent) {
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) cell.payload();
            // The START carries the input's atom (the oracle's
            // runBoundaryChild START), the check runs under the cell's own
            // origin, and the SUCCESS terminal publishes the admitted value.
            out.append(indent).append("__ev(").append(luaString(opKey(cell.opId())))
                .append(", \"START\", \"BOUNDARY\", ")
                .append(luaString(cell.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(cell.origin().parentOpId())))
                .append(", {__atom(")
                .append(luaString(staticKind(payload.descriptor()))).append(", ")
                .append(valueSlot).append(")}, nil, nil)\n");
            out.append(indent).append("__okD, __chkD = pcall(__bcheck, ")
                .append(bcheckArgs(payload.descriptor(), valueSlot)).append(")\n");
            out.append(indent).append("if not __okD then\n");
            out.append(indent).append("  __chkD.o = ")
                .append(luaString(originOf(cell))).append("\n");
            emitFailureEvent(cell.opId(), "BOUNDARY", cell, "__errtext(__chkD)");
            emitFailureEvent(invocation.opId(), invocation.kind().name(), invocation,
                "__errtext(__chkD)");
            out.append(indent).append("  error(__chkD, 0)\n");
            out.append(indent).append("end\n");
            out.append(indent).append(valueSlot).append(" = __chkD\n");
            out.append(indent).append("__ev(").append(luaString(opKey(cell.opId())))
                .append(", \"SUCCESS\", \"BOUNDARY\", ")
                .append(luaString(cell.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(cell.origin().parentOpId())))
                .append(", {}, __atom(")
                .append(luaString(staticKind(payload.descriptor()))).append(", ")
                .append(valueSlot).append("), nil)\n");
        }

        /**
         * The dynamic dispatch's fail-closed residue: a carrier whose
         * class is not resolvable at this boundary projects the pinned
         * E8001 {@code expected function} text with the carrier's actual
         * runtime kind at the call origin, emits the op's single FAILURE
         * terminal, and raises — nothing executes silently.
         */
        private void emitDynamicCarrierFailure(SemanticOp op, String origin) {
            out.append("__dynE = __failExpr(\"E8001\", \"expected function, got \""
                + "..__actualOf(\"function\", __dynC), ").append(origin)
                .append(", \"function\", __actualOf(\"function\", __dynC))\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__dynE)");
            out.append("error(__dynE, 0)\n");
        }

        /**
         * The dynamic {@code ASYNC_START} arm (ISSUE-0658; ISSUE-0678 for the
         * asynchronous host class;
         * {@code dynamic-call-shape-production-and-emission} Y4/Y5 and
         * the dynamic async start contract): the recorded parameter
         * cells ran above; a DEAL-body carrier starts the callee body
         * task under the callee's module context with the recorded
         * task cell (the body's own {@code RETURN} runs it) — a callee value
         * of another unit resolves its owning module through the carrier's
         * function id and runs its own body under that module context, the
         * emitter twin of the oracle's owning-unit body terminal; the adapter
         * class runs the landed D15 sequence and starts the source
         * class's task under the source's module context with the
         * leading-M recorded arguments (the source body task), with
         * zero caller-side return boundaries beyond the recorded task
         * cell — the oracle's {@code executeDynamicAdapterAsyncStart}; a
         * loaded host surface entry ({@code __kind == "function"}) starts the
         * declared async export through the same host calling convention and
         * {@code ASYNC_OPERATION_HANDLE} terminal as the static arm, with the
         * operation handle bound to this token under the entry's declared
         * identity (the oracle's dynamic HOST resolution; zero caller-side
         * return cells). A shared-body/retained-ABI external function value
         * carries no value tag at all (M4: the identity channel only), so a
         * value-resolved external callee of another unit is the DEAL-body
         * class above — its own body under its own module context — and the
         * identity-channel external async link stays the landed static
         * {@code ASYNC_START(EXTERNAL)} arm's recorded
         * {@code ExternalAsyncLink}. A carrier of any other class fails closed
         * here with the pinned E8001 at the start origin, as does an adapter
         * whose D15 source value identifies no class the closed protocol
         * resolves and a host-tagged carrier whose declared identity resolves
         * no unique loaded surface entry. The caller records no
         * return boundary beyond the recorded task cell, and its single
         * {@code AWAIT} drains the token.
         */
        private void emitDynamicAsyncStart(SemanticOp op,
                                           KindPayload.AsyncStartPayload payload,
                                           KindPayload.CallCallee.Dynamic callee,
                                           AsyncTokenId token) {
            String origin = luaString(originOf(op));
            String carrierArgs = "S.__sa" + op.opId().id();
            // The recorded task cell's closed form (ISSUE-0677; design
            // source {@code function-typed-value-materialization-and-dispatch}
            // M6): a call-owned record executes in this caller-side task
            // wrapper before the token completes; a callee-owned record is
            // the resolved body's own cell and runs inside the body.
            SemanticOp recordedTaskCell = payload.returnBoundaryOpId() == null
                ? null : opsById.get(payload.returnBoundaryOpId());
            boolean callOwnedTaskCell = recordedTaskCell != null
                && callOwnedCell(recordedTaskCell);
            out.append("__dynC = ").append(slot(callee.callee())).append("\n");
            out.append("__dynK = __dynClass(__dynC)\n");
            // DEAL_BODY: the carrier's function id resolves its owning
            // module; the frame and the module context are restored on
            // every path.
            out.append("if __dynK == \"DEAL_BODY\" then\n");
            out.append("  __dynM = __fnModules[__dynC.__fid]\n");
            out.append("  if __dynM == nil then\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  end\n");
            out.append("  __asyncStartTask(").append(token.tokenId())
                .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
            out.append("    __modStack[#__modStack + 1] = __module\n");
            out.append("    __module = __dynM\n");
            out.append("    table.insert(__frames, 1, tostring(__dynC.__fid))\n");
            out.append("    local __okA, __resA = pcall(__unfn(__dynC), unpack(")
                .append(carrierArgs).append(", 1, #").append(carrierArgs)
                .append("))\n");
            out.append("    table.remove(__frames, 1)\n");
            out.append("    __module = __modStack[#__modStack]\n");
            out.append("    __modStack[#__modStack] = nil\n");
            out.append("    if not __okA then error(__resA, 0) end\n");
            if (callOwnedTaskCell) {
                emitRecordedCellRun(op, recordedTaskCell, "__resA", "    ");
            }
            out.append("    return __resA\n");
            out.append("  end), ").append(carrierArgs).append(")\n");
            // ADAPTER: the landed D15 sequence resolves the source value
            // and checks its carried source spec; the source class then
            // starts its own task with the leading-M recorded arguments
            // (a DEAL-body source runs that body's own RETURN cell under
            // its module context, with zero caller-side return
            // boundaries).
            out.append("elseif __dynK == \"ADAPTER\" then\n");
            out.append("  __dynS = __adaptSource(__dynC)\n");
            out.append("  __okB, __chkB = pcall(__fncheck, __dynS, __dynC.__csrc, ")
                .append(origin).append(")\n");
            out.append("  if not __okB then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__chkB)");
            out.append("    error(__chkB, 0)\n");
            out.append("  end\n");
            out.append("  __dynS = __chkB\n");
            // The runtime adapter branch's intrinsic source (ISSUE-0680;
            // design source {@code conversion-intrinsic-function-values}
            // J5): the resolved source value is the memoized intrinsic
            // carrier, so the task is the closed DEAL_BODY task running the
            // one conversion ladder with this op's context and kind over the
            // leading-M recorded argument and completing immediately with
            // the converted value; the single AWAIT runs the landed
            // ASYNC_COMPLETION cell. Every other non-DEAL_BODY source keeps
            // the landed fail-closed residue.
            out.append("  if __dynS.__it ~= nil then\n");
            if (recordedArgCount(payload, op) == 0) {
                // The leading-M projection of the runtime intrinsic source has
                // no argument to convert (the intrinsic declares one
                // parameter): the carrier fails closed at the start origin.
                out.append("    __dynC = __dynS\n");
                emitDynamicCarrierFailure(op, origin);
            } else {
            out.append("    __asyncStartTask(").append(token.tokenId())
                .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
            out.append("      local __okA, __resA\n");
            out.append("      if __dynS.__it == \"INT_CONVERT\" then\n");
            emitIntrinsicLadderPcall(op, IntrinsicKind.INT_CONVERT,
                carrierArgs + "[1]", "        ");
            out.append("      else\n");
            emitIntrinsicLadderPcall(op, IntrinsicKind.NUMBER_CONVERT,
                carrierArgs + "[1]", "        ");
            out.append("      end\n");
            out.append("      if not __okA then error(__resA, 0) end\n");
            out.append("      return __resA\n");
            out.append("    end), ")
                .append(carrierArgs).append(")\n");
            }
            out.append("  elseif __dynClass(__dynS) ~= \"DEAL_BODY\" then\n");
            out.append("    __dynC = __dynS\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  else\n");
            out.append("  __dynM = __fnModules[__dynS.__fid]\n");
            out.append("  if __dynM == nil then\n");
            out.append("    __dynC = __dynS\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  end\n");
            out.append("  __asyncStartTask(").append(token.tokenId())
                .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
            out.append("    __modStack[#__modStack + 1] = __module\n");
            out.append("    __module = __dynM\n");
            out.append("    table.insert(__frames, 1, tostring(__dynS.__fid))\n");
            out.append("    local __okA, __resA = pcall(__unfn(__dynS), unpack(")
                .append(carrierArgs).append(", 1, __dynC.__m))\n");
            out.append("    table.remove(__frames, 1)\n");
            out.append("    __module = __modStack[#__modStack]\n");
            out.append("    __modStack[#__modStack] = nil\n");
            out.append("    if not __okA then error(__resA, 0) end\n");
            if (callOwnedTaskCell) {
                emitRecordedCellRun(op, recordedTaskCell, "__resA", "    ");
            }
            out.append("    return __resA\n");
            out.append("  end), ").append(carrierArgs).append(")\n");
            out.append("  end\n");
            // HOST: the carrier is a loaded host surface entry, so the
            // declared host export's async start runs through the same host
            // calling convention and the same ASYNC_OPERATION_HANDLE terminal
            // as the static arm — the loaded wrapper's declared-async shape
            // check inside the pcall, the operation handle bound to this
            // token under the declared identity's operation label (the
            // oracle's dynamic HOST resolution: the loaded declared async
            // export, the responder's startAsync under the same label). The
            // declared identity is the carrier's own identity-indexed home in
            // the program's export-surface registry; a carrier with no unique
            // home identifies no loaded surface entry and fails closed.
            out.append("elseif __dynK == \"HOST\" then\n");
            out.append("  __dynHN = __surfaceNameOf(__dynC)\n");
            out.append("  if __dynHN == nil then\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("  end\n");
            out.append("  __dynLbl = __dynHN[1]..\".\"..__dynHN[2]\n");
            if (trace) {
                out.append("  io.stderr:write(\"F|ASYNC_START_OP|-|\"..__esc(__dynLbl)"
                    + "..\"\\n\")\n");
                out.append("  io.stderr:flush()\n");
            }
            out.append("  __okH, __resH = pcall(__dynC.f");
            for (int i = 1; i <= recordedArgCount(payload, op); i++) {
                out.append(", ").append(carrierArgs).append("[").append(i).append("]");
            }
            out.append(", ").append(spanTripletArgs(op)).append(")\n");
            out.append("  if not __okH then\n");
            out.append("    __resH = __hostError(__resH, ").append(origin).append(")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resH)");
            out.append("    error(__resH, 0)\n");
            out.append("  end\n");
            out.append("  __asyncStartHost(").append(token.tokenId())
                .append(", __dynLbl, __resH)\n");
            // The fail-closed residue: no class is resolvable.
            out.append("else\n");
            emitDynamicCarrierFailure(op, origin);
            out.append("end\n");
        }

        /**
         * The completed argument count of one {@code ASYNC_START} payload: the
         * parameter boundaries under {@code RUN}, the raw operands under
         * {@code ELIDED_BY_ADAPTER} (the carrier table holds exactly them).
         */
        private static int recordedArgCount(KindPayload.AsyncStartPayload payload,
                                            SemanticOp op) {
            return payload.parameterBoundaryMode() == ParameterBoundaryMode.RUN
                ? payload.parameterBoundaryOpIds().size() : op.operands().size();
        }

        /** Whether one declared host position is a function type. */
        private boolean isFunctionPosition(RuntimeDescriptor descriptor) {
            RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                ? nullable.inner() : descriptor;
            return inner instanceof RuntimeDescriptor.Func;
        }

        /** The canonical descriptor text of one declared position's inner type. */
        private String innerFunctionText(RuntimeDescriptor descriptor) {
            RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                ? nullable.inner() : descriptor;
            return inner.canonicalSpecText();
        }

        /** The inner-type argument of the projection helper (nil for other positions). */
        private String sourceTextOf(RuntimeDescriptor descriptor) {
            return isFunctionPosition(descriptor)
                ? luaString(innerFunctionText(descriptor)) : "nil";
        }

        /** The literal span-triplet arguments of one host call site. */
        private String spanTripletArgs(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                return "\"-\", 0, 0";
            }
            return luaString(op.origin().sourceId()) + ", " + span.startLine() + ", "
                + span.startColumn();
        }

        private void emitIntrinsic(SemanticOp op) {
            KindPayload.IntrinsicCallPayload payload =
                (KindPayload.IntrinsicCallPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            String input = slot(payload.input());
            String kind = staticKind(op.operandTypes().get(0));
            String origin = originOf(op);
            // The direct arm keeps its own kind as the invoking op's label
            // (ISSUE-0679 J4); an intrinsic value call passes the invoking
            // CALL op's kind through the same ladder.
            switch (payload.kind()) {
                case INT_CONVERT -> out.append(target).append(" = __intConv(")
                    .append(input).append(", ").append(luaString(op.kind().name()))
                    .append(", ").append(luaString(kind)).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(origin)).append(")\n");
                case NUMBER_CONVERT -> out.append(target).append(" = __numConv(")
                    .append(input).append(", ").append(luaString(op.kind().name()))
                    .append(", ").append(luaString(kind)).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(origin)).append(")\n");
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        private void emitStdlib(SemanticOp op) {
            KindPayload.StdlibCallPayload payload =
                (KindPayload.StdlibCallPayload) op.payload();
            // The custom START: the operand atoms render the actual value
            // kind (the oracle's atomOf — a dynamic argument at a declared
            // boundary atomizes as its own kind), never the declared kind.
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"START\", \"STDLIB_CALL\", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId()))).append(", {");
            for (int i = 0; i < payload.args().size(); i++) {
                if (i > 0) {
                    out.append(", ");
                }
                out.append("__rawArgAtom(")
                    .append(luaString(staticKind(op.operandTypes().get(i))))
                    .append(", ").append(slot(payload.args().get(i))).append(")");
            }
            out.append("}, nil, nil)\n");
            // The closed STDLIB_PARAMETER boundaries in one-based declared
            // order: a failing boundary publishes the boundary FAILURE and
            // the op FAILURE events with the boundary origin, then rethrows
            // (the exact oracle event sequence — never a silent terminal).
            List<SemanticOp> paramBoundaries = stdlibParamBoundaries(op);
            for (SemanticOp boundary : paramBoundaries) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                // Custom boundary START: the input atom renders the actual
                // value kind (the oracle's atomOf).
                out.append("__ev(").append(luaString(opKey(boundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(luaString(boundary.contract().canonicalDigest()))
                    .append(", ")
                    .append(luaString(parentKey(boundary.origin().parentOpId())))
                    .append(", {__rawArgAtom(")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(slot(boundaryPayload.input()))
                    .append(")}, nil, nil)\n");
                out.append("__okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(slot(boundaryPayload.input())).append(")\n");
                out.append("if not __okB then\n");
                out.append("  __chkB.o = ").append(luaString(originOf(boundary)))
                    .append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                emitBoundarySuccess(boundary, "__chkB", boundaryPayload.descriptor());
            }
            SemanticOp returnBoundary = stdlibReturnBoundary(op);
            String target = slot((ValueId) op.result());
            if (payload.function() == deal.semantic.ir.StdlibFunctionId.CONSOLE_LOG
                    || payload.function() == deal.semantic.ir.StdlibFunctionId.CONSOLE_ERROR) {
                // The direct arm runs the same row invoker the cataloged
                // callable does (M4): the console rows' single-effect
                // write is one realization, never a second statement-level
                // copy — the result is the row invoker's null and the
                // effect is exactly one write on the row's channel with
                // the direct arm's text projection.
                out.append(target).append(" = __stdlibInvoke(")
                    .append(luaString(op.kind().name())).append(", ")
                    .append(luaString(payload.function().name())).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op)));
                for (ValueId arg : payload.args()) {
                    out.append(", ").append(slot(arg));
                }
                out.append(")\n");
            } else {
                // The in-target stdlib algorithm over the
                // boundary-admitted carriers, through the same row invoker
                // the cataloged callable runs (M4): an algorithm failure
                // publishes the op FAILURE event and raises the exact
                // closed projection at the call origin (the __stdlib
                // helper converts it through the fail-closed pattern).
                out.append(target).append(" = __stdlibInvoke(")
                    .append(luaString(op.kind().name())).append(", ")
                    .append(luaString(payload.function().name())).append(", ")
                    .append(luaString(opKey(op.opId()))).append(", ")
                    .append(luaString(op.contract().canonicalDigest())).append(", ")
                    .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(luaString(originOf(op)));
                for (ValueId arg : payload.args()) {
                    out.append(", ").append(slot(arg));
                }
                out.append(")\n");
            }
            if (returnBoundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                // Custom boundary START: the result atom renders the
                // actual value kind (the oracle's atomOf).
                out.append("__ev(").append(luaString(opKey(returnBoundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(luaString(returnBoundary.contract().canonicalDigest()))
                    .append(", ")
                    .append(luaString(parentKey(returnBoundary.origin().parentOpId())))
                    .append(", {__rawArgAtom(")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target)
                    .append(")}, nil, nil)\n");
                out.append("__okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(")\n");
                out.append("if not __okB then\n");
                out.append("  __chkB.o = ").append(luaString(originOf(returnBoundary)))
                    .append("\n");
                emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                out.append(target).append(" = __chkB\n");
                emitBoundarySuccess(returnBoundary, target, boundaryPayload.descriptor());
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * CLASS_NEW (E5, D16 construction order): provided values
         * completed before the op; default application in declaration
         * order (LOCAL through the detached class-default functions, or
         * the owner's CLASS_FACTORY transfer with the factory's events
         * parented to this caller op — the cross-unit K-D12 parent);
         * extra-key rejection first in provided-source order (E8007 at
         * the op origin); provided-field application and field
         * validation in declaration order through the boundary
         * children; the instance is tagged with its canonical class
         * identity last. Zero return boundaries; a failure publishes no
         * partial instance.
         *
         * <p>The declaration-class owners replace the tail with their own
         * construction entry: {@code BUILTIN_DEFAULTS} publishes the
         * canonical Error carrier, {@code HOST_DEFAULTS} runs the
         * deployed {@code __rt.class_} over the loaded
         * {@code <C>_defaults} entry, and {@code FFI_PLAN} (ISSUE-0666)
         * runs the runtime's four phases over the loaded
         * {@code <C>_plan} entry — see
         * {@link #emitClassNewFfiPlan}.</p>
         */
        private void emitClassNew(SemanticOp op) {
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) op.payload();
            emitStart(op);
            ClassLayout layout = classLayouts.get(payload.classId());
            if (layout == null && payload.defaultOwner() == DefaultOwner.BUILTIN_DEFAULTS) {
                // The compiler-owned builtin Error layout (ISSUE-0619; K13
                // item 1): the builtin class resolves through the same
                // compiler constant every consumer resolves — the layout is
                // a resolution-only entry (the class is excluded from the
                // generated class carriers and the JSON plans).
                layout = ClassLayout.BUILTIN_ERROR;
            }
            if (layout == null && payload.defaultOwner() == DefaultOwner.HOST_DEFAULTS) {
                // The host declaration class's registered layout (ISSUE-0624;
                // K10): the payload carries exactly the project lowering's
                // registration-seed layout (the validator checks the
                // equality against the seeds), and the declaration layouts
                // are never merged into a unit's own classLayouts.
                layout = payload.layout();
            }
            if (layout == null && payload.defaultOwner() == DefaultOwner.FFI_PLAN) {
                // The extern-C declaration class's registered C-struct
                // layout (ISSUE-0666; struct-plan F1/F2): the payload carries
                // exactly the project lowering's registration-seed layout of
                // the validated plan's ordered fields (the validator checks
                // the equality against the seeds), and the declaration
                // layouts are never merged into a unit's own classLayouts.
                layout = payload.layout();
            }
            if (layout == null) {
                throw new IllegalStateException("CLASS_NEW " + op.opId() + " classId "
                    + payload.classId() + " has no layout in the resolution context "
                    + "(producer defect)");
            }
            java.util.Set<String> provided = new java.util.HashSet<>();
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                provided.add(field.name());
            }
            switch (payload.defaultOwner()) {
                case LOCAL -> emitClassNewLocalDefaults(op, payload, provided);
                case SHARED_FACTORY -> emitClassNewFactoryTransfer(op, payload, provided);
                case HOST_DEFAULTS -> {
                    // The host declaration class construction (ISSUE-0624;
                    // K10 and the K10 contract): dispatched after the
                    // static extra-key scan below — the shape carries no
                    // default children and no factory transfer, and its
                    // phases run through the loaded <C>_defaults entry.
                }
                case FFI_PLAN -> {
                    // The extern-C C-struct construction (ISSUE-0666;
                    // struct-plan F1 and the construction contract): the
                    // provided fields' boundary children run first, then
                    // the deterministic extra-key guard, then the runtime
                    // entry over the loaded <C>_plan entry — the fixed
                    // order of the decision, so the guard's E8007 is the
                    // deterministic authority over the runtime's order-free
                    // phase-1 pairs() iteration and no default runs before
                    // it.
                    emitClassNewFfiPlan(op, payload, layout);
                    return;
                }
                case BUILTIN_DEFAULTS -> {
                    // The builtin Error construction (K13 items 2-4): the
                    // builtin defaults are compiler constants, so no default
                    // child runs — provided fields only, and the omitted
                    // fields take the constant empty string at the
                    // construction site.
                }
                default -> throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner " + payload.defaultOwner()
                    + " outside the emitted owners (producer defect)");
            }
            // K-D4 step 3: extra-key rejection first in provided-source
            // order — after default application, before any provided-field
            // application or field validation.
            emitExtraKeyRejection(op, payload, layout);
            if (payload.defaultOwner() == DefaultOwner.BUILTIN_DEFAULTS) {
                emitClassNewBuiltinDefaults(op, payload, layout);
                return;
            }
            if (payload.defaultOwner() == DefaultOwner.HOST_DEFAULTS) {
                emitClassNewHostDefaults(op, payload, layout);
                return;
            }
            // K-D4 steps 4-5: instance building plus field validation in
            // declaration order; the tag and the publication come last
            // (step 6).
            out.append("__instT = {}\n");
            out.append("__instT.__f = {}\n");
            out.append("__instT.__p = {}\n");
            for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
                SemanticOp boundary = opsById.get(entry.boundaryOpId());
                if (boundary == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " field boundary " + entry.boundaryOpId() + " does not "
                        + "resolve (producer defect)");
                }
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String inputExpr;
                if (entry.kind() == BoundaryKind.CLASS_DEFAULT_FIELD
                        && payload.defaultOwner() == DefaultOwner.SHARED_FACTORY) {
                    // The K-D4 extraction rule: the checked value is the
                    // transferred instance's named field.
                    SemanticOp factoryOp = opsById.get(factoryOpIdOf(op, payload));
                    inputExpr = "__fT";
                    out.append("__fT = __member(")
                        .append(slot((ValueId) factoryOp.result())).append(", ")
                        .append(luaString(entry.field())).append(")\n");
                } else {
                    inputExpr = slot(boundaryPayload.input());
                }
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor());
                out.append("__okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(")\n");
                out.append("if not __okB then\n");
                out.append("  __chkB.o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("  error(__chkB, 0)\n");
                out.append("end\n");
                emitBoundarySuccess(boundary, "__chkB", boundaryPayload.descriptor());
                out.append("__instT.__f[").append(luaString(entry.field()))
                    .append("] = (__chkB == nil) and __NULL or __chkB\n");
                out.append("__instT.__p[").append(luaString(entry.field()))
                    .append("] = true\n");
            }
            // K-D4 step 6: the tag, then the publication.
            out.append("__instT.__c = true\n");
            out.append("__instT.__id = ")
                .append(luaString(payload.classId().text())).append("\n");
            out.append(slot((ValueId) op.result())).append(" = __instT\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        /**
         * K-D4 step 3: the extra-key rejection in provided-source order —
         * a provided name absent from the layout raises E8007 {@code extra
         * field '<field>' in class '<identity>'} at the op's own origin,
         * before any provided-field application or field validation runs,
         * and names the first offending name in provided-source order. The
         * FFI construction runs the same guard after its provided-field
         * boundary children (struct-plan F1's fixed order).
         */
        private void emitExtraKeyRejection(SemanticOp op,
                KindPayload.ClassNewPayload payload, ClassLayout layout) {
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                if (fieldOf(layout, field.name()) == null) {
                    out.append("__eT = __failExpr(")
                        .append(luaString("E8007")).append(", ")
                        .append(luaString("extra field '" + field.name()
                            + "' in class '" + payload.classId().text() + "'"))
                        .append(", ").append(luaString(originOf(op)))
                        .append(", nil, nil)\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "__errtext(__eT)");
                    out.append("error(__eT, 0)\n");
                }
            }
        }

        /**
         * The builtin {@code Error} construction (ISSUE-0619;
         * {@code semantic-ir-construct-coverage-cutover} K13 items 3/4):
         * the provided fields run their pinned
         * {@code CLASS_LITERAL_FIELD} boundary children in payload order
         * (the descriptor-kind rule, the field's declared {@code string}
         * descriptor), the omitted fields take the compiler constant empty
         * string, and the publication is the canonical err carrier
         * {@code {__d = true, code = &lt;code&gt;, m = &lt;message&gt;}} —
         * the same carrier {@code THROW}, the async failure path,
         * {@code __bcheck("@/Error")}, and {@code __actualOf} already
         * speak. No default child, no factory transfer, and no extra-key
         * projection (the checker's E4002 rejects an extra literal field
         * before lowering).
         */
        private void emitClassNewBuiltinDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, ClassLayout layout) {
            if (!ClassId.ERROR.equals(payload.classId())
                    || !layout.equals(ClassLayout.BUILTIN_ERROR)) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner BUILTIN_DEFAULTS for " + payload.classId()
                    + " over " + layout.classId() + ": the builtin-defaults owner is"
                    + " admissible only for the compiler-owned builtin Error class"
                    + " (producer defect)");
            }
            java.util.Map<String, String> values = new java.util.LinkedHashMap<>();
            for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
                SemanticOp boundary = opsById.get(entry.boundaryOpId());
                if (boundary == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " field boundary " + entry.boundaryOpId() + " does not "
                        + "resolve (producer defect)");
                }
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String inputExpr = slot(boundaryPayload.input());
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor());
                String checked = "__ecT" + boundary.opId().id();
                out.append("__okB, ").append(checked).append(" = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(")\n");
                out.append("if not __okB then\n");
                out.append("  ").append(checked).append(".o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(" + checked + ")");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(" + checked + ")");
                out.append("  error(").append(checked).append(", 0)\n");
                out.append("end\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor());
                values.put(entry.field(), checked);
            }
            String target = slot((ValueId) op.result());
            String code = values.get("code");
            String message = values.get("message");
            out.append("__instT = {__d = true, code = ")
                .append(code == null ? luaString("") : code)
                .append(", m = ")
                .append(message == null ? luaString("") : message).append("}\n");
            out.append(target).append(" = __instT\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The host declaration class construction (ISSUE-0624;
         * {@code semantic-ir-construct-coverage-cutover} K10 and the K10
         * contract): the provided values evaluate in literal order by the
         * caller (already completed operands), the construction runs
         * through the deployed runtime's {@code __rt.class_} over the
         * declaring module's loaded {@code <C>_defaults} entry — the
         * per-attempt deep copy with the sentinel identities preserved, the
         * provided overlay with the extra provided name raising E8007 at the
         * literal origin before any field validation, the
         * {@code __MISSING} removal of the omitted optionals, and the
         * canonical identity tag — then the pinned
         * {@code CLASS_LITERAL_FIELD} boundary children run in declaration
         * order and the admitted values are written back into the instance
         * (the language null as the deployed runtime's own sentinel, so the
         * host side observes the retained convention and the emitted field
         * ops read present null as null). The instance carries the shared
         * carrier markers ({@code __c}/{@code __id}) so every boundary and
         * field-op byte-exact identity check applies unchanged. A failed
         * construction publishes no instance.
         */
        private void emitClassNewHostDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, ClassLayout layout) {
            if (!isHostClass(payload.classId())) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner HOST_DEFAULTS for " + payload.classId()
                    + ", which is not a declared host class of the compile's"
                    + " declaration surface (the class defaults entry has exactly"
                    + " one source — a producer defect)");
            }
            if (payload.classFactoryRef() != null
                    || !payload.classDefaultOpIds().isEmpty()) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner HOST_DEFAULTS with a non-null factory"
                    + " ref or a non-empty default child list: the host construction"
                    + " carries neither (the loaded defaults are data — a producer"
                    + " defect)");
            }
            // (1) The provided values in literal order, normalized to the
            // deployed runtime's own language-null sentinel.
            out.append("__provT = {}\n");
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                out.append("__pvT = ").append(slot(field.valueOpId())).append("\n");
                out.append("if __pvT == nil or __pvT == __NULL then __pvT = "
                    + "__rt.__NULL end\n");
                out.append("__provT[").append(luaString(field.name()))
                    .append("] = __pvT\n");
            }
            // (2)-(4) The deep copy, the provided overlay with the extra-key
            // rejection, the sentinel removal, and the tag: the deployed
            // construction entry (the one authority the retained route and
            // the shared route share).
            out.append("__okB, __instT = pcall(__rt.class_, ")
                .append(luaString(payload.classId().text())).append(", ")
                .append(hostDefaultsExpr(payload.classId())).append(", __provT, ")
                .append(classLiteralOriginArgs(op)).append(")\n");
            out.append("if not __okB then\n");
            out.append("  __eT = __hostError(__instT, ")
                .append(luaString(originOf(op))).append(")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__eT)");
            out.append("  error(__eT, 0)\n");
            out.append("end\n");
            out.append("__instT.__c = true\n");
            out.append("__instT.__id = ")
                .append(luaString(payload.classId().text())).append("\n");
            // (5) The CLASS_LITERAL_FIELD boundary children in declaration
            // order; the admitted value replaces the overlaid one (the
            // language null renormalizes to the runtime sentinel, so a
            // present null stays present for the host side and the
            // presence-aware reads).
            for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
                SemanticOp boundary = opsById.get(entry.boundaryOpId());
                if (boundary == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " field boundary " + entry.boundaryOpId() + " does not "
                        + "resolve (producer defect)");
                }
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String inputExpr = slot(boundaryPayload.input());
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor());
                String checked = "__hccT" + boundary.opId().id();
                out.append("__okB, ").append(checked).append(" = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(")\n");
                out.append("if not __okB then\n");
                out.append("  ").append(checked).append(".o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(" + checked + ")");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(" + checked + ")");
                out.append("  error(").append(checked).append(", 0)\n");
                out.append("end\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor());
                out.append("__instT[").append(luaString(entry.field()))
                    .append("] = (").append(checked)
                    .append(" == nil) and __rt.__NULL or ").append(checked)
                    .append("\n");
            }
            String target = slot((ValueId) op.result());
            out.append(target).append(" = __instT\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The extern-C C-struct class construction (ISSUE-0666;
         * {@code luajit-ffi-struct-plan-construction-and-oracle-projection}
         * F1 and the C-struct construction contract; the loaded plan is the
         * single default authority): the fixed order
         *
         * <ol>
         *   <li>the provided fields in declaration order — each
         *       {@code CLASS_LITERAL_FIELD} boundary child runs its
         *       descriptor-kind check and the checked value is written into
         *       the provided table under the field name; a class-typed
         *       field value is projected to the runtime representation first
         *       (the load/crossing page F4's chunk-to-wrapper direction, the
         *       same helper the call-site cells use);</li>
         *   <li>the deterministic extra-key guard in provided-source order —
         *       E8007 at the literal origin before any default runs, naming
         *       the first extra name, because the runtime entry's phase-1
         *       {@code pairs()} iteration is order-free and the artifact's
         *       guard is the deterministic authority;</li>
         *   <li>{@code __rt.class_plan_(<identity text>, <loaded plan entry>,
         *       <provided table>, <literal span triplet>)} — the runtime's
         *       four phases over the loaded {@code <C>_plan} entry: the
         *       provided copy, the omitted fields' deferred evaluators
         *       exactly once per attempt in class source order, the
         *       per-field descriptor validation (E8001/E8004) at the literal
         *       origin, and the identity tag and publication;</li>
         *   <li>the wrapper-to-chunk projection of the constructed instance
         *       into the op's slot (the same F4 helper pair), then the
         *       op's SUCCESS terminal.</li>
         * </ol>
         *
         * <p>No {@code CLASS_DEFAULT} child, no in-project factory, and no
         * default expression are emitted: the plan's generated evaluators
         * are the only default authority and they run inside the runtime
         * entry. A failed construction publishes no instance — including
         * the boundary children's own failures, which raise before the entry
         * call and before the slot write.</p>
         */
        private void emitClassNewFfiPlan(SemanticOp op,
                KindPayload.ClassNewPayload payload, ClassLayout layout) {
            if (ffiClassModules.get(payload.classId()) == null) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner FFI_PLAN for " + payload.classId()
                    + ", which is not a declared extern-C class of the compile's"
                    + " declaration surface (the class plan entry has exactly one"
                    + " source — a producer defect)");
            }
            if (payload.classFactoryRef() != null
                    || !payload.classDefaultOpIds().isEmpty()) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner FFI_PLAN with a non-null factory"
                    + " ref or a non-empty default child list: the C-struct"
                    + " construction carries neither (the loaded plan's"
                    + " evaluators are the single default authority — a"
                    + " producer defect)");
            }
            // (1) The provided fields in declaration order: the boundary
            // child's descriptor-kind check over the provided value's
            // completed slot, then the admitted value into the provided
            // table (a class-typed position projects to the runtime
            // representation the loaded matcher validates).
            out.append("__provT = {}\n");
            for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
                SemanticOp boundary = opsById.get(entry.boundaryOpId());
                if (boundary == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " field boundary " + entry.boundaryOpId() + " does not "
                        + "resolve (producer defect)");
                }
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String inputExpr = slot(boundaryPayload.input());
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor());
                String checked = "__fpcT" + boundary.opId().id();
                out.append("__okB, ").append(checked).append(" = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(")\n");
                out.append("if not __okB then\n");
                out.append("  ").append(checked).append(".o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(" + checked + ")");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(" + checked + ")");
                out.append("  error(").append(checked).append(", 0)\n");
                out.append("end\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor());
                out.append("__provT[").append(luaString(entry.field()))
                    .append("] = ")
                    .append(ffiClassFieldProjection(boundaryPayload.descriptor(),
                        checked))
                    .append("\n");
            }
            // (2) The deterministic extra-key guard.
            emitExtraKeyRejection(op, payload, layout);
            // (3) The runtime's four phases over the loaded plan entry.
            out.append("__okB, __instT = pcall(__rt.class_plan_, ")
                .append(luaString(payload.classId().text())).append(", ")
                .append(ffiPlanExpr(payload.classId())).append(", __provT, ")
                .append(classLiteralOriginArgs(op)).append(")\n");
            out.append("if not __okB then\n");
            out.append("  __eT = __hostError(__instT, ")
                .append(luaString(originOf(op))).append(")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__eT)");
            out.append("  error(__eT, 0)\n");
            out.append("end\n");
            // (4) The wrapper-to-chunk projection of the constructed
            // instance, then the publication.
            String target = slot((ValueId) op.result());
            out.append(target).append(" = __hostDealProject(")
                .append(luaString(payload.classId().text())).append(", __instT, ")
                .append(luaString(originOf(op))).append(")\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * The provided-table expression of one C-struct field: a
         * class-typed position (the declared descriptor is a class
         * identity) is projected from the chunk representation to the
         * runtime representation the loaded plan's phase-3 matcher
         * validates (the load/crossing page F4's {@code __hostClassProject})
         * and every other position passes its checked value unchanged.
         */
        private String ffiClassFieldProjection(RuntimeDescriptor descriptor,
                String checked) {
            if (descriptor instanceof RuntimeDescriptor.Class) {
                return "__hostClassProject(" + luaString(descriptorText(descriptor))
                    + ", " + checked + ")";
            }
            return checked;
        }

        /**
         * K-D4 step 2, LOCAL: the default children run in declaration
         * order through their detached class-default functions, skipping
         * any child whose field is provided (a provided field's default
         * never runs); each child emits its own START and terminal.
         */
        private void emitClassNewLocalDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, java.util.Set<String> provided) {
            for (OpId defaultOpId : payload.classDefaultOpIds()) {
                SemanticOp defaultOp = opsById.get(defaultOpId);
                if (defaultOp == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " CLASS_DEFAULT child " + defaultOpId + " does not resolve "
                        + "(producer defect)");
                }
                KindPayload.ClassDefaultPayload defaultPayload =
                    (KindPayload.ClassDefaultPayload) defaultOp.payload();
                if (provided.contains(defaultPayload.field())) {
                    continue; // the skip-provided rule
                }
                emitClassDefaultCall(op, defaultOp);
            }
        }

        /** One CLASS_DEFAULT child execution (START, function, terminal). */
        private void emitClassDefaultCall(SemanticOp op, SemanticOp defaultOp) {
            out.append("__ev(").append(luaString(opKey(defaultOp.opId())))
                .append(", \"START\", \"CLASS_DEFAULT\", ")
                .append(luaString(defaultOp.contract().canonicalDigest()))
                .append(", \"-\", {}, nil, nil)\n");
            out.append("__okT, __resT = pcall(")
                .append(defaultFn(defaultOp.opId())).append(")\n");
            out.append("if not __okT then\n");
            emitFailureEvent(defaultOp.opId(), "CLASS_DEFAULT", defaultOp,
                "__errtext(__resT)");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            if (defaultOp.result() instanceof ValueId resultId) {
                out.append(slot(resultId)).append(" = __resT\n");
            }
            out.append("__ev(").append(luaString(opKey(defaultOp.opId())))
                .append(", \"SUCCESS\", \"CLASS_DEFAULT\", ")
                .append(luaString(defaultOp.contract().canonicalDigest()))
                .append(", \"-\", {}, __atom(")
                .append(luaString(staticKind((RuntimeDescriptor) defaultOp.resultType())))
                .append(", __resT), nil)\n");
        }

        /**
         * The registered owner factory op of a SHARED_FACTORY CLASS_NEW,
         * resolved through the delivered per-module class-factory
         * registries (the one fact channel shared with the oracle and the
         * JVM session): the owner module is the module whose registry
         * binds the construction entry, never the class descriptor
         * namespace.
         */
        private OpId factoryOpIdOf(SemanticOp op, KindPayload.ClassNewPayload payload) {
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
         * The nesting-safe module save of a factory transfer: one stack
         * push; the stack order is the transfer nesting order.
         */
        private void emitModulePush() {
            out.append("__modStack[#__modStack + 1] = __module\n");
        }

        /**
         * The matching restore: the transfer's own saved module, never an
         * enclosing transfer's (the nesting-safe pop).
         */
        private void emitModulePop() {
            out.append("__module = __modStack[#__modStack]\n");
            out.append("__modStack[#__modStack] = nil\n");
        }

        /**
         * K-D4 step 2, SHARED_FACTORY: the transfer to the owner's
         * CLASS_FACTORY entry — the factory's events parent to this
         * caller op (cross-unit) and carry the owner's module path; its
         * CLASS_DEFAULT children evaluate in the declaring module's
         * scope (skipping provided fields) and fill the untagged
         * internal transfer instance, which the factory publishes as its
         * result for the caller's CLASS_DEFAULT_FIELD extraction. The
         * module switch is one stack push/pop pair (a nested transfer
         * inside an owner default restores its own saved module; the
         * caller's own terminals are emitted after the pop, so every
         * event carries its op's module).
         */
        private void emitClassNewFactoryTransfer(SemanticOp op,
                KindPayload.ClassNewPayload payload, java.util.Set<String> provided) {
            OpId factoryOpId = factoryOpIdOf(op, payload);
            SemanticOp factoryOp = opsById.get(factoryOpId);
            if (factoryOp == null || factoryOp.kind() != SemanticOpKind.CLASS_FACTORY) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " resolves factory op " + factoryOpId + " outside the pinned "
                    + "kind (producer defect)");
            }
            KindPayload.ClassFactoryPayload factoryPayload =
                (KindPayload.ClassFactoryPayload) factoryOp.payload();
            if (!factoryPayload.classId().equals(payload.classId())) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " resolves a factory of " + factoryPayload.classId()
                    + " (producer defect)");
            }
            if (!(factoryOp.result() instanceof ValueId factoryResult)) {
                throw new IllegalStateException("CLASS_FACTORY " + factoryOp.opId()
                    + " publishes no ValueId result (producer defect)");
            }
            String ownerPath = factoryOpId.module().path();
            emitModulePush();
            out.append("__module = ").append(luaString(ownerPath)).append("\n");
            out.append("__ev(").append(luaString(opKey(factoryOp.opId())))
                .append(", \"START\", \"CLASS_FACTORY\", ")
                .append(luaString(factoryOp.contract().canonicalDigest()))
                .append(", ").append(luaString(opKey(op.opId())))
                .append(", {}, nil, nil)\n");
            // The factory's default children in declaration order,
            // skipping any child whose field the caller provides.
            java.util.List<SemanticOp> filled = new ArrayList<>();
            for (OpId defaultOpId : factoryPayload.classDefaultOpIds()) {
                SemanticOp defaultOp = opsById.get(defaultOpId);
                if (defaultOp == null) {
                    throw new IllegalStateException("CLASS_FACTORY " + factoryOp.opId()
                        + " CLASS_DEFAULT child " + defaultOpId + " does not resolve "
                        + "(producer defect)");
                }
                KindPayload.ClassDefaultPayload defaultPayload =
                    (KindPayload.ClassDefaultPayload) defaultOp.payload();
                if (provided.contains(defaultPayload.field())) {
                    continue; // the skip-provided rule (K-D5)
                }
                out.append("__ev(").append(luaString(opKey(defaultOp.opId())))
                    .append(", \"START\", \"CLASS_DEFAULT\", ")
                    .append(luaString(defaultOp.contract().canonicalDigest()))
                    .append(", \"-\", {}, nil, nil)\n");
                out.append("__okT, __resT = pcall(")
                    .append(defaultFn(defaultOp.opId())).append(")\n");
                out.append("if not __okT then\n");
                emitFailureEvent(defaultOp.opId(), "CLASS_DEFAULT", defaultOp,
                    "__errtext(__resT)");
                out.append("__ev(").append(luaString(opKey(factoryOp.opId())))
                    .append(", \"FAILURE\", \"CLASS_FACTORY\", ")
                    .append(luaString(factoryOp.contract().canonicalDigest()))
                    .append(", ").append(luaString(opKey(op.opId())))
                    .append(", {}, nil, __errtext(__resT))\n");
                // Restore the caller's module before the caller's own
                // terminal: the owner-side terminals above carry the
                // owner's module, the caller's CLASS_NEW FAILURE carries
                // the caller's (the oracle's own tagging).
                emitModulePop();
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__resT)");
                out.append("  error(__resT, 0)\n");
                out.append("end\n");
                if (defaultOp.result() instanceof ValueId resultId) {
                    out.append(slot(resultId)).append(" = __resT\n");
                }
                out.append("__ev(").append(luaString(opKey(defaultOp.opId())))
                    .append(", \"SUCCESS\", \"CLASS_DEFAULT\", ")
                    .append(luaString(defaultOp.contract().canonicalDigest()))
                    .append(", \"-\", {}, __atom(")
                    .append(luaString(staticKind((RuntimeDescriptor) defaultOp.resultType())))
                    .append(", __resT), nil)\n");
                filled.add(defaultOp);
            }
            // The untagged internal transfer instance: the defaulted
            // fields present (present null via the __NULL sentinel),
            // every other field missing.
            out.append("__instT = {}\n");
            out.append("__instT.__f = {}\n");
            out.append("__instT.__p = {}\n");
            for (SemanticOp defaultOp : filled) {
                KindPayload.ClassDefaultPayload defaultPayload =
                    (KindPayload.ClassDefaultPayload) defaultOp.payload();
                out.append("__instT.__f[").append(luaString(defaultPayload.field()))
                    .append("] = (").append(slot((ValueId) defaultOp.result()))
                    .append(" == nil) and __NULL or ")
                    .append(slot((ValueId) defaultOp.result())).append("\n");
                out.append("__instT.__p[").append(luaString(defaultPayload.field()))
                    .append("] = true\n");
            }
            out.append("__instT.__c = true\n");
            out.append("__instT.__id = ")
                .append(luaString(payload.classId().text())).append("\n");
            out.append(slot(factoryResult)).append(" = __instT\n");
            out.append("__ev(").append(luaString(opKey(factoryOp.opId())))
                .append(", \"SUCCESS\", \"CLASS_FACTORY\", ")
                .append(luaString(factoryOp.contract().canonicalDigest()))
                .append(", ").append(luaString(opKey(op.opId())))
                .append(", {}, __atom(\"class\", __instT), nil)\n");
            emitModulePop();
        }

        /** The declared layout entry of one field name, or null. */
        private ClassLayout.FieldLayout fieldOf(ClassLayout layout, String name) {
            for (ClassLayout.FieldLayout field : layout.fields()) {
                if (field.name().equals(name)) {
                    return field;
                }
            }
            return null;
        }

        /** The STDLIB_PARAMETER children in one-based declared order. */
        private List<SemanticOp> stdlibParamBoundaries(SemanticOp op) {
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

        private SemanticOp stdlibReturnBoundary(SemanticOp op) {
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

        private void emitBranch(SemanticOp op) {
            KindPayload.BranchPayload payload = (KindPayload.BranchPayload) op.payload();
            emitStart(op);
            String condition = slot(payload.condition());
            switch (payload.selector()) {
                case IF -> {
                    String selected = label(payload.selectedBlock());
                    String after = label(payload.selectedBlock()) + "A";
                    if (payload.alternateBlock() != null) {
                        String alternate = label(payload.alternateBlock());
                        out.append("if ").append(condition).append(" then goto ")
                            .append(selected).append(" else goto ").append(alternate)
                            .append(" end\n");
                        emitLabeledBlock(payload.selectedBlock());
                        out.append("goto ").append(after).append("\n");
                        emitLabeledBlock(payload.alternateBlock());
                        out.append("::").append(after).append("::\n");
                    } else {
                        out.append("if ").append(condition).append(" then goto ")
                            .append(selected).append(" end\n");
                        out.append("goto ").append(after).append("\n");
                        emitLabeledBlock(payload.selectedBlock());
                        out.append("::").append(after).append("::\n");
                    }
                    emitPlainSuccess(op);
                }
                case LOGICAL_AND, LOGICAL_OR -> {
                    String selected = label(payload.selectedBlock());
                    String after = label(payload.selectedBlock()) + "A";
                    String target = slot((ValueId) op.result());
                    boolean isAnd = payload.selector()
                        == deal.semantic.ir.ControlSelector.LOGICAL_AND;
                    if (isAnd) {
                        // AND: the block runs when the left value is true.
                        out.append("if ").append(condition).append(" then goto ")
                            .append(selected).append(" end\n");
                    } else {
                        // OR: the block runs when the left value is false.
                        out.append("if not ").append(condition).append(" then goto ")
                            .append(selected).append(" end\n");
                    }
                    out.append(target).append(" = ").append(condition).append("\n");
                    out.append("goto ").append(after).append("\n");
                    emitLabeledBlock(payload.selectedBlock());
                    out.append("::").append(after).append("::\n");
                    emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
                }
                default -> throw new IllegalStateException("BRANCH selector "
                    + payload.selector());
            }
        }

        private void emitLoop(SemanticOp op) {
            KindPayload.LoopPayload payload = (KindPayload.LoopPayload) op.payload();
            emitStart(op);
            String exit = loopExit(op.opId());
            String cont = loopCont(op.opId());
            String condition = slot(payload.condition());
            switch (payload.selector()) {
                case WHILE -> {
                    out.append("::").append(cont).append("::\n");
                    emitLabeledBlock(payload.initBlock());
                    out.append("if not ").append(condition).append(" then goto ")
                        .append(exit).append(" end\n");
                    emitLabeledBlock(payload.bodyBlock());
                    out.append("goto ").append(cont).append("\n");
                    out.append("::").append(exit).append("::\n");
                }
                case FOR -> {
                    emitLabeledBlock(payload.initBlock());
                    out.append("::").append(cont).append("T::\n");
                    out.append("if not ").append(condition).append(" then goto ")
                        .append(exit).append(" end\n");
                    emitLabeledBlock(payload.bodyBlock());
                    out.append("::").append(cont).append("::\n");
                    if (payload.updateBlock() != null) {
                        emitLabeledBlock(payload.updateBlock());
                    }
                    out.append("goto ").append(cont).append("T\n");
                    out.append("::").append(exit).append("::\n");
                }
                default -> throw new IllegalStateException("LOOP selector "
                    + payload.selector());
            }
            emitPlainSuccess(op);
        }

        private void emitForEach(SemanticOp op) {
            KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) op.payload();
            emitStart(op);
            switch (payload.mode()) {
                case ARRAY_VALUES -> {
                    String iterable = slot(payload.iterable());
                    String cellName = cell(payload.binding(), payload.generation());
                    String cont = loopCont(op.opId());
                    out.append("do\n");
                    out.append("  __itT = ").append(iterable).append("\n");
                    out.append("  __itnT = __itT.__n\n");
                    out.append("  for __i = 0, __itnT - 1 do\n");
                    out.append("    __elemT = __MISSING\n");
                    out.append("    if __i < __itT.__n then\n");
                    // The element read is a typed position: the admitted
                    // int/number variant materializes exactly as at
                    // __arrayRead (the element's own slot mark and the
                    // iterable's declared element descriptor), so the
                    // loop cell carries the value's own variant.
                    out.append("      __elemT = __readVar(__itT, __i + 1, ")
                        .append("__itT[__i + 1], ")
                        .append(isNumberKind(staticKind(elementDescriptorOf(op)))
                            ? "true" : "false")
                        .append(")\n");
                    out.append("      if __elemT == __NULL then __elemT = nil\n");
                    out.append("      elseif __elemT == nil then __elemT = __MISSING end\n");
                    out.append("    end\n");
                    out.append("    __foreachCheck(")
                        .append(luaString(opKey(op.opId()))).append(", ")
                        .append(luaString(op.contract().canonicalDigest())).append(", ")
                        .append(luaString(parentKey(op.origin().parentOpId()))).append(", ")
                        .append(luaString(descriptorText(elementDescriptorOf(op))))
                        .append(", __elemT, ").append(luaString(originOf(op))).append(")\n");
                    out.append("    ").append(cellName).append(" = __elemT\n");
                    emitLabeledBlock(payload.body());
                    out.append("    ::").append(cont).append("::\n");
                    out.append("  end\n");
                    out.append("end\n");
                }
                case STRING_SCALARS -> {
                    String iterable = slot(payload.iterable());
                    String cellName = cell(payload.binding(), payload.generation());
                    String cont = loopCont(op.opId());
                    out.append("do\n");
                    out.append("  __itT = ").append(iterable).append("\n");
                    out.append("  for __i = 1, #__itT do\n");
                    out.append("    ").append(cellName)
                        .append(" = __u8sub(__itT, __i, __i)\n");
                    emitLabeledBlock(payload.body());
                    out.append("    ::").append(cont).append("::\n");
                    out.append("  end\n");
                    out.append("end\n");
                }
            }
            emitPlainSuccess(op);
        }

        private RuntimeDescriptor elementDescriptorOf(SemanticOp op) {
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

        private void emitTryCatch(SemanticOp op) {
            KindPayload.TryCatchPayload payload = (KindPayload.TryCatchPayload) op.payload();
            emitStart(op);
            String cellName = cell(payload.catchBinding(), 0);
            tryDepth++;
            out.append("__okT, __resT = pcall(function()\n");
            emitBlockOps(payload.tryBlock());
            out.append("end)\n");
            tryDepth--;
            out.append("if not __okT then\n");
            emitTransferDispatch(op, payload.tryBlock(), "  ", "__resT");
            out.append("  if type(__resT) == \"table\" and __resT.__d then\n");
            // The caught value is the canonical Error value itself (ISSUE-0619;
            // K13 item 6): the distinct caught-marker carrier is retired, so
            // the caught binding crosses an @/Error boundary and reads its
            // fields exactly like any other builtin Error value.
            out.append("    ").append(cellName).append(" = __resT\n");
            tryDepth++;
            out.append("    __okT, __terrT = pcall(function()\n");
            emitBlockOps(payload.catchBlock());
            out.append("    end)\n");
            tryDepth--;
            out.append("    if not __okT then\n");
            // The catch block's own pcall result is __terrT (ISSUE-0619: a
            // RETURN/ BREAK/CONTINUE inside the catch block signals through
            // that pcall, so its transfer dispatch reads __terrT — reading
            // the try block's __resT would wrap the transfer signal into a
            // code-less carrier).
            emitTransferDispatch(op, payload.catchBlock(), "      ", "__terrT");
            out.append("      __wrappedT = {__d = true, code = __terrT.code, "
                + "m = __terrT.m, o = __terrT.o, e = __terrT.e, a = __terrT.a, "
                + "f = __terrT.f, cause = __resT}\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__wrappedT)");
            out.append("      error(__wrappedT, 0)\n");
            out.append("    end\n");
            out.append("  else\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("    error(__resT, 0)\n");
            out.append("  end\n");
            out.append("end\n");
            emitPlainSuccess(op);
        }

        /**
         * The transfer dispatch after a pcall-wrapped block: the block's
         * BREAK/CONTINUE/RETURN ops (recursively) signalled through the
         * pcall boundary re-apply their static transfers here. The
         * {@code errorVar} names the pcall result the dispatch reads —
         * {@code __resT} for the try block, {@code __terrT} for the catch
         * block (its own pcall).
         */
        private void emitTransferDispatch(SemanticOp tryOp, BlockId block, String pad,
                                          String errorVar) {
            List<SemanticOp> transfers = new ArrayList<>();
            collectTransfers(block, transfers);
            if (transfers.isEmpty()) {
                return;
            }
            out.append(pad).append("if type(").append(errorVar)
                .append(") == \"table\" and ").append(errorVar).append(".__tr then\n");
            for (SemanticOp transfer : transfers) {
                switch (transfer.kind()) {
                    case BREAK -> {
                        KindPayload.BreakPayload breakPayload =
                            (KindPayload.BreakPayload) transfer.payload();
                        out.append(pad).append("  if ").append(errorVar)
                            .append(".t == \"break\" and ").append(errorVar)
                            .append(".id == ")
                            .append(breakPayload.loopId().id()).append(" then\n");
                        emitPlainSuccess(tryOp);
                        emitTransferClosures(tryOp, opsById.get(breakPayload.loopId()),
                            false);
                        out.append(pad).append("    goto ")
                            .append(loopExit(breakPayload.loopId())).append("\n");
                        out.append(pad).append("  end\n");
                    }
                    case CONTINUE -> {
                        KindPayload.ContinuePayload continuePayload =
                            (KindPayload.ContinuePayload) transfer.payload();
                        out.append(pad)
                            .append("  if ").append(errorVar)
                            .append(".t == \"continue\" and ").append(errorVar)
                            .append(".id == ")
                            .append(continuePayload.loopId().id()).append(" then\n");
                        emitPlainSuccess(tryOp);
                        emitTransferClosures(tryOp, opsById.get(continuePayload.loopId()),
                            false);
                        out.append(pad).append("    goto ")
                            .append(loopCont(continuePayload.loopId())).append("\n");
                        out.append(pad).append("  end\n");
                    }
                    case RETURN -> {
                        out.append(pad)
                            .append("  if ").append(errorVar)
                            .append(".t == \"return\" then\n");
                        emitPlainSuccess(tryOp);
                        emitTransferClosures(tryOp, null, false);
                        out.append(pad).append("    return ").append(errorVar)
                            .append(".v\n");
                        out.append(pad).append("  end\n");
                    }
                    default -> {
                    }
                }
            }
            out.append(pad).append("  error(").append(errorVar).append(", 0)\n");
            out.append(pad).append("end\n");
        }

        /** Collects the transfer ops of a block recursively through structure payloads. */
        private void collectTransfers(BlockId block, List<SemanticOp> transfers) {
            for (OpId opId : table.blockOps().get(block)) {
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

        private void emitThrow(SemanticOp op) {
            KindPayload.ThrowPayload payload = (KindPayload.ThrowPayload) op.payload();
            emitStart(op);
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "__errtext({__d = true, code = " + slot(payload.errorValue())
                    + ".code, m = " + slot(payload.errorValue()) + ".m, o = "
                    + luaString(originOf(op)) + ", e = nil, a = nil, f = __framesText(), "
                    + "cause = nil})");
            out.append("error({__d = true, code = ").append(slot(payload.errorValue()))
                .append(".code, m = ").append(slot(payload.errorValue()))
                .append(".m, o = ").append(luaString(originOf(op)))
                .append(", e = nil, a = nil, f = __framesText(), cause = nil}, 0)\n");
        }

        private void emitReturn(SemanticOp op) {
            KindPayload.ReturnPayload payload = (KindPayload.ReturnPayload) op.payload();
            SemanticOp boundary = opsById.get(payload.returnBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitStart(op);
            String value = payload.value() == null ? "nil" : slot(payload.value());
            out.append("__rvT = ").append(value).append("\n");
            emitBoundaryStart(boundary, "__rvT", boundaryPayload.descriptor());
            // The body-local return cell's own failure projection: the cell
            // projection carries the cell's origin (the callee's RETURN), the
            // boundary and the RETURN op emit their FAILURE terminals, and the
            // identical error propagates (the semantic oracle's
            // runBoundaryChild + the owning-op FAILURE).
            out.append("__okB, __chkB = pcall(__bcheck, ")
                .append(luaString(descriptorText(boundaryPayload.descriptor())))
                .append(", ")
                .append(luaString(staticKind(boundaryPayload.descriptor())))
                .append(", __rvT");
            if (containsFunction(boundaryPayload.descriptor())) {
                out.append(", ")
                    .append(luaString(boundaryPayload.descriptor().canonicalSpecText()));
            }
            out.append(")\n");
            out.append("if not __okB then\n");
            out.append("  __chkB.o = ").append(luaString(originOf(boundary)))
                .append("\n");
            emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                "__errtext(__chkB)");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__chkB)");
            out.append("  error(__chkB, 0)\n");
            out.append("end\n");
            out.append("__rvcT = __chkB\n");
            emitBoundarySuccess(boundary, "__rvcT", boundaryPayload.descriptor());
            emitPlainSuccess(op);
            if (tryDepth > 0) {
                emitTransferClosures(op, null, true);
                out.append("error({__tr = true, t = \"return\", v = __rvcT}, 0)\n");
            } else {
                emitTransferClosures(op, null, false);
                if (currentFunctionId != null) {
                    // Jump to the function's return trampoline — the last
                    // statement of the closure body. A raw Lua return
                    // would be followed by a structure's closing label
                    // (a return inside a branch/loop/for-each block) or by
                    // the trampoline label itself (a top-level return
                    // before the tail) — both invalid Lua.
                    out.append("goto ").append(returnLabel(currentFunctionId))
                        .append("\n");
                } else {
                    // Defensive: a RETURN outside any factory emission
                    // (never produced by the walk) keeps the plain form.
                    out.append("return __rvcT\n");
                }
            }
        }

        private void emitBreak(SemanticOp op) {
            KindPayload.BreakPayload payload = (KindPayload.BreakPayload) op.payload();
            emitStart(op);
            emitPlainSuccess(op);
            if (tryDepth > 0) {
                emitTransferClosures(op, opsById.get(payload.loopId()), true);
                out.append("error({__tr = true, t = \"break\", id = ")
                    .append(payload.loopId().id()).append("}, 0)\n");
            } else {
                emitTransferClosures(op, opsById.get(payload.loopId()), false);
                out.append("goto ").append(loopExit(payload.loopId())).append("\n");
            }
        }

        private void emitContinue(SemanticOp op) {
            KindPayload.ContinuePayload payload = (KindPayload.ContinuePayload) op.payload();
            emitStart(op);
            emitPlainSuccess(op);
            if (tryDepth > 0) {
                emitTransferClosures(op, opsById.get(payload.loopId()), true);
                out.append("error({__tr = true, t = \"continue\", id = ")
                    .append(payload.loopId().id()).append("}, 0)\n");
            } else {
                emitTransferClosures(op, opsById.get(payload.loopId()), false);
                out.append("goto ").append(loopCont(payload.loopId())).append("\n");
            }
        }

        private void emitDiscard(SemanticOp op) {
            emitStart(op);
            emitPlainSuccess(op);
        }

        /**
         * {@code EXPORT_PUBLISH} — the checked {@code MODULE_EXPORT}
         * boundary (its owned child) then the export-table publication of
         * the callable function value (the wrapper's closure, unwrapped
         * so a retained caller can invoke it directly) plus the
         * compiler-owned {@code __val} field carrying the published value
         * itself (M2: the compiled read's resolution source; the
         * {@code f} projection stays the retained-caller ABI's raw
         * callable).
         */
        private void emitExportPublish(SemanticOp op) {
            KindPayload.ExportPublishPayload payload =
                (KindPayload.ExportPublishPayload) op.payload();
            emitStart(op);
            SemanticOp boundary = boundaryChildOf(op);
            if (boundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                emitBoundaryStart(boundary, slot(payload.value()),
                    boundaryPayload.descriptor());
                out.append("__chk = ")
                    .append(bcheckExpr(boundaryPayload.descriptor(),
                        slot(payload.value())))
                    .append("\n");
                emitBoundarySuccess(boundary, "__chk", boundaryPayload.descriptor());
            }
            out.append("__exportSurfaces[")
                .append(luaString(emittingModulePath(op)))
                .append("][").append(luaString(payload.name()))
                .append("] = {__kind = \"function\", sig = ")
                .append(luaString(payload.descriptor().canonicalSpecText()))
                .append(", f = __unfn(").append(slot(payload.value()))
                .append("), __val = ").append(slot(payload.value()))
                .append("}\n");
            emitPlainSuccess(op);
        }

        /**
         * The statically known identity of the module that emits an op:
         * the export surface's key. An op with no owning module is a
         * producer defect, never a path guess.
         */
        private String emittingModulePath(SemanticOp op) {
            ModuleId moduleId = opModule.get(op.opId());
            if (moduleId == null) {
                throw new IllegalStateException("the op " + op.opId()
                    + " has no owning module (the export-surface key is the emitting "
                    + "module's identity — a producer defect, never a path guess)");
            }
            return moduleId.path();
        }

        /**
         * {@code EXTERNAL_ENTRY} — the callee-unit invocation record of a
         * function callable across a shared/shadow edge: the exports table
         * already publishes the callable value under the export name, so
         * the record needs no runtime action.
         */
        private void emitExternalEntryRecord(SemanticOp op) {
            emitStart(op);
            emitPlainSuccess(op);
        }

        /**
         * CALLBACK_INVOKE (E6, D13 host-driven dispatch): one per-unit
         * entry function the scenario host invokes top-level with
         * scripted arguments. The entry emits its own START (the
         * scripted argument inputs, no parentOpId — the scenario step
         * triggers it), runs the {@code HOST_TO_DEAL} parameter
         * boundaries in one-based order, executes the bound
         * {@link FunctionExecutionBinding} (a DEAL body, or the D15
         * adapter protocol with the leading-M projection), and closes
         * with the op's terminal (SUCCESS with the checked value, or
         * FAILURE with the propagated error). The single
         * {@code DEAL_TO_HOST} return boundary runs by the executed
         * body's {@code RETURN} (its payload names this op as the
         * enclosing invocation). The block walk never runs the entry.
         */
        private void emitCallbackInvoke(SemanticOp op) {
            KindPayload.CallbackInvokePayload payload =
                (KindPayload.CallbackInvokePayload) op.payload();
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new FunctionAllocationIdentity(payload.function().id()));
            if (binding == null) {
                throw new IllegalStateException("CALLBACK_INVOKE " + op.opId()
                    + " resolves no FunctionExecutionBinding (producer defect)");
            }
            String entry = "cb" + op.opId().id();
            out.append("__callbacks[").append(luaString(entry))
                .append("] = function(...)\n");
            out.append("  local __cargs = {...}\n");
            if (trace) {
                StringBuilder inputs = new StringBuilder();
                for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                    if (i > 0) {
                        inputs.append(", ");
                    }
                    inputs.append("__hostAtom(__cargs[").append(i + 1).append("])");
                }
                out.append("  __ev(").append(luaString(opKey(op.opId())))
                    .append(", \"START\", ")
                    .append(luaString(op.kind().name())).append(", ")
                    .append(luaString(op.contract().canonicalDigest()))
                    .append(", \"-\", {").append(inputs).append("}, nil, nil)\n");
            }
            for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                SemanticOp boundary = opsById.get(payload.parameterBoundaryOpIds().get(i));
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                if (trace) {
                    out.append("  __ev(").append(luaString(opKey(boundary.opId())))
                        .append(", \"START\", \"BOUNDARY\", ")
                        .append(luaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(luaString(parentKey(boundary.origin().parentOpId())))
                        .append(", {__hostAtom(__cargs[").append(i + 1)
                        .append("])}, nil, nil)\n");
                }
                out.append("  __okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", __cargs[").append(i + 1).append("])\n");
                out.append("  if not __okB then\n");
                out.append("    __chkB.o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "__errtext(__chkB)");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "__errtext(__chkB)");
                }
                out.append("    error(__chkB, 0)\n");
                out.append("  end\n");
                if (trace) {
                    out.append("  __ev(").append(luaString(opKey(boundary.opId())))
                        .append(", \"SUCCESS\", \"BOUNDARY\", ")
                        .append(luaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(luaString(parentKey(boundary.origin().parentOpId())))
                        .append(", {}, __atom(")
                        .append(luaString(staticKind(boundaryPayload.descriptor())))
                        .append(", __chkB), nil)\n");
                }
                out.append("  __cargs[").append(i + 1).append("] = __chkB\n");
            }
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    LoweredFunction function = unit.functions().get(body.functionId());
                    List<BindingId> captures = function == null
                        ? List.of() : function.captures();
                    StringBuilder caps = new StringBuilder();
                    for (BindingId captureId : captures) {
                        if (caps.length() > 0) {
                            caps.append(", ");
                        }
                        caps.append(cell(captureId, 0));
                    }
                    out.append("  table.insert(__frames, 1, ")
                        .append(luaString(String.valueOf(body.functionId().id())))
                        .append(")\n");
                    out.append("  __okT, __resT = pcall(")
                        .append(fnFactory(body.functionId())).append("(")
                        .append(caps).append(")");
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        out.append(", __cargs[").append(i + 1).append("]");
                    }
                    out.append(")\n");
                    out.append("  table.remove(__frames, 1)\n");
                    out.append("  if not __okT then\n");
                    if (trace) {
                        emitFailureEvent(op.opId(), op.kind().name(), op,
                            "__errtext(__resT)");
                    }
                    out.append("    error(__resT, 0)\n");
                    out.append("  end\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    String adapterSlot =
                        slot((ValueId) opsById.get(adapter.adaptOpId()).result());
                    out.append("  __okT, __resT = pcall(").append(adapterSlot)
                        .append(".__fn, ").append(adapterSlot).append(", ")
                        .append(luaString(originOf(op)));
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        out.append(", __cargs[").append(i + 1).append("]");
                    }
                    out.append(")\n");
                    out.append("  if not __okT then\n");
                    if (trace) {
                        emitFailureEvent(op.opId(), op.kind().name(), op,
                            "__errtext(__resT)");
                    }
                    out.append("    error(__resT, 0)\n");
                    out.append("  end\n");
                }
                case FunctionExecutionBinding.HostFunction host ->
                    emitHostCallbackInvoke(op, payload,
                        "__exportSurfaces[" + luaString(host.hostModuleId().path())
                            + "][" + luaString(host.exportName()) + "]");
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    SemanticOp crossing = opsById.get(
                        hostValue.materializingBoundaryOpId());
                    if (crossing == null
                            || !(crossing.payload()
                                instanceof KindPayload.BoundaryPayload boundary)) {
                        throw new IllegalStateException("CALLBACK_INVOKE "
                            + op.opId() + " names the materializing host crossing "
                            + hostValue.materializingBoundaryOpId()
                            + ", which is not a boundary op of the emitted closure"
                            + " (a producer defect)");
                    }
                    emitHostCallbackInvoke(op, payload, slot(boundary.input()));
                }
                default -> throw new IllegalStateException("CALLBACK_INVOKE "
                    + op.opId() + " resolves a binding outside the statically-resolved "
                    + "slice: " + binding);
            }
            if (trace) {
                out.append("  __ev(").append(luaString(opKey(op.opId())))
                    .append(", \"SUCCESS\", ")
                    .append(luaString(op.kind().name())).append(", ")
                    .append(luaString(op.contract().canonicalDigest()))
                    .append(", \"-\", {}, __atom(")
                    .append(luaString(staticKind(payload.descriptor().returnType())))
                    .append(", __resT), nil)\n");
            }
            out.append("  return __resT\n");
            out.append("end\n");
        }

        /**
         * The host {@code CALLBACK_INVOKE} arm (ISSUE-0651;
         * {@code host-module-load-and-host-call-realization} H3 and the sync
         * host call contract): the callback record's bound value resolves
         * to a host function, so the host-driven invocation runs the loaded
         * surface entry with the {@code HOST_TO_DEAL} checked arguments and
         * the callback op's own origin, then the callback op's own return
         * projection (its single return boundary child).
         */
        private void emitHostCallbackInvoke(SemanticOp op,
                KindPayload.CallbackInvokePayload payload, String target) {
            StringBuilder args = new StringBuilder();
            for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append("__cargs[").append(i + 1).append("]");
            }
            out.append("  __okT, __resT = pcall(").append(target).append(".f");
            if (args.length() > 0) {
                out.append(", ").append(args);
            }
            out.append(", ").append(spanTripletArgs(op)).append(")\n");
            out.append("  if not __okT then\n");
            out.append("    __resT = __hostError(__resT, ")
                .append(luaString(originOf(op))).append(")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("    error(__resT, 0)\n");
            out.append("  end\n");
            if (payload.returnBoundaryOpId() != null) {
                SemanticOp boundary = opsById.get(payload.returnBoundaryOpId());
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                emitBoundaryStart(boundary, "__resT", boundaryPayload.descriptor());
                out.append("  __okB, __chkB = pcall(__bcheck, ")
                    .append(luaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(luaString(staticKind(boundaryPayload.descriptor())))
                    .append(", __resT)\n");
                out.append("  if not __okB then\n");
                out.append("    __chkB.o = ")
                    .append(luaString(originOf(boundary))).append("\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "__errtext(__chkB)");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "__errtext(__chkB)");
                out.append("    error(__chkB, 0)\n");
                out.append("  end\n");
                out.append("  __resT = __chkB\n");
                emitBoundarySuccess(boundary, "__resT", boundaryPayload.descriptor());
            }
        }

        // -- async (E4, D13) ----------------------------------------------------------

        /** The canonical referent token identity (alias chains resolve transitively). */
        private long canonicalReferent(AsyncTokenId token) {
            AsyncTokenId current = token;
            while (current instanceof AsyncTokenId.Alias alias) {
                current = alias.referent();
            }
            return current.tokenId();
        }

        /** The canonical referent's closed owner (statically resolved). */
        private AsyncTokenOwner canonicalOwnerOf(AsyncTokenId token) {
            AsyncTokenId current = token;
            while (current instanceof AsyncTokenId.Alias alias) {
                current = alias.referent();
            }
            return ((AsyncTokenId.Canonical) current).owner();
        }

        /** The canonical token atom of an ASYNC_START/EXTERNAL_ENTRY SUCCESS. */
        private String tokenAtom(AsyncTokenId token) {
            return switch (token) {
                case AsyncTokenId.Canonical canonical -> "tok:" + canonical.tokenId()
                    + ":" + canonical.owner().name();
                case AsyncTokenId.Alias alias -> "alias:" + alias.tokenId() + "->"
                    + canonicalReferent(alias.referent());
            };
        }

        /** SUCCESS with a raw output atom expression (token atoms). */
        private void emitTokenSuccess(SemanticOp op, String atomExpr) {
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                .append(", ").append(luaString(op.contract().canonicalDigest()))
                .append(", ").append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, ").append(atomExpr).append(", nil)\n");
        }

        /** A boundary START event with a raw input atom expression. */
        private void emitBoundaryStartAtom(SemanticOp boundary, String atomExpr) {
            out.append("__ev(").append(luaString(opKey(boundary.opId())))
                .append(", \"START\", \"BOUNDARY\", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId())))
                .append(", {").append(atomExpr).append("}, nil, nil)\n");
        }

        /** A boundary SUCCESS event with a raw output atom expression. */
        private void emitBoundarySuccessAtom(SemanticOp boundary, String atomExpr) {
            out.append("__ev(").append(luaString(opKey(boundary.opId())))
                .append(", \"SUCCESS\", \"BOUNDARY\", ")
                .append(luaString(boundary.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(boundary.origin().parentOpId())))
                .append(", {}, ").append(atomExpr).append(", nil)\n");
        }

        /** The nested source ASYNC_START parented to an adapter-over-async op. */
        private SemanticOp nestedAsyncStartOf(SemanticOp outer) {
            for (SemanticOp candidate : opsById.values()) {
                if (candidate.kind() == SemanticOpKind.ASYNC_START
                        && outer.opId().equals(candidate.origin().parentOpId())) {
                    return candidate;
                }
            }
            throw new IllegalStateException("the adapter-over-async task has no nested "
                + "source ASYNC_START (producer defect)");
        }

        /**
         * ASYNC_START (E4, D13 task creation): the parameter boundaries
         * (the complete xN set under RUN — zero under
         * ELIDED_BY_ADAPTER), then exactly one task record per call. A
         * DEAL body task is a coroutine wrapping the body-task closure
         * (the canonical {@code AsyncTokenId} is the task record); an
         * adapter-over-async task resolves the D15 source, checks the
         * source signature, and executes the nested source op; a host
         * operation starts through the artifact's host-seam dispatch
         * entry (bad handle → the op's own E8010
         * {@code ASYNC_OPERATION_HANDLE}); an external operation starts
         * through the callee artifact's async-entry dispatch entry. The
         * op's terminal publishes the canonical/alias token atom.
         */
        private void emitAsyncStart(SemanticOp op) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            AsyncTokenId token = (AsyncTokenId) op.result();
            emitStart(op);
            // The argument carrier: the boundary-checked values (RUN) or
            // the raw operand values (ELIDED_BY_ADAPTER) — a fresh table
            // per execution, captured by the task record.
            if (payload.parameterBoundaryMode() == ParameterBoundaryMode.RUN) {
                out.append("S.__sa").append(op.opId().id()).append(" = {}\n");
                for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                    SemanticOp boundary = opsById.get(boundaryId);
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) boundary.payload();
                    emitBoundaryStart(boundary, slot(boundaryPayload.input()),
                        boundaryPayload.descriptor());
                    out.append("__chk = ")
                        .append(bcheckExpr(boundaryPayload.descriptor(),
                            slot(boundaryPayload.input())))
                        .append("\n");
                    emitBoundarySuccess(boundary, "__chk", boundaryPayload.descriptor());
                    out.append("S.__sa").append(op.opId().id())
                        .append("[#S.__sa").append(op.opId().id())
                        .append(" + 1] = __chk\n");
                }
            } else {
                out.append("S.__sa").append(op.opId().id()).append(" = {");
                for (int i = 0; i < op.operands().size(); i++) {
                    if (i > 0) {
                        out.append(", ");
                    }
                    out.append(slot(op.operands().get(i)));
                }
                out.append("}\n");
            }
            if (payload.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                // The dynamic async start (ISSUE-0658): the class of the
                // resolved carrier selects the task source.
                emitDynamicAsyncStart(op, payload, dynamic, token);
                emitTokenSuccess(op, luaString(tokenAtom(token)));
                return;
            }
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                default -> throw new IllegalStateException("ASYNC_START " + op.opId()
                    + " resolves a callee outside the statically-resolved slice: "
                    + payload.callee());
            };
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    LoweredFunction function = unit.functions().get(body.functionId());
                    List<BindingId> captures = function == null
                        ? List.of() : function.captures();
                    StringBuilder caps = new StringBuilder();
                    for (BindingId captureId : captures) {
                        if (caps.length() > 0) {
                            caps.append(", ");
                        }
                        caps.append(cell(captureId, 0));
                    }
                    out.append("__asyncStartTask(").append(token.tokenId())
                        .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
                    out.append("  table.insert(__frames, 1, ")
                        .append(luaString(String.valueOf(body.functionId().id())))
                        .append(")\n");
                    out.append("  local __okA, __resA = pcall(")
                        .append(fnFactory(body.functionId())).append("(").append(caps)
                        .append("), unpack(S.__sa").append(op.opId().id())
                        .append(", 1, #S.__sa").append(op.opId().id()).append("))\n");
                    out.append("  table.remove(__frames, 1)\n");
                    out.append("  if not __okA then error(__resA, 0) end\n");
                    out.append("  return __resA\n");
                    out.append("end), S.__sa").append(op.opId().id()).append(")\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    // The outer adapter-over-async task (zero return
                    // boundaries of its own): the D15 source resolution
                    // and source-signature check, then the nested source
                    // op's full emission (its task queues under the FIFO
                    // drain — the outer task completes after it).
                    SemanticOp nested = nestedAsyncStartOf(op);
                    out.append("__asyncStartTask(").append(token.tokenId())
                        .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
                    out.append("  local __srcA = __adaptSource(")
                        .append(slot((ValueId) opsById.get(adapter.adaptOpId()).result()))
                        .append(")\n");
                    out.append("  __fncheck(__srcA, ")
                        .append(luaString(adapter.sourceSignature().canonicalSpecText()))
                        .append(", ").append(luaString(originOf(op))).append(")\n");
                    emitAsyncStart(nested);
                    out.append("  return nil\n");
                    out.append("end), S.__sa").append(op.opId().id()).append(")\n");
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    if (hostSurface == null) {
                        // A unit/surface-less session is the scenario drive:
                        // its async host path is the landed deterministic
                        // seam, which the production path never reaches.
                        emitAsyncHostSeamStart(op, token, host.hostModuleId().path(),
                            host.exportName());
                    } else {
                        emitAsyncHostStart(op, token,
                            hostSurfaceEntry(host.hostModuleId().path(),
                                host.exportName()),
                            asyncStartArgs(op, payload));
                    }
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    if (hostSurface == null) {
                        emitAsyncHostSeamStart(op, token,
                            hostValue.hostModuleId().path(),
                            "@value#" + hostValue.materializingBoundaryOpId().id());
                    } else {
                        emitAsyncHostStart(op, token, hostValueTarget(hostValue),
                            asyncStartArgs(op, payload));
                    }
                }
                case FunctionExecutionBinding.ExternalFunction external ->
                    emitAsyncExternalStart(op, token, payload.externalAsyncLink());
                case FunctionExecutionBinding.IntrinsicFunction intrinsic -> {
                    // The intrinsic's async form (ISSUE-0680; design source
                    // {@code conversion-intrinsic-function-values} J3: the
                    // conversion intrinsics are synchronous values, so an
                    // async use is a checker rejection — this arm is the
                    // deterministic closed treatment of a doctored site): the
                    // closed DEAL_BODY task runs the one conversion ladder
                    // inside the task closure with this op's context and kind
                    // over the recorded argument carrier and completes
                    // immediately with the converted value; the single AWAIT
                    // runs the landed ASYNC_COMPLETION cell on the completion
                    // (zero return boundaries).
                    String carrier = "S.__sa" + op.opId().id() + "[1]";
                    out.append("__asyncStartTask(").append(token.tokenId())
                        .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
                    out.append("  local __okA, __resA\n");
                    emitIntrinsicLadderPcall(op, intrinsic.kind(), carrier, "  ");
                    out.append("  if not __okA then error(__resA, 0) end\n");
                    out.append("  return __resA\n");
                    out.append("end), S.__sa").append(op.opId().id()).append(")\n");
                }
                case FunctionExecutionBinding.DynamicFunctionValue dynamic ->
                    throw new IllegalStateException("ASYNC_START " + op.opId()
                        + " resolves the dynamic function value produced by "
                        + dynamic.materializingOpId() + " outside the dynamic arm (a "
                        + "DynamicFunctionValue names no execution class and is never a "
                        + "statically resolved callee — producer defect)");
            }
            emitTokenSuccess(op, luaString(tokenAtom(token)));
        }

        /**
         * The completed argument slots of one {@code ASYNC_START} arm: the
         * per-position entries of the {@code S.__sa<op>} carrier table.
         * Each argument is passed as its own expression — a trailing
         * {@code unpack} would be truncated to one value in a non-final
         * argument position under Lua 5.1/LuaJIT semantics, silently
         * dropping arguments and colliding with the trailing span triplet.
         */
        private List<String> asyncStartArgs(SemanticOp op,
                KindPayload.AsyncStartPayload payload) {
            int count = payload.parameterBoundaryMode() == ParameterBoundaryMode.RUN
                ? payload.parameterBoundaryOpIds().size()
                : op.operands().size();
            List<String> args = new ArrayList<>();
            for (int i = 1; i <= count; i++) {
                args.add("S.__sa" + op.opId().id() + "[" + i + "]");
            }
            return args;
        }

        /**
         * The scenario-drive {@code ASYNC_START(HOST)} terminal (the landed
         * shape): the deterministic seam start plus the bad-handle check.
         * Emitted only by a session without the compile's host declaration
         * surface (a unit/surface-less session); the production and
         * trace-mode project sessions take the operation-handle arm above.
         */
        private void emitAsyncHostSeamStart(SemanticOp op, AsyncTokenId token,
                                            String module, String export) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            String label = payload.hostOperationLabel();
            if (trace) {
                out.append("io.stderr:write(\"F|ASYNC_START_OP|-|\"..__esc(")
                    .append(luaString(label)).append(")..\"\\n\")\n");
                out.append("io.stderr:flush()\n");
            }
            out.append("local __handleH = __callbacks.__hostStartAsync(")
                .append(luaString(label)).append(", ")
                .append(luaString(module)).append(", ")
                .append(luaString(export)).append(", unpack(S.__sa")
                .append(op.opId().id()).append(", 1, #S.__sa")
                .append(op.opId().id()).append("))\n");
            out.append("if __handleH == nil then\n");
            out.append("  local __eH = __failExpr(\"E8010\", "
                + "\"async operation mismatch: expected async-operation, got nothing\", ")
                .append(luaString(originOf(op)))
                .append(", \"async-operation\", \"nothing\")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__eH)");
            out.append("  error(__eH, 0)\n");
            out.append("end\n");
            out.append("__asyncStartHost(").append(token.tokenId()).append(", ")
                .append(luaString(label)).append(")\n");
        }

        /**
         * The ASYNC_START(HOST) terminal (ISSUE-0652;
         * {@code host-module-load-and-host-call-realization} H4 and the
         * async host start and completion contract): the loaded surface
         * entry is invoked through the same host-boundary call shape as
         * the sync arm ({@code <entry>.f(args..., file, line, column)}) —
         * the loaded wrapper's declared-async shape check realizes the
         * op's {@code ASYNC_OPERATION_HANDLE} terminal with the pinned
         * E8010 {@code host async function must return an async operation,
         * got {actual}} at the call origin — and the returned operation
         * handle is bound to the canonical token. The deterministic
         * {@code __callbacks.__hostStartAsync} seam is never referenced on
         * the production path (the seam entry stays the scenario/oracle
         * drive's).
         */
        private void emitAsyncHostStart(SemanticOp op, AsyncTokenId token,
                                        String target, List<String> args) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            String label = payload.hostOperationLabel();
            if (trace) {
                out.append("io.stderr:write(\"F|ASYNC_START_OP|-|\"..__esc(")
                    .append(luaString(label)).append(")..\"\\n\")\n");
                out.append("io.stderr:flush()\n");
            }
            // The converged host-boundary call shape, identical to the
            // sync arm: the trailing literal span triplet is how the
            // loaded wrapper's declared-async shape check reports the DEAL
            // call site byte-exact (the pinned E8010 at the call origin).
            out.append("__okT, __resT = pcall((").append(target).append(").f");
            for (String arg : args) {
                out.append(", ").append(arg);
            }
            out.append(", ").append(spanTripletArgs(op)).append(")\n");
            out.append("if not __okT then\n");
            out.append("  __resT = __hostError(__resT, ")
                .append(luaString(originOf(op))).append(")\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resT)");
            out.append("  error(__resT, 0)\n");
            out.append("end\n");
            out.append("__asyncStartHost(").append(token.tokenId()).append(", ")
                .append(luaString(label)).append(", __resT)\n");
        }

        /**
         * The loaded surface entry of one declared host export: the
         * module identity is the surface key (H1), so no alias is needed
         * and the direct {@code ASYNC_START(HOST)}, the value-position
         * {@code ASYNC_START} on the read's registration, and a
         * {@code HostFunctionValue} crossing all resolve one entry.
         */
        private String hostSurfaceEntry(String modulePath, String exportName) {
            return "__exportSurfaces[" + luaString(modulePath) + "]["
                + luaString(exportName) + "]";
        }

        /**
         * The materialized host-facing function value of one
         * {@code HostFunctionValue} crossing ({@code .f} is the loaded
         * wrapper's calling convention, exactly as the sync arm's).
         */
        private String hostValueTarget(FunctionExecutionBinding.HostFunctionValue hostValue) {
            SemanticOp crossing = opsById.get(hostValue.materializingBoundaryOpId());
            if (crossing == null
                    || !(crossing.payload() instanceof KindPayload.BoundaryPayload boundary)) {
                throw new IllegalStateException("ASYNC_START names the materializing"
                    + " host crossing " + hostValue.materializingBoundaryOpId()
                    + ", which is not a boundary op of the emitted closure"
                    + " (a producer defect)");
            }
            return slot(boundary.input());
        }

        /**
         * The ASYNC_START(EXTERNAL) terminal: the callee unit's
         * async-entry dispatch inside the one artifact, keyed by the
         * callee module and export (ISSUE-0655,
         * {@code cross-module-call-realization} X2). The caller passes the
         * drive flag false (its AWAIT drains). A project session resolves
         * the link's canonical token against the emitted async-entry set
         * and fails closed when it names no entry — never a silently
         * missing invocation; a single-unit session keys the chunk-global
         * dispatch table the callee's own artifact populates (the
         * multi-artifact drive of the differential harness).
         */
        private void emitAsyncExternalStart(SemanticOp op, AsyncTokenId token,
                                            ExternalAsyncLink link) {
            if (link == null) {
                throw new IllegalStateException("ASYNC_START(EXTERNAL) without "
                    + "its ExternalAsyncLink (producer defect)");
            }
            if (projectSession) {
                resolveExternalAsyncEntry(op, link);
            }
            out.append("__asyncEntries[")
                .append(luaString(link.calleeModuleId().path() + "#"
                    + link.exportName())).append("](")
                .append(luaString(opKey(op.opId()))).append(", false, unpack(S.__sa")
                .append(op.opId().id()).append(", 1, #S.__sa")
                .append(op.opId().id()).append("))\n");
        }

        /**
         * The callee unit's recorded async {@code EXTERNAL_ENTRY} of one
         * {@code ASYNC_START(EXTERNAL)}: resolved by the link's canonical
         * token (the entry op's own id by construction) inside the callee
         * module's unit. A missing module outside the session's closure, a
         * token naming no op, a non-entry op, a sync entry, or a divergent
         * export name is a fail-closed producer defect — the entry's
         * dispatch key would otherwise resolve to no emitted entry at
         * execution.
         */
        private SemanticOp resolveExternalAsyncEntry(SemanticOp op,
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
         * AWAIT — the completion position (D13 step 6): the deterministic
         * FIFO drain first, then the canonical referent's completion. A
         * production host operation (a record carrying the loaded declared
         * async export's operation handle) is driven to completion through
         * the landed {@code __rt.async_step} machinery — the operation's
         * own DEAL failure becomes the task's failure identical (never
         * re-checked, copied, or re-projected) and a non-DEAL failure
         * rethrows as infrastructure; a seam-registered record (no
         * handle) keeps the landed deterministic host-seam completion. A
         * failed operation publishes the identical error — never a
         * re-check or a synthesized copy — and a completed value crosses
         * the single {@code ASYNC_COMPLETION} boundary at the await site
         * (a boundary failure is re-originated at that site).
         */
        private void emitAwait(SemanticOp op) {
            KindPayload.AwaitPayload payload = (KindPayload.AwaitPayload) op.payload();
            long canonicalId = canonicalReferent(payload.token());
            SemanticOp boundary = opsById.get(payload.completionBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitStart(op);
            out.append("__asyncDrain()\n");
            out.append("local __tA = __tasks[").append(canonicalId).append("]\n");
            out.append("if __tA == nil then\n");
            out.append("  error(\"AWAIT consumes an unbound token ")
                .append(payload.token()).append(" (producer defect)\", 0)\n");
            out.append("end\n");
            out.append("if __tA.status == 2 then\n");
            out.append("  if __tA.handle ~= nil then\n");
            // The production host operation: the registered operation
            // handle is driven through the landed async_step machinery.
            // The operation's own DEAL failure (the runtime's error table
            // or the chunk's tagged carrier) is the task's failure —
            // converted once into the chunk's canonical carrier with its
            // own code, message, origin, expected, and actual; anything
            // else is an infrastructure failure and rethrows identical.
            out.append("    local __okH, __errH = pcall(__rt.async_step, "
                + "__tA.handle)\n");
            out.append("    if not __okH then\n");
            out.append("      if type(__errH) == \"table\" and (__errH.__d "
                + "or (__errH.code ~= nil and __errH.message ~= nil)) then\n");
            out.append("        __tA.err = __hostError(__errH, ")
                .append(luaString(originOf(op))).append(")\n");
            if (trace) {
                out.append("        io.stderr:write(\"F|ASYNC_COMPLETE_THROW|-|\""
                    + "..__esc(__tA.label..\"!\"..__tA.err.code)..\"\\n\")\n");
                out.append("        io.stderr:flush()\n");
            }
            out.append("      else\n");
            out.append("        error(__errH, 0)\n");
            out.append("      end\n");
            out.append("    else\n");
            out.append("      __tA.value = __tA.handle.__result\n");
            if (trace) {
                out.append("      io.stderr:write(\"F|ASYNC_COMPLETE_RETURN|-|\""
                    + "..__esc(__tA.label..\"=\"..__hostAtom(__tA.value))..\"\\n\")\n");
                out.append("      io.stderr:flush()\n");
            }
            out.append("    end\n");
            out.append("  else\n");
            out.append("    local __oA = "
                + "__callbacks.__hostCompleteAsync(__tA.label)\n");
            out.append("    if __oA.ok then\n");
            if (trace) {
                out.append("      io.stderr:write(\"F|ASYNC_COMPLETE_RETURN|-|\""
                    + "..__esc(__tA.label..\"=\"..__hostAtom(__oA.v))..\"\\n\")\n");
                out.append("      io.stderr:flush()\n");
            }
            out.append("      __tA.value = __oA.v\n");
            out.append("    else\n");
            if (trace) {
                out.append("      io.stderr:write(\"F|ASYNC_COMPLETE_THROW|-|\""
                    + "..__esc(__tA.label..\"!\"..__oA.code)..\"\\n\")\n");
                out.append("      io.stderr:flush()\n");
            }
            out.append("      __tA.err = {__d = true, code = __oA.code, m = __oA.m, o = ")
                .append(luaString(originOf(op)))
                .append(", e = nil, a = nil, f = __framesText(), cause = nil}\n");
            out.append("    end\n");
            out.append("  end\n");
            out.append("  __tA.status = 1\n");
            out.append("end\n");
            out.append("if __tA.err ~= nil then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__tA.err)");
            out.append("  error(__tA.err, 0)\n");
            out.append("end\n");
            // The single ASYNC_COMPLETION boundary at the await site: a
            // host completion atomizes by its runtime carrier; a DEAL body
            // value atomizes by the declared descriptor. A boundary
            // failure is re-originated at the boundary's own origin (the
            // await expression) and publishes the boundary's FAILURE
            // beside the await op's — the oracle's boundary-child pair.
            if (canonicalOwnerOf(payload.token()) == AsyncTokenOwner.HOST_OPERATION) {
                emitBoundaryStartAtom(boundary, "__hostAtom(__tA.value)");
            } else {
                emitBoundaryStart(boundary, "__tA.value", boundaryPayload.descriptor());
            }
            out.append("__okB, __chkB = pcall(__bcheck, ")
                .append(luaString(descriptorText(boundaryPayload.descriptor())))
                .append(", ")
                .append(luaString(staticKind(boundaryPayload.descriptor())))
                .append(", __tA.value, nil, true)\n");
            out.append("if not __okB then\n");
            out.append("  __chkB.o = ").append(luaString(originOf(boundary))).append("\n");
            emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                "__errtext(__chkB)");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__chkB)");
            out.append("  error(__chkB, 0)\n");
            out.append("end\n");
            emitBoundarySuccess(boundary, "__chkB", boundaryPayload.descriptor());
            out.append(slot((ValueId) op.result())).append(" = __chkB\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        /**
         * The async EXTERNAL_ENTRY dispatch entry (the E6 dispatch-entry
         * pattern; ISSUE-0655, {@code cross-module-call-realization} X2
         * and the cross-module async call contract): the scenario host
         * adapter invokes it top-level with scripted arguments (drive
         * flag on — the entry drains and returns the completion), and a
         * cross-module caller invokes it with the drive flag off (its
         * AWAIT drains). One entry exists per async export of every
         * closure unit, keyed by the owning module's path and the export
         * name; the entry resolves its function and its capture cells
         * through its own unit. It emits the callee record's
         * START/SUCCESS under the passed parent key and creates exactly
         * one canonical task wrapping the entry function's body-task
         * closure, establishing the owning module's context around the
         * body and its own events (a cross-module caller invokes the
         * entry from the caller's context) and restoring it on every
         * path.
         */
        private void emitAsyncEntry(SemanticOp op, LoweredModuleUnit owner) {
            KindPayload.ExternalEntryPayload payload =
                (KindPayload.ExternalEntryPayload) op.payload();
            LoweredFunction function = owner.functions().get(payload.function());
            List<BindingId> captures = function == null
                ? List.of() : function.captures();
            StringBuilder caps = new StringBuilder();
            for (BindingId captureId : captures) {
                if (caps.length() > 0) {
                    caps.append(", ");
                }
                caps.append(cell(captureId, 0));
            }
            String ownerPath = owner.moduleId().path();
            out.append("__asyncEntries[")
                .append(luaString(ownerPath + "#" + payload.exportName()))
                .append("] = function(__parentKey, __drive, ...)\n");
            // The entry establishes its own module context: a
            // cross-module caller invokes it from the caller's context,
            // and every event the entry emits (and every event of the
            // callee body it wraps) must carry the callee module. The
            // landed nesting-safe push/pop pair is reused verbatim.
            emitModulePush();
            out.append("  __module = ").append(luaString(ownerPath)).append("\n");
            out.append("  local __eargs = {...}\n");
            if (trace) {
                out.append("  __ev(").append(luaString(opKey(op.opId())))
                    .append(", \"START\", ").append(luaString(op.kind().name()))
                    .append(", ").append(luaString(op.contract().canonicalDigest()))
                    .append(", __parentKey, {}, nil, nil)\n");
            }
            out.append("  __asyncStartTask(").append(op.opId().id())
                .append(", \"DEAL_BODY_TASK\", coroutine.create(function()\n");
            // The body task runs at the caller's AWAIT drain (or at the
            // entry's own drive below), so it establishes the callee
            // module itself and restores it on every path.
            emitModulePush();
            out.append("    __module = ").append(luaString(ownerPath)).append("\n");
            out.append("    table.insert(__frames, 1, ")
                .append(luaString(String.valueOf(payload.function().id())))
                .append(")\n");
            String savedState = emitInvocationStateSave(payload.function(), op.opId());
            out.append("    local __okA, __resA = pcall(")
                .append(fnFactory(payload.function())).append("(").append(caps)
                .append("), unpack(__eargs, 1, #__eargs))\n");
            out.append("    table.remove(__frames, 1)\n");
            emitInvocationStateRestore(payload.function(), savedState);
            emitModulePop();
            out.append("    if not __okA then error(__resA, 0) end\n");
            out.append("    return __resA\n");
            out.append("  end), __eargs)\n");
            if (trace) {
                out.append("  __ev(").append(luaString(opKey(op.opId())))
                    .append(", \"SUCCESS\", ").append(luaString(op.kind().name()))
                    .append(", ").append(luaString(op.contract().canonicalDigest()))
                    .append(", __parentKey, {}, \"tok:").append(op.opId().id())
                    .append(":DEAL_BODY_TASK\", nil)\n");
            }
            out.append("  if __drive then\n");
            out.append("    __asyncDrain()\n");
            out.append("    local __tE = __tasks[").append(op.opId().id()).append("]\n");
            // The caller context is restored before the entry returns or
            // raises: the drive's own failure is the caller's to observe.
            emitModulePop();
            out.append("    if __tE.err ~= nil then error(__tE.err, 0) end\n");
            out.append("    return __tE.value\n");
            out.append("  end\n");
            emitModulePop();
            out.append("end\n");
        }

        /**
         * ENTRY_INVOKE — delegates exactly one CALL(DIRECT) to main
         * (its owned child) and exits after the terminal. A delegated
         * failure publishes the ENTRY_INVOKE FAILURE terminal (the oracle's
         * own projection) before the error propagates to the module-init
         * wrapper's terminal.
         */
        private void emitEntryInvoke(SemanticOp op) {
            emitStart(op);
            out.append("__okE, __resE = pcall(function()\n");
            for (SemanticOp candidate : opsById.values()) {
                if (candidate.kind() == SemanticOpKind.CALL
                        && op.opId().equals(candidate.origin().parentOpId())) {
                    emitCall(candidate);
                }
            }
            out.append("end)\n");
            out.append("if not __okE then\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__resE)");
            out.append("  error(__resE, 0)\n");
            out.append("end\n");
            emitPlainSuccess(op);
        }

        /**
         * {@code MODULE_IMPORT} — the import's load/initialization op. A
         * {@code HOST}-kind import emits the host load inline at its
         * position in the module init walk (ISSUE-0650;
         * {@code host-module-load-and-host-call-realization} H1 and the
         * host-load contract): the module's surface entry becomes the
         * loaded table through the landed loader
         * {@code __rt.load_host(rawSpecifier, declared, file, line,
         * column)} with the compiler-owned declared map in declaration
         * order, and the chunk-global {@code __exportSurfaces} registry
         * entry is written with the idempotent {@code or} guard, so a
         * repeated import of the same module (two aliases, two
         * declarations) loads exactly once per program and every alias
         * observes the one loaded surface value. The loaded table is
         * published in the same registry the {@code EXPORT_PUBLISH}/
         * {@code EXPORT_READ} arms use, so it is the host import's
         * namespace value. The pinned E8011 defects (missing declared
         * export, invalid function/class export shape, pre-wrapped
         * signature mismatch or non-function {@code .f}, class identity
         * mismatch, missing or non-table {@code <C>_defaults}, a
         * non-table module result) fail the importing module's init at
         * the emitted import-statement origin with the host-module-abi
         * texts.
         *
         * <p>An extern-C declaration import ({@code @extern-c}) emits the
         * generator's FFI load at the same position — the provider
         * bindings re-pointed at the chunk's export-surface registry, the
         * bindings literal, and the
         * {@code __exportSurfaces[<module>] = ... __rt.load_ffi(...)}
         * registry entry with the import statement's span triplet (the
         * extern-C admission slice) — when the session carries the
         * compile's FFI emission input; the loaded module table becomes
         * the import's namespace value exactly like the host load's. A
         * session without the FFI emission input emits no FFI load: the
         * extern-C import's op keeps the landed no-op load (the trace
         * session's loaded surface is the scenario seam's).
         * {@code COMPILED}/{@code STDLIB} imports keep the landed no-op
         * realization.</p>
         */
        private void emitModuleImport(SemanticOp op) {
            KindPayload.ModuleImportPayload payload =
                (KindPayload.ModuleImportPayload) op.payload();
            emitStart(op);
            if (payload.kind() == ModuleImportKind.HOST && hostSurface != null) {
                // The host load is a production project realization; a
                // unit/trace session (no declaration surface) keeps the
                // landed no-op arm — its host path is the landed scenario
                // seam, which the production path never reaches. The
                // extern-C declaration import selects its own arm by the
                // declaration kind: the FFI load when the session carries
                // the FFI emission input, the landed no-op otherwise.
                HostDeclarationSurface.DeclarationFacts facts =
                    hostSurface.require(payload.resolvedModule());
                if (facts.kind() == HostDeclarationSurface.DeclarationKind.EXTERN_C) {
                    if (ffiInput != null) {
                        emitFfiLoad(op, payload);
                    }
                } else {
                    emitHostLoad(op, payload, facts);
                }
            }
            emitPlainSuccess(op);
        }

        /**
         * The inline host load of one {@code MODULE_IMPORT(HOST)} op: the
         * declared map is read from the compile's host declaration
         * surface by the resolved module identity (the one descriptor
         * and declaration-order source — never a second producer), and
         * the origin is the import statement's span so the pinned E8011
         * failures carry the import origin.
         */
        private void emitHostLoad(SemanticOp op,
                                  KindPayload.ModuleImportPayload payload,
                                  HostDeclarationSurface.DeclarationFacts facts) {
            // A second alias of one host module emits the same guarded load
            // at its own import position: the first call is the only load of
            // this module per program, and every later import op re-writes
            // the already published surface entry through the same guard.
            ModuleId moduleId = payload.resolvedModule();
            String key = luaString(moduleId.path());
            out.append("__exportSurfaces[").append(key).append("] = ")
                .append("__exportSurfaces[").append(key).append("] or ")
                .append("__rt.load_host(").append(luaString(payload.rawSpecifier()))
                .append(", ").append(hostDeclaredMap(facts)).append(", ")
                .append(loadOriginArgs(op)).append(")\n");
            // The load's registry entry exists from this position on, so
            // a later binding of a provider alias naming this declaration
            // module captures the published loaded table.
            emittedDeclarationLoads.add(moduleId);
        }

        /**
         * The inline FFI load of one {@code MODULE_IMPORT} of an extern-C
         * declaration module (the extern-C admission slice;
         * {@code luajit-ffi-load-emission-and-typed-crossings} F1/F2 and
         * the FFI import and load contract): the four argument literals
         * come from the landed {@link LuaFfiBindingGenerator} over the
         * FFI emission input's generated module — the descriptor's
         * {@code ffi:}-keyed module key, the cdef bundle, the per-class
         * plans with their deferred evaluators, and the forward bindings —
         * with the loader text resolved against the input's manifest
         * directory, and the import statement's own span triplet is the
         * origin, so the pinned {@code FFI_LIBRARY_LOAD}/
         * {@code FFI_SYMBOL_MISSING} failures name the import statement.
         * The provider bindings are the same alias mapping the generator
         * renders, re-pointed at the chunk-global {@code __exportSurfaces}
         * registry instead of a per-module {@code require} (the one-chunk
         * production layout has no per-provider module artifact): one
         * binding per referenced alias in the generator's graph order
         * (first-reference order over the imported function and
         * class-plan references), each capturing the provider module's
         * published surface object by identity, and the bindings literal
         * and the {@code load_ffi} publication following in the pinned
         * order. The evaluator text calls
         * {@code <prefix><alias>.<export>.f(...)}, so a provider must be
         * wrapper-capable — a session unit of the lowered closure (its
         * surface object is created at the chunk top and filled by the
         * module's own {@code EXPORT_PUBLISH} publication, so an entry
         * published later in the program is visible to the evaluator
         * through the captured object) or a covered declaration module
         * whose load this walk already emitted before the binding
         * position (the loaded table the registry holds when the binding
         * captures it). Every other provider — a spec-stdlib module, a
         * declaration module whose load the artifact does not emit or
         * emits after the binding position, and any module outside the
         * closure and the declaration facts — is wrapper-incapable and
         * fails the compile closed (a producer defect the production arm
         * maps to E6005 {@code SHARED_EMITTER_COVERAGE}, staging
         * nothing). An alias that names two provider modules is the same
         * fail-closed producer defect, never a silent first-wins. The
         * registry entry is written with the landed idempotent {@code or}
         * guard, so two aliases of one module share the one loaded table
         * and no second open runs. Nothing here evaluates a plan default,
         * opens a library, or resolves a symbol.
         */
        private void emitFfiLoad(SemanticOp op,
                                 KindPayload.ModuleImportPayload payload) {
            ModuleId moduleId = payload.resolvedModule();
            FfiGeneratedModule module = ffiInput.require(moduleId);
            int ordinal = ++ffiImportCounter;
            String bindingsLocal = "__ffi_bindings_" + ordinal;
            String importPrefix = "__ffi_import_" + ordinal + "_";
            LuaFfiBindingGenerator.Generation generation =
                LuaFfiBindingGenerator.generate(module,
                    ffiInput.manifestDirectory(), bindingsLocal,
                    importPrefix);
            if (generation.failure() != null) {
                throw new IllegalStateException("the extern-C generated"
                    + " module of '" + moduleId.path() + "' cannot be"
                    + " serialized into the load_ffi literals: "
                    + generation.failure().message());
            }
            LuaFfiBindingGenerator.LoadCallParts parts = generation.parts();
            requireOneProviderModulePerAlias(op, payload, moduleId, module);
            for (LuaFfiBindingGenerator.ProviderBinding provider
                    : LuaFfiBindingGenerator.providerBindings(
                        module.bindings())) {
                ModuleId providerId = new ModuleId(provider.importedModulePath());
                if (!isWrapperCapableProvider(providerId)) {
                    throw new IllegalStateException("the extern-C module '"
                        + moduleId.path() + "' (import '"
                        + payload.rawSpecifier() + "' at "
                        + importOriginText(op) + ") binds the provider alias '"
                        + provider.importAlias() + "' to the module '"
                        + provider.importedModulePath() + "', which the"
                        + " artifact does not publish in the wrapper"
                        + " convention before the binding position: the"
                        + " provider is neither a session unit of the"
                        + " lowered closure nor a covered declaration"
                        + " module whose load the emission already emitted"
                        + " (a provider gap — a producer defect)");
                }
                out.append("local ").append(importPrefix)
                    .append(provider.importAlias())
                    .append(" = __exportSurfaces[")
                    .append(luaString(provider.importedModulePath()))
                    .append("] or {}\n");
            }
            out.append("local ").append(bindingsLocal).append(" = ")
                .append(parts.bindingsLiteral()).append("\n");
            String key = luaString(moduleId.path());
            out.append("__exportSurfaces[").append(key).append("] = ")
                .append("__exportSurfaces[").append(key)
                .append("] or __rt.load_ffi(")
                .append(parts.moduleKeyLiteral()).append(", ")
                .append(parts.bundleLiteral()).append(", ")
                .append(parts.plansLiteral()).append(", ")
                .append(bindingsLocal).append(", ")
                .append(loadOriginArgs(op)).append(")\n");
            // The load's registry entry exists from this position on, so
            // a later binding of a provider alias naming this declaration
            // module captures the published loaded table.
            emittedDeclarationLoads.add(moduleId);
        }

        /**
         * The wrapper-capability predicate of one provider module (P2):
         * the artifact must publish the provider's export surface in the
         * wrapper convention before the binding position — either a
         * session unit of the one lowered closure (its surface object is
         * created at the chunk top and filled by the module's own
         * {@code EXPORT_PUBLISH} publication, so an entry published later
         * in the program is visible to the evaluator through the captured
         * object) or a covered declaration module whose load this walk
         * already emitted before the binding position (the loaded table
         * the registry holds when the binding captures it). Every other
         * provider is wrapper-incapable and fails the compile closed —
         * wrapper capability is a property of the artifact's publication,
         * never of the module kind alone.
         */
        private boolean isWrapperCapableProvider(ModuleId providerId) {
            return units.containsKey(providerId)
                || emittedDeclarationLoads.contains(providerId);
        }

        /**
         * The one-binding-per-alias invariant's fail-closed half (P1): one
         * import alias resolves exactly one provider module, so a
         * reference that names a provider module different from the
         * alias's already-bound provider module is a producer defect —
         * never a silent first-wins. The two reference lists are the
         * validator's frozen graph-ordered facts.
         */
        private void requireOneProviderModulePerAlias(SemanticOp op,
                KindPayload.ModuleImportPayload payload, ModuleId moduleId,
                FfiGeneratedModule module) {
            Map<String, String> aliasProviders = new LinkedHashMap<>();
            for (FfiImportedFunctionReference ref
                    : module.bindings().importedFunctions()) {
                requireStableAliasProvider(op, payload, moduleId,
                    aliasProviders, ref.importAlias(),
                    ref.importedModulePath());
            }
            for (FfiImportedClassPlanReference ref
                    : module.bindings().importedClassPlans()) {
                requireStableAliasProvider(op, payload, moduleId,
                    aliasProviders, ref.importAlias(),
                    ref.importedModulePath());
            }
        }

        /** One alias's provider-module agreement check. */
        private void requireStableAliasProvider(SemanticOp op,
                KindPayload.ModuleImportPayload payload, ModuleId moduleId,
                Map<String, String> aliasProviders, String importAlias,
                String importedModulePath) {
            String bound = aliasProviders.putIfAbsent(importAlias,
                importedModulePath);
            if (bound != null && !bound.equals(importedModulePath)) {
                throw new IllegalStateException("the extern-C module '"
                    + moduleId.path() + "' (import '"
                    + payload.rawSpecifier() + "' at "
                    + importOriginText(op) + ") binds the provider alias '"
                    + importAlias + "' to two provider modules ('" + bound
                    + "' and '" + importedModulePath + "'): one import"
                    + " alias resolves exactly one provider module (a"
                    + " provider gap — a producer defect)");
            }
        }

        /**
         * The text of one import statement's origin (file, line, column)
         * for a fail-closed provider-gap message: the same origin the
         * load's own {@code FFI_LIBRARY_LOAD}/{@code FFI_SYMBOL_MISSING}
         * failures name.
         */
        private static String importOriginText(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                return op.origin().sourceId() + ":0:0";
            }
            return op.origin().sourceId() + ":" + span.startLine() + ":"
                + span.startColumn();
        }

        /**
         * The declared-map literal of one host declaration module: the
         * declared exports in declaration order, each with its canonical
         * runtime-descriptor text ({@code RuntimeDescriptor.Func} for a
         * function export, the canonical class descriptor for a class
         * export) — the single descriptor text the loader validates.
         */
        private String hostDeclaredMap(
                HostDeclarationSurface.DeclarationFacts facts) {
            StringBuilder sb = new StringBuilder("{");
            boolean first = true;
            for (Map.Entry<String, Type> export : facts.exports().entrySet()) {
                if (!first) {
                    sb.append(", ");
                }
                first = false;
                sb.append("[").append(luaString(export.getKey()))
                    .append("] = ")
                    .append(luaString(hostDescriptorText(export.getValue())));
            }
            return sb.append("}").toString();
        }

        /**
         * The canonical descriptor text of one declared export type
         * (the compiled descriptor service — the only type-to-text
         * producer).
         */
        private String hostDescriptorText(Type type) {
            try {
                return DescriptorService.describe(type).canonicalSpecText();
            } catch (DescriptorService.Defect defect) {
                throw new IllegalStateException("a declared host export carries"
                    + " a type with no runtime representation: "
                    + defect.getMessage() + " (the declaration surface never"
                    + " carries one — a producer defect)", defect);
            }
        }

        /**
         * The literal origin triplet of a construction's call site: the
         * literal's own file, line, and column, so the pinned E8007 the
         * deployed construction entry raises names the literal origin (a
         * span-less op projects the retained {@code "-", 0, 0} triplet).
         */
        private String classLiteralOriginArgs(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                return "\"-\", 0, 0";
            }
            return luaString(op.origin().sourceId()) + ", "
                + span.startLine() + ", " + span.startColumn();
        }

        /**
         * The literal origin triplet of a load's call site: the import
         * statement's own file, line, and column, so every E8011 the
         * loader raises names the import origin.
         */
        private String loadOriginArgs(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                throw new IllegalStateException("the host import " + op.opId()
                    + " carries no source span: the pinned E8011 origin needs"
                    + " the import statement's own origin (a producer defect)");
            }
            return luaString(op.origin().sourceId()) + ", "
                + span.startLine() + ", " + span.startColumn();
        }

        /**
         * MODULE_INIT (E8; ISSUE-0590): the emitted module envelope.
         * The op's START precedes the payload init block (the
         * {@code MODULE_IMPORT}/{@code EXPORT_*}/entry-delegation ops
         * nested under it); the block runs inside a pcall so an
         * uncaught DEAL failure publishes the op's single FAILURE
         * terminal recording {@code FAILED(error)} (no export
         * publication) before the error propagates to the deferred-main
         * wrapper's terminal. The closed
         * {@code UNINITIALIZED -> INITIALIZING -> INITIALIZED} state
         * machine runs in both modes (the production mode's event
         * helpers are no-ops): a re-execution of an initialized module
         * publishes the state without re-running the block; a
         * re-entrant or failed re-execution is a producer defect, never
         * a silent re-run.
         */
        private void emitModuleInit(SemanticOp op) {
            KindPayload.ModuleInitPayload payload =
                (KindPayload.ModuleInitPayload) op.payload();
            requireParentlessModuleInit(op);
            String stateKey = "__moduleStates[" + luaString(payload.module().path()) + "]";
            out.append("if ").append(stateKey).append(" == nil then\n");
            out.append(stateKey).append(" = \"INITIALIZING\"\n");
            emitStart(op);
            out.append("local __initOk, __initErr = pcall(function()\n");
            emitBlockOps(payload.initBlock());
            out.append("end)\n");
            out.append("if not __initOk then\n");
            out.append(stateKey).append(" = \"FAILED\"\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__initErr)");
            out.append("error(__initErr, 0)\n");
            out.append("end\n");
            out.append(stateKey).append(" = \"INITIALIZED\"\n");
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", \"MODULE_INIT\", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, \"state:INITIALIZED\", nil)\n");
            out.append("elseif ").append(stateKey).append(" == \"INITIALIZED\" then\n");
            emitStart(op);
            out.append("__ev(").append(luaString(opKey(op.opId())))
                .append(", \"SUCCESS\", \"MODULE_INIT\", ")
                .append(luaString(op.contract().canonicalDigest())).append(", ")
                .append(luaString(parentKey(op.origin().parentOpId())))
                .append(", {}, \"state:INITIALIZED\", nil)\n");
            out.append("else\n");
            out.append("error(\"a second MODULE_INIT of module ")
                .append(payload.module().path())
                .append(" after a re-entrant or failed init (producer defect)\", 0)\n");
            out.append("end\n");
        }

        private void emitJsonPlan(ClassLayout layout) {
            out.append("__plans[").append(luaString(layout.classId().text()))
                .append("] = {classId = ").append(luaString(layout.classId().text()))
                .append(", fields = {\n");
            for (ClassLayout.FieldLayout field : layout.fields()) {
                out.append("  {name = ").append(luaString(field.name()))
                    .append(", desc = ").append(luaString(jsonDescriptorText(field.descriptor())))
                    .append(", optional = ").append(field.required() ? "false" : "true")
                    .append(", k = ").append(luaString(staticKind(field.descriptor())));
                SemanticOp defaultOp = classDefaultOpOf(layout.classId(), field.name());
                if (defaultOp != null && field.required()) {
                    out.append(", dk = ").append(luaString(opKey(defaultOp.opId())))
                        .append(", dd = ")
                        .append(luaString(defaultOp.contract().canonicalDigest()))
                        .append(", dfn = ").append(defaultFn(defaultOp.opId()));
                }
                out.append("},\n");
            }
            out.append("}}\n");
        }

        /** The class's CLASS_DEFAULT op of one field, or null (no declared default). */
        private SemanticOp classDefaultOpOf(ClassId classId, String field) {
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

        /**
         * The JSON plan descriptor text: the boundary descriptor text with
         * the JSON walk's {@code nullable:INNER} spelling (the walk's
         * closed kind grammar).
         */
        private static String jsonDescriptorText(RuntimeDescriptor descriptor) {
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                return "nullable:" + jsonDescriptorText(nullable.inner());
            }
            if (descriptor instanceof RuntimeDescriptor.Array array) {
                return "array(" + jsonDescriptorText(array.element()) + ")";
            }
            return descriptorText(descriptor);
        }

        /**
         * JSON_FROM_CLASS (E7/K-D8): the shared walk ({@code __jsonFromClassOp})
         * over the class's emitted plan — the payload's JSON text operand
         * resolves exactly once; the walk runs the per-site CLASS_DEFAULT
         * children (their own START/terminal events) for omitted
         * required-present defaulted fields and publishes the tagged
         * instance, or language null on any syntax/extra-key/decode/
         * default/validation failure (the {@code JSON_FROM_NULL}
         * projection; a failing default child keeps its completed
         * effects).
         */
        private void emitJsonFromClass(SemanticOp op) {
            KindPayload.JsonFromClassPayload payload =
                (KindPayload.JsonFromClassPayload) op.payload();
            emitStart(op);
            String target = slot((ValueId) op.result());
            out.append(target).append(" = __jsonFromClassOp(")
                .append(luaString(payload.layout().classId().text())).append(", ")
                .append(slot(payload.jsonString())).append(")\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType());
        }

        /**
         * JSON_TO_CLASS (E7/K-D10): the shared walk over the class's
         * emitted plan — the root identity check, the declaration-order
         * field serialization, and the first failing position's
         * {@code JSON_TO_ERROR} projection (E8001
         * {@code value at {fieldPath} is not JSON serializable: {actual}}
         * at the op origin, no cause, active frames); success publishes
         * the deterministic RFC-8259 text.
         */
        private void emitJsonToClass(SemanticOp op) {
            KindPayload.JsonToClassPayload payload =
                (KindPayload.JsonToClassPayload) op.payload();
            emitStart(op);
            out.append("__jokT, __jresT, __jpathT, __jactT = __jsonToClassOp(")
                .append(luaString(payload.layout().classId().text())).append(", ")
                .append(slot(payload.classValue())).append(")\n");
            out.append("if not __jokT then\n");
            out.append("__eT = __failExpr(\"E8001\", \"value at \"..__jpathT..\" is "
                + "not JSON serializable: \"..__jactT, ")
                .append(luaString(originOf(op))).append(", nil, nil)\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "__errtext(__eT)");
            out.append("error(__eT, 0)\n");
            out.append("end\n");
            out.append(slot((ValueId) op.result())).append(" = __jresT\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }

        /**
         * The MODULE_INIT structural-parent contract: the module-level
         * envelope op is parentless (its trace parent is the absent
         * structural parent). A recorded parent is a producer defect —
         * the orchestrator's fail-closed gate converts the throw into
         * E6005, never a silent re-parenting.
         */
        private static void requireParentlessModuleInit(SemanticOp op) {
            if (op.origin().parentOpId() != null) {
                throw new IllegalStateException("MODULE_INIT " + op.opId()
                    + " records the structural parent " + op.origin().parentOpId()
                    + " (the module-level envelope op is parentless — a wrong parent is a "
                    + "producer defect, never a silent re-parenting)");
            }
        }

        /** The unit's lowerer-produced MODULE_INIT op, or null (hand-built units). */
        private SemanticOp moduleInitOpOf(LoweredModuleUnit moduleUnit) {
            for (SemanticOp op : moduleUnit.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_INIT) {
                    return op;
                }
            }
            return null;
        }

        /**
         * {@code EXPORT_READ} — the per-kind read resolution (M2/M4/M5/M6):
         * a COMPILED read resolves the owning module's published value
         * through the chunk-global program-scoped export-surface registry
         * (the entry's {@code __val} field); a HOST/FFI read resolves the
         * same registry's entry itself — for a HOST module the surface is
         * the loaded module table {@code __rt.load_host} returns, so the
         * entry is the host ABI's value and the read never re-wraps it; an
         * absent surface or entry projects the {@code __MISSING} sentinel
         * in both cases; a STDLIB read publishes the in-target cataloged
         * callable of the closed catalog row (the one memoized accessor's
         * entry — the identical object the whole-surface population writes,
         * carrying the row's declared signature and canonical spec text,
         * never the reading site's). The emitted read expression is
         * identical in trace and production mode. In a project session a
         * COMPILED read whose owner module is not among the closure's units
         * is a producer defect and fails the emission closed; a per-unit
         * session never fails closed for a foreign owner (the owner's own
         * chunk publishes the surface of the same program).
         */
        private void emitExportRead(SemanticOp op) {
            KindPayload.ExportReadPayload payload =
                (KindPayload.ExportReadPayload) op.payload();
            // The read's module kind is the session's own recorded import
            // fact (M6). A module the session records no import fact for —
            // the test-only class-core carrier sessions, whose units carry
            // no module-level import op — keeps the landed interim
            // realization (the residual kind arm's real carrier surface);
            // the production and
            // conformance sessions record every resolved import, so a
            // COMPILED read is never guessed from a path.
            ModuleImportKind kind = importKinds.get(payload.module());
            if (kind == ModuleImportKind.COMPILED && projectSession
                    && !units.containsKey(payload.module())) {
                throw new IllegalStateException("the compiled EXPORT_READ of export '"
                    + payload.name() + "' of module '" + payload.module().path()
                    + "' resolves an owner module outside the project session's"
                    + " closure (the one lowering resolves every COMPILED import to a"
                    + " closure module — a producer defect)");
            }
            emitStart(op);
            if (kind == ModuleImportKind.COMPILED) {
                out.append(slot((ValueId) op.result())).append(" = __exportValue(")
                    .append(luaString(payload.module().path())).append(", ")
                    .append(luaString(payload.name())).append(")\n");
            } else if (kind == ModuleImportKind.HOST) {
                out.append(slot((ValueId) op.result())).append(" = __exportHostValue(")
                    .append(luaString(payload.module().path())).append(", ")
                    .append(luaString(payload.name())).append(")\n");
            } else if (kind == ModuleImportKind.STDLIB) {
                // The read publishes the catalog row's callable entry itself
                // (M4): the memoized accessor the whole-surface population
                // uses, so the read and the surface hold the identical
                // object and the read never builds a per-read value.
                out.append(slot((ValueId) op.result())).append(" = __stdlibEntry(")
                    .append(stdlibRowArgs(stdlibRowOf(payload.module().path(),
                        payload.name()))).append(")\n");
            } else {
                // The residual kind arm (a session whose unit records no
                // import fact for the read's module): the placeholder
                // publishes the memoized intrinsic carrier the identity's
                // own registration resolves, and a fresh opaque export
                // carrier otherwise (the landed per-read allocation, now a
                // real carrier surface) — never the removed marker and
                // never a re-read of the read's own slot.
                String carrier = registeredIntrinsicCarrierExpr((ValueId) op.result());
                out.append(slot((ValueId) op.result())).append(" = ")
                    .append(carrier == null ? exportPlaceholderCarrier() : carrier)
                    .append("\n");
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType());
        }
    }

    // =========================================================================
    // The Lua runtime prelude (byte-identical protocol output)
    // =========================================================================

    /**
     * The shared JSON algorithm realization (E7/K-D8/K-D10) of the
     * {@code JSON_FROM_CLASS}/{@code JSON_TO_CLASS} arms: the closed E8
     * RFC-8259 parse and canonical text algorithms plus the class walk
     * over the per-class plans the session records in {@code __plans}
     * (classId → plan: declaration-order fields with descriptor,
     * optionality, default-child metadata, and the owner factory
     * metadata of the nested-decode seam). The walk runs zero boundary
     * children; the class-default/class-factory events carry the plan's
     * recorded keys and digests. All syntax/decode/shape failures return
     * language null (the {@code JSON_FROM_NULL} projection); the
     * to-json walk returns the first declaration-order failure
     * {@code (fieldPath, actual)} for the arm's {@code JSON_TO_ERROR}
     * projection.
     */
    private static final String JSON_PRELUDE = """
-- ==== shared JSON algorithm (E7/K-D8/K-D10 realization) ====
-- The closed E8 RFC-8259 parse and canonical text algorithms plus the
-- flat-layout class walk of the JSON_FROM_CLASS/JSON_TO_CLASS arms. The
-- walk consumes the per-class plans the emitter records in __plans
-- (classId -> plan: declaration-order fields with descriptor,
-- optionality, and the per-field CLASS_DEFAULT child metadata).
-- Nested @jsonable class fields fail closed at emit time (a producer
-- defect naming the nested shape), never silently.
-- Byte-exactness: no backslash escapes appear in this source; quote and
-- backslash bytes are emitted through string.char.
local __JSONSYNTAX = setmetatable({}, {__tostring = function() return "json-syntax" end})
local __JNULL = setmetatable({}, {__tostring = function() return "json-null" end})
local __JSON_MAX_DEPTH = 512
local __plans = {}
local __BS = string.char(92)
local __QT = string.char(34)
local function __jsonIsObject(v)
  return type(v) == "table" and v.__jo == true
end
local function __jsonIsArray(v)
  return type(v) == "table" and v.__ja == true
end
local function __jsonEmptyObject()
  return {__jo = true, __jkeys = {}, __jnum = {}}
end
local function __jsonUtf8(cp)
  if cp < 0x80 then return string.char(cp) end
  if cp < 0x800 then
    return string.char(0xC0 + math.floor(cp / 0x40), 0x80 + cp % 0x40)
  end
  if cp < 0x10000 then
    return string.char(0xE0 + math.floor(cp / 0x1000),
      0x80 + math.floor(cp / 0x40) % 0x40, 0x80 + cp % 0x40)
  end
  return string.char(0xF0 + math.floor(cp / 0x40000),
    0x80 + math.floor(cp / 0x1000) % 0x40,
    0x80 + math.floor(cp / 0x40) % 0x40, 0x80 + cp % 0x40)
end
local function __jsonValidUtf8(s)
  local i = 1
  local n = #s
  while i <= n do
    local b = string.byte(s, i)
    local len
    if b < 0x80 then len = 1
    elseif b >= 0xC2 and b <= 0xDF then len = 2
    elseif b >= 0xE0 and b <= 0xEF then len = 3
    elseif b >= 0xF0 and b <= 0xF4 then len = 4
    else return false end
    if i + len - 1 > n then return false end
    local cp
    if len == 1 then cp = b
    elseif len == 2 then cp = b - 0xC0
    elseif len == 3 then cp = b - 0xE0
    else cp = b - 0xF0 end
    for k = 1, len - 1 do
      local c = string.byte(s, i + k)
      if c < 0x80 or c > 0xBF then return false end
      cp = cp * 0x40 + (c - 0x80)
    end
    if len == 2 and cp < 0x80 then return false end
    if len == 3 and cp < 0x800 then return false end
    if len == 4 and cp < 0x10000 then return false end
    if cp > 0x10FFFF then return false end
    if cp >= 0xD800 and cp <= 0xDFFF then return false end
    i = i + len
  end
  return true
end
-- The E8 parse: every number carries its per-occurrence lexical variant
-- in the container's __jnum set — a digits-only in-range integer form is
-- the int variant, every other numeric form the number variant, exactly
-- the classification the shared parser and the JVM keep — so the
-- language carriers can mark their slots and the int descriptor admits
-- only integer lexical carriers; duplicate keys keep the last value, the
-- first position, and the last value's own variant; any syntax defect
-- returns __JSONSYNTAX.
local function __jsonParse(s)
  local pos = 1
  local len = #s
  local function skipws()
    while pos <= len do
      local b = string.byte(s, pos)
      if b == 32 or b == 9 or b == 10 or b == 13 then pos = pos + 1
      else break end
    end
  end
  local parseValue
  local function parseString()
    pos = pos + 1
    local out = {}
    while true do
      if pos > len then return nil end
      local c = string.sub(s, pos, pos)
      if c == __QT then
        pos = pos + 1
        return table.concat(out)
      elseif c == __BS then
        local e = string.sub(s, pos + 1, pos + 1)
        pos = pos + 2
        if e == __QT then out[#out + 1] = __QT
        elseif e == __BS then out[#out + 1] = __BS
        elseif e == "/" then out[#out + 1] = "/"
        elseif e == "b" then out[#out + 1] = string.char(8)
        elseif e == "f" then out[#out + 1] = string.char(12)
        elseif e == "n" then out[#out + 1] = string.char(10)
        elseif e == "r" then out[#out + 1] = string.char(13)
        elseif e == "t" then out[#out + 1] = string.char(9)
        elseif e == "u" then
          local hex = string.sub(s, pos, pos + 3)
          if #hex < 4 or not string.match(hex, "^%x%x%x%x$") then return nil end
          local cp = tonumber(hex, 16)
          pos = pos + 4
          if cp >= 0xD800 and cp <= 0xDBFF then
            if string.sub(s, pos, pos + 1) == __BS .. "u" then
              local hex2 = string.sub(s, pos + 2, pos + 5)
              if #hex2 == 4 and string.match(hex2, "^%x%x%x%x$") then
                local lo = tonumber(hex2, 16)
                if lo >= 0xDC00 and lo <= 0xDFFF then
                  pos = pos + 6
                  cp = 0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00)
                end
              end
            end
            if cp >= 0xD800 and cp <= 0xDFFF then return nil end
          elseif cp >= 0xDC00 and cp <= 0xDFFF then
            return nil
          end
          out[#out + 1] = __jsonUtf8(cp)
        else
          return nil
        end
      else
        local b = string.byte(c)
        if b < 32 then return nil end
        out[#out + 1] = c
        pos = pos + 1
      end
    end
  end
  local function parseNumber()
    local start = pos
    if string.sub(s, pos, pos) == "-" then pos = pos + 1 end
    if pos > len then return nil end
    local c = string.sub(s, pos, pos)
    if c == "0" then
      pos = pos + 1
      if pos <= len and string.match(string.sub(s, pos, pos), "%d") then
        return nil
      end
    elseif string.match(c, "[1-9]") then
      while pos <= len and string.match(string.sub(s, pos, pos), "%d") do
        pos = pos + 1
      end
    else
      return nil
    end
    local integral = true
    if pos <= len and string.sub(s, pos, pos) == "." then
      integral = false
      pos = pos + 1
      if pos > len or not string.match(string.sub(s, pos, pos), "%d") then
        return nil
      end
      while pos <= len and string.match(string.sub(s, pos, pos), "%d") do
        pos = pos + 1
      end
    end
    if pos <= len then
      local e = string.sub(s, pos, pos)
      if e == "e" or e == "E" then
        integral = false
        pos = pos + 1
        local sg = string.sub(s, pos, pos)
        if sg == "+" or sg == "-" then pos = pos + 1 end
        if pos > len or not string.match(string.sub(s, pos, pos), "%d") then
          return nil
        end
        while pos <= len and string.match(string.sub(s, pos, pos), "%d") do
          pos = pos + 1
        end
      end
    end
    local text = string.sub(s, start, pos - 1)
    local value = tonumber(text)
    if value == nil then return nil end
    if integral and value >= -2147483648 and value <= 2147483647 then
      -- The signed32 integer lexical form: the int variant with -0
      -- normalized to 0 (the shared parser's exact rule).
      if value == 0 then value = 0 end
      return value, false
    end
    return value, true
  end
  parseValue = function(depth)
    if depth > __JSON_MAX_DEPTH then return nil end
    skipws()
    if pos > len then return nil end
    local c = string.sub(s, pos, pos)
    if c == "{" then
      pos = pos + 1
      local obj = {__jo = true, __jkeys = {}, __jnum = {}}
      skipws()
      if pos <= len and string.sub(s, pos, pos) == "}" then
        pos = pos + 1
        return obj
      end
      while true do
        skipws()
        if pos > len or string.sub(s, pos, pos) ~= __QT then return nil end
        local key = parseString()
        if key == nil then return nil end
        skipws()
        if pos > len or string.sub(s, pos, pos) ~= ":" then return nil end
        pos = pos + 1
        local value, numberVariant = parseValue(depth + 1)
        if value == nil then return nil end
        if obj[key] == nil then obj.__jkeys[#obj.__jkeys + 1] = key end
        obj[key] = value
        if numberVariant then obj.__jnum[key] = true else obj.__jnum[key] = nil end
        skipws()
        if pos > len then return nil end
        c = string.sub(s, pos, pos)
        if c == "," then pos = pos + 1
        elseif c == "}" then pos = pos + 1; return obj
        else return nil end
      end
    elseif c == "[" then
      pos = pos + 1
      local arr = {__ja = true, __n = 0, __jnum = {}}
      skipws()
      if pos <= len and string.sub(s, pos, pos) == "]" then
        pos = pos + 1
        return arr
      end
      while true do
        local value, numberVariant = parseValue(depth + 1)
        if value == nil then return nil end
        arr.__n = arr.__n + 1
        arr[arr.__n] = value
        if numberVariant then arr.__jnum[arr.__n] = true end
        skipws()
        if pos > len then return nil end
        c = string.sub(s, pos, pos)
        if c == "," then pos = pos + 1
        elseif c == "]" then pos = pos + 1; return arr
        else return nil end
      end
    elseif c == __QT then
      local str = parseString()
      if str == nil then return nil end
      return str
    elseif c == "t" then
      if string.sub(s, pos, pos + 3) == "true" then pos = pos + 4; return true end
      return nil
    elseif c == "f" then
      if string.sub(s, pos, pos + 4) == "false" then pos = pos + 5; return false end
      return nil
    elseif c == "n" then
      if string.sub(s, pos, pos + 3) == "null" then pos = pos + 4; return __JNULL end
      return nil
    elseif c == "-" or string.match(c, "%d") then
      return parseNumber()
    end
    return nil
  end
  local value = parseValue(0)
  if value == nil then return __JSONSYNTAX end
  skipws()
  if pos <= len then return __JSONSYNTAX end
  return value
end
-- The Java-Double.toString-compatible canonical number text (shortest
-- round-trippable digits, always one fractional digit, E-notation
-- outside [1e-3, 1e7)).
local function __jsonNumText(v)
  if v ~= v or v == math.huge or v == -math.huge then return nil end
  if v == 0 then
    if 1 / v < 0 then return "-0.0" end
    return "0.0"
  end
  local sign = ""
  if v < 0 then sign = "-"; v = -v end
  local digits = nil
  local exp = nil
  for p = 1, 17 do
    local text = string.format("%." .. (p - 1) .. "e", v)
    if tonumber(text) == v then
      local lead, rest, e = string.match(text, "^(%d)%.?(%d*)e([%+%-]?%d+)$")
      if lead ~= nil then
        digits = lead .. rest
        exp = tonumber(e)
        break
      end
    end
  end
  if digits == nil then
    return nil
  end
  digits = string.gsub(digits, "0+$", "")
  if digits == "" then digits = "0" end
  local text
  if exp >= -3 and exp < 7 then
    if exp >= 0 then
      if #digits > exp + 1 then
        text = string.sub(digits, 1, exp + 1) .. "." .. string.sub(digits, exp + 2)
      else
        text = digits .. string.rep("0", exp + 1 - #digits) .. ".0"
      end
    else
      text = "0." .. string.rep("0", -exp - 1) .. digits
    end
  else
    local mantissa
    if #digits > 1 then
      mantissa = string.sub(digits, 1, 1) .. "." .. string.sub(digits, 2)
    else
      mantissa = string.sub(digits, 1, 1) .. ".0"
    end
    text = mantissa .. "E" .. tostring(exp)
  end
  return sign .. text
end
local function __jsonEscapeString(s)
  local out = {}
  for i = 1, #s do
    local b = string.byte(s, i)
    if b == 34 then out[#out + 1] = __BS .. __QT
    elseif b == 92 then out[#out + 1] = __BS .. __BS
    elseif b == 8 then out[#out + 1] = __BS .. "b"
    elseif b == 12 then out[#out + 1] = __BS .. "f"
    elseif b == 10 then out[#out + 1] = __BS .. "n"
    elseif b == 13 then out[#out + 1] = __BS .. "r"
    elseif b == 9 then out[#out + 1] = __BS .. "t"
    elseif b < 32 then out[#out + 1] = __BS .. "u" .. string.format("%04x", b)
    else out[#out + 1] = string.sub(s, i, i) end
  end
  return table.concat(out)
end
local function __jsonKindOf(desc)
  if string.sub(desc, 1, 6) == "array(" then return "array", string.sub(desc, 7, -2) end
  if string.sub(desc, 1, 9) == "nullable:" then return "nullable", string.sub(desc, 10) end
  if string.sub(desc, 1, 1) == "@" then return "class", desc end
  return desc, nil
end
local function __jsonKnownField(plan, name)
  local fields = plan.fields
  for i = 1, #fields do
    if fields[i].name == name then return true end
  end
  return false
end
-- One CLASS_DEFAULT child execution with its own START/terminal events
-- (the detached default op's recorded key/digest, parent "-").
local function __jsonDefaultRun(f)
  __ev(f.dk, "START", "CLASS_DEFAULT", f.dd, "-", {}, nil, nil)
  local ok, produced = pcall(f.dfn)
  if not ok then
    __ev(f.dk, "FAILURE", "CLASS_DEFAULT", f.dd, "-", {}, nil, __errtext(produced))
    return false
  end
  __ev(f.dk, "SUCCESS", "CLASS_DEFAULT", f.dd, "-", {}, __atom(f.k, produced), nil)
  return true, produced
end
-- The language carrier of one parsed JSON subtree: the shared table
-- carrier's full marker set — the presence map __keys, the
-- first-insertion order list __order (the TABLE_NEW / JSON_PARSE
-- carriers'), and the per-slot number marks __nK — so every carrier
-- consumer (TABLE_KEYS, JSON_STRINGIFY, the member/index writes and
-- deletes, and the read-side variant materialization) works on a
-- decoded table exactly as on a constructed one. The marks follow the
-- parser's per-occurrence lexical int/number classification; a nested
-- container carries its own markers.
local function __jsonToLanguage(v)
  if __jsonIsArray(v) then
    local out = {__a = true, __n = v.__n, __nK = {}}
    for i = 1, v.__n do
      local element = v[i]
      if element == __JNULL then out[i] = __NULL
      elseif __jsonIsObject(element) or __jsonIsArray(element) then
        out[i] = __jsonToLanguage(element)
      else
        out[i] = element
        if v.__jnum[i] == true then out.__nK[i] = true end
      end
    end
    return out
  end
  local out = {__t = true, __keys = {}, __order = {}, __nK = {}}
  for i = 1, #v.__jkeys do
    local key = v.__jkeys[i]
    local element = v[key]
    __orderAdd(out, key)
    if element == __JNULL then out[key] = __NULL
    elseif __jsonIsObject(element) or __jsonIsArray(element) then
      out[key] = __jsonToLanguage(element)
    else
      out[key] = element
      if v.__jnum[key] == true then out.__nK[key] = true end
    end
  end
  return out
end
-- The final descriptor conformance check of the walk (K-D8 step 7).
local function __jsonConforms(desc, v)
  local kind, inner = __jsonKindOf(desc)
  if kind == "null" then return v == nil end
  if kind == "boolean" then return type(v) == "boolean" end
  if kind == "int" then
    return type(v) == "number" and v == math.floor(v)
      and v >= -2147483648 and v <= 2147483647
  end
  if kind == "number" then return type(v) == "number" end
  if kind == "string" then return type(v) == "string" and __jsonValidUtf8(v) end
  if kind == "table" then return type(v) == "table" and v.__t == true end
  if kind == "array" then
    if type(v) ~= "table" or v.__a ~= true then return false end
    for i = 1, v.__n do
      local element = v[i]
      if element == __NULL then element = nil end
      if element == nil then return false end
      if not __jsonConforms(inner, element) then return false end
    end
    return true
  end
  if kind == "nullable" then
    if v == nil then return true end
    return __jsonConforms(inner, v)
  end
  return kind ~= "class"
end
-- The provided-field decode of one declared descriptor (K-D8 step 4).
-- The fourth argument is the raw value's own number variant (the
-- parser's per-occurrence lexical classification; meaningful for
-- numbers): an int descriptor admits only an integer lexical carrier
-- (the oracle's Int-only rule), a number descriptor admits both forms
-- and publishes the number variant (its Int case converts exactly) —
-- so every decoded scalar keeps its own variant, and the decoded
-- container carriers record their slots' variants for the
-- read/write/JSON_STRINGIFY consumers.
local function __jsonDecodeRaw(desc, v, depth, numberVariant)
  if depth > __JSON_MAX_DEPTH then return false end
  local kind, inner = __jsonKindOf(desc)
  if kind == "null" then
    if v == __JNULL then return true, nil end
    return false
  elseif kind == "boolean" then
    if type(v) == "boolean" then return true, v end
    return false
  elseif kind == "int" then
    if type(v) == "number" and not numberVariant and v == math.floor(v)
        and v >= -2147483648 and v <= 2147483647 then
      return true, v, "int"
    end
    return false
  elseif kind == "number" then
    if type(v) == "number" then return true, v, "number" end
    return false
  elseif kind == "string" then
    if type(v) == "string" and __jsonValidUtf8(v) then return true, v end
    return false
  elseif kind == "table" then
    if __jsonIsObject(v) then return true, __jsonToLanguage(v) end
    if __jsonIsArray(v) and v.__n == 0 then
      return true, {__t = true, __keys = {}, __order = {}, __nK = {}}
    end
    return false
  elseif kind == "array" then
    if not __jsonIsArray(v) then return false end
    local out = {__a = true, __n = v.__n, __nK = {}}
    for i = 1, v.__n do
      local ok, element, elementVariant =
        __jsonDecodeRaw(inner, v[i], depth + 1, v.__jnum[i] == true)
      if not ok then return false end
      out[i] = (element == nil) and __NULL or element
      if elementVariant == "number" then out.__nK[i] = true end
    end
    return true, out
  elseif kind == "nullable" then
    if v == __JNULL then return true, nil end
    return __jsonDecodeRaw(inner, v, depth, numberVariant)
  elseif kind == "class" then
    error("a nested @jsonable class field (" .. desc .. ") has no shared JSON walk "
      .. "in this slice (producer defect, the nested shape is not emitted)", 0)
  end
  return false
end
local function __jsonInstanceOf(plan, fields, present, values)
  local inst = {__c = true, __id = plan.classId, __f = {}, __p = {}}
  for i = 1, #fields do
    local f = fields[i]
    if present[f.name] then
      local value = values[f.name]
      inst.__f[f.name] = (value == nil) and __NULL or value
      inst.__p[f.name] = true
    end
  end
  return inst
end
-- The JSON_FROM_CLASS walk: the tagged instance, or language null on
-- every listed failure (the JSON_FROM_NULL projection).
local function __jsonFromClassOp(planName, text)
  local plan = __plans[planName]
  if plan == nil then
    error("JSON_FROM_CLASS has no plan " .. planName .. " (producer defect)", 0)
  end
  local doc = __jsonParse(text)
  if doc == __JSONSYNTAX or doc == __JNULL then return nil end
  if __jsonIsArray(doc) and doc.__n == 0 then doc = __jsonEmptyObject() end
  if not __jsonIsObject(doc) then return nil end
  local fields = plan.fields
  for i = 1, #doc.__jkeys do
    if not __jsonKnownField(plan, doc.__jkeys[i]) then return nil end
  end
  local values = {}
  local provided = {}
  for i = 1, #fields do
    local f = fields[i]
    if doc[f.name] ~= nil then
      local ok, decoded = __jsonDecodeRaw(f.desc, doc[f.name], 0,
        doc.__jnum[f.name] == true)
      if not ok then return nil end
      values[f.name] = decoded
      provided[f.name] = true
    end
  end
  for i = 1, #fields do
    local f = fields[i]
    if not provided[f.name] and not f.optional then
      if f.dfn == nil then return nil end
      local ok, produced = __jsonDefaultRun(f)
      if not ok then return nil end
      values[f.name] = produced
      provided[f.name] = true
    end
  end
  for i = 1, #fields do
    local f = fields[i]
    if provided[f.name] and not __jsonConforms(f.desc, values[f.name]) then
      return nil
    end
  end
  return __jsonInstanceOf(plan, fields, provided, values)
end
-- The JSON_TO_CLASS walk: (true, text) or (false, nil, fieldPath,
-- actual) for the JSON_TO_ERROR projection. Table fields serialize
-- their present keys in ascending key order (the shared Lua table
-- carrier records key presence, not insertion order).
local function __jsonToClassOp(planName, root)
  local plan = __plans[planName]
  if plan == nil then
    error("JSON_TO_CLASS has no plan " .. planName .. " (producer defect)", 0)
  end
  local failurePath = nil
  local failureActual = nil
  local function fail(path, actual)
    failurePath = path
    failureActual = actual
    return nil
  end
  local encodeField
  local encodeTableValue
  local encodeArrayValue
  local function actualOf(v)
    if v == nil then return "null" end
    local t = type(v)
    if t == "boolean" then return "boolean" end
    if t == "number" then return "number" end
    if t == "string" then
      if not __jsonValidUtf8(v) then return "invalid-unicode" end
      return "string"
    end
    if t == "table" then
      if v.__a then return "array" end
      if v.__c then return "class:" .. v.__id end
      return "table"
    end
    return t
  end
  encodeTableValue = function(tv, tpath, visited)
    if visited[tv] then return fail(tpath, "table") end
    visited[tv] = true
    local keys = {}
    for k, _ in pairs(tv.__keys) do keys[#keys + 1] = k end
    table.sort(keys)
    local out = {"{"}
    for i = 1, #keys do
      local key = keys[i]
      local element = tv[key]
      if element == __NULL then element = nil end
      if i > 1 then out[#out + 1] = "," end
      out[#out + 1] = __QT .. __jsonEscapeString(key) .. __QT .. ":"
      local elementPath = (tpath == "") and key or (tpath .. "." .. key)
      if element == nil then out[#out + 1] = "null"
      elseif type(element) == "boolean" then out[#out + 1] = tostring(element)
      elseif type(element) == "number" then
        local text = __jsonNumText(element)
        if text == nil then return fail(elementPath, "number") end
        out[#out + 1] = text
      elseif type(element) == "string" then
        if not __jsonValidUtf8(element) then
          return fail(elementPath, "invalid-unicode")
        end
        out[#out + 1] = __QT .. __jsonEscapeString(element) .. __QT
      elseif type(element) == "table" then
        if element.__a then
          local nested = encodeArrayValue(element, elementPath, visited)
          if nested == nil then return nil end
          out[#out + 1] = nested
        elseif element.__t then
          local nested = encodeTableValue(element, elementPath, visited)
          if nested == nil then return nil end
          out[#out + 1] = nested
        else
          return fail(elementPath, actualOf(element))
        end
      else
        return fail(elementPath, actualOf(element))
      end
    end
    visited[tv] = nil
    out[#out + 1] = "}"
    return table.concat(out)
  end
  encodeArrayValue = function(av, apath, visited)
    if visited[av] then return fail(apath, "array") end
    visited[av] = true
    local out = {"["}
    for i = 1, av.__n do
      local element = av[i]
      if element == __NULL then element = nil end
      local elementPath = apath .. "[" .. (i - 1) .. "]"
      if i > 1 then out[#out + 1] = "," end
      if element == nil then out[#out + 1] = "null"
      elseif type(element) == "boolean" then out[#out + 1] = tostring(element)
      elseif type(element) == "number" then
        local text = __jsonNumText(element)
        if text == nil then return fail(elementPath, "number") end
        out[#out + 1] = text
      elseif type(element) == "string" then
        if not __jsonValidUtf8(element) then
          return fail(elementPath, "invalid-unicode")
        end
        out[#out + 1] = __QT .. __jsonEscapeString(element) .. __QT
      elseif type(element) == "table" then
        if element.__a then
          local nested = encodeArrayValue(element, elementPath, visited)
          if nested == nil then return nil end
          out[#out + 1] = nested
        elseif element.__t then
          local nested = encodeTableValue(element, elementPath, visited)
          if nested == nil then return nil end
          out[#out + 1] = nested
        else
          return fail(elementPath, actualOf(element))
        end
      else
        return fail(elementPath, actualOf(element))
      end
    end
    visited[av] = nil
    out[#out + 1] = "]"
    return table.concat(out)
  end
  encodeField = function(desc, v, path, visited)
    local kind, inner = __jsonKindOf(desc)
    if kind == "null" then
      if v == nil then return "null" end
      return fail(path, actualOf(v))
    elseif kind == "boolean" then
      if type(v) == "boolean" then return tostring(v) end
      return fail(path, actualOf(v))
    elseif kind == "int" then
      if type(v) == "number" and v == math.floor(v) then return tostring(v) end
      return fail(path, actualOf(v))
    elseif kind == "number" then
      if type(v) == "number" then
        local text = __jsonNumText(v)
        if text == nil then return fail(path, "number") end
        return text
      end
      return fail(path, actualOf(v))
    elseif kind == "string" then
      if type(v) ~= "string" then return fail(path, actualOf(v)) end
      if not __jsonValidUtf8(v) then return fail(path, "invalid-unicode") end
      return __QT .. __jsonEscapeString(v) .. __QT
    elseif kind == "nullable" then
      if v == nil then return "null" end
      return encodeField(inner, v, path, visited)
    elseif kind == "table" then
      if type(v) ~= "table" or v.__t ~= true then return fail(path, actualOf(v)) end
      return encodeTableValue(v, path, visited)
    elseif kind == "array" then
      if type(v) ~= "table" or v.__a ~= true then return fail(path, actualOf(v)) end
      return encodeArrayValue(v, path, visited)
    elseif kind == "class" then
      error("a nested @jsonable class field (" .. desc .. ") has no shared JSON walk "
        .. "in this slice (producer defect, the nested shape is not emitted)", 0)
    end
    return fail(path, actualOf(v))
  end
  if root == nil or type(root) ~= "table" or root.__c ~= true
      or root.__id ~= plan.classId then
    return false, nil, "", "shape"
  end
  local visited = {[root] = true}
  local fields = plan.fields
  local out = {"{"}
  local first = true
  for i = 1, #fields do
    local f = fields[i]
    if not root.__p[f.name] then
      if not f.optional then
        local path = f.name
        return false, nil, path, "missing"
      end
    else
      local raw = root.__f[f.name]
      local value = (raw == __NULL) and nil or raw
      local encoded = encodeField(f.desc, value, f.name, visited)
      if encoded == nil then
        return false, nil, failurePath, failureActual
      end
      if not first then out[#out + 1] = "," end
      first = false
      out[#out + 1] = __QT .. __jsonEscapeString(f.name) .. __QT .. ":"
      out[#out + 1] = encoded
    end
  end
  out[#out + 1] = "}"
  return true, table.concat(out), nil, nil
end
""";

    /**
     * The host-boundary prelude of the production chunk (ISSUE-0651;
     * {@code host-module-load-and-host-call-realization} H3/H7 and the sync
     * host call contract): the declared parameter/return cells of a host
     * call (the loaded runtime matcher's own rule, projected through the
     * pinned E8010 templates at the call origin — the wrapper's parameter
     * cells, run at the call site so the boundary children's trace events
     * carry the pinned projection), the DEAL-function-value to
     * host-facing-wrapper projection of a declared function position, and
     * the bridge the host calls back through. Emitted exactly for a chunk
     * with a HOST-kind import, after the runtime binding it uses.
     */
    private static final String HOST_BOUNDARY_PRELUDE = """
-- The production chunk is the v1.2 profile: the deployed runtime's int32
-- gate uses the pinned v1.2 template ("int out of safe range") for the
-- host cells' int rows, exactly like the emitted boundary checks' own
-- gate. The flag is process-wide and idempotent.
__rt.__INT32 = true
-- The actual-kind token of one host-crossing value (the pinned E8010
-- projections' {actual}): the runtime carrier's own kind, never the Lua
-- table spelling of a DEAL function or number carrier.
local function __hostKindOf(v)
  if v == nil or v == __NULL then return "null" end
  local t = type(v)
  if t ~= "table" then return t end
  if v.__jn then return "number" end
  return t
end
-- The carried class identity of one class value in either
-- representation: the chunk's __c/__id carrier or the loaded runtime's
-- __kind/__classname carrier; nil for every other value. The class-value
-- carrier projection keys on this, so a class-typed crossing never
-- consults the runtime matcher's class row (which requires the runtime
-- representation the DEAL program never holds).
local function __hostClassIdOf(v)
  if type(v) ~= "table" then return nil end
  if v.__kind == "class" then return v.__classname end
  if v.__c then return v.__id end
  return nil
end
-- The declared cell of one class-typed host-crossing position: a value
-- carrying the declared identity passes unchanged in either
-- representation; every other value fails through the pinned E8010
-- projection with the declared identity as expected and the carried
-- identity (or the canonical kind token) as actual — never the runtime
-- matcher's E8001.
local function __hostClassCell(desc, index, v, origin, isReturn)
  local prefix = isReturn and "return value 1 type mismatch: "
    or ("parameter "..index.." type mismatch: ")
  local carried = __hostClassIdOf(v)
  if carried == nil then
    return error(__failExpr("E8010", prefix.."expected class instance",
      origin, desc, __hostKindOf(v)), 0)
  end
  if carried ~= desc then
    return error(__failExpr("E8010", prefix.."expected instance of "..desc
      ..", got "..carried, origin, desc, carried), 0)
  end
  return v
end
-- The chunk-to-wrapper class-value carrier projection (F4): one fresh
-- runtime-representation value built from the source representation's own
-- complete field map — the identity text is the crossing position's
-- declared descriptor, a nested pointer field is projected by the same
-- rule, and a pointer token's own __ptr is carried. The source value is
-- never mutated; a value already carrying the runtime representation
-- passes through. No null mapping exists inside this bridge: C_STRUCT and
-- C_POINTER positions are non-nullable by the declaration policy.
local function __hostClassProject(desc, v)
  if type(v) ~= "table" then return v end
  if v.__kind == "class" then return v end
  if not v.__c then return v end
  local out = {__kind = "class", __classname = desc}
  if v.__ptr ~= nil then out.__ptr = v.__ptr end
  if type(v.__f) == "table" then
    for k, val in pairs(v.__f) do
      if type(val) == "table" and val.__c then
        out[k] = __hostClassProject(val.__id, val)
      else
        out[k] = val
      end
    end
  end
  return out
end
-- The wrapper-to-chunk class-value carrier projection (F4): the declared
-- identity text tags one fresh chunk-representation value whose declared
-- field set is the runtime instance's own non-tag keys (its phase-1
-- admission and phase-2 fill make them exactly the declared fields) and
-- whose pointer token carries its pointer. The source value is never
-- mutated; a value already carrying the chunk representation passes
-- through. The projection runs before the crossing's events, so the trace
-- observes exactly one heap value per class-typed crossing.
local function __hostDealProject(desc, v, origin)
  if type(v) ~= "table" then return v end
  if v.__c then return v end
  if v.__kind ~= "class" then return v end
  if v.__classname ~= desc then
    return error(__failExpr("E8010", "expected instance of "..desc..", got "
      ..tostring(v.__classname), origin, desc, v.__classname), 0)
  end
  local out = {__c = true, __id = desc, __f = {}, __p = {}}
  for k, val in pairs(v) do
    if k ~= "__classname" and k ~= "__kind" and k ~= "__ptr" then
      if type(val) == "table" and val.__kind == "class" then
        out.__f[k] = __hostDealProject(val.__classname, val, origin)
      else
        out.__f[k] = val
      end
      out.__p[k] = true
    end
  end
  if v.__ptr ~= nil then out.__ptr = v.__ptr end
  return out
end
-- The declared parameter cell of a function-typed host position: the
-- loaded matcher's own rule over the DEAL function carrier (byte-exact
-- carried canonical descriptor) or a host-facing wrapper; the pinned
-- E8010 text is the loaded wrapper's own parameter projection.
local function __hostFnParam(desc, inner, index, v, origin)
  if v == nil or v == __NULL then
    if string.sub(desc, 1, 1) == "?" then return __rt.__NULL end
    return error(__failExpr("E8010", "parameter "..index.." type mismatch: expected"
      .." function", origin, desc, __hostKindOf(v)), 0)
  end
  local carried = nil
  if type(v) == "table" then
    if v.__csig ~= nil then carried = v.__csig
    elseif v.__kind == "function" then carried = v.sig end
  end
  if carried == nil then
    return error(__failExpr("E8010", "parameter "..index.." type mismatch: expected"
      .." function", origin, desc, __hostKindOf(v)), 0)
  end
  if carried ~= inner then
    return error(__failExpr("E8010", "parameter "..index.." type mismatch: function"
      .." signature mismatch: expected "..inner..", got "..carried, origin, desc,
      __hostKindOf(v)), 0)
  end
  return v
end
-- The declared parameter cell of one host call: the loaded runtime's own
-- matcher (the wrapper's cell), projected through the pinned E8010
-- parameter template at the call origin. The crossing normalizes the
-- chunk's language-null sentinel to the deployed runtime's own (the two
-- sentinels are distinct values) and back on the return path.
local function __hostParamCell(desc, index, v, origin)
  if v == __NULL then v = __rt.__NULL end
  if string.sub(desc, 1, 1) == "@" then
    return __hostClassCell(desc, index, v, origin, false)
  end
  local ok, checked = pcall(__rt.check_type, desc, v)
  if ok then
    if checked == __rt.__NULL then return __NULL end
    return checked
  end
  local inner = type(checked) == "table" and checked.message or tostring(checked)
  return error(__failExpr("E8010", "parameter "..index.." type mismatch: "..inner,
    origin, desc, __hostKindOf(v)), 0)
end
-- The declared-kind event atom of one host-crossing value (the
-- declared-cell boundaries of the host arms): the deployed runtime's
-- null sentinel and the chunk's own sentinel are the language null, so
-- a null position atomizes as "null" exactly like the oracle's
-- NullValue. The value-derived atom (the completion-value effect) is
-- the prelude's own 1-argument __hostAtom — this helper is
-- deliberately named apart so the two never shadow each other in a
-- chunk that carries both.
local function __hostCellAtom(kind, v)
  if v == nil or v == __NULL or v == __rt.__NULL then return "null" end
  return __atom(kind, v)
end
-- The declared return cell of one host call: the loaded wrapper's own
-- return rule, projected through the pinned E8010 return template, then
-- the host-to-DEAL projection of the admitted value (the language-null
-- sentinel and a declared array position's shared array carrier).
local function __hostToDealArray(v)
  if type(v) ~= "table" or v.__a then return v end
  local out = {__a = true, __n = 0, __nK = {}}
  local n = 0
  for i = 1, #v do
    local element = v[i]
    if element == __rt.__NULL then element = __NULL end
    out[i] = element
    n = i
  end
  out.__n = n
  return out
end
local function __hostReturnCell(desc, v, origin, nothing)
  if nothing and v == nil then
    return error(__failExpr("E8010", "return value 1 type mismatch: expected "..desc
      ..", got nothing", origin, desc, "nothing"), 0)
  end
  if string.sub(desc, 1, 1) == "@" then
    return __hostClassCell(desc, 0, v, origin, true)
  end
  local ok, checked = pcall(__rt.check_type, desc, v)
  if not ok then
    local inner = type(checked) == "table" and checked.message or tostring(checked)
    return error(__failExpr("E8010", "return value 1 type mismatch: "..inner, origin,
      desc, __hostKindOf(v)), 0)
  end
  if checked == __rt.__NULL then return nil end
  if string.sub(desc, 1, 1) == "[" or string.sub(desc, 1, 2) == "?[" then
    return __hostToDealArray(checked)
  end
  return checked
end
-- The DEAL function value call the host performs through the declared
-- function bridge: the carrier's own body runs (its own return cell
-- applies), an adapter carrier runs the D15 protocol.
local function __dealFnValue(w, ...)
  if w.__mode ~= nil then return __adaptInvoke(w, "-", ...) end
  return w.__fn(...)
end
-- The host-facing projection of one declared function position (H7): the
-- declared host wrapper class's LuaJIT twin — a plain Lua function the
-- host calls; a host-facing wrapper passes through unadapted and anything
-- else is left to the parameter cell.
local function __hostFnArg(desc, inner, v)
  if type(v) ~= "table" then return v end
  if v.__kind == "function" then return v end
  if v.__fn == nil then return v end
  local carrier = v
  return {__kind = "function", sig = inner,
          f = function(...) return __dealFnValue(carrier, ...) end}
end
-- The declared host-facing projection of one checked parameter: a
-- declared function position is bridged, every other position's carrier
-- is the Lua value itself (the shared Lua table in both directions). The
-- crossing normalizes the chunk's language-null sentinel to the
-- deployed runtime's own for the loaded matcher.
local function __hostProjectArg(desc, inner, v)
  if v == __NULL then return __rt.__NULL end
  if v == __rt.__NULL then return v end
  if v == nil then return v end
  if inner ~= nil and (string.sub(inner, 1, 1) == "("
      or string.sub(inner, 1, 9) == "async(") then
    return __hostFnArg(desc, inner, v)
  end
  if string.sub(desc, 1, 1) == "@" then
    return __hostClassProject(desc, v)
  end
  return v
end
--- The canonical DEAL error table of one host-boundary failure: the
-- loaded runtime raises the DEALRuntimeError shape ({code, message,
-- file, line, column, expected, actual}); the emitted chunk speaks the
-- __d-tagged carrier every consumer projects, so the host arm converts
-- it once at the boundary and rethrows the identical code, message,
-- expected, actual, and origin.
local function __hostError(e, origin)
  if type(e) ~= "table" then return e end
  if e.__d then return e end
  if e.code == nil or e.message == nil then return e end
  local o = origin
  if e.file ~= nil then
    o = tostring(e.file)..":"..tostring(e.line)..":"..tostring(e.column)
  end
  return __failExpr(e.code, e.message, o, e.expected, e.actual)
end
-- The loaded <C>_defaults entry of one declared host class (ISSUE-0624;
-- semantic-ir-construct-coverage-cutover K10): the declaring module's
-- published surface is the module table the one production load returned
-- (__rt.load_host, E8011 when the mandatory defaults entry is missing or
-- non-table), and the class's defaults entry is that copy-through. An
-- absent surface (the declaring module's MODULE_IMPORT(HOST) load has not
-- run) is a fail-closed producer defect: the load precedes every
-- construction in dependency order.
local function __hostClassDefaults(module, class)
  local surface = __exportSurfaces[module]
  if type(surface) ~= "table" then
    error("the host module '"..module.."' has no published surface before the"
      .." construction of '"..class.."' (the MODULE_IMPORT(HOST) load precedes"
      .." every construction in dependency order — a producer defect)", 0)
  end
  return surface[class.."_defaults"]
end
-- The loaded <C>_plan entry of one declared extern-C C-struct class
-- (ISSUE-0666; struct-plan F1): the declaring module's published surface
-- is the loaded module table the one production load returned
-- (__rt.load_ffi, which retains the validated plan per class under the
-- runtime's own <C>_plan key), and the construction calls
-- __rt.class_plan_ over that entry. An absent surface (the declaring
-- module's MODULE_IMPORT load has not run) is a fail-closed producer
-- defect: the load precedes every construction in dependency order. An
-- absent entry stays the runtime entry's own E8001 plan-shape failure —
-- the loaded plan is the only construction authority, never a silent
-- default.
local function __ffiClassPlan(module, class)
  local surface = __exportSurfaces[module]
  if type(surface) ~= "table" then
    error("the extern-C module '"..module.."' has no published surface before"
      .." the construction of '"..class.."' (the MODULE_IMPORT load precedes"
      .." every construction in dependency order — a producer defect)", 0)
  end
  return surface[class.."_plan"]
end
""";
    private static final String PRELUDE = """
-- ==== shared runtime prelude ====
local __MISSING = setmetatable({}, {__tostring = function() return "missing" end})
local __NULL = setmetatable({}, {__tostring = function() return "null" end})
-- The member-read helper (ISSUE-0239 E10): a present key yields the
-- stored value (a present null is the plain nil stored by the write
-- paths); an absent key yields the internal MISSING sentinel — exactly
-- JvmRuntime.Table.read's present/absent split, so the contextual
-- table-read boundary decides null-vs-error identically on both
-- targets. The __keys marker sub-table is the same one the TABLE_NEW /
-- MEMBER_WRITE / MEMBER_DELETE / INDEX_WRITE / INDEX_DELETE paths
-- maintain, so read and write presence stay consistent. A class
-- instance (E5: __c marker, __id tag, __p presence map, __f field
-- values with the __NULL sentinel for a present null) reads through
-- its presence map — present null yields nil and stays distinguishable
-- from an absent key via the presence map (has()/FIELD_READ).
local function __member(t, k)
  if t.__c then
    if t.__p[k] then
      local v = t.__f[k]
      if v == __NULL then return nil end
      return v
    end
    return __MISSING
  end
  if t.__keys[k] then return t[k] end
  return __MISSING
end
local function __esc(s)
  if s == nil then return "" end
  local out = {}
  for i = 1, #s do
    local c = string.sub(s, i, i)
    local b = string.byte(c)
    if c == "\\\\" then out[#out + 1] = "\\\\\\\\"
    elseif c == "\\n" then out[#out + 1] = "\\\\n"
    elseif c == "\\t" then out[#out + 1] = "\\\\t"
    elseif c == "\\r" then out[#out + 1] = "\\\\r"
    elseif c == ";" then out[#out + 1] = "\\\\u003b"
    elseif c == "|" then out[#out + 1] = "\\\\u007c"
    elseif b < 32 or b == 127 then
      out[#out + 1] = string.format("\\\\u%04x", b)
    else out[#out + 1] = c end
  end
  return table.concat(out)
end
local function __framesText()
  if #__frames == 0 then return "-" end
  return table.concat(__frames, ",")
end
local function __allocId(v)
  local id = __allocIds[v]
  if id == nil then
    id = __allocNext
    __allocNext = __allocNext + 1
    __allocIds[v] = id
  end
  return id
end
local __intrinsicInvoke
-- The conversion intrinsics' memoized carriers (J2; published by the
-- seed's BINDING_INIT, the adapter's producer-less VALUE operand and a
-- residual export-read kind arm whose identity carries a seed
-- registration): one callable, class-tagged
-- carrier per intrinsic kind per program, carrying the intrinsic's
-- declared descriptor text and canonical spec text and no function id,
-- so the landed function row (__bcheck/__fncheck) admits it by its
-- carried signature, __unfn exposes its invoker, and every
-- materialization of one intrinsic is the identical value (functions
-- compare by reference identity). The kind tag `it` and the declared
-- signature texts `sig`/`csig` come from the unit's own
-- IntrinsicFunction registration — never a spelling, never a call
-- site's or an adapter target's signature.
local function __intrinsicFn(it, sig, csig)
  local c = __intrinsicCarriers[it]
  if c == nil then
    c = {__sig = sig, __csig = csig, __fid = nil, __it = it}
    c.__fn = function(...) return __intrinsicInvoke(it, ...) end
    __intrinsicCarriers[it] = c
  end
  return c
end
-- The residual export-read kind arm's placeholder carrier (a session
-- whose unit records no import fact for the read's module — the
-- test-only class-core carrier sessions): a fresh, per-read value
-- carrying the landed opaque export view the oracle projects for that
-- arm (a ()->number function) and the real carrier's interface, so the
-- landed function row admits it exactly as the oracle's view does and
-- the read keeps its own identity (the landed arm's per-read
-- allocation). The memoized intrinsic carrier is published at this arm
-- only when the read's identity carries an IntrinsicFunction
-- registration (the only kind authority).
local function __intrinsicExport()
  return {__fn = function() return nil end, __sig = "function(;number)",
    __csig = "()->number", __fid = nil}
end
-- The compiled export read (M2): the nil-safe accessor of the
-- chunk-global program-scoped export-surface registry. A published
-- entry exposes the compiler-owned __val field (the published value
-- itself — the entry's f projection stays the retained-caller ABI's raw
-- callable); an absent surface, an absent entry, or an entry without a
-- published value projects the __MISSING sentinel, which atomizes as
-- "missing" — exactly the oracle's Value.MissingValue and the JVM
-- runtime's MISSING. The read allocates, wraps, and copies nothing.
local function __exportValue(module, name)
  local surface = __exportSurfaces[module]
  if surface == nil then return __MISSING end
  local entry = surface[name]
  if entry == nil then return __MISSING end
  local value = entry.__val
  if value == nil then return __MISSING end
  return value
end
-- The host/FFI export read (M5): the module surface's entry itself. A
-- HOST module's surface is the loaded module table the MODULE_IMPORT
-- load publishes (__rt.load_host returns the wrapped export table), so
-- the entry is the host ABI's value — the read re-wraps nothing, copies
-- nothing, and runs no host code. An absent surface or entry (the load
-- has not run in this execution) projects the __MISSING sentinel, which
-- atomizes as "missing" — exactly the oracle's Value.MissingValue and the
-- JVM runtime's MISSING.
local function __exportHostValue(module, name)
  local surface = __exportSurfaces[module]
  if surface == nil then return __MISSING end
  local entry = surface[name]
  if entry == nil then return __MISSING end
  return entry
end
-- The numeric value view of one operand: a JSON_PARSE carrier (the
-- int/number-typed value the parsed graph carries) unwraps to its
-- number, a plain value passes through unchanged — the Lua value
-- model's realization of the shared JVM runtime's numberOf/longOf
-- tolerance, so every numeric consumer accepts either representation.
local function __num(v)
  if type(v) == "table" and v.__jn then return v.d end
  return v
end
-- The number-typed slot mark of the shared JSON_STRINGIFY walker: the
-- Lua value model carries no int/number distinction for plain numbers,
-- so every container write records the written value's own variant —
-- the __jn carrier's kind when the value is a runtime carrier, the
-- written expression's static kind otherwise. A number-variant slot
-- serializes through the closed decimal spelling (__sfNumText,
-- Double.toString parity), an int-variant slot through the integer
-- spelling. The mark is keyed exactly like the storage key (a table
-- key or a 1-based element index) and is cleared by a non-number
-- rewrite of the same slot, so the walker's decision always mirrors
-- the stored value's own variant — the oracle's and the shared JVM
-- runtime's typing rule.
local function __numKey(t, k, v, isNumber)
  if type(v) == "table" and v.__jn then isNumber = (v.k == "number") end
  if isNumber then
    local marks = t.__nK
    if type(marks) ~= "table" then marks = {}; t.__nK = marks end
    marks[k] = true
  else
    local marks = t.__nK
    if type(marks) == "table" then marks[k] = nil end
  end
end
-- The read-side variant materialization: a plain number read from a
-- container slot whose recorded variant (__numKey) is number, or read
-- at a number-typed position while the slot's variant is int, becomes
-- a __jn carrier carrying its own variant; a plain number whose variant
-- matches the reading position stays plain. This keeps the closed
-- value model's int/number distinction through every typed boundary
-- (the oracle keeps the admitted variant and the shared JVM runtime
-- keeps the boxed Long/Double), so the JSON_STRINGIFY walker, the trace
-- atoms, and the failure actuals always see the value's own variant.
local function __readVar(t, k, v, wantsNumber)
  if type(v) ~= "number" then return v end
  local marks = t.__nK
  if type(marks) == "table" and marks[k] == true then
    return {__jn = true, k = "number", d = v}
  end
  if wantsNumber then return {__jn = true, k = "int", d = v} end
  return v
end
-- The canonical hex-float spelling (Double.toHexString parity; the
-- single renderer of the number atoms and of the SQRT_NEGATIVE
-- actual): NaN, both infinities and negative zero carry their Java
-- spellings (never LuaJIT's "inf"/"-inf"), a subnormal its
-- fixed-exponent denormal spelling, every other finite nonzero value
-- its shortest round-trippable hex form. Declared before __atom so the
-- number branch captures it as an upvalue.
local function __numHex(v)
  if v ~= v then return "NaN" end
  if v == math.huge then return "Infinity" end
  if v == -math.huge then return "-Infinity" end
  local neg = v < 0 or (v == 0 and 1 / v < 0)
  if v == 0 then return neg and "-0x0.0p0" or "0x0.0p0" end
  local m = neg and -v or v
  local sign = neg and "-" or ""
  -- A subnormal (|v| < 2^-1022) keeps Java's fixed-exponent denormal
  -- spelling: the fraction as 13 hex digits with its trailing zeros
  -- stripped and the pinned -1022 exponent ("0x0.0000000000001p-1022"),
  -- never LuaJIT's normalized "0x1p-1074". The two exact scalings
  -- recover the subnormal's integer significand (m * 2^1074, exact —
  -- every intermediate is a normal power-of-two scaling).
  if m < 2 ^ -1022 then
    local k = m * 2 ^ 537 * 2 ^ 537
    local hex = string.format("%013x", k)
    hex = string.gsub(hex, "0+$", "")
    if hex == "" then hex = "0" end
    return sign.."0x0."..hex.."p-1022"
  end
  local h = string.format("%a", m)
  h = string.gsub(h, "p(%+)(%d)", "p%2")
  if not string.find(h, ".", 1, true) then
    h = string.gsub(h, "^(0x[0-9a-f]+)p", "%1.0p")
  end
  return sign..h
end
local function __atom(kind, v)
  if v == __MISSING then return "missing" end
  if type(v) == "table" and v.__jn then
    if v.k == "int" then return "int:"..tostring(v.d) end
    return __atom("number", v.d)
  end
  if kind == "null" then return "null" end
  if kind == "missing" then return "missing" end
  if kind == "bool" then return "bool:"..tostring(v) end
  if kind == "int" then return "int:"..tostring(v) end
  if kind == "number" then
    if v ~= v then return "num:nan" end
    return "num:"..__numHex(v)
  end
  if kind == "string" then
    if v == nil then return "str:" end
    return "str:"..__esc(v)
  end
  if kind == "err" then
    return "err:"..v.code..":"..__esc(v.m or "")
  end
  if kind == "ref" or kind == "table" or kind == "array" or kind == "function"
      or kind == "class" then
    return "ref:"..__allocId(v)
  end
  if string.sub(kind, 1, 9) == "nullable:" then
    if v == nil then return "null" end
    return __atom(string.sub(kind, 10), v)
  end
  return "missing"
end
local function __errtext(e)
  if type(e) == "table" and e.__d then
    local parts = {e.code, __esc(e.m or ""), e.o or "-", e.e or "-", e.a or "-",
                   e.f or "-", e.cause and __errtext(e.cause) or "-"}
    return table.concat(parts, ";")
  end
  return "E9999;"..__esc(tostring(e))..";-;-;-;-;-"
end
local function __ev(op, phase, kind, digest, parent, inputs, output, errtext)
  local parts = {__seq, __module, op, phase, kind, digest, parent}
  if inputs then
    for _, inp in ipairs(inputs) do parts[#parts + 1] = inp end
  end
  local line = "T|"..table.concat(parts, "|")
  if output then line = line.."|=>"..output end
  if errtext then line = line.."|!"..errtext end
  io.stderr:write(line.."\\n")
  io.stderr:flush()
  __seq = __seq + 1
end
local function __actualOf(staticKind, v)
  if v == __MISSING then return "missing" end
  if v == nil then return "null" end
  if type(v) == "table" and v.__jn then return v.k end
  local t = type(v)
  if t == "boolean" then return "boolean" end
  if t == "number" then
    local inner = staticKind
    if string.sub(staticKind, 1, 9) == "nullable:" then inner = string.sub(staticKind, 10) end
    if inner == "int" then return "int" end
    if inner == "number" then return "number" end
    -- A number at a non-number declared kind (a dynamic read): integral
    -- values carry the int kind (int-typed positions), the rest the
    -- number kind.
    if v % 1 == 0 then return "int" end
    return "number"
  end
  if t == "string" then return "string" end
  if t == "table" then
    -- The runtime container markers decide the actual kind first (the
    -- shared JVM runtime's actualOf resolves the carrier's own type before
    -- any declared-kind fallback): a parsed/constructed array is an array
    -- even against a declared table boundary, and a class instance or an
    -- error/function carrier renders its own kind.
    if v.__a then return "array" end
    if v.__c then return "class:"..v.__id end
    if v.__d then return "class:@builtin/Error" end
    if v.__t then return "table" end
    if v.__fn ~= nil or v.__f then return "function" end
    if staticKind == "err" then return "class:@builtin/Error" end
    if staticKind == "table" then return "table" end
    if staticKind == "array" then return "array" end
    -- A plain table against a class boundary renders its own kind.
    return "table"
  end
  if t == "function" then return "function" end
  return staticKind
end
-- The raw read atom of the OPTIONAL_READ envelope: the value's actual
-- runtime kind — missing → "missing", null → "null", else the actual
-- kind's atom (a wrong-kind present value atomizes as its own kind,
-- exactly the oracle's publish). Numbers render through the declared
-- inner kind (Lua numbers carry no int/number distinction).
local function __rawAtom(kind, v)
  if v == __MISSING then return "missing" end
  if v == nil then return "null" end
  if type(v) == "table" and v.__jn then
    if v.k == "int" then return "int:"..tostring(v.d) end
    return __atom("number", v.d)
  end
  if type(v) == "boolean" then return "bool:"..tostring(v) end
  if type(v) == "number" then
    local inner = kind
    if string.sub(kind, 1, 9) == "nullable:" then inner = string.sub(kind, 10) end
    if inner == "int" then return "int:"..tostring(v) end
    return __atom("number", v)
  end
  if type(v) == "string" then return "str:"..__esc(v) end
  if type(v) == "table" then
    if v.__d then return "err:"..v.code..":"..__esc(v.m or "") end
    return "ref:"..__allocId(v)
  end
  if type(v) == "function" then return "ref:"..__allocId(v) end
  return __atom(kind, v)
end
local function __failExpr(code, msg, o, e, a)
  return {__d = true, code = code, m = msg, o = o, e = e, a = a, f = __framesText(),
          cause = nil}
end
-- The completion cell's actual kind (the ASYNC_COMPLETION boundary at an
-- AWAIT): the pinned corpus projection of the cell has one numeric kind,
-- so every numeric carrier — the plain Lua number (the shared int carrier)
-- and the {__jn} number carrier — projects as "number"; every other
-- carrier keeps the shared classification.
local function __completionActualOf(staticKind, v)
  if type(v) == "number" or (type(v) == "table" and v.__jn) then
    return "number"
  end
  return __actualOf(staticKind, v)
end
local function __bcheck(desc, staticKind, v, csig, completion)
  local actual = completion and __completionActualOf(staticKind, v)
    or __actualOf(staticKind, v)
  local function fail(expected)
    if completion then
      -- The completion cell's pinned transcript: message
      -- "expected {expected}" (the corpus completion-cell text).
      return error(__failExpr("E8001", "expected "..expected, "-", expected,
        actual), 0)
    end
    return error(__failExpr("E8001", "expected "..expected..", got "..actual,
      "-", expected, actual), 0)
  end
  if desc == "null" then
    if v == nil then return v end
    return fail("null")
  elseif desc == "boolean" then
    if type(v) == "boolean" then return v end
    return fail("boolean")
  elseif desc == "int" then
    -- The int cell keeps the admitted value's own variant: an int
    -- carrier returns its carrier, a number carrier runs the pinned
    -- int ladder (NaN → infinity → non-integer → E8004 range) with
    -- the exact actual tokens and returns its carrier — the oracle's
    -- and the shared JVM runtime's variant-preserving admission.
    if type(v) == "table" and v.__jn then
      if v.k == "int" then return v end
      if v.d ~= v.d then
        return error(__failExpr("E8001", "expected int, got NaN", "-", "int",
          "NaN"), 0)
      end
      if v.d == math.huge or v.d == -math.huge then
        return error(__failExpr("E8001", "expected int, got infinity", "-", "int",
          "infinity"), 0)
      end
      if v.d % 1 ~= 0 then
        return error(__failExpr("E8001", "expected int, got non-integer number", "-",
          "int", "non-integer number"), 0)
      end
      if v.d < -2147483648 or v.d > 2147483647 then
        return error(__failExpr("E8004", "int out of safe range", "-", "int",
          "number"), 0)
      end
      return v
    end
    if type(v) == "number" then
      if v ~= v then
        return error(__failExpr("E8001", "expected int, got NaN", "-", "int",
          "NaN"), 0)
      end
      if v == math.huge or v == -math.huge then
        return error(__failExpr("E8001", "expected int, got infinity", "-", "int",
          "infinity"), 0)
      end
      if v % 1 ~= 0 then
        return error(__failExpr("E8001", "expected int, got non-integer number", "-",
          "int", "non-integer number"), 0)
      end
      if v < -2147483648 or v > 2147483647 then
        return error(__failExpr("E8004", "int out of safe range", "-", "int",
          "number"), 0)
      end
      return v
    end
    return fail("int")
  elseif desc == "number" then
    if type(v) == "number" then return v end
    if type(v) == "table" and v.__jn then return v end
    return fail("number")
  elseif desc == "string" then
    if type(v) == "string" then return v end
    return fail("string")
  elseif desc == "table" then
    if type(v) == "table" and v.__t then return v end
    return fail("table")
  elseif desc == "@/Error" then
    -- The builtin Error class (the err carrier): an Error table
    -- passes unchanged.
    if type(v) == "table" and v.__d then return v end
    return fail(desc)
  elseif string.sub(desc, 1, 1) == "@" then
    -- A nominal class descriptor (E5): the canonical @module/Class
    -- identity text — the instance must carry the identical tag.
    if type(v) == "table" and v.__c and v.__id == desc then return v end
    return fail(desc)
  elseif string.sub(desc, 1, 6) == "array(" then
    if type(v) == "table" and v.__a then
      local inner = string.sub(desc, 7, -2)
      local innerSig = nil
      if csig ~= nil and string.sub(csig, 1, 1) == "[" then
        innerSig = string.sub(csig, 2, -2)
      end
      for i = 1, v.__n do
        local elem = v[i]
        if elem == __NULL then elem = nil
        elseif elem == nil then elem = __MISSING end
        local ok, checked = pcall(__bcheck, inner,
          (elem == __MISSING) and "missing" or inner, elem, innerSig)
        if not ok then
          local expected = inner
          local actualKind = __actualOf((elem == __MISSING) and "missing" or inner, elem)
          return error(__failExpr("E8003",
            "array element "..i.." type mismatch", "-", expected, actualKind), 0)
        end
      end
      return v
    end
    return fail("array")
  elseif string.sub(desc, 1, 9) == "nullable(" then
    if v == nil or v == __MISSING then return nil end
    local innerSig = csig
    if innerSig ~= nil and string.sub(innerSig, 1, 1) == "?" then
      innerSig = string.sub(innerSig, 2)
    end
    return __bcheck(string.sub(desc, 10, -2), staticKind, v, innerSig, completion)
  elseif string.sub(desc, 1, 9) == "function(" then
    if type(v) == "function" then
      local carried = v.__sig or ""
      if carried == desc then return v end
      return error(__failExpr("E8010",
        "function signature mismatch: expected "..desc..", got "..carried,
        "-", desc, carried), 0)
    end
    if type(v) == "table" and v.__fn ~= nil then
      local carried = v.__sig or ""
      if carried == desc then return v end
      return error(__failExpr("E8010",
        "function signature mismatch: expected "..desc..", got "..carried,
        "-", desc, carried), 0)
    end
    if type(v) == "table" and v.__kind == "function" then
      -- The host ABI wrapper — the loaded host surface entry a HOST
      -- EXPORT_READ publishes (ISSUE-0653; host-module-load-and-host-call-
      -- realization H5's read value). The entry's own sig metadata is its
      -- declared canonical signature, so the row compares it byte-exact
      -- against the boundary's declared canonical descriptor (the
      -- emitter-supplied csig; the desc spelling is the DEAL carrier's
      -- internal text).
      local wanted = csig or desc
      if v.sig == wanted then return v end
      return error(__failExpr("E8010",
        "function signature mismatch: expected "..wanted..", got "
          ..tostring(v.sig or "nil"), "-", wanted, v.sig), 0)
    end
    return fail("function")
  end
  return v
end
local function __cmp(selector, kindL, l, kindR, r, side)
  local lnil = (l == nil or l == __MISSING)
  local rnil = (r == nil or r == __MISSING)
  if lnil or rnil then
    if selector == "NULLABLE_NULL_EQ" then
      local named = (side == "LEFT") and l or r
      return (named == nil or named == __MISSING)
    elseif selector == "NULLABLE_NULL_NE" then
      local named = (side == "LEFT") and l or r
      return not (named == nil or named == __MISSING)
    end
    local both = lnil and rnil
    if string.sub(selector, -3) == "_EQ" then return both end
    if string.sub(selector, -3) == "_NE" then return not both end
    return false
  end
  if string.sub(selector, 1, 5) == "INT32" or string.sub(selector, 1, 6) == "NUMBER"
      or string.sub(selector, 1, 8) == "NULLABLE" then
    l = __num(l); r = __num(r)
  end
  if selector == "INT32_EQ" then return l == r end
  if selector == "INT32_NE" then return l ~= r end
  if selector == "INT32_LT" then return l < r end
  if selector == "INT32_LE" then return l <= r end
  if selector == "INT32_GT" then return l > r end
  if selector == "INT32_GE" then return l >= r end
  if selector == "NUMBER_EQ" then return l == r end
  if selector == "NUMBER_NE" then return l ~= r end
  if selector == "NUMBER_LT" then return l < r end
  if selector == "NUMBER_LE" then return l <= r end
  if selector == "NUMBER_GT" then return l > r end
  if selector == "NUMBER_GE" then return l >= r end
  if selector == "STRING_EQ" then return l == r end
  if selector == "STRING_NE" then return l ~= r end
  if selector == "STRING_LT" then return l < r end
  if selector == "STRING_LE" then return l <= r end
  if selector == "STRING_GT" then return l > r end
  if selector == "STRING_GE" then return l >= r end
  if selector == "BOOLEAN_EQ" then return l == r end
  if selector == "BOOLEAN_NE" then return l ~= r end
  if selector == "NULL_EQ" then return true end
  if selector == "NULL_NE" then return false end
  if selector == "NULLABLE_EQ" then return l == r end
  if selector == "NULLABLE_NE" then return l ~= r end
  if selector == "REFERENCE_EQ" then return l == r end
  if selector == "REFERENCE_NE" then return l ~= r end
  return false
end
local function __unary(selector, v, opKey, digest, parent, origin)
  if selector == "BOOL_NOT" then return not v end
  v = __num(v)
  if selector == "INT32_NEG" then
    local r = -v
    if r < -2147483648 or r > 2147483647 then
      local e = __failExpr("E8004", "int out of safe range", origin, nil, nil)
      __ev(opKey, "FAILURE", "UNARY", digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    return r
  end
  return -v
end
local function __arith(selector, l, r, opKey, digest, parent, origin)
  l = __num(l); r = __num(r)
  local function rng(v)
    if v < -2147483648 or v > 2147483647 then
      local e = __failExpr("E8004", "int out of safe range", origin, nil, nil)
      __ev(opKey, "FAILURE", "BINARY", digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    return v
  end
  if selector == "INT32_ADD" then return rng(l + r) end
  if selector == "INT32_SUB" then return rng(l - r) end
  if selector == "INT32_MUL" then return rng(l * r) end
  if selector == "INT32_DIV_TRUNC" then
    if r == 0 then
      local e = __failExpr("E8005", "integer division by zero", origin, nil, nil)
      __ev(opKey, "FAILURE", "BINARY", digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    local q = l / r
    local t = math.floor(math.abs(q))
    if q < 0 then t = -t end
    return rng(t)
  end
  if selector == "INT32_MOD_TRUNC" then
    if r == 0 then
      local e = __failExpr("E8005", "integer division by zero", origin, nil, nil)
      __ev(opKey, "FAILURE", "BINARY", digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    return rng(l % r)
  end
  if selector == "INT32_POW" then
    if r < 0 then
      local e = __failExpr("E8006", "integer exponent must be non-negative", origin,
        nil, nil)
      __ev(opKey, "FAILURE", "BINARY", digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    local result = 1
    for _ = 1, r do result = result * l end
    return rng(result)
  end
  if selector == "NUMBER_ADD" then return l + r end
  if selector == "NUMBER_SUB" then return l - r end
  if selector == "NUMBER_MUL" then return l * r end
  if selector == "NUMBER_DIV_IEEE" then return l / r end
  if selector == "NUMBER_MOD_FLOOR" then return l - math.floor(l / r) * r end
  if selector == "NUMBER_POW_IEEE" then return l ^ r end
  return 0
end
local function __intConv(v, evKind, kind, opKey, digest, parent, origin)
  if v == nil then
    local e = __failExpr("E8001", "cannot convert null to int", origin, "int", "null")
    __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
  v = __num(v)
  if type(v) == "number" then
    if v ~= v then
      local e = __failExpr("E8001", "expected int, got NaN", origin, "int", "NaN")
      __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    if v == math.huge or v == -math.huge then
      local e = __failExpr("E8001", "expected int, got infinity", origin, "int",
        "infinity")
      __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    if v % 1 ~= 0 then
      local e = __failExpr("E8001", "expected int, got non-integer number", origin,
        "int", "non-integer number")
      __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    if v < -2147483648 or v > 2147483647 then
      local e = __failExpr("E8004", "int out of safe range", origin, "int", "number")
      __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
      error(e, 0)
    end
    return v
  end
  local e = __failExpr("E8001", "expected int, got "..__actualOf(kind, v), origin,
    "int", __actualOf(kind, v))
  __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
  error(e, 0)
end
local function __numConv(v, evKind, kind, opKey, digest, parent, origin)
  if v == nil then
    local e = __failExpr("E8001", "cannot convert null to number", origin, "number",
      "null")
    __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
  v = __num(v)
  if type(v) == "number" then return v end
  local e = __failExpr("E8001", "expected number, got "..__actualOf(kind, v), origin,
    "number", __actualOf(kind, v))
  __ev(opKey, "FAILURE", evKind, digest, parent, {}, nil, __errtext(e))
  error(e, 0)
end
-- The intrinsic carrier's generic invoker (J2): the conversion ladder
-- of the carrier's kind over the caller's first argument, with the
-- invoking call's context when one is supplied (the DEAL convention
-- packs the invoking op's kind label, the static kind, the op key, the
-- digest, the parent key, and the origin after the value) and the
-- absent context otherwise — total and deterministic for any non-DEAL
-- caller (the host bridge and any generic unwrap). DEAL call sites run
-- the ladder directly with the invoking op's own context and kind
-- (ISSUE-0679 J4); the carrier's invoker never invents a call site's
-- origin, and its declared-parameter kind is the default static kind
-- (the intrinsic's declared signature is the only descriptor source).
__intrinsicInvoke = function(it, v, evKind, kind, opKey, digest, parent, origin)
  if evKind == nil then evKind = "INTRINSIC_CALL" end
  if kind == nil then kind = (it == "INT_CONVERT") and "number" or "int" end
  if opKey == nil then opKey = "-" end
  if digest == nil then digest = "-" end
  if parent == nil then parent = "-" end
  if origin == nil then origin = "-" end
  if it == "INT_CONVERT" then
    return __intConv(v, evKind, kind, opKey, digest, parent, origin)
  end
  return __numConv(v, evKind, kind, opKey, digest, parent, origin)
end
local function __arrayRead(opKey, digest, parent, bKey, bDigest, bParent, desc, inner,
                           container, slotName, nullable, wantsNumber, origin)
  local index = slotName.i
  local elem = __MISSING
  if index < 0 then
    __ev(bKey, "START", "BOUNDARY", bDigest, bParent, {__atom("missing", __MISSING)},
      nil, nil)
    local e = __failExpr("E8002", "negative array index", origin, nil, nil)
    __ev(bKey, "FAILURE", "BOUNDARY", bDigest, bParent, {}, nil, __errtext(e))
    __ev(opKey, "FAILURE", "INDEX_READ", digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
  if index < container.__n then
    elem = container[index + 1]
    if elem == __NULL then elem = nil
    elseif elem == nil then elem = __MISSING end
  end
  -- The read-side variant materialization (the element's own slot mark
  -- and the read's declared element descriptor).
  elem = __readVar(container, index + 1, elem, wantsNumber)
  local elemKind
  if elem == __MISSING then elemKind = "missing"
  elseif elem == nil then elemKind = "null"
  else elemKind = inner end
  __ev(bKey, "START", "BOUNDARY", bDigest, bParent, {__atom(elemKind, elem)},
    nil, nil)
  __ev(bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, {}, __atom(elemKind, elem),
    nil)
  if elem == __MISSING then
    if nullable then
      return nil
    end
    return __MISSING
  end
  return elem
end
local function __arrayBounds(bKey, bDigest, bParent, input, slotName, lengthSlot,
                             desc, staticKind, isAssign, origin)
  local index = slotName.i
  __ev(bKey, "START", "BOUNDARY", bDigest, bParent, {__atom(staticKind, input)},
    nil, nil)
  if index < 0 or index > lengthSlot then
    local e = __failExpr("E8002", "array index out of bounds", origin, nil, nil)
    __ev(bKey, "FAILURE", "BOUNDARY", bDigest, bParent, {}, nil, __errtext(e))
    error(e, 0)
  end
  if isAssign then
    local ok, checked = pcall(__bcheck, desc, staticKind, input)
    if not ok then
      __ev(bKey, "FAILURE", "BOUNDARY", bDigest, bParent, {}, nil, __errtext(checked))
      error(checked, 0)
    end
  end
  __ev(bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, {}, __atom(staticKind, input),
    nil)
end
local function __slotAtom(s)
  if s.slot == "a" then
    return "slot:"..s.i.."/"..tostring(s.i < s.n).."/"..tostring(s.a and (s.i == s.n))
  end
  return "keyslot:"..__esc(s.k)
end
local function __arrayBoundsSlot(bKey, bDigest, bParent, slotName, lengthSlot,
                                    isAssign, origin)
  local index = slotName.i
  __ev(bKey, "START", "BOUNDARY", bDigest, bParent, {__slotAtom(slotName)}, nil, nil)
  if index < 0 or index > lengthSlot then
    local e = __failExpr("E8002", "array index out of bounds", origin, nil, nil)
    __ev(bKey, "FAILURE", "BOUNDARY", bDigest, bParent, {}, nil, __errtext(e))
    error(e, 0)
  end
  __ev(bKey, "SUCCESS", "BOUNDARY", bDigest, bParent, {}, __slotAtom(slotName), nil)
end
local function __foreachCheck(opKey, digest, parent, desc, elem, origin)
  if elem == __MISSING then
    local e = __failExpr("E8001", "expected "..desc..", got missing", origin, desc,
      "missing")
    __ev(opKey, "FAILURE", "FOR_EACH", digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
  local ok, checked = pcall(__bcheck, desc, desc, elem)
  if not ok then
    local e = checked
    __ev(opKey, "FAILURE", "FOR_EACH", digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
end
local function __normalizeEvent(opKey, digest, parent, slotName)
  local atom
  if slotName.slot == "a" then
    atom = "slot:"..slotName.i.."/"..tostring(slotName.i < slotName.n).."/"
      ..tostring(slotName.a and (slotName.i == slotName.n))
  else
    atom = "keyslot:"..__esc(slotName.k)
  end
  __ev(opKey, "SUCCESS", "INDEX_NORMALIZE", digest, parent, {}, atom, nil)
end
local function __u8sub(s, i, j)
  return string.sub(s, i, j)
end
-- The wrapper unwrapper: a table carrying an __fn field exposes the
-- underlying callable (the closure or the adapter protocol).
local function __unfn(v)
  if type(v) == "table" and v.__fn ~= nil then return v.__fn end
  return v
end
-- The dynamic dispatch's carrier-class resolution (ISSUE-0658;
-- dynamic-call-shape-production-and-emission Y2/Y3/Y5; ISSUE-0678 for the
-- cataloged callable's tag; ISSUE-0679 for the conversion intrinsic's): the
-- carrier's own tag selects exactly one closed resolution class — never the
-- checked descriptor, the callee spelling, or an argument value. A DEAL
-- closure or compiled export read carries its function id (__fid); an adapter
-- carries its capture mode (__mode); a loaded host surface entry carries the
-- host ABI wrapper kind (__kind == "function"); the cataloged stdlib callable
-- carries its closed catalog row tag (__sid) and resolves the HOST class,
-- whose catalog row invoker the call site runs; the conversion intrinsic
-- carries its closed kind tag (__it) and resolves the HOST class, whose
-- conversion ladder the call site runs. Every other value identifies no class
-- (nil) and the dynamic call fails closed at its origin.
local function __dynClass(v)
  if type(v) ~= "table" then return nil end
  if v.__fid ~= nil then return "DEAL_BODY" end
  if v.__mode ~= nil then return "ADAPTER" end
  if v.__kind == "function" then return "HOST" end
  if v.__sid ~= nil then return "HOST" end
  if v.__it ~= nil then return "HOST" end
  return nil
end
-- The declared identity (module path, export name) of one loaded host
-- surface entry: the program's export-surface registry is the
-- identity-indexed home of the entries the host load published (H1), so
-- the carrier itself names the declared host export the dynamic dispatch's
-- host operation start derives its operation label and its
-- ASYNC_OPERATION_HANDLE terminal from. Exactly one home is required: a
-- shared entry (never a loaded surface entry) resolves no declared
-- identity and the dispatch fails closed.
local function __surfaceNameOf(v)
  local found = nil
  for __m, __s in pairs(__exportSurfaces) do
    for __n, __e in pairs(__s) do
      if __e == v then
        if found ~= nil then return nil end
        found = {__m, __n}
      end
    end
  end
  return found
end
-- The actual-kind atom of one host-supplied argument (the callback
-- dispatch surface): null/boolean/int/number/string by the runtime
-- carrier — identical to the semantic oracle's scripted-argument
-- atomization.
local function __hostAtom(v)
  if v == nil then return "null" end
  local t = type(v)
  if t == "boolean" then return "bool:"..tostring(v) end
  if t == "number" then
    if v % 1 == 0 then return "int:"..tostring(v) end
    return __atom("number", v)
  end
  if t == "string" then return "str:"..__esc(v) end
  return "ref:"..__allocId(v)
end
-- The adapter's source-signature check (D15): the resolved source's
-- carried canonical spec text must equal the recorded source signature;
-- a mismatch is E8010 FUNCTION_SIGNATURE at the invoking op's origin
-- with the active frames (the check runs before any source-frame push).
local function __fncheck(v, expected, origin)
  local carried = ""
  -- A DEAL carrier carries its canonical spec text in __csig; a loaded
  -- host surface entry (the host ABI wrapper a HOST read publishes,
  -- ISSUE-0653) carries its declared canonical signature in sig.
  if type(v) == "table" then carried = v.__csig or v.sig or "" end
  if type(v) == "function" then carried = v.__csig or "" end
  if carried == expected then return v end
  return error(__failExpr("E8010", "function signature mismatch: expected "..expected
    ..", got "..carried, origin, expected, carried), 0)
end
-- The adapter's source resolution per the closed capture mode
-- (D15 creation half): 0 VALUE, 1 SHARED_CELL, 2 REEVALUATE_THUNK.
local function __adaptSource(w)
  if w.__mode == 0 then return w.__value
  elseif w.__mode == 1 then return w.__cell[1]
  else return w.__thunk() end
end
-- The D15 adapter invocation protocol: resolve the source per the
-- closed capture mode (0 VALUE, 1 SHARED_CELL, 2 REEVALUATE_THUNK),
-- the source-signature check, then the source invocation with the
-- leading M arguments only. A DEAL-body source pushes its function id
-- onto the active frames for the invocation (popped on every path); the
-- identical completion error propagates unchanged.
local function __adaptInvoke(w, origin, ...)
  local __cargs = {...}
  local src = __adaptSource(w)
  __fncheck(src, w.__csrc, origin)
  local __fid = nil
  if type(src) == "table" then __fid = src.__fid end
  if type(src) == "function" then __fid = src.__fid end
  local __pushed = false
  if __fid ~= nil then
    table.insert(__frames, 1, tostring(__fid))
    __pushed = true
  end
  local __okA, __vA = pcall(__unfn(src), unpack(__cargs, 1, w.__m))
  if __pushed then table.remove(__frames, 1) end
  if not __okA then error(__vA, 0) end
  return __vA
end
""";

    /**
     * The second half of the runtime prelude (the D13 async machine
     * onward): a separate constant because a single Java string constant
     * may not exceed the class-file's 65535-byte UTF-8 limit; both halves
     * are appended consecutively, so the emitted chunk is byte-identical
     * to the unsplit text.
     */
    private static final String PRELUDE_ASYNC = """
-- ==== the D13 async machine (ASYNC_START/AWAIT) ====
-- The canonical-token task registry and the deterministic FIFO queue —
-- chunk-global (one execution state across a multi-module drive).
__tasks = __tasks or {}
__ready = __ready or {}
-- One DEAL body task record: the coroutine wrapping the body-task
-- closure (the canonical AsyncTokenId is the task record).
local function __asyncStartTask(tokenId, owner, co, args)
  __tasks[tokenId] = {token = tokenId, owner = owner, co = co, args = args,
                      status = 0, value = nil, err = nil, label = nil}
  table.insert(__ready, tokenId)
  return tokenId
end
-- One async host operation record: a production operation carries the
-- operation handle the loaded declared async export returned (its
-- completion is driven at the awaiting site through the landed
-- __rt.async_step machinery, never through the body drain); a
-- scenario/seam record carries no handle and completes through the
-- deterministic host seam at the awaiting site.
local function __asyncStartHost(tokenId, label, handle)
  __tasks[tokenId] = {token = tokenId, owner = "HOST_OPERATION", co = nil,
                      args = nil, status = 2, value = nil, err = nil,
                      label = label, handle = handle}
  table.insert(__ready, tokenId)
  return tokenId
end
-- The deterministic FIFO drain (the oracle's drainReadyTasks): every
-- pending body task resumes to completion in submission order (a task
-- body's nested starts re-evaluate the queue length — the while form
-- drains them too). A DEAL failure completes the task record; an
-- infrastructure failure is never reified. Host operations complete
-- only at their own AWAIT through the seam.
local function __asyncDrain()
  local i = 1
  while i <= #__ready do
    local id = __ready[i]
    local t = __tasks[id]
    if t ~= nil and t.status == 0 then
      t.status = 1
      local ok, v = coroutine.resume(t.co, unpack(t.args, 1, #t.args))
      if not ok then
        if type(v) == "table" and v.__d then
          t.err = v
        else
          error(v, 0)
        end
      else
        t.value = v
      end
    end
    i = i + 1
  end
  __ready = {}
end
-- The first-insertion order discipline of the shared table carrier
-- (the SemanticTable order contract): TABLE_NEW / MEMBER_WRITE /
-- INDEX_WRITE append a key on first insertion, MEMBER_DELETE /
-- INDEX_DELETE remove the order slot, and a reinsertion appends it.
-- TABLE_KEYS and JSON_STRINGIFY consume exactly this order.
local function __orderAdd(t, k)
  if not t.__keys[k] then
    t.__order[#t.__order + 1] = k
  end
  t.__keys[k] = true
end
local function __orderRemove(t, k)
  t.__keys[k] = nil
  for i = 1, #t.__order do
    if t.__order[i] == k then
      table.remove(t.__order, i)
      return
    end
  end
end
-- ==== stdlib realization (the closed 21-operation table) ====
local function __u8next(s, i)
  local b = string.byte(s, i)
  if b == nil then return nil, nil end
  if b < 128 then return b, i + 1 end
  local n = 2
  if b >= 224 then n = 3 end
  if b >= 240 then n = 4 end
  local cp = b % (2 ^ (8 - n))
  for k = 1, n - 1 do
    cp = cp * 64 + (string.byte(s, i + k) % 64)
  end
  return cp, i + n
end
local function __u8len(cp)
  if cp < 128 then return 1 end
  if cp < 2048 then return 2 end
  if cp < 65536 then return 3 end
  return 4
end
local function __cps(s)
  local out = {}
  local pos = 1
  while true do
    local cp, np = __u8next(s, pos)
    if cp == nil then return out end
    out[#out + 1] = cp
    pos = np
  end
end
local function __u8enc(cp)
  if cp < 128 then return string.char(cp) end
  if cp < 2048 then
    return string.char(192 + math.floor(cp / 64), 128 + cp % 64)
  end
  if cp < 65536 then
    return string.char(224 + math.floor(cp / 4096),
      128 + math.floor(cp / 64) % 64, 128 + cp % 64)
  end
  return string.char(240 + math.floor(cp / 262144),
    128 + math.floor(cp / 4096) % 64, 128 + math.floor(cp / 64) % 64,
    128 + cp % 64)
end
-- The raw argument/result atom of the STDLIB_CALL surfaces (the op
-- START and the STDLIB_PARAMETER/STDLIB_RETURN boundary STARTs): the
-- value's actual kind, exactly the oracle's atomOf — a dynamic argument
-- at a declared boundary atomizes as its own kind (an int-typed number
-- renders the int atom, a number-typed value the hex float, a wrong-kind
-- value its own kind) instead of crashing on the declared-kind
-- rendering.
local function __rawArgAtom(kind, v)
  if v == __MISSING then return "missing" end
  if v == nil then return "null" end
  local t = type(v)
  if t == "boolean" then return "bool:"..tostring(v) end
  if t == "number" then
    local inner = kind
    if string.sub(kind, 1, 9) == "nullable:" then inner = string.sub(kind, 10) end
    if inner == "int" then return "int:"..tostring(v) end
    if inner == "number" then return __atom("number", v) end
    if v % 1 == 0 then return "int:"..tostring(v) end
    return __atom("number", v)
  end
  if t == "string" then return "str:"..__esc(v) end
  if t == "table" then
    if v.__jn then
      if v.k == "int" then return "int:"..tostring(v.d) end
      return __atom("number", v.d)
    end
    if v.__d then return "err:"..v.code..":"..__esc(v.m or "") end
    return "ref:"..__allocId(v)
  end
  if t == "function" then return "ref:"..__allocId(v) end
  return __atom(kind, v)
end
-- The Java Double.toString notation of one finite nonzero double: the
-- shortest round-tripping digit string (at least two significant
-- digits — the printed form always carries one fractional digit), the
-- closest such decimal, and the even last digit when the value is
-- exactly equidistant between two of them — the JDK's rule, which the
-- C library's %g rounding (ties away from zero) does not reproduce on
-- its own. Plain notation when the decimal exponent is in [-3, 6],
-- scientific d.dddE±dd otherwise, and a pinned ".0" suffix on integral
-- plain forms. Named distinctly from the class-encoder renderer
-- (JSON_PRELUDE's __jsonNumText), so the emitted chunk carries one name
-- per renderer.
--
-- The steps below: __sfParts reads a %g rendering as (digit integer,
-- exponent of its last digit); __sfBump steps that digit integer by one
-- grid unit; __sfDec renders a (digits, exponent) pair back to a
-- parseable decimal for the round-trip probe; __sfExpDigits reads the
-- exact expansion through 40 places (a tie candidate has at most 18
-- digits); __sfDigits picks the shortest round-tripping digits.
local function __sfParts(rep)
  local mant, e = string.match(rep, "^(%d+%.?%d*)e([%+%-]?%d+)$")
  if mant then
    local point = string.find(mant, ".", 1, true)
    local intLen = point and (point - 1) or #mant
    local digits = string.gsub(mant, "%.", "")
    return digits, tonumber(e) - (#digits - intLen)
  end
  local point = string.find(rep, ".", 1, true)
  local digits
  local expo
  if point then
    digits = string.gsub(rep, "%.", "")
    expo = point - #rep
  else
    digits = rep
    expo = 0
  end
  digits = string.gsub(digits, "^0+", "")
  if digits == "" then digits = "0" end
  return digits, expo
end
local function __sfBump(digits, up)
  local n = #digits
  local d = {}
  for i = 1, n do d[i] = tonumber(string.sub(digits, i, i)) end
  if up then
    local i = n
    while i >= 1 and d[i] == 9 do d[i] = 0; i = i - 1 end
    if i == 0 then return "1" end
    d[i] = d[i] + 1
  else
    local i = n
    while i >= 1 and d[i] == 0 do d[i] = 9; i = i - 1 end
    if i == 0 then return "9" end
    d[i] = d[i] - 1
  end
  local s = ""
  for i = 1, n do s = s..tostring(d[i]) end
  return s
end
local function __sfDec(digits, expo)
  if #digits == 1 then return digits.."e"..expo end
  return string.sub(digits, 1, 1).."."..string.sub(digits, 2)
    .."e"..(expo + #digits - 1)
end
local function __sfExpDigits(v)
  local mant = string.match(string.format("%.40e", v), "^(%d+%.?%d*)e")
  return (string.gsub(mant or "", "%.", ""))
end
local function __sfDigits(v, N)
  local rep = string.format("%."..N.."g", v)
  local digits, expo = __sfParts(rep)
  local pad = N - #digits
  if pad > 0 then
    digits = digits..string.rep("0", pad)
    expo = expo - pad
  end
  if tonumber(__sfDec(digits, expo)) ~= v then
    -- The correctly rounded decimal lies outside the rounding interval:
    -- the candidate is its in-interval neighbour.
    local up = __sfBump(digits, true)
    if tonumber(__sfDec(up, expo)) == v then return up, expo end
    local dn = __sfBump(digits, false)
    if tonumber(__sfDec(dn, expo)) == v then return dn, expo end
    return nil
  end
  local exp = __sfExpDigits(v)
  local dn = __sfBump(digits, false)
  local dnMid = string.gsub(dn.."5", "^0+", "")
  if string.sub(exp, 1, #dnMid) == dnMid
      and string.gsub(string.sub(exp, #dnMid + 1), "0", "") == ""
      and tonumber(__sfDec(dn, expo)) == v then
    if tonumber(string.sub(dn, #dn, #dn)) % 2 == 0 then return dn, expo end
    return digits, expo
  end
  local up = __sfBump(digits, true)
  local upMid = digits.."5"
  if string.sub(exp, 1, #upMid) == upMid
      and string.gsub(string.sub(exp, #upMid + 1), "0", "") == ""
      and tonumber(__sfDec(up, expo)) == v then
    if tonumber(string.sub(up, #up, #up)) % 2 == 0 then return up, expo end
    return digits, expo
  end
  return digits, expo
end
local function __sfNumText(v)
  local neg = false
  if v < 0 or (v == 0 and 1 / v < 0) then neg = true; v = -v end
  if v == 0 then return neg and "-0.0" or "0.0" end
  local digits, expo = nil, nil
  for N = 2, 17 do
    digits, expo = __sfDigits(v, N)
    if digits ~= nil then break end
  end
  if digits == nil then digits, expo = __sfParts(string.format("%.17g", v)) end
  digits = string.gsub(digits, "^0+", "")
  if digits == "" then digits = "0" end
  local trail = 0
  while #digits > 1 and string.sub(digits, #digits, #digits) == "0" do
    digits = string.sub(digits, 1, #digits - 1)
    trail = trail + 1
  end
  local k = expo + trail + #digits - 1
  local ds = digits
  local text
  if k >= -3 and k <= 6 then
    if k >= 0 then
      if #ds <= k + 1 then
        text = ds..string.rep("0", k + 1 - #ds)..".0"
      else
        text = string.sub(ds, 1, k + 1).."."..string.sub(ds, k + 2)
      end
    else
      text = "0."..string.rep("0", -k - 1)..ds
    end
  else
    local tail = string.sub(ds, 1, 1)
    if #ds > 1 then tail = tail.."."..string.sub(ds, 2) else tail = tail..".0" end
    text = tail.."E"..tostring(k)
  end
  if neg then text = "-"..text end
  return text
end
-- RFC-8259 string escaping: quote/backslash escaped, the named short
-- escapes, every other control scalar as the lowercase four-hex-digit
-- escape, every other byte (surrogate pairs included) raw — built
-- through string.char, so the emitted prelude carries no escape
-- ambiguity.
local function __jsonEscape(s)
  local out = { string.char(34) }
  for i = 1, #s do
    local b = string.byte(s, i)
    if b == 34 then out[#out + 1] = string.char(92, 34)
    elseif b == 92 then out[#out + 1] = string.char(92, 92)
    elseif b == 8 then out[#out + 1] = string.char(92, 98)
    elseif b == 12 then out[#out + 1] = string.char(92, 102)
    elseif b == 10 then out[#out + 1] = string.char(92, 110)
    elseif b == 13 then out[#out + 1] = string.char(92, 114)
    elseif b == 9 then out[#out + 1] = string.char(92, 116)
    elseif b < 32 then
      out[#out + 1] = string.char(92, 117)
      out[#out + 1] = string.format("%04x", b)
    else out[#out + 1] = string.sub(s, i, i) end
  end
  out[#out + 1] = string.char(34)
  return table.concat(out)
end
local function __subseqIndexOf(hay, needle, from)
  if #needle == 0 then
    if from <= #hay then return from end
    return -1
  end
  local limit = #hay - #needle + 1
  for i = math.max(0, from) + 1, limit do
    local ok = true
    for j = 1, #needle do
      if hay[i + j - 1] ~= needle[j] then ok = false; break end
    end
    if ok then return i - 1 end
  end
  return -1
end
-- The in-target realization of the closed stdlib table: the parameter
-- boundaries already ran, so the carriers are boundary-admitted (valid
-- scalar strings, integral numbers, tables). The invoking op's event
-- kind label is the first argument (the direct STDLIB_CALL arm's own
-- kind, or the dynamic dispatch's CALL kind): every algorithm failure
-- publishes the invoking op's FAILURE event under its own kind and
-- raises the exact closed projection at the call origin with the active
-- frames.
local function __stdlib(kind, fn, opKey, digest, parent, origin, ...)
  local __args = {...}
  -- Every numeric parameter carrier unwraps to its number: the parameter
  -- boundaries already admitted the value (a JSON_PARSE carrier passes
  -- the number/int rows through the same __bcheck unwrapping), and the
  -- shared JVM algorithm receives the Long/Double the carrier stands
  -- for — the two representations never diverge inside an algorithm.
  for __i = 1, select("#", ...) do
    local __a = __args[__i]
    if type(__a) == "table" and __a.__jn then __args[__i] = __a.d end
  end
  local function __sfail(code, msg, expected, actual)
    local e = __failExpr(code, msg, origin, expected, actual)
    __ev(opKey, "FAILURE", kind, digest, parent, {}, nil, __errtext(e))
    error(e, 0)
  end
  local function __int32Gate(value)
    if value < -2147483648 or value > 2147483647 then
      __sfail("E8004", "int out of safe range", nil, nil)
    end
    return value
  end
  if fn == "STRING_LENGTH" then
    return __int32Gate(#__cps(__args[1]))
  elseif fn == "STRING_SUBSTRING" then
    local cps = __cps(__args[1])
    local lo = math.max(0, __args[2])
    local hi = math.min(math.max(0, __args[3]), #cps)
    if lo >= hi then return "" end
    local out = {}
    for i = lo + 1, hi do out[#out + 1] = __u8enc(cps[i]) end
    return table.concat(out)
  elseif fn == "STRING_CONTAINS" then
    return __subseqIndexOf(__cps(__args[1]), __cps(__args[2]), 0) >= 0
  elseif fn == "STRING_STARTS_WITH" then
    local input = __cps(__args[1])
    local part = __cps(__args[2])
    if #part > #input then return false end
    for i = 1, #part do
      if input[i] ~= part[i] then return false end
    end
    return true
  elseif fn == "STRING_ENDS_WITH" then
    local input = __cps(__args[1])
    local part = __cps(__args[2])
    if #part > #input then return false end
    for i = 1, #part do
      if input[#input - #part + i] ~= part[i] then return false end
    end
    return true
  elseif fn == "STRING_REPLACE" then
    local input = __cps(__args[1])
    local from = __cps(__args[2])
    local to = __cps(__args[3])
    if #from == 0 then return __args[1] end
    local out = {}
    local cursor = 1
    while cursor <= #input - #from + 1 do
      local ok = true
      for j = 1, #from do
        if input[cursor + j - 1] ~= from[j] then ok = false; break end
      end
      if ok then
        for j = 1, #to do out[#out + 1] = __u8enc(to[j]) end
        cursor = cursor + #from
      else
        out[#out + 1] = __u8enc(input[cursor])
        cursor = cursor + 1
      end
    end
    for i = cursor, #input do out[#out + 1] = __u8enc(input[i]) end
    return table.concat(out)
  elseif fn == "STRING_SPLIT" then
    local input = __cps(__args[1])
    local sep = __cps(__args[2])
    if #input == 0 then return {__a = true, __n = 0} end
    if #sep == 0 then
      local singles = {__a = true, __n = #input}
      for i = 1, #input do singles[i] = __u8enc(input[i]) end
      return singles
    end
    local parts = {__a = true, __n = 0}
    local cursor = 1
    while true do
      local occ = __subseqIndexOf(input, sep, cursor - 1)
      if occ < 0 then break end
      local piece = {}
      for i = cursor, occ do piece[#piece + 1] = __u8enc(input[i]) end
      parts.__n = parts.__n + 1
      parts[parts.__n] = table.concat(piece)
      cursor = occ + 1 + #sep
    end
    local tail = {}
    for i = cursor, #input do tail[#tail + 1] = __u8enc(input[i]) end
    parts.__n = parts.__n + 1
    parts[parts.__n] = table.concat(tail)
    return parts
  elseif fn == "STRING_TRIM" then
    local cps = __cps(__args[1])
    local function isTrim(cp) return (cp >= 9 and cp <= 13) or cp == 32 end
    local first = 1
    while first <= #cps and isTrim(cps[first]) do first = first + 1 end
    local last = #cps
    while last >= first and isTrim(cps[last]) do last = last - 1 end
    local out = {}
    for i = first, last do out[#out + 1] = __u8enc(cps[i]) end
    return table.concat(out)
  elseif fn == "TABLE_KEYS" then
    local t = __args[1]
    local keys = {__a = true, __n = #t.__order}
    for i = 1, #t.__order do keys[i] = t.__order[i] end
    return keys
  elseif fn == "JSON_PARSE" then
    local s = __args[1]
    local pos = 1
    local consumed = 0
    local function atEnd() return pos > #s end
    local function peek()
      local cp = __u8next(s, pos)
      if cp == nil then return -1 end
      return cp
    end
    local function advance()
      local cp = __u8next(s, pos)
      pos = pos + __u8len(cp)
      consumed = consumed + __u8len(cp)
      return cp
    end
    local function parseFail(reason)
      __sfail("E8001",
        "JSON parse error at position "..(consumed + 1)..": "..reason, nil, nil)
    end
    local function skipWs()
      while not atEnd() do
        local c = peek()
        if c ~= 32 and c ~= 9 and c ~= 10 and c ~= 13 then return end
        advance()
      end
    end
    local function hexDigit(c)
      if c >= 48 and c <= 57 then return c - 48 end
      if c >= 97 and c <= 102 then return c - 87 end
      if c >= 65 and c <= 70 then return c - 55 end
      return -1
    end
    local parseValue
    local function parseHex4()
      local value = 0
      for i = 1, 4 do
        if atEnd() then parseFail("invalid escape") end
        local d = hexDigit(peek())
        if d < 0 then parseFail("invalid escape") end
        advance()
        value = value * 16 + d
      end
      return value
    end
    local function parseString()
      advance()
      local out = {}
      while true do
        if atEnd() then parseFail("unterminated string") end
        local c = peek()
        if c == 34 then advance(); return table.concat(out) end
        if c == 92 then
          advance()
          if atEnd() then parseFail("unterminated string") end
          local esc = peek()
          if esc == 34 then advance(); out[#out + 1] = string.char(34)
          elseif esc == 92 then advance(); out[#out + 1] = string.char(92)
          elseif esc == 47 then advance(); out[#out + 1] = string.char(47)
          elseif esc == 98 then advance(); out[#out + 1] = string.char(8)
          elseif esc == 102 then advance(); out[#out + 1] = string.char(12)
          elseif esc == 110 then advance(); out[#out + 1] = string.char(10)
          elseif esc == 114 then advance(); out[#out + 1] = string.char(13)
          elseif esc == 116 then advance(); out[#out + 1] = string.char(9)
          elseif esc == 117 then
            advance()
            local cp = parseHex4()
            if cp >= 55296 and cp <= 56319 then
              if atEnd() or peek() ~= 92 then parseFail("unpaired surrogate escape") end
              advance()
              if atEnd() or peek() ~= 117 then parseFail("unpaired surrogate escape") end
              advance()
              local lo = parseHex4()
              if lo < 56320 or lo > 57343 then parseFail("unpaired surrogate escape") end
              cp = 65536 + (cp - 55296) * 1024 + (lo - 56320)
            elseif cp >= 56320 and cp <= 57343 then
              parseFail("unpaired surrogate escape")
            end
            out[#out + 1] = __u8enc(cp)
          else
            parseFail("invalid escape")
          end
        elseif c < 32 then
          parseFail("unexpected character")
        else
          out[#out + 1] = __u8enc(advance())
        end
      end
    end
    local function parseLiteral(word, value)
      for i = 1, #word do
        if atEnd() then parseFail("unexpected end of input") end
        if peek() ~= string.byte(word, i) then parseFail("unexpected character") end
        advance()
      end
      return value
    end
    local function parseObject()
      advance()
      local t = {__t = true, __keys = {}, __order = {}}
      skipWs()
      if not atEnd() and peek() == 125 then advance(); return t end
      while true do
        skipWs()
        if atEnd() then parseFail("unexpected end of input") end
        if peek() ~= 34 then parseFail("missing key") end
        local key = parseString()
        skipWs()
        if atEnd() or peek() ~= 58 then parseFail("missing colon") end
        advance()
        skipWs()
        local value = parseValue()
        t[key] = value
        __orderAdd(t, key)
        skipWs()
        if atEnd() then parseFail("unterminated object") end
        local c = peek()
        if c == 44 then advance()
        elseif c == 125 then advance(); return t
        else parseFail("missing comma") end
      end
    end
    local function parseArray()
      advance()
      local a = {__a = true, __n = 0}
      skipWs()
      if not atEnd() and peek() == 93 then advance(); return a end
      while true do
        skipWs()
        if atEnd() then parseFail("unexpected end of input") end
        local value = parseValue()
        a.__n = a.__n + 1
        if value == nil then a[a.__n] = __NULL else a[a.__n] = value end
        skipWs()
        if atEnd() then parseFail("unterminated array") end
        local c = peek()
        if c == 44 then advance()
        elseif c == 93 then advance(); return a
        else parseFail("missing comma") end
      end
    end
    local function parseNumber()
      local startPos = pos
      local neg = false
      if peek() == 45 then neg = true; advance() end
      if atEnd() then parseFail("invalid number") end
      local c = peek()
      if c < 48 or c > 57 then parseFail("invalid number") end
      local integerForm = true
      if c == 48 then
        advance()
        if not atEnd() and peek() >= 48 and peek() <= 57 then
          parseFail("leading zero")
        end
      else
        advance()
        while not atEnd() and peek() >= 48 and peek() <= 57 do advance() end
      end
      if not atEnd() and peek() == 46 then
        integerForm = false
        advance()
        if atEnd() or peek() < 48 or peek() > 57 then parseFail("invalid number") end
        while not atEnd() and peek() >= 48 and peek() <= 57 do advance() end
      end
      if not atEnd() and (peek() == 101 or peek() == 69) then
        integerForm = false
        advance()
        if not atEnd() and (peek() == 43 or peek() == 45) then advance() end
        if atEnd() or peek() < 48 or peek() > 57 then parseFail("invalid number") end
        while not atEnd() and peek() >= 48 and peek() <= 57 do advance() end
      end
      local text = string.sub(s, startPos, pos - 1)
      if integerForm then
        local ds = text
        if neg then ds = string.sub(text, 2) end
        local sig = ds
        while #sig > 1 and string.sub(sig, 1, 1) == "0" do
          sig = string.sub(sig, 2)
        end
        local outOfRange = false
        if #sig > 10 then
          outOfRange = true
        elseif #sig == 10 then
          local limit = neg and "2147483648" or "2147483647"
          outOfRange = sig > limit
        end
        if not outOfRange then
          local value = tonumber(text)
          if value == 0 then value = 0 end
          return {__jn = true, k = "int", d = value}
        end
      end
      return {__jn = true, k = "number", d = tonumber(text)}
    end
    parseValue = function()
      if atEnd() then parseFail("unexpected end of input") end
      local c = peek()
      if c == 123 then return parseObject() end
      if c == 91 then return parseArray() end
      if c == 34 then return parseString() end
      if c == 116 then return parseLiteral("true", true) end
      if c == 102 then return parseLiteral("false", false) end
      if c == 110 then return parseLiteral("null", nil) end
      if c == 45 or (c >= 48 and c <= 57) then return parseNumber() end
      parseFail("unexpected character")
    end
    skipWs()
    local value = parseValue()
    skipWs()
    if not atEnd() then parseFail("trailing content") end
    return value
  elseif fn == "JSON_STRINGIFY" then
    local out = {}
    local path = {}
    -- The pinned STDLIB_CALL(JSON_STRINGIFY) rejection: the visible
    -- message carries the canonical actual-kind token, and the expected
    -- text and the token are the projection's expected/actual fields (the
    -- shared walker's internal fieldPath never surfaces).
    local function sfFail(actual)
      __sfail("E8001", "unsupported type for JSON encoding: "..actual,
        "string, number, boolean, or table", actual)
    end
    local sfValue
    -- The number slot flag is the written slot's recorded static kind
    -- (__numKey): a number-typed slot — integral values included —
    -- serializes through the closed decimal spelling, an int-typed
    -- slot through the integer spelling. Without the mark (a dynamic
    -- position, a __jn carrier, or a slot no shared write path wrote)
    -- the int spelling stands, exactly the JSON_PARSE carrier split.
    sfValue = function(v, isNumber)
      if v == nil then out[#out + 1] = "null"; return end
      if v == __MISSING then sfFail("missing"); return end
      local t = type(v)
      if t == "boolean" then
        out[#out + 1] = (v and "true" or "false")
        return
      end
      if t == "number" then
        if v ~= v or v == math.huge or v == -math.huge then
          sfFail("number")
        end
        if isNumber then out[#out + 1] = __sfNumText(v)
        else out[#out + 1] = tostring(v) end
        return
      end
      if t == "string" then out[#out + 1] = __jsonEscape(v); return end
      if t == "table" then
        if v.__jn then
          if v.k == "int" then out[#out + 1] = tostring(v.d)
          else
            if v.d ~= v.d or v.d == math.huge or v.d == -math.huge then
              sfFail("number")
            end
            out[#out + 1] = __sfNumText(v.d)
          end
          return
        end
        if v.__a then
          if path[v] then sfFail("array"); return end
          path[v] = true
          out[#out + 1] = "["
          local marks = v.__nK
          if type(marks) ~= "table" then marks = nil end
          for i = 1, v.__n do
            if i > 1 then out[#out + 1] = "," end
            local elem = v[i]
            -- A raw nil slot is the internal missing (the deleted
            -- element model, exactly the read-side __arrayRead mapping);
            -- a present null is the __NULL marker. The deleted element is
            -- never serialized as JSON null.
            if elem == __NULL then elem = nil
            elseif elem == nil then sfFail("missing") end
            sfValue(elem, marks ~= nil and marks[i] == true)
          end
          out[#out + 1] = "]"
          path[v] = nil
          return
        end
        if v.__t then
          if path[v] then sfFail("table"); return end
          path[v] = true
          out[#out + 1] = "{"
          local marks = v.__nK
          if type(marks) ~= "table" then marks = nil end
          for i = 1, #v.__order do
            if i > 1 then out[#out + 1] = "," end
            local k = v.__order[i]
            out[#out + 1] = __jsonEscape(k)
            out[#out + 1] = ":"
            sfValue(v[k], marks ~= nil and marks[k] == true)
          end
          out[#out + 1] = "}"
          path[v] = nil
          return
        end
        -- The class instance carries its canonical identity (the closed
        -- "class:<ClassId>" projection), never the carrier's shape: the
        -- marker is checked before the function arm (every class instance
        -- carries the field map __f).
        if v.__c then sfFail("class:"..v.__id); return end
        if v.__fn ~= nil or v.__f then sfFail("function"); return end
        if v.__d then sfFail("class:@builtin/Error"); return end
        sfFail("table")
        return
      end
      if t == "function" then sfFail("function"); return end
      sfFail("table")
    end
    sfValue(__args[1], false)
    return table.concat(out)
  elseif fn == "MATH_FLOOR" then
    return math.floor(__args[1])
  elseif fn == "MATH_CEIL" then
    return math.ceil(__args[1])
  elseif fn == "MATH_SQRT" then
    if __args[1] < 0 then
      __sfail("E8001", "sqrt of negative number", nil, __numHex(__args[1]))
    end
    return math.sqrt(__args[1])
  elseif fn == "MATH_ABS_INT" then
    local v = __args[1]
    return __int32Gate(v < 0 and -v or v)
  elseif fn == "MATH_ABS_NUMBER" then
    local v = __args[1]
    if v == 0 then return 0 end
    return math.abs(v)
  elseif fn == "MATH_MIN_INT" then
    return math.min(__args[1], __args[2])
  elseif fn == "MATH_MAX_INT" then
    return math.max(__args[1], __args[2])
  elseif fn == "TIME_NOW_MILLIS" then
    return os.time() * 1000
  end
  __sfail("E8001", "unknown stdlib call "..tostring(fn), nil, nil)
end
-- The mode-gated console effect of the two cataloged console rows (M4):
-- the row invoker's single-effect write, shared by the direct
-- STDLIB_CALL arm and the cataloged callable. STDOUT always carries the
-- real effect bytes (plus, in trace mode, the protocol record on the
-- dedicated trace stream — the two never collide); the STDERR channel
-- shares the trace stream, so trace mode publishes only the protocol
-- record (the effect's exact scalar text plus its channel) and
-- production mode the exact effect bytes.
local function __consoleEffect(channel, text)
  if channel == "STDOUT" then
    io.write(text.."\\n")
    io.stdout:flush()
    if __traceMode then
      io.stderr:write("F|CONSOLE_WRITE|STDOUT|"..__esc(text).."\\n")
      io.stderr:flush()
    end
  else
    if __traceMode then
      io.stderr:write("F|CONSOLE_WRITE|STDERR|"..__esc(text).."\\n")
    else
      io.stderr:write(text.."\\n")
    end
    io.stderr:flush()
  end
end
-- The text projection of one console invocation: the argument texts in
-- declared order joined by one space (the direct arm's projection
-- verbatim); zero arguments project the empty string.
local function __consoleText(...)
  local n = select("#", ...)
  if n == 0 then return "" end
  local parts = {}
  for i = 1, n do parts[i] = tostring((select(i, ...))) end
  return table.concat(parts, " ")
end
-- The one row invoker of the closed catalog (M4): the single callable
-- realization per catalog row, shared by the direct STDLIB_CALL arm and
-- the cataloged callable (and by the dynamic dispatch's HOST sub-class,
-- which passes the invoking CALL op's own kind label). The two console
-- rows run the single-effect write through __consoleEffect; every
-- algorithmic row delegates to __stdlib (the row identity and the
-- invoking call's context travel through unchanged — one algorithm
-- authority, never two).
local function __stdlibInvoke(kind, fn, opKey, digest, parent, origin, ...)
  if fn == "CONSOLE_LOG" then
    __consoleEffect("STDOUT", __consoleText(...))
    return nil
  elseif fn == "CONSOLE_ERROR" then
    __consoleEffect("STDERR", __consoleText(...))
    return nil
  end
  return __stdlib(kind, fn, opKey, digest, parent, origin, ...)
end
-- The memoized cataloged callable of one catalog row (M4): one carrier
-- per catalog row per module per program — {__fn = the row invoker,
-- __sig = the row's declared descriptor text, __csig = the row's
-- canonical spec text, __fid = nil, __sid = the row tag}, admissible by
-- the landed function row. Creation goes through this one accessor, so
-- a read before any surface population and the later whole-surface
-- population observe one callable object. The registry is chunk-global
-- (one program), exactly like the export-surface registry.
local function __stdlibEntry(module, name, sid, sig, csig)
  local key = module..string.char(1)..name
  local entry = __stdlibEntries[key]
  if entry == nil then
    entry = {__fn = function(kind, opKey, digest, parent, origin, ...)
        return __stdlibInvoke(kind, sid, opKey, digest, parent, origin, ...)
      end,
      __sig = sig, __csig = csig, __fid = nil, __sid = sid}
    __stdlibEntries[key] = entry
  end
  return entry
end
""";
}
