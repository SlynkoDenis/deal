package deal.codegen.jvm;

import deal.semantic.HostDeclarationSurface;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.ChainOperandCompletion;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
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
 * The shared JVM emitter of the decomposition-tail integration
 * verification (ISSUE-0410): emits a real Java artifact from the
 * validated {@link LoweredModuleUnit} + {@link StructuredBodyTable} over
 * the EVALUATION_ORDER op set (binary-comparison-selectors B-D6;
 * control-flow-structures C-D9; assignment-delete-address-chains A-D8):
 *
 * <ul>
 *   <li><b>Chains:</b> every chain child's result is materialized into a
 *       fresh local in payload order before the next child executes; the
 *       bounds check runs only from the boundary child's projection;
 *       receiver/key/RHS expressions are never re-emitted; the retained
 *       Lua {@code emitAssignment} double-evaluation shape never
 *       appears.</li>
 *   <li><b>Comparisons:</b> ints via primitive comparison; number EQ via
 *       IEEE {@code ==} (never {@code Double.compare}) and orderings via
 *       {@code <}/{@code <=}/{@code >}/{@code >=} predicates (NaN false);
 *       string order via code point comparison (never
 *       {@code String.compareTo}); reference identity via {@code ==}
 *       (never {@code equals()}).</li>
 *   <li><b>Control flow:</b> no speculative execution; condition ops
 *       emitted inside the loop structure and re-evaluated per
 *       iteration; the {@code FOR_EACH} iterable materialized into a
 *       local before the loop; the short-circuited block behind a guard;
 *       FOR's continue landing before the update; block code generated
 *       per the {@code StructuredBodyTable} membership; catches limited
 *       to DEAL errors ({@code DealError} — infrastructure failures are
 *       never caught or reified).</li>
 * </ul>
 *
 * <p>The artifact publishes its execution report on the dedicated trace
 * channel (stderr) through the
 * {@link deal.semantic.SemanticTraceProtocol} line grammar via
 * {@link JvmRuntime} — byte-identical to the semantic oracle's report —
 * and writes real console effect bytes to stdout.</p>
 */
public final class JvmSemanticEmitter {

    private JvmSemanticEmitter() {
    }

    /** The emitted Java artifact: the class name plus the source text. */
    public record EmissionResult(String className, String source) {
    }

    /** Emits the complete shared-JVM artifact for the validated unit. */
    public static EmissionResult emitModule(LoweredModuleUnit unit,
                                            StructuredBodyTable table) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        return new Session(unit, table).emit();
    }

    /**
     * Emits the combined trace artifact of a validated executable
     * project (the cross-module CLASSES surface): one class carries
     * every module's slots/cells, function factories, adapter thunks,
     * detached class-default methods, and the generated class carriers,
     * then runs each module's init walk in dependency order (each under
     * its own {@code MODULE} tag). A caller's
     * {@code CLASS_NEW(SHARED_FACTORY)} arm resolves the owner's factory
     * op and default blocks through the closure, so the owner-side
     * events carry the owner's module path and the factory's cross-unit
     * parent. Single-unit sessions are the singleton closure of the same
     * machinery.
     *
     * @param project    the validated executable closure; non-null
     * @param tables     each module's block-membership table; non-null
     * @param registries each module's class-factory registry; non-null
     * @return the combined artifact
     */
    public static EmissionResult emitProject(ExecutableLoweredProject project,
                                             Map<ModuleId, StructuredBodyTable> tables,
                                             Map<ModuleId, ClassFactoryRegistry> registries) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        return new Session(project, tables, registries, true, null, null).emit();
    }

    /**
     * Emits the combined trace artifact of a validated executable
     * project with the compile's host declaration surface (ISSUE-0651;
     * the differential drive of the sync host call realization): the
     * trace-mode project session of {@link #emitProject} additionally
     * carries the JVM host ABI emission surface, so a
     * {@code MODULE_IMPORT(HOST)} emits its module load entry and a host
     * {@code CALL}/{@code CALLBACK_INVOKE} arm resolves the emitted
     * per-export wrapper — the oracle-agreement drive (“the oracle
     * matches event-for-event in trace mode”) then compares one event
     * stream from the oracle and both targets. The trace session keeps
     * the shared conformance class name (the {@code $DealRt} scope's
     * bridges delegate to {@code __hostProjectArg}/{@code __hostToDeal}
     * of it).
     *
     * @param project            the validated executable closure; non-null
     * @param tables             each module's block-membership table;
     *                           non-null
     * @param registries         each module's class-factory registry;
     *                           non-null
     * @param declarationSurface the declaration surface covering every
     *                           declaration import of the compile; non-null
     * @return the emitted combined trace artifact
     */
    public static EmissionResult emitProject(ExecutableLoweredProject project,
                                             Map<ModuleId, StructuredBodyTable> tables,
                                             Map<ModuleId, ClassFactoryRegistry> registries,
                                             HostDeclarationSurface declarationSurface) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        Objects.requireNonNull(declarationSurface,
            "declarationSurface must not be null");
        return new Session(project, tables, registries, true, null,
            declarationSurface).emit();
    }

    /**
     * Emits the production JVM project artifact for the validated
     * executable closure (the production counterpart of
     * {@link #emitProject}; {@code production-project-emission-and-atomic-cutover}
     * P1/P2/P3 and the production JVM emission contract): one
     * {@code public final class <className>} carrying the whole closure
     * with {@code public static void main(String[])}, the conformance
     * trace protocol suppressed, the landed {@code DEAL_ERROR_CODE: <code>}
     * terminal (a DEAL failure publishes the code line on stdout and
     * exits 1; success exits 0 silently), the entry module's one
     * {@code ENTRY_INVOKE} delegation, and the per-module export-surface
     * registry keyed by the module identity.
     *
     * <p>The class name is used verbatim: the production arm passes the
     * {@code JvmBackend.classNameFor(entryModule.path())} derivation. The
     * entry consumes only the validated project, the per-module body
     * tables and class-factory registries, that class name, and the
     * compile's host declaration surface — no AST, no {@code CheckResult},
     * no route input, and no extern-C generated-module input. The
     * declaration surface is the single source of the host ABI emission
     * surface this entry emits (ISSUE-0650;
     * {@code host-module-load-and-host-call-realization} H2 and H7's
     * carrier set): the module-keyed load entries with the declared
     * parameter-class projection, the per-export wrappers with the declared
     * parameter/return cells, the {@code <C>_defaults} captures, and the
     * synthesized {@code $DealRt} host-record and host-carrier scope.</p>
     *
     * @param project            the validated executable closure; non-null
     * @param tables             each module's block-membership table;
     *                           non-null
     * @param registries         each module's class-factory registry;
     *                           non-null
     * @param className          the entry class name, used verbatim; non-null
     * @param declarationSurface the declaration surface covering every
     *                           declaration import of the compile; non-null
     * @return the emitted production project artifact
     */
    public static EmissionResult emitProductionProject(ExecutableLoweredProject project,
                                                       Map<ModuleId, StructuredBodyTable> tables,
                                                       Map<ModuleId, ClassFactoryRegistry> registries,
                                                       String className,
                                                       HostDeclarationSurface declarationSurface) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        Objects.requireNonNull(className, "className must not be null");
        Objects.requireNonNull(declarationSurface,
            "declarationSurface must not be null");
        return new Session(project, tables, registries, false, className,
            declarationSurface).emit();
    }

    /**
     * Emits the production JVM module artifact for the validated unit
     * (ISSUE-0239 E10): the conformance trace protocol is suppressed, a
     * DEAL failure publishes the retained {@code DEAL_ERROR_CODE: <code>}
     * line on stdout and exits 1, and the {@code ENTRY_INVOKE} delegation
     * executes only for the entry module. The class name is the retained
     * backend's derivation ({@code JvmBackend.classNameFor(modulePath)}),
     * so the emitted artifact set keeps the retained layout.
     *
     * @param unit        the validated lowered module unit; non-null
     * @param table       the unit's produced block-membership table; non-null
     * @param entryModule whether this module is the selected entry module
     * @param className   the retained-layout class name of the artifact
     * @return the emitted production artifact
     */
    public static EmissionResult emitProductionModule(LoweredModuleUnit unit,
                                                      StructuredBodyTable table,
                                                      boolean entryModule,
                                                      String className) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(className, "className must not be null");
        return new Session(unit, table, false, entryModule, className).emit();
    }

    // =========================================================================
    // Session
    // =========================================================================

    /**
     * The runtime-side descriptor text of one descriptor (the closed
     * {@code null|boolean|int|number|string|table|array(INNER)|
     * nullable(INNER)|function(PARAMS;RETURN)} form the runtime checks
     * dispatch on): the single producer of the text the emitted boundary
     * rows, the host ABI cell checks, and a bridged host surface entry's
     * carried signature all use.
     */
    static String runtimeDescriptorText(RuntimeDescriptor descriptor) {
        return Session.descriptorText(descriptor);
    }

    /**
     * The production projection of one checked host return held as an
     * {@code java.lang.Object} (the host-check seam's result, the
     * reflective host invocation's result): the declared carrier is
     * reconciled with the production value carrier — a numeric or boolean
     * position unboxes through its boxed form (a {@code null}-safe form for
     * a {@code ?} position), a declared array or function return crosses
     * back into the production carriers through the host-to-DEAL
     * projection, and every other reference carrier is the production value
     * itself.
     *
     * @param declaredReturn the declared position's type; non-null
     * @param expression     the Java expression holding the object-held value; non-null
     * @return the Java expression holding the production value carrier; non-null
     */
    static String checkedResultOf(Type declaredReturn, String expression) {
        Type inner = declaredReturn instanceof Type.Nullable nullable
            ? nullable.inner() : declaredReturn;
        boolean nullable = declaredReturn instanceof Type.Nullable;
        if (inner instanceof Type.Int) {
            String unbox = "java.lang.Long.valueOf(((java.lang.Number) "
                + expression + ").longValue())";
            return nullable
                ? "(" + expression + " == null ? null : " + unbox + ")"
                : unbox;
        }
        if (inner instanceof Type.Number) {
            String unbox = "java.lang.Double.valueOf(((java.lang.Number) "
                + expression + ").doubleValue())";
            return nullable
                ? "(" + expression + " == null ? null : " + unbox + ")"
                : unbox;
        }
        if (inner instanceof Type.Boolean && !nullable) {
            return "java.lang.Boolean.valueOf(((java.lang.Boolean) "
                + expression + ").booleanValue())";
        }
        if (inner instanceof Type.Array || inner instanceof Type.Func
                || inner instanceof Type.Bytes) {
            return "__hostToDeal("
                + Session.javaString(JvmHostAbiEmission.descriptorText(
                    declaredReturn))
                + ", " + expression + ")";
        }
        return expression;
    }

    /**
     * The production value carrier of one declared host position (the host
     * ABI's shared scalar rule): the host-facing scalar carriers differ from
     * the production carriers for the signed32 int (a host primitive/boxed
     * {@code int} is the production {@code Long}), the projected
     * array/function returns are already production values, and a nullable
     * position keeps the language null.
     *
     * @param declaredReturn the declared position's type; non-null
     * @param expression     the Java expression holding the host-facing value; non-null
     * @return the Java expression holding the production value carrier; non-null
     */
    static String productionValueOf(Type declaredReturn, String expression) {
        Type inner = declaredReturn instanceof Type.Nullable nullable
            ? nullable.inner() : declaredReturn;
        boolean nullable = declaredReturn instanceof Type.Nullable;
        if (inner instanceof Type.Int) {
            return nullable
                ? "(" + expression + " == null ? null :"
                    + " java.lang.Long.valueOf(((java.lang.Number) "
                    + expression + ").longValue()))"
                : "java.lang.Long.valueOf(" + expression + ")";
        }
        if (inner instanceof Type.Number) {
            return nullable
                ? "(" + expression + " == null ? null : java.lang.Double.valueOf("
                    + "((java.lang.Number) " + expression + ").doubleValue()))"
                : "java.lang.Double.valueOf(" + expression + ")";
        }
        if (inner instanceof Type.Boolean && !nullable) {
            return "java.lang.Boolean.valueOf(" + expression + ")";
        }
        return expression;
    }

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
        /**
         * The derived cell kind of every binding incarnation, keyed by
         * {@code {binding, generation}} (B2: the final kind is a property
         * of the <em>incarnation</em> — a for-let counter's generation-0
         * cell stays {@code DIRECT} while its captured per-iteration
         * generation-1 cell is {@code SHARED_CELL}). A missing entry is
         * {@code DIRECT}.
         */
        final Map<BindingId, Map<Long, BindingCellKind>> cellKinds = new HashMap<>();
        /**
         * The function factory currently being emitted (null in the module
         * region and in the detached class-default/thunk emitters): its
         * {@code captures} name the factory parameters, so a reference to a
         * captured binding inside its body reads the capture itself (never
         * a module-global cell slot) and a nested creation passes the
         * captured cell along.
         */
        LoweredFunction currentFunction;

        /** The derived cell kind of one binding incarnation ({@code DIRECT} when unknown). */
        BindingCellKind cellKindOf(BindingId binding, long generation) {
            Map<Long, BindingCellKind> generations = cellKinds.get(binding);
            if (generations == null) {
                return BindingCellKind.DIRECT;
            }
            return generations.getOrDefault(generation, BindingCellKind.DIRECT);
        }

        /** Registers one incarnation's derived cell kind (first emission wins). */
        void registerCellKind(BindingId binding, long generation, BindingCellKind kind) {
            cellKinds.computeIfAbsent(binding, k -> new HashMap<>())
                .putIfAbsent(generation, kind);
        }

        /** The capture parameter name of one captured binding. */
        String captureCell(BindingId binding) {
            return "c" + binding.id();
        }

        /**
         * True iff the function factory being emitted captures the binding
         * (its factory parameter is the body's binding source).
         */
        boolean isCurrentCapture(BindingId binding) {
            return currentFunction != null && currentFunction.captureOf(binding) != null;
        }

        /**
         * The cell expression of one {@code {binding, generation}} reference
         * at the current emission context: the enclosing factory's capture
         * parameter when the binding is one of its captures, otherwise the
         * class-scoped cell field naming the creation-site incarnation.
         */
        String cellSource(BindingId binding, long generation) {
            return isCurrentCapture(binding) ? captureCell(binding)
                : cell(binding, generation);
        }

        /**
         * One {@code CLOSURE_NEW}/group-member/general-invocation capture
         * argument: the enclosing factory's capture parameter when the
         * creating body captured the binding (the cell travels the chain),
         * otherwise the class-scoped cell field of the creation-site
         * incarnation (never a hard-coded generation 0 — a for-let capture
         * names the per-iteration incarnation).
         */
        String captureArg(BindingGeneration capture) {
            return cellSource(capture.binding(), capture.generation());
        }
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
        /** The selected entry module runs the ENTRY_INVOKE delegation. */
        final boolean entryModule;
        /** Ops the block walk skips (the entry delegation of a non-entry module). */
        final java.util.Set<OpId> skippedOps = new java.util.HashSet<>();
        final StringBuilder out = new StringBuilder();
        /** The enclosing TRY_CATCH depth: transfers inside a try body
         *  signal via JvmRuntime.Transfer and re-apply in the dispatch. */
        int tryDepth = 0;
        /** Structure ancestors are computed statically from the block tree
         *  per transfer (never a runtime-sensitive stack). */
        final String className;
        /**
         * The JVM host ABI emission surface of the production project
         * session (ISSUE-0650): non-null exactly when the session is the
         * production project entry and the closure imports a host
         * declaration module.
         */
        final JvmHostAbiEmission hostAbi;

        Session(LoweredModuleUnit unit, StructuredBodyTable table) {
            this(unit, table, true, true, null);
        }

        Session(LoweredModuleUnit unit, StructuredBodyTable table, boolean trace,
                boolean entryModule, String className) {
            this.unit = unit;
            this.table = table;
            this.trace = trace;
            this.projectSession = false;
            this.entryModule = entryModule;
            // The artifact class name resolves before the host seam: the
            // seam's emitted members delegate to the artifact class's
            // crossing helpers, so the seam needs the name.
            if (className != null) {
                this.className = className;
            } else {
                this.className = sharedClassName(unit.moduleId().path());
            }
            // The seam-only host ABI (the project session's rule, applied to
            // one unit): a unit whose op walk carries host-boundary cells of
            // its own (the DEAL_TO_HOST/HOST_PARAMETER/HOST_TO_DEAL/
            // HOST_SYNC_RETURN family — a dynamic call's recorded return
            // cells, a stdlib export read's host cells) emits checks the host
            // seam realizes, so the artifact compiles with the emitted seam.
            // A unit carrying a host import keeps the landed null (its
            // declaration surface is the production project session's).
            this.hostAbi = !unitHasHostImports(unit)
                    && unitHasHostCellBoundaries(unit)
                ? new JvmHostAbiEmission(java.util.List.of(), this.className)
                : null;
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
         * Whether the closure's op walk carries a HOST-kind import (a host or
         * extern-C declaration module).
         */
        private static boolean closureHasHostImports(ExecutableLoweredProject project) {
            for (LoweredModuleUnit moduleUnit : project.modules().values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.MODULE_IMPORT
                            && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                                == deal.semantic.ir.ModuleImportKind.HOST) {
                        return true;
                    }
                }
            }
            return false;
        }

        /**
         * Whether the closure's op walk carries at least one host-boundary cell
         * (the DEAL_TO_HOST/HOST_PARAMETER/HOST_TO_DEAL/HOST_SYNC_RETURN family
         * the emitted host seam's checks realize).
         */
        private static boolean closureHasHostCellBoundaries(
                ExecutableLoweredProject project) {
            for (LoweredModuleUnit moduleUnit : project.modules().values()) {
                if (unitHasHostCellBoundaries(moduleUnit)) {
                    return true;
                }
            }
            return false;
        }

        /**
         * Whether one unit's op walk carries at least one host-boundary cell
         * (the single-unit twin of {@link #closureHasHostCellBoundaries}).
         */
        private static boolean unitHasHostCellBoundaries(LoweredModuleUnit unit) {
            for (SemanticOp op : unit.ops()) {
                if (!(op.payload() instanceof KindPayload.BoundaryPayload boundary)) {
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
            return false;
        }

        /** Whether one unit's op walk carries a HOST-kind import. */
        private static boolean unitHasHostImports(LoweredModuleUnit unit) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT
                        && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                            == ModuleImportKind.HOST) {
                    return true;
                }
            }
            return false;
        }

        /**
         * The project-mode session (the cross-module factory surface):
         * every module's unit, table, and class-factory registry in one
         * combined artifact — the CLASS_NEW(SHARED_FACTORY) arm resolves
         * the owner's factory op and default blocks through the closure.
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                String className) {
            this(project, tables, registries, trace, className, null);
        }

        /**
         * The project-mode session of the production project entry (and,
         * since ISSUE-0651, of the host-aware trace project entry): the
         * combined closure plus the compile's host declaration surface
         * (the JVM host ABI emission surface). A session without the
         * surface carries no host ABI (the unit sessions and the
         * host-free trace project session).
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                String className, HostDeclarationSurface hostSurface) {
            // The artifact class name is resolved before the host ABI
            // construction: the emitted $DealRt scope's bridges delegate
            // to the artifact class's crossing helpers, so a trace-mode
            // project session (the shared conformance name) carries the
            // resolved name too (ISSUE-0651).
            String resolvedClassName = className != null ? className
                : sharedClassName(project.modules().containsKey(project.entryModule())
                    ? project.modules().get(project.entryModule()).moduleId().path()
                    : project.entryModule().path());
            // The host ABI emission surface: the compile's declaration surface
            // when the session carries one, and — since ISSUE-0678 — a
            // seam-only surface for a closure whose op walk carries
            // host-boundary cells of its own (the
            // DEAL_TO_HOST/HOST_PARAMETER/HOST_TO_DEAL/HOST_SYNC_RETURN family):
            // a spec-stdlib declared-function export read called as a value
            // carries that family (K2) without any host import, and its emitted
            // checks are the seam's. A session with host imports keeps its
            // landed surface (or its landed null: the scenario-seam sessions).
            this.hostAbi = hostSurface != null
                ? new JvmHostAbiEmission(JvmHostAbiEmission.collect(project, hostSurface),
                    resolvedClassName)
                : (!closureHasHostImports(project) && closureHasHostCellBoundaries(project)
                    ? new JvmHostAbiEmission(java.util.List.of(), resolvedClassName)
                    : null);
            this.unit = project.modules().get(project.entryModule());
            this.table = tables.get(project.entryModule());
            if (this.unit == null || this.table == null) {
                throw new IllegalArgumentException(
                    "the entry module is not in the executable closure");
            }
            this.trace = trace;
            this.projectSession = true;
            this.entryModule = true;
            // A production project entry passes its class name verbatim
            // (the JvmBackend.classNameFor(entry path) derivation); the
            // trace project session keeps the shared conformance name.
            this.className = resolvedClassName;
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

        /** The shared conformance class name of a module path (cross-module ABI). */
        static String sharedClassName(String modulePath) {
            StringBuilder name = new StringBuilder("SharedM");
            for (char c : modulePath.toCharArray()) {
                name.append(Character.isJavaIdentifierPart(c) ? c : '_');
            }
            return name.toString();
        }

        // -- naming ---------------------------------------------------------------

        String slot(ValueId id) {
            return "v" + id.id();
        }

        String cell(BindingId id, long generation) {
            return "b" + id.id() + "g" + generation;
        }

        String fnFactory(FunctionId id) {
            return "F" + id.id();
        }

        String loopLabel(OpId opId) {
            return "LOOP" + opId.id();
        }

        // -- static kinds -----------------------------------------------------------

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
            if (descriptor instanceof RuntimeDescriptor.Bytes) {
                return "bytes";
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

        /** The runtime-side descriptor text for a boundary check. */
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
            if (descriptor instanceof RuntimeDescriptor.Bytes) {
                return "bytes";
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

        // -- java literals -----------------------------------------------------------

        /**
         * The expression of one prelude boundary check: the descriptor
         * text, the static kind, the value, and — when the descriptor
         * carries a function position — the descriptor's canonical spec
         * text as the trailing argument, so the function row projects the
         * pinned canonical signature texts ({@code function signature
         * mismatch: expected (int)->int, got (int)->string}) on every
         * consumer. The text of every non-function check is emitted
         * unchanged (no canonical trailer).
         */
        static String bcheckArgs(RuntimeDescriptor descriptor, String value) {
            return bcheckArgs("JvmRuntime.bcheck", descriptor, value);
        }

        /**
         * The completion cell's expression over one awaited function-typed
         * completion (the {@code AWAIT} boundary): the same canonical trailer
         * as {@link #bcheckArgs(RuntimeDescriptor, String)}.
         */
        static String bcheckCompletionArgs(RuntimeDescriptor descriptor,
                                           String value) {
            return bcheckArgs("JvmRuntime.bcheckCompletion", descriptor, value);
        }

        private static String bcheckArgs(String method, RuntimeDescriptor descriptor,
                                         String value) {
            String args = javaString(descriptorText(descriptor)) + ", "
                + javaString(staticKind(descriptor)) + ", " + value;
            if (containsFunction(descriptor)) {
                args += ", " + javaString(descriptor.canonicalSpecText());
            }
            return method + "(" + args + ")";
        }

        /** Whether one descriptor carries a function position (recursively). */
        static boolean containsFunction(RuntimeDescriptor descriptor) {
            if (descriptor instanceof RuntimeDescriptor.Func) {
                return true;
            }
            if (descriptor instanceof RuntimeDescriptor.Array array) {
                return containsFunction(array.element());
            }
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                return containsFunction(nullable.inner());
            }
            return false;
        }

        static String javaString(String text) {
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
                        if (c < 0x20 || c > 0x7e) {
                            sb.append(String.format("\\u%04x", (int) c));
                        } else {
                            sb.append(c);
                        }
                    }
                }
            }
            sb.append('"');
            return sb.toString();
        }

        // -- emission ----------------------------------------------------------------

        EmissionResult emit() {
            out.append("import deal.codegen.jvm.JvmRuntime;\n");
            out.append("import deal.codegen.jvm.JvmJson;\n");
            out.append("import java.util.List;\n");
            out.append("\npublic final class ").append(className).append(" {\n");
            // Mutable so the combined walk and the cross-unit factory
            // transfer can switch the current module per module walk
            // (each event carries its op's module path).
            out.append("  public static String MODULE = ")
                .append(javaString(unit.moduleId().path())).append(";\n");
            // The per-module export-surface registry (K15 item 1: the
            // module's namespace value): one JvmRuntime.Table per module of
            // the closure, keyed by the module identity (the dotted module
            // path), created idempotently before the module walks so a
            // repeated dealMain() drive never wipes a published surface.
            // The registry is hosted by the runtime (M2), so every
            // generated class of one program resolves the same per-module
            // surfaces; the class-level field and accessor are the
            // compatible per-class view of that program-scoped registry
            // (the compiled fixture runners reference the field).
            out.append("  static final java.util.LinkedHashMap<String, "
                + "JvmRuntime.Table> EXPORT_SURFACES = JvmRuntime.EXPORT_SURFACES;\n");
            // The program-scoped active-function markers of the re-entrant
            // invocation-state save (ISSUE-0654): hosted by the runtime so
            // the per-unit classes of one program share them.
            out.append("  static final java.util.HashSet<Long> __bodyActive = "
                + "JvmRuntime.BODY_ACTIVE;\n");
            out.append("\n  static JvmRuntime.Table exportSurface(String module) {\n");
            out.append("    return JvmRuntime.exportSurface(module);\n");
            out.append("  }\n");
            // The dynamic dispatch's function-id -> owning-module
            // resolution (ISSUE-0658;
            // dynamic-call-shape-production-and-emission Y6): a generated
            // lookup over the closure's function ids, so the DEAL_BODY
            // class path establishes the callee's module before invoking
            // the resolved carrier's own invoker. A function id the
            // closure does not carry resolves null and the dynamic call
            // fails closed at its origin.
            out.append("\n  /**\n   * The owning module path of one lowered function id of this\n"
                + "   * closure, or null for an id outside the closure.\n   */\n");
            out.append("  static String dealModuleOfFunction(String fid) {\n");
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (LoweredFunction function : moduleUnit.functions().values()) {
                    out.append("    if (").append(javaString(
                            String.valueOf(function.functionId().id())))
                        .append(".equals(fid)) return ")
                        .append(javaString(moduleUnit.moduleId().path()))
                        .append(";\n");
                }
            }
            out.append("    return null;\n");
            out.append("  }\n");
            // Slots and cells (every module; ids are globally unique). A
            // value slot is declared per op result and per op operand: an
            // operand whose identity no op of the closure produces (the
            // producer-less seeded intrinsic identity) is still read by its
            // consuming op's START atom and by the enclosing body's
            // re-entrant state snapshot, so its field must exist.
            java.util.LinkedHashSet<String> fields = new java.util.LinkedHashSet<>();
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.result() instanceof ValueId valueId) {
                        fields.add(slot(valueId));
                    }
                    for (ValueId operand : op.operands()) {
                        fields.add(slot(operand));
                    }
                    switch (op.payload()) {
                        case KindPayload.BindingAllocPayload payload ->
                            fields.add(cell(payload.binding(), payload.generation()));
                        case KindPayload.BindingInitPayload payload ->
                            fields.add(cell(payload.binding(), payload.generation()));
                        case KindPayload.BindingLoadPayload payload ->
                            fields.add(cell(payload.binding(), payload.generation()));
                        case KindPayload.BindingStorePayload payload ->
                            fields.add(cell(payload.binding(), payload.generation()));
                        case KindPayload.RecursiveGroupInitPayload payload -> {
                            for (BindingId binding : payload.bindings()) {
                                fields.add(cell(binding, 0));
                            }
                        }
                        case KindPayload.ForEachPayload payload ->
                            fields.add(cell(payload.binding(), payload.generation()));
                        case KindPayload.TryCatchPayload payload ->
                            fields.add(cell(payload.catchBinding(), 0));
                        default -> {
                        }
                    }
                }
            }
            for (String field : fields) {
                out.append("  static Object ").append(field).append(";\n");
            }
            // The host ABI surface (ISSUE-0650): the module-keyed load and
            // binding fields, the per-module load entries, the per-export
            // wrappers, and the emitted boundary-check seam.
            if (hostAbi != null) {
                hostAbi.emitClassMembers(out);
            }
            // Function factories (every module).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (LoweredFunction function : moduleUnit.functions().values()) {
                    emitFunctionFactory(function);
                }
            }
            // The REEVALUATE_THUNK re-executor methods: one detached
            // thunk method per FUNCTION_ADAPT op with a thunk source.
            // The thunk ops are members only of the detached thunk block
            // (the lowerer's single-membership rule), so the module walk
            // never executes them; each invocation re-executes them here.
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() != SemanticOpKind.FUNCTION_ADAPT) {
                        continue;
                    }
                    KindPayload.FunctionAdaptPayload payload =
                        (KindPayload.FunctionAdaptPayload) op.payload();
                    if (payload.source() instanceof AdaptSourceRef.Thunk thunk) {
                        emitThunkMethod(op, thunk.blockId());
                    }
                }
            }
            // The detached class-default methods (E5): one per
            // CLASS_DEFAULT op — the default block's ops (the default op
            // itself skipped) re-execute per invocation, returning the
            // block's final producing value (the op's result slot), so
            // every triggering construction gets a fresh default
            // (mutable defaults allocate freshly per attempt).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        emitClassDefaultMethod(op);
                    }
                }
            }
            // The generated class carriers (E5): one static nested class
            // per ClassId of the resolution context with per-field value
            // slots plus boolean presence flags, tagged with the
            // canonical class identity.
            emitClassCarriers();
            // The per-class JSON plans (E7/K-D8/K-D10): one plan per class
            // layout of the resolution context — declaration-order fields
            // with descriptor, optionality, static result kind, and the
            // per-field CLASS_DEFAULT child metadata the JSON_FROM_CLASS
            // walk consumes (the lowerer's per-site JsonDefaultChildTable
            // entry, derived from the unit: one CLASS_DEFAULT op per
            // (classId, field)).
            for (ClassLayout layout : classLayouts.values()) {
                emitJsonPlan(layout);
            }
            // The module-init walk, exposed as the deferred-main entry (the
            // scenario host drives it explicitly for an async-entry
            // invocation or a multi-module drive): setup plus the walk;
            // main publishes the retained terminal contract around it.
            out.append("  public static void dealMain() {\n");
            out.append("    JvmRuntime.setModule(MODULE);\n");
            out.append("    JvmRuntime.setTraceEnabled(").append(trace).append(");\n");
            // Every closure module's surface exists before any module walk
            // (the idempotent get-or-create keeps a repeated drive's
            // published surfaces intact).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                out.append("    exportSurface(")
                    .append(javaString(moduleUnit.moduleId().path())).append(");\n");
            }
            emitStdlibSurfacePopulation(2);
            emitProjectWalk(2);
            out.append("  }\n");
            // main.
            out.append("  public static void main(String[] args) {\n");
            if (trace) {
                out.append("    try {\n");
                out.append("      dealMain();\n");
                out.append("      System.err.println(\"R|success|null\");\n");
                out.append("      System.err.flush();\n");
                out.append("    } catch (JvmRuntime.DealError e) {\n");
                out.append("      System.err.println(\"R|failure|\" + JvmRuntime.errtext(e));\n");
                out.append("      System.err.flush();\n");
                out.append("    }\n");
            } else {
                // Production terminal: a DEAL failure publishes the
                // retained DEAL_ERROR_CODE line on stdout and exits 1.
                out.append("    try {\n");
                out.append("      dealMain();\n");
                out.append("    } catch (JvmRuntime.DealError e) {\n");
                out.append("      System.out.println(\"DEAL_ERROR_CODE: \" + e.code);\n");
                out.append("      System.out.flush();\n");
                out.append("      System.exit(1);\n");
                out.append("    }\n");
            }
            out.append("  }\n");
            // The host-driven callback dispatch entries (CALLBACK_INVOKE):
            // one per-unit static entry per recorded invocation. The
            // scenario host invokes the entry top-level with scripted
            // arguments; the module-init walk never runs the unattached
            // records themselves.
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.CALLBACK_INVOKE) {
                        emitCallbackInvoke(op, 1);
                    }
                }
            }
            // The host-driven async-entry dispatch entries (async
            // EXTERNAL_ENTRY): one entry per recorded async export of
            // every closure unit — the scenario host adapter's invocation
            // surface (the E6 dispatch-entry pattern). The entry creates
            // the callee's canonical task; the drive flag makes the
            // top-level scenario invocation drain it and return the
            // completion, while a cross-module caller passes the drive
            // flag false (its AWAIT drains). The per-closure loop is the
            // same shape the CALLBACK_INVOKE entries above use: a
            // non-entry module's async export is reachable in the one
            // artifact (ISSUE-0655, cross-module-call-realization X2).
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                            && ((KindPayload.ExternalEntryPayload) op.payload()).async()) {
                        emitAsyncEntry(op, 1, moduleUnit);
                    }
                }
            }
            out.append("}\n");
            // The synthesized top-level $DealRt host-record and host-carrier
            // scope (ISSUE-0650): the deployed host implementations compile
            // against these classes unchanged. Emitted exactly for a
            // production project session carrying a host import.
            if (hostAbi != null) {
                hostAbi.emitScope(out);
            }
            return new EmissionResult(className, out.toString());
        }

        /** The combined walk: each module's init block in dependency order. */
        private void emitProjectWalk(int indent) {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                out.append(indent(indent)).append("MODULE = ")
                    .append(javaString(moduleUnit.moduleId().path())).append(";\n");
                // Every MODULE switch is mirrored into JvmRuntime's module
                // context: the runtime helpers (raise/arith/bcheck/...) emit
                // their events through currentModule(), so a helper-raised
                // failure in a non-entry module must carry that module.
                out.append(indent(indent)).append("JvmRuntime.setModule(MODULE);\n");
                SemanticOp moduleInitOp = moduleInitOpOf(moduleUnit);
                if (moduleInitOp == null) {
                    // A hand-built unit without the lowerer-produced op runs
                    // the bare init block, exactly the pre-envelope behavior.
                    emitBlockOps(moduleUnit.moduleInit().initBlock(), indent);
                } else {
                    emitModuleInit(moduleInitOp, indent);
                }
            }
        }

        /**
         * MODULE_INIT (E8; ISSUE-0590): the emitted module envelope — the
         * op's START, the payload init block (the {@code MODULE_IMPORT}/
         * {@code EXPORT_*}/entry-delegation ops nested under it) inside a
         * try so an uncaught DEAL failure publishes the op's single
         * FAILURE terminal recording {@code FAILED(error)} (no export
         * publication) before the error propagates to the retained
         * terminal, and the SUCCESS terminal publishing
         * {@code state:INITIALIZED}. The closed
         * {@code UNINITIALIZED -> INITIALIZING -> INITIALIZED} state
         * machine runs through {@link JvmRuntime} in both modes (the
         * production mode's event surface is disabled): a re-execution of
         * an initialized module publishes the state without re-running
         * the block; a re-entrant or failed re-execution is a producer
         * defect, never a silent re-run.
         */
        private void emitModuleInit(SemanticOp op, int indent) {
            KindPayload.ModuleInitPayload payload =
                (KindPayload.ModuleInitPayload) op.payload();
            requireParentlessModuleInit(op);
            String moduleText = javaString(payload.module().path());
            out.append(indent(indent)).append("if (JvmRuntime.moduleInitNeeded(")
                .append(moduleText).append(")) {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.moduleInitBegin(")
                .append(moduleText).append(");\n");
            emitStart(op, indent + 1);
            out.append(indent(indent + 1)).append("try {\n");
            emitBlockOps(payload.initBlock(), indent + 2);
            out.append(indent(indent + 2)).append("JvmRuntime.moduleInitComplete(")
                .append(moduleText).append(");\n");
            emitModuleInitSuccess(op, indent + 2);
            out.append(indent(indent + 1)).append("} catch (JvmRuntime.DealError e) {\n");
            out.append(indent(indent + 2)).append("JvmRuntime.moduleInitFail(")
                .append(moduleText).append(");\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(e)",
                indent + 2);
            out.append(indent(indent + 2)).append("throw e;\n");
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent)).append("} else {\n");
            emitStart(op, indent + 1);
            emitModuleInitSuccess(op, indent + 1);
            out.append(indent(indent)).append("}\n");
        }

        /** The MODULE_INIT SUCCESS terminal (the published {@code INITIALIZED} state). */
        private void emitModuleInitSuccess(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", \"MODULE_INIT\", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), \"state:INITIALIZED\", null);\n");
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
         * Emits one detached class-default method: the default block's
         * ops in order (the CLASS_DEFAULT op itself skipped — its own
         * events are the triggering CLASS_NEW/CLASS_FACTORY arm's) and
         * the final producing value returned.
         */
        private void emitClassDefaultMethod(SemanticOp defaultOp) {
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
            out.append("  private static Object ").append(defaultFn(defaultOp.opId()))
                .append("() {\n");
            for (OpId opId : ops) {
                if (opId.equals(defaultOp.opId()) || ownedChildren.contains(opId)) {
                    continue;
                }
                emitOp(opsById.get(opId), 2);
            }
            out.append("    return ").append(slot(resultId)).append(";\n");
            out.append("  }\n");
        }

        /** One detached class-default method name of a CLASS_DEFAULT op. */
        private String defaultFn(OpId defaultOp) {
            return "default" + defaultOp.id();
        }

        /** The generated carrier class name of one ClassId. */
        private String carrierName(ClassId classId) {
            return "C" + Integer.toHexString(classId.name().hashCode() & 0x7fffffff)
                + "x" + Integer.toHexString(classId.modulePath().hashCode() & 0x7fffffff);
        }

        /**
         * Emits the generated class carriers (E5): one static nested
         * class per ClassId of the union layout context, each with
         * per-field value slots plus boolean presence flags, tagged with
         * the canonical class identity. Present null is {@code f == null
         * && p == true} — never conflated with a missing field.
         */
        private void emitClassCarriers() {
            for (ClassLayout layout : classLayouts.values()) {
                ClassId classId = layout.classId();
                out.append("  static final class ").append(carrierName(classId))
                    .append(" implements JvmRuntime.ClassInstance {\n");
                out.append("    static final String ID = ")
                    .append(javaString(classId.text())).append(";\n");
                for (ClassLayout.FieldLayout field : layout.fields()) {
                    String slotName = fieldSlot(field.name());
                    out.append("    Object ").append(slotName).append(";\n");
                    out.append("    boolean ").append(fieldFlag(field.name())).append(";\n");
                }
                out.append("    @Override public String classIdText() { return ID; }\n");
                out.append("    @Override public boolean isPresent(String key) {\n");
                for (ClassLayout.FieldLayout field : layout.fields()) {
                    out.append("      if (")
                        .append(javaString(field.name())).append(".equals(key)) return ")
                        .append(fieldFlag(field.name())).append(";\n");
                }
                out.append("      return false;\n");
                out.append("    }\n");
                out.append("    @Override public Object read(String key) {\n");
                for (ClassLayout.FieldLayout field : layout.fields()) {
                    out.append("      if (").append(javaString(field.name()))
                        .append(".equals(key)) { if (").append(fieldFlag(field.name()))
                        .append(") return ").append(fieldSlot(field.name()))
                        .append("; return JvmRuntime.MISSING; }\n");
                }
                out.append("      return JvmRuntime.MISSING;\n");
                out.append("    }\n");
                out.append("    @Override public void write(String key, Object v) {\n");
                for (ClassLayout.FieldLayout field : layout.fields()) {
                    out.append("      if (").append(javaString(field.name()))
                        .append(".equals(key)) { ").append(fieldSlot(field.name()))
                        .append(" = v; ").append(fieldFlag(field.name()))
                        .append(" = true; }\n");
                }
                out.append("    }\n");
                out.append("    @Override public void delete(String key) {\n");
                for (ClassLayout.FieldLayout field : layout.fields()) {
                    out.append("      if (").append(javaString(field.name()))
                        .append(".equals(key)) { ").append(fieldSlot(field.name()))
                        .append(" = null; ").append(fieldFlag(field.name()))
                        .append(" = false; }\n");
                }
                out.append("    }\n");
                out.append("  }\n");
            }
        }

        /** One generated carrier's per-field value-slot name. */
        private String fieldSlot(String fieldName) {
            StringBuilder name = new StringBuilder("f");
            for (char c : fieldName.toCharArray()) {
                name.append(Character.isJavaIdentifierPart(c) ? c : '_');
            }
            return name.toString();
        }

        /** One generated carrier's per-field presence-flag name. */
        private String fieldFlag(String fieldName) {
            StringBuilder name = new StringBuilder("p");
            for (char c : fieldName.toCharArray()) {
                name.append(Character.isJavaIdentifierPart(c) ? c : '_');
            }
            return name.toString();
        }

        /** One class plan's static field name. */
        private String planName(ClassId classId) {
            return "PLAN_" + Integer.toHexString(classId.name().hashCode() & 0x7fffffff)
                + "_" + Integer.toHexString(classId.modulePath().hashCode() & 0x7fffffff);
        }

        /**
         * Emits one class's JSON plan: the declaration-order fields with
         * descriptor, optionality, static result kind, and the per-field
         * CLASS_DEFAULT child metadata (key, digest, thunk) of the
         * JSON_FROM_CLASS walk; the plan instantiates the generated
         * carrier.
         */
        private void emitJsonPlan(ClassLayout layout) {
            out.append("  private static final JvmJson.Plan ").append(planName(layout.classId()))
                .append(" = new JvmJson.Plan(")
                .append(javaString(layout.classId().text())).append(",\n");
            out.append("    new JvmJson.Field[]{\n");
            for (ClassLayout.FieldLayout field : layout.fields()) {
                SemanticOp defaultOp = classDefaultOpOf(layout.classId(), field.name());
                out.append("      new JvmJson.Field(").append(javaString(field.name()))
                    .append(", ").append(javaString(jsonDescriptorText(field.descriptor())))
                    .append(", ").append(field.required() ? "false" : "true")
                    .append(", ").append(javaString(staticKind(field.descriptor())));
                if (defaultOp != null && field.required()) {
                    out.append(", ").append(javaString(opKey(defaultOp.opId())))
                        .append(", ")
                        .append(javaString(defaultOp.contract().canonicalDigest()))
                        .append(", () -> ").append(defaultFn(defaultOp.opId())).append("()");
                }
                out.append("),\n");
            }
            out.append("    },\n    () -> new ").append(carrierName(layout.classId()))
                .append("());\n");
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

        /** The JSON plan descriptor text (the walk's closed kind grammar). */
        private static String jsonDescriptorText(RuntimeDescriptor descriptor) {
            if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
                return "nullable:" + jsonDescriptorText(nullable.inner());
            }
            if (descriptor instanceof RuntimeDescriptor.Array array) {
                return "array(" + jsonDescriptorText(array.element()) + ")";
            }
            if (descriptor instanceof RuntimeDescriptor.Class cls) {
                return cls.classId().text();
            }
            return switch (descriptor) {
                case RuntimeDescriptor.Null ignored -> "null";
                case RuntimeDescriptor.Boolean ignored -> "boolean";
                case RuntimeDescriptor.Int ignored -> "int";
                case RuntimeDescriptor.Number ignored -> "number";
                case RuntimeDescriptor.String ignored -> "string";
                case RuntimeDescriptor.Table ignored -> "table";
                case RuntimeDescriptor.Bytes ignored -> "bytes";
                case RuntimeDescriptor.Func ignored -> "function";
                case RuntimeDescriptor.Array ignored -> "array";
                case RuntimeDescriptor.Nullable ignored -> "nullable";
                case RuntimeDescriptor.Class ignored -> "class";
            };
        }

        /**
         * JSON_FROM_CLASS (E7/K-D8): the shared walk
         * ({@link JvmJson#fromClass}) over the class's emitted plan — the
         * payload's JSON text operand resolves exactly once; the walk runs
         * the per-site CLASS_DEFAULT children (their own START/terminal
         * events) for omitted required-present defaulted fields and
         * publishes the tagged instance, or language null on any
         * syntax/extra-key/decode/default/validation failure (the
         * {@code JSON_FROM_NULL} projection).
         */
        private void emitJsonFromClass(SemanticOp op, int indent) {
            KindPayload.JsonFromClassPayload payload =
                (KindPayload.JsonFromClassPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = JvmJson.fromClass(")
                .append(planName(payload.layout().classId())).append(", (String) ")
                .append(slot(payload.jsonString())).append(");\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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
        private void emitJsonToClass(SemanticOp op, int indent) {
            KindPayload.JsonToClassPayload payload =
                (KindPayload.JsonToClassPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(target).append(" = JvmJson.toClass(")
                .append(planName(payload.layout().classId())).append(", ")
                .append(slot(payload.classValue())).append(");\n");
            out.append(indent(indent)).append("} catch (JvmJson.Projection projection) {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.DealError __jsonErr = "
                + "JvmRuntime.fail(\"E8001\", \"value at \" + projection.fieldPath + "
                + "\" is not JSON serializable: \" + projection.actual, ")
                .append(javaString(originOf(op))).append(", null, null);\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__jsonErr)", indent + 1);
            out.append(indent(indent + 1)).append("throw __jsonErr;\n");
            out.append(indent(indent)).append("}\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        /** One thunk re-executor method name of an adapter op. */
        private String thunkFn(OpId adaptOp) {
            return "thunk" + adaptOp.id();
        }

        /**
         * Emits one detached thunk re-executor for a FUNCTION_ADAPT op
         * with a REEVALUATE_THUNK source: the thunk block's ops run in
         * order (payload-owned children included through their owner
         * arms) and the method returns the final producing op's result —
         * the source value the invocation consumes.
         */
        private void emitThunkMethod(SemanticOp adaptOp, BlockId block) {
            StructuredBodyTable ownerTable = blockTableOf.get(block);
            List<OpId> ops = ownerTable == null ? null : ownerTable.blockOps().get(block);
            if (ops == null) {
                throw new IllegalStateException("the adapter thunk block " + block
                    + " has no membership row (producer defect)");
            }
            out.append("  private static Object ").append(thunkFn(adaptOp.opId()))
                .append("() {\n");
            emitBlockOps(block, 2);
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
            out.append("    return ").append(slot(produced)).append(";\n");
            out.append("  }\n");
        }

        /** Emits one function factory: a FunctionValue over the passed capture cells. */
        private void emitFunctionFactory(LoweredFunction function) {
            FunctionId functionId = function.functionId();
            List<BindingGeneration> captures = function.captures();
            StringBuilder params = new StringBuilder();
            for (BindingGeneration capture : captures) {
                if (params.length() > 0) {
                    params.append(", ");
                }
                params.append("Object c" + capture.binding().id());
            }
            out.append("  static JvmRuntime.FunctionValue ").append(fnFactory(functionId))
                .append('(').append(params).append(") {\n");
            out.append("    return new JvmRuntime.FunctionValue(args -> {\n");
            List<OpId> bodyOps = tableOfFunction(function).blockOps().get(function.body());
            currentFunction = function;
            int paramCount = function.descriptor().paramTypes().size();
            for (int i = 0; i < paramCount && i < bodyOps.size(); i++) {
                SemanticOp op = opsById.get(bodyOps.get(i));
                if (op.kind() != SemanticOpKind.BINDING_ALLOC) {
                    break;
                }
                KindPayload.BindingAllocPayload payload =
                    (KindPayload.BindingAllocPayload) op.payload();
                BindingCellKind kind = cellKindOf(payload.binding(), payload.generation());
                out.append("      ").append(cell(payload.binding(), payload.generation())).append(" = ")
                    .append(kind == BindingCellKind.SHARED_CELL
                        ? "new Object[]{args[" + i + "]}" : "args[" + i + "]")
                    .append(";\n");
            }
            boolean reachable = true;
            boolean unreachableReported = false;
            for (int i = paramCount; i < bodyOps.size(); i++) {
                OpId opId = bodyOps.get(i);
                if (ownedChildren.contains(opId) || skippedOps.contains(opId)) {
                    continue;
                }
                SemanticOp op = opsById.get(opId);
                if (!reachable) {
                    // JLS §14.21: the preceding statement of this body cannot
                    // complete normally, so every later op would be
                    // unreachable Java — javac rejects it and no consumer ever
                    // executes it (the oracle's block walk stops on the same
                    // non-completing path). The skip emits no event, exactly
                    // like the never-taken path.
                    if (!unreachableReported) {
                        out.append("      // unreachable: the preceding statement"
                            + " cannot complete normally\n");
                        unreachableReported = true;
                    }
                    continue;
                }
                emitOp(op, 3);
                reachable = completesNormally(op);
            }
            // A body whose last emitted op is not a RETURN (the
            // group-core window's member bodies carry no E7 RETURN
            // production) must still terminate the lambda: the
            // unconditional null return is reachable-safe after any
            // try-catch tail and never follows a directly emitted
            // `return` (tail RETURN emits one). A body whose emitted
            // statements cannot complete normally needs no terminating
            // return (javac admits a non-completing lambda body).
            SemanticOp tail = null;
            if (reachable) {
                for (int i = bodyOps.size() - 1; i >= 0; i--) {
                    OpId candidate = bodyOps.get(i);
                    if (ownedChildren.contains(candidate)
                            || skippedOps.contains(candidate)) {
                        continue;
                    }
                    tail = opsById.get(candidate);
                    break;
                }
            }
            if (reachable && (tail == null || tail.kind() != SemanticOpKind.RETURN)) {
                out.append("      return null;\n");
            }
            out.append("    }, ")
                .append(javaString(descriptorText(function.descriptor())))
                .append(", ")
                .append(javaString(function.descriptor().canonicalSpecText()))
                .append(", ")
                .append(javaString(String.valueOf(functionId.id())))
                .append(");\n");
            out.append("  }\n");
            currentFunction = null;
        }

        private void emitBlockOps(BlockId block, int indent) {
            StructuredBodyTable ownerTable = blockTableOf.get(block);
            if (ownerTable == null) {
                ownerTable = table;
            }
            boolean reachable = true;
            boolean reported = false;
            for (OpId opId : ownerTable.blockOps().get(block)) {
                if (ownedChildren.contains(opId)) {
                    continue;
                }
                if (skippedOps.contains(opId)) {
                    continue;
                }
                SemanticOp op = opsById.get(opId);
                if (!reachable) {
                    // JLS §14.21: the preceding statement of this block
                    // cannot complete normally, so every later op of the
                    // block would be unreachable Java — javac rejects it, no
                    // consumer ever executes it (the oracle's block walk
                    // stops on the same non-completing path), and the
                    // retained emitter applies the same skip rule. The skip
                    // emits no event, exactly like the never-taken path.
                    if (!reported) {
                        out.append(indent(indent)).append("// unreachable: the"
                            + " preceding statement cannot complete normally\n");
                        reported = true;
                    }
                    continue;
                }
                emitOp(op, indent);
                reachable = completesNormally(op);
            }
        }

        /**
         * Whether the emitted Java of one op's statement can complete
         * normally (the JLS §14.21 mirror the retained emitter also
         * applies): {@code THROW}/{@code BREAK}/{@code CONTINUE} /
         * {@code RETURN} transfer unconditionally, a {@code BRANCH} can
         * only when one of its branches can, and a {@code TRY_CATCH} only
         * when its try block or its catch block can (its emitted
         * {@code Transfer} clause always rethrows). Every other op emits a
         * completing statement — the emitted loops carry their own break
         * test.
         */
        private boolean completesNormally(SemanticOp op) {
            return switch (op.kind()) {
                case THROW, BREAK, CONTINUE, RETURN -> false;
                case TRY_CATCH -> {
                    KindPayload.TryCatchPayload payload =
                        (KindPayload.TryCatchPayload) op.payload();
                    yield blockCompletesNormally(payload.tryBlock())
                        || blockCompletesNormally(payload.catchBlock());
                }
                case BRANCH -> {
                    KindPayload.BranchPayload payload =
                        (KindPayload.BranchPayload) op.payload();
                    // An if without an else clause always has the
                    // fall-through path (the emitter emits a plain if), so it
                    // completes; with both branches emitted the statement
                    // completes iff one of them does.
                    yield payload.alternateBlock() == null
                        || blockCompletesNormally(payload.selectedBlock())
                        || blockCompletesNormally(payload.alternateBlock());
                }
                default -> true;
            };
        }

        /** Whether the emitted Java of one block's last op can complete normally. */
        private boolean blockCompletesNormally(BlockId block) {
            StructuredBodyTable ownerTable = blockTableOf.get(block);
            if (ownerTable == null) {
                ownerTable = table;
            }
            java.util.List<OpId> ops = ownerTable.blockOps().get(block);
            if (ops == null || ops.isEmpty()) {
                return true;
            }
            SemanticOp last = opsById.get(ops.get(ops.size() - 1));
            return last == null || completesNormally(last);
        }

        /**
         * The {@link LoweredFunction} record of one function id across the
         * session's closure: a non-entry module's function body resolves
         * against its own module's function registry, never the entry
         * unit's (a cross-module call site's capture list is the callee's
         * own).
         */
        private LoweredFunction functionOf(FunctionId functionId) {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                LoweredFunction function = moduleUnit.functions().get(functionId);
                if (function != null) {
                    return function;
                }
            }
            return unit.functions().get(functionId);
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

        private String indent(int level) {
            return "  ".repeat(level);
        }

        // -- per-op emission ---------------------------------------------------------

        private void emitOp(SemanticOp op, int indent) {
            switch (op.kind()) {
                case CONST -> emitConst(op, indent);
                case UNARY -> emitUnary(op, indent);
                case BINARY -> emitBinary(op, indent);
                case STRING_CONCAT -> emitConcat(op, indent);
                case ARRAY_NEW -> emitArrayNew(op, indent);
                case TABLE_NEW -> emitTableNew(op, indent);
                case ARRAY_LENGTH -> emitArrayLength(op, indent);
                case MEMBER_READ -> emitMemberRead(op, indent);
                case MEMBER_WRITE -> emitMemberWrite(op, indent);
                case MEMBER_DELETE -> emitMemberDelete(op, indent);
                case INDEX_NORMALIZE -> emitNormalize(op, indent);
                case INDEX_READ -> emitIndexRead(op, indent);
                case INDEX_WRITE -> emitIndexWrite(op, indent);
                case INDEX_DELETE -> emitIndexDelete(op, indent);
                case OPTIONAL_READ -> emitOptionalRead(op, indent);
                case HAS_FIELD -> emitHasField(op, indent);
                case FIELD_READ -> emitFieldRead(op, indent);
                case FIELD_WRITE -> emitFieldWrite(op, indent);
                case FIELD_DELETE -> emitFieldDelete(op, indent);
                case BOUNDARY -> emitFreeBoundary(op, indent);
                case BINDING_ALLOC -> emitBindingAlloc(op, indent);
                case BINDING_INIT -> emitBindingInit(op, indent);
                case BINDING_LOAD -> emitBindingLoad(op, indent);
                case BINDING_STORE -> emitBindingStore(op, indent);
                case CLOSURE_NEW -> emitClosureNew(op, indent);
                case RECURSIVE_GROUP_INIT -> emitRecursiveGroupInit(op, indent);
                case FUNCTION_ADAPT -> emitFunctionAdapt(op, indent);
                case CALLBACK_INVOKE -> emitCallbackInvoke(op, indent);
                case ASYNC_START -> emitAsyncStart(op, indent);
                case AWAIT -> emitAwait(op, indent);
                case ASSIGN -> emitAssign(op, indent);
                case DELETE -> emitDelete(op, indent);
                case CALL -> emitCall(op, indent);
                case INTRINSIC_CALL -> emitIntrinsic(op, indent);
                case STDLIB_CALL -> emitStdlib(op, indent);
                case BRANCH -> emitBranch(op, indent);
                case LOOP -> emitLoop(op, indent);
                case FOR_EACH -> emitForEach(op, indent);
                case TRY_CATCH -> emitTryCatch(op, indent);
                case THROW -> emitThrow(op, indent);
                case RETURN -> emitReturn(op, indent);
                case BREAK -> emitBreak(op, indent);
                case CONTINUE -> emitContinue(op, indent);
                case DISCARD -> emitDiscard(op, indent);
                case MODULE_IMPORT -> emitModuleImport(op, indent);
                case EXPORT_READ -> emitExportRead(op, indent);
                case EXPORT_PUBLISH -> emitExportPublish(op, indent);
                case EXTERNAL_ENTRY -> emitExternalEntryRecord(op, indent);
                case ENTRY_INVOKE -> emitEntryInvoke(op, indent);
                case MODULE_INIT -> emitModuleInit(op, indent);
                case JSON_FROM_CLASS -> emitJsonFromClass(op, indent);
                case JSON_TO_CLASS -> emitJsonToClass(op, indent);
                case CLASS_NEW -> emitClassNew(op, indent);
                case CLASS_DEFAULT -> throw new IllegalStateException("a CLASS_DEFAULT "
                    + "executes only under its triggering CLASS_NEW/CLASS_FACTORY "
                    + "(the detached default block's ops are the class-default "
                    + "method's; the block walk never runs the op itself)");
                case CLASS_FACTORY -> throw new IllegalStateException("a CLASS_FACTORY "
                    + "is a detached owner-module entry executed only under the "
                    + "triggering caller's CLASS_NEW (cross-unit parent) — the "
                    + "block walk never runs it)");
                default -> throw new IllegalStateException("op kind " + op.kind()
                    + " has no shared-JVM emission in this decomposition-tail domain");
            }
        }

        private String opKey(OpId id) {
            return id.module().path() + "#" + id.id();
        }

        private String parentKey(OpId parent) {
            return parent == null ? "-" : opKey(parent);
        }

        private void emitStart(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            StringBuilder inputs = new StringBuilder();
            for (int i = 0; i < op.operands().size(); i++) {
                if (i > 0) {
                    inputs.append(", ");
                }
                inputs.append("JvmRuntime.atom(").append(slot(op.operands().get(i)))
                    .append(", ").append(javaString(staticKind(op.operandTypes().get(i))))
                    .append(")");
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(").append(inputs).append("), null, null);\n");
        }

        /** START with the closed slot atom for the second operand (slot ops). */
        private void emitSlotOperandStart(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            StringBuilder inputs = new StringBuilder();
            inputs.append("JvmRuntime.atom(").append(slot(op.operands().get(0)))
                .append(", ").append(javaString(staticKind(op.operandTypes().get(0))))
                .append("), ");
            inputs.append("\"slot:\" + ((long[]) ").append(slot(op.operands().get(1)))
                .append(")[0] + \"/\" + (((long[]) ").append(slot(op.operands().get(1)))
                .append(")[0] < ((long[]) ").append(slot(op.operands().get(1)))
                .append(")[1]) + \"/\" + (((long[]) ").append(slot(op.operands().get(1)))
                .append(")[2] == 1 && ((long[]) ").append(slot(op.operands().get(1)))
                .append(")[0] == ((long[]) ").append(slot(op.operands().get(1)))
                .append(")[1])");
            for (int i = 2; i < op.operands().size(); i++) {
                inputs.append(", JvmRuntime.atom(").append(slot(op.operands().get(i)))
                    .append(", ").append(javaString(staticKind(op.operandTypes().get(i))))
                    .append(")");
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(").append(inputs).append("), null, null);\n");
        }

        /** The INDEX_READ START of a bytes read: the container atom plus the bytes slot atom. */
        private void emitBytesSlotOperandStart(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            StringBuilder inputs = new StringBuilder();
            inputs.append("JvmRuntime.atom(").append(slot(op.operands().get(0)))
                .append(", ").append(javaString(staticKind(op.operandTypes().get(0))))
                .append("), ");
            inputs.append("\"byteslot:\" + ((Object[]) ").append(slot(op.operands().get(1)))
                .append(")[1] + \"/\" + (((Long) ((Object[]) ")
                .append(slot(op.operands().get(1))).append(")[1]) < ((Long) ((Object[]) ")
                .append(slot(op.operands().get(1))).append(")[2]))");
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(").append(inputs).append("), null, null);\n");
        }

        private void emitBoundaryStart(SemanticOp boundary, String inputExpr,
                                       RuntimeDescriptor inputDescriptor, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(boundary.opId()))).append(", \"START\", ")
                .append("\"BOUNDARY\", ")
                .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(boundary.origin().parentOpId())))
                .append(", List.of(JvmRuntime.atom(").append(inputExpr).append(", ")
                .append(javaString(staticKind(inputDescriptor)))
                .append(")), null, null);\n");
        }

        private void emitBoundarySuccess(SemanticOp boundary, String valueExpr,
                                         RuntimeDescriptor descriptor, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(boundary.opId()))).append(", \"SUCCESS\", ")
                .append("\"BOUNDARY\", ")
                .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(boundary.origin().parentOpId())))
                .append(", List.of(), JvmRuntime.atom(").append(valueExpr).append(", ")
                .append(javaString(staticKind(descriptor))).append("), null);\n");
        }

        /** A boundary SUCCESS event with a raw output atom expression. */
        private void emitBoundarySuccessAtom(SemanticOp boundary, String atomExpr,
                                             int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(boundary.opId()))).append(", \"SUCCESS\", ")
                .append("\"BOUNDARY\", ")
                .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(boundary.origin().parentOpId())))
                .append(", List.of(), ").append(atomExpr).append(", null);\n");
        }

        /**
         * The op's SUCCESS event with the value-aware atom (the oracle's
         * {@code atomOf}): a deferred composite read atomizes the value's
         * own kind, never the declared descriptor's kind.
         */
        private void emitResultSuccessAtom(SemanticOp op, String valueExpr, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), JvmRuntime.rawAtom(").append(valueExpr)
                .append(", \"ref\"), null);\n");
        }

        private void emitResultSuccess(SemanticOp op, String valueExpr,
                                       RuntimeDescriptor resultDescriptor, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), JvmRuntime.atom(").append(valueExpr).append(", ")
                .append(javaString(staticKind(resultDescriptor))).append("), null);\n");
        }

        private void emitPlainSuccess(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), null, null);\n");
        }

        /** The raw SUCCESS emission of a structure closed by a transfer. */
        private void emitClosedSuccess(SemanticOp op, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), null, null);\n");
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

        /** Emits the transfer closures of the ancestors down to (and including)
         *  the target loop; stops at an enclosing TRY_CATCH when requested
         *  (its dispatch closes it). */
        private void emitTransferClosures(SemanticOp transferOp, SemanticOp targetLoop,
                                          boolean stopAtTry, int indent) {
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
                emitClosedSuccess(ancestor, indent);
            }
        }

        private void emitFailureEvent(OpId id, String kindName, SemanticOp op,
                                      String errExpr, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(id))).append(", \"FAILURE\", ")
                .append(javaString(kindName)).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), null, ").append(errExpr).append(");\n");
        }

        static String numberLiteral(double value) {
            if (Double.isNaN(value)) {
                return "Double.valueOf(Double.NaN)";
            }
            if (Double.isInfinite(value)) {
                return value > 0 ? "Double.valueOf(Double.POSITIVE_INFINITY)"
                    : "Double.valueOf(Double.NEGATIVE_INFINITY)";
            }
            return "Double.valueOf(" + Double.toHexString(value) + ")";
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

        private void emitConst(SemanticOp op, int indent) {
            KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
            String literal = switch (payload.value()) {
                case ScalarValue.Null ignored -> "null";
                case ScalarValue.Boolean bool -> bool.value()
                    ? "Boolean.TRUE" : "Boolean.FALSE";
                case ScalarValue.Int intValue -> "Long.valueOf(" + intValue.value() + "L)";
                case ScalarValue.Number number -> numberLiteral(number.value());
                case ScalarValue.String string -> javaString(string.value());
            };
            emitStart(op, indent);
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(literal).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitUnary(SemanticOp op, int indent) {
            KindPayload.UnaryPayload payload = (KindPayload.UnaryPayload) op.payload();
            emitStart(op, indent);
            if (payload.selector() == deal.semantic.ir.UnarySelector.BOOL_NOT) {
                out.append(indent(indent)).append(slot((ValueId) op.result()))
                    .append(" = !((Boolean) ").append(slot(op.operands().get(0)))
                    .append(");\n");
            } else {
                out.append(indent(indent)).append(slot((ValueId) op.result()))
                    .append(" = JvmRuntime.unary(")
                    .append(javaString(payload.selector().name())).append(", ")
                    .append(slot(op.operands().get(0))).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(originOf(op))).append(");\n");
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitBinary(SemanticOp op, int indent) {
            KindPayload.BinaryPayload payload = (KindPayload.BinaryPayload) op.payload();
            emitStart(op, indent);
            boolean arithmetic = payload.selector().name().startsWith("INT32_")
                || payload.selector().name().startsWith("NUMBER_");
            boolean comparison = payload.selector().name().endsWith("_EQ")
                || payload.selector().name().endsWith("_NE")
                || payload.selector().name().endsWith("_LT")
                || payload.selector().name().endsWith("_LE")
                || payload.selector().name().endsWith("_GT")
                || payload.selector().name().endsWith("_GE");
            if (arithmetic && !comparison) {
                out.append(indent(indent)).append(slot((ValueId) op.result()))
                    .append(" = JvmRuntime.arith(")
                    .append(javaString(payload.selector().name())).append(", ")
                    .append(slot(op.operands().get(0))).append(", ")
                    .append(slot(op.operands().get(1))).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(originOf(op))).append(");\n");
                emitResultSuccess(op, slot((ValueId) op.result()),
                    (RuntimeDescriptor) op.resultType(), indent);
                return;
            }
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = JvmRuntime.cmp(")
                .append(javaString(payload.selector().name())).append(", ")
                .append(javaString(staticKind(op.operandTypes().get(0)))).append(", ")
                .append(slot(op.operands().get(0))).append(", ")
                .append(javaString(staticKind(op.operandTypes().get(1)))).append(", ")
                .append(slot(op.operands().get(1))).append(", ")
                .append(payload.side() == null ? "null"
                    : javaString(payload.side().name())).append(");\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitConcat(SemanticOp op, int indent) {
            KindPayload.StringConcatPayload payload =
                (KindPayload.StringConcatPayload) op.payload();
            emitStart(op, indent);
            StringBuilder expr = new StringBuilder();
            for (ValueId fragment : payload.fragments()) {
                if (expr.length() > 0) {
                    expr.append(" + ");
                }
                expr.append("((String) ").append(slot(fragment)).append(")");
            }
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(expr.length() == 0 ? "\"\"" : expr).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitArrayNew(SemanticOp op, int indent) {
            KindPayload.ArrayNewPayload payload = (KindPayload.ArrayNewPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = new JvmRuntime.Array(")
                .append(payload.values().size()).append(");\n");
            for (int i = 0; i < payload.values().size(); i++) {
                OpId boundaryId = payload.elementBoundaryOpIds().get(i);
                SemanticOp boundary = opsById.get(boundaryId);
                ValueId input = payload.values().get(i);
                emitBoundaryStart(boundary, slot(input), payload.elementDescriptor(),
                    indent);
                out.append(indent(indent)).append("Object __be_").append(boundary.opId().id())
                    .append(" = ")
                    .append(bcheckArgs(payload.elementDescriptor(), slot(input)))
                    .append(";\n");
                out.append(indent(indent)).append("((JvmRuntime.Array) ").append(target)
                    .append(").elements.add(__be_").append(boundary.opId().id())
                    .append(");\n");
                emitBoundarySuccess(boundary, "__be_" + boundary.opId().id(),
                    payload.elementDescriptor(), indent);
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitTableNew(SemanticOp op, int indent) {
            KindPayload.TableNewPayload payload = (KindPayload.TableNewPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = new JvmRuntime.Table();\n");
            for (KindPayload.TableEntry entry : payload.entries()) {
                out.append(indent(indent)).append("((").append(
                        "JvmRuntime.Table) ").append(target).append(").write(")
                    .append(javaString(entry.key())).append(", ")
                    .append(slot(entry.value())).append(");\n");
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitArrayLength(SemanticOp op, int indent) {
            KindPayload.ArrayLengthPayload payload =
                (KindPayload.ArrayLengthPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            if (isBytesValue(payload.arrayValue())) {
                // K6 item 7: b.length reads the bytes buffer's fixed
                // logical length at the read's own origin.
                out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.bytesLength(")
                    .append(slot(payload.arrayValue())).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(originOf(op))).append(");\n");
            } else {
                out.append(indent(indent)).append(target)
                    .append(" = Long.valueOf(((").append("JvmRuntime.Array) ")
                    .append(slot(payload.arrayValue())).append(").length);\n");
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * Whether one value identity's producing op publishes a bytes
         * value (the {@code b.length} receiver selector, K6 item 7): an
         * {@code ARRAY_LENGTH} op carries no operands, so the receiver
         * producer's own result descriptor is the classification
         * authority.
         */
        private boolean isBytesValue(deal.semantic.ir.ValueId value) {
            for (SemanticOp candidate : opsById.values()) {
                if (value.equals(candidate.result())
                        && candidate.resultType() instanceof RuntimeDescriptor.Bytes) {
                    return true;
                }
            }
            return false;
        }

        private void emitMemberRead(SemanticOp op, int indent) {
            KindPayload.MemberReadPayload payload = (KindPayload.MemberReadPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = ((")
                .append("JvmRuntime.Table) ").append(slot(payload.table())).append(").read(")
                .append(javaString(payload.key())).append(");\n");
            SemanticOp boundary = boundaryChildOf(op);
            if (boundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                if (trace) {
                    // Custom boundary START: the input atom renders the
                    // actual value kind (the oracle's atomOf — a
                    // wrong-kind present value atomizes as its own kind).
                    out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(boundary.opId())))
                        .append(", \"START\", \"BOUNDARY\", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", List.of(JvmRuntime.rawAtom(")
                        .append(target).append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append(")), null, null);\n");
                }
                out.append(indent(indent)).append("  Object __mr_")
                    .append(boundary.opId().id()).append(";\n");
                out.append(indent(indent)).append("  try {\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    // A composite contextual read (ISSUE-0651): the
                    // function/array carriers pass through unchanged — the
                    // consuming declared cell carries the pinned E8010
                    // projection at its own origin, exactly the oracle's
                    // identical deferral and the LuaJIT arm's identical
                    // condition. The SUCCESS atom renders the value's own
                    // kind (the oracle's atomOf).
                    out.append(indent(indent)).append("    __mr_")
                        .append(boundary.opId().id()).append(" = ")
                        .append(target).append(";\n");
                } else {
                    out.append(indent(indent)).append("    __mr_")
                        .append(boundary.opId().id())
                        .append(" = ")
                        .append(bcheckArgs(boundaryPayload.descriptor(), target))
                        .append(";\n");
                }
                out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("    JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("    throw __bre;\n");
                out.append(indent(indent)).append("  }\n");
                out.append(indent(indent)).append(target).append(" = __mr_")
                    .append(boundary.opId().id()).append(";\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    emitBoundarySuccessAtom(boundary, "JvmRuntime.rawAtom("
                        + target + ", "
                        + javaString(staticKind(boundaryPayload.descriptor())) + ")",
                        indent);
                    // The deferred composite read's own SUCCESS atom renders
                    // the value's own kind too (the oracle's value-aware
                    // publish, never the declared kind).
                    emitResultSuccessAtom(op, target, indent);
                } else {
                    emitBoundarySuccess(boundary, target,
                        boundaryPayload.descriptor(), indent);
                    emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(),
                        indent);
                }
                return;
            }
            // The OPTIONAL_READ envelope shape: the raw read publishes the
            // internal missing or the present value (present null included)
            // and its SUCCESS atom renders the actual value kind —
            // missing → "missing", null → "null", else the actual-kind
            // atom, exactly the oracle's publish (a wrong-kind present
            // value atomizes as its own kind, never the declared kind).
            SemanticOp optional = optionalReadOf((ValueId) op.result());
            RuntimeDescriptor inner = optional == null
                ? null
                : ((KindPayload.OptionalReadPayload) optional.payload()).descriptor();
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), JvmRuntime.rawAtom(").append(target)
                .append(", ")
                .append(javaString(inner == null ? "ref" : "nullable:" + staticKind(inner)))
                .append("), null);\n");
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
        private void emitOptionalRead(SemanticOp op, int indent) {
            KindPayload.OptionalReadPayload payload =
                (KindPayload.OptionalReadPayload) op.payload();
            if (payload.value() == null) {
                emitStart(op, indent);
            } else {
                // Custom START: the raw operand atom renders the actual
                // value kind (a wrong-kind present value atomizes as its
                // own kind, exactly the oracle's publish).
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId())))
                    .append(", List.of(JvmRuntime.rawAtom(")
                    .append(slot(payload.value())).append(", ")
                    .append(javaString("nullable:" + staticKind(payload.descriptor())))
                    .append(")), null, null);\n");
            }
            String target = slot((ValueId) op.result());
            if (payload.value() == null) {
                out.append(indent(indent)).append(target).append(" = null;\n");
            } else {
                String source = slot(payload.value());
                out.append(indent(indent)).append(target).append(" = ")
                    .append(source).append(" == JvmRuntime.MISSING ? null : ")
                    .append(source).append(";\n");
            }
            SemanticOp boundary = boundaryChildOf(op);
            if (boundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                // Custom boundary START: the input atom renders the
                // actual value kind (identical for a passing value,
                // actual-kind for a wrong-kind present value).
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(boundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(boundary.origin().parentOpId())))
                    .append(", List.of(JvmRuntime.rawAtom(").append(target)
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(")), null, null);\n");
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
                // exactly the oracle's identical deferral and the LuaJIT
                // arm's identical condition. Every other descriptor keeps
                // the strict row.
                String checkedName = "__orb_" + boundary.opId().id();
                String errorName = "__obe_" + boundary.opId().id();
                String rebuiltName = "__obe2_" + boundary.opId().id();
                out.append(indent(indent)).append("try {\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    out.append(indent(indent + 1)).append("Object ")
                        .append(checkedName).append(" = ").append(target)
                        .append(";\n");
                } else {
                    out.append(indent(indent + 1)).append("Object ")
                        .append(checkedName)
                        .append(" = ")
                        .append(bcheckArgs(boundaryPayload.descriptor(), target))
                        .append(";\n");
                }
                out.append(indent(indent + 1)).append(target).append(" = ")
                    .append(checkedName).append(";\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError ")
                    .append(errorName).append(") {\n");
                out.append(indent(indent + 1)).append("JvmRuntime.DealError ")
                    .append(rebuiltName).append(" = new JvmRuntime.DealError(")
                    .append(errorName).append(".code, ").append(errorName)
                    .append(".msg, ").append(javaString(originOf(boundary)))
                    .append(", ").append(errorName).append(".expected, ")
                    .append(errorName).append(".actual, ").append(errorName)
                    .append(".frames, ").append(errorName).append(".cause);\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(" + rebuiltName + ")", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(" + rebuiltName + ")", indent + 1);
                out.append(indent(indent + 1)).append("throw ").append(rebuiltName)
                    .append(";\n");
                out.append(indent(indent)).append("}\n");
                if (defersContextualCheck(boundaryPayload.descriptor())) {
                    emitBoundarySuccessAtom(boundary, "JvmRuntime.rawAtom("
                        + target + ", "
                        + javaString(staticKind(boundaryPayload.descriptor())) + ")",
                        indent);
                } else {
                    emitBoundarySuccess(boundary, target,
                        boundaryPayload.descriptor(), indent);
                }
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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
            // The composite carriers (functions, arrays, and bytes — a bytes
            // contextual read defers its shape check to the consuming
            // declared cell, whose bytes projection carries the pinned
            // "expected bytes" text at the declaration's own origin).
            return isFunctionDescriptor(descriptor) || isArrayDescriptor(descriptor)
                || isBytesDescriptor(descriptor);
        }

        /** Whether one boundary descriptor is the bytes carrier (nullable unwrapped). */
        private boolean isBytesDescriptor(RuntimeDescriptor descriptor) {
            RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                ? nullable.inner() : descriptor;
            return inner instanceof RuntimeDescriptor.Bytes;
        }

        /**
         * HAS_FIELD: the presence boolean over one checked receiver key —
         * present (present null included) → true, absent → false. The
         * runtime helper realizes the table-presence half; the
         * class-instance presence flags are the CLASSES family's
         * realization.
         */
        private void emitHasField(SemanticOp op, int indent) {
            KindPayload.HasFieldPayload payload =
                (KindPayload.HasFieldPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = JvmRuntime.hasField(")
                .append(slot(payload.receiver())).append(", ")
                .append(javaString(payload.key())).append(");\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        // =====================================================================
        // The class field ops (CLASSES step 8, E5): FIELD_READ is
        // presence-aware (missing → the OPTIONAL_FIELD_READ boundary's
        // pre-mapped language null; present null stays distinguishable
        // through the carrier's presence flags); FIELD_WRITE/FIELD_DELETE
        // are commit ops consuming the ASSIGN/DELETE chain's resolved
        // receiver and stored value — exactly one mutation, never a
        // re-evaluated source expression.
        // =====================================================================

        /**
         * FIELD_READ (K-D6): the nominal receiver boundary
         * ({@code UNTYPED_CLASS_INPUT}) runs first — a null receiver or a
         * foreign class identity fails its canonical E8001 projection —
         * then the presence-aware read (a missing field pre-maps to
         * language null; present null is the carrier's null value seen
         * through a true presence flag, never conflated with missing)
         * goes through the {@code OPTIONAL_FIELD_READ} boundary; SUCCESS
         * publishes the boundary-checked value.
         */
        private void emitFieldRead(SemanticOp op, int indent) {
            KindPayload.FieldReadPayload payload =
                (KindPayload.FieldReadPayload) op.payload();
            emitStart(op, indent);
            String receiver = "__frr_" + op.opId().id();
            emitFieldBoundaryCheck(op,
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT),
                slot(payload.classValue()), receiver, indent);
            String read = "__frv_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(read)
                .append(" = ((").append("JvmRuntime.ClassInstance) ")
                .append(receiver).append(").read(")
                .append(javaString(payload.field())).append(");\n");
            out.append(indent(indent)).append(read).append(" = ").append(read)
                .append(" == JvmRuntime.MISSING ? null : ").append(read)
                .append(";\n");
            emitFieldBoundaryCheck(op,
                boundaryChildOfKind(op, BoundaryKind.OPTIONAL_FIELD_READ),
                read, slot((ValueId) op.result()), indent);
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * FIELD_WRITE (K-D6, the ASSIGN chain's commit child): the
         * receiver boundary runs over the resolved receiver slot, then the
         * field boundary ({@code CLASS_FIELD_ASSIGNMENT}) over the
         * resolved stored value — the store commits only after both pass
         * (a failed boundary commits nothing), and the instance carries
         * the boundary-published value in the named field with every
         * other presence state unchanged.
         */
        private void emitFieldWrite(SemanticOp op, int indent) {
            KindPayload.FieldWritePayload payload =
                (KindPayload.FieldWritePayload) op.payload();
            emitStart(op, indent);
            String receiver = "__fwr_" + op.opId().id();
            emitFieldBoundaryCheck(op,
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT),
                slot(payload.classValue()), receiver, indent);
            String value = "__fwv_" + op.opId().id();
            emitFieldBoundaryCheck(op,
                boundaryChildOfKind(op, BoundaryKind.CLASS_FIELD_ASSIGNMENT),
                slot(payload.value()), value, indent);
            out.append(indent(indent)).append("((").append("JvmRuntime.ClassInstance) ")
                .append(receiver).append(").write(")
                .append(javaString(payload.field())).append(", ").append(value)
                .append(");\n");
            emitPlainSuccess(op, indent);
        }

        /**
         * FIELD_DELETE (K-D6, the DELETE chain's commit child): the
         * receiver boundary runs over the resolved receiver slot, then the
         * named field's presence and value are cleared — deleting an
         * already-missing field is a no-op SUCCESS, and every other field
         * state is unchanged.
         */
        private void emitFieldDelete(SemanticOp op, int indent) {
            KindPayload.FieldDeletePayload payload =
                (KindPayload.FieldDeletePayload) op.payload();
            emitStart(op, indent);
            String receiver = "__fdr_" + op.opId().id();
            emitFieldBoundaryCheck(op,
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT),
                slot(payload.classValue()), receiver, indent);
            out.append(indent(indent)).append("((").append("JvmRuntime.ClassInstance) ")
                .append(receiver).append(").delete(")
                .append(javaString(payload.field())).append(");\n");
            emitPlainSuccess(op, indent);
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
         * "null", never an allocation id), the check runs into the given
         * local, and the terminal is the boundary SUCCESS with its
         * published value or the two FAILURE events (boundary then owner)
         * with the boundary's own origin.
         */
        private void emitFieldBoundaryCheck(SemanticOp owner, SemanticOp boundary,
                                            String inputExpr, String checkedName,
                                            int indent) {
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) boundary.payload();
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(boundary.opId())))
                    .append(", \"START\", \"BOUNDARY\", ")
                    .append(javaString(boundary.contract().canonicalDigest()))
                    .append(", ")
                    .append(javaString(parentKey(boundary.origin().parentOpId())))
                    .append(", List.of(JvmRuntime.rawAtom(").append(inputExpr)
                    .append(", ")
                    .append(javaString(staticKind(payload.descriptor())))
                    .append(")), null, null);\n");
            }
            out.append(indent(indent)).append("Object ").append(checkedName)
                .append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(checkedName)
                .append(" = ")
                .append(bcheckArgs(payload.descriptor(), inputExpr))
                .append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __fbe) {\n");
            out.append(indent(indent + 1))
                .append("JvmRuntime.DealError __fbre = new JvmRuntime.DealError("
                    + "__fbe.code, __fbe.msg, ")
                .append(javaString(originOf(boundary)))
                .append(", __fbe.expected, __fbe.actual, __fbe.frames, null);\n");
            if (trace) {
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__fbre)", indent + 1);
                emitFailureEvent(owner.opId(), owner.kind().name(), owner,
                    "JvmRuntime.errtext(__fbre)", indent + 1);
            }
            out.append(indent(indent + 1)).append("throw __fbre;\n");
            out.append(indent(indent)).append("}\n");
            emitBoundarySuccess(boundary, checkedName, payload.descriptor(), indent);
        }

        private void emitMemberWrite(SemanticOp op, int indent) {
            KindPayload.MemberWritePayload payload =
                (KindPayload.MemberWritePayload) op.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("((").append("JvmRuntime.Table) ")
                .append(slot(payload.table())).append(").write(")
                .append(javaString(payload.key())).append(", ")
                .append(slot(payload.value())).append(");\n");
            emitPlainSuccess(op, indent);
        }

        private void emitMemberDelete(SemanticOp op, int indent) {
            KindPayload.MemberDeletePayload payload =
                (KindPayload.MemberDeletePayload) op.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("((").append("JvmRuntime.Table) ")
                .append(slot(payload.table())).append(").remove(")
                .append(javaString(payload.key())).append(");\n");
            emitPlainSuccess(op, indent);
        }

        private void emitNormalize(SemanticOp op, int indent) {
            KindPayload.IndexNormalizePayload payload =
                (KindPayload.IndexNormalizePayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            switch (payload.mode()) {
                case ARRAY_READ, ARRAY_WRITE -> {
                    boolean write = payload.mode() == deal.semantic.ir.IndexMode.ARRAY_WRITE;
                    // The normalized index/length are numeric views: a
                    // runtime number carrier (the value model's variant
                    // representation) unwraps, a plain Long passes through.
                    out.append(indent(indent)).append(target)
                        .append(" = new long[]{JvmRuntime.indexOf(")
                        .append(slot(payload.rawKey())).append("), JvmRuntime.indexOf(")
                        .append(slot(payload.currentLength())).append("), ")
                        .append(write ? "1L" : "0L").append("};\n");
                }
                case BYTES_READ, BYTES_WRITE ->
                    // The bytes slot (K6 item 5): the index against the
                    // receiver's length read; no append decision exists.
                    out.append(indent(indent)).append(target)
                        .append(" = new Object[]{\"b\", Long.valueOf(JvmRuntime.indexOf(")
                        .append(slot(payload.rawKey()))
                        .append(")), Long.valueOf(JvmRuntime.indexOf(")
                        .append(slot(payload.currentLength())).append("))};\n");
                case TABLE_READ, TABLE_WRITE ->
                    out.append(indent(indent)).append(target).append(" = new Object[]{")
                        .append("\"t\", ").append(slot(payload.rawKey())).append("};\n");
            }
            // SUCCESS with the closed slot atom.
            out.append(indent(indent)).append("if (").append(target)
                .append(" instanceof long[]) {\n");
            out.append(indent(indent)).append("  long[] __s = (long[]) ").append(target)
                .append(";\n");
            out.append(indent(indent)).append(
                "  JvmRuntime.ev(MODULE, ").append(javaString(opKey(op.opId())))
                .append(", \"SUCCESS\", \"INDEX_NORMALIZE\", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), \"slot:\" + __s[0] + \"/\" + (__s[0] < __s[1]) "
                    + "+ \"/\" + (__s[2] == 1 && __s[0] == __s[1]), null);\n");
            out.append(indent(indent)).append("} else if (\"b\".equals(((Object[]) ")
                .append(target).append(")[0])) {\n");
            out.append(indent(indent)).append("  Object[] __s = (Object[]) ").append(target)
                .append(";\n");
            out.append(indent(indent)).append(
                "  JvmRuntime.ev(MODULE, ").append(javaString(opKey(op.opId())))
                .append(", \"SUCCESS\", \"INDEX_NORMALIZE\", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), \"byteslot:\" + __s[1] + \"/\" + (((Long) __s[1]) "
                    + "< ((Long) __s[2])), null);\n");
            out.append(indent(indent)).append("} else {\n");
            out.append(indent(indent)).append("  Object[] __s = (Object[]) ").append(target)
                .append(";\n");
            out.append(indent(indent)).append(
                "  JvmRuntime.ev(MODULE, ").append(javaString(opKey(op.opId())))
                .append(", \"SUCCESS\", \"INDEX_NORMALIZE\", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), \"keyslot:\" + JvmRuntime.esc((String) __s[1]), "
                    + "null);\n");
            out.append(indent(indent)).append("}\n");
        }

        private void emitIndexRead(SemanticOp op, int indent) {
            KindPayload.IndexReadPayload payload = (KindPayload.IndexReadPayload) op.payload();
            SemanticOp boundary = opsById.get(payload.elementBoundaryOpId());
            RuntimeDescriptor descriptor =
                ((KindPayload.BoundaryPayload) boundary.payload()).descriptor();
            boolean nullable = descriptor instanceof RuntimeDescriptor.Nullable;
            RuntimeDescriptor inner = nullable
                ? ((RuntimeDescriptor.Nullable) descriptor).inner() : descriptor;
            if (!op.operandTypes().isEmpty()
                    && op.operandTypes().get(0) instanceof RuntimeDescriptor.Bytes) {
                // K6 item 2: the bytes element read — the length read's
                // result is the normalize's currentLength and the
                // BYTE_ELEMENT_READ cell consumes {index, length} from the
                // same slot.
                emitBytesSlotOperandStart(op, indent);
                String bytesTarget = slot((ValueId) op.result());
                out.append(indent(indent)).append(bytesTarget)
                    .append(" = JvmRuntime.bytesRead(")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(opKey(boundary.opId()))).append(", ")
                    .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(boundary.origin().parentOpId())))
                    .append(", ").append(slot(payload.container())).append(", ((Long) ")
                    .append("((Object[]) ").append(slot(payload.slot()))
                    .append(")[1]).longValue(), ((Long) ((Object[]) ")
                    .append(slot(payload.slot())).append(")[2]).longValue(), ")
                    .append(javaString(originOf(boundary))).append(");\n");
                emitResultSuccess(op, bytesTarget, (RuntimeDescriptor) op.resultType(),
                    indent);
                return;
            }
            emitSlotOperandStart(op, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target).append(" = JvmRuntime.arrayRead(")
                .append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(opKey(boundary.opId()))).append(", ")
                .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(boundary.origin().parentOpId()))).append(", ")
                .append(javaString(descriptorText(descriptor))).append(", ")
                .append(javaString(staticKind(inner))).append(", (JvmRuntime.Array) ")
                .append(slot(payload.container())).append(", ((long[]) ")
                .append(slot(payload.slot())).append(")[0], ")
                .append(nullable ? "true" : "false").append(", ")
                .append(javaString(originOf(op))).append(");\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitIndexWrite(SemanticOp op, int indent) {
            KindPayload.IndexWritePayload payload =
                (KindPayload.IndexWritePayload) op.payload();
            emitStart(op, indent);
            String container = slot(payload.container());
            String slotName = slot(payload.slot());
            String value = slot(payload.value());
            out.append(indent(indent)).append("if (").append(slotName)
                .append(" instanceof long[]) {\n");
            out.append(indent(indent)).append("  long[] __s = (long[]) ").append(slotName)
                .append(";\n");
            out.append(indent(indent)).append("  if (__s[2] == 1 && __s[0] == __s[1]) ((")
                .append("JvmRuntime.Array) ").append(container).append(").length++;\n");
            out.append(indent(indent)).append("  int __wi = (int) __s[0];\n");
            out.append(indent(indent)).append("  while (((")
                .append("JvmRuntime.Array) ").append(container)
                .append(").elements.size() <= __wi) ((")
                .append("JvmRuntime.Array) ").append(container)
                .append(").elements.add(null);\n");
            out.append(indent(indent)).append("  ((")
                .append("JvmRuntime.Array) ").append(container)
                .append(").elements.set(__wi, ").append(value).append(");\n");
            out.append(indent(indent)).append("} else if (\"b\".equals(((Object[]) ")
                .append(slotName).append(")[0])) {\n");
            // The bytes commit (K6 item 4): the E8013 value-range check at
            // the assignment expression and the single in-place mutation;
            // the bounds already passed at the chain's
            // BYTE_ELEMENT_ASSIGNMENT boundary.
            out.append(indent(indent)).append("  Object[] __s = (Object[]) ").append(slotName)
                .append(";\n");
            out.append(indent(indent)).append("  JvmRuntime.bytesCommit(")
                .append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(container).append(", ((Long) __s[1]).longValue(), ").append(value)
                .append(", ").append(javaString(originOf(op))).append(");\n");
            out.append(indent(indent)).append("} else {\n");
            out.append(indent(indent)).append("  Object[] __s = (Object[]) ").append(slotName)
                .append(";\n");
            out.append(indent(indent)).append("  ((").append("JvmRuntime.Table) ")
                .append(container).append(").write((String) __s[1], ").append(value)
                .append(");\n");
            out.append(indent(indent)).append("}\n");
            emitPlainSuccess(op, indent);
        }

        private void emitIndexDelete(SemanticOp op, int indent) {
            KindPayload.IndexDeletePayload payload =
                (KindPayload.IndexDeletePayload) op.payload();
            emitStart(op, indent);
            String container = slot(payload.container());
            String slotName = slot(payload.slot());
            out.append(indent(indent)).append("if (").append(slotName)
                .append(" instanceof long[]) {\n");
            out.append(indent(indent)).append("  long[] __s = (long[]) ").append(slotName)
                .append(";\n");
            out.append(indent(indent)).append("  if (__s[0] < ((")
                .append("JvmRuntime.Array) ").append(container).append(").length && __s[0] < ((")
                .append("JvmRuntime.Array) ").append(container)
                .append(").elements.size()) ((").append("JvmRuntime.Array) ")
                .append(container).append(").elements.set((int) __s[0], "
                    + "JvmRuntime.MISSING);\n");
            out.append(indent(indent)).append("} else {\n");
            out.append(indent(indent)).append("  Object[] __s = (Object[]) ").append(slotName)
                .append(";\n");
            out.append(indent(indent)).append("  ((").append("JvmRuntime.Table) ")
                .append(container).append(").remove((String) __s[1]);\n");
            out.append(indent(indent)).append("}\n");
            emitPlainSuccess(op, indent);
        }

        /**
         * A free BOUNDARY op: the runtime check over the payload input,
         * run under the boundary's own origin with the boundary's own
         * single FAILURE terminal — the parented arms' contract (no owner
         * terminal exists for an unparented boundary); the success
         * terminal is unchanged.
         */
        private void emitFreeBoundary(SemanticOp op, int indent) {
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                .append("\"BOUNDARY\", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), null, null);\n");
            }
            String target = "__fb_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(target).append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent)).append("  ").append(target)
                .append(" = ")
                .append(bcheckArgs(payload.descriptor(), slot(payload.input())))
                .append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
            out.append(indent(indent))
                .append("  JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                    + "__be.code, __be.msg, ")
                .append(javaString(originOf(op)))
                .append(", __be.expected, __be.actual, __be.frames, null);\n");
            if (trace) {
                emitFailureEvent(op.opId(), "BOUNDARY", op,
                    "JvmRuntime.errtext(__bre)", indent + 1);
            }
            out.append(indent(indent)).append("  throw __bre;\n");
            out.append(indent(indent)).append("}\n");
            if (op.result() instanceof ValueId valueId) {
                out.append(indent(indent)).append(slot(valueId)).append(" = ")
                    .append(target).append(";\n");
                emitBoundarySuccess(op, slot(valueId), payload.descriptor(), indent);
            } else {
                emitBoundarySuccess(op, target, payload.descriptor(), indent);
            }
        }

        private void emitBindingAlloc(SemanticOp op, int indent) {
            KindPayload.BindingAllocPayload payload =
                (KindPayload.BindingAllocPayload) op.payload();
            emitStart(op, indent);
            if (isCatchBinding(payload.binding())) {
                // The catch binding's ALLOC sits at the catch block's entry
                // and its pinned initializing write is the TRY_CATCH arm's
                // catch-entry assignment, which runs before the catch block's
                // ops (the catch binding's cell carries the reified Error
                // value — ISSUE-0619's catch reification). A cell reset here
                // would clobber the caught value.
                emitPlainSuccess(op, indent);
                return;
            }
            switch (cellKindOf(payload.binding(), payload.generation())) {
                case DIRECT -> out.append(indent(indent))
                    .append(cell(payload.binding(), payload.generation())).append(" = null;\n");
                case SHARED_CELL -> out.append(indent(indent))
                    .append(cell(payload.binding(), payload.generation())).append(" = new Object[1];\n");
            }
            emitPlainSuccess(op, indent);
        }

        /**
         * True iff the binding is a {@code TRY_CATCH} op's catch binding in
         * the closure: its cell is created and initialized by the
         * {@code TRY_CATCH} arm's catch-entry write, so the catch binding's
         * {@code BINDING_ALLOC} (the catch block's first op) must not reset
         * it.
         */
        private boolean isCatchBinding(deal.semantic.ir.BindingId binding) {
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

        private void emitBindingInit(SemanticOp op, int indent) {
            KindPayload.BindingInitPayload payload =
                (KindPayload.BindingInitPayload) op.payload();
            emitStart(op, indent);
            BindingCellKind kind = cellKindOf(payload.binding(), payload.generation());
            String valueExpr = intrinsicCarrierExpr(payload.value());
            if (valueExpr == null) {
                valueExpr = hasProducer(payload.value())
                    ? slot(payload.value()) : exportPlaceholderCarrier();
            }
            if (kind == BindingCellKind.SHARED_CELL) {
                out.append(indent(indent)).append("((").append("Object[]) ")
                    .append(cellSource(payload.binding(), payload.generation())).append(")[0] = ")
                    .append(valueExpr).append(";\n");
            } else {
                out.append(indent(indent)).append(cellSource(payload.binding(), payload.generation())).append(" = ")
                    .append(valueExpr).append(";\n");
            }
            emitPlainSuccess(op, indent);
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
                    new deal.semantic.ir.FunctionAllocationIdentity(valueId.id()));
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
                    new deal.semantic.ir.FunctionAllocationIdentity(valueId.id()));
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
            return "JvmRuntime.intrinsicExport()";
        }

        /**
         * The memoized carrier accessor of one intrinsic kind: the kind
         * tag and the intrinsic's declared descriptor text and canonical
         * spec text — the only descriptor source (never a call site's or
         * an adapter target's).
         */
        private static String intrinsicAccessor(IntrinsicKind kind) {
            RuntimeDescriptor.Func declared = kind.declaredSignature();
            return "JvmRuntime.intrinsic(" + javaString(kind.name()) + ", "
                + javaString(descriptorText(declared)) + ", "
                + javaString(declared.canonicalSpecText()) + ")";
        }

        private void emitBindingLoad(SemanticOp op, int indent) {
            KindPayload.BindingLoadPayload payload =
                (KindPayload.BindingLoadPayload) op.payload();
            emitStart(op, indent);
            BindingCellKind kind = cellKindOf(payload.binding(), payload.generation());
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(kind == BindingCellKind.SHARED_CELL
                    ? "((Object[]) " + cellSource(payload.binding(), payload.generation()) + ")[0]"
                    : cellSource(payload.binding(), payload.generation()))
                .append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitBindingStore(SemanticOp op, int indent) {
            KindPayload.BindingStorePayload payload =
                (KindPayload.BindingStorePayload) op.payload();
            emitStart(op, indent);
            BindingCellKind kind = cellKindOf(payload.binding(), payload.generation());
            if (kind == BindingCellKind.SHARED_CELL) {
                out.append(indent(indent)).append("((").append("Object[]) ")
                    .append(cellSource(payload.binding(), payload.generation())).append(")[0] = ")
                    .append(slot(payload.value())).append(";\n");
            } else {
                out.append(indent(indent)).append(cellSource(payload.binding(), payload.generation())).append(" = ")
                    .append(slot(payload.value())).append(";\n");
            }
            emitPlainSuccess(op, indent);
        }

        private void emitClosureNew(SemanticOp op, int indent) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            StringBuilder args = new StringBuilder();
            for (BindingGeneration capture : payload.captures()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(captureArg(capture));
            }
            out.append(indent(indent)).append(target).append(" = ")
                .append(fnFactory(payload.function())).append("(").append(args)
                .append(");\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * FUNCTION_ADAPT (E6, D15 creation): a generated adapter object
         * carrying the closed capture mode — VALUE retains the
         * creation-time source identity; SHARED_CELL records the
         * generation cell re-read per invocation (live reassignment
         * observed); REEVALUATE_THUNK records the detached thunk
         * re-executor method. Creation evaluates no thunk and reads no
         * binding (VALUE's single operand already completed); every
         * invocation runs the D15 sequence through
         * {@code JvmRuntime.invokeAdapter} with the invoking op's
         * origin.
         */
        private void emitFunctionAdapt(SemanticOp op, int indent) {
            KindPayload.FunctionAdaptPayload payload =
                (KindPayload.FunctionAdaptPayload) op.payload();
            // The VALUE operand's carrier expression: for the seeded
            // intrinsic identity no field holds it before this creation, so
            // the START's operand atom and the adapter's own value field read
            // the one local the creation materializes (never an undeclared
            // slot).
            String valueLocal = null;
            if (payload.source() instanceof AdaptSourceRef.Value value) {
                valueLocal = "__iav_" + op.opId().id();
                out.append(indent(indent)).append("Object ").append(valueLocal)
                    .append(" = ").append(adaptValueExpr(value)).append(";\n");
            }
            emitAdaptStart(op, payload, valueLocal, indent);
            String target = slot((ValueId) op.result());
            out.append(indent(indent)).append(target)
                .append(" = new JvmRuntime.AdapterValue(__a -> { throw new "
                    + "IllegalStateException(\"an adapter executes only under its "
                    + "invoking op's D15 protocol\"); }, ")
                .append(javaString(descriptorText(payload.targetSignature())))
                .append(", ")
                .append(javaString(payload.targetSignature().canonicalSpecText()))
                .append(", ");
            switch (payload.mode()) {
                case VALUE -> out.append("0");
                case SHARED_CELL -> out.append("1");
                case REEVALUATE_THUNK -> out.append("2");
            }
            switch (payload.source()) {
                case AdaptSourceRef.Value ignored ->
                    out.append(", ").append(valueLocal).append(", null, null");
                case AdaptSourceRef.SharedCell cell ->
                    out.append(", null, (Object[]) ")
                        .append(cell(cell.binding(), cell.generation()))
                        .append(", null");
                case AdaptSourceRef.Thunk thunk ->
                    out.append(", null, null, __t -> ")
                        .append(thunkFn(op.opId())).append("()");
            }
            out.append(", ").append(payload.sourceSignature().paramTypes().size())
                .append(", ")
                .append(javaString(payload.sourceSignature().canonicalSpecText()))
                .append(");\n");
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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
         * creation's own value local ({@code valueLocal}) exactly when the op
         * records that operand (the oracle atomizes its operand list); the
         * SHARED_CELL and REEVALUATE_THUNK modes carry zero operand atoms
         * (their operands are empty by construction).
         */
        private void emitAdaptStart(SemanticOp op,
                KindPayload.FunctionAdaptPayload payload, String valueLocal,
                int indent) {
            if (!trace) {
                return;
            }
            StringBuilder inputs = new StringBuilder();
            if (valueLocal != null && !op.operands().isEmpty()) {
                inputs.append("JvmRuntime.atom(").append(valueLocal).append(", ")
                    .append(javaString(staticKind(payload.sourceSignature())))
                    .append(")");
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(").append(inputs).append("), null, null);\n");
        }

        /**
         * RECURSIVE_GROUP_INIT (E8, atomic publication): phase 1
         * allocates every member's SHARED_CELL (a fresh one-element
         * array per execution); phase 2 allocates every member identity
         * into a local — the per-member factory invocation over the
         * member's capture cells; phase 3 assigns the member function
         * objects to the group fields in declaration order in one
         * ordered sequence. The publication writes into the
         * already-allocated cell arrays (never a replacement — a
         * sibling's capture holds the cell array by identity), and no
         * member observes a partially initialized group: no member body
         * runs at group execution and every identity is allocated before
         * the first publication.
         */
        private void emitRecursiveGroupInit(SemanticOp op, int indent) {
            KindPayload.RecursiveGroupInitPayload payload =
                (KindPayload.RecursiveGroupInitPayload) op.payload();
            emitStart(op, indent);
            for (BindingId binding : payload.bindings()) {
                out.append(indent(indent)).append(cell(binding, 0))
                    .append(" = new Object[1];\n");
            }
            for (int i = 0; i < payload.functions().size(); i++) {
                FunctionId functionId = payload.functions().get(i);
                LoweredFunction function = functionOf(functionId);
                if (function == null) {
                    throw new IllegalStateException("group member " + functionId
                        + " has no LoweredFunction record (producer defect)");
                }
                StringBuilder args = new StringBuilder();
                for (BindingGeneration capture : function.captures()) {
                    if (args.length() > 0) {
                        args.append(", ");
                    }
                    args.append(captureArg(capture));
                }
                out.append(indent(indent)).append("JvmRuntime.FunctionValue ")
                    .append(groupTemp(op, i)).append(" = ")
                    .append(fnFactory(functionId)).append("(").append(args)
                    .append(");\n");
            }
            for (int i = 0; i < payload.bindings().size(); i++) {
                out.append(indent(indent)).append("((Object[]) ")
                    .append(cell(payload.bindings().get(i), 0)).append(")[0] = ")
                    .append(groupTemp(op, i)).append(";\n");
            }
            emitPlainSuccess(op, indent);
        }

        /** One member identity local of the group op (per-op unique). */
        private String groupTemp(SemanticOp op, int member) {
            return "__gv" + op.opId().id() + "_" + member;
        }

        private void emitAssign(SemanticOp op, int indent) {
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) op.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("try {\n");
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opsById.get(childId);
                emitChainOperandProducers(child, indent + 1);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    emitChainBoundary(child,
                        (KindPayload.BoundaryPayload) child.payload(), op, indent + 1);
                } else {
                    emitOp(child, indent + 1);
                }
            }
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(__e)",
                indent + 1);
            out.append(indent(indent)).append("  throw __e;\n");
            out.append(indent(indent)).append("}\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                producerResultType(op.result()), indent);
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

        private void emitDelete(SemanticOp op, int indent) {
            KindPayload.DeletePayload payload = (KindPayload.DeletePayload) op.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("try {\n");
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opsById.get(childId);
                emitChainOperandProducers(child, indent + 1);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    emitChainBoundary(child,
                        (KindPayload.BoundaryPayload) child.payload(), op, indent + 1);
                } else {
                    emitOp(child, indent + 1);
                }
            }
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(__e)",
                indent + 1);
            out.append(indent(indent)).append("  throw __e;\n");
            out.append(indent(indent)).append("}\n");
            emitPlainSuccess(op, indent);
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
        private void emitChainOperandProducers(SemanticOp child, int indent) {
            for (SemanticOp producer : ChainOperandCompletion.operandProducersOf(
                    child, unitOwning(child), structuralOwned)) {
                emitOp(producer, indent);
            }
        }

        /**
         * The lowered unit that owns one op (the chain-operand completion's
         * membership authority): a chain inside a non-entry module's
         * factory resolves its operand producers against that module's own
         * ops, never against the session's entry unit — a cross-module
         * closure body's chain (the returned-closure drive) would otherwise
         * lose its operand producers (their value identities live in the
         * owning module) and execute with unset slots.
         */
        private LoweredModuleUnit unitOwning(SemanticOp op) {
            ModuleId owner = opModule.get(op.opId());
            LoweredModuleUnit owning = owner == null ? null : units.get(owner);
            return owning == null ? unit : owning;
        }

        /**
         * A chain boundary child: the bounds check runs only from this
         * boundary's projection with the chain-supplied {index, length}
         * context (A-D8 — never a target-side re-check that can raise
         * twice).
         */
        private void emitChainBoundary(SemanticOp boundary,
                                       KindPayload.BoundaryPayload payload,
                                       SemanticOp chain, int indent) {
            String input = slot(payload.input());
            switch (payload.kind()) {
                case BYTE_ELEMENT_ASSIGNMENT -> {
                    // K6 item 4: the E8012 bounds cell (index-expression
                    // origin), then the element descriptor check; the
                    // commit owns the E8013 range check.
                    out.append(indent(indent)).append("JvmRuntime.bytesBounds(")
                        .append(javaString(opKey(boundary.opId()))).append(", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", ").append(input).append(", ((Long) ((Object[]) ")
                        .append(chainSlotExpr(chain)).append(")[1]).longValue(), ((Long) ")
                        .append("((Object[]) ").append(chainSlotExpr(chain))
                        .append(")[2]).longValue(), ")
                        .append(javaString(descriptorText(payload.descriptor())))
                        .append(", ").append(javaString(staticKind(payload.descriptor())))
                        .append(", ").append(javaString(originOf(boundary)))
                        .append(");\n");
                }
                case ARRAY_ELEMENT_ASSIGNMENT, ARRAY_ELEMENT_DELETE -> {
                    // JvmRuntime.arrayBounds emits the boundary START/terminal
                    // events (the bounds check runs only from this projection);
                    // the delete boundary's input operand is the normalized
                    // slot (the closed slot atom, never a value atom).
                    if (payload.kind() == BoundaryKind.ARRAY_ELEMENT_DELETE
                            && slotEqualsChainSlot(payload.input(), chain)) {
                        out.append(indent(indent))
                            .append("JvmRuntime.arrayBoundsSlot(")
                            .append(javaString(opKey(boundary.opId()))).append(", ")
                            .append(javaString(boundary.contract().canonicalDigest()))
                            .append(", ")
                            .append(javaString(parentKey(boundary.origin().parentOpId())))
                            .append(", (long[]) ").append(chainSlotExpr(chain))
                            .append(", JvmRuntime.indexOf(").append(chainLengthExpr(chain))
                            .append("), ")
                            .append(javaString(originOf(boundary))).append(");\n");
                    } else {
                    out.append(indent(indent)).append("JvmRuntime.arrayBounds(")
                        .append(javaString(opKey(boundary.opId()))).append(", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", ").append(input).append(", ((long[]) ")
                        .append(chainSlotExpr(chain)).append(")[0], JvmRuntime.indexOf(")
                        .append(chainLengthExpr(chain)).append("), ")
                        .append(javaString(descriptorText(payload.descriptor())))
                        .append(", ")
                        .append(javaString(staticKind(payload.descriptor())))
                        .append(", ")
                        .append(payload.kind() == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                            ? "true" : "false").append(", ")
                        .append(javaString(originOf(boundary))).append(");\n");
                    }
                }
                default -> {
                    emitBoundaryStart(boundary, input, payload.descriptor(), indent);
                    out.append(indent(indent)).append("Object __cb_")
                        .append(boundary.opId().id())
                        .append(" = ")
                        .append(bcheckArgs(payload.descriptor(), input))
                        .append(";\n");
                    emitBoundarySuccess(boundary, "__cb_" + boundary.opId().id(),
                        payload.descriptor(), indent);
                }
            }
        }

        private List<OpId> chainChildOps(SemanticOp chain) {
            return switch (chain.payload()) {
                case KindPayload.AssignPayload assign -> assign.childOps();
                case KindPayload.DeletePayload delete -> delete.childOps();
                default -> List.of();
            };
        }

        /** True iff the boundary input value is the chain's normalize slot. */
        private boolean slotEqualsChainSlot(deal.semantic.ir.ValueId input,
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

        /** The chain's normalize-slot local (found among its children). */
        private String chainSlotExpr(SemanticOp chain) {
            for (OpId childId : chainChildOps(chain)) {
                SemanticOp child = opsById.get(childId);
                if (child.kind() == SemanticOpKind.INDEX_NORMALIZE
                        && child.result() instanceof ValueId valueId) {
                    return slot(valueId);
                }
            }
            return "null";
        }

        private String chainLengthExpr(SemanticOp chain) {
            for (OpId childId : chainChildOps(chain)) {
                SemanticOp child = opsById.get(childId);
                if (child.kind() == SemanticOpKind.ARRAY_LENGTH
                        && child.result() instanceof ValueId valueId) {
                    return slot(valueId);
                }
            }
            return "null";
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

        private void emitCall(SemanticOp op, int indent) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
            FunctionExecutionBinding binding = callBinding(payload);
            emitStart(op, indent);
            // The host arms (ISSUE-0651; host-module-load-and-host-call-
            // realization H3 and the sync host call contract): the loaded
            // surface entry is invoked through the emitted per-export
            // wrapper and the boundary children's events surround the
            // checks. The wrapper is the single check authority for the
            // host cells: the arm runs no generic descriptor-kind check on
            // the DEAL_TO_HOST/HOST_TO_DEAL cells.
            if (binding instanceof FunctionExecutionBinding.HostFunction host) {
                emitHostCall(op, payload, host.hostModuleId(), host.exportName(), indent);
                return;
            }
            if (binding instanceof FunctionExecutionBinding.HostFunctionValue hostValue) {
                emitHostValueCall(op, payload, hostValue, indent);
                return;
            }
            // The conversion intrinsic's value call (ISSUE-0679; design source
            // {@code conversion-intrinsic-function-values} J3/J4): the seeded
            // identity's registration is a boundary-shaped callable, so the
            // indirect arm runs the recorded host cell family and the one
            // conversion ladder with the invoking CALL op's own context and
            // kind, exactly the landed statically classified rows' discipline.
            if (binding instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic) {
                emitIntrinsicValueCall(op, payload, intrinsic, indent);
                return;
            }
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                emitBoundaryStart(boundary, slot(boundaryPayload.input()),
                    boundaryPayload.descriptor(), indent);
                // The cell runs under the recorded call origin: a failing
                // declared parameter reports the callee's parameter
                // declaration (the pinned corpus span), and the boundary
                // and the CALL each publish their own FAILURE terminal
                // (the oracle's exact sequence).
                String cell = "__pb_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(cell)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(cell).append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(),
                        slot(boundaryPayload.input())))
                    .append(";\n");
                out.append(indent(indent))
                    .append("} catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("  JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                out.append(indent(indent)).append("  throw __bre;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, cell, boundaryPayload.descriptor(),
                    indent);
            }
            if (payload.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                // The dynamic dispatch (ISSUE-0658): the recorded parameter
                // cells above are the class-independent family; the
                // carrier's own class tag selects the path.
                emitDynamicCall(op, payload, dynamic, indent);
                emitResultSuccess(op, slot((ValueId) op.result()),
                    (RuntimeDescriptor) op.resultType(), indent);
                return;
            }
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionId callee = body.functionId();
                    StateSlot savedState = emitInvocationStateSave(callee, op.opId(),
                        indent);
                    // The invocation's result lands in a method-local: the
                    // callee's own private state is restored by the finally
                    // below, and a recursive call shares the result slot's
                    // name (the call site's slot belongs to the callee's
                    // body too) — the assignment therefore happens after
                    // the restore.
                    String resultLocal = "__res_" + op.opId().id();
                    out.append(indent(indent)).append("Object ").append(resultLocal)
                        .append(" = null;\n");
                    out.append(indent(indent)).append("try {\n");
                    out.append(indent(indent + 1)).append("JvmRuntime.pushFrame(")
                        .append(javaString(String.valueOf(callee.id()))).append(");\n");
                    out.append(indent(indent + 1)).append("try {\n");
                    out.append(indent(indent + 1)).append("  ")
                        .append(resultLocal)
                        .append(" = ");
                    if (payload.callee()
                            instanceof KindPayload.CallCallee.Indirect indirect) {
                        // The value-carried invocation (a body with
                        // creation-site captures): the closure value the
                        // binding holds runs its own invoker, whose
                        // captured cells are the ones its creation
                        // published — never a call-site re-resolution of
                        // a per-iteration incarnation.
                        out.append("((JvmRuntime.FunctionValue) ")
                            .append(slot(indirect.callee()))
                            .append(").fn.invoke(new Object[]{");
                    } else {
                        out.append(fnFactory(callee)).append("(");
                        deal.semantic.ir.LoweredFunction calleeFunction =
                            functionOf(callee);
                        List<deal.semantic.ir.BindingGeneration> captures =
                            calleeFunction == null ? List.of()
                                : calleeFunction.captures();
                        for (int i = 0; i < captures.size(); i++) {
                            if (i > 0) {
                                out.append(", ");
                            }
                            out.append(captureArg(captures.get(i)));
                        }
                        out.append(").fn.invoke(new Object[]{");
                    }
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        if (i > 0) {
                            out.append(", ");
                        }
                        SemanticOp boundary =
                            opsById.get(payload.parameterBoundaryOpIds().get(i));
                        out.append(slot(((KindPayload.BoundaryPayload) boundary.payload())
                            .input()));
                    }
                    out.append("});\n");
                    out.append(indent(indent + 1))
                        .append("} catch (JvmRuntime.DealError __e) {\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__e)", indent + 2);
                    out.append(indent(indent + 1)).append("  throw __e;\n");
                    out.append(indent(indent + 1)).append("} finally {\n");
                    out.append(indent(indent + 1)).append("  JvmRuntime.popFrame();\n");
                    out.append(indent(indent + 1)).append("}\n");
                    out.append(indent(indent)).append("} finally {\n");
                    emitInvocationStateRestore(callee, savedState, indent + 1);
                    out.append(indent(indent)).append("}\n");
                    out.append(indent(indent)).append(slot((ValueId) op.result()))
                        .append(" = ").append(resultLocal).append(";\n");
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
                        emitAdapterOverIntrinsicRun(op, payload, adapter, indent);
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
                    // The resolved source's own module carries the events of
                    // its body (the oracle's owning-unit body run): a
                    // cross-module adapted source reports its own module,
                    // never the invoking module's tag, so the frame's body
                    // resolves like a dynamic DEAL-body invocation's. A
                    // REEVALUATE_THUNK source is only resolved by the
                    // adapter protocol itself (a pre-resolution would run
                    // the thunk twice), so its crossing keeps the landed
                    // single evaluation.
                    String adapterSuffix = String.valueOf(op.opId().id());
                    boolean switchAdapterModule =
                        adapter.captureMode() != deal.semantic.ir.CaptureMode
                            .REEVALUATE_THUNK;
                    if (switchAdapterModule) {
                        out.append(indent(indent)).append("Object __as")
                            .append(adapterSuffix).append(" = JvmRuntime.adapterSource("
                                + "(JvmRuntime.AdapterValue) ")
                            .append(adapterSlot).append(");\n");
                        out.append(indent(indent)).append("String __am")
                            .append(adapterSuffix).append(" = (__as")
                            .append(adapterSuffix)
                            .append(" instanceof JvmRuntime.FunctionValue __fv")
                            .append(adapterSuffix).append(" && __fv")
                            .append(adapterSuffix)
                            .append(".fid != null) ? dealModuleOfFunction(__fv")
                            .append(adapterSuffix).append(".fid) : null;\n");
                        out.append(indent(indent)).append("String __pm")
                            .append(adapterSuffix).append(" = MODULE;\n");
                        out.append(indent(indent)).append("String __pr")
                            .append(adapterSuffix)
                            .append(" = JvmRuntime.currentModule();\n");
                        out.append(indent(indent)).append("if (__am")
                            .append(adapterSuffix).append(" != null) { MODULE = __am")
                            .append(adapterSuffix)
                            .append("; JvmRuntime.setModule(MODULE); }\n");
                    }
                    out.append(indent(indent)).append("try {\n");
                    out.append(indent(indent)).append("  ")
                        .append(slot((ValueId) op.result()))
                        .append(" = JvmRuntime.invokeAdapter((JvmRuntime.AdapterValue) ")
                        .append(adapterSlot).append(", ")
                        .append(javaString(originOf(op))).append(", new Object[]{")
                        .append(args).append("});\n");
                    out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__e)", indent + 1);
                    out.append(indent(indent)).append("  throw __e;\n");
                    if (switchAdapterModule) {
                        out.append(indent(indent)).append("} finally {\n");
                        out.append(indent(indent)).append("  MODULE = __pm")
                            .append(adapterSuffix).append(";\n");
                        out.append(indent(indent)).append("  JvmRuntime.setModule(__pr")
                            .append(adapterSuffix).append(");\n");
                        out.append(indent(indent)).append("}\n");
                    } else {
                        out.append(indent(indent)).append("}\n");
                    }
                }
                case FunctionExecutionBinding.ExternalFunction external ->
                    emitExternalCall(op, payload, external, indent);
                default -> throw new IllegalStateException("CALL " + op.opId()
                    + " resolves a binding outside the statically-resolved slice: "
                    + binding);
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The {@code ExternalFunction(SHARED_BODY)} CALL arm (ISSUE-0654;
         * {@code cross-module-call-realization} X1/X4/X5 and the
         * cross-module sync call contract): the callee unit's recorded
         * {@code EXTERNAL_ENTRY} runs inside the one artifact under the
         * callee module's context (the {@code MODULE} literal and the
         * runtime's own module context), with the entry's trace events
         * parented to the caller's {@code CALL} op, and the callee body's
         * {@code RETURN} runs the callee's single {@code EXTERNAL_RETURN}
         * boundary. The caller publishes the returned value without
         * re-checking (its own {@code EXTERNAL_PARAMETER} cells ran
         * exactly once above); the module context is restored on success
         * and on failure.
         */
        private void emitExternalCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.ExternalFunction external, int indent) {
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
            String prevMod = "__xmm_" + op.opId().id();
            String prevRun = "__xmr_" + op.opId().id();
            StringBuilder caps = new StringBuilder();
            for (BindingGeneration capture : calleeFunction.captures()) {
                if (caps.length() > 0) {
                    caps.append(", ");
                }
                caps.append(captureArg(capture));
            }
            StringBuilder args = new StringBuilder();
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(slot(((KindPayload.BoundaryPayload)
                    opsById.get(boundaryId).payload()).input()));
            }
            // The saved module context lives in the enclosing block: the
            // try/finally's finally and the caller-level catch below both
            // restore from it (a try block's locals are not in the scope
            // of its own finally), and the caller's CALL FAILURE must
            // carry the caller's module (the oracle's own tagging) — the
            // entry's own terminals carry the callee's.
            out.append(indent(indent)).append("String ").append(prevMod)
                .append(" = MODULE;\n");
            out.append(indent(indent)).append("String ").append(prevRun)
                .append(" = JvmRuntime.currentModule();\n");
            // The invocation's result lands in a method-local: the
            // callee's own private state is restored by the state finally
            // below, and a recursive call shares the result slot's name
            // (the call site's slot belongs to the callee's body too) —
            // the assignment therefore happens after the restore.
            String resultLocal = "__res_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(resultLocal)
                .append(" = null;\n");
            StateSlot savedState = emitInvocationStateSave(entryPayload.function(),
                op.opId(), indent);
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append("try {\n");
            out.append(indent(indent + 2)).append("MODULE = ")
                .append(javaString(calleePath)).append(";\n");
            out.append(indent(indent + 2)).append("JvmRuntime.setModule(MODULE);\n");
            if (trace) {
                out.append(indent(indent + 2)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(entry.opId())))
                    .append(", \"START\", \"EXTERNAL_ENTRY\", ")
                    .append(javaString(entry.contract().canonicalDigest()))
                    .append(", ").append(javaString(opKey(op.opId())))
                    .append(", List.of(), null, null);\n");
            }
            out.append(indent(indent + 2)).append("JvmRuntime.pushFrame(")
                .append(javaString(String.valueOf(entryPayload.function().id())))
                .append(");\n");
            out.append(indent(indent + 2)).append("try {\n");
            out.append(indent(indent + 3)).append("try {\n");
            out.append(indent(indent + 4)).append(resultLocal)
                .append(" = ").append(fnFactory(entryPayload.function()))
                .append("(").append(caps).append(").fn.invoke(new Object[]{")
                .append(args).append("});\n");
            out.append(indent(indent + 3))
                .append("} catch (JvmRuntime.DealError __ex) {\n");
            if (trace) {
                out.append(indent(indent + 4)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(entry.opId())))
                    .append(", \"FAILURE\", \"EXTERNAL_ENTRY\", ")
                    .append(javaString(entry.contract().canonicalDigest()))
                    .append(", ").append(javaString(opKey(op.opId())))
                    .append(", List.of(), null, JvmRuntime.errtext(__ex));\n");
            }
            out.append(indent(indent + 4)).append("throw __ex;\n");
            out.append(indent(indent + 3)).append("}\n");
            if (trace) {
                out.append(indent(indent + 3)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(entry.opId())))
                    .append(", \"SUCCESS\", \"EXTERNAL_ENTRY\", ")
                    .append(javaString(entry.contract().canonicalDigest()))
                    .append(", ").append(javaString(opKey(op.opId())))
                    .append(", List.of(), JvmRuntime.atom(")
                    .append(resultLocal).append(", ")
                    .append(javaString(staticKind(
                        entryPayload.signature().returnType())))
                    .append("), null);\n");
            }
            out.append(indent(indent + 2)).append("} finally {\n");
            out.append(indent(indent + 3)).append("JvmRuntime.popFrame();\n");
            out.append(indent(indent + 2)).append("}\n");
            out.append(indent(indent + 1)).append("} finally {\n");
            out.append(indent(indent + 2)).append("MODULE = ").append(prevMod)
                .append(";\n");
            out.append(indent(indent + 2)).append("JvmRuntime.setModule(")
                .append(prevRun).append(");\n");
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__e)", indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("} finally {\n");
            emitInvocationStateRestore(entryPayload.function(), savedState, indent + 1);
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = ").append(resultLocal).append(";\n");
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

        /** A body-private cell key: {@code DIRECT} cells only (shared state stays shared). */
        private void addCellStateKey(java.util.Set<String> keys, BindingId binding,
                                     long generation) {
            if (cellKindOf(binding, generation) == BindingCellKind.SHARED_CELL) {
                return;
            }
            keys.add(cell(binding, generation));
        }

        /**
         * The re-entrant invocation's private-state save, or {@code null}
         * when the callee body has no private state. Only a nested
         * invocation of the same body (recursion) can overwrite the
         * enclosing invocation's own state, so the emitted arm records
         * whether the body is already active and saves the state exactly
         * then — a plain call keeps the flat observable state the
         * artifact's slots always had.
         */
        private StateSlot emitInvocationStateSave(FunctionId callee, OpId invocation,
                                                  int indent) {
            List<String> keys = bodyStateKeys(callee);
            if (keys.isEmpty()) {
                return null;
            }
            String previous = "__pa_" + invocation.id();
            String saved = "__sv_" + invocation.id();
            out.append(indent(indent)).append("boolean ").append(previous)
                .append(" = __bodyActive.contains(").append(callee.id())
                .append("L);\n");
            out.append(indent(indent)).append("Object[] ").append(saved)
                .append(" = ").append(previous).append(" ? new Object[]{")
                .append(String.join(", ", keys)).append("} : null;\n");
            out.append(indent(indent)).append("__bodyActive.add(")
                .append(callee.id()).append("L);\n");
            return new StateSlot(previous, saved);
        }

        /** The matching re-entrant restore, executed on every path. */
        private void emitInvocationStateRestore(FunctionId callee, StateSlot slot,
                                                int indent) {
            if (slot == null) {
                return;
            }
            List<String> keys = bodyStateKeys(callee);
            out.append(indent(indent)).append("if (").append(slot.previous())
                .append(") {\n");
            for (int i = 0; i < keys.size(); i++) {
                out.append(indent(indent + 1)).append(keys.get(i)).append(" = ")
                    .append(slot.saved()).append("[").append(i).append("];\n");
            }
            // A re-entrant invocation leaves the enclosing invocation's
            // marker in place; only the outermost one clears it.
            out.append(indent(indent)).append("} else {\n");
            out.append(indent(indent + 1)).append("__bodyActive.remove(")
                .append(callee.id()).append("L);\n");
            out.append(indent(indent)).append("}\n");
        }

        /** One invocation's re-entrant state save: its flag and its saved array. */
        private record StateSlot(String previous, String saved) {
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
         * The registered execution binding of one allocation identity. The
         * project session's units share one identity space (every semantic
         * id is globally unique within the closure), so the registration is
         * resolved across the closure's units: an {@code Indirect} callee
         * value of one unit may name an identity whose producing
         * {@code CLOSURE_NEW} sits in a dependency module (the same
         * resolution the semantic oracle's {@code bindingOf} performs).
         */
        private FunctionExecutionBinding bindingOfIdentity(ValueId identity) {
            for (LoweredModuleUnit moduleUnit : units.values()) {
                FunctionExecutionBinding found = moduleUnit.functionBindings().get(
                    new deal.semantic.ir.FunctionAllocationIdentity(identity.id()));
                if (found != null) {
                    return found;
                }
            }
            return null;
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
                    bindingOfIdentity(indirect.callee());
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
         * The dynamic CALL arm (ISSUE-0658;
         * {@code dynamic-call-shape-production-and-emission} Y2/Y3/Y5/Y6
         * and the dynamic dispatch contract): the recorded parameter
         * cells ran once, left to right, before the dispatch (the
         * class-independent family); the carrier's own class tag then
         * selects exactly one class path — never the checked descriptor,
         * the callee spelling, or an argument value.
         *
         * <p>{@code DEAL_BODY} resolves the carrier's function id to its
         * owning module through the emitted
         * {@code dealModuleOfFunction} lookup (built over the closure's
         * function ids), pushes the callee frame, switches the module
         * context, and invokes the carrier's own invoker ({@code fn});
         * {@code ADAPTER} runs the landed D15 sequence (the source
         * value's own tag, the source-signature check, the leading-M
         * argument projection) and executes the cell the source class
         * selects — a DEAL-body source runs that body's own
         * {@code RETURN} cell; {@code HOST} invokes the loaded surface
         * entry carrier through its own invoker and runs the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell of the
         * dynamic return-boundary set.</p>
         *
         * <p>Every other carrier — and an adapter whose D15 source value
         * identifies no executable class at this boundary — fails closed
         * with the pinned E8001 {@code expected function} projection
         * ({@code expected}/{@code actual}) at the call origin, exactly
         * the projection the materialization-site function row produces:
         * never a guessed path and never a silent no-op. The module
         * context and the frame stack are restored on success and on
         * failure.</p>
         */
        private void emitDynamicCall(SemanticOp op, KindPayload.CallPayload payload,
                                     KindPayload.CallCallee.Dynamic callee, int indent) {
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
            String id = String.valueOf(op.opId().id());
            String carrier = "__dc" + id;
            String result = "__dr" + id;
            String cls = "__dk" + id;
            // The recorded DEAL-body cell's closed form (ISSUE-0677; design
            // source {@code function-typed-value-materialization-and-dispatch}
            // M6): a call-owned record is executed by the invocation site on
            // the value the resolved body returned, after the body's own
            // RETURN ran the body's own cell; a callee-owned record is that
            // body's own cell and runs nothing here.
            SemanticOp recordedDealCell = opsById.get(cells.dealBodyBoundaryOpId());
            boolean callOwnedDealCell = recordedDealCell != null
                && callOwnedCell(recordedDealCell);
            StringBuilder args = new StringBuilder();
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(slot(((KindPayload.BoundaryPayload)
                    opsById.get(boundaryId).payload()).input()));
            }
            String argList = args.toString();
            out.append(indent(indent)).append("Object ").append(result)
                .append(" = null;\n");
            out.append(indent(indent)).append("Object ").append(carrier)
                .append(" = ").append(slot(callee.callee())).append(";\n");
            out.append(indent(indent)).append("String ").append(cls).append(";\n");
            out.append(indent(indent)).append("if (").append(carrier)
                .append(" instanceof JvmRuntime.AdapterValue) {\n");
            out.append(indent(indent + 1)).append(cls).append(" = \"ADAPTER\";\n");
            out.append(indent(indent)).append("} else if (").append(carrier)
                .append(" instanceof JvmRuntime.FunctionValue __fv").append(id)
                .append(" && __fv").append(id).append(".fid != null) {\n");
            out.append(indent(indent + 1)).append(cls).append(" = \"DEAL_BODY\";\n");
            out.append(indent(indent)).append("} else if (").append(carrier)
                .append(" instanceof JvmRuntime.FunctionValue) {\n");
            out.append(indent(indent + 1)).append(cls).append(" = \"HOST\";\n");
            out.append(indent(indent)).append("} else {\n");
            emitDynamicCarrierFailure(op, carrier, indent + 1);
            out.append(indent(indent)).append("}\n");
            // DEAL_BODY: the carrier's own invoker under the callee's
            // module; the frame and the module context are restored on
            // every path.
            out.append(indent(indent)).append("if (\"DEAL_BODY\".equals(")
                .append(cls).append(")) {\n");
            emitDynamicBodyInvoke(op, carrier, result,
                "new Object[]{ " + argList + " }", id, indent + 1);
            if (callOwnedDealCell) {
                emitRecordedCellRun(op, recordedDealCell, result, "__cr" + id,
                    indent + 1);
            }
            // ADAPTER: the landed D15 sequence; the source class selects
            // the return cell (a DEAL-body source runs its own body's
            // RETURN cell, and a call-owned recorded cell then runs at the
            // invocation site).
            out.append(indent(indent)).append("} else if (\"ADAPTER\".equals(")
                .append(cls).append(")) {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.AdapterValue __ad")
                .append(id).append(" = (JvmRuntime.AdapterValue) ").append(carrier)
                .append(";\n");
            out.append(indent(indent + 1)).append("Object __src").append(id)
                .append(" = JvmRuntime.fnCheck(JvmRuntime.adapterSource(__ad")
                .append(id).append("), __ad").append(id).append(".sourceSpec, ")
                .append(javaString(originOf(op))).append(");\n");
            out.append(indent(indent + 1)).append("if (__src").append(id)
                .append(" instanceof JvmRuntime.Intrinsic __ii").append(id)
                .append(") {\n");
            // The runtime adapter branch's intrinsic source (ISSUE-0680;
            // design source {@code conversion-intrinsic-function-values} J5):
            // the resolved source value is the memoized intrinsic carrier, so
            // the same D15 sequence runs here — the leading-M recorded
            // argument through the one conversion ladder with the invoking
            // CALL op's context and kind, then the recorded HOST_TO_DEAL +
            // HOST_SYNC_RETURN cell of the dynamic set (the source class is
            // HOST). Non-intrinsic source values keep the landed arms.
            if (payload.parameterBoundaryOpIds().isEmpty()) {
                // The leading-M projection of the runtime intrinsic source has
                // no argument to convert (the intrinsic declares one
                // parameter): the carrier fails closed at the call origin.
                emitDynamicCarrierFailure(op, carrier, indent + 2);
            } else {
                String dynamicArg = slot(((KindPayload.BoundaryPayload)
                    opsById.get(payload.parameterBoundaryOpIds().get(0)).payload())
                    .input());
                String converted = "__di" + id;
                out.append(indent(indent + 2)).append("Object ").append(converted)
                    .append(";\n");
                out.append(indent(indent + 2)).append("if (\"INT_CONVERT\".equals("
                    + "__ii").append(id).append(".kind)) {\n");
                out.append(indent(indent + 3)).append(converted)
                    .append(" = JvmRuntime.intConv(").append(dynamicArg).append(", ")
                    .append(javaString(op.kind().name())).append(", \"number\", ")
                    .append(intrinsicContextArgs(op)).append(");\n");
                out.append(indent(indent + 2)).append("} else {\n");
                out.append(indent(indent + 3)).append(converted)
                    .append(" = JvmRuntime.numConv(").append(dynamicArg).append(", ")
                    .append(javaString(op.kind().name())).append(", \"int\", ")
                    .append(intrinsicContextArgs(op)).append(");\n");
                out.append(indent(indent + 2)).append("}\n");
                String dynamicAdmitted = emitHostCellRun(op, hostCell, converted,
                    indent + 2);
                out.append(indent(indent + 2)).append(result).append(" = ")
                    .append(dynamicAdmitted).append(";\n");
            }
            out.append(indent(indent + 1)).append("} else if (__src").append(id)
                .append(" instanceof JvmRuntime.FunctionValue) {\n");
            emitDynamicBodyInvoke(op, "__src" + id, result,
                "java.util.Arrays.copyOfRange(new Object[]{ " + argList
                    + " }, 0, __ad" + id + ".arity)", id, indent + 2);
            if (callOwnedDealCell) {
                emitRecordedCellRun(op, recordedDealCell, result, "__cr" + id,
                    indent + 2);
            }
            out.append(indent(indent + 1)).append("} else {\n");
            emitDynamicCarrierFailure(op, "__src" + id, indent + 2);
            out.append(indent(indent + 1)).append("}\n");
            // HOST: the loaded surface entry carrier and the recorded
            // HOST_TO_DEAL + HOST_SYNC_RETURN cell.
            out.append(indent(indent)).append("} else {\n");
            emitDynamicHostRow(op, payload, hostCell, carrier, result, id, indent + 1);
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(result).append(";\n");
        }

        /**
         * One dynamically dispatched DEAL-body invocation: the carrier's
         * function id resolves its owning module through the emitted
         * lookup, the frame is pushed, the module context is switched,
         * and the carrier's own invoker runs; the invocation's private
         * state is restored and the op's FAILURE terminal carries the
         * caller's module when the callee fails.
         */
        private void emitDynamicBodyInvoke(SemanticOp op, String source, String result,
                                           String invokeArgs, String id, int indent) {
            String fid = "__fy" + id;
            out.append(indent(indent)).append("JvmRuntime.FunctionValue ").append(fid)
                .append(" = (JvmRuntime.FunctionValue) ").append(source).append(";\n");
            out.append(indent(indent)).append("if (").append(fid)
                .append(".fid == null) {\n");
            emitDynamicCarrierFailure(op, source, indent + 1);
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("String __fm").append(id)
                .append(" = dealModuleOfFunction(").append(fid).append(".fid);\n");
            out.append(indent(indent)).append("if (__fm").append(id)
                .append(" == null) {\n");
            emitDynamicCarrierFailure(op, source, indent + 1);
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("String __pm").append(id)
                .append(" = MODULE;\n");
            out.append(indent(indent)).append("String __pr").append(id)
                .append(" = JvmRuntime.currentModule();\n");
            out.append(indent(indent)).append("MODULE = __fm").append(id).append(";\n");
            out.append(indent(indent)).append("JvmRuntime.setModule(MODULE);\n");
            out.append(indent(indent)).append("JvmRuntime.pushFrame(").append(fid)
                .append(".fid);\n");
            out.append(indent(indent)).append("JvmRuntime.DealError __fd").append(id)
                .append(" = null;\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(result).append(" = ")
                .append(fid).append(".fn.invoke(").append(invokeArgs)
                .append(");\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e")
                .append(id).append(") {\n");
            out.append(indent(indent + 1)).append("__fd").append(id)
                .append(" = __e").append(id).append(";\n");
            out.append(indent(indent)).append("} finally {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.popFrame();\n");
            out.append(indent(indent + 1)).append("MODULE = __pm").append(id)
                .append(";\n");
            out.append(indent(indent + 1)).append("JvmRuntime.setModule(__pr")
                .append(id).append(");\n");
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("if (__fd").append(id)
                .append(" != null) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__fd" + id + ")", indent + 1);
            out.append(indent(indent + 1)).append("throw __fd").append(id)
                .append(";\n");
            out.append(indent(indent)).append("}\n");
        }

        /**
         * The dynamic dispatch's HOST row: the carrier's own HOST sub-class
         * decides the path (never the checked descriptor). The conversion
         * intrinsic ({@code JvmRuntime.Intrinsic}) runs the closed kind's
         * conversion ladder with the invoking CALL op's own context and kind
         * label — one algorithm authority with the direct
         * {@code INTRINSIC_CALL} arm (ISSUE-0679; design source
         * {@code conversion-intrinsic-function-values} J3/J4). The cataloged
         * stdlib callable ({@code StdlibFunctionValue}) runs the closed catalog
         * row's one invoker — {@code JvmRuntime.invokeStdlibCallable} with the
         * invoking CALL op's context (the row identity plus the op key, contract
         * digest, parent key, origin, and the invoking op's own kind label for
         * its FAILURE event) — one algorithm authority with the direct
         * {@code STDLIB_CALL} arm and the read's callable. A loaded surface entry
         * bridges the emitted per-export wrapper ({@code carrier.fn}) with the
         * completed production values. Every sub-class then runs the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell at the call origin
         * (the oracle's {@code invokeResolvedHostRequest} followed by
         * {@code runBoundaryChild}).
         */
        private void emitDynamicHostRow(SemanticOp op, KindPayload.CallPayload payload,
                                        SemanticOp returnBoundary, String carrier,
                                        String result, String id, int indent) {
            StringBuilder args = new StringBuilder();
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(slot(((KindPayload.BoundaryPayload)
                    opsById.get(boundaryId).payload()).input()));
            }
            String hostValue = "__dh" + id;
            out.append(indent(indent)).append("Object ").append(hostValue).append(";\n");
            // The conversion intrinsic's HOST sub-class (ISSUE-0679; design
            // source {@code conversion-intrinsic-function-values} J3/J4): the
            // carrier's own kind tag selects the one conversion ladder — never
            // a spelling, a checked descriptor, or an argument value — with
            // the invoking CALL op's own context and kind label (the pinned
            // conversion texts and the FAILURE event carry the invoking op),
            // over the value the recorded class-independent parameter cells
            // admitted. The intrinsic's declared arity is one, so a site with
            // exactly one recorded parameter cell carries the ladder; the tag
            // still fails closed at any other arity rather than guessing a
            // conversion.
            if (payload.parameterBoundaryOpIds().size() == 1) {
                String declaredKind = javaString(staticKind(
                    ((KindPayload.BoundaryPayload) opsById.get(
                        payload.parameterBoundaryOpIds().get(0)).payload()).descriptor()));
                out.append(indent(indent)).append("if (").append(carrier)
                    .append(" instanceof JvmRuntime.Intrinsic __iv").append(id)
                    .append(") {\n");
                out.append(indent(indent + 1)).append("if (\"INT_CONVERT\".equals(__iv")
                    .append(id).append(".kind)) {\n");
                out.append(indent(indent + 2)).append(hostValue)
                    .append(" = JvmRuntime.intConv(").append(args).append(", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(declaredKind)
                    .append(", ").append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(originOf(op))).append(");\n");
                out.append(indent(indent + 1)).append("} else {\n");
                out.append(indent(indent + 2)).append(hostValue)
                    .append(" = JvmRuntime.numConv(").append(args).append(", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(declaredKind)
                    .append(", ").append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(originOf(op))).append(");\n");
                out.append(indent(indent + 1)).append("}\n");
                out.append(indent(indent)).append("} else if (").append(carrier)
                    .append(" instanceof JvmRuntime.StdlibFunctionValue) {\n");
            } else {
                out.append(indent(indent)).append("if (").append(carrier)
                    .append(" instanceof JvmRuntime.Intrinsic) {\n");
                emitDynamicCarrierFailure(op, carrier, indent + 1);
                out.append(indent(indent)).append("} else if (").append(carrier)
                    .append(" instanceof JvmRuntime.StdlibFunctionValue) {\n");
            }
            out.append(indent(indent + 1)).append(hostValue)
                .append(" = JvmRuntime.invokeStdlibCallable((JvmRuntime."
                    + "StdlibFunctionValue) ")
                .append(carrier).append(", ").append(javaString(op.kind().name()))
                .append(", ").append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(originOf(op))).append(", new Object[]{ ")
                .append(args).append(" });\n");
            out.append(indent(indent)).append("} else {\n");
            out.append(indent(indent + 1)).append(hostValue)
                .append(" = ((JvmRuntime.FunctionValue) ").append(carrier)
                .append(").fn.invoke(new Object[]{ ").append(args).append(" });\n");
            out.append(indent(indent)).append("}\n");
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) returnBoundary.payload();
            String checked = "__dhc" + id;
            emitBoundaryStart(returnBoundary, hostValue, boundaryPayload.descriptor(),
                indent);
            out.append(indent(indent)).append("Object ").append(checked).append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(checked)
                .append(" = ")
                .append(bcheckArgs(boundaryPayload.descriptor(), hostValue))
                .append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
            // The recorded cell's own origin replaces the check engine's
            // neutral one, exactly the Lua arm's `__chkB.o = <cell origin>`:
            // the pinned failure framing of a cataloged callee names the
            // call expression (K2/K15), and the oracle's recorded-cell run
            // carries the identical origin.
            out.append(indent(indent + 1))
                .append("JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                    + "__be.code, __be.msg, ")
                .append(javaString(originOf(returnBoundary)))
                .append(", __be.expected, __be.actual, __be.frames, null);\n");
            emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                "JvmRuntime.errtext(__bre)", indent + 1);
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__bre)", indent + 1);
            out.append(indent(indent + 1)).append("throw __bre;\n");
            out.append(indent(indent)).append("}\n");
            emitBoundarySuccess(returnBoundary, checked, boundaryPayload.descriptor(),
                indent);
            out.append(indent(indent)).append(result).append(" = ").append(checked)
                .append(";\n");
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
         * DEAL-body cell (ISSUE-0677; the oracle's {@code runBoundaryChild}
         * over the recorded cell): the same emission the parented boundary
         * cells use — the START event with the input's raw atom, the check
         * under the cell's own origin, the SUCCESS terminal with the admitted
         * value, and the cell's plus the invocation op's FAILURE events on a
         * failure. The cell is total on the admitted value (an identical
         * declared descriptor), so its check passes and only its boundary
         * events are observable.
         *
         * @param invocation  the dynamic invocation op; non-null
         * @param cell        the recorded call-owned cell; non-null
         * @param valueExpr   the emitted expression holding the returned value; non-null
         * @param checkedName the emitted local receiving the admitted value; non-null
         * @param indent      the emitted block's indentation depth; ≥0
         */
        private void emitRecordedCellRun(SemanticOp invocation, SemanticOp cell,
                                         String valueExpr, String checkedName, int indent) {
            emitFieldBoundaryCheck(invocation, cell, valueExpr, checkedName, indent);
            out.append(indent(indent)).append(valueExpr).append(" = ")
                .append(checkedName).append(";\n");
        }

        /**
         * The dynamic dispatch's fail-closed residue: a carrier whose
         * class is not resolvable at this boundary projects the pinned
         * E8001 {@code expected function} text with the carrier's actual
         * runtime kind at the call origin, emits the op's single FAILURE
         * terminal, and throws — nothing executes silently.
         */
        private void emitDynamicCarrierFailure(SemanticOp op, String carrierExpr,
                                               int indent) {
            String error = "__dy_" + op.opId().id();
            out.append(indent(indent)).append("JvmRuntime.DealError ").append(error)
                .append(" = JvmRuntime.fail(\"E8001\", \"expected function, got \""
                    + " + JvmRuntime.actualOf(\"function\", ").append(carrierExpr)
                .append("), ").append(javaString(originOf(op)))
                .append(", \"function\", JvmRuntime.actualOf(\"function\", ")
                .append(carrierExpr).append("));\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(" + error + ")", indent);
            out.append(indent(indent)).append("throw ").append(error).append(";\n");
        }

        /**
         * The dynamic {@code ASYNC_START} arm (ISSUE-0658; ISSUE-0678 for the
         * asynchronous host class;
         * {@code dynamic-call-shape-production-and-emission} Y4/Y5 and
         * the dynamic async start contract): the recorded parameter
         * cells ran above; a DEAL-body carrier starts the callee body
         * task under the callee's module context with the recorded task
         * cell (the body's own {@code RETURN} runs it) — a callee value of
         * another unit resolves its owning module through the carrier's
         * function id and runs its own body under that module context, the
         * emitter twin of the oracle's owning-unit body terminal; the adapter
         * class runs the landed D15 sequence and starts the source
         * class's task under the source's module context with the
         * leading-M recorded arguments (the source body task), with
         * zero caller-side return boundaries beyond the recorded task
         * cell — the oracle's {@code executeDynamicAdapterAsyncStart}; a
         * loaded host surface entry (a {@code FunctionValue} with no frame id)
         * starts the declared async export through the same host calling
         * convention and {@code ASYNC_OPERATION_HANDLE} terminal as the static
         * arm, with the operation handle bound to this token under the entry's
         * declared identity (the oracle's dynamic HOST resolution; zero
         * caller-side return cells). A shared-body/retained-ABI external
         * function value carries no value tag at all (M4: the identity channel
         * only), so a value-resolved external callee of another unit is the
         * DEAL-body class above — its own body under its own module context —
         * and the identity-channel external async link stays the landed static
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
                                           AsyncTokenId token, List<String> args,
                                           int indent) {
            String id = String.valueOf(op.opId().id());
            String carrier = "__dc" + id;
            // The recorded task cell's closed form (ISSUE-0677; design
            // source {@code function-typed-value-materialization-and-dispatch}
            // M6): a call-owned record executes in this caller-side task
            // wrapper before the token completes; a callee-owned record is
            // the resolved body's own cell and runs inside the body.
            SemanticOp recordedTaskCell = payload.returnBoundaryOpId() == null
                ? null : opsById.get(payload.returnBoundaryOpId());
            boolean callOwnedTaskCell = recordedTaskCell != null
                && callOwnedCell(recordedTaskCell);
            out.append(indent(indent)).append("Object ").append(carrier)
                .append(" = ").append(slot(callee.callee())).append(";\n");
            // ADAPTER: the landed D15 sequence resolves the source value
            // and checks its carried source spec; the source class then
            // starts its own task with the leading-M recorded arguments
            // (a DEAL-body source runs that body's own RETURN cell under
            // its module context, with zero caller-side return
            // boundaries).
            out.append(indent(indent)).append("if (").append(carrier)
                .append(" instanceof JvmRuntime.AdapterValue) {\n");
            String adapter = "__da" + id;
            String source = "__ds" + id;
            String sourceModule = "__dm" + id;
            out.append(indent(indent + 1)).append("JvmRuntime.AdapterValue ")
                .append(adapter).append(" = (JvmRuntime.AdapterValue) ")
                .append(carrier).append(";\n");
            out.append(indent(indent + 1)).append("Object ").append(source)
                .append(" = JvmRuntime.fnCheck(JvmRuntime.adapterSource(")
                .append(adapter).append("), ").append(adapter)
                .append(".sourceSpec, ").append(javaString(originOf(op)))
                .append(");\n");
            // The runtime adapter branch's intrinsic source (ISSUE-0680;
            // design source {@code conversion-intrinsic-function-values} J5):
            // the resolved source value is the memoized intrinsic carrier, so
            // the task is the closed DEAL_BODY task running the one conversion
            // ladder with this op's context and kind over the leading-M
            // recorded argument and completing immediately with the converted
            // value; the single AWAIT runs the landed ASYNC_COMPLETION cell.
            // Every other source value keeps the landed arms.
            out.append(indent(indent + 1)).append("if (").append(source)
                .append(" instanceof JvmRuntime.Intrinsic __ii").append(id)
                .append(") {\n");
            if (args.isEmpty()) {
                // The leading-M projection of the runtime intrinsic source has
                // no argument to convert (the intrinsic declares one
                // parameter): the carrier fails closed at the start origin.
                emitDynamicCarrierFailure(op, source, indent + 2);
            } else {
                out.append(indent(indent + 2)).append("JvmRuntime.startBodyTask(")
                    .append(token.tokenId()).append(", \"DEAL_BODY_TASK\", () -> ")
                    .append("\"INT_CONVERT\".equals(__ii").append(id)
                    .append(".kind) ? JvmRuntime.intConv(").append(args.get(0))
                    .append(", ").append(javaString(op.kind().name()))
                    .append(", \"number\", ").append(intrinsicContextArgs(op))
                    .append(") : JvmRuntime.numConv(").append(args.get(0)).append(", ")
                    .append(javaString(op.kind().name())).append(", \"int\", ")
                    .append(intrinsicContextArgs(op)).append("));\n");
            }
            out.append(indent(indent + 1)).append("} else {\n");
            out.append(indent(indent + 1)).append("if (!(").append(source)
                .append(" instanceof JvmRuntime.FunctionValue) || "
                    + "((JvmRuntime.FunctionValue) ").append(source)
                .append(").fid == null) {\n");
            emitDynamicCarrierFailure(op, source, indent + 2);
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("String ").append(sourceModule)
                .append(" = dealModuleOfFunction(((JvmRuntime.FunctionValue) ")
                .append(source).append(").fid);\n");
            out.append(indent(indent + 1)).append("if (").append(sourceModule)
                .append(" == null) {\n");
            emitDynamicCarrierFailure(op, source, indent + 2);
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("JvmRuntime.startBodyTask(")
                .append(token.tokenId()).append(", \"DEAL_BODY_TASK\", () -> {\n");
            out.append(indent(indent + 2)).append("String __prevM = "
                + "JvmRuntime.currentModule();\n");
            out.append(indent(indent + 2)).append("MODULE = ").append(sourceModule)
                .append(";\n");
            out.append(indent(indent + 2)).append("JvmRuntime.setModule(MODULE);\n");
            out.append(indent(indent + 2)).append("JvmRuntime.pushFrame("
                + "((JvmRuntime.FunctionValue) ").append(source).append(").fid);\n");
            out.append(indent(indent + 2)).append("try {\n");
            if (callOwnedTaskCell) {
                out.append(indent(indent + 3)).append("Object __dv").append(id)
                    .append(" = ")
                    .append("((JvmRuntime.FunctionValue) ").append(source)
                    .append(").fn.invoke(java.util.Arrays.copyOfRange(new Object[]{ ")
                    .append(String.join(", ", args)).append(" }, 0, ")
                    .append(adapter).append(".arity));\n");
                emitRecordedCellRun(op, recordedTaskCell, "__dv" + id, "__vc" + id,
                    indent + 3);
                out.append(indent(indent + 3)).append("return __dv").append(id)
                    .append(";\n");
            } else {
                out.append(indent(indent + 3)).append("return "
                    + "((JvmRuntime.FunctionValue) ").append(source)
                    .append(").fn.invoke(java.util.Arrays.copyOfRange(new Object[]{ ")
                    .append(String.join(", ", args)).append(" }, 0, ")
                    .append(adapter).append(".arity));\n");
            }
            out.append(indent(indent + 2)).append("} finally {\n");
            out.append(indent(indent + 3)).append("JvmRuntime.popFrame();\n");
            out.append(indent(indent + 3)).append("MODULE = __prevM;\n");
            out.append(indent(indent + 3)).append("JvmRuntime.setModule(__prevM);\n");
            out.append(indent(indent + 2)).append("}\n");
            out.append(indent(indent + 1)).append("});\n");
            out.append(indent(indent + 1)).append("}\n");
            // DEAL_BODY: the carrier's own invoker under the callee's
            // module; the frame and the module context are restored on
            // every path.
            out.append(indent(indent)).append("} else if (").append(carrier)
                .append(" instanceof JvmRuntime.FunctionValue ")
                .append("__fv").append(id).append(" && __fv").append(id)
                .append(".fid != null) {\n");
            String functionValue = "__fv" + id;
            out.append(indent(indent + 1)).append("String __fm").append(id)
                .append(" = dealModuleOfFunction(").append(functionValue)
                .append(".fid);\n");
            out.append(indent(indent + 1)).append("if (__fm").append(id)
                .append(" == null) {\n");
            emitDynamicCarrierFailure(op, carrier, indent + 2);
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("JvmRuntime.startBodyTask(")
                .append(token.tokenId()).append(", \"DEAL_BODY_TASK\", () -> {\n");
            out.append(indent(indent + 2)).append("String __prevM = "
                + "JvmRuntime.currentModule();\n");
            out.append(indent(indent + 2)).append("MODULE = __fm").append(id)
                .append(";\n");
            out.append(indent(indent + 2)).append("JvmRuntime.setModule(MODULE);\n");
            out.append(indent(indent + 2)).append("JvmRuntime.pushFrame(")
                .append(functionValue).append(".fid);\n");
            out.append(indent(indent + 2)).append("try {\n");
            if (callOwnedTaskCell) {
                out.append(indent(indent + 3)).append("Object __dv").append(id)
                    .append(" = ").append(functionValue)
                    .append(".fn.invoke(new Object[]{ ").append(String.join(", ", args))
                    .append(" });\n");
                emitRecordedCellRun(op, recordedTaskCell, "__dv" + id, "__vc" + id,
                    indent + 3);
                out.append(indent(indent + 3)).append("return __dv").append(id)
                    .append(";\n");
            } else {
                out.append(indent(indent + 3)).append("return ")
                    .append(functionValue)
                    .append(".fn.invoke(new Object[]{ ")
                    .append(String.join(", ", args)).append(" });\n");
            }
            out.append(indent(indent + 2)).append("} finally {\n");
            out.append(indent(indent + 3)).append("JvmRuntime.popFrame();\n");
            out.append(indent(indent + 3)).append("MODULE = __prevM;\n");
            out.append(indent(indent + 3)).append("JvmRuntime.setModule(__prevM);\n");
            out.append(indent(indent + 2)).append("}\n");
            out.append(indent(indent + 1)).append("});\n");
            // HOST: the carrier is a loaded host surface entry, so the declared
            // host export's async start runs through the same host calling
            // convention and the same ASYNC_OPERATION_HANDLE terminal as the
            // static arm — the loaded wrapper's declared-async shape check
            // inside the emitted wrapper, the operation handle bound to this
            // token under the declared identity's operation label (the same
            // label the oracle's dynamic HOST resolution derives from the
            // binding). The declared identity is the carrier's own
            // identity-indexed home in the program's export-surface registry; a
            // carrier with no unique home (never a loaded surface entry) fails
            // closed.
            out.append(indent(indent)).append("} else if (").append(carrier)
                .append(" instanceof JvmRuntime.FunctionValue __hv").append(id)
                .append(" && __hv").append(id).append(".fid == null")
                .append(" && !(").append(carrier)
                .append(" instanceof JvmRuntime.StdlibFunctionValue)) {\n");
            String hostName = "__hn" + id;
            String hostLabel = "__hl" + id;
            String hostHandle = "__hh" + id;
            out.append(indent(indent + 1)).append("String[] ").append(hostName)
                .append(" = JvmRuntime.surfaceNameOf(").append(carrier).append(");\n");
            out.append(indent(indent + 1)).append("if (").append(hostName)
                .append(" == null) {\n");
            emitDynamicCarrierFailure(op, carrier, indent + 2);
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("String ").append(hostLabel)
                .append(" = ").append(hostName).append("[0] + \".\" + ")
                .append(hostName).append("[1];\n");
            out.append(indent(indent + 1))
                .append("JvmRuntime.effect(\"ASYNC_START_OP\", ").append(hostLabel)
                .append(");\n");
            out.append(indent(indent + 1)).append("Object ").append(hostHandle)
                .append(";\n");
            out.append(indent(indent + 1)).append("try {\n");
            out.append(indent(indent + 2)).append(hostHandle).append(" = ")
                .append("((JvmRuntime.FunctionValue) ").append(carrier)
                .append(").fn.invoke(new Object[]{ ").append(String.join(", ", args))
                .append(" });\n");
            out.append(indent(indent + 1)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__e)", indent + 2);
            out.append(indent(indent + 2)).append("throw __e;\n");
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("JvmRuntime.startHostTask(")
                .append(token.tokenId()).append(", ").append(hostLabel).append(", ")
                .append(hostHandle).append(");\n");
            // The fail-closed residue: no class is resolvable.
            out.append(indent(indent)).append("} else {\n");
            emitDynamicCarrierFailure(op, carrier, indent + 1);
            out.append(indent(indent)).append("}\n");
        }
        /**
         * The sync host call arm (ISSUE-0651;
         * {@code host-module-load-and-host-call-realization} H3/H7 and the
         * sync host call contract): every declared parameter cell runs in
         * one-based order through the emitted host-check seam (the same
         * rule the wrapper's own cell runs, so the pinned E8010
         * {@code parameter {i} type mismatch} projection surfaces at the
         * call origin), each checked value is projected into its declared
         * host-facing carrier (H7: the per-signature function bridge, the
         * declared element-shape array carrier), the emitted per-export
         * wrapper is invoked with the import's origin triple, and the
         * declared return value is projected back into the production
         * value carriers. The wrapper is the single check authority for
         * the host cells: this arm runs no generic descriptor-kind check
         * on the DEAL_TO_HOST/HOST_TO_DEAL cells. A declared array
         * parameter's host element writes are copied back into the
         * production array only after a normal return (a failed call
         * copies nothing back). A DEAL error the host raises propagates
         * unchanged.
         */
        private void emitHostCall(SemanticOp op, KindPayload.CallPayload payload,
                ModuleId hostModuleId, String exportName, int indent) {
            // The cataloged-callable sub-class (ISSUE-0678; K2): the read's own
            // registration of a spec-stdlib declared function exports resolves
            // the closed catalog row, so the invocation is the row's one invoker
            // with the invoking call's own context — never a loaded surface entry
            // and never a host responder. The recorded HOST cell family runs
            // exactly as the landed host arm's does.
            StdlibFunctionCatalog.Entry catalogRow = StdlibFunctionCatalog
                .lookup(hostModuleId.path(), exportName).orElse(null);
            if (catalogRow != null) {
                emitStdlibCalleeCall(op, payload, catalogRow, indent);
                return;
            }
            if (hostAbi == null) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " resolves the host export '" + hostModuleId.path() + "."
                    + exportName + "' but the session carries no host ABI"
                    + " emission surface (a producer defect; only the"
                    + " production project entry carries the compile's"
                    + " declaration surface)");
            }
            String wrapper = hostAbi.requireWrapper(hostModuleId.path(), exportName);
            Type.Func declared = hostAbi.declaredFunction(hostModuleId.path(),
                exportName);
            HostCallArguments arguments = emitHostArguments(op, payload, declared, indent);
            StringBuilder call = new StringBuilder(wrapper).append('(');
            for (String projected : arguments.projected()) {
                call.append(projected).append(", ");
            }
            call.append(originArgs(op)).append(')');
            finishHostCall(op, payload, declared, arguments, call.toString(), true,
                indent);
        }

        /**
         * The cataloged-callable static arm: the read's own registration used as
         * a call callee (the static/indirect arm) resolved the closed catalog
         * row, so the declared parameter cells run through the emitted host-check
         * seam (the landed host cell family and its pinned E8010 texts), the row's
         * one invoker runs with the invoking call's own context, and the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell admits the result at
         * the call origin — one algorithm authority with the direct
         * {@code STDLIB_CALL} arm, exactly the oracle's cataloged branch of
         * {@code invokeResolvedHostRequest}.
         *
         * <p>The argument domain is the recorded {@code HOST_PARAMETER} cells'
         * checked values: the closed catalog rows declare non-nullable
         * scalar/table parameter positions only, for which the host-facing
         * projection is the identity — a nullable, function, or class position is
         * a fail-closed producer defect, never a silently projected argument.</p>
         */
        private void emitStdlibCalleeCall(SemanticOp op, KindPayload.CallPayload payload,
                StdlibFunctionCatalog.Entry row, int indent) {
            List<String> checked = new ArrayList<>();
            int index = 1;
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                RuntimeDescriptor descriptor = boundaryPayload.descriptor();
                if (descriptor instanceof RuntimeDescriptor.Nullable
                        || descriptor instanceof RuntimeDescriptor.Class
                        || descriptor instanceof RuntimeDescriptor.Func) {
                    throw new IllegalStateException("the cataloged callable '"
                        + row.declaredDescriptor().canonicalSpecText() + "' arrives at "
                        + op.opId() + " with the parameter position "
                        + descriptor.canonicalSpecText() + ", whose host-facing "
                        + "projection is not the identity — a producer defect");
                }
                String input = slot(boundaryPayload.input());
                emitBoundaryStart(boundary, input, descriptor, indent);
                String name = "__sp_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(name).append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent + 1)).append(name)
                    .append(" = __hostParamCheck(").append(index).append(", ")
                    .append(javaString(descriptorText(descriptor))).append(", ")
                    .append(input).append(", ").append(originArgs(op)).append(");\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__be)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__be)", indent + 1);
                out.append(indent(indent + 1)).append("throw __be;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, name, descriptor, indent);
                checked.add(name);
                index++;
            }
            String result = "__sc_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(result)
                .append(" = JvmRuntime.invokeStdlibCallable(JvmRuntime.stdlibCallable(")
                .append(stdlibRowArgs(row)).append("), ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(originOf(op))).append(", new Object[]{ ")
                .append(String.join(", ", checked)).append(" });\n");
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null ? null
                : opsById.get(payload.returnBoundaryOpId());
            if (returnBoundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                emitBoundaryStart(returnBoundary, result, boundaryPayload.descriptor(),
                    indent);
                String admitted = "__sr_" + op.opId().id();
                out.append(indent(indent)).append("Object ").append(admitted).append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent + 1)).append(admitted).append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), result))
                    .append(";\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                // The cataloged result's terminal is the descriptor-kind
                // projection of the direct STDLIB_RETURN boundary (the int
                // ladder's pinned E8004 included), never the recorded host
                // cell's HOST_SYNC_RETURN row; the cell's own origin
                // replaces the check engine's neutral one.
                out.append(indent(indent + 1))
                    .append("JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(returnBoundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                out.append(indent(indent + 1)).append("throw __bre;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(returnBoundary, admitted,
                    boundaryPayload.descriptor(), indent);
                result = admitted;
            }
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(result).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The conversion intrinsic's value call (ISSUE-0679; design source
         * {@code conversion-intrinsic-function-values} J3/J4): the seeded
         * identity's registration is a boundary-shaped callable, so the
         * indirect arm runs exactly the recorded host cell family — one
         * {@code DEAL_TO_HOST} + {@code HOST_PARAMETER} cell per declared
         * parameter through the emitted host-check seam (the argument domain
         * the cells own; a null or wrong-kind argument is a parameter-cell
         * projection) — then the one conversion ladder
         * ({@code JvmRuntime.intConv}/{@code numConv}) with the invoking CALL
         * op's own context and kind label, then the recorded
         * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell at the call
         * origin. One algorithm authority with the direct
         * {@code INTRINSIC_CALL} arm, whose kind label stays its own.
         */
        private void emitIntrinsicValueCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.IntrinsicFunction intrinsic, int indent) {
            List<String> checked = new ArrayList<>();
            int index = 1;
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                RuntimeDescriptor descriptor = boundaryPayload.descriptor();
                if (descriptor instanceof RuntimeDescriptor.Nullable
                        || descriptor instanceof RuntimeDescriptor.Class
                        || descriptor instanceof RuntimeDescriptor.Func) {
                    throw new IllegalStateException("the conversion intrinsic '"
                        + intrinsic.kind() + "' arrives at " + op.opId()
                        + " with the parameter position "
                        + descriptor.canonicalSpecText() + ", whose host-facing "
                        + "projection is not the identity — a producer defect");
                }
                String input = slot(boundaryPayload.input());
                emitBoundaryStart(boundary, input, descriptor, indent);
                String name = "__ip_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(name).append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent + 1)).append(name)
                    .append(" = __hostParamCheck(").append(index).append(", ")
                    .append(javaString(descriptorText(descriptor))).append(", ")
                    .append(input).append(", ").append(originArgs(op)).append(");\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__be)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__be)", indent + 1);
                out.append(indent(indent + 1)).append("throw __be;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, name, descriptor, indent);
                checked.add(name);
                index++;
            }
            if (checked.size() != intrinsic.descriptor().paramTypes().size()) {
                throw new IllegalStateException("the conversion intrinsic call "
                    + op.opId() + " records " + checked.size() + " parameter cell(s) for "
                    + "the '" + intrinsic.kind() + "' intrinsic's "
                    + intrinsic.descriptor().paramTypes().size() + " declared "
                    + "parameter(s) (a producer defect)");
            }
            // The one conversion ladder at the call site: the invoking CALL op's
            // context, origin, and kind label (the pinned conversion texts and
            // the FAILURE event carry the invoking op).
            String result = "__ic_" + op.opId().id();
            String helper = intrinsic.kind() == IntrinsicKind.INT_CONVERT
                ? "JvmRuntime.intConv" : "JvmRuntime.numConv";
            out.append(indent(indent)).append("Object ").append(result).append(" = ")
                .append(helper).append("(")
                .append(String.join(", ", checked)).append(", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(staticKind(
                    intrinsic.descriptor().paramTypes().get(0)))).append(", ")
                .append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(originOf(op))).append(");\n");
            // The recorded HOST_TO_DEAL + HOST_SYNC_RETURN cell, run by the call
            // op exactly once per invocation.
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null ? null
                : opsById.get(payload.returnBoundaryOpId());
            if (returnBoundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                emitBoundaryStart(returnBoundary, result, boundaryPayload.descriptor(),
                    indent);
                String admitted = "__iac_" + op.opId().id();
                out.append(indent(indent)).append("Object ").append(admitted)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent + 1)).append(admitted).append(" = __hostCheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ").append(result).append(", false, ")
                    .append(originArgs(op)).append(");\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                    "JvmRuntime.errtext(__be)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__be)", indent + 1);
                out.append(indent(indent + 1)).append("throw __be;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(returnBoundary, admitted,
                    boundaryPayload.descriptor(), indent);
                result = admitted;
            }
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(result).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
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
         * {@code JvmRuntime.invokeAdapter} protocol.
         */
        private IntrinsicKind adapterIntrinsicKind(
                FunctionExecutionBinding.AdapterBinding adapter) {
            if (!(adapter.sourceRef() instanceof AdaptSourceRef.Value value)) {
                return null;
            }
            return intrinsicKindOf(value.value());
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
         * records.
         */
        private void emitAdapterOverIntrinsicRun(SemanticOp op,
                KindPayload.CallPayload payload,
                FunctionExecutionBinding.AdapterBinding adapter, int indent) {
            IntrinsicKind kind = adapterIntrinsicKind(adapter);
            if (kind == null) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " records an adapter whose source is not the seeded intrinsic "
                    + "identity (producer defect)");
            }
            RuntimeDescriptor.Func declared = kind.declaredSignature();
            String adapterSlot = slot((ValueId) opsById.get(adapter.adaptOpId()).result());
            // The source-signature check runs under the call op's FAILURE
            // terminal (the landed adapter arm's discipline): a source-signature
            // failure has no ladder event of its own, so the CALL op publishes
            // it and propagates the identical error value. The conversion's own
            // failure event already carries the invoking CALL op's key and kind
            // (J4), so it is not duplicated here.
            String source = "__ais" + op.opId().id();
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append("Object ").append(source)
                .append(" = JvmRuntime.fnCheck(JvmRuntime.adapterSource("
                    + "(JvmRuntime.AdapterValue) ")
                .append(adapterSlot).append("), ")
                .append(javaString(adapter.sourceSignature().canonicalSpecText()))
                .append(", ").append(javaString(originOf(op))).append(");\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__e)", indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("}\n");
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
            String helper = kind == IntrinsicKind.INT_CONVERT
                ? "JvmRuntime.intConv" : "JvmRuntime.numConv";
            String converted = "__aiv" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(converted)
                .append(" = ").append(helper).append("(").append(input).append(", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(staticKind(declared.paramTypes().get(0))))
                .append(", ").append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(originOf(op))).append(");\n");
            // The recorded HOST_TO_DEAL + HOST_SYNC_RETURN cell, run by the
            // call op exactly once per invocation (the source class HOST).
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null ? null
                : opsById.get(payload.returnBoundaryOpId());
            String admitted = emitHostCellRun(op, returnBoundary, converted, indent);
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(admitted).append(";\n");
        }

        /**
         * One recorded {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} cell
         * run by the invoking call op (ISSUE-0680; the landed intrinsic
         * value-call return cell's shared form): the boundary START, the
         * host-check seam over the cell's declared descriptor, the boundary
         * FAILURE with the call op's own terminal on a check failure, and
         * the boundary SUCCESS. Returns the expression holding the admitted
         * value (the input expression when the op records no cell).
         */
        private String emitHostCellRun(SemanticOp op, SemanticOp returnBoundary,
                                       String valueExpr, int indent) {
            if (returnBoundary == null) {
                return valueExpr;
            }
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) returnBoundary.payload();
            emitBoundaryStart(returnBoundary, valueExpr, boundaryPayload.descriptor(),
                indent);
            String admitted = "__iacc_" + returnBoundary.opId().id();
            out.append(indent(indent)).append("Object ").append(admitted)
                .append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(admitted).append(" = __hostCheck(")
                .append(javaString(descriptorText(boundaryPayload.descriptor())))
                .append(", ").append(valueExpr).append(", false, ")
                .append(originArgs(op)).append(");\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
            emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                "JvmRuntime.errtext(__be)", indent + 1);
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__be)", indent + 1);
            out.append(indent(indent + 1)).append("throw __be;\n");
            out.append(indent(indent)).append("}\n");
            emitBoundarySuccess(returnBoundary, admitted,
                boundaryPayload.descriptor(), indent);
            return admitted;
        }

        /**
         * The {@code HostFunctionValue} indirect call arm: the value
         * materialized at its producing host crossing ({@code
         * host-module-load-and-host-call-realization} H3/H5/H7) is
         * invoked through the production function carrier the crossing's
         * declared-return projection published, with the same declared
         * parameter cells and the pinned E8010 texts at the call origin.
         */
        private void emitHostValueCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.HostFunctionValue hostValue, int indent) {
            if (hostAbi == null) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " resolves the host-materialized function value of module '"
                    + hostValue.hostModuleId().path() + "' but the session carries"
                    + " no host ABI emission surface (a producer defect)");
            }
            Type.Func declared = hostAbi.declaredFunctionValue(
                hostValue.descriptor().canonicalSpecText());
            SemanticOp crossing = opsById.get(hostValue.materializingBoundaryOpId());
            if (crossing == null
                    || !(crossing.payload() instanceof KindPayload.BoundaryPayload boundary)) {
                throw new IllegalStateException("CALL " + op.opId()
                    + " names the materializing host crossing "
                    + hostValue.materializingBoundaryOpId()
                    + ", which is not a boundary op of the emitted closure"
                    + " (a producer defect)");
            }
            String value = slot(boundary.input());
            HostCallArguments arguments = emitHostArguments(op, payload, declared, indent);
            StringBuilder call = new StringBuilder("((JvmRuntime.FunctionValue) ")
                .append(value).append(").fn.invoke(new java.lang.Object[]{ ");
            for (int i = 0; i < arguments.projected().size(); i++) {
                if (i > 0) {
                    call.append(", ");
                }
                call.append(arguments.projected().get(i));
            }
            call.append(" })");
            finishHostCall(op, payload, declared, arguments, call.toString(), false,
                indent);
        }

        /** The projected argument names, array carriers, and array parameters of one host call. */
        private record HostCallArguments(List<String> projected, List<String> carriers,
            List<String> arrays, List<String> arrayCarriers) {
        }

        /**
         * The declared parameter cells of one host call: one-based order,
         * each cell through the emitted host-check seam with the pinned
         * E8010 projection at the call origin, then the host-facing
         * crossing projection (H7).
         */
        private HostCallArguments emitHostArguments(SemanticOp op,
                KindPayload.CallPayload payload, Type.Func declared, int indent) {
            List<String> projected = new ArrayList<>();
            List<String> carriers = new ArrayList<>();
            List<String> arrays = new ArrayList<>();
            List<String> arrayCarriers = new ArrayList<>();
            int index = 1;
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String input = slot(boundaryPayload.input());
                Type declaredParameter = index - 1 < declared.paramTypes().size()
                    ? declared.paramTypes().get(index - 1) : null;
                String desc = declaredParameter == null
                    ? boundaryPayload.descriptor().canonicalSpecText()
                    : JvmHostAbiEmission.descriptorText(declaredParameter);
                emitBoundaryStart(boundary, input, boundaryPayload.descriptor(), indent);
                String checked = "__hp_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(checked)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(checked)
                    .append(" = __hostParamCheck(").append(index).append(", ")
                    .append(javaString(desc)).append(", ").append(input)
                    .append(", ").append(originArgs(op)).append(");\n");
                out.append(indent(indent))
                    .append("} catch (JvmRuntime.DealError __be) {\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__be)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__be)", indent + 1);
                out.append(indent(indent)).append("  throw __be;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor(),
                    indent);
                String value = "__hq_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(value)
                    .append(" = __hostProjectArg(").append(javaString(desc))
                    .append(", ").append(checked).append(");\n");
                projected.add(value);
                if (declaredParameter != null
                        && innerOf(declaredParameter) instanceof Type.Array) {
                    // The copy-back target is the production array the
                    // crossing materialized the carrier from, and the source
                    // is the projected carrier the host method received.
                    arrays.add(checked);
                    carriers.add(desc);
                    arrayCarriers.add(value);
                }
                index++;
            }
            return new HostCallArguments(List.copyOf(projected), List.copyOf(carriers),
                List.copyOf(arrays), List.copyOf(arrayCarriers));
        }

        /**
         * The call half of one host arm: the invocation under the op's
         * FAILURE events, the declared return value's production
         * projection, the normal-return copy-back of the declared array
         * parameters, and the return boundary's events.
         */
        private void finishHostCall(SemanticOp op, KindPayload.CallPayload payload,
                Type.Func declared, HostCallArguments arguments, String invocation,
                boolean targetChecksReturn, int indent) {
            Type declaredReturn = declared.returnType();
            String result = "__hr_" + op.opId().id();
            String call = targetChecksReturn ? invocation
                : "__hostCheck("
                    + javaString(JvmHostAbiEmission.descriptorText(declaredReturn))
                    + ", " + invocation + ", false, " + originArgs(op) + ")";
            if (declaredReturn instanceof Type.Null) {
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(call).append(";\n");
                emitHostCallCatch(op, payload, indent);
                out.append(indent(indent)).append("Object ").append(result)
                    .append(" = null;\n");
            } else {
                // The direct host arm assigns the emitted wrapper's
                // declared return carrier; the HostFunctionValue arm
                // assigns the emitted host-check seam's java.lang.Object
                // result (the wrapper is not involved), so the held slot
                // is Object there and the checked value is reconciled
                // with the declared production carrier after the seam.
                String carrier = targetChecksReturn
                        && !hostAbi.needsReturnProjection(declaredReturn)
                    ? hostAbi.carrierType(declaredReturn,
                        declaredReturn instanceof Type.Nullable)
                    : "java.lang.Object";
                String held = "__hw_" + op.opId().id();
                out.append(indent(indent)).append(carrier).append(" ").append(held)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(held).append(" = ")
                    .append(call).append(";\n");
                emitHostCallCatch(op, payload, indent);
                out.append(indent(indent)).append("Object ").append(result)
                    .append(" = ").append(targetChecksReturn
                        ? productionValueOf(declaredReturn, held)
                        : checkedResultOf(declaredReturn, held))
                    .append(";\n");
            }
            for (int i = 0; i < arguments.arrays().size(); i++) {
                out.append(indent(indent)).append("__hostArrayCopyBack(")
                    .append(javaString(arguments.carriers().get(i))).append(", ")
                    .append(arguments.arrayCarriers().get(i))
                    .append(", (JvmRuntime.Array) ")
                    .append(arguments.arrays().get(i)).append(");\n");
            }
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null ? null
                : opsById.get(payload.returnBoundaryOpId());
            if (returnBoundary != null) {
                // The return boundary's event pair runs for every declared
                // return position, a declared null included (the oracle's
                // return cell emits the same pair over the language null),
                // so the differential comparison stays event-for-event.
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                emitBoundaryStart(returnBoundary, result,
                    boundaryPayload.descriptor(), indent);
                emitBoundarySuccess(returnBoundary, result,
                    boundaryPayload.descriptor(), indent);
            }
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(result).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The catch half of one host call: the op FAILURE (and, for the
         * wrapper's declared-return cell, the return boundary's FAILURE)
         * with the wrapper's own error, then the identical rethrow — a
         * DEAL error the host raises propagates unchanged.
         */
        private void emitHostCallCatch(SemanticOp op, KindPayload.CallPayload payload,
                int indent) {
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            SemanticOp returnBoundary = payload.returnBoundaryOpId() == null ? null
                : opsById.get(payload.returnBoundaryOpId());
            if (returnBoundary != null) {
                out.append(indent(indent)).append("  if (\"E8010\".equals(__e.code)"
                    + " && __e.msg != null && __e.msg.startsWith(\"return value 1"
                    + " type mismatch\")) {\n");
                emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                    "JvmRuntime.errtext(__e)", indent + 2);
                out.append(indent(indent)).append("  }\n");
            }
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__e)", indent + 1);
            out.append(indent(indent)).append("  throw __e;\n");
            out.append(indent(indent)).append("}\n");
        }

        /** The declared inner type of one position (nullable unwrapped). */
        private static Type innerOf(Type type) {
            return type instanceof Type.Nullable nullable ? nullable.inner() : type;
        }

        /**
         * The production projection of one checked host return held as
         * the host-check seam's {@code java.lang.Object} result (the
         * {@code HostFunctionValue} indirect and callback arms; H3/H7):
         * the declared carrier is reconciled with the production value
         * carrier — a numeric or boolean position unboxes through its
         * boxed form (a {@code null}-safe form for a {@code ?} position),
         * a declared array or function return crosses back into the
         * production carriers through the host-to-DEAL projection, and
         * every other reference carrier is the production value itself.
         */

        /** The origin-argument triplet of a wrapper invocation. */
        private String originArgs(SemanticOp op) {
            SourceSpan span = op.origin().span();
            if (span == null) {
                return "\"-\", 0, 0";
            }
            return javaString(op.origin().sourceId()) + ", " + span.startLine()
                + ", " + span.startColumn();
        }

        /**
         * The conversion ladder's invoking-op context arguments (ISSUE-0679
         * J4): the op key, the contract digest, the parent key, and the
         * origin — one algorithm authority with the direct
         * {@code INTRINSIC_CALL} arm and the static intrinsic value call.
         */
        private String intrinsicContextArgs(SemanticOp op) {
            return javaString(opKey(op.opId())) + ", "
                + javaString(op.contract().canonicalDigest()) + ", "
                + javaString(parentKey(op.origin().parentOpId())) + ", "
                + javaString(originOf(op));
        }

        /**
         * CLASS_NEW (E5, D16 construction order): provided values
         * completed before the op; default application in declaration
         * order (LOCAL through the detached class-default methods, or the
         * owner's CLASS_FACTORY transfer with the factory's events
         * parented to this caller op — the cross-unit K-D12 parent);
         * extra-key rejection first in provided-source order (E8007 at
         * the op origin); provided-field application and field validation
         * in declaration order through the boundary children; the
         * instance is tagged with its canonical class identity last.
         * Zero return boundaries; a failure publishes no partial
         * instance.
         */
        private void emitClassNew(SemanticOp op, int indent) {
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) op.payload();
            emitStart(op, indent);
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
                // The host declaration class's registered layout
                // (ISSUE-0624; K10): the payload carries exactly the project
                // lowering's registration-seed layout (the validator checks
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
                case LOCAL -> emitClassNewLocalDefaults(op, payload, provided, indent);
                case SHARED_FACTORY -> emitClassNewFactoryTransfer(op, payload, provided,
                    indent);
                case HOST_DEFAULTS -> {
                    // The host declaration class construction (ISSUE-0624;
                    // K10 and the K10 contract): dispatched after the static
                    // extra-key scan below — the shape carries no default
                    // children and no factory transfer, and its phases run
                    // through the loaded <C>_defaults capture and the
                    // synthesized host record.
                }
                case FFI_PLAN ->
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " carries defaultOwner " + payload.defaultOwner()
                        + ": the extern-C C-struct construction is the FFI"
                        + " child's and is not emitted here — a fail-closed"
                        + " producer defect, never emitted");
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
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                if (fieldOf(layout, field.name()) == null) {
                    String errName = "__ee_" + op.opId().id() + "_"
                        + Integer.toHexString(field.name().hashCode() & 0x7fffffff);
                    // The static extra-key check always fires at this
                    // site (the emitter proves the name is outside the
                    // layout); the constant guard keeps the trailing
                    // instance build reachable for javac.
                    out.append(indent(indent)).append("if (true) {\n");
                    out.append(indent(indent)).append("  JvmRuntime.DealError ")
                        .append(errName)
                        .append(" = new JvmRuntime.DealError(")
                        .append(javaString("E8007")).append(", ")
                        .append(javaString("extra field '" + field.name()
                            + "' in class '" + payload.classId().text() + "'"))
                        .append(", ").append(javaString(originOf(op)))
                        .append(", null, null, JvmRuntime.framesText(), null);\n");
                    if (trace) {
                        emitFailureEvent(op.opId(), op.kind().name(), op,
                            "JvmRuntime.errtext(" + errName + ")", indent + 1);
                    }
                    out.append(indent(indent)).append("  throw ").append(errName)
                        .append(";\n");
                    out.append(indent(indent)).append("}\n");
                }
            }
            if (payload.defaultOwner() == DefaultOwner.BUILTIN_DEFAULTS) {
                emitClassNewBuiltinDefaults(op, payload, layout, indent);
                return;
            }
            if (payload.defaultOwner() == DefaultOwner.HOST_DEFAULTS) {
                emitClassNewHostDefaults(op, payload, indent);
                return;
            }
            // K-D4 steps 4-5: instance building plus field validation in
            // declaration order; the tag and the publication come last
            // (step 6).
            String carrier = carrierName(payload.classId());
            String instName = "__inst_" + op.opId().id();
            out.append(indent(indent)).append(carrier).append(' ').append(instName)
                .append(" = new ").append(carrier).append("();\n");
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
                    String extracted = "__ft_" + boundary.opId().id();
                    out.append(indent(indent)).append("Object ").append(extracted)
                        .append(" = ((").append("JvmRuntime.ClassInstance) ")
                        .append(slot((ValueId) factoryOp.result())).append(").read(")
                        .append(javaString(entry.field())).append(");\n");
                    inputExpr = extracted;
                } else {
                    inputExpr = slot(boundaryPayload.input());
                }
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor(), indent);
                String checked = "__c_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(checked)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(checked)
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), inputExpr))
                    .append(";\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("  JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("  throw __bre;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor(), indent);
                out.append(indent(indent)).append(instName).append('.')
                    .append(fieldSlot(entry.field())).append(" = ").append(checked)
                    .append(";\n");
                out.append(indent(indent)).append(instName).append('.')
                    .append(fieldFlag(entry.field())).append(" = true;\n");
            }
            // K-D4 step 6: the tag is the carrier's class identity (the
            // generated class carries it by construction), then the
            // publication.
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = ").append(instName).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The builtin {@code Error} construction (ISSUE-0619;
         * {@code semantic-ir-construct-coverage-cutover} K13 items 4/7):
         * the provided fields run their pinned {@code CLASS_LITERAL_FIELD}
         * boundary children in payload order (the descriptor-kind rule, the
         * field's declared {@code string} descriptor), the omitted fields
         * take the compiler constant empty string, and the publication is
         * {@code new JvmRuntime.ErrorValue(&lt;code&gt;, &lt;message&gt;)} —
         * the canonical carrier {@code THROW}, the catch reification,
         * {@code bcheck("@/Error")}, and {@code actualOf} already speak.
         * No default child, no factory transfer, and no extra-key
         * projection (the checker's E4002 rejects an extra literal field
         * before lowering).
         */
        private void emitClassNewBuiltinDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, ClassLayout layout, int indent) {
            if (!ClassId.ERROR.equals(payload.classId())
                    || !layout.equals(ClassLayout.BUILTIN_ERROR)) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner BUILTIN_DEFAULTS for " + payload.classId()
                    + " over " + layout.classId() + ": the builtin-defaults owner is"
                    + " admissible only for the compiler-owned builtin Error class"
                    + " (producer defect)");
            }
            String code = null;
            String message = null;
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
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor(), indent);
                String checked = "__ec_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(checked)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(checked)
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), inputExpr))
                    .append(";\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("  JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__bre)", indent + 1);
                out.append(indent(indent)).append("  throw __bre;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor(), indent);
                if ("code".equals(entry.field())) {
                    code = checked;
                } else if ("message".equals(entry.field())) {
                    message = checked;
                } else {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " names the builtin Error field '" + entry.field() + "':"
                        + " the builtin class declares exactly code and message —"
                        + " a fail-closed producer defect, never emitted");
                }
            }
            String instName = "__inst_" + op.opId().id();
            out.append(indent(indent)).append("JvmRuntime.ErrorValue ")
                .append(instName).append(" = new JvmRuntime.ErrorValue(")
                .append(code == null ? javaString("") : "(String) " + code)
                .append(", ")
                .append(message == null ? javaString("") : "(String) " + message)
                .append(");\n");
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = ").append(instName).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The host declaration class construction (ISSUE-0624;
         * {@code semantic-ir-construct-coverage-cutover} K10 and the K10
         * contract): the provided values complete in literal order before
         * the op (already-completed operands), the extra provided name the
         * load-time-captured {@code <C>_defaults} map does not carry raises
         * E8007 at the literal origin before any field validation, the
         * pinned {@code CLASS_LITERAL_FIELD} boundary children run in
         * declaration order, an omitted required-present field takes the
         * loaded default (the fail-closed E8001 when the loaded map carries
         * none), an omitted optional field stays absent, and the published
         * value is the synthesized {@code $DealRt} host record tagged with
         * the canonical class identity — the record the deployed host
         * implementation reads directly. A failed construction publishes no
         * instance.
         */
        private void emitClassNewHostDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, int indent) {
            JvmHostAbiEmission.HostClassFacts facts = hostAbi == null ? null
                : hostAbi.hostClassFacts(payload.classId());
            if (facts == null) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner HOST_DEFAULTS for " + payload.classId()
                    + ", which is not a declared host class of the compile's"
                    + " declaration surface (the class defaults capture has exactly"
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
            // K-D4 step 3: the extra-key rejection first in provided-source
            // order against the loaded defaults capture (the accepted-key
            // authority), after the operand completion and before any field
            // validation.
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                out.append(indent(indent)).append("if (!").append(facts.defaultsField())
                    .append(".containsKey(").append(javaString(field.name()))
                    .append(")) {\n");
                String errName = "__eh_" + op.opId().id() + "_"
                    + Integer.toHexString(field.name().hashCode() & 0x7fffffff);
                out.append(indent(indent)).append("  JvmRuntime.DealError ")
                    .append(errName).append(" = new JvmRuntime.DealError(")
                    .append(javaString("E8007")).append(", ")
                    .append(javaString("extra field '" + field.name()
                        + "' in class '" + payload.classId().text() + "'"))
                    .append(", ").append(javaString(originOf(op)))
                    .append(", null, null, JvmRuntime.framesText(), null);\n");
                if (trace) {
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(" + errName + ")", indent + 1);
                }
                out.append(indent(indent)).append("  throw ").append(errName)
                    .append(";\n");
                out.append(indent(indent)).append("}\n");
            }
            // K-D4 step 5: the pinned CLASS_LITERAL_FIELD boundary children
            // in declaration order; the admitted value is the one the record
            // carries.
            java.util.Map<String, String> checked = new java.util.LinkedHashMap<>();
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
                emitBoundaryStart(boundary, inputExpr, boundaryPayload.descriptor(), indent);
                String checkedName = "__hc_" + boundary.opId().id();
                out.append(indent(indent)).append("Object ").append(checkedName)
                    .append(";\n");
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent)).append("  ").append(checkedName)
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), inputExpr))
                    .append(";\n");
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("  JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("  throw __bre;\n");
                out.append(indent(indent)).append("}\n");
                emitBoundarySuccess(boundary, checkedName, boundaryPayload.descriptor(),
                    indent);
                checked.put(entry.field(), checkedName);
            }
            // Phases 2-5: the record in field declaration order — provided
            // fields with their boundary-published values projected onto the
            // declared host carriers, omitted required-present fields from
            // the loaded defaults capture (the retained missing-default
            // guard when the map carries none), omitted optional fields
            // absent; the constructor tags the instance with its canonical
            // class identity.
            java.util.Map<String, ValueId> providedSlots = new java.util.LinkedHashMap<>();
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                providedSlots.put(field.name(), field.valueOpId());
            }
            java.util.List<String> args = new java.util.ArrayList<>();
            for (JvmHostAbiEmission.HostFieldFacts field : facts.fields()) {
                String providedChecked = checked.get(field.name());
                if (providedSlots.containsKey(field.name())) {
                    if (providedChecked == null) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " provides field '" + field.name() + "' without its"
                            + " pinned CLASS_LITERAL_FIELD boundary child (producer"
                            + " defect)");
                    }
                    args.add(JvmHostAbiEmission.hostFieldWriteProjection(
                        field.descriptorText(), field.storageType(), providedChecked,
                        "__hostProjectArg"));
                    if (field.optional()) {
                        args.add("true");
                    }
                    continue;
                }
                if (field.optional()) {
                    args.add("null");
                    args.add("false");
                    continue;
                }
                String loaded = "__hostDefault(" + facts.defaultsField() + ", "
                    + javaString(field.name()) + ", "
                    + javaString(payload.classId().text()) + ", "
                    + originArgs(op) + ")";
                args.add(JvmHostAbiEmission.hostFieldWriteProjection(
                    field.descriptorText(), field.storageType(), loaded,
                    "__hostProjectArg"));
            }
            String instName = "__hi_" + op.opId().id();
            out.append(indent(indent)).append("$DealRt.")
                .append(facts.recordSimpleName()).append(' ').append(instName)
                .append(" = new $DealRt.").append(facts.recordSimpleName())
                .append('(').append(String.join(", ", args)).append(");\n");
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = ").append(instName).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * K-D4 step 2, LOCAL: the default children run in declaration
         * order through their detached class-default methods, skipping
         * any child whose field is provided (a provided field's default
         * never runs); each child emits its own START and terminal.
         */
        private void emitClassNewLocalDefaults(SemanticOp op,
                KindPayload.ClassNewPayload payload, java.util.Set<String> provided,
                int indent) {
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
                emitClassDefaultCall(op, defaultOp, indent);
            }
        }

        /** One CLASS_DEFAULT child execution (START, method, terminal). */
        private void emitClassDefaultCall(SemanticOp op, SemanticOp defaultOp, int indent) {
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(defaultOp.opId())))
                    .append(", \"START\", \"CLASS_DEFAULT\", ")
                    .append(javaString(defaultOp.contract().canonicalDigest()))
                    .append(", \"-\", List.of(), null, null);\n");
            }
            out.append(indent(indent)).append("try {\n");
            if (defaultOp.result() instanceof ValueId resultId) {
                out.append(indent(indent)).append("  ").append(slot(resultId))
                    .append(" = ").append(defaultFn(defaultOp.opId())).append("();\n");
            } else {
                out.append(indent(indent)).append("  ")
                    .append(defaultFn(defaultOp.opId())).append("();\n");
            }
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            if (trace) {
                emitFailureEvent(defaultOp.opId(), "CLASS_DEFAULT", defaultOp,
                    "JvmRuntime.errtext(__e)", indent + 1);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__e)", indent + 1);
            }
            out.append(indent(indent)).append("  throw __e;\n");
            out.append(indent(indent)).append("}\n");
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(defaultOp.opId())))
                    .append(", \"SUCCESS\", \"CLASS_DEFAULT\", ")
                    .append(javaString(defaultOp.contract().canonicalDigest()))
                    .append(", \"-\", List.of(), JvmRuntime.atom(")
                    .append(defaultOp.result() instanceof ValueId resultId
                        ? slot(resultId) : "null")
                    .append(", ")
                    .append(javaString(staticKind(
                        (RuntimeDescriptor) defaultOp.resultType())))
                    .append("), null);\n");
            }
        }

        /**
         * The registered owner factory op of a SHARED_FACTORY CLASS_NEW,
         * resolved through the delivered per-module class-factory
         * registries (the one fact channel shared with the oracle and the
         * LuaJIT session): the owner module is the module whose registry
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
         * K-D4 step 2, SHARED_FACTORY: the transfer to the owner's
         * CLASS_FACTORY entry — the factory's events parent to this
         * caller op (cross-unit) and carry the owner's module path; its
         * CLASS_DEFAULT children evaluate in the declaring module's
         * scope (skipping provided fields) and fill the untagged
         * internal transfer instance, which the factory publishes as its
         * result for the caller's CLASS_DEFAULT_FIELD extraction.
         */
        private void emitClassNewFactoryTransfer(SemanticOp op,
                KindPayload.ClassNewPayload payload, java.util.Set<String> provided,
                int indent) {
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
            out.append(indent(indent)).append("String __prevMod_")
                .append(op.opId().id()).append(" = MODULE;\n");
            out.append(indent(indent)).append("MODULE = ")
                .append(javaString(ownerPath)).append(";\n");
            out.append(indent(indent)).append("JvmRuntime.setModule(MODULE);\n");
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(factoryOp.opId())))
                    .append(", \"START\", \"CLASS_FACTORY\", ")
                    .append(javaString(factoryOp.contract().canonicalDigest()))
                    .append(", ").append(javaString(opKey(op.opId())))
                    .append(", List.of(), null, null);\n");
            }
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
                if (trace) {
                    out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(defaultOp.opId())))
                        .append(", \"START\", \"CLASS_DEFAULT\", ")
                        .append(javaString(defaultOp.contract().canonicalDigest()))
                        .append(", \"-\", List.of(), null, null);\n");
                }
                out.append(indent(indent)).append("try {\n");
                if (defaultOp.result() instanceof ValueId resultId) {
                    out.append(indent(indent)).append("  ").append(slot(resultId))
                        .append(" = ").append(defaultFn(defaultOp.opId())).append("();\n");
                } else {
                    out.append(indent(indent)).append("  ")
                        .append(defaultFn(defaultOp.opId())).append("();\n");
                }
                out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
                if (trace) {
                    emitFailureEvent(defaultOp.opId(), "CLASS_DEFAULT", defaultOp,
                        "JvmRuntime.errtext(__e)", indent + 1);
                    out.append(indent(indent)).append("  JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(factoryOp.opId())))
                        .append(", \"FAILURE\", \"CLASS_FACTORY\", ")
                        .append(javaString(factoryOp.contract().canonicalDigest()))
                        .append(", ").append(javaString(opKey(op.opId())))
                        .append(", List.of(), null, JvmRuntime.errtext(__e));\n");
                }
                // Restore the caller's module context before the caller's
                // own terminal: the owner-side terminals above carry the
                // owner's module, the caller's CLASS_NEW FAILURE carries
                // the caller's (the oracle's own tagging).
                out.append(indent(indent)).append("  MODULE = __prevMod_")
                    .append(op.opId().id()).append(";\n");
                out.append(indent(indent)).append("  JvmRuntime.setModule(MODULE);\n");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__e)", indent + 1);
                out.append(indent(indent)).append("  throw __e;\n");
                out.append(indent(indent)).append("}\n");
                if (trace) {
                    out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(defaultOp.opId())))
                        .append(", \"SUCCESS\", \"CLASS_DEFAULT\", ")
                        .append(javaString(defaultOp.contract().canonicalDigest()))
                        .append(", \"-\", List.of(), JvmRuntime.atom(")
                        .append(defaultOp.result() instanceof ValueId resultId
                            ? slot(resultId) : "null")
                        .append(", ")
                        .append(javaString(staticKind(
                            (RuntimeDescriptor) defaultOp.resultType())))
                        .append("), null);\n");
                }
                filled.add(defaultOp);
            }
            // The untagged internal transfer instance: the defaulted
            // fields present (present null is f == null && p == true),
            // every other field missing.
            String carrier = carrierName(payload.classId());
            String instName = "__tf_" + factoryOp.opId().id() + "_" + op.opId().id();
            out.append(indent(indent)).append(carrier).append(' ').append(instName)
                .append(" = new ").append(carrier).append("();\n");
            for (SemanticOp defaultOp : filled) {
                KindPayload.ClassDefaultPayload defaultPayload =
                    (KindPayload.ClassDefaultPayload) defaultOp.payload();
                out.append(indent(indent)).append(instName).append('.')
                    .append(fieldSlot(defaultPayload.field())).append(" = ")
                    .append(slot((ValueId) defaultOp.result())).append(";\n");
                out.append(indent(indent)).append(instName).append('.')
                    .append(fieldFlag(defaultPayload.field())).append(" = true;\n");
            }
            out.append(indent(indent)).append(slot(factoryResult)).append(" = ")
                .append(instName).append(";\n");
            if (trace) {
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(factoryOp.opId())))
                    .append(", \"SUCCESS\", \"CLASS_FACTORY\", ")
                    .append(javaString(factoryOp.contract().canonicalDigest()))
                    .append(", ").append(javaString(opKey(op.opId())))
                    .append(", List.of(), JvmRuntime.atom(").append(instName)
                    .append(", \"class\"), null);\n");
            }
            out.append(indent(indent)).append("MODULE = __prevMod_")
                .append(op.opId().id()).append(";\n");
            out.append(indent(indent)).append("JvmRuntime.setModule(MODULE);\n");
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

        private void emitIntrinsic(SemanticOp op, int indent) {
            KindPayload.IntrinsicCallPayload payload =
                (KindPayload.IntrinsicCallPayload) op.payload();
            emitStart(op, indent);
            String target = slot((ValueId) op.result());
            String input = slot(payload.input());
            String kind = staticKind(op.operandTypes().get(0));
            String origin = originOf(op);
            switch (payload.kind()) {
                // The direct arm keeps its own kind as the invoking op's
                // label (ISSUE-0679); an intrinsic value call passes the
                // invoking CALL op's kind through the same ladder.
                case INT_CONVERT -> out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.intConv(").append(input).append(", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(kind)).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(origin)).append(");\n");
                case NUMBER_CONVERT -> out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.numConv(").append(input).append(", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(kind)).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(origin)).append(");\n");
                case BYTES_NEW -> out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.bytesNew(").append(input).append(", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(origin)).append(");\n");
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitStdlib(SemanticOp op, int indent) {
            KindPayload.StdlibCallPayload payload =
                (KindPayload.StdlibCallPayload) op.payload();
            if (trace) {
                // The custom START: the operand atoms render the actual
                // value kind (the oracle's atomOf — a dynamic argument at
                // a declared boundary atomizes as its own kind), never the
                // declared kind.
                StringBuilder inputs = new StringBuilder();
                for (int i = 0; i < payload.args().size(); i++) {
                    if (i > 0) {
                        inputs.append(", ");
                    }
                    inputs.append("JvmRuntime.rawAtom(")
                        .append(slot(payload.args().get(i))).append(", ")
                        .append(javaString(staticKind(op.operandTypes().get(i))))
                        .append(")");
                }
                out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                    .append("\"STDLIB_CALL\", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId())))
                    .append(", List.of(").append(inputs).append("), null, null);\n");
            }
            // The closed STDLIB_PARAMETER boundaries in one-based declared
            // order: a failing boundary publishes the boundary FAILURE and
            // the op FAILURE events with the boundary origin, then rethrows
            // (the exact oracle event sequence — never a silent terminal).
            List<SemanticOp> paramBoundaries = stdlibParamBoundaries(op);
            for (SemanticOp boundary : paramBoundaries) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                if (trace) {
                    // Custom boundary START: the input atom renders the
                    // actual value kind (the oracle's atomOf).
                    out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(boundary.opId())))
                        .append(", \"START\", \"BOUNDARY\", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", List.of(JvmRuntime.rawAtom(")
                        .append(slot(boundaryPayload.input())).append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append(")), null, null);\n");
                }
                out.append(indent(indent)).append("  Object __sb_")
                    .append(boundary.opId().id()).append(";\n");
                out.append(indent(indent)).append("  try {\n");
                out.append(indent(indent)).append("    __sb_")
                    .append(boundary.opId().id())
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), slot(boundaryPayload.input())))
                    .append(";\n");
                out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("    JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("    throw __bre;\n");
                out.append(indent(indent)).append("  }\n");
                emitBoundarySuccess(boundary, "__sb_" + boundary.opId().id(),
                    boundaryPayload.descriptor(), indent);
            }
            SemanticOp returnBoundary = stdlibReturnBoundary(op);
            String target = slot((ValueId) op.result());
            // Every row runs the one row invoker the cataloged callable also
            // runs (M4: the two console rows' single-effect write included),
            // so the direct arm and the callable share one realization and
            // the direct arm's observable is unchanged.
            out.append(indent(indent)).append(target)
                .append(" = JvmRuntime.stdlibInvoke(")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(payload.function().name())).append(", ")
                .append(javaString(opKey(op.opId()))).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                .append(javaString(originOf(op))).append(", new Object[]{");
            for (int i = 0; i < payload.args().size(); i++) {
                if (i > 0) {
                    out.append(", ");
                }
                out.append(slot(payload.args().get(i)));
            }
            out.append("});\n");
            if (returnBoundary != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) returnBoundary.payload();
                if (trace) {
                    // Custom boundary START: the result atom renders the
                    // actual value kind (the oracle's atomOf).
                    out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(returnBoundary.opId())))
                        .append(", \"START\", \"BOUNDARY\", ")
                        .append(javaString(returnBoundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(
                            parentKey(returnBoundary.origin().parentOpId())))
                        .append(", List.of(JvmRuntime.rawAtom(")
                        .append(target).append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append(")), null, null);\n");
                }
                out.append(indent(indent)).append("  try {\n");
                out.append(indent(indent)).append("    ").append(target)
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), target))
                    .append(";\n");
                out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("    JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(returnBoundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(returnBoundary.opId(), "BOUNDARY", returnBoundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("    throw __bre;\n");
                out.append(indent(indent)).append("  }\n");
                emitBoundarySuccess(returnBoundary, target, boundaryPayload.descriptor(),
                    indent);
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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

        private void emitBranch(SemanticOp op, int indent) {
            KindPayload.BranchPayload payload = (KindPayload.BranchPayload) op.payload();
            emitStart(op, indent);
            String condition = slot(payload.condition());
            switch (payload.selector()) {
                case IF -> {
                    out.append(indent(indent)).append("if (((Boolean) ").append(condition)
                        .append(").booleanValue()) {\n");
                    emitBlockOps(payload.selectedBlock(), indent + 1);
                    out.append(indent(indent)).append("}");
                    if (payload.alternateBlock() != null) {
                        out.append(" else {\n");
                        emitBlockOps(payload.alternateBlock(), indent + 1);
                        out.append(indent(indent)).append("}");
                    }
                    out.append("\n");
                    emitPlainSuccess(op, indent);
                }
                case LOGICAL_AND, LOGICAL_OR -> {
                    String target = slot((ValueId) op.result());
                    boolean isAnd = payload.selector()
                        == deal.semantic.ir.ControlSelector.LOGICAL_AND;
                    if (isAnd) {
                        // AND: the block runs when the left value is true.
                        out.append(indent(indent)).append("if (((Boolean) ")
                            .append(condition).append(").booleanValue()) {\n");
                    } else {
                        // OR: the block runs when the left value is false.
                        out.append(indent(indent)).append("if (!((Boolean) ")
                            .append(condition).append(").booleanValue()) {\n");
                    }
                    emitBlockOps(payload.selectedBlock(), indent + 1);
                    out.append(indent(indent)).append("} else {\n");
                    out.append(indent(indent)).append("  ").append(target).append(" = ")
                        .append(condition).append(";\n");
                    out.append(indent(indent)).append("}\n");
                    emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(),
                        indent);
                }
                default -> throw new IllegalStateException("BRANCH selector "
                    + payload.selector());
            }
        }

        private void emitLoop(SemanticOp op, int indent) {
            KindPayload.LoopPayload payload = (KindPayload.LoopPayload) op.payload();
            emitStart(op, indent);
            String condition = slot(payload.condition());
            switch (payload.selector()) {
                case WHILE -> {
                    out.append(indent(indent)).append(loopLabel(op.opId()))
                        .append(": while (true) {\n");
                    emitBlockOps(payload.initBlock(), indent + 1);
                    out.append(indent(indent)).append("  if (!((Boolean) ").append(condition)
                        .append(").booleanValue()) break ").append(loopLabel(op.opId()))
                        .append(";\n");
                    emitBlockOps(payload.bodyBlock(), indent + 1);
                    out.append(indent(indent)).append("}\n");
                }
                case FOR -> {
                    emitBlockOps(payload.initBlock(), indent);
                    out.append(indent(indent)).append(loopLabel(op.opId()))
                        .append(": while (true) {\n");
                    out.append(indent(indent)).append("  if (!((Boolean) ").append(condition)
                        .append(").booleanValue()) break ").append(loopLabel(op.opId()))
                        .append(";\n");
                    out.append(indent(indent)).append("  CONT").append(op.opId().id())
                        .append(": do {\n");
                    emitBlockOps(payload.bodyBlock(), indent + 2);
                    out.append(indent(indent)).append("  } while (false);\n");
                    if (payload.updateBlock() != null) {
                        emitBlockOps(payload.updateBlock(), indent + 1);
                    }
                    out.append(indent(indent)).append("}\n");
                }
                default -> throw new IllegalStateException("LOOP selector "
                    + payload.selector());
            }
            emitPlainSuccess(op, indent);
        }

        private void emitForEach(SemanticOp op, int indent) {
            KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) op.payload();
            emitStart(op, indent);
            switch (payload.mode()) {
                case ARRAY_VALUES -> {
                    String iterable = slot(payload.iterable());
                    String cellName = cell(payload.binding(), payload.generation());
                    out.append(indent(indent)).append("{\n");
                    out.append(indent(indent)).append("  JvmRuntime.Array __it = (JvmRuntime.Array) ")
                        .append(iterable).append(";\n");
                    out.append(indent(indent)).append("  int __itn = __it.length;\n");
                    out.append(indent(indent)).append("  FE").append(op.opId().id())
                        .append(": for (int __i = 0; __i < __itn; __i++) {\n");
                    out.append(indent(indent)).append("    Object __elem = JvmRuntime.MISSING;\n");
                    out.append(indent(indent)).append("    if (__i < __it.length && __i < __it.elements.size()) {\n");
                    out.append(indent(indent)).append("      __elem = __it.elements.get(__i);\n");
                    out.append(indent(indent)).append("    }\n");
                    out.append(indent(indent)).append("    JvmRuntime.foreachCheck(")
                        .append(javaString(opKey(op.opId()))).append(", ")
                        .append(javaString(op.contract().canonicalDigest())).append(", ")
                        .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                        .append(javaString(descriptorText(elementDescriptorOf(op))))
                        .append(", __elem, ").append(javaString(originOf(op))).append(");\n");
                    out.append(indent(indent)).append("    ").append(cellName)
                        .append(" = new Object[]{__elem};\n");
                    emitBlockOps(payload.body(), indent + 2);
                    out.append(indent(indent)).append("  }\n");
                    out.append(indent(indent)).append("}\n");
                }
                case STRING_SCALARS -> {
                    String iterable = slot(payload.iterable());
                    String cellName = cell(payload.binding(), payload.generation());
                    out.append(indent(indent)).append("{\n");
                    out.append(indent(indent)).append("  String __it = (String) ")
                        .append(iterable).append(";\n");
                    out.append(indent(indent)).append("  int[] __cps = __it.codePoints().toArray();\n");
                    out.append(indent(indent)).append("  FE").append(op.opId().id())
                        .append(": for (int __cp : __cps) {\n");
                    out.append(indent(indent)).append("    ").append(cellName)
                        .append(" = new Object[]{new String(Character.toChars(__cp))};\n");
                    emitBlockOps(payload.body(), indent + 2);
                    out.append(indent(indent)).append("  }\n");
                    out.append(indent(indent)).append("}\n");
                }
            }
            emitPlainSuccess(op, indent);
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

        /**
         * The TRY_CATCH arm: the try block runs under a {@code DealError}
         * catch clause that reifies the caught failure as the builtin Error
         * carrier in the catch binding's cell, then the catch block runs
         * under its own {@code DealError} wrapper (a failure of the catch
         * block re-projects the wrapped carrier with {@code cause} = the
         * original). The transfer dispatch (a {@code RETURN}/{@code BREAK}/
         * {@code CONTINUE} inside the try block or the catch block signals
         * through {@code JvmRuntime.Transfer}) wraps the WHOLE try/catch: an
         * exception raised inside a catch clause is never handled by the
         * sibling clauses of its own try statement, so the dispatch cannot
         * live beside the {@code DealError} clause (ISSUE-0619's catch
         * rethrow/return surface).
         */
        private void emitTryCatch(SemanticOp op, int indent) {
            KindPayload.TryCatchPayload payload =
                (KindPayload.TryCatchPayload) op.payload();
            emitStart(op, indent);
            String cellName = cell(payload.catchBinding(), 0);
            out.append(indent(indent)).append("try {\n");
            tryDepth++;
            try {
                out.append(indent(indent)).append("  try {\n");
                emitBlockOps(payload.tryBlock(), indent + 2);
                out.append(indent(indent))
                    .append("  } catch (JvmRuntime.DealError __terr) {\n");
                out.append(indent(indent)).append("    ").append(cellName)
                    .append(" = new JvmRuntime.ErrorValue(__terr.code, __terr.msg);\n");
                out.append(indent(indent)).append("    try {\n");
                emitBlockOps(payload.catchBlock(), indent + 3);
                out.append(indent(indent))
                    .append("    } catch (JvmRuntime.DealError __cerr) {\n");
                out.append(indent(indent))
                    .append("      JvmRuntime.DealError __wrapped = new "
                        + "JvmRuntime.DealError(__cerr.code, __cerr.msg, "
                        + "__cerr.origin, __cerr.expected, __cerr.actual, "
                        + "__cerr.frames, __terr);\n");
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__wrapped)", indent + 3);
                out.append(indent(indent)).append("      throw __wrapped;\n");
                out.append(indent(indent)).append("    }\n");
                out.append(indent(indent)).append("  }\n");
            } finally {
                tryDepth--;
            }
            out.append(indent(indent))
                .append("} catch (JvmRuntime.Transfer __tr) {\n");
            emitJvmTransferDispatch(op, payload.tryBlock(), indent + 1);
            emitJvmTransferDispatch(op, payload.catchBlock(), indent + 1);
            out.append(indent(indent)).append("  throw __tr;\n");
            out.append(indent(indent)).append("}\n");
            if (blockCompletesNormally(payload.tryBlock())
                    || blockCompletesNormally(payload.catchBlock())) {
                emitPlainSuccess(op, indent);
            } else {
                // JLS §14.21: the emitted try/catch cannot complete normally
                // (both clauses end in a transfer), so its
                // normal-completion SUCCESS event is unreachable — javac
                // rejects a plain statement here, and the oracle's
                // normal-completion path is unreachable on the same traces.
                out.append(indent(indent)).append("// unreachable: the preceding"
                    + " statement cannot complete normally\n");
            }
        }

        /** The transfer dispatch: each distinct BREAK/CONTINUE/RETURN of the
         *  block re-applies after emitting the TRY_CATCH SUCCESS. */
        private void emitJvmTransferDispatch(SemanticOp tryOp, BlockId block, int indent) {
            List<SemanticOp> transfers = new ArrayList<>();
            collectTransfers(block, transfers);
            for (SemanticOp transfer : transfers) {
                switch (transfer.kind()) {
                    case BREAK -> {
                        KindPayload.BreakPayload breakPayload =
                            (KindPayload.BreakPayload) transfer.payload();
                        out.append(indent(indent)).append("if (\"break\".equals(__tr.kind) ")
                            .append("&& __tr.id == ").append(breakPayload.loopId().id())
                            .append("L) {\n");
                        emitPlainSuccess(tryOp, indent + 1);
                        emitTransferClosures(tryOp, opsById.get(breakPayload.loopId()),
                            false, indent + 1);
                        out.append(indent(indent)).append("  break ")
                            .append(loopLabel(breakPayload.loopId())).append(";\n");
                        out.append(indent(indent)).append("}\n");
                    }
                    case CONTINUE -> {
                        KindPayload.ContinuePayload continuePayload =
                            (KindPayload.ContinuePayload) transfer.payload();
                        out.append(indent(indent)).append("if (\"continue\".equals(__tr.kind) ")
                            .append("&& __tr.id == ").append(continuePayload.loopId().id())
                            .append("L) {\n");
                        emitPlainSuccess(tryOp, indent + 1);
                        emitTransferClosures(tryOp, opsById.get(continuePayload.loopId()),
                            false, indent + 1);
                        SemanticOp target = opsById.get(continuePayload.loopId());
                        if (target != null && target.kind() == SemanticOpKind.LOOP
                                && ((KindPayload.LoopPayload) target.payload()).selector()
                                    == deal.semantic.ir.ControlSelector.FOR) {
                            out.append(indent(indent)).append("  continue CONT")
                                .append(continuePayload.loopId().id()).append(";\n");
                        } else {
                            out.append(indent(indent)).append("  continue ")
                                .append(loopLabel(continuePayload.loopId())).append(";\n");
                        }
                        out.append(indent(indent)).append("}\n");
                    }
                    case RETURN -> {
                        out.append(indent(indent)).append("if (\"return\".equals(__tr.kind)) {\n");
                        emitPlainSuccess(tryOp, indent + 1);
                        emitTransferClosures(tryOp, null, false, indent + 1);
                        out.append(indent(indent)).append("  return __tr.value;\n");
                        out.append(indent(indent)).append("}\n");
                    }
                    default -> {
                    }
                }
            }
        }

        /** Collects the transfer ops of a block recursively through structure payloads. */
        private void collectTransfers(BlockId block, List<SemanticOp> transfers) {
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

        private void emitThrow(SemanticOp op, int indent) {
            KindPayload.ThrowPayload payload = (KindPayload.ThrowPayload) op.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("JvmRuntime.DealError __thrown = new "
                + "JvmRuntime.DealError(((").append("JvmRuntime.ErrorValue) ")
                .append(slot(payload.errorValue())).append(").code, ((")
                .append("JvmRuntime.ErrorValue) ").append(slot(payload.errorValue()))
                .append(").message, ").append(javaString(originOf(op)))
                .append(", null, null, JvmRuntime.framesText(), null);\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__thrown)", indent);
            out.append(indent(indent)).append("throw __thrown;\n");
        }

        private void emitReturn(SemanticOp op, int indent) {
            KindPayload.ReturnPayload payload = (KindPayload.ReturnPayload) op.payload();
            SemanticOp boundary = opsById.get(payload.returnBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitStart(op, indent);
            String value = payload.value() == null ? "null" : slot(payload.value());
            out.append(indent(indent)).append("Object __rv_").append(op.opId().id())
                .append(" = ").append(value).append(";\n");
            emitBoundaryStart(boundary, "__rv_" + op.opId().id(),
                boundaryPayload.descriptor(), indent);
            // The body-local return cell's own failure projection: the cell
            // projection carries the cell's origin (the callee's RETURN), the
            // boundary and the RETURN op emit their FAILURE terminals, and the
            // identical error propagates (the semantic oracle's
            // runBoundaryChild + the owning-op FAILURE).
            String rvc = "__rvc_" + op.opId().id();
            String rejection = "__bre_" + op.opId().id();
            String caught = "__be_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(rvc).append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(rvc)
                .append(" = ")
                .append(bcheckArgs(boundaryPayload.descriptor(), "__rv_" + op.opId().id()))
                .append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError ")
                .append(caught).append(") {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.DealError ")
                .append(rejection).append(" = new JvmRuntime.DealError(")
                .append(caught).append(".code, ").append(caught)
                .append(".msg, ")
                .append(javaString(originOf(boundary)))
                .append(", ").append(caught).append(".expected, ").append(caught)
                .append(".actual, ").append(caught).append(".frames, null);\n");
            emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                "JvmRuntime.errtext(" + rejection + ")", indent + 1);
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(" + rejection + ")", indent + 1);
            out.append(indent(indent + 1)).append("throw ").append(rejection)
                .append(";\n");
            out.append(indent(indent)).append("}\n");
            emitBoundarySuccess(boundary, rvc, boundaryPayload.descriptor(), indent);
            emitPlainSuccess(op, indent);
            if (tryDepth > 0) {
                emitTransferClosures(op, null, true, indent);
                out.append(indent(indent))
                    .append("throw new JvmRuntime.Transfer(\"return\", 0L, __rvc_")
                    .append(op.opId().id()).append(");\n");
            } else {
                emitTransferClosures(op, null, false, indent);
                out.append(indent(indent)).append("return __rvc_").append(op.opId().id())
                    .append(";\n");
            }
        }

        private void emitBreak(SemanticOp op, int indent) {
            KindPayload.BreakPayload payload = (KindPayload.BreakPayload) op.payload();
            emitStart(op, indent);
            emitPlainSuccess(op, indent);
            if (tryDepth > 0) {
                emitTransferClosures(op, opsById.get(payload.loopId()), true, indent);
                out.append(indent(indent)).append("throw new JvmRuntime.Transfer(\"break\", ")
                    .append(payload.loopId().id()).append("L, null);\n");
            } else {
                emitTransferClosures(op, opsById.get(payload.loopId()), false, indent);
                SemanticOp target = opsById.get(payload.loopId());
                if (target != null && target.kind() == SemanticOpKind.FOR_EACH) {
                    out.append(indent(indent)).append("break FE")
                        .append(payload.loopId().id()).append(";\n");
                } else {
                    out.append(indent(indent)).append("break ")
                        .append(loopLabel(payload.loopId())).append(";\n");
                }
            }
        }

        private void emitContinue(SemanticOp op, int indent) {
            KindPayload.ContinuePayload payload = (KindPayload.ContinuePayload) op.payload();
            emitStart(op, indent);
            emitPlainSuccess(op, indent);
            if (tryDepth > 0) {
                emitTransferClosures(op, opsById.get(payload.loopId()), true, indent);
                out.append(indent(indent))
                    .append("throw new JvmRuntime.Transfer(\"continue\", ")
                    .append(payload.loopId().id()).append("L, null);\n");
            } else {
                emitTransferClosures(op, opsById.get(payload.loopId()), false, indent);
                SemanticOp target = opsById.get(payload.loopId());
                if (target != null && target.kind() == SemanticOpKind.FOR_EACH) {
                    out.append(indent(indent)).append("continue FE")
                        .append(payload.loopId().id()).append(";\n");
                } else if (target != null && target.kind() == SemanticOpKind.LOOP
                        && ((KindPayload.LoopPayload) target.payload()).selector()
                            == deal.semantic.ir.ControlSelector.FOR) {
                    out.append(indent(indent)).append("continue CONT")
                        .append(payload.loopId().id()).append(";\n");
                } else {
                    out.append(indent(indent)).append("continue ")
                        .append(loopLabel(payload.loopId())).append(";\n");
                }
            }
        }

        private void emitDiscard(SemanticOp op, int indent) {
            emitStart(op, indent);
            emitPlainSuccess(op, indent);
        }

        /**
         * {@code EXPORT_PUBLISH} — the checked {@code MODULE_EXPORT}
         * boundary (its owned child) then the publication of the callable
         * function value ({@code JvmRuntime.FunctionValue}) into the
         * emitting module's export surface.
         */
        private void emitExportPublish(SemanticOp op, int indent) {
            KindPayload.ExportPublishPayload payload =
                (KindPayload.ExportPublishPayload) op.payload();
            emitStart(op, indent);
            for (SemanticOp candidate : opsById.values()) {
                if (candidate.kind() == SemanticOpKind.BOUNDARY
                        && op.opId().equals(candidate.origin().parentOpId())) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) candidate.payload();
                    emitBoundaryStart(candidate, slot(boundaryPayload.input()),
                        boundaryPayload.descriptor(), indent + 1);
                    out.append(indent(indent + 1)).append("Object __ep_")
                        .append(candidate.opId().id())
                        .append(" = ")
                        .append(bcheckArgs(boundaryPayload.descriptor(),
                            slot(boundaryPayload.input()))).append(";\n");
                    emitBoundarySuccess(candidate, "__ep_" + candidate.opId().id(),
                        boundaryPayload.descriptor(), indent + 1);
                }
            }
            out.append(indent(indent)).append("exportSurface(")
                .append(javaString(emittingModulePath(op))).append(").write(")
                .append(javaString(payload.name())).append(", ")
                .append(slot(payload.value())).append(");\n");
            emitPlainSuccess(op, indent);
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
         * function callable across a shared/shadow edge: production export
         * transport is the retained layout's artifact ABI, so the record
         * needs no runtime action.
         */
        private void emitExternalEntryRecord(SemanticOp op, int indent) {
            emitStart(op, indent);
            emitPlainSuccess(op, indent);
        }

        /**
         * CALLBACK_INVOKE (E6, D13 host-driven dispatch): one per-unit
         * static entry method the scenario host invokes top-level with
         * scripted arguments. The entry emits its own START (the scripted
         * argument inputs, no parentOpId — the scenario step triggers
         * it), runs the {@code HOST_TO_DEAL} parameter boundaries in
         * one-based order, executes the bound
         * {@link FunctionExecutionBinding} (a DEAL body, or the D15
         * adapter protocol with the leading-M projection), and closes
         * with the op's terminal (SUCCESS with the checked value, or
         * FAILURE with the propagated error). The single
         * {@code DEAL_TO_HOST} return boundary runs by the executed
         * body's {@code RETURN} (its payload names this op as the
         * enclosing invocation). The block walk never runs the entry.
         */
        private void emitCallbackInvoke(SemanticOp op, int indent) {
            KindPayload.CallbackInvokePayload payload =
                (KindPayload.CallbackInvokePayload) op.payload();
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new deal.semantic.ir.FunctionAllocationIdentity(
                    payload.function().id()));
            if (binding == null) {
                throw new IllegalStateException("CALLBACK_INVOKE " + op.opId()
                    + " resolves no FunctionExecutionBinding (producer defect)");
            }
            String entry = "cb" + op.opId().id();
            out.append(indent(indent)).append("public static Object ").append(entry)
                .append("(Object[] __args) {\n");
            if (trace) {
                StringBuilder inputs = new StringBuilder();
                for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                    if (i > 0) {
                        inputs.append(", ");
                    }
                    inputs.append("JvmRuntime.hostAtom(__args[").append(i).append("])");
                }
                out.append(indent(indent)).append("  JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest()))
                    .append(", \"-\", List.of(").append(inputs)
                    .append("), null, null);\n");
            }
            for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                SemanticOp boundary = opsById.get(payload.parameterBoundaryOpIds().get(i));
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                String checked = "__cb_" + boundary.opId().id();
                if (trace) {
                    out.append(indent(indent)).append("  JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(boundary.opId())))
                        .append(", \"START\", \"BOUNDARY\", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", List.of(JvmRuntime.hostAtom(__args[")
                        .append(i).append("])), null, null);\n");
                }
                out.append(indent(indent)).append("  Object ").append(checked)
                    .append(";\n");
                out.append(indent(indent)).append("  try {\n");
                out.append(indent(indent)).append("    ").append(checked)
                    .append(" = ")
                    .append(bcheckArgs(boundaryPayload.descriptor(), "__args[" + i + "]"))
                    .append(";\n");
                out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __be) {\n");
                out.append(indent(indent))
                    .append("    JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                        + "__be.code, __be.msg, ")
                    .append(javaString(originOf(boundary)))
                    .append(", __be.expected, __be.actual, __be.frames, null);\n");
                if (trace) {
                    emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__bre)", indent + 1);
                }
                out.append(indent(indent)).append("    throw __bre;\n");
                out.append(indent(indent)).append("  }\n");
                if (trace) {
                    out.append(indent(indent)).append("  JvmRuntime.ev(MODULE, ")
                        .append(javaString(opKey(boundary.opId())))
                        .append(", \"SUCCESS\", \"BOUNDARY\", ")
                        .append(javaString(boundary.contract().canonicalDigest()))
                        .append(", ")
                        .append(javaString(parentKey(boundary.origin().parentOpId())))
                        .append(", List.of(), JvmRuntime.atom(")
                        .append(checked).append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append("), null);\n");
                }
            }
            out.append(indent(indent)).append("  Object __res;\n");
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    LoweredFunction function = functionOf(body.functionId());
                    List<BindingGeneration> captures = function == null
                        ? List.of() : function.captures();
                    StringBuilder caps = new StringBuilder();
                    for (BindingGeneration capture : captures) {
                        if (caps.length() > 0) {
                            caps.append(", ");
                        }
                        caps.append(captureArg(capture));
                    }
                    out.append(indent(indent)).append("  JvmRuntime.pushFrame(")
                        .append(javaString(String.valueOf(body.functionId().id())))
                        .append(");\n");
                    out.append(indent(indent)).append("  try {\n");
                    out.append(indent(indent)).append("    __res = ")
                        .append(fnFactory(body.functionId())).append("(")
                        .append(caps).append(").fn.invoke(new Object[]{");
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        if (i > 0) {
                            out.append(", ");
                        }
                        SemanticOp boundary =
                            opsById.get(payload.parameterBoundaryOpIds().get(i));
                        out.append("__cb_").append(boundary.opId().id());
                    }
                    out.append("});\n");
                    out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __e) {\n");
                    if (trace) {
                        emitFailureEvent(op.opId(), op.kind().name(), op,
                            "JvmRuntime.errtext(__e)", indent + 1);
                    }
                    out.append(indent(indent)).append("    throw __e;\n");
                    out.append(indent(indent)).append("  } finally {\n");
                    out.append(indent(indent)).append("    JvmRuntime.popFrame();\n");
                    out.append(indent(indent)).append("  }\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    String adapterSlot =
                        slot((ValueId) opsById.get(adapter.adaptOpId()).result());
                    out.append(indent(indent)).append("  try {\n");
                    out.append(indent(indent))
                        .append("    __res = JvmRuntime.invokeAdapter((JvmRuntime.AdapterValue) ")
                        .append(adapterSlot).append(", ")
                        .append(javaString(originOf(op))).append(", new Object[]{");
                    for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                        if (i > 0) {
                            out.append(", ");
                        }
                        SemanticOp boundary =
                            opsById.get(payload.parameterBoundaryOpIds().get(i));
                        out.append("__cb_").append(boundary.opId().id());
                    }
                    out.append("});\n");
                    out.append(indent(indent)).append("  } catch (JvmRuntime.DealError __e) {\n");
                    if (trace) {
                        emitFailureEvent(op.opId(), op.kind().name(), op,
                            "JvmRuntime.errtext(__e)", indent + 1);
                    }
                    out.append(indent(indent)).append("    throw __e;\n");
                    out.append(indent(indent)).append("  }\n");
                }
                case FunctionExecutionBinding.HostFunction host ->
                    emitHostCallbackInvoke(op, payload,
                        hostAbi.requireWrapper(host.hostModuleId().path(),
                            host.exportName()),
                        hostAbi.declaredFunction(host.hostModuleId().path(),
                            host.exportName()), indent);
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
                    emitHostCallbackValue(op, payload, slot(boundary.input()), indent);
                }
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw new IllegalStateException("CALLBACK_INVOKE " + op.opId()
                        + " resolves the " + intrinsic.kind() + " intrinsic carrier"
                        + " (the intrinsic carrier is the function-typed-value"
                        + " child's — a fail-closed producer defect)");
                case FunctionExecutionBinding.ExternalFunction external ->
                    throw new IllegalStateException("CALLBACK_INVOKE " + op.opId()
                        + " resolves an external binding outside the statically-"
                        + "resolved slice (a fail-closed producer defect)");
                default -> throw new IllegalStateException("CALLBACK_INVOKE "
                    + op.opId() + " resolves a binding outside the statically-resolved "
                    + "slice: " + binding);
            }
            if (trace) {
                out.append(indent(indent)).append("  JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest()))
                    .append(", \"-\", List.of(), JvmRuntime.atom(__res, ")
                    .append(javaString(staticKind(payload.descriptor().returnType())))
                    .append("), null);\n");
            }
            out.append(indent(indent)).append("  return __res;\n");
            out.append(indent(indent)).append("}\n");
        }

        /**
         * The host {@code CALLBACK_INVOKE} arm (ISSUE-0651;
         * {@code host-module-load-and-host-call-realization} H3 and the sync
         * host call contract): the callback record's bound value resolves
         * to a declared host export, so the host-driven invocation runs the
         * emitted per-export wrapper with the {@code HOST_TO_DEAL} checked
         * arguments and the callback op's own origin, then the callback
         * op's own return projection (its single return boundary child).
         */
        private void emitHostCallbackInvoke(SemanticOp op,
                KindPayload.CallbackInvokePayload payload, String wrapper,
                Type.Func declared, int indent) {
            StringBuilder call = new StringBuilder(wrapper).append('(');
            for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                SemanticOp boundary = opsById.get(payload.parameterBoundaryOpIds().get(i));
                call.append("__cb_").append(boundary.opId().id()).append(", ");
            }
            call.append(originArgs(op)).append(')');
            out.append(indent(indent)).append("  try {\n");
            if (declared.returnType() instanceof Type.Null) {
                // The emitted wrapper of a declared null return is void:
                // the invocation is a statement and the callback value is
                // the language null (the op's own return cell below checks
                // it).
                out.append(indent(indent)).append("    ").append(call).append(";\n");
                out.append(indent(indent)).append("    __res = null;\n");
            } else {
                out.append(indent(indent)).append("    __res = ").append(call)
                    .append(";\n");
            }
            out.append(indent(indent))
                .append("  } catch (JvmRuntime.DealError __e) {\n");
            if (trace) {
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__e)", indent + 2);
            }
            out.append(indent(indent)).append("    throw __e;\n");
            out.append(indent(indent)).append("  }\n");
            emitCallbackReturnCell(op, payload, indent);
        }

        /**
         * The host-materialized {@code CALLBACK_INVOKE} arm: the value the
         * callback record's producing host crossing published is invoked
         * through its production function carrier with the same declared
         * cells and the callback op's own return projection.
         */
        private void emitHostCallbackValue(SemanticOp op,
                KindPayload.CallbackInvokePayload payload, String value, int indent) {
            out.append(indent(indent)).append("  try {\n");
            out.append(indent(indent)).append("    __res = ((JvmRuntime.FunctionValue) ")
                .append(value).append(").fn.invoke(new Object[]{");
            for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                if (i > 0) {
                    out.append(", ");
                }
                SemanticOp boundary = opsById.get(payload.parameterBoundaryOpIds().get(i));
                out.append("__cb_").append(boundary.opId().id());
            }
            out.append("});\n");
            out.append(indent(indent))
                .append("  } catch (JvmRuntime.DealError __e) {\n");
            if (trace) {
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__e)", indent + 2);
            }
            out.append(indent(indent)).append("    throw __e;\n");
            out.append(indent(indent)).append("  }\n");
            emitCallbackReturnCell(op, payload, indent);
        }

        /** The callback op's own single return boundary cell, when recorded. */
        private void emitCallbackReturnCell(SemanticOp op,
                KindPayload.CallbackInvokePayload payload, int indent) {
            if (payload.returnBoundaryOpId() == null) {
                return;
            }
            SemanticOp boundary = opsById.get(payload.returnBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitBoundaryStartAtom(boundary, "JvmRuntime.atom(__res, "
                + javaString(staticKind(boundaryPayload.descriptor())) + ")", indent);
            String checked = "__cbr_" + boundary.opId().id();
            out.append(indent(indent)).append("  Object ").append(checked)
                .append(";\n");
            out.append(indent(indent)).append("  try {\n");
            out.append(indent(indent)).append("    ").append(checked)
                .append(" = ")
                .append(bcheckArgs(boundaryPayload.descriptor(), "__res"))
                .append(";\n");
            out.append(indent(indent))
                .append("  } catch (JvmRuntime.DealError __be) {\n");
            out.append(indent(indent))
                .append("    JvmRuntime.DealError __bre = new JvmRuntime.DealError("
                    + "__be.code, __be.msg, ")
                .append(javaString(originOf(boundary)))
                .append(", __be.expected, __be.actual, __be.frames, null);\n");
            if (trace) {
                emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                    "JvmRuntime.errtext(__bre)", indent + 2);
                emitFailureEvent(op.opId(), op.kind().name(), op,
                    "JvmRuntime.errtext(__bre)", indent + 2);
            }
            out.append(indent(indent)).append("    throw __bre;\n");
            out.append(indent(indent)).append("  }\n");
            emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor(),
                indent + 1);
            out.append(indent(indent)).append("  __res = ").append(checked)
                .append(";\n");
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
        private void emitTokenSuccess(SemanticOp op, String atomExpr, int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                .append(javaString(op.kind().name())).append(", ")
                .append(javaString(op.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(op.origin().parentOpId())))
                .append(", List.of(), ").append(atomExpr).append(", null);\n");
        }

        /** A boundary START event with a raw input atom expression. */
        private void emitBoundaryStartAtom(SemanticOp boundary, String atomExpr,
                                           int indent) {
            if (!trace) {
                return;
            }
            out.append(indent(indent)).append("JvmRuntime.ev(MODULE, ")
                .append(javaString(opKey(boundary.opId()))).append(", \"START\", ")
                .append("\"BOUNDARY\", ")
                .append(javaString(boundary.contract().canonicalDigest())).append(", ")
                .append(javaString(parentKey(boundary.origin().parentOpId())))
                .append(", List.of(").append(atomExpr).append("), null, null);\n");
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
         * DEAL body task is a {@code CompletableFuture} completed by the
         * module's run-local single-thread serial executor (never the JDK
         * common pool); an adapter-over-async task resolves the D15
         * source, checks the source signature, and executes the nested
         * source op; a host operation starts through the artifact's
         * host-seam entry (bad handle → the op's own E8010
         * {@code ASYNC_OPERATION_HANDLE}); an external operation starts
         * through the callee artifact's async-entry dispatch entry. The
         * op's terminal publishes the canonical/alias token atom.
         */
        private void emitAsyncStart(SemanticOp op, int indent) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            AsyncTokenId token = (AsyncTokenId) op.result();
            emitStart(op, indent);
            // The argument expressions per position: the boundary-checked
            // values (RUN) or the raw operand slots (ELIDED_BY_ADAPTER).
            List<String> args = new ArrayList<>();
            if (payload.parameterBoundaryMode() == ParameterBoundaryMode.RUN) {
                for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                    SemanticOp boundary = opsById.get(boundaryId);
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) boundary.payload();
                    emitBoundaryStart(boundary, slot(boundaryPayload.input()),
                        boundaryPayload.descriptor(), indent);
                    String checked = "__sa_" + boundary.opId().id();
                    out.append(indent(indent)).append("Object ").append(checked)
                        .append(" = ")
                        .append(bcheckArgs(boundaryPayload.descriptor(),
                            slot(boundaryPayload.input()))).append(";\n");
                    emitBoundarySuccess(boundary, checked,
                        boundaryPayload.descriptor(), indent);
                    args.add(checked);
                }
            } else {
                for (ValueId operand : op.operands()) {
                    args.add(slot(operand));
                }
            }
            if (payload.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                // The dynamic async start (ISSUE-0658): the class of the
                // resolved carrier selects the task source.
                emitDynamicAsyncStart(op, payload, dynamic, token, args, indent);
                emitTokenSuccess(op, javaString(tokenAtom(token)), indent);
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
                    LoweredFunction function = functionOf(body.functionId());
                    List<BindingGeneration> captures = function == null
                        ? List.of() : function.captures();
                    StringBuilder caps = new StringBuilder();
                    for (BindingGeneration capture : captures) {
                        if (caps.length() > 0) {
                            caps.append(", ");
                        }
                        caps.append(captureArg(capture));
                    }
                    out.append(indent(indent)).append("JvmRuntime.startBodyTask(")
                        .append(token.tokenId()).append(", \"DEAL_BODY_TASK\", () -> {\n");
                    out.append(indent(indent + 1)).append("String __prevM = "
                        + "JvmRuntime.currentModule();\n");
                    out.append(indent(indent + 1)).append("JvmRuntime.setModule(MODULE);\n");
                    out.append(indent(indent + 1)).append("JvmRuntime.pushFrame(")
                        .append(javaString(String.valueOf(body.functionId().id())))
                        .append(");\n");
                    out.append(indent(indent + 1)).append("try {\n");
                    out.append(indent(indent + 2)).append("return ")
                        .append(fnFactory(body.functionId())).append("(").append(caps)
                        .append(").fn.invoke(new Object[]{")
                        .append(String.join(", ", args)).append("});\n");
                    out.append(indent(indent + 1)).append("} finally {\n");
                    out.append(indent(indent + 2)).append("JvmRuntime.popFrame();\n");
                    out.append(indent(indent + 2)).append("JvmRuntime.setModule(__prevM);\n");
                    out.append(indent(indent + 1)).append("}\n");
                    out.append(indent(indent)).append("});\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    // The outer adapter-over-async task (zero return
                    // boundaries of its own): the D15 source resolution
                    // and source-signature check, then the nested source
                    // op's full emission (its task queues under the FIFO
                    // drain — the outer task completes after it).
                    SemanticOp nested = nestedAsyncStartOf(op);
                    out.append(indent(indent)).append("JvmRuntime.startBodyTask(")
                        .append(token.tokenId()).append(", \"DEAL_BODY_TASK\", () -> {\n");
                    out.append(indent(indent + 1)).append("Object __src = "
                        + "JvmRuntime.adapterSource((JvmRuntime.AdapterValue) ")
                        .append(slot((ValueId) opsById.get(adapter.adaptOpId()).result()))
                        .append(");\n");
                    out.append(indent(indent + 1)).append("JvmRuntime.fnCheck(__src, ")
                        .append(javaString(adapter.sourceSignature().canonicalSpecText()))
                        .append(", ").append(javaString(originOf(op))).append(");\n");
                    emitAsyncStart(nested, indent + 1);
                    out.append(indent(indent + 1)).append("return null;\n");
                    out.append(indent(indent)).append("});\n");
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    if (hostAbi == null) {
                        // A unit/surface-less session is the scenario drive:
                        // its async host path is the landed deterministic
                        // seam, which the production path never reaches.
                        emitAsyncHostSeamStart(op, indent, token,
                            host.hostModuleId().path(), host.exportName(), args);
                    } else {
                        emitAsyncHostStart(op, indent, token, host.hostModuleId(),
                            host.exportName(), args);
                    }
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    if (hostAbi == null) {
                        emitAsyncHostSeamStart(op, indent, token,
                            hostValue.hostModuleId().path(),
                            "@value#" + hostValue.materializingBoundaryOpId().id(), args);
                    } else {
                        emitAsyncHostValueStart(op, indent, token, hostValue, args);
                    }
                }
                case FunctionExecutionBinding.ExternalFunction external ->
                    emitAsyncExternalStart(op, indent, token, payload.externalAsyncLink(),
                        args);
                case FunctionExecutionBinding.IntrinsicFunction intrinsic -> {
                    // The intrinsic's async form (ISSUE-0680; design source
                    // {@code conversion-intrinsic-function-values} J3: the
                    // conversion intrinsics are synchronous values, so an
                    // async use is a checker rejection — this arm is the
                    // deterministic closed treatment of a doctored site): the
                    // closed DEAL_BODY task runs the one conversion ladder
                    // inside the task body with this op's context and kind
                    // over the recorded argument carrier and completes
                    // immediately with the converted value; the single AWAIT
                    // runs the landed ASYNC_COMPLETION cell on the completion
                    // (zero return boundaries).
                    if (args.size() != intrinsic.descriptor().paramTypes().size()) {
                        throw new IllegalStateException("ASYNC_START " + op.opId()
                            + " carries " + args.size() + " argument(s) for the '"
                            + intrinsic.kind() + "' intrinsic's "
                            + intrinsic.descriptor().paramTypes().size()
                            + " declared parameter(s) (producer defect)");
                    }
                    out.append(indent(indent)).append("JvmRuntime.startBodyTask(")
                        .append(token.tokenId())
                        .append(", \"DEAL_BODY_TASK\", () -> ")
                        .append(intrinsic.kind() == IntrinsicKind.INT_CONVERT
                            ? "JvmRuntime.intConv(" : "JvmRuntime.numConv(")
                        .append(args.get(0)).append(", ")
                        .append(javaString(op.kind().name())).append(", ")
                        .append(javaString(staticKind(
                            intrinsic.descriptor().paramTypes().get(0))))
                        .append(", ").append(intrinsicContextArgs(op))
                        .append("));\n");
                }
                case FunctionExecutionBinding.DynamicFunctionValue dynamic ->
                    throw new IllegalStateException("ASYNC_START " + op.opId()
                        + " resolves the dynamic function value produced by "
                        + dynamic.materializingOpId() + " outside the dynamic arm (a "
                        + "DynamicFunctionValue names no execution class and is never a "
                        + "statically resolved callee — producer defect)");
            }
            emitTokenSuccess(op, javaString(tokenAtom(token)), indent);
        }

        /**
         * The scenario-drive {@code ASYNC_START(HOST)} terminal (the landed
         * shape): the deterministic seam start plus the bad-handle check.
         * Emitted only by a session without the compile's host ABI emission
         * surface (a unit/surface-less session); the production and
         * trace-mode project sessions take the operation-handle arm.
         */
        private void emitAsyncHostSeamStart(SemanticOp op, int indent,
                                            AsyncTokenId token, String module,
                                            String export, List<String> args) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            String label = payload.hostOperationLabel();
            out.append(indent(indent)).append("JvmRuntime.effect(\"ASYNC_START_OP\", ")
                .append(javaString(label)).append(");\n");
            out.append(indent(indent)).append("if (JvmRuntime.HOST_ASYNC == null) {\n");
            out.append(indent(indent + 1))
                .append("throw new IllegalStateException(\"an async host start has no "
                    + "deterministic host seam (the scenario host drives it)\");\n");
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("String __bound = "
                + "JvmRuntime.HOST_ASYNC.startAsync(")
                .append(javaString(module)).append(", ").append(javaString(export))
                .append(", ").append(javaString(label)).append(", new Object[]{")
                .append(String.join(", ", args)).append("});\n");
            out.append(indent(indent)).append("if (__bound == null) {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.DealError __e = "
                + "JvmRuntime.fail(\"E8010\", \"async operation mismatch: expected "
                + "async-operation, got nothing\", ")
                .append(javaString(originOf(op)))
                .append(", \"async-operation\", \"nothing\");\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(__e)",
                indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("JvmRuntime.startHostTask(")
                .append(token.tokenId()).append(", ").append(javaString(label))
                .append(");\n");
        }

        /**
         * The ASYNC_START(HOST) terminal (ISSUE-0652;
         * {@code host-module-load-and-host-call-realization} H4 and the
         * async host start and completion contract): the loaded surface
         * entry is invoked through the emitted per-export wrapper — the
         * same host-boundary call shape as the sync arm, with the call
         * origin triplet — whose declared-async shape check realizes the
         * op's {@code ASYNC_OPERATION_HANDLE} terminal with the pinned
         * E8010 {@code host async function must return an async operation,
         * got {actual}} at the call origin, and the returned operation
         * handle is bound to the canonical token through the production
         * {@code startHostTask(tokenId, label, operation)} registration.
         * The wrapper returns the handle instead of joining it (the shared
         * {@code AWAIT} machine owns the token and the single completion
         * boundary), and the deterministic {@code JvmRuntime.HOST_ASYNC}
         * seam is never referenced on the production path.
         */
        private void emitAsyncHostStart(SemanticOp op, int indent, AsyncTokenId token,
                                        ModuleId moduleId, String exportName,
                                        List<String> args) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            String label = payload.hostOperationLabel();
            if (hostAbi == null) {
                throw new IllegalStateException("ASYNC_START " + op.opId()
                    + " resolves the host export '" + moduleId.path() + "."
                    + exportName + "' but the session carries no host ABI emission"
                    + " surface (a producer defect; only the production project"
                    + " entry carries the compile's declaration surface)");
            }
            String wrapper = hostAbi.requireWrapper(moduleId.path(), exportName);
            StringBuilder call = new StringBuilder(wrapper).append('(');
            for (String arg : args) {
                call.append(arg).append(", ");
            }
            call.append(originArgs(op)).append(')');
            emitAsyncHostOperation(op, indent, token, label, call.toString());
        }

        /**
         * The {@code HostFunctionValue} async arm: the value materialized
         * at its producing host crossing is invoked through the production
         * function carrier the crossing's declared-return projection
         * published (the surface entry's own bridging wrapper), whose
         * declared-async shape check carries the pinned projection — the
         * same route as the sync{\@code HostFunctionValue} arm.
         */
        private void emitAsyncHostValueStart(SemanticOp op, int indent,
                                             AsyncTokenId token,
                                             FunctionExecutionBinding.HostFunctionValue hostValue,
                                             List<String> args) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            String label = payload.hostOperationLabel();
            if (hostAbi == null) {
                throw new IllegalStateException("ASYNC_START " + op.opId()
                    + " resolves the host-materialized function value of module '"
                    + hostValue.hostModuleId().path() + "' but the session carries"
                    + " no host ABI emission surface (a producer defect)");
            }
            SemanticOp crossing = opsById.get(hostValue.materializingBoundaryOpId());
            if (crossing == null
                    || !(crossing.payload() instanceof KindPayload.BoundaryPayload boundary)) {
                throw new IllegalStateException("ASYNC_START " + op.opId()
                    + " names the materializing host crossing "
                    + hostValue.materializingBoundaryOpId()
                    + ", which is not a boundary op of the emitted closure"
                    + " (a producer defect)");
            }
            StringBuilder call = new StringBuilder("((JvmRuntime.FunctionValue) ")
                .append(slot(boundary.input()))
                .append(").fn.invoke(new java.lang.Object[]{ ");
            for (int i = 0; i < args.size(); i++) {
                if (i > 0) {
                    call.append(", ");
                }
                call.append(args.get(i));
            }
            call.append(" })");
            emitAsyncHostOperation(op, indent, token, label, call.toString());
        }

        /**
         * The shared invocation half of one async host start: the
         * declared-async shape check (inside the emitted wrapper) under the
         * op's own failure path, then the operation handle bound to the
         * canonical token through the production host-task registration.
         */
        private void emitAsyncHostOperation(SemanticOp op, int indent,
                                            AsyncTokenId token, String label,
                                            String invocation) {
            out.append(indent(indent)).append("JvmRuntime.effect(\"ASYNC_START_OP\", ")
                .append(javaString(label)).append(");\n");
            String handle = "__ha_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(handle)
                .append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(handle).append(" = ")
                .append(invocation).append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__e)", indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("}\n");
            out.append(indent(indent)).append("JvmRuntime.startHostTask(")
                .append(token.tokenId()).append(", ").append(javaString(label))
                .append(", ").append(handle).append(");\n");
        }

        /**
         * The ASYNC_START(EXTERNAL) terminal: the callee unit's
         * async-entry dispatch inside the one artifact (ISSUE-0655,
         * {@code cross-module-call-realization} X2). A project session
         * emits the local method reference — one {@code ae<entry op id>}
         * method per async entry op lives in the one production class, the
         * callee token id is the entry op's id by construction, and no
         * per-module {@code SharedM} class is referenced — and resolves
         * the link against the emitted async-entry set, failing closed
         * when it names no entry. A single-unit session keeps the landed
         * cross-class reference: the callee unit's own artifact is a
         * sibling class of the same multi-artifact drive and carries the
         * entry method. The caller passes the drive flag false (its AWAIT
         * drains).
         */
        private void emitAsyncExternalStart(SemanticOp op, int indent, AsyncTokenId token,
                                            ExternalAsyncLink link, List<String> args) {
            if (link == null) {
                throw new IllegalStateException("ASYNC_START(EXTERNAL) without "
                    + "its ExternalAsyncLink (producer defect)");
            }
            if (projectSession) {
                // The one production class carries the entry method: the
                // reference resolves locally (and fails closed when the
                // link names no emitted entry).
                resolveExternalAsyncEntry(op, link);
                out.append(indent(indent)).append("ae")
                    .append(link.calleeTokenId().tokenId()).append("(")
                    .append(javaString(opKey(op.opId())))
                    .append(", false, new Object[]{")
                    .append(String.join(", ", args)).append("});\n");
            } else {
                out.append(indent(indent))
                    .append(sharedClassName(link.calleeModuleId().path()))
                    .append(".ae").append(link.calleeTokenId().tokenId()).append("(")
                    .append(javaString(opKey(op.opId())))
                    .append(", false, new Object[]{")
                    .append(String.join(", ", args)).append("});\n");
            }
        }

        /**
         * The callee unit's recorded async {@code EXTERNAL_ENTRY} of one
         * {@code ASYNC_START(EXTERNAL)}: resolved by the link's canonical
         * token (the entry op's own id by construction) inside the callee
         * module's unit. A missing module outside the session's closure, a
         * token naming no op, a non-entry op, a sync entry, or a divergent
         * export name is a fail-closed producer defect — the emitted
         * local method reference would otherwise name no method of the
         * artifact.
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
         * FIFO drain first (the serial executor's join), then the
         * canonical referent's completion. A production host operation
         * joins its registered operation and never reads the seam; a
         * seam-registered host operation completes through the host seam
         * (the ordered ASYNC_COMPLETE_* effects); a failed operation
         * publishes the identical error — never a re-check or a
         * synthesized copy — and a completed value crosses the single
         * {@code ASYNC_COMPLETION} boundary at the await site (a boundary
         * failure is re-originated at that site and publishes the
         * boundary's FAILURE beside the await op's, exactly the oracle's
         * boundary-child pair).
         */
        private void emitAwait(SemanticOp op, int indent) {
            KindPayload.AwaitPayload payload = (KindPayload.AwaitPayload) op.payload();
            long canonicalId = canonicalReferent(payload.token());
            SemanticOp boundary = opsById.get(payload.completionBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitStart(op, indent);
            String awaited = "__av_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(awaited)
                .append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(awaited)
                .append(" = JvmRuntime.awaitTask(")
                .append(canonicalId).append(", ").append(javaString(originOf(op)))
                .append(");\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(__e)",
                indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("}\n");
            // The single ASYNC_COMPLETION boundary at the await site: a
            // host completion atomizes by its runtime carrier; a DEAL
            // body value atomizes by the declared descriptor.
            if (canonicalOwnerOf(payload.token()) == AsyncTokenOwner.HOST_OPERATION) {
                emitBoundaryStartAtom(boundary, "JvmRuntime.hostAtom(" + awaited + ")",
                    indent);
            } else {
                emitBoundaryStart(boundary, awaited, boundaryPayload.descriptor(),
                    indent);
            }
            String checked = "__avc_" + op.opId().id();
            out.append(indent(indent)).append("Object ").append(checked).append(";\n");
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append(checked).append(" = ")
                .append(bcheckCompletionArgs(boundaryPayload.descriptor(), awaited))
                .append(";\n");
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __be) {\n");
            out.append(indent(indent + 1)).append("JvmRuntime.DealError __bre = new "
                + "JvmRuntime.DealError(__be.code, __be.msg, ")
                .append(javaString(originOf(boundary)))
                .append(", __be.expected, __be.actual, __be.frames, null);\n");
            emitFailureEvent(boundary.opId(), "BOUNDARY", boundary,
                "JvmRuntime.errtext(__bre)", indent + 1);
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__bre)", indent + 1);
            out.append(indent(indent + 1)).append("throw __bre;\n");
            out.append(indent(indent)).append("}\n");
            emitBoundarySuccess(boundary, checked, boundaryPayload.descriptor(),
                indent);
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = ").append(checked).append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The async EXTERNAL_ENTRY dispatch entry (the E6 dispatch-entry
         * pattern; ISSUE-0655, {@code cross-module-call-realization} X2
         * and the cross-module async call contract): the scenario host
         * adapter invokes it top-level with scripted arguments (drive
         * flag on — the entry drains and returns the completion), and a
         * cross-module caller invokes it with the drive flag off (its
         * AWAIT drains). One entry exists per async export of every
         * closure unit, emitted as the local static method
         * {@code ae<entry op id>} of the one production class; the entry
         * resolves its function and its capture cells through its own
         * unit. It emits the callee record's START/SUCCESS under the
         * passed parent key and creates exactly one canonical task
         * wrapping the entry function's body-task future under the
         * owning module's context (the per-entry module literal), with
         * the module restored on every path.
         */
        private void emitAsyncEntry(SemanticOp op, int indent,
                                    LoweredModuleUnit owner) {
            KindPayload.ExternalEntryPayload payload =
                (KindPayload.ExternalEntryPayload) op.payload();
            LoweredFunction function = owner.functions().get(payload.function());
            List<BindingGeneration> captures = function == null
                ? List.of() : function.captures();
            StringBuilder caps = new StringBuilder();
            for (BindingGeneration capture : captures) {
                if (caps.length() > 0) {
                    caps.append(", ");
                }
                caps.append(captureArg(capture));
            }
            String ownerPath = owner.moduleId().path();
            out.append(indent(indent)).append("public static Object ae")
                .append(op.opId().id())
                .append("(String __parent, boolean __drive, Object[] __args) {\n");
            if (trace) {
                // The entry's own events pass the owning module literal:
                // a cross-module caller invokes the entry from the
                // caller's context and the shared mutable MODULE would
                // otherwise tag the entry's events with the caller's
                // module.
                out.append(indent(indent + 1)).append("JvmRuntime.ev(")
                    .append(javaString(ownerPath)).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest()))
                    .append(", __parent, List.of(), null, null);\n");
            }
            out.append(indent(indent + 1)).append("JvmRuntime.startBodyTask(")
                .append(op.opId().id()).append(", \"DEAL_BODY_TASK\", () -> {\n");
            out.append(indent(indent + 2)).append("String __prevM = "
                + "JvmRuntime.currentModule();\n");
            out.append(indent(indent + 2)).append("String __prevModule = MODULE;\n");
            out.append(indent(indent + 2)).append("MODULE = ")
                .append(javaString(ownerPath)).append(";\n");
            out.append(indent(indent + 2)).append("JvmRuntime.setModule(MODULE);\n");
            out.append(indent(indent + 2)).append("JvmRuntime.pushFrame(")
                .append(javaString(String.valueOf(payload.function().id())))
                .append(");\n");
            out.append(indent(indent + 2)).append("try {\n");
            out.append(indent(indent + 3)).append("return ")
                .append(fnFactory(payload.function())).append("(").append(caps)
                .append(").fn.invoke(__args);\n");
            out.append(indent(indent + 2)).append("} finally {\n");
            out.append(indent(indent + 3)).append("JvmRuntime.popFrame();\n");
            out.append(indent(indent + 3)).append("MODULE = __prevModule;\n");
            out.append(indent(indent + 3)).append("JvmRuntime.setModule(__prevM);\n");
            out.append(indent(indent + 2)).append("}\n");
            out.append(indent(indent + 1)).append("});\n");
            if (trace) {
                out.append(indent(indent + 1)).append("JvmRuntime.ev(")
                    .append(javaString(ownerPath)).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", \"SUCCESS\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest()))
                    .append(", __parent, List.of(), \"tok:").append(op.opId().id())
                    .append(":DEAL_BODY_TASK\", null);\n");
            }
            out.append(indent(indent + 1)).append("if (__drive) {\n");
            out.append(indent(indent + 2)).append("return JvmRuntime.awaitTask(")
                .append(op.opId().id()).append(", ")
                .append(javaString(originOf(op))).append(");\n");
            out.append(indent(indent + 1)).append("}\n");
            out.append(indent(indent + 1)).append("return null;\n");
            out.append(indent(indent)).append("}\n");
        }

        /**
         * ENTRY_INVOKE — delegates exactly one CALL(DIRECT) to main
         * (its owned child) and exits after the terminal. A delegated
         * failure publishes the ENTRY_INVOKE FAILURE terminal (the oracle's
         * own projection) before the error propagates to the module-init
         * wrapper's terminal.
         */
        private void emitEntryInvoke(SemanticOp op, int indent) {
            emitStart(op, indent);
            out.append(indent(indent)).append("try {\n");
            for (SemanticOp candidate : opsById.values()) {
                if (candidate.kind() == SemanticOpKind.CALL
                        && op.opId().equals(candidate.origin().parentOpId())) {
                    emitCall(candidate, indent + 1);
                }
            }
            out.append(indent(indent))
                .append("} catch (JvmRuntime.DealError __entryErr) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op,
                "JvmRuntime.errtext(__entryErr)", indent + 1);
            out.append(indent(indent)).append("  throw __entryErr;\n");
            out.append(indent(indent)).append("}\n");
            emitPlainSuccess(op, indent);
        }

        /**
         * {@code MODULE_IMPORT} — the import's load/initialization op
         * (ISSUE-0650; {@code host-module-load-and-host-call-realization}
         * H1/H2 item 1): a {@code HOST}-kind import calls its module-keyed
         * load entry from its position in the module init walk with the
         * import statement's origin, so the landed E8011 defects carry the
         * import origin and a second alias of one host module binds
         * nothing new (the entry is idempotent per module).
         * {@code COMPILED}/{@code STDLIB} imports keep the landed no-op
         * load realization: their surface entry is the module's own
         * publication (its {@code EXPORT_PUBLISH} writes, or the chunk-top
         * cataloged-callable population).</p>
         *
         * <p><b>The completion write (K15 items 1-2).</b> After the
         * kind-specific load the op's payload {@code aliasCells} receive
         * the module's namespace value — the module-identity-keyed
         * {@code JvmRuntime.EXPORT_SURFACES} entry through the one
         * {@code exportSurface} accessor, the surface object the module's
         * own publication or its single guarded load created, never a
         * per-alias re-derivation — so {@code let t = time} reads the very
         * table the direct read/publish arms use and two aliases of one
         * module observe the identical value. It is the alias cells'
         * single initializing write (an alias cell never carries a
         * {@code BINDING_INIT}); the cell-kind switch keeps the
         * {@code SHARED_CELL} in-place publication discipline.</p>
         */
        private void emitModuleImport(SemanticOp op, int indent) {
            KindPayload.ModuleImportPayload payload =
                (KindPayload.ModuleImportPayload) op.payload();
            emitStart(op, indent);
            if (payload.kind() == deal.semantic.ir.ModuleImportKind.HOST
                    && hostAbi != null) {
                // The host load is the production/trace project session's
                // realization; a unit session or a host-free project
                // session (no host ABI surface) keeps the landed no-op arm
                // — its host path is the landed scenario seam, which the
                // production path never reaches (ISSUE-0651: the
                // host-aware trace project entry carries the surface too,
                // so the oracle-agreement drive loads the same surface).
                SourceSpan span = op.origin().span();
                if (span == null) {
                    throw new IllegalStateException("the host import " + op.opId()
                        + " carries no source span: the pinned E8011 origin"
                        + " needs the import statement's own origin (a producer"
                        + " defect)");
                }
                out.append(indent(indent))
                    .append(JvmHostAbiEmission.loadEntry(JvmHostAbiEmission.key(
                        payload.resolvedModule().path())))
                    .append('(').append(javaString(op.origin().sourceId()))
                    .append(", ").append(span.startLine()).append(", ")
                    .append(span.startColumn()).append(");\n");
            }
            emitAliasCellCompletion(payload, indent);
            emitPlainSuccess(op, indent);
        }

        /**
         * The {@code MODULE_IMPORT} completion write (K15 item 2): every
         * alias cell named by the payload receives the module's namespace
         * value — the module-identity-keyed surface through the one
         * {@code exportSurface} accessor, the one surface object the
         * module's publication or its single load created — in the cell's
         * own publication discipline. The write runs after the
         * kind-specific load, so a HOST/FFI alias holds the loaded table.
         */
        private void emitAliasCellCompletion(KindPayload.ModuleImportPayload payload,
                                             int indent) {
            if (payload.aliasCells().isEmpty()) {
                return;
            }
            String surface = "exportSurface("
                + javaString(payload.resolvedModule().path()) + ")";
            for (BindingId aliasCell : payload.aliasCells()) {
                BindingCellKind kind = cellKindOf(aliasCell, 0);
                if (kind == BindingCellKind.SHARED_CELL) {
                    out.append(indent(indent)).append("((Object[]) ")
                        .append(cell(aliasCell, 0)).append(")[0] = ")
                        .append(surface).append(";\n");
                } else {
                    out.append(indent(indent)).append(cell(aliasCell, 0))
                        .append(" = ").append(surface).append(";\n");
                }
            }
        }

        /**
         * The cataloged callable surfaces of the session's STDLIB imports
         * (M4/K15 item 1): one surface entry per catalog row of every
         * imported STDLIB module, in catalog order, created through the one
         * memoized accessor ({@code JvmRuntime.stdlibCallable}) — the
         * whole-surface population and the read resolve the identical
         * carrier per row, and the surface is written only by this
         * session-scoped catalog memoization (never re-derived per read).
         */
        private void emitStdlibSurfacePopulation(int indent) {
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
                for (StdlibFunctionCatalog.Entry row : rows) {
                    out.append(indent(indent)).append("exportSurface(")
                        .append(javaString(modulePath)).append(").write(")
                        .append(javaString(row.exportName()))
                        .append(", JvmRuntime.stdlibCallable(")
                        .append(stdlibRowArgs(row)).append("));\n");
                }
            }
        }

        /**
         * The closed catalog rows of one imported stdlib module, in catalog
         * order (the pinned declaration order of the one catalog authority);
         * an unimported or unknown module has none.
         */
        private static List<StdlibFunctionCatalog.Entry> stdlibRowsOf(String modulePath) {
            List<StdlibFunctionCatalog.Entry> rows = new java.util.ArrayList<>();
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
         * ({@code JvmRuntime.stdlibCallable(module, name, rowTag, signature,
         * spec)}): the row's declared descriptor text and its canonical spec
         * text — the row's declared signature, never the reading site's.
         */
        private static String stdlibRowArgs(StdlibFunctionCatalog.Entry row) {
            return javaString(row.modulePath()) + ", " + javaString(row.exportName())
                + ", " + javaString(row.function().name()) + ", "
                + javaString(descriptorText(row.declaredDescriptor())) + ", "
                + javaString(row.declaredDescriptor().canonicalSpecText());
        }

        /**
         * {@code EXPORT_READ} — the per-kind read resolution (M2/M4/M5/M6):
         * the read is the uniform program-scoped surface lookup
         * {@code exportSurface(module).read(name)} for a COMPILED read
         * (whose stored entry is the owner's published
         * {@code JvmRuntime.FunctionValue} carrier — the identical object
         * for every read of one export in one program) and for a HOST/FFI
         * read (whose stored entry is the loaded module table's entry),
         * whose landed {@code Table.read} projects
         * {@code JvmRuntime.MISSING} for an absent key; a STDLIB read
         * publishes the in-target cataloged callable of the closed catalog
         * row (the one memoized carrier per row per module per program —
         * the identical object the whole-surface population writes,
         * carrying the row's declared signature and canonical spec text); a
         * read whose unit records no import fact keeps the residual kind
         * arm's memoized intrinsic carrier. The emitted read expression is
         * identical in trace
         * and production mode. In a project session a COMPILED read whose
         * owner module is not among the closure's units is a producer
         * defect and fails the emission closed; a per-unit session never
         * fails closed for a foreign owner (the owner's own class
         * publishes the surface of the same program).
         */
        private void emitExportRead(SemanticOp op, int indent) {
            KindPayload.ExportReadPayload payload =
                (KindPayload.ExportReadPayload) op.payload();
            // The read's module kind is the session's own recorded import
            // fact (M6). A module the session records no import fact for —
            // the test-only class-core carrier sessions, whose units carry
            // no module-level import op — keeps the landed interim
            // realization (the residual kind arm's memoized intrinsic
            // carrier); the production and
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
            emitStart(op, indent);
            out.append(indent(indent)).append(slot((ValueId) op.result()));
            if (kind == ModuleImportKind.COMPILED || kind == ModuleImportKind.HOST) {
                out.append(" = exportSurface(")
                    .append(javaString(payload.module().path())).append(").read(")
                    .append(javaString(payload.name())).append(");\n");
            } else if (kind == ModuleImportKind.STDLIB) {
                // The read publishes the catalog row's callable carrier
                // itself (M4): the memoized accessor the whole-surface
                // population uses, so the read and the surface hold the
                // identical object and the read never builds a per-read
                // value.
                out.append(" = JvmRuntime.stdlibCallable(")
                    .append(stdlibRowArgs(stdlibRowOf(payload.module().path(),
                        payload.name()))).append(");\n");
            } else {
                // The residual kind arm (a session whose unit records no
                // import fact for the read's module): the placeholder
                // publishes the memoized intrinsic carrier the identity's
                // own registration resolves, and a fresh opaque export
                // carrier otherwise (the landed per-read allocation, now a
                // real carrier surface) — never the removed marker and
                // never a re-read of the read's own slot.
                String carrier = registeredIntrinsicCarrierExpr((ValueId) op.result());
                out.append(" = ")
                    .append(carrier == null ? exportPlaceholderCarrier() : carrier)
                    .append(";\n");
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }
    }
}
