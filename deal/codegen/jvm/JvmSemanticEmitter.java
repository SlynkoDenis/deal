package deal.codegen.jvm;

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
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
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
        final Map<OpId, SemanticOp> opsById = new HashMap<>();
        final Map<BindingId, BindingCellKind> cellKinds = new HashMap<>();
        /**
         * Each op's owning module (the export-surface key): the module
         * whose unit carries the op, statically known at emission — the
         * surface key is the emitting module's identity, never a path
         * guess.
         */
        final Map<OpId, ModuleId> opModule = new HashMap<>();
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
            // A single-unit session never carries the host ABI emission
            // surface: the surface is emitted once per production project
            // artifact, and a unit session has no declaration surface.
            this.hostAbi = null;
            if (className != null) {
                this.className = className;
            } else {
                this.className = sharedClassName(unit.moduleId().path());
            }
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
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                String className) {
            this(project, tables, registries, trace, className, null);
        }

        /**
         * The project-mode session of the production project entry: the
         * combined closure plus the compile's host declaration surface
         * (the JVM host ABI emission surface). A trace-mode or unit
         * session carries no host surface (the host ABI emission surface
         * is a production realization).
         */
        Session(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                Map<ModuleId, ClassFactoryRegistry> registries, boolean trace,
                String className, HostDeclarationSurface hostSurface) {
            this.hostAbi = hostSurface == null ? null
                : new JvmHostAbiEmission(JvmHostAbiEmission.collect(
                    project, hostSurface));
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
            this.className = className != null ? className
                : sharedClassName(this.unit.moduleId().path());
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
            out.append("\n  static JvmRuntime.Table exportSurface(String module) {\n");
            out.append("    return JvmRuntime.exportSurface(module);\n");
            out.append("  }\n");
            // Slots and cells (every module; ids are globally unique).
            java.util.LinkedHashSet<String> fields = new java.util.LinkedHashSet<>();
            for (LoweredModuleUnit moduleUnit : units.values()) {
                for (SemanticOp op : moduleUnit.ops()) {
                    if (op.result() instanceof ValueId valueId) {
                        fields.add(slot(valueId));
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
            // EXTERNAL_ENTRY): one per-unit static entry per recorded
            // async export — the scenario host adapter's invocation
            // surface (the E6 dispatch-entry pattern). The entry creates
            // the callee's canonical task; the drive flag makes the
            // top-level scenario invocation drain it and return the
            // completion, while a cross-module caller passes the drive
            // flag false (its AWAIT drains).
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                        && ((KindPayload.ExternalEntryPayload) op.payload()).async()) {
                    emitAsyncEntry(op, 1);
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
            List<BindingId> captures = function.captures();
            StringBuilder params = new StringBuilder();
            for (BindingId captureId : captures) {
                if (params.length() > 0) {
                    params.append(", ");
                }
                params.append("Object c" + captureId.id());
            }
            out.append("  static JvmRuntime.FunctionValue ").append(fnFactory(functionId))
                .append('(').append(params).append(") {\n");
            out.append("    return new JvmRuntime.FunctionValue(args -> {\n");
            List<OpId> bodyOps = tableOfFunction(function).blockOps().get(function.body());
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

        /** The structure ancestors of a block, innermost first (static). */
        private List<SemanticOp> structureAncestors(BlockId block) {
            List<SemanticOp> result = new ArrayList<>();
            BlockId current = block;
            while (current != null) {
                SemanticOp enclosing = structureReferencing(current);
                if (enclosing == null) {
                    break;
                }
                result.add(enclosing);
                current = table.opBlocks().get(enclosing.opId());
            }
            return result;
        }

        /** Emits the transfer closures of the ancestors down to (and including)
         *  the target loop; stops at an enclosing TRY_CATCH when requested
         *  (its dispatch closes it). */
        private void emitTransferClosures(SemanticOp transferOp, SemanticOp targetLoop,
                                          boolean stopAtTry, int indent) {
            BlockId block = table.opBlocks().get(transferOp.opId());
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
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(payload.elementDescriptor())))
                    .append(", ")
                    .append(javaString(staticKind(payload.elementDescriptor())))
                    .append(", ").append(slot(input)).append(");\n");
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
            out.append(indent(indent)).append(slot((ValueId) op.result()))
                .append(" = Long.valueOf(((").append("JvmRuntime.Array) ")
                .append(slot(payload.arrayValue())).append(").length);\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
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
                out.append(indent(indent)).append("    __mr_")
                    .append(boundary.opId().id()).append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(");\n");
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
                emitBoundarySuccess(boundary, target, boundaryPayload.descriptor(), indent);
                emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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
                String checkedName = "__orb_" + boundary.opId().id();
                String errorName = "__obe_" + boundary.opId().id();
                String rebuiltName = "__obe2_" + boundary.opId().id();
                out.append(indent(indent)).append("try {\n");
                out.append(indent(indent + 1)).append("Object ").append(checkedName)
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(");\n");
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
                emitBoundarySuccess(boundary, target, boundaryPayload.descriptor(), indent);
            }
            emitResultSuccess(op, target, (RuntimeDescriptor) op.resultType(), indent);
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
                .append(" = JvmRuntime.bcheck(")
                .append(javaString(descriptorText(payload.descriptor()))).append(", ")
                .append(javaString(staticKind(payload.descriptor()))).append(", ")
                .append(inputExpr).append(");\n");
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
                .append(javaString(descriptorText(inner))).append(", (JvmRuntime.Array) ")
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

        /** A free BOUNDARY op: the runtime check over the payload input. */
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
            out.append(indent(indent)).append("Object __fb_").append(op.opId().id())
                .append(" = JvmRuntime.bcheck(")
                .append(javaString(descriptorText(payload.descriptor()))).append(", ")
                .append(javaString(staticKind(payload.descriptor()))).append(", ")
                .append(slot(payload.input())).append(");\n");
            if (op.result() instanceof ValueId valueId) {
                out.append(indent(indent)).append(slot(valueId)).append(" = __fb_")
                    .append(op.opId().id()).append(";\n");
                emitBoundarySuccess(op, slot(valueId), payload.descriptor(), indent);
            } else {
                emitBoundarySuccess(op, "__fb_" + op.opId().id(), payload.descriptor(),
                    indent);
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
            switch (payload.cellKind()) {
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
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            String valueExpr = hasProducer(payload.value())
                ? slot(payload.value()) : "new JvmRuntime.Intrinsic()";
            if (kind == BindingCellKind.SHARED_CELL) {
                out.append(indent(indent)).append("((").append("Object[]) ")
                    .append(cell(payload.binding(), payload.generation())).append(")[0] = ")
                    .append(valueExpr).append(";\n");
            } else {
                out.append(indent(indent)).append(cell(payload.binding(), payload.generation())).append(" = ")
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

        private void emitBindingLoad(SemanticOp op, int indent) {
            KindPayload.BindingLoadPayload payload =
                (KindPayload.BindingLoadPayload) op.payload();
            emitStart(op, indent);
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            out.append(indent(indent)).append(slot((ValueId) op.result())).append(" = ")
                .append(kind == BindingCellKind.SHARED_CELL
                    ? "((Object[]) " + cell(payload.binding(), payload.generation()) + ")[0]"
                    : cell(payload.binding(), payload.generation()))
                .append(";\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        private void emitBindingStore(SemanticOp op, int indent) {
            KindPayload.BindingStorePayload payload =
                (KindPayload.BindingStorePayload) op.payload();
            emitStart(op, indent);
            BindingCellKind kind = cellKinds.getOrDefault(payload.binding(),
                BindingCellKind.DIRECT);
            if (kind == BindingCellKind.SHARED_CELL) {
                out.append(indent(indent)).append("((").append("Object[]) ")
                    .append(cell(payload.binding(), payload.generation())).append(")[0] = ")
                    .append(slot(payload.value())).append(";\n");
            } else {
                out.append(indent(indent)).append(cell(payload.binding(), payload.generation())).append(" = ")
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
            for (BindingId captureId : payload.captures()) {
                if (args.length() > 0) {
                    args.append(", ");
                }
                args.append(cell(captureId, 0));
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
            emitStart(op, indent);
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
                case AdaptSourceRef.Value value ->
                    out.append(", ")
                        .append(hasProducer(value.value()) ? slot(value.value())
                            : "new JvmRuntime.Intrinsic()")
                        .append(", null, null");
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
                    child, unit, structuralOwned)) {
                emitOp(producer, indent);
            }
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
                        .append(boundary.opId().id()).append(" = JvmRuntime.bcheck(")
                        .append(javaString(descriptorText(payload.descriptor())))
                        .append(", ")
                        .append(javaString(staticKind(payload.descriptor())))
                        .append(", ").append(input).append(");\n");
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
            for (OpId boundaryId : payload.parameterBoundaryOpIds()) {
                SemanticOp boundary = opsById.get(boundaryId);
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) boundary.payload();
                emitBoundaryStart(boundary, slot(boundaryPayload.input()),
                    boundaryPayload.descriptor(), indent);
                out.append(indent(indent)).append("Object __pb_").append(boundary.opId().id())
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(slot(boundaryPayload.input())).append(");\n");
                emitBoundarySuccess(boundary, "__pb_" + boundary.opId().id(),
                    boundaryPayload.descriptor(), indent);
            }
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    FunctionId callee = body.functionId();
                    out.append(indent(indent)).append("JvmRuntime.pushFrame(")
                        .append(javaString(String.valueOf(callee.id()))).append(");\n");
                    out.append(indent(indent)).append("try {\n");
                    out.append(indent(indent)).append("  ")
                        .append(slot((ValueId) op.result()))
                        .append(" = ").append(fnFactory(callee)).append("(");
                    deal.semantic.ir.LoweredFunction calleeFunction =
                        unit.functions().get(callee);
                    List<deal.semantic.ir.BindingId> captures = calleeFunction == null
                        ? List.of() : calleeFunction.captures();
                    for (int i = 0; i < captures.size(); i++) {
                        if (i > 0) {
                            out.append(", ");
                        }
                        out.append(cell(captures.get(i), 0));
                    }
                    out.append(").fn.invoke(new Object[]{");
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
                    out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
                    emitFailureEvent(op.opId(), op.kind().name(), op,
                        "JvmRuntime.errtext(__e)", indent + 1);
                    out.append(indent(indent)).append("  throw __e;\n");
                    out.append(indent(indent)).append("} finally {\n");
                    out.append(indent(indent)).append("  JvmRuntime.popFrame();\n");
                    out.append(indent(indent)).append("}\n");
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    // The D15 invocation protocol: resolve the source per
                    // the recorded capture mode, the source-signature
                    // check (E8010 at this CALL's origin), then the
                    // source invocation with the leading M arguments
                    // only — every N target-signature parameter boundary
                    // already ran above. The adapter protocol pushes the
                    // source body's frame itself; the identical
                    // completion error propagates unchanged.
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
                    out.append(indent(indent)).append("}\n");
                }
                default -> throw new IllegalStateException("CALL " + op.opId()
                    + " resolves a binding outside the statically-resolved slice: "
                    + binding);
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }

        /**
         * The statically resolved execution binding of one CALL: the
         * inline Static binding or the unit's registered binding of an
         * Indirect callee identity (the same registration the semantic
         * oracle re-resolves at execution). A Dynamic callee is the
         * runtime-resolution slice (ISSUE-0531) and fails closed here.
         */
        private FunctionExecutionBinding callBinding(KindPayload.CallPayload payload) {
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                case KindPayload.CallCallee.Indirect indirect ->
                    unit.functionBindings().get(
                        new deal.semantic.ir.FunctionAllocationIdentity(
                            indirect.callee().id()));
                case KindPayload.CallCallee.Dynamic ignored -> null;
            };
            if (binding == null) {
                throw new IllegalStateException("CALL " + payload
                    + " resolves no FunctionExecutionBinding (producer defect)");
            }
            return binding;
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
                case HOST_DEFAULTS, FFI_PLAN ->
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " carries defaultOwner " + payload.defaultOwner()
                        + ": the declaration-class owners are the project lowering's"
                        + " class registration seeds (ISSUE-0631) and their construction"
                        + " is not emitted in this slice — a fail-closed producer"
                        + " defect, never emitted");
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
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(");\n");
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
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(inputExpr).append(");\n");
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
                case INT_CONVERT -> out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.intConv(").append(input).append(", ")
                    .append(javaString(kind)).append(", ")
                    .append(javaString(opKey(op.opId()))).append(", ")
                    .append(javaString(op.contract().canonicalDigest())).append(", ")
                    .append(javaString(parentKey(op.origin().parentOpId()))).append(", ")
                    .append(javaString(origin)).append(");\n");
                case NUMBER_CONVERT -> out.append(indent(indent)).append(target)
                    .append(" = JvmRuntime.numConv(").append(input).append(", ")
                    .append(javaString(kind)).append(", ")
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
                    .append(boundary.opId().id()).append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(slot(boundaryPayload.input())).append(");\n");
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
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", ").append(target).append(");\n");
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
                        .append(" = __elem;\n");
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
                        .append(" = new String(Character.toChars(__cp));\n");
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
            out.append(indent(indent)).append("Object __rvc_").append(op.opId().id())
                .append(" = JvmRuntime.bcheck(")
                .append(javaString(descriptorText(boundaryPayload.descriptor())))
                .append(", ")
                .append(javaString(staticKind(boundaryPayload.descriptor())))
                .append(", __rv_").append(op.opId().id()).append(");\n");
            emitBoundarySuccess(boundary, "__rvc_" + op.opId().id(),
                boundaryPayload.descriptor(), indent);
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
                        .append(candidate.opId().id()).append(" = JvmRuntime.bcheck(")
                        .append(javaString(descriptorText(boundaryPayload.descriptor())))
                        .append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append(", ").append(slot(boundaryPayload.input()))
                        .append(");\n");
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
                    .append(" = JvmRuntime.bcheck(")
                    .append(javaString(descriptorText(boundaryPayload.descriptor())))
                    .append(", ")
                    .append(javaString(staticKind(boundaryPayload.descriptor())))
                    .append(", __args[").append(i).append("]);\n");
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
                        .append(" = JvmRuntime.bcheck(")
                        .append(javaString(descriptorText(boundaryPayload.descriptor())))
                        .append(", ")
                        .append(javaString(staticKind(boundaryPayload.descriptor())))
                        .append(", ").append(slot(boundaryPayload.input()))
                        .append(");\n");
                    emitBoundarySuccess(boundary, checked,
                        boundaryPayload.descriptor(), indent);
                    args.add(checked);
                }
            } else {
                for (ValueId operand : op.operands()) {
                    args.add(slot(operand));
                }
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
                case FunctionExecutionBinding.HostFunction host ->
                    emitAsyncHostStart(op, indent, token, host.hostModuleId().path(),
                        host.exportName(), args);
                case FunctionExecutionBinding.HostFunctionValue hostValue ->
                    emitAsyncHostStart(op, indent, token, hostValue.hostModuleId().path(),
                        "@value#" + hostValue.materializingBoundaryOpId().id(), args);
                case FunctionExecutionBinding.ExternalFunction external ->
                    emitAsyncExternalStart(op, indent, token, payload.externalAsyncLink(),
                        args);
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw new IllegalStateException("ASYNC_START " + op.opId()
                        + " resolves the intrinsic function carrier " + intrinsic.kind()
                        + " (the intrinsic carrier's async execution is the "
                        + "function-value child's; the conversion intrinsics are "
                        + "synchronous values — producer defect)");
            }
            emitTokenSuccess(op, javaString(tokenAtom(token)), indent);
        }

        /** The ASYNC_START(HOST) terminal: the seam start + the bad-handle check. */
        private void emitAsyncHostStart(SemanticOp op, int indent, AsyncTokenId token,
                                        String module, String export, List<String> args) {
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

        /** The ASYNC_START(EXTERNAL) terminal: the callee artifact's async-entry dispatch. */
        private void emitAsyncExternalStart(SemanticOp op, int indent, AsyncTokenId token,
                                            ExternalAsyncLink link, List<String> args) {
            if (link == null) {
                throw new IllegalStateException("ASYNC_START(EXTERNAL) without "
                    + "its ExternalAsyncLink (producer defect)");
            }
            out.append(indent(indent)).append(sharedClassName(link.calleeModuleId().path()))
                .append(".ae").append(link.calleeTokenId().tokenId()).append("(")
                .append(javaString(opKey(op.opId()))).append(", false, new Object[]{")
                .append(String.join(", ", args)).append("});\n");
        }

        /**
         * AWAIT — the completion position (D13 step 6): the deterministic
         * FIFO drain first (the serial executor's join), then the
         * canonical referent's completion. A pending host operation
         * completes through the host seam (the ordered ASYNC_COMPLETE_*
         * effects); a failed operation publishes the identical error —
         * never a re-check or a synthesized copy — and a completed value
         * crosses the single {@code ASYNC_COMPLETION} boundary at the
         * await site.
         */
        private void emitAwait(SemanticOp op, int indent) {
            KindPayload.AwaitPayload payload = (KindPayload.AwaitPayload) op.payload();
            long canonicalId = canonicalReferent(payload.token());
            SemanticOp boundary = opsById.get(payload.completionBoundaryOpId());
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundary.payload();
            emitStart(op, indent);
            out.append(indent(indent)).append("try {\n");
            out.append(indent(indent + 1)).append("Object __av = JvmRuntime.awaitTask(")
                .append(canonicalId).append(", ").append(javaString(originOf(op)))
                .append(");\n");
            // The single ASYNC_COMPLETION boundary at the await site: a
            // host-scripted completion atomizes by its runtime carrier; a
            // DEAL body value atomizes by the declared descriptor.
            if (canonicalOwnerOf(payload.token()) == AsyncTokenOwner.HOST_OPERATION) {
                emitBoundaryStartAtom(boundary, "JvmRuntime.hostAtom(__av)", indent + 1);
            } else {
                emitBoundaryStart(boundary, "__av", boundaryPayload.descriptor(),
                    indent + 1);
            }
            out.append(indent(indent + 1)).append("Object __avc = JvmRuntime.bcheck(")
                .append(javaString(descriptorText(boundaryPayload.descriptor())))
                .append(", ")
                .append(javaString(staticKind(boundaryPayload.descriptor())))
                .append(", __av);\n");
            emitBoundarySuccess(boundary, "__avc", boundaryPayload.descriptor(),
                indent + 1);
            out.append(indent(indent + 1)).append(slot((ValueId) op.result()))
                .append(" = __avc;\n");
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent + 1);
            out.append(indent(indent)).append("} catch (JvmRuntime.DealError __e) {\n");
            emitFailureEvent(op.opId(), op.kind().name(), op, "JvmRuntime.errtext(__e)",
                indent + 1);
            out.append(indent(indent + 1)).append("throw __e;\n");
            out.append(indent(indent)).append("}\n");
        }

        /**
         * The async EXTERNAL_ENTRY dispatch entry (the E6 dispatch-entry
         * pattern): the scenario host adapter invokes it top-level with
         * scripted arguments (drive flag on — the entry drains and
         * returns the completion), and a cross-module caller invokes it
         * with the drive flag off (its AWAIT drains). The entry emits the
         * callee record's START/SUCCESS under the passed parent key and
         * creates exactly one canonical task wrapping the entry function's
         * body-task future.
         */
        private void emitAsyncEntry(SemanticOp op, int indent) {
            KindPayload.ExternalEntryPayload payload =
                (KindPayload.ExternalEntryPayload) op.payload();
            LoweredFunction function = unit.functions().get(payload.function());
            List<BindingId> captures = function == null
                ? List.of() : function.captures();
            StringBuilder caps = new StringBuilder();
            for (BindingId captureId : captures) {
                if (caps.length() > 0) {
                    caps.append(", ");
                }
                caps.append(cell(captureId, 0));
            }
            out.append(indent(indent)).append("public static Object ae")
                .append(op.opId().id())
                .append("(String __parent, boolean __drive, Object[] __args) {\n");
            if (trace) {
                out.append(indent(indent + 1)).append("JvmRuntime.ev(MODULE, ")
                    .append(javaString(opKey(op.opId()))).append(", \"START\", ")
                    .append(javaString(op.kind().name())).append(", ")
                    .append(javaString(op.contract().canonicalDigest()))
                    .append(", __parent, List.of(), null, null);\n");
            }
            out.append(indent(indent + 1)).append("JvmRuntime.startBodyTask(")
                .append(op.opId().id()).append(", \"DEAL_BODY_TASK\", () -> {\n");
            out.append(indent(indent + 2)).append("String __prevM = "
                + "JvmRuntime.currentModule();\n");
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
            out.append(indent(indent + 3)).append("JvmRuntime.setModule(__prevM);\n");
            out.append(indent(indent + 2)).append("}\n");
            out.append(indent(indent + 1)).append("});\n");
            if (trace) {
                out.append(indent(indent + 1)).append("JvmRuntime.ev(MODULE, ")
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
         * realization.
         */
        private void emitModuleImport(SemanticOp op, int indent) {
            KindPayload.ModuleImportPayload payload =
                (KindPayload.ModuleImportPayload) op.payload();
            emitStart(op, indent);
            if (payload.kind() == deal.semantic.ir.ModuleImportKind.HOST
                    && hostAbi != null) {
                // The host load is a production project realization; a
                // unit/trace session (no host ABI surface) keeps the landed
                // no-op arm — its host path is the landed scenario seam,
                // which the production path never reaches.
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
            emitPlainSuccess(op, indent);
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
         * read whose unit records no import fact keeps the landed
         * placeholder. The emitted read expression is identical in trace
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
            // realization (the STDLIB placeholder); the production and
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
                out.append(" = new JvmRuntime.Intrinsic();\n");
            }
            emitResultSuccess(op, slot((ValueId) op.result()),
                (RuntimeDescriptor) op.resultType(), indent);
        }
    }
}
