package deal.semantic.ir;

import deal.diagnostics.CompilerDiagnostic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The namespace-registration production record of the project lowering
 * ({@code project-lowering-entry-and-registration-seeds} D8 and the
 * namespace registration contract; the recording half of
 * {@code semantic-ir-construct-coverage-cutover} K9 item 8/K15 items
 * 1-2):
 *
 * <pre>{@code
 * NamespaceRegistrations {
 *   registrations: Map<ModuleId, NamespaceRegistration>   // one entry per imported module
 * }
 * }</pre>
 *
 * <p><b>Cardinality by construction.</b> The map key is the module
 * identity, so exactly one entry exists per distinct resolved imported
 * module of the complete closure: a unit with two import declarations
 * resolving to one module contributes two cells to that module's single
 * entry and never creates a second entry. Map iteration order is the
 * assembly order — closure (dependency) order, then first-import
 * declaration order — so repeated assemblies of the same closure are
 * byte-identical in their typed surface.</p>
 *
 * <p><b>Recording surface only.</b> The registrations plus the
 * {@code MODULE_IMPORT} payload {@code aliasCells} are the whole
 * recording surface: no namespace-value op, no op result, and no new op
 * kind exist; the namespace value's creation stays with the namespace
 * children. Neither the unit text protocol nor the project manifest
 * carries the registrations (the alias cells are verified through the
 * {@code MODULE_IMPORT} payloads and this typed record).</p>
 *
 * <p><b>The recording-half assembly.</b> {@link #assemble} derives the
 * registrations from already-lowered units in closure order, enforcing
 * the payload discipline fail-closed: every named cell is an
 * import-alias allocation of its own unit, every import-alias allocation
 * is named by exactly one completion, no cell is named twice (including
 * under two modules), and every completion's {@link ModuleImportKind}
 * equals its entry's kind. {@code lowerProject} completes the same
 * record during its walk; this surface is the equivalent post-hoc
 * assembly over the lowered units.</p>
 *
 * <p><b>Read-only once assembled.</b> The map is defensively copied into
 * an insertion-ordered unmodifiable map and each entry's cell list is an
 * unmodifiable copy, so later mutation of a constructor argument cannot
 * change the record.</p>
 *
 * @param registrations the per-imported-module registrations; non-null
 *                      (keys and values must be non-null and each value's
 *                      module must equal its key)
 */
public record NamespaceRegistrations(Map<ModuleId, NamespaceRegistration> registrations) {

    /**
     * The producer-defect rule id of every registration-assembly E6005
     * (the project-gate half of the namespace registration contract's
     * visible errors).
     */
    public static final String NAMESPACE_REGISTRATION = "NAMESPACE_REGISTRATION";

    public NamespaceRegistrations {
        Objects.requireNonNull(registrations, "registrations must not be null");
        Map<ModuleId, NamespaceRegistration> copied = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, NamespaceRegistration> entry : registrations.entrySet()) {
            ModuleId module = Objects.requireNonNull(entry.getKey(),
                "registrations keys must not be null");
            NamespaceRegistration registration = Objects.requireNonNull(entry.getValue(),
                "registrations values must not be null");
            if (!module.equals(registration.module())) {
                throw new IllegalArgumentException("the registration entry of " + module
                    + " carries the module " + registration.module()
                    + " (the map key is the module identity)");
            }
            copied.put(module, registration);
        }
        registrations = Collections.unmodifiableMap(copied);
    }

    /**
     * The registration of the given imported module, or {@code null} when
     * the module is not imported by the closure.
     *
     * @param module the imported module identity; non-null
     * @return the registration, or {@code null}
     */
    public NamespaceRegistration registrationFor(ModuleId module) {
        return registrations.get(Objects.requireNonNull(module,
            "module must not be null"));
    }

    /**
     * The recording-half assembly: derives the namespace registrations
     * from the closure's lowered units in closure order.
     *
     * <p>Rules (fail-closed, first defect wins): a named cell must be an
     * import-alias allocation of the naming unit (a module-scope
     * {@code BINDING_ALLOC} with no {@code BINDING_INIT}); every
     * import-alias allocation must be named by exactly one completion of
     * its unit whenever the unit carries the modules arm (at least one
     * completion — a unit of the intermediate class/binding windows
     * carries none and has no alias-cell recording surface); a cell must
     * not be named by two completions and must not be registered under
     * two modules; and a module's completions must agree on their
     * {@link ModuleImportKind}. On the first defect the result carries
     * exactly that E6005 and {@code null} registrations — no partial
     * registration set.</p>
     *
     * @param closure the complete implementation closure's lowered units
     *                in dependency order; non-null
     * @return the assembled registrations, or the first E6005
     */
    public static Assembly assemble(List<LoweredModuleUnit> closure) {
        Objects.requireNonNull(closure, "closure must not be null");
        Recorder recorder = new Recorder(Map.of());
        for (LoweredModuleUnit unit : closure) {
            Optional<CompilerDiagnostic> failure = recorder.record(unit);
            if (failure.isPresent()) {
                return new Assembly(null, List.of(failure.get()));
            }
        }
        return recorder.build();
    }

    /**
     * The recording-half builder of the project walk (ISSUE-0634;
     * {@code project-lowering-entry-and-registration-seeds} D8 and the
     * namespace registration contract): the registrations are created
     * <em>before</em> the first unit walk — the map key is the module
     * identity, so one entry exists per pre-registered distinct resolved
     * imported module in the given order (closure order, then first-import
     * declaration order) — and each lowered unit's import arm completes
     * them as its {@code MODULE_IMPORT} completions are recorded.
     *
     * <p>Every rule of {@link #assemble} is enforced here fail-closed and
     * first-defect-wins: a completion naming a cell that is not an
     * import-alias allocation of its unit, a cell named by two completions,
     * a cell registered under two modules, an import-alias allocation named
     * by no completion (of a unit that carries the modules arm), and a kind
     * disagreement between a completion and its entry. A pre-registered
     * module whose completions carry another kind is exactly that kind
     * disagreement: the entry exists before the walk, so a mismatched
     * completion is a producer defect, never a second entry.</p>
     */
    public static final class Recorder {

        /** The entry kinds in creation order (the registration order). */
        private final Map<ModuleId, ModuleImportKind> kinds = new LinkedHashMap<>();

        /** The ordered alias cells per module entry. */
        private final Map<ModuleId, List<BindingId>> cells = new LinkedHashMap<>();

        /** The owning module of every named cell (the one-entry clause). */
        private final Map<BindingId, ModuleId> ownerOfCell = new LinkedHashMap<>();

        /**
         * Creates one recorder over the pre-registered entries.
         *
         * @param preRegistered the distinct resolved imported modules of
         *                      the complete closure with their closed
         *                      import kinds, in closure order then
         *                      first-import declaration order; non-null
         */
        public Recorder(Map<ModuleId, ModuleImportKind> preRegistered) {
            Objects.requireNonNull(preRegistered, "preRegistered must not be null");
            for (Map.Entry<ModuleId, ModuleImportKind> entry
                    : preRegistered.entrySet()) {
                Objects.requireNonNull(entry.getKey(),
                    "pre-registered module must not be null");
                Objects.requireNonNull(entry.getValue(),
                    "pre-registered kind must not be null");
                kinds.put(entry.getKey(), entry.getValue());
                cells.put(entry.getKey(), new ArrayList<>());
            }
        }

        /**
         * Records one lowered unit's completions: the recording rule of
         * {@link NamespaceRegistrations#assemble} over the given unit's
         * produced {@code MODULE_IMPORT} payloads.
         *
         * @param unit the lowered unit in closure order; non-null
         * @return empty on success, otherwise the first E6005
         */
        public Optional<CompilerDiagnostic> record(LoweredModuleUnit unit) {
            Objects.requireNonNull(unit, "unit must not be null");
            Set<BindingId> aliases = aliasAllocations(unit);
            Set<BindingId> named = new LinkedHashSet<>();
            int completions = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.MODULE_IMPORT
                        || !(op.payload()
                            instanceof KindPayload.ModuleImportPayload payload)) {
                    continue;
                }
                completions++;
                ModuleId module = payload.resolvedModule();
                if (!kinds.containsKey(module)) {
                    kinds.put(module, payload.kind());
                    cells.put(module, new ArrayList<>());
                }
                ModuleImportKind entryKind = kinds.get(module);
                if (entryKind != payload.kind()) {
                    return Optional.of(fail(unit, "the MODULE_IMPORT completion "
                        + op.opId() + " of " + module + " carries the kind "
                        + payload.kind()
                        + " but the module's registration entry kind is " + entryKind
                        + " (a completion's ModuleImportKind equals its entry's kind)"));
                }
                List<BindingId> entryCells = cells.get(module);
                for (BindingId cell : payload.aliasCells()) {
                    if (!aliases.contains(cell)) {
                        return Optional.of(fail(unit, "the MODULE_IMPORT completion "
                            + op.opId() + " of " + module + " names the cell " + cell
                            + " which is not an import-alias allocation of the unit "
                            + "(a completion names import-alias cells only)"));
                    }
                    ModuleId previousOwner = ownerOfCell.putIfAbsent(cell, module);
                    if (previousOwner != null && !previousOwner.equals(module)) {
                        return Optional.of(fail(unit, "the cell " + cell
                            + " is registered under two modules (" + previousOwner
                            + " and " + module
                            + "; every alias cell appears in exactly one entry)"));
                    }
                    if (!named.add(cell)) {
                        return Optional.of(fail(unit, "the cell " + cell
                            + " is named by two MODULE_IMPORT completions (exactly"
                            + " one pinned initializing write per import-alias"
                            + " allocation)"));
                    }
                    entryCells.add(cell);
                }
            }
            for (BindingId alias : aliases) {
                if (completions > 0 && !named.contains(alias)) {
                    return Optional.of(fail(unit, "the import-alias allocation "
                        + alias + " is named by no MODULE_IMPORT completion (the "
                        + "completion write is the import alias's pinned initializing "
                        + "write)"));
                }
            }
            return Optional.empty();
        }

        /**
         * Builds the recorded registrations: one
         * {@link NamespaceRegistration} per entry in creation order
         * (closure order, then first-import declaration order).
         *
         * @return the assembled registrations with no diagnostics
         */
        public Assembly build() {
            Map<ModuleId, NamespaceRegistration> registrations = new LinkedHashMap<>();
            for (Map.Entry<ModuleId, ModuleImportKind> entry : kinds.entrySet()) {
                registrations.put(entry.getKey(), new NamespaceRegistration(
                    entry.getKey(), entry.getValue(), cells.get(entry.getKey())));
            }
            return new Assembly(new NamespaceRegistrations(registrations), List.of());
        }

        /** The first-defect E6005 of one recording step, with no register set. */
        private static CompilerDiagnostic fail(LoweredModuleUnit unit, String what) {
            LoweringFailureDetail detail = new LoweringFailureDetail(
                unit.moduleId().path(),
                SemanticCapability.MODULES,
                NAMESPACE_REGISTRATION,
                unit.semanticProfile(),
                LoweredModuleUnit.FORMAT_VERSION,
                "NamespaceRegistrations record (" + what + ")");
            return FailureContractRegistry.e6005(detail);
        }
    }

    /**
     * The import-alias allocations of one unit: the module-scope
     * {@code BINDING_ALLOC}s with no {@code BINDING_INIT} (the language
     * requires an initializer on every {@code let}, module-level function
     * names and the intrinsic seeds always carry their INITs, and group
     * members have no ALLOC — so every remaining module-scope
     * INIT-less ALLOC is an import alias).
     */
    private static Set<BindingId> aliasAllocations(LoweredModuleUnit unit) {
        BlockId moduleBlock = unit.moduleInit().initBlock();
        Set<BindingId> moduleScopeAllocs = new LinkedHashSet<>();
        Set<BindingId> initialized = new LinkedHashSet<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.scope().equals(moduleBlock)) {
                moduleScopeAllocs.add(alloc.binding());
            } else if (op.payload() instanceof KindPayload.BindingInitPayload init) {
                initialized.add(init.binding());
            }
        }
        moduleScopeAllocs.removeAll(initialized);
        return moduleScopeAllocs;
    }

    /**
     * The result of one registration assembly: the assembled record, or
     * {@code null} registrations with exactly the first E6005 diagnostic
     * on failure (no partial registration set).
     *
     * @param registrations the assembled {@link NamespaceRegistrations},
     *                      or {@code null} on failure
     * @param diagnostics   empty on success, otherwise the failure
     *                      diagnostics
     */
    public record Assembly(NamespaceRegistrations registrations,
                           List<CompilerDiagnostic> diagnostics) {

        public Assembly {
            Objects.requireNonNull(diagnostics, "diagnostics must not be null");
            diagnostics = List.copyOf(diagnostics);
        }

        /** True iff the assembly failed (no registrations were produced). */
        public boolean hasErrors() {
            return !diagnostics.isEmpty();
        }
    }
}
