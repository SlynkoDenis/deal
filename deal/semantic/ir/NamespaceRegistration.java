package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * One namespace registration of the project lowering
 * ({@code project-lowering-entry-and-registration-seeds} D8; the
 * recording half of {@code semantic-ir-construct-coverage-cutover} K9
 * item 8/K15 items 1-2): the imported module identity, the closed
 * {@link ModuleImportKind} every one of its completions carries, and the
 * ordered alias cells whose {@code MODULE_IMPORT} completions name that
 * module.
 *
 * <p><b>Recording surface only.</b> The registration records no
 * namespace-value op, no op result, and no new op kind: the module
 * namespace value's creation (the module's own publication or its single
 * load, and the completion write into the alias cells) is the namespace
 * child's realization. This record is the project's typed fact that
 * exactly one namespace exists per distinct imported module and that its
 * ordered alias cells are exactly the cells the module's completions
 * hold.</p>
 *
 * <p><b>Order.</b> {@code aliasCells} is the ordered union of the cells
 * whose {@code MODULE_IMPORT} completion names this module, in closure
 * order and then import-declaration order; a unit with two import
 * declarations resolving to one module contributes two cells to the one
 * entry. The list is defensively copied, so the registration is
 * read-only once assembled.</p>
 *
 * @param module     the distinct resolved imported module identity; non-null
 * @param kind       the closed module-import kind of the module's
 *                   completions; non-null
 * @param aliasCells the ordered alias cells the module's completions
 *                   write; non-null (empty for a module with no named
 *                   cell)
 */
public record NamespaceRegistration(ModuleId module, ModuleImportKind kind,
                                    List<BindingId> aliasCells) {

    public NamespaceRegistration {
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(kind, "kind must not be null");
        aliasCells = List.copyOf(Objects.requireNonNull(aliasCells,
            "aliasCells must not be null"));
        for (BindingId cell : aliasCells) {
            Objects.requireNonNull(cell, "aliasCells entries must not be null");
        }
    }
}
