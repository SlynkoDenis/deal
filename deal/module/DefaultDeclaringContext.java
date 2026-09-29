package deal.module;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * The concrete declaring lexical context of a resolved default
 * expression (ISSUE-0541; the planner-owned content of the
 * {@link DeclaringLexicalContext} seam pinned by the carrier shape,
 * {@code provider-versioned-default-plans} D3): every default resolves
 * through its declaring module's scope — lexical/local bindings,
 * same-module functions and classes, and import aliases.
 *
 * <p>The context records exactly the declaration-site resolution
 * surface the serializer and graph epics consume: the declaring
 * module's private semantic identity plus the importer-local alias
 * surface (alias spelling &rarr; the imported module's private semantic
 * identity, importer-relative). Same-module and local bindings live in
 * {@link ResolvedDefaultExpression#resolvedBindings()}, never here.</p>
 *
 * <p>Immutable and deterministic; identities are compiler-internal and
 * never appear in runtime descriptors, diagnostic type names, public
 * export keys, or source-language values.</p>
 *
 * @param declaringModuleIdentity the declaring module's private
 *                                semantic identity
 * @param importAliases           alias spelling &rarr; imported
 *                                module's private semantic identity,
 *                                insertion-ordered
 */
public record DefaultDeclaringContext(
    SemanticModuleIdentity declaringModuleIdentity,
    Map<String, SemanticModuleIdentity> importAliases
) implements DeclaringLexicalContext {

    public DefaultDeclaringContext {
        Objects.requireNonNull(declaringModuleIdentity,
            "declaringModuleIdentity");
        importAliases = Map.copyOf(Objects.requireNonNull(importAliases,
            "importAliases"));
    }

    /**
     * The declaring context of one module's resolved import surface: its
     * private semantic identity plus alias spelling &rarr; imported
     * module's private semantic identity, derived from the imports'
     * resolved locations in insertion order.
     */
    static DefaultDeclaringContext of(Map<String, DefaultPlanImport> imports,
            SourceModuleLocation location) {
        Map<String, SemanticModuleIdentity> aliases = new LinkedHashMap<>();
        for (Map.Entry<String, DefaultPlanImport> entry : imports.entrySet()) {
            aliases.put(entry.getKey(),
                entry.getValue().location().semanticModuleIdentity());
        }
        return new DefaultDeclaringContext(
            location.semanticModuleIdentity(), aliases);
    }
}
