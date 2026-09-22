package deal.semantic;

import deal.ast.ExpressionNode;
import deal.ast.IdentifierExpr;
import deal.ast.MemberAccessExpr;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.StdlibFunctionCatalog.Entry;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The closed checked-fact stdlib-call recognition predicate
 * ({@code stdlib-operations-and-time-lock} D1): the only consumer-side
 * classifier that may map a call callee to a stdlib call. No consumer may
 * interpret a module/name pair as a stdlib algorithm outside
 * {@link StdlibFunctionCatalog} and this predicate; the lowerer's stdlib
 * branch (ISSUE-0236 call machinery) runs exactly this classification.
 *
 * <p><b>Predicate (D1, exact).</b> {@link #recognize} returns the
 * catalog entry exactly when all of the following hold, using only
 * checked facts (the callee AST node, the checker's symbol-table scope
 * at the callee's site, and the module's resolved import list):</p>
 *
 * <ol>
 *   <li>the callee is a {@link MemberAccessExpr};</li>
 *   <li>its object is an {@link IdentifierExpr};</li>
 *   <li>the checker's scope resolves that identifier to a
 *       {@link Symbol.ModuleSymbol} — the namespace-import binding the
 *       checker created from the {@code import * as alias from
 *       "modulePath"} declaration (namespace-only imports,
 *       {@code deal/ast/ImportDeclaration.java});</li>
 *   <li>the module's {@link ResolvedImport} facts contain the import for
 *       that alias (the alias join is exact: one import per alias per
 *       module);</li>
 *   <li>that import's resolved module is classified
 *       {@link ExternalModuleKind#STDLIB} — the spec-stdlib
 *       classification the {@link CheckedProjectBuilder} index records
 *       ({@code deal/semantic/CheckedProjectBuilder.java});</li>
 *   <li>the member name is a {@link StdlibFunctionCatalog} key for the
 *       resolved module path.</li>
 * </ol>
 *
 * <p><b>Negatives (D1).</b> The predicate returns {@code
 * Optional.empty()} for user modules, host modules, local or shadowed
 * bindings, non-member callees, any member chain whose object is not
 * such a module symbol, identifier spellings that merely equal a stdlib
 * alias but resolve to a non-STDLIB module (anti-hollow: spelling-based
 * matching is never used), and any member the catalog does not carry.
 * {@code std/time} has been a cataloged module since K7, so
 * {@code time.nowMillis()} is recognized like every other declared
 * stdlib call through this predicate and the closed catalog row.
 * An absent import fact or a null scope resolves nothing — fail closed to
 * "not a stdlib call", never an error.</p>
 *
 * <p><b>Purity.</b> The predicate is a pure function over its three
 * checked-fact inputs: no state, no retry, no timeout, no AST mutation,
 * no module/name interpretation. The same inputs always yield the same
 * entry; absent inputs yield empty.</p>
 */
public final class StdlibCallRecognition {

    private StdlibCallRecognition() {
        // Static surface only; no instances and no state.
    }

    /**
     * The closed recognition predicate (D1): the catalog entry for a
     * callee recognized as a stdlib call from checked facts only, or
     * {@code Optional.empty()} — "not a stdlib call" — for every other
     * shape.
     *
     * @param callee       the call's callee expression; non-null
     * @param checkerScope the checker's symbol-table scope at the
     *                     callee's site (the {@code CheckResult}'s root
     *                     table or a {@code scopeMap} entry; resolution
     *                     walks the chain to the module root); a null
     *                     scope resolves nothing and yields empty
     * @param imports      the module's resolved imports in source order
     *                     ({@code CheckedModuleInput.imports}); non-null
     * @return the closed catalog entry when all six predicate conditions
     *         hold; empty otherwise
     */
    public static Optional<Entry> recognize(ExpressionNode callee, SymbolTable checkerScope,
                                            List<ResolvedImport> imports) {
        Objects.requireNonNull(callee, "callee must not be null");
        Objects.requireNonNull(imports, "imports must not be null");
        if (!(callee instanceof MemberAccessExpr access)) {
            return Optional.empty();
        }
        if (!(access.object() instanceof IdentifierExpr identifier)) {
            return Optional.empty();
        }
        if (checkerScope == null) {
            return Optional.empty();
        }
        Symbol symbol = checkerScope.resolve(identifier.name());
        if (!(symbol instanceof Symbol.ModuleSymbol moduleSymbol)) {
            return Optional.empty();
        }
        ResolvedImport importFact = null;
        for (ResolvedImport candidate : imports) {
            if (candidate.alias().equals(moduleSymbol.name())) {
                importFact = candidate;
                break;
            }
        }
        if (importFact == null) {
            return Optional.empty();
        }
        if (importFact.kind() != ExternalModuleKind.STDLIB) {
            return Optional.empty();
        }
        return StdlibFunctionCatalog.lookup(
            importFact.resolvedModuleId().path(), access.field());
    }
}
