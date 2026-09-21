package deal.semantic;

import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.Parameter;
import deal.ast.StatementNode;
import deal.ast.TypeNode;
import deal.checker.CheckResult;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FieldInterface;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The checked-project builder of the pre-lowering foundation (F2, one
 * component): after project-wide checking succeeds, exactly one call
 * consumes the orchestrator's module map in dependency order
 * ({@code buildCheckOrder}) and produces exactly one immutable
 * {@link CheckedProjectInput} and one immutable {@link ProjectInterfaceIndex}
 * ({@code deal.semantic-interface/1}) — the input covering the
 * implementation modules only (every entry
 * {@code CheckedModuleInput.kind = IMPLEMENTATION} with {@code checks};
 * the parent-pinned DECLARATION input kind has no producer under the
 * current orchestrator classification) and the index covering every
 * module in the dependency closure with the pinned four-value
 * {@code ExternalModuleInterface.kind} (spec-stdlib modules are STDLIB
 * index entries and every other declaration file is a HOST index entry
 * per the orchestrator's host predicate
 * {@code isDeclarationFile && !isSpecStdlibModuleInfo}; the parent-pinned
 * DECLARATION index kind has no producer).
 *
 * <p><b>Pinned fact sources (F2).</b> Implementation entries render from
 * checked facts: exports = the module's Phase-3-corrected resolved export
 * map in its insertion order (declaration order, then the
 * {@code @jsonable} synthetic exports), each {@link Type} value rendered
 * through {@link CanonicalTypeText#render(Type)}; classes = one
 * {@link ClassInterface} per exported class from the module's checked
 * {@code ClassSymbol} records. STDLIB/HOST declaration entries render from
 * the declaration AST — never from a {@code CheckResult} (none exists):
 * exports in declaration order from the declaration AST's
 * {@code ExportDeclaration} statements via the pinned
 * {@code TypeNode → CanonicalTypeText} grammar (function exports as the
 * full sync/async function form, class exports as
 * {@code @<moduleId>/<ClassName>}) plus the {@code @jsonable} synthetic
 * exports where the export map carries them; imports in source order
 * resolved through the orchestrator's resolution facts
 * ({@code resolveImportPath} plus the externals maps, supplied as
 * {@link ModuleFact.ImportFact} records); classes from exported class
 * declarations with the derived route-independent
 * {@code constructionEntry}; {@code initialization =
 * ONCE_AFTER_DEPENDENCIES} for every entry.</p>
 *
 * <p><b>{@code constructionEntry} derivation (F2).</b> A deterministic,
 * route-independent {@link ClassFactoryId} allocated at index-build time
 * through the {@link SemanticIdAllocator} ordering the later lowering
 * epics consume — dependency order, then exported classes in declaration
 * (source) order, semantic role factory entry, synthetic ordinal 0. The
 * index never records the owner's eventual route; an absent
 * {@code constructionEntry} is a producer defect (E6005), never a
 * legitimate state.</p>
 *
 * <p><b>E6005 guards (F2).</b> Missing checked facts (no
 * {@code CheckResult} for an input entry, an exported class without its
 * checked {@code ClassSymbol}), a defensive {@link Type.Error} in a
 * declared-type position, and out-of-grammar declaration annotations
 * (unresolvable qualified-type alias, chained {@code T | null | null},
 * unknown non-primitive {@code NamedType}) all raise E6005 through
 * {@link FailureContractRegistry} with the payload
 * {@code LoweringFailureDetail {module, capability: FOUNDATION_VALUES,
 * validatorRule: INDEX_INTERNAL_ERROR_SENTINEL, semanticProfile,
 * irVersion, origin}} — never an invented rendering, never a crash.
 * The builder never mutates the AST, {@code CheckResult}, or symbol
 * tables (no re-lex/re-parse), and dependency-order iteration plus the
 * single canonical JSON facility make repeated builds byte-identical —
 * STDLIB/HOST declaration entries included.</p>
 */
public final class CheckedProjectBuilder {

    /**
     * The builder fact-defect identifier carried as the E6005
     * {@code validatorRule} (foundation F2): a builder fact-defect
     * identifier, not a {@code SemanticIrValidator} rule — the closed
     * 14-condition validator rule set is unchanged.
     */
    public static final String INDEX_INTERNAL_ERROR_SENTINEL = "INDEX_INTERNAL_ERROR_SENTINEL";

    private CheckedProjectBuilder() {
        // Static build surface only; no instances.
    }

    /**
     * Builds exactly one {@link CheckedProjectInput} and one
     * {@link ProjectInterfaceIndex} from the orchestrator's module facts
     * in dependency order (foundation F2). The input records the
     * invocation's derived {@code releaseStateHash} verbatim (a copy of
     * the invocation field, never a recomputation).
     *
     * @param invocation              the release-owned compiler invocation; non-null
     * @param entryModule             the entry module's dotted module path; non-null
     * @param dependencyOrderedModules the module facts in
     *                                {@code buildCheckOrder}; non-null,
     *                                non-empty, distinct module ids
     * @return the build result: both records plus no diagnostics on
     *         success, both {@code null} plus one E6005 on a fact defect
     */
    public static CheckedProjectBuildResult build(CompilerInvocation invocation,
                                                  ModuleId entryModule,
                                                  List<ModuleFact> dependencyOrderedModules) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(entryModule, "entryModule must not be null");
        Objects.requireNonNull(dependencyOrderedModules,
            "dependencyOrderedModules must not be null");
        if (dependencyOrderedModules.isEmpty()) {
            throw new IllegalArgumentException(
                "the dependency-ordered module list must not be empty");
        }
        List<ModuleFact> facts = List.copyOf(dependencyOrderedModules);
        Map<String, ModuleFact> byModuleId = new LinkedHashMap<>();
        Map<String, ModuleFact> bySourcePath = new LinkedHashMap<>();
        for (ModuleFact fact : facts) {
            if (byModuleId.putIfAbsent(fact.moduleId().path(), fact) != null) {
                throw new IllegalArgumentException(
                    "duplicate module id \"" + fact.moduleId().path()
                        + "\" in the dependency-ordered module list");
            }
            bySourcePath.put(fact.sourcePath(), fact);
        }
        if (!byModuleId.containsKey(entryModule.path())) {
            throw new IllegalArgumentException(
                "entry module \"" + entryModule.path()
                    + "\" is not part of the dependency-ordered module closure");
        }

        // The dependency-ordered module list is also the allocator's
        // pinned module order (S7): constructionEntry ids are handed out
        // in dependency order, then exported classes in declaration
        // (source) order, role CLASS_FACTORY, synthetic ordinal 0.
        List<ModuleId> moduleIds = facts.stream().map(ModuleFact::moduleId).toList();
        SemanticIdAllocator allocator = SemanticIdAllocator.over(moduleIds);
        Map<ClassId, ClassFactoryId> constructionEntries = new LinkedHashMap<>();
        for (ModuleFact fact : facts) {
            long sourceOrdinal = 0;
            for (StatementNode stmt : fact.ast().statements()) {
                if (stmt instanceof ExportDeclaration ed
                        && ed.declaration() instanceof ClassDeclaration cd) {
                    ClassId classId = classIdOf(fact, cd);
                    constructionEntries.put(classId,
                        allocator.nextClassFactoryId(fact.moduleId(), sourceOrdinal, 0));
                }
                sourceOrdinal++;
            }
        }

        // Index entries: every module in the dependency closure.
        Map<ModuleId, ExternalModuleInterface> indexModules = new LinkedHashMap<>();
        for (ModuleFact fact : facts) {
            ExternalModuleKind kind = classify(fact);
            CanonicalTypeText.Context context = typeContext(fact, bySourcePath);
            ExternalModuleInterface entry;
            try {
                entry = buildIndexEntry(fact, kind, context, bySourcePath,
                    constructionEntries);
            } catch (CanonicalTypeText.Defect defect) {
                return failedResult(invocation, fact.moduleId(), defect.getMessage());
            }
            indexModules.put(fact.moduleId(), entry);
        }
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, indexModules);

        // Input modules: the implementation modules only, in dependency
        // (check) order — exactly the modules typeCheckAll checked, each
        // carrying its CheckResult by construction.
        List<CheckedModuleInput> inputs = new ArrayList<>();
        for (ModuleFact fact : facts) {
            if (fact.isDeclarationFile()) {
                continue;
            }
            CheckResult checks = fact.checkResult();
            if (checks == null) {
                return failedResult(invocation, fact.moduleId(),
                    "implementation module has no CheckResult (missing checked facts; "
                        + "every input entry is IMPLEMENTATION and typeCheckAll fills its "
                        + "CheckResult)");
            }
            List<ResolvedImport> imports;
            List<ExportInterface> exports;
            try {
                imports = buildImports(fact, bySourcePath);
                exports = buildImplementationExports(fact);
            } catch (CanonicalTypeText.Defect defect) {
                return failedResult(invocation, fact.moduleId(), defect.getMessage());
            }
            inputs.add(new CheckedModuleInput(fact.moduleId(), fact.sourcePath(),
                Path.of(fact.sourcePath()), fact.ast(), checks, imports, exports,
                CheckedModuleKind.IMPLEMENTATION));
        }

        CheckedProjectInput input = new CheckedProjectInput(invocation, entryModule,
            inputs, invocation.releaseStateHash());
        return new CheckedProjectBuildResult(input, index, List.of());
    }

    // =========================================================================
    // Classification and context
    // =========================================================================

    /**
     * The pinned population-rule classification (F2): implementation
     * modules (non-declaration files) are IMPLEMENTATION entries;
     * spec-stdlib declaration modules are STDLIB entries only; every
     * other declaration file — project-local or externals-registered — is
     * a HOST entry only. This is exactly the orchestrator's host
     * predicate {@code isDeclarationFile && !isSpecStdlibModuleInfo}; the
     * parent-pinned DECLARATION index kind has no producer.
     */
    private static ExternalModuleKind classify(ModuleFact fact) {
        if (!fact.isDeclarationFile()) {
            return ExternalModuleKind.IMPLEMENTATION;
        }
        return fact.isSpecStdlibModule() ? ExternalModuleKind.STDLIB : ExternalModuleKind.HOST;
    }

    /**
     * The rendering context of one declaring module: the classes declared
     * in the module (top-level class declarations, exported or not — the
     * only non-primitive {@code NamedType} names inside the grammar) and
     * the import-alias → resolved-module-path join over the module's
     * import records (the same join the signature-extraction pass
     * performs for qualified export signatures).
     */
    private static CanonicalTypeText.Context typeContext(ModuleFact fact,
                                                         Map<String, ModuleFact> bySourcePath) {
        Set<String> declaredClasses = new LinkedHashSet<>();
        for (StatementNode stmt : fact.ast().statements()) {
            switch (stmt) {
                case ClassDeclaration cd -> declaredClasses.add(cd.name());
                case ExportDeclaration ed when
                        ed.declaration() instanceof ClassDeclaration cd ->
                    declaredClasses.add(cd.name());
                default -> { }
            }
        }
        Map<String, String> aliasJoin = new LinkedHashMap<>();
        for (ModuleFact.ImportFact imp : fact.imports()) {
            ModuleFact target = bySourcePath.get(imp.resolvedSourcePath());
            if (target != null) {
                aliasJoin.put(imp.alias(), target.moduleId().path());
            }
        }
        return new CanonicalTypeText.Context(fact.moduleId(),
            Set.copyOf(declaredClasses), Map.copyOf(aliasJoin));
    }

    // =========================================================================
    // Index entry derivation
    // =========================================================================

    private static ExternalModuleInterface buildIndexEntry(ModuleFact fact,
                                                           ExternalModuleKind kind,
                                                           CanonicalTypeText.Context context,
                                                           Map<String, ModuleFact> bySourcePath,
                                                           Map<ClassId, ClassFactoryId> constructionEntries) {
        List<ResolvedImport> imports = buildImports(fact, bySourcePath);
        List<ExportInterface> exports;
        List<ClassInterface> classes;
        if (kind == ExternalModuleKind.IMPLEMENTATION) {
            exports = buildImplementationExports(fact);
            classes = buildImplementationClasses(fact, context, constructionEntries);
        } else {
            exports = buildDeclarationExports(fact, context);
            classes = buildDeclarationClasses(fact, context, constructionEntries);
        }
        return new ExternalModuleInterface(fact.moduleId(), kind, imports, exports,
            classes, InitializationMode.ONCE_AFTER_DEPENDENCIES);
    }

    /**
     * The pinned import derivation: in source order from the orchestrator's
     * resolved imports, each as {@code ResolvedImport {alias, modulePath
     * (the raw specifier as written), resolvedModuleId (the resolved
     * target's dotted module path), kind (the resolved target's index
     * kind)}}.
     */
    private static List<ResolvedImport> buildImports(ModuleFact fact,
                                                     Map<String, ModuleFact> bySourcePath) {
        List<ResolvedImport> imports = new ArrayList<>(fact.imports().size());
        for (ModuleFact.ImportFact imp : fact.imports()) {
            ModuleFact target = bySourcePath.get(imp.resolvedSourcePath());
            if (target == null) {
                throw new CanonicalTypeText.Defect(
                    "import '" + imp.modulePath() + "' resolves to source path '"
                        + imp.resolvedSourcePath()
                        + "' that is not part of the dependency closure (inconsistent "
                        + "resolution facts)");
            }
            imports.add(new ResolvedImport(imp.alias(), imp.modulePath(),
                target.moduleId(), classify(target)));
        }
        return imports;
    }

    /**
     * Implementation-entry exports: the module's Phase-3-corrected
     * resolved export map in its insertion order (source export-declaration
     * order, then the {@code @jsonable} synthetic exports the same pass
     * appends), each rendered through the checked-{@link Type} rendering
     * of {@link CanonicalTypeText}.
     */
    private static List<ExportInterface> buildImplementationExports(ModuleFact fact) {
        List<ExportInterface> exports = new ArrayList<>(fact.exports().size());
        for (Map.Entry<String, Type> entry : fact.exports().entrySet()) {
            exports.add(new ExportInterface(entry.getKey(),
                CanonicalTypeText.render(entry.getValue())));
        }
        return exports;
    }

    /**
     * The canonical class identity of one exported class declaration of
     * an index entry (descriptor-identity-propagation D1): an
     * implementation module's class carries the checker-resolved
     * {@link Symbol.ClassSymbol#identity()} projected through
     * {@link DescriptorService#semanticModulePath} — the same producer
     * the checker, the declaration surface, the canonical type text, and
     * the lowerer's class arms use, so the index entry's
     * {@code ClassInterface} is the identity a class literal resolves and
     * the construction entries key on exactly that identity. The private
     * deployment wiring key ({@code ClassSymbol.modulePath()}) never
     * renders descriptor text. A declaration module's class keeps the
     * pinned {@code @<moduleId>/<ClassName>} declaration spelling.
     */
    private static ClassId classIdOf(ModuleFact fact, ClassDeclaration cd) {
        if (fact.isDeclarationFile()) {
            return new ClassId(fact.moduleId().path(), cd.name());
        }
        SymbolTable table = fact.symbolTable();
        Symbol symbol = table == null ? null : table.resolve(cd.name());
        if (symbol instanceof Symbol.ClassSymbol classSymbol) {
            return new ClassId(
                DescriptorService.semanticModulePath(classSymbol.identity()),
                classSymbol.name());
        }
        // A missing checked ClassSymbol is a producer defect the per-kind
        // builders report; the wiring path is the failure-path fallback
        // only.
        return new ClassId(fact.moduleId().path(), cd.name());
    }

    /**
     * Implementation-entry classes: one {@link ClassInterface} per
     * exported class from the module's checked {@code ClassSymbol}
     * records, carrying the checker-resolved class identity (the
     * descriptor-text identity, never the private deployment wiring key),
     * fields rendered via the pinned {@code TypeNode → CanonicalTypeText}
     * grammar with {@code optional}/{@code nullable} from the record and
     * {@code hasDefault} from {@code defaultExpr} presence.
     */
    private static List<ClassInterface> buildImplementationClasses(ModuleFact fact,
                                                                   CanonicalTypeText.Context context,
                                                                   Map<ClassId, ClassFactoryId> constructionEntries) {
        SymbolTable table = fact.symbolTable();
        if (table == null) {
            throw new CanonicalTypeText.Defect(
                "implementation module has no symbol table (missing checked facts)");
        }
        List<ClassInterface> classes = new ArrayList<>();
        for (StatementNode stmt : fact.ast().statements()) {
            if (stmt instanceof ExportDeclaration ed
                    && ed.declaration() instanceof ClassDeclaration cd) {
                Symbol symbol = table.resolve(cd.name());
                if (!(symbol instanceof Symbol.ClassSymbol classSymbol)) {
                    throw new CanonicalTypeText.Defect(
                        "exported class '" + cd.name() + "' has no checked ClassSymbol "
                            + "(missing checked facts)");
                }
                ClassId classId = new ClassId(
                    DescriptorService.semanticModulePath(classSymbol.identity()),
                    classSymbol.name());
                List<FieldInterface> fields = new ArrayList<>(classSymbol.fields().size());
                for (ClassField field : classSymbol.fields()) {
                    fields.add(buildFieldInterface(field, context));
                }
                classes.add(new ClassInterface(classId, fields,
                    requireConstructionEntry(classId, constructionEntries)));
            }
        }
        return classes;
    }

    /**
     * STDLIB/HOST declaration-entry exports (F2 derivation item 1): in
     * declaration order from the declaration AST's
     * {@code ExportDeclaration} statements via the pinned TypeNode
     * grammar — a function export as the full sync/async function form
     * from {@code fd.params()}, {@code fd.returnType()},
     * {@code fd.isAsync()}; a class export as
     * {@code @<moduleId>/<ClassName>} — plus the {@code @jsonable}
     * synthetic exports exactly where the module's export map carries
     * them (an exported {@code @jsonable} class appends
     * {@code C$fromJson: (string) => C | null} and
     * {@code C$toJson: (C) => string} after the declared exports).
     */
    private static List<ExportInterface> buildDeclarationExports(ModuleFact fact,
                                                                 CanonicalTypeText.Context context) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode stmt : fact.ast().statements()) {
            if (!(stmt instanceof ExportDeclaration ed)) {
                continue;
            }
            switch (ed.declaration()) {
                case FunctionDeclaration fd -> {
                    List<TypeNode> params = new ArrayList<>(fd.params().size());
                    for (Parameter parameter : fd.params()) {
                        params.add(parameter.type());
                    }
                    exports.add(new ExportInterface(fd.name(),
                        CanonicalTypeText.renderFunctionForm(params, fd.returnType(),
                            fd.isAsync(), context)));
                }
                case ClassDeclaration cd -> exports.add(new ExportInterface(cd.name(),
                    "@" + fact.moduleId().path() + "/" + cd.name()));
                default -> { }
            }
        }
        for (StatementNode stmt : fact.ast().statements()) {
            if (stmt instanceof ExportDeclaration ed
                    && ed.declaration() instanceof ClassDeclaration cd
                    && cd.isJsonable()) {
                String fromJson = cd.name() + "$fromJson";
                String toJson = cd.name() + "$toJson";
                if (fact.exports().containsKey(fromJson)) {
                    exports.add(new ExportInterface(fromJson,
                        CanonicalTypeText.render(fact.exports().get(fromJson))));
                }
                if (fact.exports().containsKey(toJson)) {
                    exports.add(new ExportInterface(toJson,
                        CanonicalTypeText.render(fact.exports().get(toJson))));
                }
            }
        }
        return exports;
    }

    /**
     * STDLIB/HOST declaration-entry classes (F2 derivation item 3): one
     * {@link ClassInterface} per exported class declaration in
     * declaration order with {@code classId = @<moduleId>/<ClassName>},
     * fields from the {@code ClassField} records rendered via the pinned
     * TypeNode grammar, and the derived route-independent
     * {@code constructionEntry}.
     */
    private static List<ClassInterface> buildDeclarationClasses(ModuleFact fact,
                                                                CanonicalTypeText.Context context,
                                                                Map<ClassId, ClassFactoryId> constructionEntries) {
        List<ClassInterface> classes = new ArrayList<>();
        for (StatementNode stmt : fact.ast().statements()) {
            if (stmt instanceof ExportDeclaration ed
                    && ed.declaration() instanceof ClassDeclaration cd) {
                ClassId classId = new ClassId(fact.moduleId().path(), cd.name());
                List<FieldInterface> fields = new ArrayList<>(cd.fields().size());
                for (ClassField field : cd.fields()) {
                    fields.add(buildFieldInterface(field, context));
                }
                classes.add(new ClassInterface(classId, fields,
                    requireConstructionEntry(classId, constructionEntries)));
            }
        }
        return classes;
    }

    /**
     * The pinned {@code FieldInterface} derivation from a
     * {@code ClassField} record: {@code {name, declaredType, optional,
     * nullable, hasDefault}} with {@code declaredType} via the pinned
     * TypeNode grammar, {@code optional}/{@code nullable} from the record,
     * and {@code hasDefault} from {@code defaultExpr} presence.
     */
    private static FieldInterface buildFieldInterface(ClassField field,
                                                      CanonicalTypeText.Context context) {
        return new FieldInterface(field.name(),
            CanonicalTypeText.render(field.type(), context),
            field.optional(), field.nullable(), field.defaultExpr().isPresent());
    }

    /**
     * The F2 completeness invariant: an absent {@code constructionEntry}
     * is a producer defect (E6005), never a legitimate state — the index
     * build allocates one per exported class before routing.
     */
    private static ClassFactoryId requireConstructionEntry(ClassId classId,
                                                           Map<ClassId, ClassFactoryId> constructionEntries) {
        ClassFactoryId entry = constructionEntries.get(classId);
        if (entry == null) {
            throw new CanonicalTypeText.Defect(
                "exported class '" + classId.text()
                    + "' has no derived constructionEntry (producer defect: the index "
                    + "build allocates one per exported class before routing)");
        }
        return entry;
    }

    // =========================================================================
    // E6005 through the failure contract registry
    // =========================================================================

    private static CheckedProjectBuildResult failedResult(CompilerInvocation invocation,
                                                          ModuleId module, String reason) {
        LoweringFailureDetail detail = new LoweringFailureDetail(module.path(),
            SemanticCapability.FOUNDATION_VALUES, INDEX_INTERNAL_ERROR_SENTINEL,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "CheckedProjectBuilder " + INDEX_INTERNAL_ERROR_SENTINEL + " (" + reason + ")");
        return new CheckedProjectBuildResult(null, null,
            List.of(FailureContractRegistry.e6005(detail)));
    }
}
