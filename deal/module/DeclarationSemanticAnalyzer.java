package deal.module;

import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.DeclarationDirective;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.identity.CanonicalClassIdentity;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The declaration/C-struct half of the shared default planning pipeline
 * (ISSUE-0541; design sources
 * {@code deal-v1.2-directives-and-c-ffi-declarations} D3,
 * {@code provider-versioned-default-plans} D1-D4): plans the C-struct
 * classes of an extern-C declaration module with the same
 * {@link CompilerClassDefaultPlan} shape and the same plan-shape gates
 * as implementation classes.
 *
 * <p>The analyzer hoists the declaration's symbols (imports, functions,
 * classes) through a declaration-scope name resolution, checks each
 * C-struct default against its field type through the production
 * checker over a synthetic program of the directive-stripped class
 * declarations (E3001 at the default expression range — the checker
 * identity), applies the E4001 declaration-shape gate at the field
 * declaration range and the E3020 sync gate at the await range, records
 * the typed evaluator IR with the complete walk, and publishes the
 * ordered provisional occurrence data. Host-declared classes are
 * exempt: only {@code @c-struct} classes are planned, and the analyzer
 * publishes no digest and constructs no
 * {@link RuntimeResourceReference} or {@link RuntimeImportDependency}
 * record.</p>
 */
public final class DeclarationSemanticAnalyzer {

    private DeclarationSemanticAnalyzer() {
        // Static entry; no instances.
    }

    /**
     * The analysis result: the diagnostics (never null) and the planned
     * C-struct classes in class source order (empty when any
     * error-level diagnostic fired).
     */
    public record Result(
        List<CompilerDiagnostic> diagnostics,
        List<PlannedDefaultClass> plannedClasses
    ) {

        public Result {
            diagnostics = List.copyOf(Objects.requireNonNull(diagnostics,
                "diagnostics"));
            plannedClasses = List.copyOf(Objects.requireNonNull(
                plannedClasses, "plannedClasses"));
        }

        /** True when any diagnostic is an error (no plans then). */
        public boolean hasErrors() {
            return diagnostics.stream().anyMatch(
                d -> "error".equals(d.severity()));
        }
    }

    /**
     * Analyzes one extern-C declaration module and plans its C-struct
     * classes.
     *
     * @param input            the module's read-only declaration facts
     * @param identityAssembly the compilation's identity assembly (the
     *                         plan's class identity comes from its
     *                         required-identity gate)
     * @return the diagnostics and the planned classes; on any
     *         error-level diagnostic {@code plannedClasses} is empty
     */
    public static Result analyze(DefaultDeclarationModuleInput input,
                                 ModuleIdentityAssembly identityAssembly) {
        Objects.requireNonNull(input, "input");
        Objects.requireNonNull(identityAssembly, "identityAssembly");
        List<CompilerDiagnostic> diagnostics = new ArrayList<>();

        // 1. Hoist declaration symbols over the declaration's own AST:
        // imports, functions, classes.
        NameResolver resolver = new NameResolver(input.modulePath(),
            input.moduleResolver(), new HashSet<>(),
            input.classification()::get);
        SymbolTable root;
        try {
            root = resolver.resolve(input.program());
        } catch (RuntimeException defect) {
            // No raw resolver exception escapes (fail closed).
            diagnostics.add(CompilerDiagnostic.syntheticError(
                DiagnosticCode.E6005,
                "declaration default analysis failed: "
                    + defect.getMessage(),
                input.sourcePath(),
                "missing anchor: declaration default analysis of module '"
                    + input.modulePath() + "'"));
            return new Result(diagnostics, List.of());
        }
        diagnostics.addAll(resolver.diagnostics());
        if (resolver.diagnostics().stream().anyMatch(
                d -> "error".equals(d.severity()))) {
            return new Result(diagnostics, List.of());
        }

        // 2. The plan-bearing declaration classes: @c-struct classes in
        // source order. Host-declared (non-C-struct) classes produce no
        // plan.
        List<ClassDeclaration> structClasses = new ArrayList<>();
        for (StatementNode stmt : input.program().statements()) {
            ClassDeclaration cd = classDeclarationOf(stmt);
            if (cd != null && cd.directives().contains(
                    DeclarationDirective.C_STRUCT)) {
                structClasses.add(cd);
            }
        }
        if (structClasses.isEmpty()) {
            return new Result(diagnostics, List.of());
        }

        // 3. Check every C-struct default against its field type through
        // the production checker over a synthetic program of the
        // directive-stripped class declarations (E3001 at the default
        // expression range; no @jsonable logic runs for extern-C
        // declarations).
        List<StatementNode> checkedStatements = new ArrayList<>();
        for (ClassDeclaration cd : structClasses) {
            checkedStatements.add(new ClassDeclaration(cd.span(),
                cd.name(), cd.fields(), Set.of()));
        }
        ProgramNode checkedProgram = new ProgramNode(
            input.program().span(), checkedStatements,
            input.program().fileDirectives());
        CheckResult checked = TypeChecker.check(input.modulePath(), root,
            resolver, checkedProgram);
        diagnostics.addAll(checked.diagnostics());
        if (checked.hasErrors()) {
            return new Result(diagnostics, List.of());
        }

        // 4. Plan each C-struct class with the shared gates and the
        // shared IR walk.
        DefaultDeclaringContext declaringContext =
            declaringContextOf(input);
        List<PlannedDefaultClass> planned = new ArrayList<>();
        for (ClassDeclaration cd : structClasses) {
            ModuleIdentityAssembly.ClassIdentityResult identityResult =
                identityAssembly.requireClassIdentity(input.location(),
                    cd.name(), cd.span());
            if (identityResult
                    instanceof ModuleIdentityAssembly.ClassIdentityResult
                        .Failure f) {
                diagnostics.add(f.diagnostic());
                continue;
            }
            CanonicalClassIdentity classIdentity =
                ((ModuleIdentityAssembly.ClassIdentityResult.Identity)
                    identityResult).identity();
            PlannedDefaultClass plannedClass = planStructClass(cd, root,
                classIdentity, input, checked, resolver, declaringContext,
                diagnostics);
            if (plannedClass != null) {
                planned.add(plannedClass);
            }
        }
        return new Result(diagnostics, planned);
    }

    /**
     * Plans one C-struct class; null when any gate or default defect
     * fired (the diagnostics were appended to {@code diagnostics}).
     */
    private static PlannedDefaultClass planStructClass(
            ClassDeclaration cd, SymbolTable root,
            CanonicalClassIdentity classIdentity,
            DefaultDeclarationModuleInput input, CheckResult checked,
            NameResolver resolver, DefaultDeclaringContext declaringContext,
            List<CompilerDiagnostic> diagnostics) {
        List<CompilerDiagnostic> classDiagnostics = new ArrayList<>();
        List<CompilerClassDefaultEntry> entries = new ArrayList<>();
        List<DefaultResourceOccurrence> occurrences = new ArrayList<>();
        Set<SemanticResourceIdentity> seen = new LinkedHashSet<>();
        Set<String> fieldNames = new LinkedHashSet<>();

        resolver.setCurrentScope(root);
        boolean failed = false;
        for (ClassField cf : cd.fields()) {
            if (!fieldNames.add(cf.name())) {
                // C-struct field names must be unique (the plan's
                // entries require unique names); the FFI phase's E7002
                // owns the policy. No plan-entry shape exists for a
                // duplicated C-struct field name, so the class plan is
                // withheld (the FFI phase fails the compile) — never a
                // raw plan-construction exception.
                failed = true;
                continue;
            }
            if (cf.optional()) {
                // C-struct fields must be required (spec §C struct
                // classes); the FFI phase's E7002 owns the policy. No
                // plan-entry shape exists for an optional C-struct
                // field, so the class plan is withheld (the FFI phase
                // fails the compile).
                failed = true;
                continue;
            }
            if (cf.defaultExpr().isEmpty()) {
                // D2 declaration-shape gate (spec §Class declaration
                // :679-680; spec §C struct classes requires the same
                // shape): E4001 at the field declaration range — the
                // shared planner gate, preceding the FFI phase's own
                // missing-default policy.
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E4001,
                    "Class field without default is not valid: field '"
                        + cf.name() + "' of class '" + cd.name()
                        + "' must provide a default value expression",
                    cf.span().range()));
                failed = true;
                continue;
            }
            Type fieldType = resolver.resolveTypeNode(cf.type());
            if (fieldType == null || fieldType == Type.Error.INSTANCE) {
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "declaration default analysis failed: field '"
                        + cf.name() + "' of class '" + cd.name()
                        + "' has no resolved field type",
                    cf.span().range()));
                failed = true;
                continue;
            }
            String runtimeTypeDescriptor;
            try {
                runtimeTypeDescriptor = input.descriptors().encode(fieldType);
            } catch (IllegalStateException defect) {
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "declaration default analysis failed: field '"
                        + cf.name() + "' of class '" + cd.name()
                        + "' has no canonical runtime descriptor ("
                        + defect.getMessage() + ")",
                    cf.span().range()));
                failed = true;
                continue;
            }
            ExpressionNode def = cf.defaultExpr().get();
            Type defType = checked.typeMap().get(def);
            if (defType == null) {
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "declaration default analysis failed: the default of"
                        + " field '" + cf.name() + "' of class '"
                        + cd.name() + "' has no checked type",
                    def.span().range()));
                failed = true;
                continue;
            }
            if (defType != Type.Error.INSTANCE
                    && !DefaultSemanticPlanner.defaultTypeAssignable(
                        fieldType, defType)) {
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E3001,
                    "Default value type mismatch for field '" + cf.name()
                        + "': expected " + TypeChecker.typeName(fieldType)
                        + ", got " + TypeChecker.typeName(defType),
                    def.span().range()));
                failed = true;
                continue;
            }

            DefaultIrRecorder recorder = new DefaultIrRecorder(
                checked.typeMap(), checked.scopeMap(), input.imports(),
                input.classification(), input.location(), input.modulePath(),
                input.program(),
                (typeNode, resolutionScope) -> {
                    resolver.setCurrentScope(resolutionScope);
                    return resolver.resolveTypeNode(typeNode);
                },
                DefaultIrRecorder.qualifiedClassAliasesOf(cf.type()));
            DefaultIrNode ir = recorder.record(def, root, fieldType);
            classDiagnostics.addAll(recorder.awaitDiagnostics());
            if (!recorder.awaitDiagnostics().isEmpty()) {
                failed = true;
            }
            ResolvedDefaultExpression expression =
                new ResolvedDefaultExpression(
                    def, defType, def.span().range(), declaringContext,
                    recorder.bindings(), ir, null, null, Set.of());
            entries.add(new CompilerClassDefaultEntry(cf.name(),
                fieldType, runtimeTypeDescriptor, false, expression));
            for (DefaultResourceOccurrence occurrence
                    : recorder.occurrences()) {
                if (seen.add(occurrence.semanticResourceIdentity())) {
                    occurrences.add(occurrence);
                }
            }
        }

        if (failed || classDiagnostics.stream().anyMatch(
                d -> "error".equals(d.severity()))) {
            diagnostics.addAll(classDiagnostics);
            return null;
        }
        CompilerClassDefaultPlan plan = new CompilerClassDefaultPlan(
            classIdentity, input.location().semanticModuleIdentity(),
            entries, Set.of());
        return new PlannedDefaultClass(plan, cd, occurrences);
    }

    private static ClassDeclaration classDeclarationOf(StatementNode stmt) {
        if (stmt instanceof ClassDeclaration cd) {
            return cd;
        }
        if (stmt instanceof ExportDeclaration ed
                && ed.declaration() instanceof ClassDeclaration cd) {
            return cd;
        }
        return null;
    }

    private static DefaultDeclaringContext declaringContextOf(
            DefaultDeclarationModuleInput input) {
        Map<String, SemanticModuleIdentity> aliases =
            new java.util.LinkedHashMap<>();
        for (Map.Entry<String, DefaultPlanImport> entry
                : input.imports().entrySet()) {
            aliases.put(entry.getKey(),
                entry.getValue().location().semanticModuleIdentity());
        }
        return new DefaultDeclaringContext(
            input.location().semanticModuleIdentity(), aliases);
    }
}
