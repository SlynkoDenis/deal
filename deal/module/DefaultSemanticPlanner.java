package deal.module;

import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ExpressionNode;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.identity.CanonicalClassIdentity;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The shared resolved default planner for implementation classes
 * (ISSUE-0541; design source {@code provider-versioned-default-plans}
 * D1-D4): one {@link CompilerClassDefaultPlan} per plan-bearing
 * implementation class, produced from the module's checked facts —
 * resolution and type checking in the declaring lexical/import context,
 * typed evaluator IR recording with the complete walk, and the two
 * plan-shape gates (E4001 declaration shape, E3020 sync evaluators).
 *
 * <p>The plan-shape gates ({@code provider-versioned-default-plans}
 * D2):</p>
 * <ul>
 *   <li>a required-present field without a default is E4001 "Class
 *       field without default is not valid" at the field declaration
 *       range;</li>
 *   <li>an {@code await} node at evaluator scope — outside a nested
 *       function-expression body — is E3020 "'await' in class default"
 *       at the await range, including defaults of classes declared
 *       inside async function bodies (which the checker's E3012 does
 *       not cover); await inside a nested async function-expression
 *       body stays legal.</li>
 * </ul>
 *
 * <p>A class with any gate violation or default defect publishes no
 * plan. A published plan carries empty {@code runtimeDependencies}
 * (plans stay compiler-internal until the dependency graph succeeds,
 * D1) and the ordered, deduplicated provisional
 * {@link DefaultResourceOccurrence} list — no digest is computed and no
 * {@link RuntimeResourceReference} or {@link RuntimeImportDependency}
 * record is constructed (the serializer and graph epics own those).
 * An optional field's declared default is checked and recorded (the
 * E3020 gate applies to every declared default) but carries no runtime
 * effect: the plan entry omits it.</p>
 */
public final class DefaultSemanticPlanner {

    private DefaultSemanticPlanner() {
        // Static entry; no instances.
    }

    /**
     * The planning result: the diagnostics (never null) and the
     * planned classes in class source order (empty when any error-level
     * diagnostic fired — failure publishes no plan).
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
     * Plans every class declaration of one implementation module — in
     * checker walk order (source order) — over the module's checked
     * facts.
     *
     * @param input            the module's read-only checked facts
     * @param identityAssembly the compilation's identity assembly (the
     *                         plan's class identity comes from its
     *                         required-identity gate; idempotent
     *                         registration)
     * @return the diagnostics and the planned classes; on any
     *         error-level diagnostic {@code plannedClasses} is empty
     */
    public static Result plan(DefaultPlanModuleInput input,
                              ModuleIdentityAssembly identityAssembly) {
        Objects.requireNonNull(input, "input");
        Objects.requireNonNull(identityAssembly, "identityAssembly");
        List<CompilerDiagnostic> diagnostics = new ArrayList<>();
        List<PlannedDefaultClass> planned = new ArrayList<>();

        DefaultDeclaringContext declaringContext =
            DefaultDeclaringContext.of(input.imports(), input.location());
        for (Map.Entry<ClassDeclaration, SymbolTable> entry
                : input.checkResult().classScopes().entrySet()) {
            ClassDeclaration cd = entry.getKey();
            SymbolTable scope = entry.getValue();
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
            PlannedDefaultClass plannedClass = planClass(cd, scope,
                classIdentity, input, declaringContext, diagnostics);
            if (plannedClass != null) {
                planned.add(plannedClass);
            }
        }
        return new Result(diagnostics, planned);
    }

    /**
     * Plans one class declaration; null when any gate or default defect
     * fired for the class (the diagnostics were appended to
     * {@code diagnostics}).
     */
    private static PlannedDefaultClass planClass(ClassDeclaration cd,
            SymbolTable scope, CanonicalClassIdentity classIdentity,
            DefaultPlanModuleInput input,
            DefaultDeclaringContext declaringContext,
            List<CompilerDiagnostic> diagnostics) {
        List<CompilerDiagnostic> classDiagnostics = new ArrayList<>();
        List<CompilerClassDefaultEntry> entries = new ArrayList<>();
        List<DefaultResourceOccurrence> occurrences = new ArrayList<>();
        Set<SemanticResourceIdentity> seen = new LinkedHashSet<>();

        // Field type resolution runs against the class declaration's
        // checking scope (the declaring lexical context).
        input.nameResolver().setCurrentScope(scope);

        boolean failed = false;
        for (ClassField cf : cd.fields()) {
            if (!cf.optional() && cf.defaultExpr().isEmpty()) {
                // D2 declaration-shape gate: a required-present field
                // without a default is not valid (spec §Class
                // declaration :679-680).
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E4001,
                    "Class field without default is not valid: field '"
                        + cf.name() + "' of class '" + cd.name()
                        + "' must provide a default value expression",
                    cf.span().range()));
                failed = true;
                continue;
            }
            Type fieldType = input.nameResolver().resolveTypeNode(cf.type());
            if (fieldType == null || fieldType == Type.Error.INSTANCE) {
                // Defensive: an unresolved field type never reaches
                // planning (phase 3 fails first).
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "default planning failed: field '" + cf.name()
                        + "' of class '" + cd.name()
                        + "' has no resolved field type",
                    cf.span().range()));
                failed = true;
                continue;
            }
            String runtimeTypeDescriptor;
            try {
                runtimeTypeDescriptor = input.descriptors().encode(fieldType);
            } catch (IllegalStateException defect) {
                // Defensive: the descriptor encoder is total for the
                // pre-registered identity set.
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "default planning failed: field '" + cf.name()
                        + "' of class '" + cd.name()
                        + "' has no canonical runtime descriptor ("
                        + defect.getMessage() + ")",
                    cf.span().range()));
                failed = true;
                continue;
            }

            if (cf.defaultExpr().isEmpty()) {
                // Optional field without a declared default.
                entries.add(new CompilerClassDefaultEntry(cf.name(),
                    fieldType, runtimeTypeDescriptor, true, null));
                continue;
            }
            ExpressionNode def = cf.defaultExpr().get();
            Type defType = input.checkResult().typeMap().get(def);
            if (defType == null) {
                // Defensive: the checker records a type for every
                // checked default subexpression.
                classDiagnostics.add(CompilerDiagnostic.error(
                    DiagnosticCode.E6005,
                    "default planning failed: the default of field '"
                        + cf.name() + "' of class '" + cd.name()
                        + "' has no checked type",
                    def.span().range()));
                failed = true;
                continue;
            }
            if (defType != Type.Error.INSTANCE
                    && !defaultTypeAssignable(fieldType, defType)) {
                // D3: each default type-checks against its resolved
                // field type; a mismatch is E3001 at the default
                // expression range (the checker identity, re-verified
                // defensively at the planner).
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
                input.checkResult().typeMap(),
                input.checkResult().scopeMap(), input.imports(),
                input.classification(), input.location(), input.modulePath(),
                input.program(),
                (typeNode, resolutionScope) -> {
                    input.nameResolver().setCurrentScope(resolutionScope);
                    return input.nameResolver().resolveTypeNode(typeNode);
                },
                DefaultIrRecorder.qualifiedClassAliasesOf(cf.type()));
            DefaultIrNode ir = recorder.record(def, scope, fieldType);
            classDiagnostics.addAll(recorder.awaitDiagnostics());
            if (!recorder.awaitDiagnostics().isEmpty()) {
                failed = true;
            }
            if (cf.optional()) {
                // An optional field's declared default is checked but
                // never evaluates (D2, runtime page D1): the plan entry
                // keeps the field declared — in class source order,
                // optional with no default expression, so construction
                // and fromJson accept provided values for it — while no
                // default expression, no runtime resource occurrence,
                // and no evaluator ever exist for it. The recorded IR
                // stays an input for the serializer's metadata only.
                entries.add(new CompilerClassDefaultEntry(cf.name(),
                    fieldType, runtimeTypeDescriptor, true, null));
                continue;
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

    /**
     * The checker's assignment compatibility for a default against its
     * field type (mirrors {@code TypeChecker.isAssignable}).
     */
    static boolean defaultTypeAssignable(Type expected, Type actual) {
        if (Types.equals(expected, actual)) {
            return true;
        }
        if (expected instanceof Type.Nullable nullable) {
            if (Types.equals(nullable.inner(), actual)) {
                return true;
            }
            if (actual instanceof Type.Null) {
                return true;
            }
        }
        if (expected instanceof Type.Func ef
                && actual instanceof Type.Func af) {
            return Types.isAssignable(af, ef);
        }
        return false;
    }
}
