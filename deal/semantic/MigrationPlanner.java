package deal.semantic;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ContinueStatement;
import deal.ast.DeleteStatement;
import deal.ast.Either;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.HasExpr;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.ImportDeclaration;
import deal.ast.IndexExpr;
import deal.ast.LiteralExpr;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.CheckResult;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.FieldInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticProfile;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The route planner of the pre-lowering foundation (F4, one component):
 * one deterministic {@link ModuleRoutePlan} per target over the closed
 * routing rules, with the closed plan-time E6005-vs-LEGACY-reroute
 * split.
 *
 * <p><b>Closed routing rules (applied in dependency order).</b></p>
 * <ol>
 *   <li>{@code LEGACY_SAFE_INT} profile → every implementation module
 *       {@code LEGACY}, {@code shadowModules} empty (never lowered).</li>
 *   <li>Rule 2 ({@code STDLIB_TIME_CONFLICT}, inert since K7): a module
 *       whose manifest requires {@code STDLIB_TIME_CONFLICT} (never
 *       claimed since the four-part line trigger and its propagation
 *       are retired) → {@code LEGACY} in every purpose,
 *       including {@code COMMON_SHADOW} — never a shadow entry. The rule
 *       stays as the closed-set surface the capability catalog and the
 *       validator's empty-evidence rule still consume.</li>
 *   <li>Rule 2b (ISSUE-0574 bytes guard, parent S1b): a module whose
 *       manifest carries the plan-time {@code bytesBearing} marker →
 *       {@code LEGACY} in every purpose — {@code PUBLIC_BUILD} pre- and
 *       post-activation, {@code COMMON_SHADOW} even when
 *       shadow-requested (never a shadow entry), and
 *       {@code LEGACY_REGRESSION}. Deterministic, plan-time-only,
 *       never an error; the plan records the bytes-exception reason in
 *       its {@code bytesExceptions} route-report set.</li>
 *   <li>{@code PUBLIC_BUILD + PRE_ACTIVATION} → every implementation
 *       module {@code LEGACY}; {@code shadowModules} empty. Production
 *       SHARED routing is unreachable by construction in this release
 *       state.</li>
 *   <li>{@code PUBLIC_BUILD + V1_2_ACTIVE} → a module is {@code SHARED}
 *       only when every capability in its manifest is {@code PROMOTED}
 *       for the target in the capability registry (F7's capability ×
 *       target lookup) and its mixed ABI edges satisfy the plan-time
 *       index checks below. A module that fails any index check raises
 *       E6005 per the closed split — these are index-fact checks, never
 *       reroute conditions. A module with a non-{@code PROMOTED}
 *       capability reroutes {@code LEGACY} at plan time, before
 *       emission: never an error, never a within-run fallback. This arm
 *       exists structurally and is unreachable in this epic because the
 *       release registry is all {@code SHADOW} (ISSUE-0241 promotes).</li>
 *   <li>{@code COMMON_SHADOW + DEAL_V1_2_INT32} → requested modules are
 *       recorded as shadow SHARED entries in {@code shadowModules};
 *       shadow entries never drive production publication. Only the
 *       closed {@code shadowRequests} argument names requested modules —
 *       there is no other shadow-selection surface.</li>
 * </ol>
 *
 * <p><b>Plan-time error split (closed).</b> E6005 is raised at plan time
 * only for internally inconsistent checked/interface facts: the
 * interface index contradicts the checked project (an input module
 * missing from the index or wrongly classified, an index
 * IMPLEMENTATION entry without an input module, a manifest/input
 * mismatch, an import resolving outside the dependency-ordered index, or
 * an import kind contradicting the index entry), an import of a SHARED
 * module has no resolved export entry in the index, an imported export's
 * entry is absent or ill-formed (missing name or declared type), a
 * {@code ClassInterface} has no {@code constructionEntry}, an
 * initialization contract is not {@code ONCE_AFTER_DEPENDENCIES}, or the
 * index's {@code formatVersion} contradicts the invocation (the pinned
 * interface version is {@code deal.semantic-interface/1}; any other
 * value is an inconsistent fact). Every E6005 flows through
 * {@link FailureContractRegistry} with
 * {@code LoweringFailureDetail {module, capability: MODULES,
 * validatorRule: ROUTE_INTERNAL_ERROR_SENTINEL, semanticProfile,
 * irVersion, origin}}. Profile/purpose contradictions are rejected at
 * invocation resolution before checking/lowering (F1) and never reach
 * the planner as E6005 conditions; the planner's defensive guard raises
 * {@link IllegalArgumentException} for an inconsistent invocation, a
 * registry whose digest differs from the invocation's recorded digest,
 * shadow requests outside the {@code COMMON_SHADOW} contract, a
 * manifest/input coverage mismatch, or an entry module outside the
 * input — producer-defect wiring guards, never part of the closed E6005
 * split.</p>
 *
 * <p><b>Determinism.</b> Closed rules, dependency-order iteration, the
 * first-reference-order ABI edge list, and the single canonical JSON
 * facility make repeated builds byte-identical with stable
 * {@code invocationHash}/{@code planId}: {@code invocationHash =
 * SHA-256(canonical JSON {purpose, semanticProfile, releaseState,
 * capabilityRegistryHash, interfaceIndexDigest, target})} (F4),
 * {@code planId = "plan-" + first 16 hex chars of invocationHash}. The
 * staging-tree nonce of the publication stage exists only in on-disk
 * tree names — never in the plan, any record, or any hash.</p>
 *
 * <p><b>Plan-time {@link TargetModuleAbi} records (F5).</b> One record
 * per legacy dependency of a shared module, derived from the index
 * facts: {@code moduleId}, {@code target},
 * {@code artifactOwner: RETAINED_LUAJIT|RETAINED_JVM}, the project
 * {@code semanticProfile}, and {@code classFactoryAbi}/
 * {@code classLayoutAbi} copied from the module's
 * {@code ClassInterface} records. {@code exportedDescriptors} is empty
 * at plan time (ISSUE-0233); the emission-owned realization fields are
 * absent (null) and completed during staging (ISSUE-0239). The planner
 * never invents retained wrapper names, sync-invocation entry names,
 * async-handle protocol records, or load keys.</p>
 *
 * <p>The computation is strictly read-only over the checked facts — no
 * AST, checker, or symbol-table mutation — and this epic's closed rules
 * contain no plan-time edge-incompatibility reroute condition (such
 * rules are added only by ISSUE-0239 under parent verification 3): the
 * reroute arm covers profile/purpose/capability ineligibility only.</p>
 */
public final class MigrationPlanner {

    /**
     * The planner fact-defect identifier carried as the E6005
     * {@code validatorRule} (foundation F4): a planner fact-defect
     * identifier, not a {@code SemanticIrValidator} rule — the closed
     * 14-condition validator rule set is unchanged.
     */
    public static final String ROUTE_INTERNAL_ERROR_SENTINEL =
        "ROUTE_INTERNAL_ERROR_SENTINEL";

    private MigrationPlanner() {
        // Static planning surface only; no instances.
    }

    // =========================================================================
    // Public planning surface
    // =========================================================================

    /**
     * Produces exactly one {@link ModuleRoutePlan} per target (foundation
     * F4) — the closed routing rules applied in dependency order over
     * the checked project, the interface index, and the already-computed
     * dependency-ordered manifests.
     *
     * @param invocation     the release-owned compiler invocation; non-null
     * @param registry       the release-owned capability registry (F7); non-null
     * @param input          the checked project input (implementation
     *                       modules in dependency order); non-null
     * @param index          the project interface index covering the full
     *                       dependency closure; non-null
     * @param manifests      the dependency-ordered manifests, one per
     *                       input module; non-null
     * @param target         the closed plan target; non-null
     * @param shadowRequests the COMMON_SHADOW shadow-requested module ids
     *                       (empty for every other purpose); non-null
     * @return the route-plan result: the plan plus no diagnostics on
     *         success, {@code null} plan plus one E6005 on an
     *         internally inconsistent fact (never a silent reroute for a
     *         fact defect; ineligibility reroutes with zero diagnostics)
     * @throws IllegalArgumentException for a producer-defect wiring
     *         guard — an inconsistent invocation, a registry digest
     *         differing from the invocation's recorded digest, shadow
     *         requests outside the COMMON_SHADOW contract, a
     *         manifest/input coverage mismatch, or an entry module
     *         outside the input
     */
    public static RoutePlanResult planRoutes(CompilerInvocation invocation,
                                             CapabilityRegistry registry,
                                             CheckedProjectInput input,
                                             ProjectInterfaceIndex index,
                                             List<SemanticRequirementManifest> manifests,
                                             Target target,
                                             Set<ModuleId> shadowRequests) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(registry, "registry must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(index, "index must not be null");
        Objects.requireNonNull(manifests, "manifests must not be null");
        Objects.requireNonNull(target, "target must not be null");
        Objects.requireNonNull(shadowRequests, "shadowRequests must not be null");
        if (shadowRequests.stream().anyMatch(Objects::isNull)) {
            throw new IllegalArgumentException("shadowRequests must not contain null");
        }
        requireInvocationConsistent(invocation);
        requireRegistryMatchesInvocation(invocation, registry);
        requireShadowRequestsConsistent(invocation, input, shadowRequests);
        requireManifestCoverage(input, manifests);

        try {
            Map<ModuleId, SemanticRequirementManifest> manifestByModule =
                verifyGlobalFacts(invocation, input, index, manifests);

            Map<ModuleId, ModuleRoute> entries = new LinkedHashMap<>();
            Set<ModuleId> shadowModules = new LinkedHashSet<>();
            Set<ModuleId> bytesExceptions = new LinkedHashSet<>();
            Map<ModuleId, TargetModuleAbi> abiByModule = new LinkedHashMap<>();

            for (CheckedModuleInput module : input.modules()) {
                SemanticRequirementManifest manifest =
                    manifestByModule.get(module.moduleId());
                boolean shadowRequested = shadowRequests.contains(module.moduleId());
                // Rule 2b's route-accounting record (ISSUE-0574): a
                // bytes-bearing module is a recorded retained-route
                // bytes exception in every purpose — the plan's
                // bytesExceptions set is the route report naming the
                // reason (never an error, never a shadow entry, never a
                // within-run fallback).
                if (manifest.bytesBearing()) {
                    bytesExceptions.add(module.moduleId());
                }
                ModuleRoute route = routeOf(invocation, registry, target, manifest,
                    shadowRequested);
                if (route == ModuleRoute.SHARED
                        && !allImplementationImportsRouted(module, entries)) {
                    // A tolerated declaration-only import cycle (foundation
                    // F3's atomic-component input shape): the shared
                    // module's implementation import has no route yet in
                    // the planner's single ordered pass. Silent plan-time
                    // LEGACY reroute — complete retained modules selected
                    // before lowering, never E6005, never a within-run
                    // fallback (the rollback reroute contract).
                    route = ModuleRoute.LEGACY;
                }
                if (route == ModuleRoute.SHARED) {
                    verifySharedEdges(invocation, module, index);
                    if (shadowRequested) {
                        shadowModules.add(module.moduleId());
                    }
                    collectAbiEdges(module, entries, index, invocation, target,
                        abiByModule);
                }
                entries.put(module.moduleId(), route);
            }

            String interfaceIndexDigest = index.interfaceIndexDigest();
            String invocationHash =
                deriveInvocationHash(invocation, interfaceIndexDigest, target);
            String planId = planIdFor(invocationHash);
            ModuleRoutePlan plan = new ModuleRoutePlan(target, entries, shadowModules,
                bytesExceptions, List.copyOf(abiByModule.values()), invocationHash,
                planId);
            return new RoutePlanResult(plan, List.of());
        } catch (FactDefect defect) {
            return new RoutePlanResult(null, List.of(defect.diagnostic()));
        }
    }

    // =========================================================================
    // Closed routing rules (F4, applied in dependency order)
    // =========================================================================

    /**
     * The closed routing decision for one implementation module: rule 1
     * (legacy profile), rule 2 ({@code STDLIB_TIME_CONFLICT}, an inert
     * marker no manifest claims since K7), rule 2b
     * (the bytes-bearing marker, ISSUE-0574), rule 3
     * ({@code PUBLIC_BUILD + PRE_ACTIVATION}), rule 4
     * ({@code PUBLIC_BUILD + V1_2_ACTIVE} promotion gate), rule 5
     * ({@code COMMON_SHADOW} shadow request).
     */
    private static ModuleRoute routeOf(CompilerInvocation invocation,
                                       CapabilityRegistry registry, Target target,
                                       SemanticRequirementManifest manifest,
                                       boolean shadowRequested) {
        if (invocation.semanticProfile() == SemanticProfile.LEGACY_SAFE_INT) {
            return ModuleRoute.LEGACY; // rule 1: never lowered
        }
        if (manifest.capabilities().contains(SemanticCapability.STDLIB_TIME_CONFLICT)) {
            return ModuleRoute.LEGACY; // rule 2: never shared in any purpose
        }
        if (manifest.bytesBearing()) {
            // Rule 2b (ISSUE-0574): a bytes-bearing module stays on the
            // retained route in every purpose, before the purpose switch so
            // the CONTAINERS_AND_STRINGS promotion never flips it SHARED.
            // The production path never consults the route plan (C3); the
            // marker is the retained route report's own subject.
            // Deterministic, plan-time-only, never an error.
            return ModuleRoute.LEGACY;
        }
        switch (invocation.purpose()) {
            case PUBLIC_BUILD -> {
                if (invocation.releaseState() == ReleaseState.PRE_ACTIVATION) {
                    return ModuleRoute.LEGACY; // rule 3: production SHARED unreachable
                }
                // Rule 4 (V1_2_ACTIVE): SHARED only when every manifest
                // capability is PROMOTED for the target; otherwise a
                // silent plan-time LEGACY reroute (never an error, never a
                // within-run fallback).
                return allPromoted(registry, target, manifest)
                    ? ModuleRoute.SHARED
                    : ModuleRoute.LEGACY;
            }
            case COMMON_SHADOW -> {
                // Rule 5: requested modules are recorded as shadow SHARED
                // entries; shadow entries never drive production
                // publication. Rules 1-2 already applied above.
                return shadowRequested ? ModuleRoute.SHARED : ModuleRoute.LEGACY;
            }
            case LEGACY_REGRESSION -> {
                // Defensive: LEGACY_REGRESSION resolves with
                // LEGACY_SAFE_INT, so rule 1 already produced LEGACY.
                return ModuleRoute.LEGACY;
            }
        }
        // Unreachable: the switch covers the closed three-value purpose
        // enum exhaustively.
        throw new IllegalStateException("unreachable purpose " + invocation.purpose());
    }

    /** F7's capability × target lookup over every manifest capability. */
    private static boolean allPromoted(CapabilityRegistry registry, Target target,
                                       SemanticRequirementManifest manifest) {
        for (SemanticCapability capability : manifest.capabilities()) {
            if (registry.state(capability, target) != CapabilityRegistry.State.PROMOTED) {
                return false;
            }
        }
        return true;
    }

    // =========================================================================
    // Plan-time index checks — the closed E6005 split (F4)
    // =========================================================================

    /**
     * The global fact verification, run before routing: the six closed
     * fact-defect classes over the index/checked-project/manifest facts.
     * Returns the dependency-ordered manifest lookup used by routing.
     * Fails fast with the first defect in deterministic order (never a
     * silent reroute for a fact defect).
     */
    private static Map<ModuleId, SemanticRequirementManifest> verifyGlobalFacts(
            CompilerInvocation invocation, CheckedProjectInput input,
            ProjectInterfaceIndex index, List<SemanticRequirementManifest> manifests)
            throws FactDefect {

        // 1. formatVersion contradicts the pinned interface version
        //    (defensive: the index record guards the value at construction;
        //    this is the planner's producer-defect backstop, F4).
        CompilerDiagnostic versionDefect = verifyFormatVersionFact(invocation,
            input.entryModule(), index.formatVersion());
        if (versionDefect != null) {
            throw new FactDefect(versionDefect);
        }

        // 2. The index contradicts the checked project: input↔index
        //    coverage and classification, and import resolution. (Manifest
        //    coverage is a producer-defect wiring guard checked at the API
        //    boundary — never an E6005 class.)
        Map<ModuleId, CheckedModuleInput> inputByModule = new LinkedHashMap<>();
        for (CheckedModuleInput module : input.modules()) {
            inputByModule.put(module.moduleId(), module);
            ExternalModuleInterface indexEntry = index.modules().get(module.moduleId());
            if (indexEntry == null) {
                throw defect(invocation, module.moduleId(),
                    "implementation module is missing from the interface index (the "
                        + "index contradicts the checked project)");
            }
            if (indexEntry.kind() != ExternalModuleKind.IMPLEMENTATION) {
                throw defect(invocation, module.moduleId(),
                    "the index classifies the implementation module as "
                        + indexEntry.kind() + " (the index contradicts the checked "
                        + "project)");
            }
        }
        for (ExternalModuleInterface indexEntry : index.modules().values()) {
            if (indexEntry.kind() == ExternalModuleKind.IMPLEMENTATION
                    && !inputByModule.containsKey(indexEntry.moduleId())) {
                throw defect(invocation, indexEntry.moduleId(),
                    "the index carries an IMPLEMENTATION entry without a checked input "
                        + "module (the index contradicts the checked project)");
            }
        }

        Map<ModuleId, SemanticRequirementManifest> manifestByModule =
            new LinkedHashMap<>();
        for (SemanticRequirementManifest manifest : manifests) {
            manifestByModule.put(manifest.moduleId(), manifest);
        }
        for (CheckedModuleInput module : input.modules()) {
            for (ResolvedImport resolvedImport : module.imports()) {
                ExternalModuleInterface targetEntry =
                    index.modules().get(resolvedImport.resolvedModuleId());
                if (targetEntry == null) {
                    throw defect(invocation, module.moduleId(),
                        "import '" + resolvedImport.modulePath() + "' of module '"
                            + module.moduleId() + "' resolves to '"
                            + resolvedImport.resolvedModuleId()
                            + "' which is missing from the dependency-ordered index "
                            + "(the index contradicts the checked project)");
                }
                if (targetEntry.kind() != resolvedImport.kind()) {
                    throw defect(invocation, module.moduleId(),
                        "import '" + resolvedImport.modulePath() + "' of module '"
                            + module.moduleId() + "' records kind "
                            + resolvedImport.kind() + " but the index entry carries "
                            + targetEntry.kind() + " (inconsistent resolution facts)");
                }
            }
        }

        // 3. Defensive invariant guards (F2/F4): every index entry's
        //    initialization contract and every ClassInterface's
        //    constructionEntry are producer-defect guards over the pinned
        //    single-value/derived invariants.
        for (ExternalModuleInterface indexEntry : index.modules().values()) {
            CompilerDiagnostic initDefect = verifyInitializationFact(invocation,
                indexEntry.moduleId(), indexEntry.initialization());
            if (initDefect != null) {
                throw new FactDefect(initDefect);
            }
            for (ClassInterface classEntry : indexEntry.classes()) {
                CompilerDiagnostic constructionDefect = verifyConstructionEntryFact(
                    invocation, indexEntry.moduleId(), classEntry.classId(),
                    classEntry.constructionEntry());
                if (constructionDefect != null) {
                    throw new FactDefect(constructionDefect);
                }
            }
        }

        return manifestByModule;
    }

    /**
     * The shared-module edge checks (F4 rule 4's index checks; run for
     * production SHARED and shadow SHARED modules alike): every used
     * export of an imported implementation module — legacy or shared —
     * has a complete export entry in the index (name and declared type
     * present). The used-export facts come from a read-only walk over
     * the shared module's AST: a member access whose object identifier
     * resolves through the module-scope chain to the import's
     * {@code ModuleSymbol} and whose field the checker's phase-1 export
     * map names — the same fact sources the checker used, never a
     * re-resolution of imports. The name gate makes the walk
     * false-positive-free: a local binding shadowing the alias can never
     * turn a non-export field into a fact defect.
     */
    private static void verifySharedEdges(CompilerInvocation invocation,
                                          CheckedModuleInput shared,
                                          ProjectInterfaceIndex index)
            throws FactDefect {
        for (ResolvedImport resolvedImport : shared.imports()) {
            if (resolvedImport.kind() != ExternalModuleKind.IMPLEMENTATION) {
                continue; // stdlib/host entries are index entries, never route entries
            }
            ExternalModuleInterface targetEntry =
                index.modules().get(resolvedImport.resolvedModuleId());
            if (targetEntry == null) {
                throw defect(invocation, shared.moduleId(),
                    "import '" + resolvedImport.modulePath() + "' of module '"
                        + shared.moduleId() + "' resolves outside the interface index "
                        + "(the index contradicts the checked project)");
            }
            for (String exportName : usedExportNames(shared, resolvedImport.alias())) {
                ExportInterface exportEntry = findExport(targetEntry.exports(),
                    exportName);
                if (exportEntry == null) {
                    throw defect(invocation, shared.moduleId(),
                        "imported export '" + exportName + "' of module '"
                            + resolvedImport.resolvedModuleId()
                            + "' has no export entry in the interface index (absent "
                            + "export entry)");
                }
                if (exportEntry.name().isEmpty()
                        || exportEntry.declaredType().isEmpty()) {
                    throw defect(invocation, shared.moduleId(),
                        "imported export '" + exportName + "' of module '"
                            + resolvedImport.resolvedModuleId()
                            + "' has an ill-formed export entry (missing name or "
                            + "declared type)");
                }
            }
        }
    }

    private static ExportInterface findExport(List<ExportInterface> exports, String name) {
        for (ExportInterface exportEntry : exports) {
            if (exportEntry.name().equals(name)) {
                return exportEntry;
            }
        }
        return null;
    }

    /**
     * The read-only used-export walk (F4): the export names of the
     * imported module the shared module references, in first-occurrence
     * source order.
     */
    private static List<String> usedExportNames(CheckedModuleInput shared, String alias) {
        ExportUseScanner scanner = new ExportUseScanner(shared.checks().symbolTable(),
            alias);
        for (StatementNode statement : shared.ast().statements()) {
            scanner.walkStatement(statement);
        }
        return scanner.names();
    }

    /**
     * The AST walk collecting member accesses on one imported module
     * symbol. A field is collected only when the object identifier
     * resolves to the import's {@code ModuleSymbol} and the field is a
     * name of its phase-1 export map — the same facts the checker
     * consumed, so a shadowing local binding never produces a fact
     * defect.
     */
    private static final class ExportUseScanner {
        private final SymbolTable symbolTable;
        private final String alias;
        private final LinkedHashSet<String> names = new LinkedHashSet<>();

        ExportUseScanner(SymbolTable symbolTable, String alias) {
            this.symbolTable = symbolTable;
            this.alias = alias;
        }

        List<String> names() {
            return new ArrayList<>(names);
        }

        void walkStatement(StatementNode statement) {
            switch (statement) {
                case ImportDeclaration ignored -> { }
                case ExportDeclaration exportDeclaration ->
                    walkStatement(exportDeclaration.declaration());
                case ClassDeclaration classDeclaration -> {
                    for (ClassField field : classDeclaration.fields()) {
                        if (field.defaultExpr().isPresent()) {
                            walkExpression(field.defaultExpr().get());
                        }
                    }
                }
                case FunctionDeclaration functionDeclaration -> {
                    if (functionDeclaration.body() != null) {
                        walkStatement(functionDeclaration.body());
                    }
                }
                case VariableDeclaration variableDeclaration ->
                    walkExpression(variableDeclaration.initializer());
                case ReturnStatement returnStatement -> {
                    if (returnStatement.expr().isPresent()) {
                        walkExpression(returnStatement.expr().get());
                    }
                }
                case IfStatement ifStatement -> {
                    walkExpression(ifStatement.condition());
                    walkStatement(ifStatement.thenBlock());
                    if (ifStatement.elseBranch().isPresent()) {
                        walkEither(ifStatement.elseBranch().get());
                    }
                }
                case WhileStatement whileStatement -> {
                    walkExpression(whileStatement.condition());
                    walkStatement(whileStatement.body());
                }
                case ForStatement forStatement -> {
                    if (forStatement.init().isPresent()) {
                        walkForInit(forStatement.init().get());
                    }
                    if (forStatement.condition().isPresent()) {
                        walkExpression(forStatement.condition().get());
                    }
                    if (forStatement.update().isPresent()) {
                        walkExpression(forStatement.update().get());
                    }
                    walkStatement(forStatement.body());
                }
                case ForOfStatement forOfStatement -> {
                    walkExpression(forOfStatement.iterable());
                    walkStatement(forOfStatement.body());
                }
                case BreakStatement ignored -> { }
                case ContinueStatement ignored -> { }
                case ExpressionStatement expressionStatement ->
                    walkExpression(expressionStatement.expr());
                case DeleteStatement deleteStatement ->
                    walkExpression(deleteStatement.target());
                case TryStatement tryStatement -> {
                    walkStatement(tryStatement.tryBlock());
                    walkStatement(tryStatement.catchBlock());
                }
                case ThrowStatement throwStatement ->
                    walkExpression(throwStatement.expr());
                case Block block -> {
                    for (StatementNode nested : block.statements()) {
                        walkStatement(nested);
                    }
                }
            }
        }

        private void walkEither(Either<IfStatement, Block> branch) {
            switch (branch) {
                case Either.Left<IfStatement, Block> left ->
                    walkStatement(left.value());
                case Either.Right<IfStatement, Block> right ->
                    walkStatement(right.value());
            }
        }

        private void walkForInit(ForInit init) {
            switch (init) {
                case ForInit.VarDecl varDecl -> walkStatement(varDecl.decl());
                case ForInit.AssignExpr assignExpr -> walkExpression(assignExpr.expr());
            }
        }

        private void walkExpression(ExpressionNode expression) {
            switch (expression) {
                case LiteralExpr ignored -> { }
                case IdentifierExpr ignored -> { }
                case BinaryExpr binaryExpr -> {
                    walkExpression(binaryExpr.left());
                    walkExpression(binaryExpr.right());
                }
                case UnaryExpr unaryExpr -> walkExpression(unaryExpr.expr());
                case CallExpr callExpr -> {
                    walkExpression(callExpr.callee());
                    for (ExpressionNode argument : callExpr.args()) {
                        walkExpression(argument);
                    }
                }
                case MemberAccessExpr memberAccessExpr -> {
                    walkExpression(memberAccessExpr.object());
                    if (memberAccessExpr.object() instanceof IdentifierExpr id) {
                        Symbol symbol = symbolTable.resolve(id.name());
                        if (symbol instanceof Symbol.ModuleSymbol moduleSymbol
                                && moduleSymbol.name().equals(alias)
                                && moduleSymbol.exports()
                                    .containsKey(memberAccessExpr.field())) {
                            names.add(memberAccessExpr.field());
                        }
                    }
                }
                case IndexExpr indexExpr -> {
                    walkExpression(indexExpr.array());
                    walkExpression(indexExpr.index());
                }
                case ArrayLiteralExpr arrayLiteralExpr -> {
                    for (ExpressionNode element : arrayLiteralExpr.elements()) {
                        walkExpression(element);
                    }
                }
                case ObjectLiteralExpr objectLiteralExpr -> {
                    for (Property property : objectLiteralExpr.properties()) {
                        walkExpression(property.value());
                    }
                }
                case FunctionExpr functionExpr -> walkStatement(functionExpr.body());
                case HasExpr hasExpr -> walkExpression(hasExpr.object());
                case AssignmentExpr assignmentExpr -> {
                    walkExpression(assignmentExpr.target());
                    walkExpression(assignmentExpr.value());
                }
                case TemplateLiteralExpr templateLiteralExpr -> {
                    for (ExpressionNode part : templateLiteralExpr.parts()) {
                        walkExpression(part);
                    }
                }
                case AwaitExpression awaitExpression ->
                    walkExpression(awaitExpression.callee());
            }
        }
    }

    // =========================================================================
    // Plan-time TargetModuleAbi derivation (F5)
    // =========================================================================

    /**
     * The plan-time routedness precondition of a SHARED route: every
     * implementation import of the module must already carry a route
     * entry in the planner's single ordered pass. A missing route is the
     * tolerated declaration-only cycle shape (foundation F3 — the
     * orchestrator's atomic-component input) and reroutes the module
     * LEGACY at plan time, never an exception and never an E6005 class.
     */
    private static boolean allImplementationImportsRouted(CheckedModuleInput module,
                                                          Map<ModuleId, ModuleRoute> entries) {
        for (ResolvedImport resolvedImport : module.imports()) {
            if (resolvedImport.kind() != ExternalModuleKind.IMPLEMENTATION) {
                continue;
            }
            if (!entries.containsKey(resolvedImport.resolvedModuleId())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Collects one plan-time {@link TargetModuleAbi} per legacy
     * Collects one plan-time {@link TargetModuleAbi} per legacy
     * dependency of the shared module (F4/F5): the planner-owned fields
     * copied from the index — {@code classFactoryAbi} from the
     * F2-derived {@code constructionEntry} values and
     * {@code classLayoutAbi} from the declaration-order
     * {@code FieldInterface} lists. {@code exportedDescriptors} is empty
     * at plan time (ISSUE-0233); every emission-owned field is absent
     * (null) until staging (ISSUE-0239). The planner never invents
     * retained wrapper names, sync-invocation entry names, async-handle
     * protocol records, or load keys.
     */
    private static void collectAbiEdges(CheckedModuleInput shared,
                                        Map<ModuleId, ModuleRoute> entries,
                                        ProjectInterfaceIndex index,
                                        CompilerInvocation invocation, Target target,
                                        Map<ModuleId, TargetModuleAbi> abiByModule) {
        for (ResolvedImport resolvedImport : shared.imports()) {
            if (resolvedImport.kind() != ExternalModuleKind.IMPLEMENTATION) {
                continue;
            }
            ModuleRoute targetRoute = entries.get(resolvedImport.resolvedModuleId());
            if (targetRoute == null) {
                throw new IllegalArgumentException(
                    "the shared module '" + shared.moduleId() + "' imports '"
                        + resolvedImport.resolvedModuleId() + "' which has no route "
                        + "yet (the input is not in dependency order — an internal "
                        + "wiring defect)");
            }
            if (targetRoute != ModuleRoute.LEGACY) {
                continue; // shared modules' own ABI manifests come from emission
            }
            if (abiByModule.containsKey(resolvedImport.resolvedModuleId())) {
                continue; // one record per legacy dependency
            }
            ExternalModuleInterface dependencyEntry =
                index.modules().get(resolvedImport.resolvedModuleId());
            abiByModule.put(resolvedImport.resolvedModuleId(),
                derivePlanTimeAbi(invocation, target, dependencyEntry));
        }
    }

    private static TargetModuleAbi derivePlanTimeAbi(CompilerInvocation invocation,
                                                     Target target,
                                                     ExternalModuleInterface dependencyEntry) {
        Map<ClassId, ClassFactoryId> factoryAbi = new LinkedHashMap<>();
        Map<ClassId, List<FieldInterface>> layoutAbi =
            new LinkedHashMap<>();
        for (ClassInterface classEntry : dependencyEntry.classes()) {
            factoryAbi.put(classEntry.classId(), classEntry.constructionEntry());
            layoutAbi.put(classEntry.classId(), classEntry.fields());
        }
        return new TargetModuleAbi(dependencyEntry.moduleId(), target,
            target == Target.LUAJIT ? ArtifactOwner.RETAINED_LUAJIT
                : ArtifactOwner.RETAINED_JVM,
            invocation.semanticProfile(), factoryAbi, layoutAbi, Map.of(),
            null, null, null, null, null);
    }

    // =========================================================================
    // Hashes (F4): invocationHash through T3's serializer, planId derivation
    // =========================================================================

    /**
     * The pinned invocation-hash derivation (F4):
     * {@code SHA-256(canonical JSON {purpose, semanticProfile,
     * releaseState, capabilityRegistryHash, interfaceIndexDigest,
     * target})} over the single canonical JSON facility (T3/S2) — the
     * fully determined input of {@code planId} and the
     * byte-identical-plan gate. The staging-tree nonce never enters this
     * hash, the plan, or any record (F4/F6).
     *
     * @param invocation           the invocation; non-null
     * @param interfaceIndexDigest the index digest (foundation F2); non-null
     * @param target               the plan target; non-null
     * @return the lowercase 64-character hex digest
     */
    public static String deriveInvocationHash(CompilerInvocation invocation,
                                              String interfaceIndexDigest,
                                              Target target) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(interfaceIndexDigest,
            "interfaceIndexDigest must not be null");
        Objects.requireNonNull(target, "target must not be null");
        CanonicalJson.Value json = CanonicalJson.obj(
            CanonicalJson.e("capabilityRegistryHash",
                CanonicalJson.str(invocation.capabilityRegistryHash())),
            CanonicalJson.e("interfaceIndexDigest",
                CanonicalJson.str(interfaceIndexDigest)),
            CanonicalJson.e("purpose", CanonicalJson.str(invocation.purpose().name())),
            CanonicalJson.e("releaseState",
                CanonicalJson.str(invocation.releaseState().name())),
            CanonicalJson.e("semanticProfile",
                CanonicalJson.str(invocation.semanticProfile().name())),
            CanonicalJson.e("target", CanonicalJson.str(target.name())));
        return CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(json));
    }

    /**
     * The pinned plan-id derivation (F4): {@code "plan-" + first 16 hex
     * chars of invocationHash}.
     *
     * @param invocationHash the lowercase 64-character hex invocation
     *                       hash; non-null
     * @return the plan id
     */
    public static String planIdFor(String invocationHash) {
        Objects.requireNonNull(invocationHash, "invocationHash must not be null");
        if (!invocationHash.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException(
                "invocationHash must be the lowercase 64-character hex SHA-256 digest; "
                    + "got \"" + invocationHash + "\"");
        }
        return "plan-" + invocationHash.substring(0, 16);
    }

    // =========================================================================
    // Producer-defect guards (IllegalArgumentException — never E6005)
    // =========================================================================

    /**
     * The defensive invocation-consistency guard (F1/F4; A1): the
     * planner admits exactly the closed purpose×profile matrix —
     * {@code PUBLIC_BUILD} → the profile must equal
     * {@link CompilerProfileProvider#publicProfile(ReleaseState)};
     * {@code COMMON_SHADOW} → {@code DEAL_V1_2_INT32} regardless of
     * release state (pre- and post-activation shadowing);
     * {@code LEGACY_REGRESSION} → {@code LEGACY_SAFE_INT} regardless of
     * release state (the retention window extends past activation).
     * Purpose/profile contradictions are rejected at invocation
     * resolution by {@link CompilerProfileProvider} and at the record by
     * {@link CompilerInvocation} before checking/lowering, so the
     * planner never observes a mismatched invocation; this backstop
     * raises {@link IllegalArgumentException} (a producer-defect guard,
     * not a planner E6005 condition). The closed F4 routing rules are
     * unchanged: this guard is the planner's defensive wiring backstop,
     * not a routing rule.
     */
    private static void requireInvocationConsistent(CompilerInvocation invocation) {
        switch (invocation.purpose()) {
            case PUBLIC_BUILD -> {
                SemanticProfile derived =
                    CompilerProfileProvider.publicProfile(invocation.releaseState());
                if (invocation.semanticProfile() != derived) {
                    throw new IllegalArgumentException(
                        "the PUBLIC_BUILD profile must equal the release-state "
                            + "derivation: " + invocation.releaseState() + " derives "
                            + derived + ", got " + invocation.semanticProfile());
                }
            }
            case COMMON_SHADOW -> {
                if (invocation.semanticProfile() != SemanticProfile.DEAL_V1_2_INT32) {
                    throw new IllegalArgumentException(
                        "COMMON_SHADOW requires DEAL_V1_2_INT32 regardless of release "
                            + "state; got " + invocation.semanticProfile() + " under "
                            + invocation.releaseState());
                }
            }
            case LEGACY_REGRESSION -> {
                if (invocation.semanticProfile() != SemanticProfile.LEGACY_SAFE_INT) {
                    throw new IllegalArgumentException(
                        "LEGACY_REGRESSION requires LEGACY_SAFE_INT regardless of "
                            + "release state; got " + invocation.semanticProfile()
                            + " under " + invocation.releaseState());
                }
            }
        }
    }

    /**
     * The defensive registry-consistency guard (F1/F7): the planner's
     * capability × target lookups must run over the release registry the
     * invocation recorded. A different registry is a producer-defect
     * wiring guard ({@link IllegalArgumentException}), never part of the
     * closed E6005 split.
     */
    private static void requireRegistryMatchesInvocation(CompilerInvocation invocation,
                                                         CapabilityRegistry registry) {
        if (!registry.capabilityRegistryHash()
                .equals(invocation.capabilityRegistryHash())) {
            throw new IllegalArgumentException(
                "the capability registry digest must equal the invocation's recorded "
                    + "capabilityRegistryHash (F1/F7): the invocation records the "
                    + "release registry's digest and the planner must route over the "
                    + "same release state");
        }
    }

    /**
     * The defensive shadow-request guard (F4): shadow requests are
     * admissible only for {@code COMMON_SHADOW} and must name input
     * modules. A violation is an internal-harness wiring defect
     * ({@link IllegalArgumentException}) — the closed E6005 split names
     * exactly the six fact-defect classes and nothing else.
     */
    private static void requireShadowRequestsConsistent(CompilerInvocation invocation,
                                                        CheckedProjectInput input,
                                                        Set<ModuleId> shadowRequests) {
        if (!shadowRequests.isEmpty()
                && invocation.purpose() != InvocationPurpose.COMMON_SHADOW) {
            throw new IllegalArgumentException(
                "shadow requests are admissible only for COMMON_SHADOW; purpose "
                    + invocation.purpose() + " records no shadow entries (foundation F4 "
                    + "rule 5)");
        }
        for (ModuleId shadow : shadowRequests) {
            boolean inInput = false;
            for (CheckedModuleInput module : input.modules()) {
                if (module.moduleId().equals(shadow)) {
                    inInput = true;
                    break;
                }
            }
            if (!inInput) {
                throw new IllegalArgumentException(
                    "the shadow request names module '" + shadow
                        + "' which is outside the checked project (an "
                        + "internal-harness wiring defect)");
            }
        }
    }

    /**
     * The defensive manifest-coverage guard (F4): the planner consumes
     * exactly one dependency-ordered manifest per input module (the
     * {@link LoweringSupport} product). A duplicate, missing, or
     * out-of-project manifest — and a duplicate input module or an entry
     * module outside the input — is an internal wiring defect
     * ({@link IllegalArgumentException}), never one of the closed six
     * E6005 fact-defect classes: the planner can never silently invent a
     * route for a module without facts.
     */
    private static void requireManifestCoverage(CheckedProjectInput input,
                                                List<SemanticRequirementManifest> manifests) {
        boolean entryInInput = false;
        Map<ModuleId, Boolean> seenInput = new LinkedHashMap<>();
        for (CheckedModuleInput module : input.modules()) {
            if (module.moduleId().equals(input.entryModule())) {
                entryInInput = true;
            }
            if (seenInput.put(module.moduleId(), Boolean.TRUE) != null) {
                throw new IllegalArgumentException(
                    "the checked project carries module '" + module.moduleId()
                        + "' twice (an internal wiring defect)");
            }
        }
        if (!entryInInput) {
            throw new IllegalArgumentException(
                "the entry module '" + input.entryModule()
                    + "' is not among the input modules (an internal wiring defect)");
        }
        Map<ModuleId, Boolean> seenManifest = new LinkedHashMap<>();
        for (SemanticRequirementManifest manifest : manifests) {
            if (seenManifest.put(manifest.moduleId(), Boolean.TRUE) != null) {
                throw new IllegalArgumentException(
                    "the manifest list carries module '" + manifest.moduleId()
                        + "' twice (an internal wiring defect)");
            }
            if (!seenInput.containsKey(manifest.moduleId())) {
                throw new IllegalArgumentException(
                    "the manifest names module '" + manifest.moduleId()
                        + "' which is outside the checked project (an internal "
                        + "wiring defect)");
            }
        }
        for (CheckedModuleInput module : input.modules()) {
            if (!seenManifest.containsKey(module.moduleId())) {
                throw new IllegalArgumentException(
                    "implementation module '" + module.moduleId()
                        + "' has no manifest in the dependency-ordered manifest list "
                        + "(an internal wiring defect)");
            }
        }
    }

    // =========================================================================
    // Fact-check seams (the single E6005 checks; defensive over record-guarded
    // invariants — the defect arms are exercised directly by the planner test)
    // =========================================================================

    /**
     * The formatVersion fact check (F4): the pinned interface version is
     * {@code deal.semantic-interface/1}; any other value is an
     * inconsistent fact. The index record guards the value at
     * construction; this check is the planner's single producer-defect
     * backstop over the same invariant.
     *
     * @param invocation    the invocation; non-null
     * @param entryModule   the payload module (the entry module); non-null
     * @param formatVersion the index's format version; nullable in the
     *                      defect arm
     * @return null when consistent, else the E6005 diagnostic
     */
    static CompilerDiagnostic verifyFormatVersionFact(CompilerInvocation invocation,
                                                      ModuleId entryModule,
                                                      String formatVersion) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(entryModule, "entryModule must not be null");
        if (ProjectInterfaceIndex.FORMAT_VERSION.equals(formatVersion)) {
            return null;
        }
        return factDefectDiagnostic(invocation, entryModule,
            "the index formatVersion contradicts the pinned "
                + ProjectInterfaceIndex.FORMAT_VERSION + ": "
                + String.valueOf(formatVersion));
    }

    /**
     * The initialization fact check (F4): every index entry's
     * initialization contract is {@code ONCE_AFTER_DEPENDENCIES} — the
     * surface's single pinned value, enforced by the closed enum and the
     * record guard; this check is the planner's single producer-defect
     * backstop over the same invariant.
     *
     * @param invocation     the invocation; non-null
     * @param moduleId       the payload module; non-null
     * @param initialization the index entry's initialization mode;
     *                       nullable in the defect arm
     * @return null when consistent, else the E6005 diagnostic
     */
    static CompilerDiagnostic verifyInitializationFact(CompilerInvocation invocation,
                                                       ModuleId moduleId,
                                                       InitializationMode initialization) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(moduleId, "moduleId must not be null");
        if (initialization == InitializationMode.ONCE_AFTER_DEPENDENCIES) {
            return null;
        }
        return factDefectDiagnostic(invocation, moduleId,
            "the initialization contract is not ONCE_AFTER_DEPENDENCIES: "
                + String.valueOf(initialization));
    }

    /**
     * The constructionEntry fact check (F4): every
     * {@code ClassInterface} carries its derived route-independent
     * {@code constructionEntry} — an absent entry is a producer defect,
     * never a legitimate state (F2: "F4's completeness check is a
     * defensive guard over that invariant"). The record guard rejects a
     * null entry at construction; this check is the planner's single
     * producer-defect backstop over the same invariant.
     *
     * @param invocation        the invocation; non-null
     * @param moduleId          the payload module; non-null
     * @param classId           the class identity; non-null
     * @param constructionEntry the class entry's construction entry;
     *                          nullable in the defect arm
     * @return null when consistent, else the E6005 diagnostic
     */
    static CompilerDiagnostic verifyConstructionEntryFact(CompilerInvocation invocation,
                                                          ModuleId moduleId,
                                                          ClassId classId,
                                                          ClassFactoryId constructionEntry) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(moduleId, "moduleId must not be null");
        Objects.requireNonNull(classId, "classId must not be null");
        if (constructionEntry != null) {
            return null;
        }
        return factDefectDiagnostic(invocation, moduleId,
            "the ClassInterface of class " + classId.text()
                + " has no constructionEntry (producer defect)");
    }

    // =========================================================================
    // E6005 construction through the failure contract registry (T5)
    // =========================================================================

    /** An internally inconsistent checked/interface fact (never a crash). */
    private static final class FactDefect extends Exception {
        private final CompilerDiagnostic diagnostic;

        FactDefect(CompilerDiagnostic diagnostic) {
            super(diagnostic.message());
            this.diagnostic = diagnostic;
        }

        CompilerDiagnostic diagnostic() {
            return diagnostic;
        }
    }

    private static FactDefect defect(CompilerInvocation invocation, ModuleId module,
                                     String reason) {
        return new FactDefect(factDefectDiagnostic(invocation, module, reason));
    }

    /**
     * The single plan-time E6005 construction: the prescribed
     * {@code LoweringFailureDetail} payload with {@code capability:
     * MODULES} and {@code validatorRule:
     * ROUTE_INTERNAL_ERROR_SENTINEL}, instantiated by the failure
     * contract registry — no component hand-crafts an E6005 message.
     */
    private static CompilerDiagnostic factDefectDiagnostic(
            CompilerInvocation invocation, ModuleId module, String reason) {
        LoweringFailureDetail detail = new LoweringFailureDetail(module.path(),
            SemanticCapability.MODULES, ROUTE_INTERNAL_ERROR_SENTINEL,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "MigrationPlanner " + ROUTE_INTERNAL_ERROR_SENTINEL + " (" + reason + ")");
        return FailureContractRegistry.e6005(detail);
    }
}
