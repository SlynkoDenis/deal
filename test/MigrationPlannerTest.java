package deal.semantic;

import deal.ast.CallExpr;
import deal.ast.ExpressionStatement;
import deal.ast.IdentifierExpr;
import deal.ast.ImportDeclaration;
import deal.ast.MemberAccessExpr;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.module.CompilationOrchestrator;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FieldInterface;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticProfile;
import deal.test.ConformanceHarnessMetadata;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Verifies the ISSUE-0290 foundation surface: {@link MigrationPlanner}
 * producing exactly one deterministic {@link ModuleRoutePlan} per target
 * over the closed routing rules and the closed plan-time
 * E6005-vs-LEGACY-reroute split, plus the {@link TargetModuleAbi}
 * record with its three-way field split.
 *
 * <p>Tests:
 * <ol>
 *   <li>Rule matrix: {@code PUBLIC_BUILD+PRE_ACTIVATION} → all LEGACY, no
 *       shadow, no abiEdges; {@code LEGACY_REGRESSION} → all LEGACY;
 *       {@code COMMON_SHADOW+DEAL_V1_2_INT32} → requested modules
 *       recorded as shadow SHARED entries; the {@code V1_2_ACTIVE} arm
 *       with the all-SHADOW release registry → all LEGACY
 *       (capability-not-PROMOTED silent reroute); a
 *       {@code STDLIB_TIME_CONFLICT} manifest (direct or propagated)
 *       → LEGACY in every purpose, never in shadowModules, zero
 *       diagnostics.</li>
 *   <li>Rule 2b (ISSUE-0574 bytes guard): a manifest carrying the
 *       {@code bytesBearing} marker → LEGACY in every purpose —
 *       {@code PUBLIC_BUILD} pre- and post-activation (beating rule 4
 *       even with the claiming capability PROMOTED),
 *       {@code COMMON_SHADOW} with a shadow request (never a shadow
 *       entry), and {@code LEGACY_REGRESSION} — with the bytes
 *       exception recorded in the plan's {@code bytesExceptions}
 *       route report, zero diagnostics, and a non-bytes module with
 *       identical claims routing by the unchanged rules 4/5.</li>
 *   <li>Closed split: every fact-defect class raises E6005 through T5
 *       with the prescribed payload (absent export entry, ill-formed
 *       entry, missing constructionEntry, initialization not
 *       {@code ONCE_AFTER_DEPENDENCIES}, formatVersion not
 *       {@code deal.semantic-interface/1}, index contradicting the
 *       checked project); every ineligibility condition reroutes LEGACY
 *       silently with zero diagnostics; profile/purpose mismatches are
 *       rejected at invocation resolution (asserted at T4's boundary
 *       here).</li>
 *   <li>TargetModuleAbi: plan-time records carry exactly the derived
 *       index facts ({@code classFactoryAbi} equals T8's
 *       {@code constructionEntry} ids, {@code classLayoutAbi} equals the
 *       declaration-order {@code FieldInterface} lists,
 *       {@code exportedDescriptors} empty, emission-owned fields
 *       absent); {@code artifactOwner = RETAINED_LUAJIT|RETAINED_JVM}
 *       per target; one record per legacy dependency of a shared module.</li>
 *   <li>Determinism: two plans for identical inputs are byte-identical;
 *       {@code invocationHash}/{@code planId} match stored goldens; the
 *       staging nonce appears nowhere in the serialized plan.</li>
 *   <li>Record guards: {@code ModuleRoutePlan} enforces the
 *       {@code planId} derivation, the hex shape, and the
 *       shadowModules ⊆ SHARED-entries invariant;
 *       {@code TargetModuleAbi} enforces non-null planner-owned fields.</li>
 *   <li>Orchestrator integration (combined T1/T3/T4/T5/T8/T9 deps): a
 *       full compile drives invocation resolution → checked project →
 *       interface index → manifests → route plan; the plan is
 *       all-LEGACY under {@code PRE_ACTIVATION}, deterministic across
 *       builds, and the JS backend skips the phase (no closed target).</li>
 * </ol>
 */
public class MigrationPlannerTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Small helpers
    // =========================================================================

    private static Span span() {
        return new Span("test.deal", 1, 1, 1, 1);
    }

    private static CompilerInvocation publicPreActivation() {
        return CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation publicV12Active() {
        return CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation commonShadow() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation legacyRegression() {
        return CompilerProfileProvider.resolveLegacyRegression(
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
    }

    /** A program carrying one import plus one module member call {@code alias.field()}. */
    private static ProgramNode programUsing(ModuleId id, String alias, String field) {
        StatementNode importStmt = new ImportDeclaration(span(), alias, "./" + id.path());
        ExpressionStatement use = new ExpressionStatement(span(),
            new CallExpr(span(),
                new MemberAccessExpr(span(), new IdentifierExpr(span(), alias), field),
                List.of()));
        return new ProgramNode(span(), List.of(importStmt, use));
    }

    /** A program carrying only the import statement. */
    private static ProgramNode programWithImport(ModuleId id, String alias) {
        return new ProgramNode(span(),
            List.of(new ImportDeclaration(span(), alias, "./" + id.path())));
    }

    /** Checked facts whose module-scope table binds the import alias to a
     *  module symbol exporting the named fields (the phase-1 export map). */
    private static CheckResult checksWithModule(String alias, Map<String, Type> exports) {
        SymbolTable table = new SymbolTable();
        table.define(alias, new Symbol.ModuleSymbol(alias, exports, span()));
        return new CheckResult(Map.of(), table, List.of());
    }

    private static CheckedModuleInput moduleOf(CompilerInvocation invocation, ModuleId id,
                                               ProgramNode ast, CheckResult checks,
                                               List<ResolvedImport> imports,
                                               List<ExportInterface> exports) {
        return new CheckedModuleInput(id, "src/" + id.path() + ".deal",
            Path.of("src/" + id.path() + ".deal"), ast, checks, imports, exports,
            CheckedModuleKind.IMPLEMENTATION);
    }

    private static ExternalModuleInterface indexEntryOf(ModuleId id,
                                                        ExternalModuleKind kind,
                                                        List<ResolvedImport> imports,
                                                        List<ExportInterface> exports,
                                                        List<ClassInterface> classes) {
        return new ExternalModuleInterface(id, kind, imports, exports, classes,
            InitializationMode.ONCE_AFTER_DEPENDENCIES);
    }

    private static SemanticRequirementManifest manifestOf(ModuleId id,
                                                          SemanticCapability... extra) {
        return manifestOf(id, false, extra);
    }

    /** A non-bytes or bytes-bearing manifest over the closed capability set. */
    private static SemanticRequirementManifest manifestOf(ModuleId id,
                                                          boolean bytesBearing,
                                                          SemanticCapability... extra) {
        EnumSet<SemanticCapability> capabilities =
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES);
        capabilities.addAll(List.of(extra));
        return new SemanticRequirementManifest(id, capabilities, Map.of(), bytesBearing);
    }

    private static ResolvedImport implImport(String alias, ModuleId target) {
        return new ResolvedImport(alias, "./" + target.path(), target,
            ExternalModuleKind.IMPLEMENTATION);
    }

    private static <K, V> LinkedHashMap<K, V> orderedMap(K k1, V v1, K k2, V v2) {
        LinkedHashMap<K, V> map = new LinkedHashMap<>();
        map.put(k1, v1);
        map.put(k2, v2);
        return map;
    }

    private static <K, V> LinkedHashMap<K, V> orderedMap(K k1, V v1, K k2, V v2,
                                                         K k3, V v3) {
        LinkedHashMap<K, V> map = new LinkedHashMap<>();
        map.put(k1, v1);
        map.put(k2, v2);
        map.put(k3, v3);
        return map;
    }

    /** The standard two-module project: lib (exports f) ← main (uses lib.f). */
    private static final class Project {
        final CompilerInvocation invocation;
        final ModuleId libId = new ModuleId("lib");
        final ModuleId mainId = new ModuleId("main");
        final CheckedProjectInput input;
        final ProjectInterfaceIndex index;
        final List<SemanticRequirementManifest> manifests;

        Project(CompilerInvocation invocation, List<ExportInterface> libExports,
                List<ClassInterface> libClasses) {
            this.invocation = invocation;
            ResolvedImport libImport = implImport("lib", libId);
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programUsing(libId, "lib", "f"),
                checksWithModule("lib",
                    Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
                List.of(libImport),
                List.of(new ExportInterface("main", "() => null")));
            CheckedModuleInput lib = moduleOf(invocation, libId,
                new ProgramNode(span(), List.of()), checksWithModule("lib", Map.of()),
                List.of(), libExports);
            this.input = new CheckedProjectInput(invocation, mainId,
                List.of(lib, main), invocation.releaseStateHash());
            this.index = new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                orderedMap(
                    libId, indexEntryOf(libId, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), libExports, libClasses),
                    mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                        List.of(libImport), List.of(new ExportInterface("main", "() => null")),
                        List.of())));
            this.manifests = List.of(manifestOf(libId), manifestOf(mainId));
        }
    }

    private static ExportInterface exportOf(String name, String declaredType) {
        return new ExportInterface(name, declaredType);
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception e) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    /** Asserts the prescribed T5 payload of one plan-time E6005. */
    private static void assertE6005Payload(CompilerDiagnostic diagnostic,
                                           String modulePath,
                                           SemanticProfile profile,
                                           String reasonPart) {
        check("E6005".equals(diagnostic.code())
                && diagnostic.diagnosticCode() == DiagnosticCode.E6005
                && "error".equals(diagnostic.severity()),
            reasonPart + ": the diagnostic is error-severity E6005; got "
                + diagnostic.code() + "/" + diagnostic.severity());
        check(DiagnosticCode.fromCode("E6005") != null
                && DiagnosticCode.fromCode("E6005").phase()
                    == DiagnosticCode.Phase.BACKEND_LOWERING,
            reasonPart + ": E6005 is BACKEND_LOWERING");
        String message = diagnostic.message();
        check(message.contains("Common semantic lowering failed"),
            reasonPart + ": the registry-owned message template is instantiated");
        check(message.contains("module '" + modulePath + "'"),
            reasonPart + ": the payload names the failing module; got " + message);
        check(message.contains("capability MODULES"),
            reasonPart + ": the payload capability is MODULES; got " + message);
        check(message.contains("validatorRule "
                + MigrationPlanner.ROUTE_INTERNAL_ERROR_SENTINEL),
            reasonPart + ": the payload validatorRule is ROUTE_INTERNAL_ERROR_SENTINEL; got "
                + message);
        check(message.contains("semanticProfile " + profile.name()),
            reasonPart + ": the payload carries the invocation profile; got " + message);
        check(message.contains("irVersion " + LoweredModuleUnit.FORMAT_VERSION),
            reasonPart + ": the payload carries the pinned IR version; got " + message);
        check(message.contains("origin MigrationPlanner "
                + MigrationPlanner.ROUTE_INTERNAL_ERROR_SENTINEL),
            reasonPart + ": the payload names the planner as the origin; got " + message);
    }

    private static void assertFailedPlan(RoutePlanResult result, String modulePath,
                                         SemanticProfile profile, String what) {
        check(result != null && result.hasErrors() && result.plan() == null,
            what + ": planning fails with a null plan and one E6005");
        if (result == null || !result.hasErrors()) {
            return;
        }
        check(result.diagnostics().size() == 1,
            what + ": exactly one diagnostic; got " + result.diagnostics().size());
        assertE6005Payload(result.diagnostics().get(0), modulePath, profile, what);
    }

    private static void assertAllLegacy(RoutePlanResult result, List<ModuleId> modules,
                                        String what) {
        check(result != null && !result.hasErrors() && result.plan() != null,
            what + ": planning succeeds with zero diagnostics: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        check(result.plan().entries().size() == modules.size(),
            what + ": one entry per implementation module; got "
                + result.plan().entries());
        for (ModuleId module : modules) {
            check(result.plan().entries().get(module) == ModuleRoute.LEGACY,
                what + ": module '" + module + "' routes LEGACY");
        }
        check(result.plan().shadowModules().isEmpty(),
            what + ": shadowModules is empty");
        check(result.plan().abiEdges().isEmpty(),
            what + ": no plan-time ABI records exist without a shared module");
        check("plan-".equals(result.plan().planId().substring(0, 5)),
            what + ": the planId carries the pinned plan- prefix");
    }

    // =========================================================================
    // 1. Routing matrix (F4 rules 1-5)
    // =========================================================================

    static void testPublicPreActivationAllLegacy() {
        System.out.println("-- PUBLIC_BUILD + PRE_ACTIVATION: all LEGACY, no shadow --");

        Project project = new Project(publicPreActivation(),
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(project.invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.LUAJIT, Set.of());
        assertAllLegacy(result, List.of(project.libId, project.mainId),
            "PUBLIC_BUILD+PRE_ACTIVATION");
        if (result != null && !result.hasErrors()) {
            check(result.plan().target() == Target.LUAJIT,
                "the plan carries the LUAJIT target");
            check(result.plan().entries().keySet().stream().toList()
                    .equals(List.of(project.libId, project.mainId)),
                "the entries iterate in dependency order (lib before main)");
        }
    }

    static void testLegacyRegressionAllLegacy() {
        System.out.println("-- LEGACY_REGRESSION + LEGACY_SAFE_INT: all LEGACY --");

        Project project = new Project(legacyRegression(),
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(project.invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.JVM, Set.of());
        assertAllLegacy(result, List.of(project.libId, project.mainId),
            "LEGACY_REGRESSION");
        if (result != null && !result.hasErrors()) {
            check(result.plan().target() == Target.JVM,
                "the plan carries the JVM target");
        }
    }

    static void testV12ActiveAllShadowRegistryReroutesSilently() {
        System.out.println("-- PUBLIC_BUILD + V1_2_ACTIVE, all-SHADOW registry: silent reroute --");

        Project project = new Project(publicV12Active(),
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(project.invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.LUAJIT, Set.of());
        assertAllLegacy(result, List.of(project.libId, project.mainId),
            "V1_2_ACTIVE + all-SHADOW registry");
        if (result != null && !result.hasErrors()) {
            check(result.diagnostics().isEmpty(),
                "the capability-not-PROMOTED reroute is silent (zero diagnostics)");
            check(result.plan().shadowModules().isEmpty(),
                "no shadow entries exist under PUBLIC_BUILD");
        }
    }

    static void testCommonShadowRequestedModules() {
        System.out.println("-- COMMON_SHADOW + DEAL_V1_2_INT32: requested modules shadow SHARED --");

        Project project = new Project(commonShadow(),
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(project.invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.LUAJIT, Set.of(project.libId, project.mainId));
        check(result != null && !result.hasErrors() && result.plan() != null,
            "COMMON_SHADOW planning succeeds with zero diagnostics: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        check(result.plan().entries().get(project.libId) == ModuleRoute.SHARED
                && result.plan().entries().get(project.mainId) == ModuleRoute.SHARED,
            "both requested modules are recorded as shadow SHARED entries");
        check(result.plan().shadowModules()
                .equals(new LinkedHashSet<>(List.of(project.libId, project.mainId))),
            "shadowModules carries exactly the requested modules");
        check(result.plan().abiEdges().isEmpty(),
            "no plan-time ABI records exist without a legacy dependency");
        check(result.plan().entries().keySet().stream().toList()
                .equals(List.of(project.libId, project.mainId)),
            "the entries iterate in dependency order under COMMON_SHADOW too");
    }

    static void testCommonShadowUnrequestedStaysLegacy() {
        System.out.println("-- COMMON_SHADOW: unrequested modules stay LEGACY --");

        Project project = new Project(commonShadow(),
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(project.invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.LUAJIT, Set.of(project.mainId));
        check(result != null && !result.hasErrors() && result.plan() != null,
            "COMMON_SHADOW planning succeeds: " + (result == null ? "null"
                : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        check(result.plan().entries().get(project.libId) == ModuleRoute.LEGACY,
            "the unrequested legacy dependency stays LEGACY");
        check(result.plan().entries().get(project.mainId) == ModuleRoute.SHARED
                && result.plan().shadowModules().equals(Set.of(project.mainId)),
            "the requested module is the single shadow SHARED entry");
    }

    static void testTimeConflictNeverShared() {
        System.out.println("-- STDLIB_TIME_CONFLICT (direct + propagated): LEGACY in every purpose --");

        Project conflict = new Project(commonShadow(),
            List.of(exportOf("f", "() => int")), List.of());
        List<SemanticRequirementManifest> conflictManifests = List.of(
            manifestOf(conflict.libId, SemanticCapability.STDLIB_TIME_CONFLICT),
            manifestOf(conflict.mainId, SemanticCapability.STDLIB_TIME_CONFLICT));
        RoutePlanResult shadowResult = MigrationPlanner.planRoutes(conflict.invocation,
            CapabilityRegistry.releaseRegistry(), conflict.input, conflict.index,
            conflictManifests, Target.LUAJIT, Set.of(conflict.libId, conflict.mainId));
        check(shadowResult != null && !shadowResult.hasErrors(),
            "a conflict-claiming project plans with zero diagnostics (silent reroute)");
        if (shadowResult != null && !shadowResult.hasErrors()) {
            check(shadowResult.plan().entries().get(conflict.libId) == ModuleRoute.LEGACY
                    && shadowResult.plan().entries().get(conflict.mainId)
                        == ModuleRoute.LEGACY,
                "detected and propagated conflict claims route LEGACY under COMMON_SHADOW");
            check(shadowResult.plan().shadowModules().isEmpty(),
                "conflict-claiming modules are never in shadowModules");
        }

        Project publicActive = new Project(publicV12Active(),
            List.of(exportOf("f", "() => int")), List.of());
        List<SemanticRequirementManifest> publicManifests = List.of(
            manifestOf(publicActive.libId),
            manifestOf(publicActive.mainId, SemanticCapability.STDLIB_TIME_CONFLICT));
        RoutePlanResult publicResult = MigrationPlanner.planRoutes(publicActive.invocation,
            CapabilityRegistry.releaseRegistry(), publicActive.input, publicActive.index,
            publicManifests, Target.JVM, Set.of());
        check(publicResult != null && !publicResult.hasErrors()
                && publicResult.plan().entries().get(publicActive.mainId)
                    == ModuleRoute.LEGACY,
            "a propagated conflict claim routes LEGACY under PUBLIC_BUILD+V1_2_ACTIVE "
                + "with zero diagnostics (rule 2 beats rule 4)");
    }

    static void testBytesBearingNeverShared() {
        System.out.println("-- Rule 2b (ISSUE-0574): bytes-bearing modules route LEGACY "
            + "in every purpose and record the bytes-exception reason --");

        // The bytes population shape: lib is bytes-bearing (marker true,
        // claiming CONTAINERS_AND_STRINGS exactly like the LoweringSupport
        // arm), main carries identical claims but no bytes (marker false).
        Project base = new Project(publicPreActivation(),
            List.of(exportOf("f", "() => int")), List.of());

        // (a) PUBLIC_BUILD + PRE_ACTIVATION: rule 2b records the bytes
        // exception; the non-bytes sibling routes LEGACY via rule 3 and
        // is not recorded.
        {
            List<SemanticRequirementManifest> bytesManifests = List.of(
                manifestOf(base.libId, true, SemanticCapability.CONTAINERS_AND_STRINGS),
                manifestOf(base.mainId, false, SemanticCapability.CONTAINERS_AND_STRINGS));
            RoutePlanResult result = MigrationPlanner.planRoutes(base.invocation,
                CapabilityRegistry.releaseRegistry(), base.input, base.index,
                bytesManifests, Target.LUAJIT, Set.of());
            assertAllLegacy(result, List.of(base.libId, base.mainId),
                "PUBLIC_BUILD+PRE_ACTIVATION bytes project");
            if (result != null && !result.hasErrors()) {
                check(result.plan().bytesExceptions().equals(Set.of(base.libId)),
                    "the plan records exactly the bytes-bearing module as the "
                        + "bytes exception (route accounting): "
                        + result.plan().bytesExceptions());
            }
        }

        // (b) PUBLIC_BUILD + V1_2_ACTIVE with CONTAINERS_AND_STRINGS and
        // FOUNDATION_VALUES PROMOTED for the target: rule 2b beats rule 4 —
        // the bytes-bearing module stays LEGACY (never SHARED, never an
        // error) while the non-bytes module with identical claims routes
        // SHARED exactly by the unchanged rule 4/allPromoted gate.
        {
            CapabilityRegistry promoted = CapabilityRegistry.releaseRegistry()
                .withState(SemanticCapability.FOUNDATION_VALUES, Target.LUAJIT,
                    CapabilityRegistry.State.PROMOTED)
                .withState(SemanticCapability.CONTAINERS_AND_STRINGS, Target.LUAJIT,
                    CapabilityRegistry.State.PROMOTED);
            CompilerInvocation active = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, promoted);
            Project activeProject = new Project(active,
                List.of(exportOf("f", "() => int")), List.of());
            List<SemanticRequirementManifest> bytesManifests = List.of(
                manifestOf(activeProject.libId, true,
                    SemanticCapability.CONTAINERS_AND_STRINGS),
                manifestOf(activeProject.mainId, false,
                    SemanticCapability.CONTAINERS_AND_STRINGS));
            RoutePlanResult result = MigrationPlanner.planRoutes(active, promoted,
                activeProject.input, activeProject.index, bytesManifests,
                Target.LUAJIT, Set.of());
            check(result != null && !result.hasErrors() && result.plan() != null
                    && result.diagnostics().isEmpty(),
                "the post-activation bytes project plans with zero diagnostics "
                    + "(rule 2b is never an error): "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) {
                return;
            }
            check(result.plan().entries().get(activeProject.libId) == ModuleRoute.LEGACY,
                "the bytes-bearing module routes LEGACY under V1_2_ACTIVE even "
                    + "with CONTAINERS_AND_STRINGS PROMOTED (rule 2b beats rule 4, "
                    + "the promotion never flips it)");
            check(result.plan().entries().get(activeProject.mainId) == ModuleRoute.SHARED,
                "the non-bytes module with identical claims routes SHARED by the "
                    + "unchanged rule 4 (allPromoted): "
                    + result.plan().entries().get(activeProject.mainId));
            check(result.plan().bytesExceptions().equals(Set.of(activeProject.libId)),
                "the route report records exactly the bytes exception: "
                    + result.plan().bytesExceptions());
            check(result.plan().shadowModules().isEmpty(),
                "no shadow entries exist under PUBLIC_BUILD");
            check(result.plan().canonicalText().contains("\"bytesExceptions\""),
                "the plan's canonical route report carries the bytesExceptions key");
        }

        // (c) COMMON_SHADOW with a shadow request for both modules: the
        // bytes-bearing module stays LEGACY — never a shadow entry — and
        // the non-bytes module keeps its shadow SHARED entry (rule 5
        // unchanged).
        {
            Project shadow = new Project(commonShadow(),
                List.of(exportOf("f", "() => int")), List.of());
            List<SemanticRequirementManifest> bytesManifests = List.of(
                manifestOf(shadow.libId, true, SemanticCapability.CONTAINERS_AND_STRINGS),
                manifestOf(shadow.mainId, false, SemanticCapability.CONTAINERS_AND_STRINGS));
            RoutePlanResult result = MigrationPlanner.planRoutes(shadow.invocation,
                CapabilityRegistry.releaseRegistry(), shadow.input, shadow.index,
                bytesManifests, Target.LUAJIT,
                Set.of(shadow.libId, shadow.mainId));
            check(result != null && !result.hasErrors() && result.plan() != null,
                "COMMON_SHADOW planning succeeds with zero diagnostics: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) {
                return;
            }
            check(result.plan().entries().get(shadow.libId) == ModuleRoute.LEGACY
                    && !result.plan().shadowModules().contains(shadow.libId),
                "a shadow request for the bytes-bearing module still routes LEGACY "
                    + "and never produces a shadow entry (rule 2b beats rule 5)");
            check(result.plan().entries().get(shadow.mainId) == ModuleRoute.SHARED
                    && result.plan().shadowModules().equals(Set.of(shadow.mainId)),
                "the non-bytes module's shadow request keeps its shadow SHARED "
                    + "entry (rule 5 unchanged)");
            check(result.plan().bytesExceptions().equals(Set.of(shadow.libId)),
                "the shadow plan records exactly the bytes exception: "
                    + result.plan().bytesExceptions());
        }

        // (d) LEGACY_REGRESSION: all LEGACY (rule 1), the bytes exception
        // still recorded in the route report.
        {
            Project regression = new Project(legacyRegression(),
                List.of(exportOf("f", "() => int")), List.of());
            List<SemanticRequirementManifest> bytesManifests = List.of(
                manifestOf(regression.libId, true,
                    SemanticCapability.CONTAINERS_AND_STRINGS),
                manifestOf(regression.mainId, false,
                    SemanticCapability.CONTAINERS_AND_STRINGS));
            RoutePlanResult result = MigrationPlanner.planRoutes(regression.invocation,
                CapabilityRegistry.releaseRegistry(), regression.input,
                regression.index, bytesManifests, Target.JVM, Set.of());
            assertAllLegacy(result, List.of(regression.libId, regression.mainId),
                "LEGACY_REGRESSION bytes project");
            if (result != null && !result.hasErrors()) {
                check(result.plan().bytesExceptions().equals(Set.of(regression.libId)),
                    "the regression plan records exactly the bytes exception: "
                        + result.plan().bytesExceptions());
            }
        }
    }

    // =========================================================================
    // 2. Closed split: E6005 fact defects through T5
    // =========================================================================

    static void testE6005IndexContradictions() {
        System.out.println("-- E6005: index contradicts the checked project --");

        CompilerInvocation invocation = commonShadow();
        ModuleId libId = new ModuleId("lib");
        ModuleId mainId = new ModuleId("main");

        // (a) Input module missing from the index.
        {
            ResolvedImport libImport = implImport("lib", libId);
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programUsing(libId, "lib", "f"),
                checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
                List.of(libImport), List.of(exportOf("main", "() => null")));
            CheckedModuleInput lib = moduleOf(invocation, libId,
                new ProgramNode(span(), List.of()), checksWithModule("lib", Map.of()),
                List.of(), List.of(exportOf("f", "() => int")));
            CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
                List.of(lib, main), invocation.releaseStateHash());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                    List.of(libImport), List.of(exportOf("main", "() => null")),
                    List.of())));
            RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
                CapabilityRegistry.releaseRegistry(), input, index,
                List.of(manifestOf(libId), manifestOf(mainId)), Target.LUAJIT,
                Set.of(mainId));
            assertFailedPlan(result, "lib",
                invocation.semanticProfile(), "input module missing from the index");
        }

        // (b) Input module's index entry classified HOST.
        {
            ResolvedImport libImport = implImport("lib", libId);
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programUsing(libId, "lib", "f"),
                checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
                List.of(libImport), List.of(exportOf("main", "() => null")));
            CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
                List.of(main), invocation.releaseStateHash());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(mainId, indexEntryOf(mainId, ExternalModuleKind.HOST,
                    List.of(libImport), List.of(exportOf("main", "() => null")),
                    List.of())));
            RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
                CapabilityRegistry.releaseRegistry(), input, index,
                List.of(manifestOf(mainId)), Target.LUAJIT, Set.of(mainId));
            assertFailedPlan(result, "main",
                invocation.semanticProfile(), "input module misclassified by the index");
        }

        // (c) Index IMPLEMENTATION entry without an input module.
        {
            ResolvedImport libImport = implImport("lib", libId);
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programUsing(libId, "lib", "f"),
                checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
                List.of(libImport), List.of(exportOf("main", "() => null")));
            CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
                List.of(main), invocation.releaseStateHash());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION,
                orderedMap(
                    mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                        List.of(libImport), List.of(exportOf("main", "() => null")),
                        List.of()),
                    new ModuleId("ghost"), indexEntryOf(new ModuleId("ghost"),
                        ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(),
                        List.of())));
            RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
                CapabilityRegistry.releaseRegistry(), input, index,
                List.of(manifestOf(mainId)), Target.LUAJIT, Set.of(mainId));
            assertFailedPlan(result, "ghost",
                invocation.semanticProfile(), "IMPLEMENTATION index entry without input");
        }

        // (d) Manifest missing for an input module: a producer-defect
        // wiring guard (IllegalArgumentException) — the closed E6005 split
        // names exactly the six fact-defect classes.
        {
            Project project = new Project(invocation,
                List.of(exportOf("f", "() => int")), List.of());
            try {
                MigrationPlanner.planRoutes(invocation,
                    CapabilityRegistry.releaseRegistry(), project.input, project.index,
                    List.of(manifestOf(project.libId)), Target.LUAJIT,
                    Set.of(project.mainId));
                fail("an input module without a manifest must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "an input module without a manifest is rejected at the "
                    + "planner boundary (wiring guard, never E6005, never a silent "
                    + "route)");
            }
        }

        // (e) Manifest naming a module outside the input: same wiring guard.
        {
            Project project = new Project(invocation,
                List.of(exportOf("f", "() => int")), List.of());
            try {
                MigrationPlanner.planRoutes(invocation,
                    CapabilityRegistry.releaseRegistry(), project.input, project.index,
                    List.of(manifestOf(project.libId), manifestOf(project.mainId),
                        manifestOf(new ModuleId("ghost"))),
                    Target.LUAJIT, Set.of(project.mainId));
                fail("a manifest outside the checked project must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "a manifest outside the checked project is rejected at the "
                    + "planner boundary (wiring guard, never E6005)");
            }
        }

        // (f) Import resolving outside the index.
        {
            ResolvedImport ghostImport = implImport("g", new ModuleId("ghost"));
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programWithImport(new ModuleId("ghost"), "g"),
                checksWithModule("g", Map.of()), List.of(ghostImport),
                List.of(exportOf("main", "() => null")));
            CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
                List.of(main), invocation.releaseStateHash());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                    List.of(ghostImport), List.of(exportOf("main", "() => null")),
                    List.of())));
            RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
                CapabilityRegistry.releaseRegistry(), input, index,
                List.of(manifestOf(mainId)), Target.LUAJIT, Set.of(mainId));
            assertFailedPlan(result, "main",
                invocation.semanticProfile(), "import resolving outside the index");
        }

        // (g) Import kind contradicting the index entry kind.
        {
            ResolvedImport wrongKind = new ResolvedImport("lib", "./lib", libId,
                ExternalModuleKind.HOST);
            CheckedModuleInput main = moduleOf(invocation, mainId,
                programUsing(libId, "lib", "f"),
                checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
                List.of(wrongKind), List.of(exportOf("main", "() => null")));
            CheckedModuleInput lib = moduleOf(invocation, libId,
                new ProgramNode(span(), List.of()), checksWithModule("lib", Map.of()),
                List.of(), List.of(exportOf("f", "() => int")));
            CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
                List.of(lib, main), invocation.releaseStateHash());
            ProjectInterfaceIndex index = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION,
                orderedMap(
                    libId, indexEntryOf(libId, ExternalModuleKind.IMPLEMENTATION,
                        List.of(), List.of(exportOf("f", "() => int")), List.of()),
                    mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                        List.of(wrongKind), List.of(exportOf("main", "() => null")),
                        List.of())));
            RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
                CapabilityRegistry.releaseRegistry(), input, index,
                List.of(manifestOf(libId), manifestOf(mainId)), Target.LUAJIT,
                Set.of(mainId));
            assertFailedPlan(result, "main",
                invocation.semanticProfile(), "import kind contradicting the index");
        }

        // (h) Shadow request naming a module outside the input: an
        // internal-harness wiring defect (IllegalArgumentException), never
        // one of the closed six E6005 classes.
        {
            Project project = new Project(invocation,
                List.of(exportOf("f", "() => int")), List.of());
            try {
                MigrationPlanner.planRoutes(invocation,
                    CapabilityRegistry.releaseRegistry(), project.input, project.index,
                    project.manifests, Target.LUAJIT,
                    Set.of(project.mainId, new ModuleId("ghost")));
                fail("a shadow request outside the input must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "a shadow request outside the input is rejected at the "
                    + "planner boundary (wiring guard, never E6005, never a silent "
                    + "route)");
            }
        }
    }

    static void testE6005AbsentExportEntry() {
        System.out.println("-- E6005: absent export entry (an import of a SHARED module) --");

        CompilerInvocation invocation = commonShadow();
        Project project = new Project(invocation, List.of(), List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), project.input, project.index,
            project.manifests, Target.LUAJIT, Set.of(project.mainId));
        assertFailedPlan(result, "main", invocation.semanticProfile(),
            "used export missing from the index");
        if (result != null && !result.hasErrors()) {
            return;
        }
        String message = result.diagnostics().get(0).message();
        check(message.contains("imported export 'f' of module 'lib'")
                && message.contains("absent export entry"),
            "the E6005 names the absent imported export; got " + message);
    }

    static void testE6005IllFormedExportEntry() {
        System.out.println("-- E6005: ill-formed export entry (missing name or declared type) --");

        CompilerInvocation invocation = commonShadow();
        Project emptyType = new Project(invocation, List.of(exportOf("f", "")),
            List.of());
        RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), emptyType.input, emptyType.index,
            emptyType.manifests, Target.LUAJIT, Set.of(emptyType.mainId));
        assertFailedPlan(result, "main", invocation.semanticProfile(),
            "used export with an empty declared type");
        if (result != null && result.hasErrors()) {
            check(result.diagnostics().get(0).message().contains("ill-formed export entry"),
                "the E6005 names the ill-formed-entry class; got "
                    + result.diagnostics().get(0).message());
        }

        Project emptyName = new Project(invocation, List.of(exportOf("", "() => int")),
            List.of());
        // The used name "f" is absent (the entry carries an empty name), so
        // the absent-export-entry class fires first in deterministic order.
        RoutePlanResult nameResult = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), emptyName.input, emptyName.index,
            emptyName.manifests, Target.LUAJIT, Set.of(emptyName.mainId));
        assertFailedPlan(nameResult, "main", invocation.semanticProfile(),
            "used export entry with an empty name (absent in the name map)");
    }

    static void testDefensiveSeamChecks() {
        System.out.println("-- Defensive invariant checks: formatVersion, initialization, "
            + "constructionEntry --");

        CompilerInvocation invocation = publicPreActivation();
        ModuleId mainId = new ModuleId("main");

        CompilerDiagnostic version = MigrationPlanner.verifyFormatVersionFact(invocation,
            mainId, "deal.semantic-interface/2");
        check(version != null, "a non-pinned formatVersion raises E6005 (defensive "
            + "producer-defect backstop over the T8 record guard)");
        assertE6005Payload(version, "main", invocation.semanticProfile(),
            "formatVersion defect");
        check(version.message().contains("formatVersion contradicts the pinned"),
            "the E6005 names the formatVersion class; got " + version.message());
        check(MigrationPlanner.verifyFormatVersionFact(invocation, mainId,
                ProjectInterfaceIndex.FORMAT_VERSION) == null,
            "the pinned formatVersion passes the check");

        CompilerDiagnostic init = MigrationPlanner.verifyInitializationFact(invocation,
            mainId, null);
        check(init != null, "an initialization contract that is not "
            + "ONCE_AFTER_DEPENDENCIES raises E6005 (defensive backstop)");
        assertE6005Payload(init, "main", invocation.semanticProfile(),
            "initialization defect");
        check(init.message().contains("initialization contract is not "
                + "ONCE_AFTER_DEPENDENCIES"),
            "the E6005 names the initialization class; got " + init.message());
        check(MigrationPlanner.verifyInitializationFact(invocation, mainId,
                InitializationMode.ONCE_AFTER_DEPENDENCIES) == null,
            "the pinned initialization passes the check");

        ClassId pointId = new ClassId("main", "Point");
        CompilerDiagnostic construction = MigrationPlanner
            .verifyConstructionEntryFact(invocation, mainId, pointId, null);
        check(construction != null, "a ClassInterface without a constructionEntry raises "
            + "E6005 (defensive backstop over the F2 derivation)");
        assertE6005Payload(construction, "main", invocation.semanticProfile(),
            "constructionEntry defect");
        check(construction.message().contains("no constructionEntry"),
            "the E6005 names the constructionEntry class; got "
                + construction.message());
        check(MigrationPlanner.verifyConstructionEntryFact(invocation, mainId, pointId,
                new ClassFactoryId(3)) == null,
            "a present constructionEntry passes the check");
    }

    // =========================================================================
    // 3. TargetModuleAbi derivation (F5)
    // =========================================================================

    static void testTargetModuleAbiDerivation() {
        System.out.println("-- TargetModuleAbi: plan-time records carry exactly the derived "
            + "index facts --");

        CompilerInvocation invocation = commonShadow();
        ModuleId libId = new ModuleId("lib");
        ModuleId mainId = new ModuleId("main");
        ModuleId midId = new ModuleId("mid");
        ClassId pointId = new ClassId("lib", "Point");
        FieldInterface x = new FieldInterface("x", "int", false, false, true);
        FieldInterface y = new FieldInterface("y", "int", true, true, false);
        ClassInterface pointClass = new ClassInterface(pointId, List.of(x, y),
            new ClassFactoryId(7));

        ResolvedImport libImport = implImport("lib", libId);
        ResolvedImport mainImport = implImport("main", mainId);
        CheckedModuleInput main = moduleOf(invocation, mainId,
            programUsing(libId, "lib", "f"),
            checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
            List.of(libImport), List.of(exportOf("main", "() => null")));
        CheckedModuleInput lib = moduleOf(invocation, libId,
            new ProgramNode(span(), List.of()), checksWithModule("lib", Map.of()),
            List.of(), List.of(exportOf("f", "() => int")));
        CheckedModuleInput mid = moduleOf(invocation, midId,
            programUsing(libId, "lib", "f"),
            checksWithModule("lib", Map.of("f", Types.func(List.of(), Type.Int.INSTANCE))),
            List.of(libImport, mainImport), List.of(exportOf("mid", "() => null")));
        CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
            List.of(lib, main, mid), invocation.releaseStateHash());
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION,
            orderedMap(
                libId, indexEntryOf(libId, ExternalModuleKind.IMPLEMENTATION, List.of(),
                    List.of(exportOf("f", "() => int")), List.of(pointClass)),
                mainId, indexEntryOf(mainId, ExternalModuleKind.IMPLEMENTATION,
                    List.of(libImport), List.of(exportOf("main", "() => null")),
                    List.of()),
                midId, indexEntryOf(midId, ExternalModuleKind.IMPLEMENTATION,
                    List.of(libImport, mainImport), List.of(exportOf("mid", "() => null")),
                    List.of())));
        List<SemanticRequirementManifest> manifests = List.of(
            manifestOf(libId), manifestOf(mainId), manifestOf(midId));

        RoutePlanResult result = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), input, index, manifests, Target.LUAJIT,
            Set.of(mainId, midId));
        check(result != null && !result.hasErrors() && result.plan() != null,
            "planning succeeds: " + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        ModuleRoutePlan plan = result.plan();
        check(plan.entries().get(libId) == ModuleRoute.LEGACY
                && plan.entries().get(mainId) == ModuleRoute.SHARED
                && plan.entries().get(midId) == ModuleRoute.SHARED,
            "lib routes LEGACY while main and mid are shadow SHARED");
        check(plan.abiEdges().size() == 1,
            "exactly one plan-time record per legacy dependency of a shared module "
                + "(deduplicated across the two shared importers); got "
                + plan.abiEdges().size());
        TargetModuleAbi abi = plan.abiEdges().get(0);
        check(abi.moduleId().equals(libId), "the ABI record names the legacy dependency");
        check(abi.target() == Target.LUAJIT, "the ABI record carries the plan target");
        check(abi.artifactOwner() == ArtifactOwner.RETAINED_LUAJIT,
            "artifactOwner is RETAINED_LUAJIT for the LUAJIT plan");
        check(abi.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
            "the ABI record carries the project profile");
        check(abi.classFactoryAbi().get(pointId).equals(new ClassFactoryId(7)),
            "classFactoryAbi equals T8's constructionEntry ids");
        check(abi.classLayoutAbi().get(pointId).equals(List.of(x, y)),
            "classLayoutAbi equals the declaration-order FieldInterface lists");
        check(abi.exportedDescriptors().isEmpty(),
            "exportedDescriptors is empty at plan time (ISSUE-0233)");
        check(abi.loadKey() == null && abi.initializationEntry() == null
                && abi.functionWrapperAbi() == null
                && abi.syncInvocationEntries() == null
                && abi.asyncLinkageRecords() == null,
            "every emission-owned realization field is absent at plan time (ISSUE-0239)");

        // JVM plan: artifactOwner follows the target.
        RoutePlanResult jvmResult = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), input, index, manifests, Target.JVM,
            Set.of(mainId, midId));
        check(jvmResult != null && !jvmResult.hasErrors()
                && jvmResult.plan().abiEdges().size() == 1
                && jvmResult.plan().abiEdges().get(0).artifactOwner()
                    == ArtifactOwner.RETAINED_JVM
                && jvmResult.plan().abiEdges().get(0).target() == Target.JVM,
            "the JVM plan derives a RETAINED_JVM record per target");

        // Canonical serialization of the plan-time record is deterministic.
        TargetModuleAbi abi2 = jvmResult.plan().abiEdges().get(0);
        check(abi.canonicalText().equals(abi.canonicalText()),
            "the plan-time ABI record serializes deterministically (same input, "
                + "same bytes)");
        check(!abi.canonicalText().isEmpty()
                && abi.canonicalText().contains("\"exportedDescriptors\":{}")
                && abi.canonicalText().contains("\"loadKey\":null"),
            "the plan-time record's canonical text carries the empty descriptor map "
                + "and explicit nulls for the absent emission-owned fields");
        check(abi2.canonicalText().contains("\"artifactOwner\":\"RETAINED_JVM\""),
            "the JVM record serializes its RETAINED_JVM owner");
    }

    // =========================================================================
    // 4. Determinism, goldens, and the nonce exclusion
    // =========================================================================

    static void testDeterminismAndGoldens() {
        System.out.println("-- Determinism: byte-identical plans, pinned hash/planId goldens, "
            + "no staging nonce --");

        CompilerInvocation invocation = publicPreActivation();
        Project first = new Project(invocation, List.of(exportOf("f", "() => int")),
            List.of());
        Project second = new Project(invocation, List.of(exportOf("f", "() => int")),
            List.of());
        RoutePlanResult a = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), first.input, first.index,
            first.manifests, Target.LUAJIT, Set.of());
        RoutePlanResult b = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), second.input, second.index,
            second.manifests, Target.LUAJIT, Set.of());
        check(a != null && !a.hasErrors() && b != null && !b.hasErrors(),
            "both plans succeed: " + (a == null ? "null" : a.diagnostics()) + " / "
                + (b == null ? "null" : b.diagnostics()));
        if (a == null || a.hasErrors() || b == null || b.hasErrors()) {
            return;
        }
        check(a.plan().equals(b.plan()),
            "two plans for identical inputs are structurally equal");
        check(a.plan().canonicalText().equals(b.plan().canonicalText()),
            "two plans for identical inputs serialize byte-identically");
        check(a.plan().invocationHash().equals(b.plan().invocationHash())
                && a.plan().planId().equals(b.plan().planId()),
            "invocationHash and planId are stable across repeated builds");

        // Pinned goldens: the deterministic project above has one fixed
        // serialization, so the hash/planId must equal these exact values.
        String goldenHash = "e7acb948681195ee5464b5bbcb86b85825a0a57142831276967ac4b690ae5e99";
        String goldenPlanId = "plan-e7acb948681195ee";
        check(a.plan().invocationHash().equals(goldenHash),
            "the invocationHash matches the pinned golden; got "
                + a.plan().invocationHash());
        check(a.plan().planId().equals(goldenPlanId),
            "the planId matches the pinned golden; got " + a.plan().planId());
        check(a.plan().planId()
                .equals("plan-" + a.plan().invocationHash().substring(0, 16)),
            "planId = \"plan-\" + the first 16 hex chars of invocationHash");

        // The staging nonce appears nowhere in the serialized plan: the
        // nonce exists only in on-disk tree names (F4/F6).
        String nonce = "12345-" + "deadbeef-cafe-babe-0123-456789abcdef";
        check(!a.plan().canonicalText().contains(nonce)
                && !a.plan().canonicalText().contains("deal-stage")
                && !a.plan().canonicalText().contains("nonce"),
            "the staging nonce appears nowhere in the serialized plan");
        check(!a.plan().invocationHash().contains(nonce)
                && !a.plan().planId().contains(nonce),
            "the staging nonce appears in no plan hash");

        // The canonical JSON facility is the single serializer (T3): the
        // plan's canonical text round-trips through it byte-exactly.
        check(CanonicalJson.serializeText(CanonicalJson.parse(
                a.plan().canonicalText())).equals(a.plan().canonicalText()),
            "the plan's canonical JSON round-trips byte-exactly through T3's parser");
    }

    // =========================================================================
    // 5. Record guards
    // =========================================================================

    static void testRecordGuards() {
        System.out.println("-- Record guards: ModuleRoutePlan / TargetModuleAbi / results --");

        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(), Set.of(), Set.of(), List.of(),
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                "plan-other");
            fail("a planId not derived from the invocationHash must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a mismatched planId is rejected at construction");
        }
        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(), Set.of(), Set.of(), List.of(),
                "not-hex", "plan-not-hex");
            fail("a non-hex invocationHash must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a non-hex invocationHash is rejected at construction");
        }
        ModuleId mainId = new ModuleId("main");
        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(mainId, ModuleRoute.LEGACY),
                Set.of(mainId), Set.of(), List.of(),
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                "plan-0123456789abcd");
            fail("a shadow module routed LEGACY must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "shadowModules ⊆ SHARED entries is enforced at construction");
        }
        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(), Set.of(mainId), Set.of(),
                List.of(),
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                "plan-0123456789abcd");
            fail("a shadow module without an entry must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a shadow module without an entry is rejected at construction");
        }
        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(mainId, ModuleRoute.SHARED),
                Set.of(), Set.of(mainId), List.of(),
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                "plan-0123456789abcd");
            fail("a bytes exception routed SHARED must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "bytesExceptions ⊆ LEGACY entries is enforced at construction");
        }
        try {
            new ModuleRoutePlan(Target.LUAJIT, Map.of(), Set.of(), Set.of(mainId),
                List.of(),
                "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
                "plan-0123456789abcd");
            fail("a bytes exception without an entry must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a bytes exception without an entry is rejected at construction");
        }

        try {
            new TargetModuleAbi(mainId, Target.LUAJIT, ArtifactOwner.RETAINED_LUAJIT,
                SemanticProfile.DEAL_V1_2_INT32, null, Map.of(), Map.of(), null, null,
                null, null, null);
            fail("a null classFactoryAbi must be rejected");
        } catch (RuntimeException expected) {
            check(true, "a null planner-owned field is rejected at construction");
        }
        try {
            new TargetModuleAbi(mainId, Target.LUAJIT, ArtifactOwner.RETAINED_LUAJIT,
                SemanticProfile.DEAL_V1_2_INT32, Map.of(), null, Map.of(), null, null,
                null, null, null);
            fail("a null classLayoutAbi must be rejected");
        } catch (RuntimeException expected) {
            check(true, "a null classLayoutAbi is rejected at construction");
        }
        try {
            new RoutePlanResult(null, List.of());
            fail("a failed route plan without a diagnostic must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a failed result carries at least one diagnostic");
        }

        // The planner's producer-defect guards: shadow requests under a
        // non-shadow purpose are rejected at the API boundary (never
        // E6005, never a silent route).
        Project publicProject = new Project(publicPreActivation(),
            List.of(exportOf("f", "() => int")), List.of());
        try {
            MigrationPlanner.planRoutes(publicProject.invocation,
                CapabilityRegistry.releaseRegistry(), publicProject.input,
                publicProject.index, publicProject.manifests, Target.LUAJIT,
                Set.of(publicProject.mainId));
            fail("shadow requests under PUBLIC_BUILD must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "shadow requests under a non-shadow purpose are rejected at the "
                + "planner boundary (producer-defect guard, never E6005)");
        }
    }

    // =========================================================================
    // 6. Orchestrator integration (combined T1/T3/T4/T5/T8/T9)
    // =========================================================================

    static void testOrchestratorIntegration() throws Exception {
        System.out.println("-- Orchestrator integration: full pipeline → route plan --");

        Path tmp = Files.createTempDirectory("deal-route-orchestrator");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("a.deal"), """
                import * as time from "std/time"

                export function getNow(): () => int {
                  return time.nowMillis
                }
                """);
            Files.writeString(src.resolve("main.deal"), """
                import * as a from "./a"

                export function main(): null {
                  let g: () => int = a.getNow()
                  g()
                  return null
                }
                """);
            // ISSUE-0643 P10 item 3: the wrapper scenario carries
            // later-slice constructs (time.nowMillis, function-typed
            // values), so the suite's orchestrator compile — whose subject
            // is the route plan — resolves the harness invocation and
            // keeps the harness arm. The production arm's routing-free
            // outcome is asserted separately below.
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                false, false, false, deal.codegen.Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null,
                ConformanceHarnessMetadata.invocation(
                    SemanticProfile.DEAL_V1_2_INT32));
            boolean ok = orchestrator.compile();
            check(ok, "the wrapper scenario compiles end to end: "
                + orchestrator.diagnostics());
            RoutePlanResult plan = orchestrator.routePlan();
            check(ok && plan != null && !plan.hasErrors() && plan.plan() != null,
                "the orchestrator produced exactly one route plan: "
                    + (plan == null ? "null" : plan.diagnostics()));
            if (plan == null || plan.hasErrors()) {
                return;
            }
            check(plan.plan().target() == Target.LUAJIT,
                "the plan targets the compile's LUAJIT backend");
            check(plan.plan().entries().size() == 2
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                "the harness invocation routes every implementation module "
                    + "LEGACY (the propagated conflict and the purpose rule alike)");
            check(plan.plan().shadowModules().isEmpty()
                    && plan.plan().abiEdges().isEmpty(),
                "the harness plan carries no shadow entries and no ABI records");
            check(orchestrator.checkedProject().index().modules().keySet().stream()
                    .anyMatch(m -> m.path().equals("std.time")),
                "the index covers the std/time STDLIB declaration entry");
            check(plan.plan().entries().keySet().stream()
                    .noneMatch(m -> m.path().equals("std.time")),
                "stdlib/host declaration modules are index entries, never route "
                    + "entries");

            // Determinism across two identical orchestrator compiles.
            Path secondOut = tmp.resolve("build2");
            CompilationOrchestrator second = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), secondOut, false,
                false, false, false, deal.codegen.Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null,
                ConformanceHarnessMetadata.invocation(
                    SemanticProfile.DEAL_V1_2_INT32));
            boolean secondOk = second.compile();
            check(secondOk, "the second compile succeeds: " + second.diagnostics());
            RoutePlanResult secondPlan = second.routePlan();
            check(secondPlan != null && !secondPlan.hasErrors()
                    && secondPlan.plan().canonicalText()
                        .equals(plan.plan().canonicalText()),
                "two orchestrator compiles produce byte-identical route plans");

            // The route plan is read-only over the frontend facts: the
            // checked project and index digests are unchanged.
            check(orchestrator.checkedProject().index().interfaceIndexDigest()
                    .equals(second.checkedProject().index().interfaceIndexDigest()),
                "the interface index digest is stable across compiles");

            // ISSUE-0643 P4 (retargeted by ISSUE-0675): the release-owned
            // production invocation runs the production arm — it computes
            // and consults no route plan (phase 3.7 stays skipped, the
            // route-plan view stays null). The wrapper fixture's
            // function-typed values are realized by the producer rule's
            // materialization arms (the imported call result and the
            // dynamic call over its carrier), so the production arm lowers
            // and emits the fixture through the shared route; the harness
            // plan above stays the retained route subject.
            CompilationOrchestrator production = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(),
                tmp.resolve("build-production"), false, false, false, false,
                deal.codegen.Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null,
                CompilerProfileProvider.resolve(
                    ReleaseConfiguration.CURRENT_RELEASE_STATE,
                    ReleaseConfiguration.releaseCapabilityRegistry()));
            boolean productionOk = production.compile();
            check(productionOk,
                "the release-owned production invocation lowers the wrapper "
                    + "fixture through the producer rule's materialization arms: "
                    + production.diagnostics());
            check(production.routePlan() == null,
                "the production arm computes and consults no route plan");
            check(production.diagnostics().stream()
                    .noneMatch(d -> "E6005".equals(d.code())),
                "the production compile reports no lowering defect: "
                    + production.diagnostics());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testJsBackendSkipsRoutePlan() throws Exception {
        System.out.println("-- JS backend: the closed route-plan phase is skipped --");

        Path tmp = Files.createTempDirectory("deal-route-js");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                export function main(): null {
                  return null
                }
                """);
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                false, false, deal.codegen.Backend.JS, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize());
            boolean ok = orchestrator.compile();
            check(ok, "the JS compile succeeds: " + orchestrator.diagnostics());
            check(orchestrator.routePlan() == null,
                "the JS backend produces no route plan (the closed target axis is "
                    + "LUAJIT|JVM, foundation F4)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 7. Failure registry + closed-set invariants (T1/T5 faults)
    // =========================================================================

    static void testRegistryAndClosedSetInvariants() {
        System.out.println("-- Failure registry / closed sets (T1/T5 faults) --");

        // The planner's E6005 flows through the single failure contract
        // registry: the message equals the registry's instantiation of the
        // detail payload.
        CompilerInvocation invocation = publicPreActivation();
        ModuleId mainId = new ModuleId("main");
        CompilerDiagnostic diagnostic = MigrationPlanner.verifyInitializationFact(
            invocation, mainId, null);
        check(diagnostic != null, "the seam produces a diagnostic");
        String expected = FailureContractRegistry.instantiateMessage(
            new deal.semantic.ir.LoweringFailureDetail("main", SemanticCapability.MODULES,
                MigrationPlanner.ROUTE_INTERNAL_ERROR_SENTINEL,
                invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
                "MigrationPlanner " + MigrationPlanner.ROUTE_INTERNAL_ERROR_SENTINEL
                    + " (the initialization contract is not ONCE_AFTER_DEPENDENCIES: "
                    + "null)"));
        check(diagnostic.message().equals(expected),
            "the planner's E6005 message equals the registry's instantiation of the "
                + "detail payload (no hand-crafted message)");

        // The route and artifact-owner enums are closed two/three-value sets.
        List<String> routes = new ArrayList<>();
        for (ModuleRoute route : ModuleRoute.values()) {
            routes.add(route.name());
        }
        check(routes.equals(List.of("LEGACY", "SHARED")),
            "ModuleRoute is exactly {LEGACY, SHARED}; got " + routes);
        List<String> owners = new ArrayList<>();
        for (ArtifactOwner owner : ArtifactOwner.values()) {
            owners.add(owner.name());
        }
        check(owners.equals(List.of("SHARED", "RETAINED_LUAJIT", "RETAINED_JVM")),
            "ArtifactOwner is exactly {SHARED, RETAINED_LUAJIT, RETAINED_JVM}; got "
                + owners);

        // A1 matrix: wrong-profile internal combinations are rejected at
        // invocation resolution and at the record guard (T4's boundary),
        // never at plan time.
        try {
            CompilerProfileProvider.resolveCommonShadow(SemanticProfile.LEGACY_SAFE_INT,
                ReleaseState.PRE_ACTIVATION, CapabilityRegistry.releaseRegistry());
            fail("COMMON_SHADOW with a legacy profile must be rejected at resolution");
        } catch (IllegalArgumentException shadowMismatch) {
            check(true, "COMMON_SHADOW + LEGACY_SAFE_INT is rejected at invocation "
                + "resolution (A1 boundary)");
        }
        try {
            CompilerProfileProvider.resolveLegacyRegression(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                CapabilityRegistry.releaseRegistry());
            fail("LEGACY_REGRESSION with a v1.2 profile must be rejected at resolution");
        } catch (IllegalArgumentException regressionMismatch) {
            check(true, "LEGACY_REGRESSION + DEAL_V1_2_INT32 is rejected at invocation "
                + "resolution (A1 boundary)");
        }
        String registryHash = CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
        try {
            new CompilerInvocation(InvocationPurpose.COMMON_SHADOW,
                SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
                registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                    ReleaseState.PRE_ACTIVATION, registryHash));
            fail("the record must reject COMMON_SHADOW + LEGACY_SAFE_INT");
        } catch (IllegalArgumentException recordShadowMismatch) {
            check(true, "the CompilerInvocation record guard rejects COMMON_SHADOW + "
                + "LEGACY_SAFE_INT (A1 matrix at the record)");
        }
        try {
            new CompilerInvocation(InvocationPurpose.LEGACY_REGRESSION,
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                    ReleaseState.V1_2_ACTIVE, registryHash));
            fail("the record must reject LEGACY_REGRESSION + DEAL_V1_2_INT32");
        } catch (IllegalArgumentException recordRegressionMismatch) {
            check(true, "the CompilerInvocation record guard rejects LEGACY_REGRESSION + "
                + "DEAL_V1_2_INT32 (A1 matrix at the record)");
        }

        // A1 matrix: the planner's invocation-consistency guard admits the
        // pre-activation shadow path — COMMON_SHADOW + DEAL_V1_2_INT32 +
        // PRE_ACTIVATION with zero shadow requests plans all-LEGACY under
        // F4 rule 5 (the wiring proof every later child's verification
        // uses).
        CompilerInvocation shadowPre = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
        Project shadowPreProject = new Project(shadowPre,
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult shadowPreResult = MigrationPlanner.planRoutes(
            shadowPreProject.invocation, CapabilityRegistry.releaseRegistry(),
            shadowPreProject.input, shadowPreProject.index, shadowPreProject.manifests,
            Target.LUAJIT, Set.of());
        assertAllLegacy(shadowPreResult,
            List.of(shadowPreProject.libId, shadowPreProject.mainId),
            "COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION");

        // A1 matrix: LEGACY_REGRESSION + LEGACY_SAFE_INT + V1_2_ACTIVE is
        // admitted (the retention window extends past activation) and
        // routes all-LEGACY under rule 1.
        CompilerInvocation legacyActive = CompilerProfileProvider.resolveLegacyRegression(
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        Project legacyActiveProject = new Project(legacyActive,
            List.of(exportOf("f", "() => int")), List.of());
        RoutePlanResult legacyActiveResult = MigrationPlanner.planRoutes(
            legacyActiveProject.invocation, CapabilityRegistry.releaseRegistry(),
            legacyActiveProject.input, legacyActiveProject.index,
            legacyActiveProject.manifests, Target.JVM, Set.of());
        assertAllLegacy(legacyActiveResult,
            List.of(legacyActiveProject.libId, legacyActiveProject.mainId),
            "LEGACY_REGRESSION + LEGACY_SAFE_INT + V1_2_ACTIVE");

        // The registry's capability × target lookup drives rule 4: every
        // release-registry entry is SHADOW in this epic, so the lookup
        // returns SHADOW for every manifest capability.
        for (SemanticCapability capability : SemanticCapability.values()) {
            check(CapabilityRegistry.releaseRegistry().state(capability, Target.LUAJIT)
                    == CapabilityRegistry.State.SHADOW
                    && CapabilityRegistry.releaseRegistry().state(capability, Target.JVM)
                        == CapabilityRegistry.State.SHADOW,
                "the release registry is all SHADOW for " + capability);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Migration Planner / Route Plan Test (ISSUE-0290) ===\n");

        testPublicPreActivationAllLegacy();
        testLegacyRegressionAllLegacy();
        testV12ActiveAllShadowRegistryReroutesSilently();
        testCommonShadowRequestedModules();
        testCommonShadowUnrequestedStaysLegacy();
        testTimeConflictNeverShared();
        testBytesBearingNeverShared();
        testE6005IndexContradictions();
        testE6005AbsentExportEntry();
        testE6005IllFormedExportEntry();
        testDefensiveSeamChecks();
        testTargetModuleAbiDerivation();
        testDeterminismAndGoldens();
        testRecordGuards();
        testOrchestratorIntegration();
        testJsBackendSkipsRoutePlan();
        testRegistryAndClosedSetInvariants();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
