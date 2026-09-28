package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.ClassRegistrationSeeds;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.NamespaceRegistrations;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.lang.reflect.RecordComponent;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0637: the project-gate fault battery and the unchanged-surface
 * audit of the one-lowering slice
 * ({@code project-lowering-entry-and-registration-seeds} Sequencing item 6
 * and Verifications 7-8, D11 and D12;
 * {@code semantic-ir-construct-coverage-cutover} K9's frozen extension
 * set; {@code luajit-jvm-single-lowering-production-cutover} C5/C6).
 *
 * <p><b>The fault battery.</b> Every fault of the newly composed gate
 * clause set is driven through the real production surfaces and returns
 * the first E6005 with its rule, module, capability, and origin, and
 * produces no project, no tables, no registries, no seeds, and no
 * registrations:</p>
 *
 * <ol>
 *   <li>input-representable faults run through the real
 *       {@link SemanticLowerer#lowerProject} entry over a real
 *       multi-module checked project (the production frontend): the
 *       extern-C plan/class mismatch ({@code FFI_PLAN_MISMATCH}), a
 *       declaration class without a resolvable {@code ClassId}
 *       ({@code DECLARATION_CLASS_IDENTITY_UNRESOLVED}), and the
 *       inconsistent-fact imported-class deferral
 *       ({@code RETAINED_ABI_DEFERRED});</li>
 *   <li>producer-side faults that a correct producer cannot express are
 *       forged in the units the real entry produced (which carry the
 *       registration seeds, the intrinsic bindings, the alias cells, the
 *       in-project factory facts, and the identity takeover) and driven
 *       through the same composed per-unit chain the entry runs
 *       ({@link SemanticLowerer#validateProjectUnit}): the intrinsic
 *       admission clauses (a registered key with no seed
 *       {@code BINDING_INIT}, a key with two, a producer-less init
 *       operand without a registration, a mismatched
 *       ({@code kind, descriptor}) pair), the alias/namespace agreement
 *       (a cell named by two completions, a completion naming a non-alias
 *       allocation, and a completion/entry kind disagreement through the
 *       real {@link NamespaceRegistrations.Recorder}), and the two
 *       body-local producer defects ({@code R-BOUNDARY-TRIPLE});</li>
 *   <li>the four named epic negative seeds (a corrupted unit, a missing
 *       module, a non-v1.2 invocation, an alias without a resolved import
 *       fact) are exercised by the project lowering entry child
 *       ({@code ProjectLoweringTest}) and are not duplicated here; this
 *       battery asserts that child's main stays registered.</li>
 * </ol>
 *
 * <p><b>The unchanged-surface audit.</b> The audit reads the real loaded
 * closed sets (the {@link SemanticOpKind} membership, the
 * {@link DefaultOwner} members, the permitted
 * {@link FunctionExecutionBinding} shapes, every payload record's shape
 * through reflection), the version constant, the dumper's closed key sets
 * (the unit text protocol and the project manifest), and the real
 * production source surface (exactly one {@code deal/**} call site invokes
 * {@code lowerProject}, in the production project emission unit, plus the
 * single declaration in {@code SemanticLowerer.java}; the production unit
 * reads no routing, planner, registry, retained-backend, or counting
 * surface; the emission entries, the harness route planning and
 * dispatch, the retained loops and counters, the mixed-edge validation,
 * the source-map handling, the stager, and the CLI keep their
 * manifest-registered tests). No JavaScript source references the
 * slice's new surfaces, the retained backends keep their entry points and
 * tests, every superseded pin's test still exists, and every focused test
 * main of the slice is registered in {@code tools/gate-manifest.sh}.</p>
 */
public class ProjectGateFaultBatteryTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    private static final ModuleId UTIL = new ModuleId("util");
    private static final ModuleId APP = new ModuleId("app");
    private static final ModuleId HOST_CFG = new ModuleId("host.cfg");
    private static final String HOST_CFG_SPECIFIER = "host/cfg";

    private static final String HOST_DECLARATION = """
        export class Endpoint {
          path: string;
          port?: int;
        }

        export function version(): int;
        """;

    /**
     * The project-gate fixture's library module: an exported class (the
     * in-project imported-class fact and the class-registration seed
     * context), a non-exported declaration with zero call sites (the
     * identity takeover's body-local cell), and an exported factory
     * function.
     */
    private static final String BATTERY_UTIL_SOURCE = """
        export class Point {
          x: int = 0;
          y: int = 1;
        }

        function helper(): int {
          return 7;
        }

        export function makePoint(x: int): Point {
          let ref: () => int = helper;
          return {x: x};
        }
        """;

    /**
     * The project-gate fixture's entry module: two resolved imports (the
     * COMPILED and HOST namespace registrations with their alias cells),
     * the in-project imported-class construction through the owner's
     * factory facts, and a cross-module call through the accumulated
     * {@code EXTERNAL_ENTRY}.
     */
    private static final String BATTERY_APP_SOURCE = """
        import * as u from "util"
        import * as cfg from "host/cfg"

        export function main(): null {
          let p: u.Point = {x: 5};
          let q: u.Point = u.makePoint(7);
          return null;
        }
        """;

    /** The extern-C declaration module (the {@code FFI_PLAN} plan source). */
    private static final String EXTERN_C_DECLARATION = """
        // @extern-c

        // @c-struct
        export class Vec2 {
          x: number = 0.0;
          y: number = 0.0;
        }

        export function ffi_pair_sum(value: Vec2): number;
        """;

    private static final ModuleId NATIVE = new ModuleId("native.math");
    private static final String NATIVE_SPECIFIER = "native/math";
    private static final ClassId NATIVE_VEC2 =
        new ClassId("$external/native/math", "Vec2");

    private static final String EXTERN_C_APP_SOURCE = """
        import * as native from "native/math"

        export function main(): null {
          let v: native.Vec2 = {x: 1.0, y: 2.0};
          return null;
        }
        """;

    // =========================================================================
    // The real-project harness (the production frontend + the project entry)
    // =========================================================================

    private record RealProject(
        Path root,
        CompilationOrchestrator orchestrator,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    private static RealProject compileProject(String appSource) throws Exception {
        return compileProject(appSource, Map.of(), Map.of());
    }

    private static RealProject compileProject(String appSource,
            Map<String, String> extraSources,
            Map<String, String> extraExternals) throws Exception {
        Path proj = Files.createTempDirectory("project-gate-battery");
        writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
        writeFileIn(proj, "src/util.deal", BATTERY_UTIL_SOURCE);
        writeFileIn(proj, "src/app.deal", appSource);
        for (Map.Entry<String, String> extra : extraSources.entrySet()) {
            writeFileIn(proj, extra.getKey(), extra.getValue());
        }
        Path entry = proj.resolve("src/app.deal").toAbsolutePath();
        Path output = proj.resolve("out").toAbsolutePath();
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(HOST_CFG_SPECIFIER,
            proj.resolve("src/cfg.d.deal").toAbsolutePath().toString());
        for (Map.Entry<String, String> extra : extraExternals.entrySet()) {
            externals.put(extra.getKey(),
                proj.resolve(extra.getValue()).toAbsolutePath().toString());
        }
        // P10 item 3: the battery's subject is the project lowering
        // entry and its fixtures carry host, extern-C, and cross-module
        // constructs, so the orchestrator compile runs through a harness
        // invocation (COMMON_SHADOW) and keeps the harness arm — never
        // the release-owned production invocation.
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, externals,
            List.of(proj.resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(), null, invocation());
        boolean compiled = orchestrator.compile();
        check(compiled, "the fixture project compiles through the production "
            + "pipeline: " + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            "the production checked-project builder produced the closure and the "
                + "index: " + (built == null ? "null" : built.diagnostics()));
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(proj);
            throw new IllegalStateException("the fixture project did not build");
        }
        Map<ModuleId, FfiGeneratedModule> externC = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externC.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            String specifier = null;
            for (String candidate : externals.keySet()) {
                if (candidate.replace('/', '.').equals(declarationModule.path())) {
                    specifier = candidate;
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new RealProject(proj, orchestrator, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(), externC,
            identities);
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** One {@link SemanticLowerer#lowerProject} call over the real project. */
    private static SemanticLowerer.ProjectLoweringResult lower(RealProject project) {
        return lower(project, project.externCModules(),
            project.declarationIdentities());
    }

    private static SemanticLowerer.ProjectLoweringResult lower(RealProject project,
            Map<ModuleId, FfiGeneratedModule> externCModules,
            Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
        return SemanticLowerer.lowerProject(invocation(), project.checkedProject(),
            project.index(), project.manifests(), project.surface(),
            declarationIdentities, externCModules,
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    // =========================================================================
    // Part 1: the input-representable faults through lowerProject
    // =========================================================================

    private static void testExternCPlanMismatchThroughEntry() throws Exception {
        System.out.println("-- fault: an extern-C plan/class mismatch reaches the "
            + "project entry's seed production --");
        RealProject project = compileProject(EXTERN_C_APP_SOURCE,
            Map.of("src/native.d.deal", EXTERN_C_DECLARATION),
            Map.of(NATIVE_SPECIFIER, "src/native.d.deal"));
        try {
            FfiGeneratedModule real = project.externCModules().get(NATIVE);
            check(real != null, "the extern-C declaration module carries the real "
                + "phase-3.9 generated metadata");
            if (real == null) {
                return;
            }
            FfiCompilerClassDefaultPlan plan = real.plans().get(NATIVE_VEC2.text());
            check(plan != null && plan.entries().size() == 2,
                "the generated metadata carries the Vec2 plan with its two "
                    + "declared C-struct fields");
            if (plan == null) {
                return;
            }
            // The fault: the declared class loses its plan entry.
            Map<String, FfiCompilerClassDefaultPlan> stripped =
                new LinkedHashMap<>(real.plans());
            stripped.remove(NATIVE_VEC2.text());
            Map<ModuleId, FfiGeneratedModule> mismatched = new LinkedHashMap<>();
            mismatched.put(NATIVE, new FfiGeneratedModule(real.modulePath(),
                real.descriptor(), real.cdefBundle(), stripped, real.bindings()));
            assertEntryFault(lower(project, mismatched, project.declarationIdentities()),
                ClassRegistrationSeeds.FFI_PLAN_MISMATCH, NATIVE,
                SemanticCapability.CLASSES,
                "ClassRegistrationSeeds " + ClassRegistrationSeeds.FFI_PLAN_MISMATCH);
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testDeclarationClassIdentityUnresolvedThroughEntry()
            throws Exception {
        System.out.println("-- fault: a declaration class without a resolvable "
            + "ClassId reaches the project entry's seed production --");
        RealProject project = compileProject(BATTERY_APP_SOURCE);
        try {
            check(project.surface().moduleIds().contains(HOST_CFG)
                    && project.surface().require(HOST_CFG).classes()
                        .containsKey("Endpoint"),
                "the declaration surface covers the imported host declaration "
                    + "class whose identity the fault removes");
            // The fault: the declaring module carries no public canonical
            // module identity.
            Map<ModuleId, CanonicalModuleIdentity> identities =
                new LinkedHashMap<>(project.declarationIdentities());
            identities.remove(HOST_CFG);
            assertEntryFault(lower(project, project.externCModules(), identities),
                ClassRegistrationSeeds.DECLARATION_CLASS_IDENTITY_UNRESOLVED,
                HOST_CFG, SemanticCapability.CLASSES,
                "ClassRegistrationSeeds "
                    + ClassRegistrationSeeds.DECLARATION_CLASS_IDENTITY_UNRESOLVED);
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testInconsistentFactDeferralThroughEntry() throws Exception {
        System.out.println("-- fault: the inconsistent-fact imported-class "
            + "deferral (an owner outside the closure and the declaration set) --");
        RealProject project = compileProject(BATTERY_APP_SOURCE);
        try {
            // The same real project with the owner module removed from the
            // closure and the index: the checker-resolved class identity
            // stays, but no lowered implementation module, no declaration
            // surface entry, and no registration seed covers it.
            List<CheckedModuleInput> modules = new ArrayList<>();
            for (CheckedModuleInput module : project.checkedProject().modules()) {
                if (!module.moduleId().equals(UTIL)) {
                    modules.add(module);
                }
            }
            Map<ModuleId, ExternalModuleInterface> indexModules = new LinkedHashMap<>();
            for (Map.Entry<ModuleId, ExternalModuleInterface> entry
                    : project.index().modules().entrySet()) {
                if (!entry.getKey().equals(UTIL)) {
                    indexModules.put(entry.getKey(), entry.getValue());
                }
            }
            ProjectInterfaceIndex strippedIndex = new ProjectInterfaceIndex(
                ProjectInterfaceIndex.FORMAT_VERSION, indexModules);
            List<SemanticRequirementManifest> manifests = new ArrayList<>();
            for (SemanticRequirementManifest manifest : project.manifests()) {
                if (!manifest.moduleId().equals(UTIL)) {
                    manifests.add(manifest);
                }
            }
            CompilerInvocation invocation = invocation();
            CheckedProjectInput stripped = new CheckedProjectInput(invocation,
                project.checkedProject().entryModule(), modules,
                invocation.releaseStateHash());
            SemanticLowerer.ProjectLoweringResult result =
                SemanticLowerer.lowerProject(invocation, stripped, strippedIndex,
                    manifests, project.surface(), project.declarationIdentities(),
                    project.externCModules(),
                    BuiltinErrorDeclaration.synthesized(
                        modules.get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT,
                        IntrinsicKind.NUMBER_CONVERT),
                    Set.of());
            assertEntryFault(result, "RETAINED_ABI_DEFERRED", APP,
                SemanticCapability.CLASSES,
                "SemanticLowerer RETAINED_ABI_DEFERRED");
        } finally {
            deleteRecursively(project.root());
        }
    }

    /**
     * Asserts the entry-level fault surface: exactly one E6005 carrying the
     * rule, the module, the capability, and the origin, and no project, no
     * tables, no registries, no seeds, and no registrations.
     */
    private static void assertEntryFault(
            SemanticLowerer.ProjectLoweringResult result, String rule,
            ModuleId module, SemanticCapability capability, String originFragment) {
        check(result.project() == null, "the fault produces no project: "
            + result.diagnostics());
        check(result.tables().isEmpty(),
            "the fault produces no block-membership tables");
        check(result.registries().isEmpty(),
            "the fault produces no class-factory registries");
        check(result.seeds() == null,
            "the fault produces no class registration seeds");
        check(result.namespaces() == null,
            "the fault produces no namespace registrations");
        check(result.diagnostics().size() == 1,
            "the fault returns exactly the first E6005; got "
                + result.diagnostics().size() + " diagnostic(s)");
        if (result.diagnostics().isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = result.diagnostics().get(0);
        check("E6005".equals(diagnostic.code()),
            "the fault returns E6005; got " + diagnostic.code());
        check(diagnostic.message().contains("validatorRule " + rule),
            "the fault names the rule " + rule + "; got " + diagnostic.message());
        check(diagnostic.message().contains("module '" + module.path() + "'"),
            "the fault names the module " + module.path() + "; got "
                + diagnostic.message());
        check(diagnostic.message().contains("capability " + capability),
            "the fault names the capability " + capability + "; got "
                + diagnostic.message());
        check(diagnostic.message().contains("origin " + originFragment),
            "the fault names the origin " + originFragment + "; got "
                + diagnostic.message());
    }

    // =========================================================================
    // Part 2: the composed-gate faults over units the real entry produced
    // =========================================================================

    /**
     * The battery's base lowering: one real project whose units carry the
     * registration seeds, the intrinsic bindings, the alias cells, the
     * in-project factory facts, and the identity takeover.
     */
    private static SemanticLowerer.ProjectLoweringResult baseProject() throws Exception {
        RealProject project = compileProject(BATTERY_APP_SOURCE);
        SemanticLowerer.ProjectLoweringResult result = lower(project);
        if (result.project() == null) {
            fail("the battery's base project lowers through the entry: "
                + result.diagnostics());
            deleteRecursively(project.root());
            return null;
        }
        // The combined-behavior carriers the battery forges against: the
        // produced units carry the registration seeds (the two
        // IntrinsicFunction bindings), the alias cells on the MODULE_IMPORT
        // payloads, the in-project factory facts (CLASS_NEW with
        // SHARED_FACTORY), and the identity takeover (the zero-call-site
        // body's creation-op identity).
        LoweredModuleUnit utilUnit = unitOf(result, UTIL);
        LoweredModuleUnit appUnit = unitOf(result, APP);
        check(utilUnit != null && appUnit != null,
            "the base project carries both units");
        if (utilUnit != null && appUnit != null) {
            int intrinsicRegistrations = 0;
            for (FunctionExecutionBinding binding : utilUnit.functionBindings().values()) {
                if (binding instanceof FunctionExecutionBinding.IntrinsicFunction) {
                    intrinsicRegistrations++;
                }
            }
            checkEq(2, intrinsicRegistrations,
                "the produced unit carries the two intrinsic registrations");
            boolean aliasCells = false;
            for (SemanticOp op : appUnit.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT
                        && op.payload() instanceof KindPayload.ModuleImportPayload payload
                        && !payload.aliasCells().isEmpty()) {
                    aliasCells = true;
                }
            }
            check(aliasCells,
                "the produced completion payloads carry the alias cells");
            boolean sharedFactoryConstruction = false;
            for (SemanticOp op : appUnit.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW
                        && op.payload() instanceof KindPayload.ClassNewPayload payload
                        && payload.defaultOwner() == DefaultOwner.SHARED_FACTORY
                        && payload.classFactoryRef() != null) {
                    sharedFactoryConstruction = true;
                }
            }
            check(sharedFactoryConstruction,
                "the produced app unit carries the in-project constructor's "
                    + "SHARED_FACTORY reference");
            boolean identityTakeover = false;
            for (SemanticOp op : utilUnit.ops()) {
                if (op.kind() == SemanticOpKind.RETURN
                        && op.payload() instanceof KindPayload.ReturnPayload returned
                        && isCreationOp(utilUnit, returned.enclosingInvocationOpId())) {
                    identityTakeover = true;
                }
            }
            check(identityTakeover,
                "the produced util unit carries the body-local identity takeover");
        }
        return result;
    }

    private static void testIntrinsicAdmissionFaults() throws Exception {
        System.out.println("-- faults: the intrinsic admission clauses inside an "
            + "E7-armed unit --");
        SemanticLowerer.ProjectLoweringResult result = baseProject();
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = unitOf(result, UTIL);
        check(unit != null, "the battery carries the util unit");
        if (unit == null) {
            return;
        }
        Map<Long, IntrinsicKey> keys = intrinsicKeys(unit);
        checkEq(2, keys.size(),
            "the E7-armed unit carries the two producer-less intrinsic keys");
        IntrinsicKey intKey = keyFor(keys, IntrinsicKind.INT_CONVERT);
        IntrinsicKey numberKey = keyFor(keys, IntrinsicKind.NUMBER_CONVERT);
        check(intKey != null && numberKey != null,
            "both conversion intrinsics are registered");
        if (intKey == null || numberKey == null) {
            return;
        }
        long producerLessValue = 900_000_001L;

        // (a) a registered key with no seed BINDING_INIT: the int seed's
        // init operand is rewired to a producer-less value, so the int key
        // keeps its registration and loses its producing position.
        LoweredModuleUnit noSeedInit = withInitOperand(unit, intKey.initOp,
            new ValueId(producerLessValue));
        assertGateFault(noSeedInit, result.tableOf(UTIL), result, UTIL,
            BindingsProductionValidator.REGISTRY_ONE_TO_ONE,
            SemanticCapability.BINDINGS, "0 seed BINDING_INIT",
            "BindingsProductionValidator REGISTRY_ONE_TO_ONE");

        // (b) a key with two seed BINDING_INITs: the other intrinsic's seed
        // init is rewired onto the int key and the other registration is
        // removed, so exactly that key carries the doubled position.
        LoweredModuleUnit doubled = withInitOperand(unit, numberKey.initOp,
            intKey.value);
        doubled = withFunctionBindings(doubled, withoutRegistration(doubled,
            new FunctionAllocationIdentity(numberKey.value.id())));
        assertGateFault(doubled, result.tableOf(UTIL), result, UTIL,
            BindingsProductionValidator.REGISTRY_ONE_TO_ONE,
            SemanticCapability.BINDINGS, "2 seed BINDING_INIT",
            "BindingsProductionValidator REGISTRY_ONE_TO_ONE");

        // (c) a producer-less init operand without a registration: the
        // number seed's init operand becomes a fresh producer-less value and
        // the number registration is removed, so the converse clause is the
        // first failing key.
        LoweredModuleUnit unregistered = withInitOperand(unit, numberKey.initOp,
            new ValueId(producerLessValue + 1));
        unregistered = withFunctionBindings(unregistered, withoutRegistration(
            unregistered, new FunctionAllocationIdentity(numberKey.value.id())));
        assertGateFault(unregistered, result.tableOf(UTIL), result, UTIL,
            BindingsProductionValidator.REGISTRY_ONE_TO_ONE,
            SemanticCapability.BINDINGS, "keyed by no registration",
            "BindingsProductionValidator REGISTRY_ONE_TO_ONE");

        // (d) a mismatched (kind, descriptor) pair: the int registration
        // carries the number conversion's declared signature.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.put(new FunctionAllocationIdentity(intKey.value.id()),
            new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                IntrinsicKind.NUMBER_CONVERT.declaredSignature()));
        LoweredModuleUnit mismatched = withFunctionBindings(unit, bindings);
        assertGateFault(mismatched, result.tableOf(UTIL), result, UTIL,
            BindingsProductionValidator.REGISTRY_ONE_TO_ONE,
            SemanticCapability.BINDINGS, "pinned declared signature",
            "BindingsProductionValidator REGISTRY_ONE_TO_ONE");

        // Positive control: the unmodified unit passes the same composed
        // chain with the real in-project facts.
        Optional<CompilerDiagnostic> intact = SemanticLowerer.validateProjectUnit(
            unit, result.tableOf(UTIL), comparisonFacts(result),
            BindingsProductionValidator.PinnedWriteFacts.empty(),
            result.registryOf(UTIL), new JsonDefaultChildTable(Map.of()),
            result.project().interfaceIndex().modules().get(UTIL),
            inProjectFacts(result));
        check(intact.isEmpty(),
            "the unmodified unit carrying the seeds passes the composed chain: "
                + intact.orElse(null));
    }

    /** One registered producer-less intrinsic key of the unit. */
    private record IntrinsicKey(IntrinsicKind kind, ValueId value, OpId initOp) {
    }

    private static IntrinsicKey keyFor(Map<Long, IntrinsicKey> keys,
            IntrinsicKind kind) {
        for (IntrinsicKey key : keys.values()) {
            if (key.kind == kind) {
                return key;
            }
        }
        return null;
    }

    /**
     * The unit's registered intrinsic keys: for every
     * {@code IntrinsicFunction} registration, the seeded value identity and
     * the single {@code BINDING_INIT} whose init operand is that identity.
     */
    private static Map<Long, IntrinsicKey> intrinsicKeys(LoweredModuleUnit unit) {
        Map<Long, IntrinsicKey> keys = new LinkedHashMap<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (!(entry.getValue()
                    instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic)) {
                continue;
            }
            ValueId value = new ValueId(entry.getKey().id());
            OpId initOp = null;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BINDING_INIT
                        && op.payload() instanceof KindPayload.BindingInitPayload init
                        && init.value().equals(value)) {
                    initOp = op.opId();
                    break;
                }
            }
            keys.put(entry.getKey().id(),
                new IntrinsicKey(intrinsic.kind(), value, initOp));
        }
        return keys;
    }

    private static void testAliasNamespaceFaults() throws Exception {
        System.out.println("-- faults: the alias/namespace agreement (cells, "
            + "completions, and the registration entry kind) --");
        SemanticLowerer.ProjectLoweringResult result = baseProject();
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = unitOf(result, APP);
        check(unit != null, "the battery carries the app unit");
        if (unit == null) {
            return;
        }
        SemanticOp completion = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT
                    && op.payload() instanceof KindPayload.ModuleImportPayload payload
                    && payload.resolvedModule().equals(UTIL)) {
                completion = op;
            }
        }
        check(completion != null, "the app unit carries the util import completion");
        if (completion == null) {
            return;
        }
        KindPayload.ModuleImportPayload payload =
            (KindPayload.ModuleImportPayload) completion.payload();
        checkEq(1, payload.aliasCells().size(),
            "the util import completion names exactly one alias cell");

        // (a) a cell named by two completions: the same completion op is
        // duplicated (a second MODULE_IMPORT naming the same cell).
        OpId duplicateId = new OpId(APP, 900_000_002L);
        LoweredModuleUnit doublyNamed = withDuplicateImport(unit, completion,
            duplicateId);
        check(doublyNamed != null, "the doubly-naming unit is built");
        if (doublyNamed != null) {
            StructuredBodyTable table = tableWithDuplicate(
                result.tableOf(APP), completion.opId(), duplicateId);
            check(table != null, "the duplicate completion is tabled");
            if (table != null) {
                assertGateFault(doublyNamed, table, result, APP,
                    BindingsProductionValidator.BINDING_INIT_ONCE,
                    SemanticCapability.BINDINGS,
                    "named by two MODULE_IMPORT completions",
                    "BindingsProductionValidator BINDING_INIT_ONCE");
            }
        }

        // (b) a completion naming a non-alias allocation: the util
        // completion names a module-scope initialized binding (never an
        // import alias) instead of its ordered cell list.
        BindingId nonAlias = moduleScopeInitializedBinding(unit);
        check(nonAlias != null,
            "the unit carries a module-scope initialized (non-alias) binding");
        if (nonAlias != null) {
            LoweredModuleUnit wrongCell = withImportCells(unit, completion,
                List.of(nonAlias));
            assertGateFault(wrongCell, result.tableOf(APP), result, APP,
                BindingsProductionValidator.BINDING_INIT_ONCE,
                SemanticCapability.BINDINGS,
                "which is not an import-alias allocation of the unit",
                "BindingsProductionValidator BINDING_INIT_ONCE");
        }

        // (c) a completion/entry kind disagreement: the real project-level
        // recorder is pre-registered with a kind the unit's completion does
        // not carry.
        NamespaceRegistrations.Recorder recorder = new NamespaceRegistrations.Recorder(
            Map.of(UTIL, ModuleImportKind.STDLIB));
        Optional<CompilerDiagnostic> kindFailure = recorder.record(unit);
        check(kindFailure.isPresent(),
            "the registration entry kind disagreement is rejected");
        if (kindFailure.isPresent()) {
            CompilerDiagnostic diagnostic = kindFailure.get();
            check("E6005".equals(diagnostic.code())
                    && diagnostic.message().contains("validatorRule "
                        + NamespaceRegistrations.NAMESPACE_REGISTRATION)
                    && diagnostic.message().contains("module '" + APP.path() + "'")
                    && diagnostic.message().contains(
                        "capability " + SemanticCapability.MODULES)
                    && diagnostic.message().contains(
                        "origin NamespaceRegistrations record"),
                "the kind disagreement returns the first E6005 "
                    + "NAMESPACE_REGISTRATION with module, capability, and origin; "
                    + "got " + diagnostic.message());
        }
        // Positive control: the same unit records cleanly under the real
        // import facts.
        NamespaceRegistrations.Assembly assembly =
            NamespaceRegistrations.assemble(List.of(unit));
        check(!assembly.hasErrors() && assembly.registrations() != null,
            "the same unit assembles under the real import facts: "
                + assembly.diagnostics());
    }

    private static void testBodyLocalFaults() throws Exception {
        System.out.println("-- faults: the body-local producer defects "
            + "(R-BOUNDARY-TRIPLE) --");
        SemanticLowerer.ProjectLoweringResult result = baseProject();
        if (result == null) {
            return;
        }
        // (a) a body-local identity on a body with an assigned invocation
        // shape: the entry body's RETURN is re-keyed to its own CLOSURE_NEW
        // while the ENTRY_INVOKE call is the assigned invocation.
        LoweredModuleUnit app = unitOf(result, APP);
        check(app != null, "the battery carries the app unit");
        if (app != null) {
            FunctionId mainFunction = mainFunctionOf(app);
            SemanticOp mainCreation = creationOf(app, mainFunction);
            check(mainFunction != null && mainCreation != null,
                "the entry body's CLOSURE_NEW is carried by the unit");
            if (mainFunction != null && mainCreation != null) {
                LoweredModuleUnit forged = withReturnEnclosing(app, mainFunction,
                    mainCreation.opId());
                check(forged != null, "the forged body-local identity unit is built");
                if (forged != null) {
                    assertGateFault(forged, result.tableOf(APP), result, APP,
                        SemanticIrValidator.R_BOUNDARY_TRIPLE,
                        SemanticCapability.FOUNDATION_VALUES,
                        "assigned invocation shape",
                        "SemanticIrValidator R-BOUNDARY-TRIPLE");
                }
            }
        }

        // (b) a body-local boundary outside its body's RETURN: the
        // zero-call-site body's body-local boundary is re-parented to its
        // creation op.
        LoweredModuleUnit util = unitOf(result, UTIL);
        check(util != null, "the battery carries the util unit");
        if (util != null) {
            SemanticOp bodyLocalReturn = null;
            for (SemanticOp op : util.ops()) {
                if (op.kind() == SemanticOpKind.RETURN
                        && op.payload() instanceof KindPayload.ReturnPayload returned
                        && isCreationOp(util, returned.enclosingInvocationOpId())) {
                    bodyLocalReturn = op;
                }
            }
            check(bodyLocalReturn != null,
                "the util unit carries the body-local return cell of the "
                    + "zero-call-site body");
            if (bodyLocalReturn != null) {
                KindPayload.ReturnPayload returned =
                    (KindPayload.ReturnPayload) bodyLocalReturn.payload();
                LoweredModuleUnit forged = withBoundaryParent(util,
                    returned.returnBoundaryOpId(),
                    returned.enclosingInvocationOpId());
                check(forged != null, "the re-parented boundary unit is built");
                if (forged != null) {
                    assertGateFault(forged, result.tableOf(UTIL), result, UTIL,
                        SemanticIrValidator.R_BOUNDARY_TRIPLE,
                        SemanticCapability.FOUNDATION_VALUES,
                        "parented to the body's RETURN",
                        "SemanticIrValidator R-BOUNDARY-TRIPLE");
                }
            }
        }
    }

    /**
     * Asserts the composed-gate fault surface over a unit the real entry
     * produced: the first E6005 with the rule, the module, the capability,
     * and the origin, and no project, tables, registries, seeds, or
     * registrations. The corrupted unit cannot enter a project: the
     * per-unit chain the entry composes rejects it before any record is
     * collected, so the entry's failure projection carries the unchanged
     * no-partial-result invariant.
     */
    private static void assertGateFault(LoweredModuleUnit unit,
            StructuredBodyTable table, SemanticLowerer.ProjectLoweringResult result,
            ModuleId module, String rule, SemanticCapability capability,
            String contains, String originFragment) {
        ExternalModuleInterface ownInterface =
            result.project().interfaceIndex().modules().get(module);
        Optional<CompilerDiagnostic> failure = SemanticLowerer.validateProjectUnit(
            unit, table, comparisonFacts(result),
            BindingsProductionValidator.PinnedWriteFacts.empty(),
            result.registryOf(module), new JsonDefaultChildTable(Map.of()),
            ownInterface, inProjectFacts(result));
        check(failure.isPresent(),
            "the forged " + rule + " fault fails the composed chain");
        if (failure.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = failure.get();
        check("E6005".equals(diagnostic.code()),
            "the forged fault returns E6005; got " + diagnostic.code());
        check(diagnostic.message().contains("validatorRule " + rule),
            "the forged fault names the rule " + rule + "; got "
                + diagnostic.message());
        check(diagnostic.message().contains("module '" + module.path() + "'"),
            "the forged fault names the module " + module.path() + "; got "
                + diagnostic.message());
        check(diagnostic.message().contains("capability " + capability),
            "the forged fault names the capability " + capability + "; got "
                + diagnostic.message());
        check(diagnostic.message().contains(contains),
            "the forged fault names its defect (\"" + contains + "\"); got "
                + diagnostic.message());
        check(diagnostic.message().contains("origin " + originFragment),
            "the forged fault names the origin " + originFragment + "; got "
                + diagnostic.message());
        // The failure projection's no-partial-result invariant: the exact
        // projection the entry builds on a unit-chain failure carries the
        // first E6005 and no project, no tables, no registries, no seeds,
        // and no registrations, and any populated variant is rejected.
        SemanticLowerer.ProjectLoweringResult projected =
            new SemanticLowerer.ProjectLoweringResult(null, Map.of(), Map.of(),
                null, null, List.of(diagnostic));
        check(projected.project() == null && projected.tables().isEmpty()
                && projected.registries().isEmpty() && projected.seeds() == null
                && projected.namespaces() == null
                && projected.diagnostics().equals(List.of(diagnostic)),
            "the failure projection carries the first E6005 and no records");
        try {
            new SemanticLowerer.ProjectLoweringResult(null, Map.of(module, table),
                Map.of(), null, null, List.of(diagnostic));
            fail("a failed project lowering result must reject a populated table map");
        } catch (IllegalArgumentException expected) {
            passed++;
        }
    }

    private static SemanticIrValidator.ComparisonFacts comparisonFacts(
            SemanticLowerer.ProjectLoweringResult result) {
        return new SemanticIrValidator.ComparisonFacts(
            result.project().interfaceIndex().interfaceIndexDigest(),
            SemanticProfile.DEAL_V1_2_INT32,
            invocation().capabilityRegistryHash());
    }

    private static LoweredModuleUnit unitOf(
            SemanticLowerer.ProjectLoweringResult result, ModuleId module) {
        if (result == null || result.project() == null) {
            return null;
        }
        return result.project().modules().get(module);
    }

    private static FunctionId mainFunctionOf(LoweredModuleUnit unit) {
        FunctionId mainFunction = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.ENTRY_INVOKE
                    && op.payload() instanceof KindPayload.EntryInvokePayload entry) {
                mainFunction = entry.mainFunction();
            }
        }
        return mainFunction;
    }

    private static SemanticOp creationOf(LoweredModuleUnit unit,
            FunctionId function) {
        if (function == null) {
            return null;
        }
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CLOSURE_NEW
                    && op.payload() instanceof KindPayload.ClosureNewPayload closure
                    && closure.function().equals(function)) {
                return op;
            }
        }
        return null;
    }

    private static boolean isCreationOp(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op.kind() == SemanticOpKind.CLOSURE_NEW
                    || op.kind() == SemanticOpKind.RECURSIVE_GROUP_INIT;
            }
        }
        return false;
    }

    /** A module-scope ALLOC whose binding also carries a BINDING_INIT. */
    private static BindingId moduleScopeInitializedBinding(LoweredModuleUnit unit) {
        Set<BindingId> initialized = new LinkedHashSet<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingInitPayload init) {
                initialized.add(init.binding());
            }
        }
        BlockId moduleBlock = unit.moduleInit().initBlock();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && alloc.scope().equals(moduleBlock)
                    && initialized.contains(alloc.binding())) {
                return alloc.binding();
            }
        }
        return null;
    }

    // =========================================================================
    // Corruption helpers
    // =========================================================================

    /** One lowered unit with the given op list (the corruption surface). */
    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
                                             List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    /** One lowered unit with the given function-binding registrations. */
    private static LoweredModuleUnit withFunctionBindings(LoweredModuleUnit unit,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), bindings, unit.ops());
    }

    /** The registrations without the given key (the removal surface). */
    private static Map<FunctionAllocationIdentity, FunctionExecutionBinding>
            withoutRegistration(LoweredModuleUnit unit,
                FunctionAllocationIdentity key) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.remove(key);
        return bindings;
    }

    /** The unit with one {@code BINDING_INIT}'s init operand replaced. */
    private static LoweredModuleUnit withInitOperand(LoweredModuleUnit unit,
            OpId initOpId, ValueId value) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(initOpId)
                    && op.payload() instanceof KindPayload.BindingInitPayload init) {
                ops.add(rebuild(op, new KindPayload.BindingInitPayload(
                    init.binding(), init.generation(), value)));
            } else {
                ops.add(op);
            }
        }
        return withOps(unit, ops);
    }

    /** The unit with one {@code MODULE_IMPORT}'s alias-cell list replaced. */
    private static LoweredModuleUnit withImportCells(LoweredModuleUnit unit,
            SemanticOp completion, List<BindingId> cells) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(completion.opId())
                    && op.payload()
                        instanceof KindPayload.ModuleImportPayload payload) {
                ops.add(rebuild(op, new KindPayload.ModuleImportPayload(
                    payload.rawSpecifier(), payload.resolvedModule(),
                    payload.kind(), cells)));
            } else {
                ops.add(op);
            }
        }
        return withOps(unit, ops);
    }

    /**
     * The unit with a second {@code MODULE_IMPORT} op naming the same module
     * and cells (the two-completions corruption).
     */
    private static LoweredModuleUnit withDuplicateImport(LoweredModuleUnit unit,
            SemanticOp completion, OpId duplicateId) {
        if (!(completion.payload()
                instanceof KindPayload.ModuleImportPayload payload)) {
            return null;
        }
        SemanticOp duplicate = rebuildWithId(completion, duplicateId,
            new KindPayload.ModuleImportPayload(payload.rawSpecifier(),
                payload.resolvedModule(), payload.kind(), payload.aliasCells()));
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op);
            if (op.opId().equals(completion.opId())) {
                ops.add(duplicate);
            }
        }
        return withOps(unit, ops);
    }

    /**
     * The block-membership table with the duplicate completion inserted
     * directly after the original in its block.
     */
    private static StructuredBodyTable tableWithDuplicate(
            StructuredBodyTable original, OpId originalOpId, OpId duplicateId) {
        BlockId block = original.opBlocks().get(originalOpId);
        if (block == null) {
            return null;
        }
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<OpId>> entry : original.blockOps().entrySet()) {
            blockOps.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>(original.opBlocks());
        List<OpId> list = blockOps.computeIfAbsent(block, k -> new ArrayList<>());
        int position = list.indexOf(originalOpId);
        if (position < 0) {
            return null;
        }
        list.add(position + 1, duplicateId);
        opBlocks.put(duplicateId, block);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /** The unit with one body's {@code RETURN}s re-keyed to a forged identity. */
    private static LoweredModuleUnit withReturnEnclosing(LoweredModuleUnit unit,
            FunctionId function, OpId enclosing) {
        List<SemanticOp> ops = new ArrayList<>();
        boolean rewritten = false;
        for (SemanticOp op : unit.ops()) {
            SemanticOp candidate = op;
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload returned
                    && returned.function().equals(function)) {
                candidate = rebuild(op, new KindPayload.ReturnPayload(returned.value(),
                    returned.function(), enclosing, returned.returnBoundaryOpId()));
                rewritten = true;
            }
            ops.add(candidate);
        }
        return rewritten ? withOps(unit, ops) : null;
    }

    /** The unit with one op re-parented to the given op id. */
    private static LoweredModuleUnit withBoundaryParent(LoweredModuleUnit unit,
            OpId boundaryId, OpId parent) {
        List<SemanticOp> ops = new ArrayList<>();
        boolean rewritten = false;
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(boundaryId)) {
                SourceOrigin origin = op.origin();
                ops.add(new SemanticOp(op.opId(), op.kind(),
                    new SourceOrigin(origin.sourceId(), origin.span(), origin.kind(),
                        origin.anchorId(), parent),
                    op.result(), op.resultType(), op.operands(), op.operandTypes(),
                    op.payload(), op.failurePolicy(), op.contract()));
                rewritten = true;
                continue;
            }
            ops.add(op);
        }
        return rewritten ? withOps(unit, ops) : null;
    }

    /** One op with a replaced payload and its wired contract snapshot. */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        return rebuildWithId(op, op.opId(), payload);
    }

    private static SemanticOp rebuildWithId(SemanticOp op, OpId opId,
            KindPayload payload) {
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(),
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(), digest);
        return new SemanticOp(opId, op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contract);
    }

    /** The in-project {@code SharedFactoryFacts} of the base project. */
    private static Map<ClassId, SharedFactoryFacts> inProjectFacts(
            SemanticLowerer.ProjectLoweringResult result) {
        Map<ClassId, SharedFactoryFacts> facts = new LinkedHashMap<>();
        if (result == null || result.project() == null) {
            return facts;
        }
        for (ModuleId module : result.project().modules().keySet()) {
            LoweredModuleUnit unit = result.project().modules().get(module);
            ExternalModuleInterface entry =
                result.project().interfaceIndex().modules().get(module);
            if (unit == null || entry == null || result.registryOf(module) == null) {
                continue;
            }
            for (ClassInterface classEntry : entry.classes()) {
                ClassLayout layout = unit.classLayouts().get(classEntry.classId());
                if (layout == null) {
                    continue;
                }
                OpId factoryOpId = result.registryOf(module)
                    .factoryFor(classEntry.constructionEntry());
                if (factoryOpId == null) {
                    continue;
                }
                SemanticOp factoryOp = null;
                for (SemanticOp op : unit.ops()) {
                    if (op.opId().equals(factoryOpId)) {
                        factoryOp = op;
                    }
                }
                if (factoryOp == null
                        || !(factoryOp.result() instanceof ValueId value)) {
                    continue;
                }
                facts.put(classEntry.classId(), new SharedFactoryFacts(
                    classEntry.classId(), classEntry, layout, factoryOpId, value));
            }
        }
        return facts;
    }

    // =========================================================================
    // Part 3: the unchanged-surface audit
    // =========================================================================

    /** The pre-slice closed {@code SemanticOpKind} membership (55 kinds). */
    private static final List<String> PRE_SLICE_SEMANTIC_OP_KINDS = List.of(
        "ARRAY_LENGTH", "ARRAY_NEW", "ASSIGN", "ASYNC_START", "AWAIT", "BINARY",
        "BINDING_ALLOC", "BINDING_INIT", "BINDING_LOAD", "BINDING_STORE", "BOUNDARY",
        "BRANCH", "BREAK", "CALL", "CALLBACK_INVOKE", "CLASS_DEFAULT", "CLASS_FACTORY",
        "CLASS_NEW", "CLOSURE_NEW", "CONST", "CONTINUE", "DELETE", "DISCARD",
        "ENTRY_INVOKE", "EXPORT_PUBLISH", "EXPORT_READ", "EXTERNAL_ENTRY", "FIELD_DELETE",
        "FIELD_READ", "FIELD_WRITE", "FOR_EACH", "FUNCTION_ADAPT", "HAS_FIELD",
        "INDEX_DELETE", "INDEX_NORMALIZE", "INDEX_READ", "INDEX_WRITE", "INTRINSIC_CALL",
        "JSON_FROM_CLASS", "JSON_TO_CLASS", "LOOP", "MEMBER_DELETE", "MEMBER_READ",
        "MEMBER_WRITE", "MODULE_IMPORT", "MODULE_INIT", "OPTIONAL_READ",
        "RECURSIVE_GROUP_INIT", "RETURN", "STDLIB_CALL", "STRING_CONCAT", "TABLE_NEW",
        "THROW", "TRY_CATCH", "UNARY");

    /** The pre-slice closed {@code DefaultOwner} membership (three members). */
    private static final List<String> PRE_SLICE_DEFAULT_OWNERS = List.of(
        "LOCAL", "SHARED_FACTORY", "RETAINED_ABI");

    /** The three registration-owned members this slice adds. */
    private static final List<String> REGISTRATION_DEFAULT_OWNERS = List.of(
        "HOST_DEFAULTS", "FFI_PLAN", "BUILTIN_DEFAULTS");

    /** The pre-slice closed {@code FunctionExecutionBinding} shapes (five). */
    private static final List<String> PRE_SLICE_FUNCTION_BINDINGS = List.of(
        "AdapterBinding", "ExternalFunction", "HostFunction", "HostFunctionValue",
        "LoweredBody");

    /** The one binding shape this slice adds. */
    private static final String INTRINSIC_FUNCTION_BINDING = "IntrinsicFunction";

    /**
     * The one binding shape the function-typed-value child adds
     * (ISSUE-0673): the dynamic materialization whose execution class is
     * resolved from the runtime value's producing registration.
     */
    private static final String DYNAMIC_FUNCTION_VALUE_BINDING = "DynamicFunctionValue";

    /**
     * The SHA-256 of the {@link #payloadShapeBaseline()} text of the real
     * loaded payload records, with {@code ModuleImportPayload}'s recorded
     * alias-cell component excluded: the frozen pre-slice payload-record
     * shapes. The one recorded addition is asserted structurally.
     */
    private static final String PAYLOAD_SHAPE_BASELINE_SHA256 =
        "22df0512f1b66f7de4aa3e1094b2d4332d4ada29f0f0517bbec42389636105a9";

    private static void testFrozenClosedSets() {
        System.out.println("-- frozen surfaces: the closed sets --");
        List<String> kinds = new ArrayList<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            kinds.add(kind.name());
        }
        checkEq(PRE_SLICE_SEMANTIC_OP_KINDS, sorted(kinds),
            "the closed SemanticOpKind membership equals the pre-slice set");
        checkEq(55, kinds.size(),
            "the closed SemanticOpKind set stays at 55 members");

        List<String> owners = new ArrayList<>();
        for (DefaultOwner owner : DefaultOwner.values()) {
            owners.add(owner.name());
        }
        List<String> expectedOwners = new ArrayList<>(PRE_SLICE_DEFAULT_OWNERS);
        expectedOwners.addAll(REGISTRATION_DEFAULT_OWNERS);
        checkEq(expectedOwners, owners,
            "the closed DefaultOwner membership is the pre-slice three plus the "
                + "three registration-owned members");
        for (String owner : PRE_SLICE_DEFAULT_OWNERS) {
            check(owners.contains(owner),
                "the pre-slice DefaultOwner member " + owner + " is unchanged");
        }
        for (String owner : REGISTRATION_DEFAULT_OWNERS) {
            check(owners.contains(owner),
                "the registration-owned DefaultOwner member " + owner
                    + " is present");
        }

        Set<String> expectedBindings = new LinkedHashSet<>(PRE_SLICE_FUNCTION_BINDINGS);
        expectedBindings.add(INTRINSIC_FUNCTION_BINDING);
        expectedBindings.add(DYNAMIC_FUNCTION_VALUE_BINDING);
        Class<?>[] permitted = FunctionExecutionBinding.class.getPermittedSubclasses();
        check(permitted != null,
            "FunctionExecutionBinding stays a sealed closed set");
        if (permitted != null) {
            Set<String> actual = new LinkedHashSet<>();
            for (Class<?> shape : permitted) {
                actual.add(shape.getSimpleName());
                check(shape.isRecord(),
                    "the binding shape " + shape.getSimpleName() + " stays a record");
            }
            checkEq(expectedBindings, actual,
                "the closed FunctionExecutionBinding set is the pre-slice five plus "
                    + "the IntrinsicFunction shape plus the DynamicFunctionValue shape");
        }

        // The other closed sets the seeds and the namespace registrations
        // consume keep their pre-slice membership, plus the ISSUE-0626
        // bytes extension: the closed intrinsic-kind set gains the
        // allocation intrinsic BYTES_NEW (K6 item 1 / K9 item 1; the two
        // conversion intrinsics stay the seeded first-class values).
        List<String> intrinsicKinds = new ArrayList<>();
        for (IntrinsicKind kind : IntrinsicKind.values()) {
            intrinsicKinds.add(kind.name());
        }
        checkEq(List.of("INT_CONVERT", "NUMBER_CONVERT", "BYTES_NEW"), intrinsicKinds,
            "the closed IntrinsicKind set is the two conversion intrinsics plus the "
                + "bytes allocation intrinsic");
        List<String> importKinds = new ArrayList<>();
        for (ModuleImportKind kind : ModuleImportKind.values()) {
            importKinds.add(kind.name());
        }
        checkEq(List.of("COMPILED", "STDLIB", "HOST"), importKinds,
            "the closed ModuleImportKind set is unchanged");
    }

    private static void testFrozenPayloadRecords() {
        System.out.println("-- frozen surfaces: every payload record's shape --");
        Set<Class<?>> shapes = new LinkedHashSet<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            Class<? extends KindPayload> payload = kind.payloadClass();
            check(payload.isRecord(), kind + " keeps its payload record");
            check(shapes.add(payload), kind + " keeps its distinct payload shape");
        }
        checkEq(55, shapes.size(),
            "55 distinct payload shapes for the 55 closed kinds");

        // The one recorded payload addition: ModuleImportPayload's ordered
        // alias-cell list, appended after the three pre-existing components.
        RecordComponent[] importComponents =
            KindPayload.ModuleImportPayload.class.getRecordComponents();
        checkEq(4, importComponents.length,
            "MODULE_IMPORT carries exactly one new component");
        if (importComponents.length == 4) {
            checkEq("rawSpecifier", importComponents[0].getName(),
                "the first pre-existing MODULE_IMPORT component keeps its position");
            checkEq("resolvedModule", importComponents[1].getName(),
                "the second pre-existing MODULE_IMPORT component keeps its position");
            checkEq("kind", importComponents[2].getName(),
                "the third pre-existing MODULE_IMPORT component keeps its position");
            checkEq("aliasCells", importComponents[3].getName(),
                "the new component is named aliasCells");
            checkEq(List.class, importComponents[3].getType(),
                "the new component is the ordered alias-cell list");
        }

        // The canonical MODULE_IMPORT payload carries exactly the four
        // keys through the real canonicalizer mapping.
        CanonicalJson.Obj payloadJson = (CanonicalJson.Obj)
            ContractSnapshotCanonicalizer.payloadJson(
                new KindPayload.ModuleImportPayload("a", new ModuleId("a"),
                    ModuleImportKind.COMPILED, List.of()));
        checkEq(List.of("aliasCells", "kind", "rawSpecifier", "resolvedModule"),
            sorted(keysOf(payloadJson)),
            "the canonical MODULE_IMPORT payload carries exactly the four keys");

        // Every other payload record keeps the frozen pre-slice shape: the
        // baseline text excludes only the recorded alias-cell component.
        String baseline = payloadShapeBaseline();
        String digest = CanonicalJson.sha256Hex(
            baseline.getBytes(StandardCharsets.UTF_8));
        if (!PAYLOAD_SHAPE_BASELINE_SHA256.equals(digest)) {
            System.err.println("--- computed payload shape baseline ---");
            System.err.println(baseline);
            System.err.println("--- end baseline ---");
        }
        checkEq(PAYLOAD_SHAPE_BASELINE_SHA256, digest,
            "every payload record except MODULE_IMPORT keeps the frozen pre-slice "
                + "shape (the baseline excludes only the recorded alias-cell component)");
    }

    /**
     * The canonical text of every payload record's components, sorted by
     * record name, with {@code ModuleImportPayload}'s alias-cell component
     * excluded. The text is read through reflection over the real loaded
     * payload records.
     */
    private static String payloadShapeBaseline() {
        List<String> lines = new ArrayList<>();
        Set<Class<?>> seen = new LinkedHashSet<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            Class<? extends KindPayload> payload = kind.payloadClass();
            if (!seen.add(payload)) {
                continue;
            }
            StringBuilder sb = new StringBuilder(payload.getSimpleName()).append('(');
            boolean first = true;
            for (RecordComponent component : payload.getRecordComponents()) {
                if (payload == KindPayload.ModuleImportPayload.class
                        && component.getName().equals("aliasCells")) {
                    continue;
                }
                if (!first) {
                    sb.append(',');
                }
                first = false;
                sb.append(component.getName()).append(':')
                    .append(component.getGenericType().getTypeName());
            }
            lines.add(sb.append(')').toString());
        }
        return String.join("\n", sorted(lines));
    }

    private static void testFrozenVersionAndDumpKeySets() throws Exception {
        System.out.println("-- frozen surfaces: the version text and both closed "
            + "dump key sets --");
        checkEq("deal.semantic-ir/1", LoweredModuleUnit.FORMAT_VERSION,
            "the deal.semantic-ir/1 version text is unchanged");
        SemanticLowerer.ProjectLoweringResult result = baseProject();
        if (result == null) {
            return;
        }
        CanonicalJson.Obj unitJson = (CanonicalJson.Obj) CanonicalJson.parse(
            SemanticIrDumper.dumpModuleText(unitOf(result, APP)));
        checkEq(List.of("constructCoverage", "formatVersion", "functionBindings",
                "interfaceHash", "loweringContextHash", "moduleId", "ops",
                "requiredCapabilities", "semanticProfile"),
            sorted(keysOf(unitJson)),
            "the unit text protocol's closed key set is unchanged");
        CanonicalJson.Obj manifestJson = (CanonicalJson.Obj) CanonicalJson.parse(
            SemanticIrDumper.dumpManifestText(result.project()));
        checkEq(List.of("entryModule", "formatVersion", "modules", "semanticProfile"),
            sorted(keysOf(manifestJson)),
            "the project manifest's closed key set is unchanged");
        // The registrations and the seeds are not part of either closed key
        // set: the alias cells travel on the MODULE_IMPORT payloads.
        boolean carriedCells = false;
        for (SemanticOp op : unitOf(result, APP).ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT
                    && op.payload() instanceof KindPayload.ModuleImportPayload payload
                    && !payload.aliasCells().isEmpty()) {
                carriedCells = true;
            }
        }
        check(carriedCells,
            "the dump-visible MODULE_IMPORT payloads carry the alias-cell lists");
    }

    private static List<String> keysOf(CanonicalJson.Obj object) {
        return object.entries().stream().map(CanonicalJson.Entry::key).toList();
    }

    /**
     * The text between the signature's opening brace and its matching
     * closing brace (string/char literals and comments are respected), or
     * null when the signature is absent.
     */
    private static String methodBody(String source, String signature) {
        int signatureAt = source.indexOf(signature);
        if (signatureAt < 0) {
            return null;
        }
        int open = source.indexOf('{', signatureAt + signature.length());
        if (open < 0) {
            return null;
        }
        int depth = 0;
        boolean inString = false;
        boolean inChar = false;
        boolean inLineComment = false;
        boolean inBlockComment = false;
        for (int i = open; i < source.length(); i++) {
            char c = source.charAt(i);
            char next = i + 1 < source.length() ? source.charAt(i + 1) : '\0';
            if (inLineComment) {
                if (c == '\n') {
                    inLineComment = false;
                }
                continue;
            }
            if (inBlockComment) {
                if (c == '*' && next == '/') {
                    inBlockComment = false;
                    i++;
                }
                continue;
            }
            if (inString) {
                if (c == '\\') {
                    i++;
                } else if (c == '"') {
                    inString = false;
                }
                continue;
            }
            if (inChar) {
                if (c == '\\') {
                    i++;
                } else if (c == '\'') {
                    inChar = false;
                }
                continue;
            }
            if (c == '/' && next == '/') {
                inLineComment = true;
                i++;
                continue;
            }
            if (c == '/' && next == '*') {
                inBlockComment = true;
                i++;
                continue;
            }
            if (c == '"') {
                inString = true;
                continue;
            }
            if (c == '\'') {
                inChar = true;
                continue;
            }
            if (c == '{') {
                depth++;
            } else if (c == '}') {
                depth--;
                if (depth == 0) {
                    return source.substring(open, i + 1);
                }
            }
        }
        return null;
    }

    private static void testProductionPathUnchanged() throws Exception {
        System.out.println("-- frozen surfaces: the production compile path --");
        Path root = repoRoot();
        check(root != null, "the repository root is located");
        if (root == null) {
            return;
        }
        List<Path> productionSources = javaSources(root.resolve("deal"));
        check(!productionSources.isEmpty(),
            "the production source surface is real and non-empty");
        int entryDeclarations = 0;
        int unitCallSites = 0;
        for (Path file : productionSources) {
            String text = Files.readString(file, StandardCharsets.UTF_8);
            int occurrences = countOccurrences(text, "lowerProject(");
            if (file.getFileName().toString().equals("SemanticLowerer.java")) {
                entryDeclarations += occurrences;
            } else if (file.getFileName().toString()
                    .equals("ProductionProjectEmission.java")) {
                unitCallSites += occurrences;
            } else {
                check(occurrences == 0,
                    "no production call site invokes lowerProject in " + file);
            }
        }
        checkEq(1, entryDeclarations,
            "SemanticLowerer.java carries the single lowerProject declaration and "
                + "no production call site");
        checkEq(1, unitCallSites,
            "the production project emission unit carries the single lowerProject "
                + "call site of the production source set");

        // ISSUE-0642: the production unit reads no routing, planner,
        // registry, retained-backend, or counting surface.
        String productionUnit = Files.readString(
            root.resolve("deal/module/ProductionProjectEmission.java"),
            StandardCharsets.UTF_8);
        for (String forbidden : List.of("ModuleRoute", "MigrationPlanner",
                "CapabilityRegistry", "routeOf(", "validateMixedEdges",
                "LuaBackend.generate", "JvmBackend.generate",
                "retainedEmissionCount")) {
            check(!productionUnit.contains(forbidden),
                "the production project emission unit references no '" + forbidden
                    + "'");
        }

        String orchestrator = Files.readString(
            root.resolve("deal/module/CompilationOrchestrator.java"),
            StandardCharsets.UTF_8);
        for (String site : List.of("emitSharedLuaModule(", "emitSharedJvmModule(",
                "lowerSharedModule(", "routeOf(info)", "validateMixedEdges()",
                "retainedEmissionCount++", "semanticEmissionCount++",
                "LuaBackend.generateToFile(", "JvmBackend.generate(")) {
            check(orchestrator.contains(site),
                "the production compile path keeps its call site '" + site + "'");
        }

        // ISSUE-0643 P11: the phase-4 dispatch method and the production
        // arm method of the orchestrator reach no retained backend, no
        // route surface, no planner/registry, and no retained counter;
        // the harness remnants stay outside their method bodies.
        String dispatch = methodBody(orchestrator, "private void codegenAll()");
        check(dispatch != null, "the phase-4 dispatch method is located");
        if (dispatch != null) {
            check(dispatch.contains("productionArmApplies()")
                    && dispatch.contains("emitProductionProject()"),
                "the dispatch selects the production arm through the"
                    + " release-owned predicate: " + dispatch);
            for (String forbidden : List.of("ModuleRoute", "ModuleRoutePlan",
                    "MigrationPlanner", "CapabilityRegistry", "routeOf(",
                    "validateMixedEdges", "LuaBackend", "JvmBackend",
                    "retainedEmissionCount", "semanticEmissionCount")) {
                check(!dispatch.contains(forbidden),
                    "the phase-4 dispatch method references no '" + forbidden
                        + "'");
            }
        }
        String arm = methodBody(orchestrator,
            "private void emitProductionProject()");
        check(arm != null, "the production arm method is located");
        if (arm != null) {
            check(arm.contains("ProductionProjectEmission.run("),
                "the production arm runs the production project emission"
                    + " unit: " + arm);
            for (String forbidden : List.of("ModuleRoute", "ModuleRoutePlan",
                    "MigrationPlanner", "CapabilityRegistry", "routeOf(",
                    "validateMixedEdges", "LuaBackend", "JvmBackend",
                    "retainedEmissionCount", "generate(")) {
                check(!arm.contains(forbidden),
                    "the production arm method references no '" + forbidden
                        + "'");
            }
        }
        String predicate = methodBody(orchestrator,
            "public static boolean isProductionInvocation(");
        check(predicate != null
                && predicate.contains("defaultInvocation()")
                && !predicate.contains("purpose"),
            "the production-invocation predicate is record identity, never"
                + " a purpose-only test: " + predicate);
        String planner = Files.readString(
            root.resolve("deal/semantic/MigrationPlanner.java"),
            StandardCharsets.UTF_8);
        check(planner.contains("planRoutes("),
            "the route planning entry is unchanged");
        String stager = Files.readString(
            root.resolve("deal/publication/PublicationStager.java"),
            StandardCharsets.UTF_8);
        check(stager.contains("class PublicationStager"),
            "the transactional stager stays in the tree");
        String main = Files.readString(root.resolve("deal/Main.java"),
            StandardCharsets.UTF_8);
        check(main.contains("public static void main("),
            "the CLI entry stays in the tree");
        check(orchestrator.contains("sourceMap"),
            "the source-map handling stays in the compile path");
    }

    private static void testJavaScriptAndRetainedClasses() throws Exception {
        System.out.println("-- frozen surfaces: JavaScript and the retained "
            + "classes --");
        Path root = repoRoot();
        check(root != null, "the repository root is located");
        if (root == null) {
            return;
        }
        List<Path> jsSources = new ArrayList<>();
        Path runtimeJs = root.resolve("deal/runtime.js");
        check(Files.isRegularFile(runtimeJs),
            "the JavaScript runtime stays in the tree");
        jsSources.add(runtimeJs);
        try (Stream<Path> listing = Files.list(root.resolve("std"))) {
            listing.filter(path -> path.getFileName().toString().endsWith(".js"))
                .sorted()
                .forEach(jsSources::add);
        }
        check(!jsSources.isEmpty(),
            "the JavaScript standard library stays in the tree");
        for (Path js : jsSources) {
            String text = Files.readString(js, StandardCharsets.UTF_8);
            for (String marker : JS_SLICE_MARKERS) {
                check(!text.contains(marker),
                    "the JavaScript source " + js.getFileName()
                        + " carries no slice surface '" + marker + "'");
            }
        }
        String jsBackend = Files.readString(
            root.resolve("deal/codegen/js/JsBackend.java"),
            StandardCharsets.UTF_8);
        for (String marker : JS_SLICE_MARKERS) {
            check(!jsBackend.contains(marker),
                "the JavaScript emitter carries no slice surface '" + marker + "'");
        }

        // The retained backends stay in the tree with their entry points.
        String luaBackend = Files.readString(
            root.resolve("deal/codegen/lua/LuaBackend.java"),
            StandardCharsets.UTF_8);
        check(luaBackend.contains("public static String generate(")
                && luaBackend.contains("generateToFile("),
            "the retained LuaJIT backend keeps its generate entry points");
        String jvmBackend = Files.readString(
            root.resolve("deal/codegen/jvm/JvmBackend.java"),
            StandardCharsets.UTF_8);
        check(jvmBackend.contains("public static JvmCodegenResult generate("),
            "the retained JVM backend keeps its generate entry points");

        // Every focused test main of the slice and every superseded pin's
        // test still exists and stays registered (nothing deleted).
        String manifest = Files.readString(root.resolve("tools/gate-manifest.sh"),
            StandardCharsets.UTF_8);
        List<String> sliceMains = List.of(
            "ProjectLoweringTest", "BodyInvocationIdentityTest",
            "HostDeclarationSurfaceTest", "ClassRegistrationSeedsTest",
            "IntrinsicSeedBindingsTest", "ModuleImportNamespaceRegistrationTest",
            "ProjectGateFaultBatteryTest");
        for (String mainClass : sliceMains) {
            check(Files.isRegularFile(root.resolve("test/" + mainClass + ".java")),
                "the slice's focused test main " + mainClass
                    + ".java stays in the tree");
            check(manifest.contains("deal.test." + mainClass),
                "the slice's focused test main " + mainClass
                    + " is registered in tools/gate-manifest.sh");
        }
        List<String> retargetedPins = List.of(
            "AdapterShapeMapPayloadTest", "BindingImmutabilityProofTest",
            "BindingsIntegrationVerificationTest", "BindingsValidationTest",
            "CheckedProjectBuilderTest", "ClosureLoweringTest",
            "FunctionBindingRegistryTest", "SemanticIrDumperTest",
            "SemanticIrSchemaTest");
        // ISSUE-0642: the production project emission unit's focused main
        // stays in the tree and registered (nothing deleted).
        check(Files.isRegularFile(
                root.resolve("test/ProductionProjectEmissionTest.java")),
            "the production project emission unit's focused test main stays in the "
                + "tree");
        check(manifest.contains("deal.test.ProductionProjectEmissionTest"),
            "the production project emission unit's focused test main is registered "
                + "in tools/gate-manifest.sh");
        for (String pin : retargetedPins) {
            check(Files.isRegularFile(root.resolve("test/" + pin + ".java")),
                "the retargeted pin " + pin
                    + ".java stays in the tree (none deleted)");
            check(manifest.contains("deal.test." + pin),
                "the retargeted pin " + pin
                    + " is registered in tools/gate-manifest.sh");
        }
        for (String retainedTest : List.of("LuaBackendTest",
                "LuaBackendIntegrationTest", "JvmBackendTest", "JsBackendTest",
                "JsConformanceTest", "JsE2eTest")) {
            check(Files.isRegularFile(root.resolve("test/" + retainedTest + ".java")),
                "the retained test " + retainedTest + ".java stays in the tree");
            check(manifest.contains("deal.test." + retainedTest),
                "the retained test " + retainedTest
                    + " stays registered in tools/gate-manifest.sh");
        }
        // The production-path test mains stay registered and green without
        // retargeting (their assertions are the suite's evidence).
        for (String productionTest : List.of("SemanticProductionGateTest",
                "MigrationPlannerTest", "PublicationStagerTest", "SourceMapTest",
                "ModuleInitDifferentialTest", "ProjectIntegrationGatesTest",
                "ProjectMigrationIntegrationTest",
                "ClassConstructionIntegrationTailTest", "SemanticIrValidatorTest")) {
            check(Files.isRegularFile(root.resolve("test/" + productionTest + ".java")),
                "the production-path test " + productionTest
                    + ".java stays in the tree");
            check(manifest.contains("deal.test." + productionTest)
                    || manifest.contains("deal.semantic." + productionTest),
                "the production-path test " + productionTest
                    + " stays registered in tools/gate-manifest.sh");
        }
    }

    /** The JavaScript sources may not reference any slice surface. */
    private static final List<String> JS_SLICE_MARKERS = List.of(
        "aliasCells", "ntrinsicFunction", "ynamicFunctionValue", "HOST_DEFAULTS",
        "FFI_PLAN", "BUILTIN_DEFAULTS", "lowerProject", "NamespaceRegistration",
        "R-BOUNDARY-TRIPLE");

    private static List<String> sorted(List<String> values) {
        List<String> copy = new ArrayList<>(values);
        java.util.Collections.sort(copy);
        return copy;
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int index = text.indexOf(needle);
        while (index >= 0) {
            count++;
            index = text.indexOf(needle, index + 1);
        }
        return count;
    }

    private static List<Path> javaSources(Path root) throws Exception {
        List<Path> sources = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            walk.filter(path -> path.getFileName().toString().endsWith(".java"))
                .sorted()
                .forEach(sources::add);
        }
        return sources;
    }

    private static Path repoRoot() {
        Path dir = Path.of("").toAbsolutePath();
        while (dir != null) {
            if (Files.isRegularFile(dir.resolve("tools/gate-manifest.sh"))
                    && Files.isDirectory(dir.resolve("deal"))) {
                return dir;
            }
            dir = dir.getParent();
        }
        return null;
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (Stream<Path> walk = Files.walk(path)) {
                    walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
                        try {
                            Files.deleteIfExists(entry);
                        } catch (java.io.IOException ignored) {
                            // best effort
                        }
                    });
                }
            }
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Project-Gate Fault Battery and Unchanged-Surface "
            + "Audit (ISSUE-0637) ===\n");

        testExternCPlanMismatchThroughEntry();
        testDeclarationClassIdentityUnresolvedThroughEntry();
        testInconsistentFactDeferralThroughEntry();
        testIntrinsicAdmissionFaults();
        testAliasNamespaceFaults();
        testBodyLocalFaults();
        testFrozenClosedSets();
        testFrozenPayloadRecords();
        testFrozenVersionAndDumpKeySets();
        testProductionPathUnchanged();
        testJavaScriptAndRetainedClasses();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
