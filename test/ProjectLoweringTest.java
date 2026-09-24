package deal.test;

import deal.ast.ClassField;
import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.ClassConstructionValidator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.NamespaceRegistration;
import deal.semantic.ir.NamespaceRegistrations;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0634: the one project lowering entry, the one allocator, and the
 * composed validator chain
 * ({@code project-lowering-entry-and-registration-seeds} D1/D2/D4/D8/D11/
 * D12 and the project lowering, registration-seed, namespace registration,
 * and project validation gate contracts;
 * {@code luajit-jvm-single-lowering-production-cutover} C1/C4/C7/C10;
 * {@code semantic-ir-construct-coverage-cutover} K3/K12's lowering
 * context), extended by ISSUE-0636 with the in-project imported-class
 * resolution ({@code project-lowering-entry-and-registration-seeds} D10
 * and the in-project imported-class contract; K3).
 *
 * <ol>
 *   <li>a real multi-module checked project (an entry module, an imported
 *       implementation module, and an imported host declaration module)
 *       built by the production checked-project builder lowers through
 *       {@link SemanticLowerer#lowerProject} to exactly one project with
 *       the complete closure in dependency order, the entry module
 *       present, globally unique ids from one allocator, and byte-identical
 *       repeated project dumps;</li>
 *   <li>the result carries exactly one block-membership table and one
 *       class-factory registry per module, the class registration seeds
 *       (one layout per declared class plus the builtin {@code Error}
 *       layout), the closed {@code IntrinsicFunction} bindings of the two
 *       conversion intrinsics, and one namespace registration per distinct
 *       imported module with the alias cells its {@code MODULE_IMPORT}
 *       completions name (dump-visible);</li>
 *   <li>the composed per-unit chain (the closed 14 rules, the address-chain
 *       protocol, the control-flow validator, the bindings production
 *       validator, and the class-construction validator) accepts the
 *       E7-armed unified units, so the unsupplied-facts chain members are
 *       re-asserted directly over the produced units and tables;</li>
 *   <li>the unified walk's class arm: an implementation module declares an
 *       exported and a local class and constructs both in the one session,
 *       so the unit's own {@code classLayouts} entries, the
 *       {@code CLASS_NEW(LOCAL)} constructions, and the exported class's
 *       {@code CLASS_FACTORY} registration are asserted over the produced
 *       unit and the composed chain re-runs over it;</li>
 *   <li>the in-project imported-class resolution (ISSUE-0636; D10 and the
 *       in-project imported-class contract; K3): the dependent module's
 *       checker-valid literals of two imported in-project classes lower
 *       {@code CLASS_NEW(SHARED_FACTORY)} with each owner's
 *       {@code constructionEntry} factory reference, an empty
 *       {@code classDefaultOpIds} list, the literal-order provided fields
 *       and the declaration-order boundaries (the omitted defaulted field
 *       wired to the owner factory op's result), zero
 *       {@code RETAINED_ABI_DEFERRED}, and the composed chain re-run with
 *       the in-project facts; the same project's cross-module call resolves
 *       through the accumulated {@code EXTERNAL_ENTRY} records as a
 *       {@code SHARED_BODY} external, and the inconsistent-fact seed (an
 *       owner outside the closure and outside the declaration set) still
 *       returns the deferral with no project;</li>
 *   <li>the four negative seeds (a corrupted unit, a missing module, a
 *       non-v1.2 invocation, an alias without a resolved import fact)
 *       return the first E6005 and no project, no tables, no registries, no
 *       seeds, and no registrations;</li>
 *   <li>the declaration-class fail-closed acceptance: a checker-valid
 *       literal of a host declaration class and of an extern-C declaration
 *       class resolves to the seed's owner member and fails closed at the
 *       class-construction validator — never a silent construction and
 *       never an artifact — while the builtin {@code Error} literal
 *       lowers its {@code CLASS_NEW(BUILTIN_DEFAULTS)} through the one
 *       project entry (ISSUE-0619; {@code semantic-ir-construct-coverage-
 *       cutover} K13) and passes the composed chain.</li>
 * </ol>
 */
public class ProjectLoweringTest {

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
    private static final CanonicalModuleIdentity HOST_CFG_IDENTITY =
        new CanonicalModuleIdentity.ExternalModule("host/cfg");
    private static final String HOST_CFG_SPECIFIER = "host/cfg";
    private static final ClassId ENDPOINT = new ClassId("$external/host/cfg",
        "Endpoint");
    private static final ClassId BUILTIN_ERROR = ClassId.ERROR;

    private static final String UTIL_SOURCE = """
        export function add(a: int, b: int): int {
          return a + b;
        }

        export function twice(x: int): int {
          return x * 2;
        }

        // A module-level recursive group (the recursive-group arm's closed
        // member-body shape: value references only, never invoked from
        // source).
        function left(): null {
          let rightRef: () => null = right;
        }
        function right(): null {
          let leftRef: () => null = left;
        }
        """;

    private static final String HOST_DECLARATION = """
        export class Endpoint {
          path: string;
          port?: int;
        }

        export function version(): int;
        """;

    /** The main fixture: source calls, an adapter, cross-module calls, and a host import. */
    private static final String APP_SOURCE = """
        import * as u from "util"
        import * as cfg from "host/cfg"

        function inc(x: int): int {
          return x + 1;
        }

        function helper(x: int): int {
          return u.add(x, 1);
        }

        export function main(): null {
          let f: (x: int) => int = inc;
          let h: (a: int, b: int) => int = f;
          let total: int = helper(2);
          let extended: int = h(3, 9);
          let doubled: int = u.twice(3);
          return null;
        }
        """;

    /** The host-declaration-class construction (the fail-closed acceptance). */
    private static final String HOST_CLASS_APP_SOURCE = """
        import * as u from "util"
        import * as cfg from "host/cfg"

        export function main(): null {
          let e: cfg.Endpoint = {path: "p"};
          return null;
        }
        """;

    /** The builtin-Error construction (the production-outcome acceptance). */
    private static final String ERROR_APP_SOURCE = """
        import * as cfg from "host/cfg"

        export function main(): null {
          let e: Error = {code: "E1", message: "boom"};
          return null;
        }
        """;

    /**
     * The in-project class arm: an implementation module declares an
     * exported class and a local class and constructs both, so the unified
     * walk's class-declaration arm, its class-literal arm, and the exported
     * variant's {@code CLASS_FACTORY} run in one session with the call and
     * closure arms.
     */
    private static final String CLASS_UTIL_SOURCE = """
        export class Point {
          x: int = 0;
          y: int = 1;
        }

        class Hidden {
          label: string = "hidden";
        }

        export function makePoint(x: int): Point {
          let p: Point = {x: x};
          let h: Hidden = {label: "local"};
          return p;
        }
        """;

    private static final String CLASS_APP_SOURCE = """
        import * as u from "util"

        export function main(): null {
          let p: u.Point = u.makePoint(4);
          return null;
        }
        """;

    /**
     * The imported in-project class resolution fixture (ISSUE-0636;
     * design sources {@code project-lowering-entry-and-registration-seeds}
     * D10 and the in-project imported-class contract;
     * {@code semantic-ir-construct-coverage-cutover} K3): the owner module
     * declares an exported class with an omitted defaulted field and an
     * exported factory function; the dependent module constructs the
     * imported class and calls the imported function in one project walk.
     */
    private static final String IMPORTED_CLASS_UTIL_SOURCE = """
        export class Point {
          x: int = 0;
          y: int = 1;
        }

        export class Segment {
          length: int = 0;
        }

        export function makePoint(x: int): Point {
          return {x: x};
        }
        """;

    private static final String IMPORTED_CLASS_APP_SOURCE = """
        import * as u from "util"

        export function main(): null {
          let p: u.Point = {x: 5};
          let s: u.Segment = {length: 3};
          let q: u.Point = u.makePoint(7);
          return null;
        }
        """;

    private static final ClassId SEGMENT = new ClassId("src", "Segment");

    // The compiler's canonical module path of a root-contained module is
    // the configured root text plus the source's relative directory
    // components (the file name is omitted), so both classes of the
    // fixture — declared in the flat `src` root — carry `@src/<Name>`:
    // the identity the checker, the declaration surface, the checked
    // project's interface index, and the legacy emission all produce.
    private static final ClassId POINT = new ClassId("src", "Point");
    private static final ClassId HIDDEN = new ClassId("src", "Hidden");

    /**
     * The extern-C declaration module of the fail-closed acceptance (the
     * {@code FFI_PLAN} seed owner): a C-struct class with its phase-3.9
     * generated plan and a declared C function.
     */
    private static final String NATIVE_DECLARATION = """
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

    /** The extern-C declaration-class construction (the fail-closed acceptance). */
    private static final String EXTERN_C_CLASS_APP_SOURCE = """
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

    /**
     * The generalized fixture harness: {@code extraSources} writes further
     * (or replacement) module files relative to the project root and
     * {@code extraExternals} adds externals declarations
     * (raw specifier &rarr; project-relative declaration path).
     */
    private static RealProject compileProject(String appSource,
            Map<String, String> extraSources,
            Map<String, String> extraExternals) throws Exception {
        Path proj = Files.createTempDirectory("project-lowering");
        writeFileIn(proj, "src/cfg.d.deal", HOST_DECLARATION);
        writeFileIn(proj, "src/util.deal", UTIL_SOURCE);
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
        // ISSUE-0643 P10 item 3: the fixture project carries host and
        // extern-C declaration imports and cross-module calls, while the
        // suite's subject — the one project lowering entry — is
        // arm-independent, so the compile resolves the harness invocation
        // and keeps the harness arm.
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, externals,
            List.of(proj.resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(), null,
            ConformanceHarnessMetadata.invocation(
                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32));
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
                || manifests.manifests() == null) {
            deleteRecursively(proj);
            throw new IllegalStateException("the fixture project did not build");
        }
        Map<ModuleId, FfiGeneratedModule> externC = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externC.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : orchestrator.hostDeclarationSurface()
                .moduleIds()) {
            // An externals-listed declaration module's public identity is
            // the externals map key exactly as written (the module-identity
            // layer's pinned rule); a project-classified declaration module
            // carries the standalone identity of its dotted module path.
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
    private static SemanticLowerer.ProjectLoweringResult lower(
            RealProject project, CompilerInvocation invocation) {
        return SemanticLowerer.lowerProject(invocation, project.checkedProject(),
            project.index(), project.manifests(), project.surface(),
            project.declarationIdentities(), project.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    // =========================================================================
    // 1. The one project lowering and determinism
    // =========================================================================

    private static void testOneProjectLoweringAndDeterminism() throws Exception {
        System.out.println("-- the one project lowering: closure, entry, one "
            + "allocator, byte-identical repeats --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            checkEq(List.of(UTIL, APP),
                project.checkedProject().modules().stream()
                    .map(CheckedModuleInput::moduleId).toList(),
                "the checked closure carries the implementation modules in "
                    + "dependency order");

            SemanticLowerer.ProjectLoweringResult first = lower(project, invocation());
            SemanticLowerer.ProjectLoweringResult second = lower(project, invocation());
            check(!first.hasErrors() && first.project() != null,
                "the project lowers to exactly one project: " + first.diagnostics());
            check(second.project() != null, "the repeated lowering lowers too");
            if (first.project() == null || second.project() == null) {
                return;
            }
            ExecutableLoweredProject lowered = first.project();
            checkEq(SemanticProfile.DEAL_V1_2_INT32, lowered.semanticProfile(),
                "the project carries the DEAL_V1_2_INT32 profile");
            checkEq(List.of(UTIL, APP), List.copyOf(lowered.modules().keySet()),
                "the project's module insertion order is the dependency order");
            checkEq(APP, lowered.entryModule(), "the entry module is present");
            check(lowered.modules().containsKey(lowered.entryModule()),
                "the entry module is a member of the closure");

            // One table and one registry per module; nothing else escapes.
            checkEq(Set.of(UTIL, APP), first.tables().keySet(),
                "the result carries one block-membership table per module");
            checkEq(Set.of(UTIL, APP), first.registries().keySet(),
                "the result carries one class-factory registry per module");

            // Globally unique ids from one allocator.
            Set<Long> opIds = new LinkedHashSet<>();
            int ops = 0;
            for (LoweredModuleUnit unit : lowered.modules().values()) {
                for (SemanticOp op : unit.ops()) {
                    ops++;
                    check(op.opId().module().equals(unit.moduleId()),
                        "every op id carries its producing module");
                    if (!opIds.add(op.opId().id())) {
                        fail("the op id " + op.opId() + " is issued twice");
                    }
                }
            }
            check(ops > 0 && opIds.size() == ops,
                "the ids are issued once per compilation and globally unique (" + ops
                    + " ops, " + opIds.size() + " distinct ids)");

            // Byte-identical repeated project dumps.
            SemanticIrDumper.ProjectDump firstDump = SemanticIrDumper.dumpProject(lowered);
            SemanticIrDumper.ProjectDump secondDump =
                SemanticIrDumper.dumpProject(second.project());
            check(java.util.Arrays.equals(firstDump.manifest(), secondDump.manifest()),
                "the repeated project manifests are byte-identical");
            check(firstDump.modules().size() == secondDump.modules().size(),
                "both dumps carry every module");
            for (int i = 0; i < firstDump.modules().size(); i++) {
                check(firstDump.modules().get(i).moduleId()
                        .equals(secondDump.modules().get(i).moduleId())
                        && java.util.Arrays.equals(
                            firstDump.modules().get(i).bytes(),
                            secondDump.modules().get(i).bytes()),
                    "the repeated dump of module "
                        + firstDump.modules().get(i).moduleId() + " is byte-identical");
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 2. The seeds, the intrinsic bindings, and the namespace registrations
    // =========================================================================

    private static void testSeedsIntrinsicsAndNamespaces() throws Exception {
        System.out.println("-- the seeds, the intrinsic bindings, and the "
            + "namespace registrations --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            if (result.project() == null) {
                fail("the project lowers: " + result.diagnostics());
                return;
            }
            // The class registration seeds: the compiler-owned builtin
            // Error plus one layout per declared class of every declaration
            // module.
            check(result.seeds() != null, "the result carries the class "
                + "registration seeds");
            if (result.seeds() == null) {
                return;
            }
            ClassLayout errorLayout = result.seeds().registrationFor(BUILTIN_ERROR)
                == null ? null : result.seeds().registrationFor(BUILTIN_ERROR).layout();
            check(errorLayout != null
                    && result.seeds().registrationFor(BUILTIN_ERROR).owner()
                        == DefaultOwner.BUILTIN_DEFAULTS,
                "the seeds carry the compiler-owned builtin Error layout under "
                    + "BUILTIN_DEFAULTS");
            checkEq(2, result.seeds().registrations().size(),
                "the seeds carry exactly one layout per declared class of every "
                    + "declaration module plus the builtin Error entry");
            // The seeds are the layout resolution context, never merged into
            // a unit's own declared layouts.
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                check(unit.classLayouts().isEmpty(),
                    "module " + unit.moduleId() + " carries no seeded layout in its "
                        + "own classLayouts map (the seeds are never merged into it)");
            }
            if (errorLayout != null) {
                checkEq(ClassLayout.BUILTIN_ERROR, errorLayout,
                    "the seeds' builtin Error registration is exactly the "
                        + "compiler-owned ClassLayout.BUILTIN_ERROR constant (the "
                        + "layout is identical in every unit's context)");
                checkEq(List.of("code", "message"),
                    errorLayout.fields().stream().map(ClassLayout.FieldLayout::name)
                        .toList(),
                    "the builtin Error layout carries code/message in declaration "
                        + "order");
                check(errorLayout.fields().stream()
                        .allMatch(field -> field.required()
                            && field.defaultOwner() == DefaultOwner.BUILTIN_DEFAULTS),
                    "both builtin Error fields are required-present under "
                        + "BUILTIN_DEFAULTS");
            }
            ClassLayout endpointLayout = result.seeds().registrationFor(ENDPOINT)
                == null ? null : result.seeds().registrationFor(ENDPOINT).layout();
            check(endpointLayout != null
                    && result.seeds().registrationFor(ENDPOINT).owner()
                        == DefaultOwner.HOST_DEFAULTS,
                "the declared host class carries its layout under HOST_DEFAULTS "
                    + "(the seed proves the declaration identity classification)");
            if (endpointLayout != null) {
                checkEq(List.of("path", "port"),
                    endpointLayout.fields().stream().map(ClassLayout.FieldLayout::name)
                        .toList(),
                    "the declared host class fields keep declaration order");
                check(endpointLayout.fields().get(0).required()
                        && !endpointLayout.fields().get(1).required(),
                    "required-present is the declaration's optional-negation");
            }

            // The closed IntrinsicFunction bindings of both conversion
            // intrinsics, per unit, with their declared signatures.
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                List<FunctionExecutionBinding.IntrinsicFunction> intrinsics =
                    new ArrayList<>();
                for (FunctionExecutionBinding binding
                        : unit.functionBindings().values()) {
                    if (binding
                            instanceof FunctionExecutionBinding.IntrinsicFunction
                            intrinsic) {
                        intrinsics.add(intrinsic);
                    }
                }
                check(intrinsics.size() == 2,
                    "module " + unit.moduleId() + " carries exactly the two closed "
                        + "intrinsic bindings; got " + intrinsics.size());
                Set<IntrinsicKind> kinds = new LinkedHashSet<>();
                for (FunctionExecutionBinding.IntrinsicFunction intrinsic
                        : intrinsics) {
                    kinds.add(intrinsic.kind());
                    check(intrinsic.descriptor()
                            .equals(intrinsic.kind().declaredSignature()),
                        "the intrinsic binding of " + intrinsic.kind()
                            + " carries its pinned declared signature");
                }
                checkEq(Set.of(IntrinsicKind.INT_CONVERT,
                        IntrinsicKind.NUMBER_CONVERT), kinds,
                    "the two conversion intrinsics are registered");
                // The dump carries the registration: the closed shape tag and
                // the alias cells of the module's completions.
                String dump = new String(
                    SemanticIrDumper.dumpModule(unit), StandardCharsets.UTF_8);
                check(dump.contains("intrinsicFunction"),
                    "the dump of module " + unit.moduleId()
                        + " records the closed intrinsicFunction binding shape");
                if (unit.ops().stream().anyMatch(op ->
                        op.kind() == SemanticOpKind.MODULE_IMPORT)) {
                    check(dump.contains("aliasCells"),
                        "the dump of module " + unit.moduleId()
                            + " carries the MODULE_IMPORT aliasCells list");
                }
            }

            // The namespace registrations: exactly one entry per distinct
            // imported module of the closure.
            check(result.namespaces() != null,
                "the result carries the namespace registrations");
            if (result.namespaces() == null) {
                return;
            }
            Map<ModuleId, BindingId> dumpedCells = new LinkedHashMap<>();
            Map<ModuleId, Integer> dumpedCompletions = new LinkedHashMap<>();
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() != SemanticOpKind.MODULE_IMPORT
                            || !(op.payload()
                                instanceof KindPayload.ModuleImportPayload payload)) {
                        continue;
                    }
                    dumpedCompletions.merge(payload.resolvedModule(), 1,
                        Integer::sum);
                    check(payload.aliasCells().size() == 1,
                        "each import completion names its one alias cell; got "
                            + payload.aliasCells());
                    if (payload.aliasCells().size() == 1) {
                        dumpedCells.put(payload.resolvedModule(),
                            payload.aliasCells().get(0));
                    }
                }
            }
            checkEq(Set.of(UTIL, HOST_CFG), result.namespaces().registrations().keySet(),
                "exactly one registration exists per distinct imported module");
            NamespaceRegistration cfg = result.namespaces()
                .registrationFor(HOST_CFG);
            check(cfg != null && cfg.kind() == deal.semantic.ir.ModuleImportKind.HOST,
                "the host import's registration carries the HOST kind");
            if (cfg != null) {
                checkEq(List.of(dumpedCells.get(HOST_CFG)), cfg.aliasCells(),
                    "the entry's alias cells equal the cells its completion names");
            }
            NamespaceRegistration compiledModule = result.namespaces()
                .registrationFor(UTIL);
            check(compiledModule != null
                    && compiledModule.kind()
                        == deal.semantic.ir.ModuleImportKind.COMPILED,
                "the compiled implementation import's registration carries the "
                    + "COMPILED kind");
            if (compiledModule != null) {
                checkEq(List.of(dumpedCells.get(UTIL)), compiledModule.aliasCells(),
                    "the compiled import's cells equal the cells its completion "
                        + "names");
            }
            // The dumped MODULE_IMPORT payload names the same cells.
            List<BindingId> dumpedHostCells = new ArrayList<>();
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.MODULE_IMPORT
                            && op.payload()
                                instanceof KindPayload.ModuleImportPayload payload
                            && payload.resolvedModule().equals(HOST_CFG)) {
                        dumpedHostCells.addAll(payload.aliasCells());
                    }
                }
            }
            checkEq(cfg == null ? List.of("missing") : cfg.aliasCells(),
                dumpedHostCells,
                "the dumped MODULE_IMPORT payloads carry the registered cells");
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 3. The composed chain over the unified units
    // =========================================================================

    private static void testComposedChainOverUnifiedUnits() throws Exception {
        System.out.println("-- the composed chain accepts the E7-armed unified "
            + "units --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            if (result.project() == null) {
                fail("the project lowers: " + result.diagnostics());
                return;
            }
            SemanticIrValidator.ComparisonFacts facts =
                new SemanticIrValidator.ComparisonFacts(
                    project.index().interfaceIndexDigest(),
                    SemanticProfile.DEAL_V1_2_INT32,
                    invocation().capabilityRegistryHash());
            check(SemanticIrValidator.validate(result.project(), facts).isEmpty(),
                "the project passes the project-form closed gate");
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                StructuredBodyTable table = result.tableOf(unit.moduleId());
                check(table != null, "the module's produced table is carried");
                check(SemanticIrValidator.validate(unit, facts).isEmpty(),
                    "module " + unit.moduleId() + " passes the closed 14 rules");
                check(AddressChainProtocol.validate(unit).isEmpty(),
                    "module " + unit.moduleId()
                        + " passes the address-chain protocol");
                check(deal.semantic.ControlFlowValidator.validate(unit, table)
                        .isEmpty(),
                    "module " + unit.moduleId() + " passes the control-flow "
                        + "validator");
                check(deal.semantic.ClassConstructionValidator.validate(unit,
                        table, result.registryOf(unit.moduleId()),
                        new JsonDefaultChildTable(Map.of()),
                        project.index().modules().get(unit.moduleId()),
                        Map.of()).isEmpty(),
                    "module " + unit.moduleId() + " passes the class-construction "
                        + "validator");
                // The unified session really carried the E7 arms: the
                // cross-module call produced the caller's EXTERNAL_ENTRY
                // reference and the callee's entry.
                if (unit.moduleId().equals(APP)) {
                    check(unit.ops().stream().anyMatch(op ->
                            op.kind() == SemanticOpKind.CALL
                                && op.payload() instanceof KindPayload.CallPayload
                                    call && call.externalEntryRef() != null),
                        "the entry module's cross-module call carries its "
                            + "externalEntryRef");
                }
                if (unit.moduleId().equals(UTIL)) {
                    check(unit.ops().stream().anyMatch(op ->
                            op.kind() == SemanticOpKind.EXTERNAL_ENTRY),
                        "the callee module records its EXTERNAL_ENTRY");
                    // The recursive-group arm is active in the same session:
                    // exactly one RECURSIVE_GROUP_INIT with both members.
                    List<SemanticOp> groups = new ArrayList<>();
                    for (SemanticOp op : unit.ops()) {
                        if (op.kind() == SemanticOpKind.RECURSIVE_GROUP_INIT) {
                            groups.add(op);
                        }
                    }
                    check(groups.size() == 1,
                        "the unified session produced exactly one "
                            + "RECURSIVE_GROUP_INIT; got " + groups.size());
                    if (groups.size() == 1
                            && groups.get(0).payload()
                                instanceof KindPayload.RecursiveGroupInitPayload group) {
                        checkEq(2, group.functions().size(),
                            "the group op publishes both members");
                    }
                }
                if (unit.moduleId().equals(APP)) {
                    // The adapter arm is active in the same session.
                    check(unit.ops().stream().anyMatch(op ->
                            op.kind() == SemanticOpKind.FUNCTION_ADAPT),
                        "the unified session produced the adapter");
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 4. The unified walk's class arm (in-project classes)
    // =========================================================================

    private static void testInProjectClassArm() throws Exception {
        System.out.println("-- the unified walk's class arm: an in-project class "
            + "declared and constructed in one session --");
        RealProject project = compileProject(CLASS_APP_SOURCE,
            Map.of("src/util.deal", CLASS_UTIL_SOURCE), Map.of());
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            check(!result.hasErrors() && result.project() != null,
                "the class-declaring project lowers through the composed chain: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit util = result.project().modules().get(UTIL);
            check(util != null, "the class-declaring module is in the closure");
            if (util == null) {
                return;
            }
            // The class-declaration arm produced the unit's own layouts (the
            // exported class and the local one); the seeds stay out of them.
            ClassLayout pointLayout = util.classLayouts().get(POINT);
            ClassLayout hiddenLayout = util.classLayouts().get(HIDDEN);
            check(pointLayout != null && hiddenLayout != null,
                "the unified walk produced the unit's own classLayouts entries: "
                    + util.classLayouts().keySet());
            check(!util.classLayouts().containsKey(ENDPOINT)
                    && !util.classLayouts().containsKey(BUILTIN_ERROR),
                "the class registration seeds stay out of the unit's own "
                    + "classLayouts map");
            if (pointLayout == null || hiddenLayout == null) {
                return;
            }
            checkEq(List.of("x", "y"),
                pointLayout.fields().stream().map(ClassLayout.FieldLayout::name)
                    .toList(),
                "the exported class layout carries its fields in declaration order");
            check(pointLayout.fields().stream().allMatch(field -> field.required()
                    && field.defaultOwner() == DefaultOwner.LOCAL),
                "the in-project class fields carry the LOCAL owner member");
            checkEq(List.of("label"),
                hiddenLayout.fields().stream().map(ClassLayout.FieldLayout::name)
                    .toList(),
                "the local class layout carries its field in declaration order");

            // The class-literal arm in the same session: one LOCAL CLASS_NEW
            // per construction, with the provided field as a literal boundary
            // and the omitted defaulted field as a default boundary.
            List<SemanticOp> constructions = new ArrayList<>();
            for (SemanticOp op : util.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW) {
                    constructions.add(op);
                }
            }
            checkEq(2, constructions.size(),
                "the unified walk produced one CLASS_NEW per class literal");
            boolean sawPoint = false;
            boolean sawHidden = false;
            for (SemanticOp op : constructions) {
                KindPayload.ClassNewPayload payload =
                    (KindPayload.ClassNewPayload) op.payload();
                check(payload.defaultOwner() == DefaultOwner.LOCAL
                        && payload.classFactoryRef() == null,
                    "the same-module literal carries LOCAL with no factory ref");
                if (payload.classId().equals(POINT)) {
                    sawPoint = true;
                    checkEq(pointLayout, payload.layout(),
                        "the exported class literal carries the unit's own layout");
                    checkEq(1, payload.classDefaultOpIds().size(),
                        "the omitted defaulted y field lists its CLASS_DEFAULT child");
                    checkEq(List.of("x", "y"),
                        payload.fieldBoundaries().stream()
                            .map(KindPayload.FieldBoundary::field).toList(),
                        "the construction boundaries run in declaration order");
                    check(payload.fieldBoundaries().get(0).kind()
                            == BoundaryKind.CLASS_LITERAL_FIELD
                            && payload.fieldBoundaries().get(1).kind()
                                == BoundaryKind.CLASS_DEFAULT_FIELD,
                        "the provided field is a literal boundary and the omitted "
                            + "defaulted field a default boundary");
                }
                if (payload.classId().equals(HIDDEN)) {
                    sawHidden = true;
                    checkEq(hiddenLayout, payload.layout(),
                        "the local class literal carries the unit's own layout");
                    check(payload.classDefaultOpIds().isEmpty()
                            && payload.fieldBoundaries().size() == 1
                            && payload.fieldBoundaries().get(0).kind()
                                == BoundaryKind.CLASS_LITERAL_FIELD,
                        "the fully provided local literal carries no default child");
                }
            }
            check(sawPoint && sawHidden,
                "both the exported and the local class literal lowered CLASS_NEW");

            // The exported variant's CLASS_FACTORY registration; the local
            // class never gets one.
            ExternalModuleInterface utilInterface =
                project.index().modules().get(UTIL);
            ClassInterface pointInterface = null;
            if (utilInterface != null) {
                for (ClassInterface candidate : utilInterface.classes()) {
                    if (candidate.classId().equals(POINT)) {
                        pointInterface = candidate;
                    }
                }
            }
            check(pointInterface != null,
                "the exported class carries its interface entry");
            ClassFactoryRegistry produced = result.registryOf(UTIL);
            check(produced != null,
                "the class-declaring module carries its class-factory registry");
            ClassFactoryRegistry registry = produced == null
                ? new ClassFactoryRegistry(Map.of()) : produced;
            if (pointInterface != null) {
                ClassFactoryId entry = pointInterface.constructionEntry();
                OpId factoryOpId = registry.factoryFor(entry);
                check(factoryOpId != null,
                    "the exported class's CLASS_FACTORY is registered under its "
                        + "constructionEntry");
                SemanticOp factory = null;
                for (SemanticOp op : util.ops()) {
                    if (op.opId().equals(factoryOpId)) {
                        factory = op;
                    }
                }
                check(factory != null
                        && factory.kind() == SemanticOpKind.CLASS_FACTORY
                        && factory.payload()
                            instanceof KindPayload.ClassFactoryPayload factoryPayload
                        && factoryPayload.classId().equals(POINT),
                    "the registered id names the exported class's CLASS_FACTORY op");
            }
            boolean hiddenFactory = false;
            for (SemanticOp op : util.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_FACTORY
                        && op.payload()
                            instanceof KindPayload.ClassFactoryPayload factory
                        && factory.classId().equals(HIDDEN)) {
                    hiddenFactory = true;
                }
            }
            check(!hiddenFactory,
                "the local class never gets a CLASS_FACTORY (a non-exported "
                    + "class carries no factory id)");

            // The composed chain re-runs over the class-carrying unit.
            SemanticIrValidator.ComparisonFacts facts =
                new SemanticIrValidator.ComparisonFacts(
                    project.index().interfaceIndexDigest(),
                    SemanticProfile.DEAL_V1_2_INT32,
                    invocation().capabilityRegistryHash());
            check(SemanticIrValidator.validate(util, facts).isEmpty(),
                "the class-carrying unit passes the closed 14 rules");
            check(AddressChainProtocol.validate(util).isEmpty(),
                "the class-carrying unit passes the address-chain protocol");
            check(deal.semantic.ControlFlowValidator.validate(util,
                    result.tableOf(UTIL)).isEmpty(),
                "the class-carrying unit passes the control-flow validator");
            check(ClassConstructionValidator.validate(util, result.tableOf(UTIL),
                    registry, new JsonDefaultChildTable(Map.of()), utilInterface,
                    Map.of()).isEmpty(),
                "the class-carrying unit passes the class-construction validator "
                    + "(the composed chain's class arm)");
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 4b. In-project imported-class resolution (ISSUE-0636)
    // =========================================================================

    private static void testImportedInProjectClassResolution() throws Exception {
        System.out.println("-- the in-project imported-class construction: "
            + "CLASS_NEW(SHARED_FACTORY) with the owner's factory reference --");
        RealProject project = compileProject(IMPORTED_CLASS_APP_SOURCE,
            Map.of("src/util.deal", IMPORTED_CLASS_UTIL_SOURCE), Map.of());
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            check(!result.hasErrors() && result.project() != null,
                "the imported in-project class literal lowers through the one "
                    + "project entry: " + result.diagnostics());
            boolean retainedAbiDeferred = false;
            for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                if (diagnostic.message().contains("RETAINED_ABI_DEFERRED")) {
                    retainedAbiDeferred = true;
                }
            }
            check(!retainedAbiDeferred,
                "the checker-valid in-project input reports zero "
                    + "RETAINED_ABI_DEFERRED");
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit util = result.project().modules().get(UTIL);
            LoweredModuleUnit app = result.project().modules().get(APP);
            check(util != null && app != null,
                "both the owner and the dependent module are in the closure");
            if (util == null || app == null) {
                return;
            }
            // The in-project records of the owner: the interface entry from
            // the project index, the owner unit's layout, the owner
            // registry's factory op id for the interface constructionEntry,
            // and the factory op's result ValueId.
            ExternalModuleInterface utilInterface = project.index().modules().get(UTIL);
            ClassInterface pointEntry = null;
            if (utilInterface != null) {
                for (ClassInterface candidate : utilInterface.classes()) {
                    if (candidate.classId().equals(POINT)) {
                        pointEntry = candidate;
                    }
                }
            }
            ClassLayout ownerLayout = util.classLayouts().get(POINT);
            ClassFactoryRegistry ownerRegistry = result.registryOf(UTIL);
            check(pointEntry != null && ownerLayout != null && ownerRegistry != null,
                "the owner's interface entry, layout, and registry resolve");
            if (pointEntry == null || ownerLayout == null || ownerRegistry == null) {
                return;
            }
            OpId factoryOpId = ownerRegistry.factoryFor(pointEntry.constructionEntry());
            SemanticOp factoryOp = factoryOpId == null ? null : opOf(util, factoryOpId);
            check(factoryOpId != null && factoryOp != null
                    && factoryOp.kind() == SemanticOpKind.CLASS_FACTORY
                    && factoryOp.result() instanceof ValueId,
                "the owner's CLASS_FACTORY is registered under the interface "
                    + "constructionEntry with a result value");
            if (factoryOpId == null || factoryOp == null
                    || !(factoryOp.result() instanceof ValueId factoryResult)) {
                return;
            }
            SharedFactoryFacts facts = new SharedFactoryFacts(POINT, pointEntry,
                ownerLayout, factoryOpId, factoryResult);

            // The dependent module's imported literals: one CLASS_NEW per
            // constructed imported class, each with defaultOwner
            // SHARED_FACTORY, the owner's constructionEntry as the factory
            // reference, an empty CLASS_DEFAULT child list, the provided
            // fields, and the declaration-order boundary list.
            Map<ClassId, KindPayload.ClassNewPayload> constructions =
                new LinkedHashMap<>();
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW
                        && op.payload() instanceof KindPayload.ClassNewPayload candidate) {
                    constructions.put(candidate.classId(), candidate);
                }
            }
            checkEq(Set.of(POINT, SEGMENT), constructions.keySet(),
                "the dependent module lowers one CLASS_NEW per constructed imported "
                    + "in-project class");
            KindPayload.ClassNewPayload payload = constructions.get(POINT);
            check(payload != null, "the imported Point literal lowered CLASS_NEW");
            if (payload == null) {
                return;
            }
            checkEq(DefaultOwner.SHARED_FACTORY, payload.defaultOwner(),
                "the imported literal carries defaultOwner SHARED_FACTORY");
            checkEq(facts.interfaceEntry().constructionEntry(),
                payload.classFactoryRef(),
                "the literal carries the owner's interface constructionEntry as its "
                    + "factory reference");
            check(payload.classDefaultOpIds().isEmpty(),
                "the SHARED_FACTORY literal carries an empty classDefaultOpIds list "
                    + "(the defaults transfer to the owner's factory)");
            checkEq(ownerLayout, payload.layout(),
                "the payload layout is the owner unit's layout, resolved through the "
                    + "in-project interface facts");
            checkEq(List.of("x"), payload.providedFields().stream()
                    .map(KindPayload.ProvidedField::name).toList(),
                "the provided fields stay in literal order");
            checkEq(List.of("x", "y"), payload.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the field boundaries run in declaration order");
            checkEq(List.of(BoundaryKind.CLASS_LITERAL_FIELD,
                    BoundaryKind.CLASS_DEFAULT_FIELD),
                payload.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::kind).toList(),
                "the provided field is a literal boundary and the omitted defaulted "
                    + "field a default boundary");
            SemanticOp defaultBoundary = opOf(app,
                payload.fieldBoundaries().get(1).boundaryOpId());
            check(defaultBoundary != null
                    && defaultBoundary.payload()
                        instanceof KindPayload.BoundaryPayload boundary
                    && boundary.input().equals(facts.factoryResult()),
                "the omitted defaulted field's boundary wires the owner factory op's "
                    + "result ValueId (the in-project factory reference)");

            // Repeats are deterministic: the same accumulation and walk
            // produce the byte-identical dependent unit.
            SemanticLowerer.ProjectLoweringResult repeat = lower(project, invocation());
            check(repeat.project() != null
                    && java.util.Arrays.equals(
                        SemanticIrDumper.dumpModule(app),
                        SemanticIrDumper.dumpModule(
                            repeat.project().modules().get(APP))),
                "the repeated lowering of the imported in-project class project is "
                    + "byte-identical");

            // Every exported class of the lowered owner accumulates its own
            // fact (the loop, not one fixture class): the second class
            // constructs SHARED_FACTORY with its own constructionEntry and
            // its own owner layout.
            ClassInterface segmentEntry = null;
            if (utilInterface != null) {
                for (ClassInterface candidate : utilInterface.classes()) {
                    if (candidate.classId().equals(SEGMENT)) {
                        segmentEntry = candidate;
                    }
                }
            }
            ClassLayout segmentLayout = util.classLayouts().get(SEGMENT);
            OpId segmentFactoryOpId = segmentEntry == null ? null
                : ownerRegistry.factoryFor(segmentEntry.constructionEntry());
            SemanticOp segmentFactoryOp = segmentFactoryOpId == null ? null
                : opOf(util, segmentFactoryOpId);
            KindPayload.ClassNewPayload segment = constructions.get(SEGMENT);
            check(segment != null && segmentEntry != null && segmentLayout != null
                    && segment.defaultOwner() == DefaultOwner.SHARED_FACTORY
                    && segment.classFactoryRef().equals(
                        segmentEntry.constructionEntry())
                    && segment.classDefaultOpIds().isEmpty()
                    && segment.layout().equals(segmentLayout)
                    && segmentFactoryOp != null
                    && segmentFactoryOp.kind() == SemanticOpKind.CLASS_FACTORY,
                "every exported class of the lowered owner accumulates its own fact "
                    + "(the second class constructs SHARED_FACTORY with its own "
                    + "constructionEntry and layout)");

            // The composed chain re-runs over the dependent unit with the
            // in-project facts of both classes (the class-construction arm's
            // imported path).
            Map<ClassId, SharedFactoryFacts> inProjectFacts = new LinkedHashMap<>();
            inProjectFacts.put(POINT, facts);
            if (segmentEntry != null && segmentLayout != null
                    && segmentFactoryOpId != null && segmentFactoryOp != null
                    && segmentFactoryOp.result() instanceof ValueId segmentResult) {
                inProjectFacts.put(SEGMENT, new SharedFactoryFacts(SEGMENT,
                    segmentEntry, segmentLayout, segmentFactoryOpId, segmentResult));
            }
            check(ClassConstructionValidator.validate(app, result.tableOf(APP),
                    result.registryOf(APP), new JsonDefaultChildTable(Map.of()),
                    project.index().modules().get(APP),
                    inProjectFacts).isEmpty(),
                "the dependent unit passes the class-construction validator with the "
                    + "in-project facts");

            // The combined behavior: the dependent module's cross-module call
            // resolves through the accumulated EXTERNAL_ENTRY records.
            KindPayload.CallPayload externalCall = null;
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.CALL
                        && op.payload() instanceof KindPayload.CallPayload call
                        && call.callee()
                            instanceof KindPayload.CallCallee.Static staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.ExternalFunction external
                        && external.moduleId().equals(UTIL)) {
                    externalCall = call;
                    check(external.executionOwner()
                            == deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY,
                        "the cross-module callee is a SHARED_BODY external (no "
                            + "retained-ABI owner enters the project lowering)");
                }
            }
            check(externalCall != null,
                "the dependent module's cross-module call carries the in-project "
                    + "external binding");
            if (externalCall != null) {
                OpId entryRef = externalCall.externalEntryRef();
                SemanticOp entry = entryRef == null ? null : opOf(util, entryRef);
                check(entry != null
                        && entry.kind() == SemanticOpKind.EXTERNAL_ENTRY
                        && entry.payload()
                            instanceof KindPayload.ExternalEntryPayload entryPayload
                        && entryPayload.exportName().equals("makePoint"),
                    "the call's externalEntryRef names the owner's recorded "
                        + "EXTERNAL_ENTRY (the accumulated in-project record)");
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testInconsistentFactSeed() throws Exception {
        System.out.println("-- the inconsistent-fact negative: an owner outside the "
            + "closure and outside the declaration set still defers --");
        RealProject project = compileProject(IMPORTED_CLASS_APP_SOURCE,
            Map.of("src/util.deal", IMPORTED_CLASS_UTIL_SOURCE), Map.of());
        try {
            // The same real project with the owner module removed from the
            // closure and the index: the checker-resolved class identity
            // stays, but no lowered implementation module, no declaration
            // surface entry, and no registration seed covers it — the
            // inconsistent-fact case the deferral remains for.
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
            check(result.hasErrors() && result.project() == null,
                "the inconsistent-fact seed produces no project: "
                    + result.diagnostics());
            check(result.tables().isEmpty() && result.registries().isEmpty()
                    && result.seeds() == null && result.namespaces() == null,
                "the inconsistent-fact seed produces no tables, no registries, no "
                    + "seeds, and no registrations");
            if (!result.diagnostics().isEmpty()) {
                CompilerDiagnostic diagnostic = result.diagnostics().get(0);
                check("E6005".equals(diagnostic.code())
                        && diagnostic.message().contains("RETAINED_ABI_DEFERRED"),
                    "the inconsistent-fact seed returns the first E6005 "
                        + "RETAINED_ABI_DEFERRED; got " + diagnostic.message());
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 5. The declaration-class construction acceptance
    // =========================================================================

    /**
     * The host declaration class construction (ISSUE-0624;
     * {@code semantic-ir-construct-coverage-cutover} K10): the literal
     * resolves to the seed and lowers the {@code HOST_DEFAULTS} shape through
     * the one project entry with zero diagnostics — the retargeted pin of the
     * pre-slice fail-closed acceptance.
     */
    private static void testDeclarationClassConstruction() throws Exception {
        System.out.println("-- a host declaration class literal resolves to the "
            + "seed and lowers CLASS_NEW(HOST_DEFAULTS) through the one project "
            + "entry --");
        RealProject project = compileProject(HOST_CLASS_APP_SOURCE, Map.of(),
            Map.of());
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            check(!result.hasErrors() && result.project() != null,
                "the host declaration class literal lowers through the one project "
                    + "entry with zero diagnostics: " + result.diagnostics());
            boolean deferred = false;
            for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                if (diagnostic.message().contains("RETAINED_ABI_DEFERRED")) {
                    deferred = true;
                }
            }
            check(!deferred,
                "checker-valid host-class input reports zero RETAINED_ABI_DEFERRED");
            if (result.project() == null) {
                return;
            }
            check(result.seeds().registrationFor(ENDPOINT) != null
                    && result.seeds().registrationFor(ENDPOINT).owner()
                        == DefaultOwner.HOST_DEFAULTS,
                "the declared host class resolves in the seeds under HOST_DEFAULTS");
            LoweredModuleUnit app = result.project().modules().get(APP);
            check(app != null, "the app unit is in the closure");
            if (app == null) {
                return;
            }
            SemanticOp classNew = null;
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW) {
                    classNew = op;
                }
            }
            check(classNew != null, "the unit carries the host CLASS_NEW");
            if (classNew == null) {
                return;
            }
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) classNew.payload();
            checkEq(ENDPOINT, payload.classId(),
                "the CLASS_NEW classId is the declared host class identity");
            checkEq(DefaultOwner.HOST_DEFAULTS, payload.defaultOwner(),
                "the CLASS_NEW defaultOwner is HOST_DEFAULTS");
            check(payload.classFactoryRef() == null,
                "the host construction carries the null factory ref");
            check(payload.classDefaultOpIds().isEmpty(),
                "the host construction carries empty classDefaultOpIds");
            checkEq(result.seeds().registrationFor(ENDPOINT).layout(),
                payload.layout(),
                "the payload's layout is the registered declaration layout");
            checkEq(List.of("path"),
                payload.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the field boundaries are the provided fields in literal order");
            check(payload.fieldBoundaries().stream().allMatch(entry ->
                    entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD),
                "every field boundary is a CLASS_LITERAL_FIELD (the loaded "
                    + "defaults are data, never in-project default expressions)");
            check(!payload.layout().fields().isEmpty()
                    && payload.layout().fields().stream().allMatch(field ->
                        field.defaultOwner() == DefaultOwner.HOST_DEFAULTS),
                "the registered declaration layout carries the HOST_DEFAULTS "
                    + "field owner");

            // The composed per-unit chain re-run with the seeds: the unified
            // unit passes every validator (the class arm included).
            Optional<CompilerDiagnostic> failure =
                SemanticLowerer.validateProjectUnit(app, result.tableOf(APP),
                    new SemanticIrValidator.ComparisonFacts(
                        project.index().interfaceIndexDigest(),
                        SemanticProfile.DEAL_V1_2_INT32,
                        invocation().capabilityRegistryHash()),
                    deal.semantic.BindingsProductionValidator.PinnedWriteFacts
                        .empty(),
                    result.registryOf(APP),
                    new JsonDefaultChildTable(Map.of()),
                    project.index().modules().get(APP), Map.of(),
                    result.seeds().registrations());
            check(failure.isEmpty(),
                "the composed chain accepts the host construction unit: "
                    + failure.map(CompilerDiagnostic::message).orElse(""));
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testBuiltinErrorConstruction() throws Exception {
        System.out.println("-- a builtin Error literal constructs through the one "
            + "project entry: CLASS_NEW(BUILTIN_DEFAULTS) over the compiler-owned "
            + "layout --");
        RealProject project = compileProject(ERROR_APP_SOURCE, Map.of(), Map.of());
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            check(!result.hasErrors() && result.project() != null,
                "the builtin Error literal lowers through the one project entry "
                    + "with zero diagnostics: " + result.diagnostics());
            boolean deferred = false;
            for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                if (diagnostic.message().contains("RETAINED_ABI_DEFERRED")) {
                    deferred = true;
                }
            }
            check(!deferred,
                "checker-valid builtin Error input reports zero "
                    + "RETAINED_ABI_DEFERRED");
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            check(app != null, "the app unit is in the closure");
            if (app == null) {
                return;
            }
            SemanticOp classNew = null;
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW) {
                    classNew = op;
                }
            }
            check(classNew != null, "the unit carries the Error CLASS_NEW");
            if (classNew == null) {
                return;
            }
            checkEq(ClassId.ERROR, ((KindPayload.ClassNewPayload) classNew.payload())
                    .classId(), "the CLASS_NEW classId is the builtin @/Error");
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) classNew.payload();
            checkEq(DefaultOwner.BUILTIN_DEFAULTS, payload.defaultOwner(),
                "the CLASS_NEW defaultOwner is BUILTIN_DEFAULTS");
            check(payload.classFactoryRef() == null,
                "the builtin Error construction carries the null factory ref");
            check(payload.classDefaultOpIds().isEmpty(),
                "the builtin Error construction carries empty classDefaultOpIds");
            checkEq(ClassLayout.BUILTIN_ERROR, payload.layout(),
                "the payload's layout is the compiler-owned builtin Error layout");
            checkEq(List.of("code", "message"),
                payload.providedFields().stream()
                    .map(KindPayload.ProvidedField::name).toList(),
                "the provided fields keep literal order (code, message)");
            checkEq(List.of("code", "message"),
                payload.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the field boundaries are the declared order (code, message)");
            check(payload.fieldBoundaries().stream().allMatch(entry ->
                    entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD),
                "every field boundary is a CLASS_LITERAL_FIELD (no "
                    + "CLASS_DEFAULT_FIELD: the builtin defaults are compiler "
                    + "constants)");

            // The composed per-unit chain re-run: the unified unit passes
            // every validator with the project's own factory records and the
            // in-project facts (the class arm included).
            Optional<CompilerDiagnostic> failure =
                SemanticLowerer.validateProjectUnit(app, result.tableOf(APP),
                    new SemanticIrValidator.ComparisonFacts(
                        project.index().interfaceIndexDigest(),
                        SemanticProfile.DEAL_V1_2_INT32,
                        invocation().capabilityRegistryHash()),
                    deal.semantic.BindingsProductionValidator.PinnedWriteFacts
                        .empty(),
                    result.registryOf(APP),
                    new JsonDefaultChildTable(Map.of()),
                    project.index().modules().get(APP), Map.of());
            check(failure.isEmpty(),
                "the composed chain accepts the builtin Error unit: "
                    + failure.map(CompilerDiagnostic::message).orElse(""));
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testExternCDeclarationClassFailClosed() throws Exception {
        System.out.println("-- an extern-C declaration class literal resolves to "
            + "the FFI_PLAN seed and fails closed at the class-construction "
            + "validator --");
        RealProject project = compileProject(EXTERN_C_CLASS_APP_SOURCE,
            Map.of("src/native.d.deal", NATIVE_DECLARATION),
            Map.of(NATIVE_SPECIFIER, "src/native.d.deal"));
        try {
            check(project.externCModules().containsKey(NATIVE),
                "the extern-C declaration module carries the real phase-3.9 "
                    + "generated metadata: " + project.externCModules().keySet());
            check(project.surface().moduleIds().contains(NATIVE)
                    && project.surface().require(NATIVE).kind()
                        == HostDeclarationSurface.DeclarationKind.EXTERN_C,
                "the declaration surface classifies the module extern-C: "
                    + project.surface().moduleIds());
            checkFailsClosed(lower(project, invocation()),
                "the extern-C declaration class literal", NATIVE_VEC2.text());
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void assertFailsClosed(String appSource,
            Map<String, String> extraSources, Map<String, String> extraExternals,
            String what, String expectedClassText) throws Exception {
        RealProject project = compileProject(appSource, extraSources, extraExternals);
        try {
            checkFailsClosed(lower(project, invocation()), what, expectedClassText);
        } finally {
            deleteRecursively(project.root());
        }
    }

    /**
     * The four fail-closed assertions of a seeded-owner construction (the
     * intended intermediate state): the first E6005 from the
     * class-construction validator, capability {@code CLASSES}, naming the
     * seeded class identity, with no project, no tables, no registries, no
     * seeds, and no namespace registrations.
     */
    private static void checkFailsClosed(SemanticLowerer.ProjectLoweringResult result,
            String what, String expectedClassText) {
        check(result.hasErrors() && result.project() == null,
            what + " fails closed with no project: " + result.diagnostics());
        check(result.tables().isEmpty() && result.registries().isEmpty()
                && result.seeds() == null && result.namespaces() == null,
            what + " fails closed with no tables, no registries, no seeds, and "
                + "no registrations");
        if (result.diagnostics().isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = result.diagnostics().get(0);
        check("E6005".equals(diagnostic.code()),
            what + " fails with E6005; got " + diagnostic.code());
        check(diagnostic.message().contains(
                ClassConstructionValidator.CONSTRUCTION_COHERENCE),
            what + " fails at the class-construction validator; got "
                + diagnostic.message());
        check(diagnostic.message().contains("capability CLASSES"),
            what + " carries capability CLASSES; got " + diagnostic.message());
        if (expectedClassText != null) {
            check(diagnostic.message().contains(expectedClassText),
                what + " names the seeded class identity " + expectedClassText
                    + " (the seed lookup resolved it); got "
                    + diagnostic.message());
        }
    }

    // =========================================================================
    // 6. The negative seeds
    // =========================================================================

    private static void testCorruptedUnitSeed() throws Exception {
        System.out.println("-- the corrupted-unit negative: a wrong boundary "
            + "triple fails the unit chain --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            if (result.project() == null) {
                fail("the project lowers: " + result.diagnostics());
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            LoweredModuleUnit corrupted = corruptReturnBoundary(app);
            check(corrupted != null, "the corrupted unit is built (a RETURN names "
                + "an unknown return boundary)");
            if (corrupted == null) {
                return;
            }
            Optional<CompilerDiagnostic> failure =
                SemanticLowerer.validateProjectUnit(corrupted,
                    result.tableOf(APP),
                    new SemanticIrValidator.ComparisonFacts(
                        project.index().interfaceIndexDigest(),
                        SemanticProfile.DEAL_V1_2_INT32,
                        invocation().capabilityRegistryHash()),
                    deal.semantic.BindingsProductionValidator.PinnedWriteFacts
                        .empty(),
                    new ClassFactoryRegistry(Map.of()),
                    new JsonDefaultChildTable(Map.of()),
                    project.index().modules().get(APP), Map.of());
            check(failure.isPresent(),
                "the corrupted unit fails the composed chain");
            if (failure.isEmpty()) {
                return;
            }
            check("E6005".equals(failure.get().code())
                    && failure.get().message().contains(
                        SemanticIrValidator.R_BOUNDARY_TRIPLE),
                "the corrupted unit returns the first E6005 R-BOUNDARY-TRIPLE; got "
                    + failure.get().message());
        } finally {
            deleteRecursively(project.root());
        }
    }

    /**
     * Rebuilds a lowered unit with the {@code RETURN}'s return boundary op
     * dropped from the produced op list — the dangling return identity of
     * the corrupted-unit negative (a hand-built closed-rule violation; the
     * op payloads stay untouched, so the op contract digests stay valid and
     * the closed gate is the rejecting member).
     */
    private static LoweredModuleUnit corruptReturnBoundary(LoweredModuleUnit unit) {
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload payload) {
                List<SemanticOp> corrupted = new ArrayList<>();
                boolean dropped = false;
                for (SemanticOp candidate : ops) {
                    if (!dropped
                            && candidate.opId().equals(payload.returnBoundaryOpId())) {
                        dropped = true;
                        continue;
                    }
                    corrupted.add(candidate);
                }
                if (!dropped) {
                    return null;
                }
                return withOps(unit, corrupted);
            }
        }
        return null;
    }

    /** One lowered unit with the given op list (the corruption surface). */
    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
                                             List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    private static void testMissingModuleSeed() throws Exception {
        System.out.println("-- the missing-module negative: a reference outside "
            + "the closure fails the project-form R-EXTERNAL-ENTRY arm --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project, invocation());
            if (result.project() == null) {
                fail("the project lowers: " + result.diagnostics());
                return;
            }
            Map<ModuleId, LoweredModuleUnit> shortened = new LinkedHashMap<>();
            for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                    : result.project().modules().entrySet()) {
                if (!entry.getKey().equals(UTIL)) {
                    shortened.put(entry.getKey(), entry.getValue());
                }
            }
            ExecutableLoweredProject missing = new ExecutableLoweredProject(
                SemanticProfile.DEAL_V1_2_INT32, project.index(), shortened, APP);
            Optional<CompilerDiagnostic> failure = SemanticIrValidator.validate(
                missing, new SemanticIrValidator.ComparisonFacts(
                    project.index().interfaceIndexDigest(),
                    SemanticProfile.DEAL_V1_2_INT32,
                    invocation().capabilityRegistryHash()));
            check(failure.isPresent(),
                "the project with the missing callee module fails the project-form "
                    + "gate");
            if (failure.isEmpty()) {
                return;
            }
            check("E6005".equals(failure.get().code())
                    && failure.get().message().contains(
                        SemanticIrValidator.R_EXTERNAL_ENTRY)
                    && failure.get().message().contains("outside the implementation "
                        + "closure"),
                "the missing module returns the first E6005 R-EXTERNAL-ENTRY naming "
                    + "the closure violation; got " + failure.get().message());
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testNonV12InvocationSeed() throws Exception {
        System.out.println("-- the non-v1.2 invocation negative: the profile "
            + "guard fires before any id is allocated --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            CompilerInvocation legacy = CompilerProfileProvider.resolveLegacyRegression(
                SemanticProfile.LEGACY_SAFE_INT, ReleaseState.V1_2_ACTIVE,
                CapabilityRegistry.releaseRegistry());
            CheckedProjectInput legacyProject = new CheckedProjectInput(legacy,
                project.checkedProject().entryModule(),
                project.checkedProject().modules(), legacy.releaseStateHash());
            SemanticLowerer.ProjectLoweringResult result =
                SemanticLowerer.lowerProject(legacy, legacyProject, project.index(),
                    project.manifests(), project.surface(),
                    project.declarationIdentities(), project.externCModules(),
                    BuiltinErrorDeclaration.synthesized(
                        project.checkedProject().modules().get(1).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT,
                        IntrinsicKind.NUMBER_CONVERT),
                    Set.of());
            check(result.hasErrors() && result.project() == null,
                "the legacy invocation produces no project");
            check(result.tables().isEmpty() && result.registries().isEmpty()
                    && result.seeds() == null && result.namespaces() == null,
                "the legacy invocation produces no tables, no registries, no "
                    + "seeds, and no registrations");
            if (!result.diagnostics().isEmpty()) {
                CompilerDiagnostic diagnostic = result.diagnostics().get(0);
                check("E6005".equals(diagnostic.code())
                        && diagnostic.message().contains(
                            SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED),
                    "the legacy invocation fails the profile guard with "
                        + "LOWER_LEGACY_PROFILE_REJECTED; got " + diagnostic.message());
                check(diagnostic.message().contains("LEGACY_SAFE_INT"),
                    "the failure names the rejected profile; got "
                        + diagnostic.message());
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testUnresolvedAliasSeed() throws Exception {
        System.out.println("-- the unresolved-alias negative: an alias without a "
            + "resolved import fact fails the import arm --");
        RealProject project = compileProject(APP_SOURCE);
        try {
            List<CheckedModuleInput> modules = new ArrayList<>();
            for (CheckedModuleInput module : project.checkedProject().modules()) {
                modules.add(module.moduleId().equals(APP)
                    ? new CheckedModuleInput(module.moduleId(), module.sourceId(),
                        module.sourcePath(), module.ast(), module.checks(),
                        List.of(), module.exports(), module.kind())
                    : module);
            }
            CompilerInvocation invocation = invocation();
            CheckedProjectInput stripped = new CheckedProjectInput(invocation,
                project.checkedProject().entryModule(), modules,
                invocation.releaseStateHash());
            SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
                invocation, stripped, project.index(), project.manifests(),
                project.surface(), project.declarationIdentities(),
                project.externCModules(),
                BuiltinErrorDeclaration.synthesized(
                    project.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                Set.of());
            check(result.hasErrors() && result.project() == null,
                "the unresolved alias produces no project");
            check(result.tables().isEmpty() && result.registries().isEmpty()
                    && result.seeds() == null && result.namespaces() == null,
                "the unresolved alias produces no tables, no registries, no seeds, "
                    + "and no registrations");
            if (!result.diagnostics().isEmpty()) {
                CompilerDiagnostic diagnostic = result.diagnostics().get(0);
                check("E6005".equals(diagnostic.code())
                        && diagnostic.message().contains(
                            SemanticLowerer.CONSTRUCT_UNLOWERED)
                        && diagnostic.message().contains(
                            "without a resolved import fact"),
                    "the unresolved alias fails the import arm with "
                        + "CONSTRUCT_UNLOWERED; got " + diagnostic.message());
            }
        } finally {
            deleteRecursively(project.root());
        }
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
                try (var walk = Files.walk(path)) {
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

    /** The unit's op named by the id, or {@code null}. */
    private static SemanticOp opOf(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    public static void main(String[] args) throws Exception {
        System.out.println("=== Project Lowering Entry Tests (ISSUE-0634) ===\n");
        testOneProjectLoweringAndDeterminism();
        testSeedsIntrinsicsAndNamespaces();
        testComposedChainOverUnifiedUnits();
        testInProjectClassArm();
        testImportedInProjectClassResolution();
        testInconsistentFactSeed();
        testDeclarationClassConstruction();
        testBuiltinErrorConstruction();
        testExternCDeclarationClassFailClosed();
        testCorruptedUnitSeed();
        testMissingModuleSeed();
        testNonV12InvocationSeed();
        testUnresolvedAliasSeed();
        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
