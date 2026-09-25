package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.project.ProjectLocator;
import deal.publication.PublicationStager;
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.ClassConstructionValidator;
import deal.semantic.ClassRegistrationSeeds;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.test.conformance.CorpusFfi;
import deal.test.conformance.SidecarExpectations;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0666: the C-struct construction site and the seed-layout validator
 * admission ({@code
 * luajit-ffi-struct-plan-construction-and-oracle-projection} F1/F2/F3;
 * {@code luajit-ffi-shared-emission-and-jvm-rejection} F6;
 * {@code semantic-ir-construct-coverage-cutover} K9 item 3; sequencing
 * step 5).
 *
 * <ol>
 *   <li>{@code ffi/019-ffi-struct-copy-isolation} constructs
 *       {@code native.Pair} through the loaded plan: the fixture compiles
 *       through the production arm with the corpus's production FFI
 *       metadata and executes under {@code luajit} with the
 *       sidecar-pinned transcript, and the emitted artifact carries the
 *       {@code __rt.class_plan_} call over the export-surface registry's
 *       {@code Pair_plan} entry with the literal's span triplet, the two
 *       {@code CLASS_LITERAL_FIELD} boundary children in declaration
 *       order, the deterministic extra-key guard preceding the entry call,
 *       the wrapper-to-chunk projection, and no {@code CLASS_DEFAULT}
 *       child, no in-project factory, and no ABI conversion text.</li>
 *   <li>the evaluator-once drive: a focused declaration whose struct
 *       fields carry native-counting defaults constructs twice with one
 *       field omitted each time — zero evaluator invocations at load,
 *       exactly one evaluator invocation per omitted field per attempt in
 *       class source order, and a provided field suppressing exactly its
 *       own evaluator — and a failed attempt (the doctored extra-key
 *       payload) invokes no evaluator at all.</li>
 *   <li>the extra-key E8007 drive: a doctored {@code CLASS_NEW(FFI_PLAN)}
 *       payload carrying two provided names absent from the layout fails
 *       with exactly one E8007 naming the first provided-source extra at
 *       the literal origin, and the emitted guard precedes the runtime
 *       entry call (no default runs for the failed attempt).</li>
 *   <li>the validator deviation battery: the composed validator resolves
 *       the extern-C class through the seed-layout input (never merged
 *       into {@code unit.classLayouts()}) and admits exactly the realized
 *       FFI_PLAN shape; the pre-change unresolvable-layout outcome, a
 *       non-seed layout, a non-null factory ref, a non-empty default-op
 *       list, a {@code CLASS_DEFAULT_FIELD} boundary, a missing
 *       provided-field boundary, a wrong boundary order, and the
 *       {@code HOST_DEFAULTS} owner over an extern-C class each fail with
 *       {@code CONSTRUCTION_COHERENCE}.</li>
 *   <li>the JVM arm keeps its fail-closed FFI_PLAN producer defect (no
 *       JVM realization exists: the phase-3.9 E6006 rejection precedes any
 *       lowering of an extern-C closure).</li>
 * </ol>
 */
public class FfiStructConstructionTest {

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
    // The fixtures of this slice
    // =========================================================================

    private static final String CORPUS_FFI_DIR = "test/conformance/backend-runtime/ffi";
    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String NATIVE = "candidate/native";
    private static final String NATIVE_DOTTED = "candidate.native";
    private static final String PAIR_DESC = "@$external/candidate/native/Pair";
    private static final String CORPUS_CASE = "019-ffi-struct-copy-isolation";

    private static final String FOCUSED_SPECIFIER = "ffi/valid";
    private static final String FOCUSED_DOTTED = "ffi.valid";
    private static final String FOCUSED_PROBE_DESC = "@$external/ffi/valid/Probe";

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** One compiled fixture project of the drives. */
    private record Fixture(
        Path root,
        Path sourceRoot,
        String specifier,
        String dotted,
        String appFileName,
        String strippedApp,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        Path outputRoot) {
    }

    /** The corpus FFI fixture project of this slice. */
    private static Fixture compileCorpus() throws Exception {
        String rawFixture = Files.readString(Path.of(CORPUS_FFI_DIR + "/"
            + CORPUS_CASE + ".deal"), StandardCharsets.UTF_8);
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT, NATIVE);
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + NATIVE + "'");
        }
        String declaration = Files.readString(CONFORMANCE_ROOT
            .resolve(CorpusFfi.FFI_DIR).resolve(wiring.declarationCorpusPath()),
            StandardCharsets.UTF_8);
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT, NATIVE,
            SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException(
                "the corpus declaration of '" + NATIVE + "' does not validate: "
                    + module.validationDiagnostics());
        }
        String app = ConformanceHarnessMetadata.stripClassificationHeaders(rawFixture);
        Path root = Files.createTempDirectory("ffi-struct-corpus");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("native.d.deal"),
            ConformanceHarnessMetadata.stripClassificationHeaders(declaration),
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve(CORPUS_CASE + ".deal"), app,
            StandardCharsets.UTF_8);
        Path entry = src.resolve(CORPUS_CASE + ".deal").toAbsolutePath();
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(NATIVE, src.resolve("native.d.deal").toAbsolutePath()
            .toString());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, false, false, false, Backend.LUAJIT,
            externals, List.of(src.toAbsolutePath()), null, null,
            productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null
                || built.index() == null || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the corpus FFI fixture '"
                + CORPUS_CASE + "' did not build: " + detail + " / "
                + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        externCModules.put(new ModuleId(NATIVE_DOTTED), module.generatedModule());
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(NATIVE));
        }
        return new Fixture(root, src, NATIVE, NATIVE_DOTTED,
            CORPUS_CASE + ".deal", app, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            externCModules, identities, root.resolve("out-prod"));
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** One published production artifact. */
    private record Artifact(String name, String text) {
    }

    /** Emits one fixture through the production arm and publishes it. */
    private static Artifact emitAndPublish(Fixture fixture, Path out)
            throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = ProductionProjectEmission.run(productionInvocation(),
                fixture.checkedProject(), fixture.index(), fixture.manifests(),
                fixture.surface(), fixture.declarationIdentities(),
                fixture.externCModules(), fixture.sourceRoot().toString(),
                BuiltinErrorDeclaration.synthesized(
                    fixture.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                Set.of(), Backend.LUAJIT, false,
                DistributionHome.forManifestDirectory(
                    fixture.sourceRoot().toString()),
                stager);
            if (result.emitted()) {
                stager.publish();
            }
        } finally {
            stager.discard();
        }
        if (!result.emitted()) {
            throw new IllegalStateException("the FFI fixture artifact did not emit: "
                + result.diagnostics());
        }
        String name = result.artifactRelativePath();
        return new Artifact(name,
            Files.readString(out.resolve(name), StandardCharsets.UTF_8));
    }

    /** The lowered FFI_PLAN construction of one fixture. */
    private static SemanticOp constructionOf(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.CLASS_NEW
                        && op.payload() instanceof KindPayload.ClassNewPayload payload
                        && payload.defaultOwner() == DefaultOwner.FFI_PLAN) {
                    return op;
                }
            }
        }
        throw new IllegalStateException("the closure carries no"
            + " CLASS_NEW(FFI_PLAN) construction");
    }

    /** The module unit carrying one FFI_PLAN construction. */
    private static LoweredModuleUnit unitOf(ExecutableLoweredProject project,
            SemanticOp construction) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(construction.opId())) {
                    return unit;
                }
            }
        }
        throw new IllegalStateException("the construction's unit is not in the"
            + " closure");
    }

    // =========================================================================
    // 1. The ffi/019 artifact drive
    // =========================================================================

    private static void testCorpusStructConstructionDrive() throws Exception {
        System.out.println("-- ffi/019 constructs native.Pair through the loaded"
            + " plan and executes through the production artifact --");
        Fixture fixture = compileCorpus();
        Path out = fixture.root().resolve("out-prod");
        try {
            Artifact emitted = emitAndPublish(fixture, out);
            String artifact = emitted.text();
            String fileText = fixture.sourceRoot().resolve(fixture.appFileName())
                .toAbsolutePath().toString();
            int literalLine = lineOf(fixture.strippedApp(),
                "let pair: native.Pair");
            int literalColumn = columnOf(fixture.strippedApp(), "{ left: 4");

            // (a) The construction site: the runtime entry over the loaded
            // plan entry with the literal's span triplet. The span triple
            // is relative to the literal's own source coordinates, so read
            // it from the artifact and compare with the source.
            String planCall = "pcall(__rt.class_plan_, \"" + PAIR_DESC
                + "\", __ffiClassPlan(\"" + NATIVE_DOTTED + "\", \"Pair\"), "
                + "__provT, \"" + fileText + "\", " + literalLine + ", "
                + literalColumn + ")";
            check(artifact.contains(planCall),
                "the artifact calls __rt.class_plan_ over the export-surface"
                    + " registry's Pair_plan entry with the literal's span: "
                    + planCall);
            check(artifact.contains("local function __ffiClassPlan(module, class)")
                    && artifact.contains("return surface[class..\"_plan\"]"),
                "the plan reference resolves through the chunk's export-surface"
                    + " registry (never a dotted-path require)");
            int entryCall = artifact.indexOf("pcall(__rt.class_plan_, ");
            check(entryCall > 0, "the entry call is emitted");
            int projection = artifact.indexOf("__hostDealProject(\"" + PAIR_DESC);
            check(projection > entryCall,
                "the projection runs after the runtime entry call");
            String construction = constructionRegion(artifact,
                "pcall(__rt.class_plan_, \"" + PAIR_DESC + "\"");
            check(!construction.isEmpty(),
                "the construction region is emitted: " + construction);
            // (b) The provided fields in declaration order, each with its
            // CLASS_LITERAL_FIELD boundary child before the entry call.
            int leftWrite = construction.indexOf("__provT[\"left\"] = ");
            int rightWrite = construction.indexOf("__provT[\"right\"] = ");
            check(leftWrite >= 0 && rightWrite > leftWrite,
                "the checked values land in the provided table under their"
                    + " field names in declaration order");
            check(construction.contains("pcall(__bcheck, \"int\", \"int\", ")
                    && leftWrite < construction.indexOf("pcall(__rt.class_plan_, ")
                    && rightWrite < construction.indexOf("pcall(__rt.class_plan_, "),
                "both provided-field boundary children run before the entry"
                    + " call");
            // (c) A well-formed payload emits no extra-key guard, and the
            // construction emits no CLASS_DEFAULT child, no in-project
            // factory, no default expression, and no ABI conversion text.
            check(!construction.contains("E8007"),
                "a well-formed provided-field payload emits no extra-key guard");
            check(!construction.contains("CLASS_DEFAULT"),
                "the C-struct construction emits no CLASS_DEFAULT child");
            check(!construction.contains("CLASS_FACTORY")
                    && !construction.contains("__fT"),
                "the C-struct construction emits no factory transfer");
            check(artifact.contains("evaluator = function() return 0 end"),
                "the plan literal carries the deferred evaluators (the only"
                    + " default authority)");
            check(!artifact.contains("ffi.cast") && !artifact.contains("cdef(")
                    && !artifact.contains("ffi.new"),
                "the artifact carries no ABI conversion or cdef text");

            // (d) The fixture's own copy-isolation assertions under luajit —
            // the construction, the load prelude, and the crossings of the
            // T1/T2 slices combined in one production artifact.
            check(artifact.contains("__hostDealProject(\"" + PAIR_DESC
                    + "\", __instT, "),
                "the constructed instance is projected into the chunk"
                    + " representation");
            SidecarExpectations.RuntimeExpectation.Executed expectation =
                luajitExpectation();
            checkEq("runtime-ok", expectation.mode(),
                "ffi/019 is a runtime-ok fixture");
            ProcessOutcome run = runProcess(
                List.of("luajit", emitted.name()), out, Map.of());
            check(run.exitCode() == expectation.exitCode(),
                "ffi/019 exit code matches the sidecar: exit=" + run.exitCode()
                    + " stderr=" + escaped(run.stderr()));
            checkEq(new String(expectation.stdout(), StandardCharsets.UTF_8),
                run.stdout(), "ffi/019 stdout transcript");
            checkEq(new String(expectation.stderr(), StandardCharsets.UTF_8),
                run.stderr(), "ffi/019 stderr transcript");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The lowered and emitted FFI_PLAN shape
    // =========================================================================

    private static void testConstructionShape() throws Exception {
        System.out.println("-- the lowered and emitted FFI_PLAN construction"
            + " shape: the seed layout, the null factory ref, the empty"
            + " default-op list, and the provided-field boundaries --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp op = constructionOf(project);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) op.payload();
            checkEq(new ClassId("$external/" + NATIVE, "Pair"), payload.classId(),
                "the construction carries the declared class identity");
            checkEq(DefaultOwner.FFI_PLAN, payload.defaultOwner(),
                "the CLASS_NEW defaultOwner is FFI_PLAN");
            check(payload.classFactoryRef() == null,
                "the C-struct construction carries the null factory ref");
            check(payload.classDefaultOpIds().isEmpty(),
                "the C-struct construction carries empty classDefaultOpIds");
            ClassRegistrationSeeds.ClassRegistration registration =
                lowered.seeds().registrationFor(payload.classId());
            check(registration != null
                    && registration.owner() == DefaultOwner.FFI_PLAN,
                "the class resolves in the project's registration seeds under"
                    + " FFI_PLAN");
            if (registration != null) {
                checkEq(registration.layout(), payload.layout(),
                    "the payload's layout is exactly the registered C-struct"
                        + " layout");
                check(registration.layout().fields().stream().allMatch(field ->
                        field.required()
                            && field.defaultOwner() == DefaultOwner.FFI_PLAN),
                    "every registered struct field is required-present under"
                        + " FFI_PLAN");
                checkEq(List.of("left", "right"),
                    registration.layout().fields().stream()
                        .map(ClassLayout.FieldLayout::name).toList(),
                    "the registered layout keeps the plan's source order");
            }
            checkEq(List.of("left", "right"),
                payload.fieldBoundaries().stream()
                    .map(KindPayload.FieldBoundary::field).toList(),
                "the field boundaries are the provided fields in declaration"
                    + " order");
            check(payload.fieldBoundaries().stream().allMatch(entry ->
                    entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD),
                "every field boundary is a CLASS_LITERAL_FIELD (no"
                    + " CLASS_DEFAULT_FIELD: the omitted fields are the loaded"
                    + " plan's)");
            LoweredModuleUnit unit = unitOf(project, op);
            check(!unit.classLayouts().containsKey(payload.classId()),
                "the seed layout is never merged into the unit's own"
                    + " classLayouts");

            // The composed gate accepts the realized shape over the seeds.
            Optional<CompilerDiagnostic> failure =
                SemanticLowerer.validateProjectUnit(unit,
                    lowered.tables().get(unit.moduleId()),
                    new SemanticIrValidator.ComparisonFacts(
                        project.interfaceIndex().interfaceIndexDigest(),
                        SemanticProfile.DEAL_V1_2_INT32,
                        productionInvocation().capabilityRegistryHash()),
                    BindingsProductionValidator.PinnedWriteFacts.empty(),
                    lowered.registries().get(unit.moduleId()),
                    new JsonDefaultChildTable(Map.of()),
                    project.interfaceIndex().modules().get(unit.moduleId()), Map.of(),
                    lowered.seeds().registrations());
            check(failure.isEmpty(),
                "the composed chain accepts the C-struct construction unit: "
                    + failure.map(CompilerDiagnostic::message).orElse(""));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The evaluator-once drive
    // =========================================================================

    private static final String COUNTING_DECLARATION = """
        // @extern-c

        // @c-struct
        export class Probe {
          a: int = fixture_count_call_int();
          b: int = fixture_count_call_int();
        }

        export function fixture_count_call_int(): int;
        export function fixture_call_count(): int;
        export function fixture_reset_counter(): null;
        """;

    private static final String COUNTING_APP = """
        import * as native from "ffi/valid"

        export function main(): null {
          // Zero evaluator invocations at load: the plan's evaluators are
          // deferred and no library symbol resolves a default.
          if (native.fixture_call_count() !== 0) {
            throw { code: "TEST_FAIL", message: "a default evaluated at load" };
          }
          // The first attempt: both fields omitted, so each deferred
          // evaluator runs exactly once, in class source order.
          let first: native.Probe = {};
          if (first.a !== 1 || first.b !== 2) {
            throw { code: "TEST_FAIL", message: "the omitted fields' evaluators did not run once each in class source order" };
          }
          if (native.fixture_call_count() !== 2) {
            throw { code: "TEST_FAIL", message: "the per-attempt evaluator count" };
          }
          // A provided field suppresses exactly its own evaluator.
          let second: native.Probe = { a: 99 };
          if (second.a !== 99 || second.b !== 3) {
            throw { code: "TEST_FAIL", message: "a provided field did not suppress its own evaluator" };
          }
          if (native.fixture_call_count() !== 3) {
            throw { code: "TEST_FAIL", message: "the provided-field suppression count" };
          }
          // A further attempt re-runs the omitted fields' evaluators.
          let third: native.Probe = {};
          if (third.a !== 4 || third.b !== 5) {
            throw { code: "TEST_FAIL", message: "the re-executed evaluators did not continue the counter" };
          }
          if (native.fixture_call_count() !== 5) {
            throw { code: "TEST_FAIL", message: "the final evaluator count" };
          }
          return null;
        }
        """;

    /**
     * The extra-key drive's application: the `broken` literal's provided
     * field is the doctored site (the guard raises E8007 before the runtime
     * entry call, so no deferred evaluator runs for the failed attempt),
     * and the `after` literal's omitted fields re-execute the evaluators
     * once the attempt's own recovery completed.
     */
    private static final String DOCTORED_APP = """
        import * as native from "ffi/valid"

        export function main(): null {
          if (native.fixture_call_count() !== 0) {
            throw { code: "TEST_FAIL", message: "a default evaluated at load" };
          }
          try {
            let broken: native.Probe = { a: 7 };
            throw { code: "TEST_FAIL", message: "the doctored construction did not fail" };
          } catch (e) {
            if (e.code !== "E8007") {
              throw { code: "TEST_FAIL", message: "the doctored construction raised the wrong code" };
            }
            if (e.message !== "extra field 'zzz' in class '@$external/ffi/valid/Probe'") {
              throw { code: "TEST_FAIL", message: "the E8007 message does not name the first provided-source extra" };
            }
          }
          // The failed attempt ran no evaluator: the counter is unchanged,
          // and the next attempt takes the first values.
          if (native.fixture_call_count() !== 0) {
            throw { code: "TEST_FAIL", message: "an evaluator ran for the failed attempt" };
          }
          let after: native.Probe = {};
          if (after.a !== 1 || after.b !== 2) {
            throw { code: "TEST_FAIL", message: "the omitted fields' evaluators did not run once each in class source order" };
          }
          if (native.fixture_call_count() !== 2) {
            throw { code: "TEST_FAIL", message: "the post-failure evaluator count" };
          }
          return null;
        }
        """;

    private static final String COUNTING_MANIFEST = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "output": "build/lua",
          "backend": "luajit",
          "externals": {
            "ffi/valid": {
              "declaration": "ffi.d.deal",
              "nativeLibrary": "libs/phase-ffi.so"
            }
          }
        }
        """;

    /**
     * Builds the focused project's native fixture (the committed FFIGEN
     * integration C source) into the manifest-relative loader path, then
     * compiles the project through the production arm.
     */
    private static Fixture compileCountingFixture(Path root, String appName,
            String appSource) throws Exception {
        if (!toolAvailable("gcc", "--version")) {
            throw new IllegalStateException("gcc is unavailable — the focused"
                + " C-struct fixture cannot build its native library");
        }
        Path libs = root.resolve("libs");
        Files.createDirectories(libs);
        String eventsPath = root.resolve("events.log").toString();
        ProcessOutcome gcc = runProcess(List.of("gcc", "-shared", "-fPIC", "-O2",
            "-DFIXTURE_EVENTS_PATH=\"" + eventsPath + "\"", "-o",
            libs.resolve("phase-ffi.so").toString(),
            Path.of("test", "fixtures", "ffigen",
                "ffigen-integration-fixture.c").toAbsolutePath().normalize()
                .toString()), root, Map.of());
        if (gcc.exitCode() != 0) {
            throw new IllegalStateException("the focused native fixture compile"
                + " failed: " + gcc.stdout() + gcc.stderr());
        }
        String app = ConformanceHarnessMetadata
            .stripClassificationHeaders(appSource);
        // The declaration path is manifest-relative (the project root).
        Files.writeString(root.resolve("ffi.d.deal"),
            ConformanceHarnessMetadata
                .stripClassificationHeaders(COUNTING_DECLARATION),
            StandardCharsets.UTF_8);
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(appName + ".deal"), app,
            StandardCharsets.UTF_8);
        Files.writeString(root.resolve("deal.json"), COUNTING_MANIFEST,
            StandardCharsets.UTF_8);
        Path entry = src.resolve(appName + ".deal").toAbsolutePath();
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entry.toString(), null);
        if (located.context() == null) {
            throw new IllegalStateException("the focused project does not"
                + " locate: " + located.e2010());
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entry, false, false, false, false, null,
            productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null
                || built.index() == null || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            throw new IllegalStateException("the focused FFI fixture did not"
                + " build: " + detail + " / " + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()),
                generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(FOCUSED_SPECIFIER));
        }
        return new Fixture(root, src, FOCUSED_SPECIFIER, FOCUSED_DOTTED,
            appName + ".deal", app, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            externCModules, identities, Path.of(located.context().outputPath()
            .absoluteNormalizedPath()));
    }

    private static void testEvaluatorOnceDrive() throws Exception {
        System.out.println("-- the evaluator-once drive: zero at load, once per"
            + " omitted field per attempt in class source order, provided-field"
            + " suppression, and no evaluator for a failed attempt --");
        Path root = Files.createTempDirectory("ffi-struct-counting");
        try {
            Fixture fixture;
            try {
                fixture = compileCountingFixture(root, "struct-counting",
                    COUNTING_APP);
            } catch (IllegalStateException failure) {
                fail(failure.getMessage());
                return;
            }
            // The production compile already emitted and published the
            // project artifact (the orchestrator's production arm).
            Path artifact = fixture.outputRoot().resolve(
                fixture.appFileName().replace(".deal", ".lua"));
            check(Files.isRegularFile(artifact),
                "the focused project publishes its production artifact: "
                    + artifact);
            if (!Files.isRegularFile(artifact)) {
                return;
            }
            String text = Files.readString(artifact, StandardCharsets.UTF_8);
            String region = constructionRegion(text,
                "pcall(__rt.class_plan_, \"" + FOCUSED_PROBE_DESC + "\"");
            check(region.contains("pcall(__rt.class_plan_, \""
                    + FOCUSED_PROBE_DESC + "\", __ffiClassPlan(\""
                    + FOCUSED_DOTTED + "\", \"Probe\"), __provT, "),
                "the artifact constructs through the loaded Probe plan: "
                    + region);
            check(text.contains("fixture_count_call_int")
                    && text.contains("evaluator = function() return "),
                "the plan literal carries the generated deferred evaluators"
                    + " (the only default authority)");
            check(!region.contains("CLASS_DEFAULT"),
                "the C-struct construction emits no CLASS_DEFAULT child: "
                    + region);

            ProcessOutcome run = runProcess(List.of("luajit",
                fixture.appFileName().replace(".deal", ".lua")),
                fixture.outputRoot(), Map.of());
            check(run.exitCode() == 0,
                "the evaluator-once drive exits 0 (zero at load, one per"
                    + " omitted field per attempt in class source order,"
                    + " provided-field suppression, and no evaluator for the"
                    + " failed attempt): exit=" + run.exitCode() + " stdout="
                    + escaped(run.stdout()) + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 4. The extra-key E8007 drive
    // =========================================================================

    private static void testExtraKeyE8007Drive() throws Exception {
        System.out.println("-- the extra-key E8007 drive: a doctored FFI_PLAN"
            + " payload with two extra provided names fails with exactly one"
            + " E8007 naming the first provided-source extra at the literal"
            + " origin, before any default --");
        Path root = Files.createTempDirectory("ffi-struct-extra-key");
        try {
            Fixture fixture;
            try {
                fixture = compileCountingFixture(root, "struct-doctored",
                    DOCTORED_APP);
            } catch (IllegalStateException failure) {
                fail(failure.getMessage());
                return;
            }
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the focused fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            // The `broken` literal (inside the app's try/catch) carries one
            // provided field; the `after` literal carries none.
            SemanticOp broken = null;
            SemanticOp after = null;
            for (LoweredModuleUnit candidate : project.modules().values()) {
                for (SemanticOp op : candidate.ops()) {
                    if (op.kind() != SemanticOpKind.CLASS_NEW
                            || !(op.payload()
                                instanceof KindPayload.ClassNewPayload payload)
                            || payload.defaultOwner() != DefaultOwner.FFI_PLAN) {
                        continue;
                    }
                    String line = sourceLine(fixture.strippedApp(),
                        op.origin().span().startLine());
                    if (line.contains("let broken")) {
                        broken = op;
                    }
                    if (line.contains("let after")) {
                        after = op;
                    }
                }
            }
            check(broken != null && after != null,
                "the app's `broken` and `after` constructions are in the"
                    + " closure");
            if (broken == null || after == null) {
                return;
            }
            KindPayload.ClassNewPayload brokenPayload =
                (KindPayload.ClassNewPayload) broken.payload();
            checkEq(List.of("a"), brokenPayload.providedFields().stream()
                    .map(KindPayload.ProvidedField::name).toList(),
                "the `broken` literal provides exactly one field");

            // Run A: the doctored `broken` payload over the app's own
            // try/catch — the DEAL-visible code and message and the
            // unchanged evaluator counter (no default ran for the failed
            // attempt).
            Doctored runA = doctored(fixture, lowered, project,
                List.of(broken), brokenPayload.providedFields().get(0)
                    .valueOpId());
            String chunkA = runA.chunk();
            String origin = broken.origin().sourceId() + ":"
                + broken.origin().span().startLine() + ":"
                + broken.origin().span().startColumn();
            String regionA = constructionRegion(chunkA, "extra field 'zzz'");
            int guardAt = regionA.indexOf("__failExpr(\"E8007\","
                + " \"extra field 'zzz'");
            int entryAt = regionA.indexOf("pcall(__rt.class_plan_, ");
            check(guardAt > 0, "the emitted guard names the first"
                + " provided-source extra: " + regionA);
            check(guardAt > 0 && guardAt < entryAt,
                "the guard precedes the runtime entry call (no default runs"
                    + " for the failed attempt)");
            check(chunkA.contains("extra field 'zzz' in class '"
                    + FOCUSED_PROBE_DESC + "'\", \"" + origin
                    + "\", nil, nil)"),
                "the guard raises E8007 at the literal origin " + origin);
            check(regionA.indexOf("extra field 'zzz'")
                    < regionA.indexOf("extra field 'yyy'"),
                "the guards keep the provided-source order");
            check(regionA.indexOf("__provT[\"a\"] = ") > 0
                    && regionA.indexOf("__provT[\"a\"] = ") < guardAt,
                "the declared provided field's boundary child precedes the"
                    + " guard");
            check(chunkA.contains("__provT[\"zzz\"]") == false
                    && chunkA.contains("__provT[\"yyy\"]") == false,
                "an extra provided name never reaches the provided table");
            ProcessOutcome run = runProcess(List.of("luajit",
                "struct-doctored.lua"), runA.out(), Map.of());
            check(run.exitCode() == 0 && run.stdout().trim().isEmpty(),
                "the app's own checks accept the doctored attempt's pinned"
                    + " E8007 projection and the unchanged evaluator count:"
                    + " exit=" + run.exitCode() + " stdout="
                    + escaped(run.stdout()) + " stderr=" + escaped(run.stderr()));

            // Run B: both sites doctored — the `broken` attempt stays
            // caught (the app's own recovery runs), and the `after`
            // attempt's E8007 is uncaught, so the runtime reports its
            // literal origin and the native counter read after the failure
            // proves that no default ran for either failed attempt.
            Doctored runB = doctored(fixture, lowered, project,
                List.of(broken, after), null);
            String chunkB = runB.chunk();
            ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"),
                runB.out(), Map.of("DEAL_DEFER_MAIN", "1"));
            check(probe.exitCode() == 0,
                "the doctored artifact's failure probe runs: exit="
                    + probe.exitCode() + " stdout=" + escaped(probe.stdout())
                    + " stderr=" + escaped(probe.stderr()));
            if (probe.exitCode() == 0) {
                String[] lines = probe.stdout().trim().split("\\n", -1);
                String[] parts = lines[0].split("\\|", -1);
                checkEq("ERR", parts.length > 0 ? parts[0] : null,
                    "the doctored construction raises a DEAL error");
                checkEq("E8007", parts.length > 1 ? parts[1] : null,
                    "the doctored construction raises E8007");
                checkEq("extra field 'zzz' in class '" + FOCUSED_PROBE_DESC + "'",
                    parts.length > 2 ? parts[2] : null,
                    "the E8007 message names the first provided-source extra");
                String firstOrigin = after.origin().sourceId() + ":"
                    + after.origin().span().startLine() + ":"
                    + after.origin().span().startColumn();
                checkEq(firstOrigin, parts.length > 5
                        ? parts[3] + ":" + parts[4] + ":" + parts[5] : null,
                    "the E8007 origin is the literal origin " + firstOrigin);
                check(probe.stdout().contains("COUNTER|0"),
                    "no default ran for the failed attempt (the native counter"
                        + " is zero after the failure): "
                        + escaped(probe.stdout()));
            }
            String regionB = constructionRegion(chunkB, "extra field 'zzz'");
            check(regionB.indexOf("extra field 'zzz'") > 0
                    && regionB.indexOf("extra field 'zzz'")
                        < regionB.indexOf("pcall(__rt.class_plan_, "),
                "the second doctored site keeps the guard-before-entry order: "
                    + regionB);
        } finally {
            deleteRecursively(root);
        }
    }

    /** One doctored emission with its materialized artifact tree. */
    private record Doctored(String chunk, Path out) {
    }

    /**
     * Emits the focused project with one construction's provided-field list
     * extended by the two extra names {@code zzz} and {@code yyy} (the
     * doctored boundary payload the runtime arm defends), materializes the
     * chunk beside the deployed runtime, and copies the failure probe.
     */
    private static Doctored doctored(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult lowered,
            ExecutableLoweredProject project, List<SemanticOp> targets,
            ValueId reusedValue) throws Exception {
        LoweredModuleUnit unit = unitOf(project, targets.get(0));
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        for (SemanticOp target : targets) {
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) target.payload();
            ValueId reused = reusedValue != null ? reusedValue
                : payload.fieldBoundaries().isEmpty() ? null
                    : ((KindPayload.BoundaryPayload) opOf(project, payload
                        .fieldBoundaries().get(0).boundaryOpId()).payload())
                        .input();
            if (reused == null) {
                // A construction with no provided field and no boundary:
                // reuse the first value the unit publishes, so the extra
                // names carry a well-formed operand id.
                reused = firstValueId(project, target);
            }
            List<KindPayload.ProvidedField> extended =
                new ArrayList<>(payload.providedFields());
            extended.add(new KindPayload.ProvidedField("zzz", reused));
            extended.add(new KindPayload.ProvidedField("yyy", reused));
            KindPayload.ClassNewPayload doctoredPayload =
                new KindPayload.ClassNewPayload(payload.classId(),
                    payload.layout(), extended, payload.defaultOwner(),
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    payload.fieldBoundaries());
            ops.set(ops.indexOf(target), rebuildOp(target, doctoredPayload));
        }
        LoweredModuleUnit doctoredUnit = withOps(unit, ops);

        // The composed validator rejects the doctored shape (the emitter
        // would never see it from the lowering; the runtime arm defends the
        // boundary payload).
        Optional<CompilerDiagnostic> rejected =
            ClassConstructionValidator.validate(doctoredUnit,
                lowered.tables().get(unit.moduleId()),
                lowered.registries().get(unit.moduleId()),
                new JsonDefaultChildTable(Map.of()),
                project.interfaceIndex().modules().get(unit.moduleId()), Map.of(),
                lowered.seeds().registrations());
        check(rejected.isPresent() && "E6005".equals(rejected.get().code())
                && rejected.get().message()
                    .contains(ClassConstructionValidator.CONSTRUCTION_COHERENCE),
            "the doctored payload is rejected by the composed validator: "
                + rejected.map(CompilerDiagnostic::message).orElse("accepted"));

        Map<ModuleId, LoweredModuleUnit> modules =
            new LinkedHashMap<>(project.modules());
        modules.put(unit.moduleId(), doctoredUnit);
        ExecutableLoweredProject doctoredProject = new ExecutableLoweredProject(
            project.semanticProfile(), project.interfaceIndex(), modules,
            project.entryModule());
        String chunk = LuaSemanticEmitter.emitProductionProject(doctoredProject,
            lowered.tables(), lowered.registries(), fixture.surface(),
            new FfiEmissionInput(fixture.externCModules(),
                fixture.root().toString()));
        Path out = fixture.root().resolve("out-doctored-"
            + Integer.toHexString(System.identityHashCode(targets.get(0))
                + targets.size()));
        Files.createDirectories(out.resolve("deal"));
        Files.copy(Path.of("deal", "runtime.lua"),
            out.resolve("deal").resolve("runtime.lua"));
        Files.writeString(out.resolve(fixture.appFileName().replace(".deal",
            ".lua")), chunk, StandardCharsets.UTF_8);
        Files.writeString(out.resolve("probe.lua"),
            countingFailureProbe(fixture.appFileName().replace(".deal", ".lua")),
            StandardCharsets.UTF_8);
        return new Doctored(chunk, out);
    }

    /** The unit's op named by one id. */
    private static SemanticOp opOf(ExecutableLoweredProject project, OpId opId) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(opId)) {
                    return op;
                }
            }
        }
        throw new IllegalStateException("no op " + opId + " in the closure");
    }

    /** The first published value id of one construction's unit. */
    private static ValueId firstValueId(ExecutableLoweredProject project,
            SemanticOp target) {
        LoweredModuleUnit unit = unitOf(project, target);
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId id
                    && op.origin().span() != null
                    && op.origin().span().startLine()
                        == target.origin().span().startLine()) {
                return id;
            }
        }
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId id) {
                return id;
            }
        }
        throw new IllegalStateException("the unit publishes no value to reuse");
    }

    /**
     * The failure probe of the counting drive: the uncaught DEAL error's
     * code, message, and origin, then the native counter read through the
     * loaded surface — the runtime proof that a failed attempt ran no
     * evaluator.
     */
    private static String countingFailureProbe(String artifactName) {
        return """
            local function fail(message)
              print("PROBE-FAIL|" .. message)
              os.exit(1)
            end
            local surface = dofile("%s")
            if type(surface) ~= "table" then fail("the chunk returns no surface") end
            local ok, err = __dealMain()
            if ok then fail("the module init succeeded") end
            if type(err) ~= "table" or err.code == nil then
              fail("the raised value is not a runtime error table")
            end
            local message = err.message or err.m
            local file, line, column = err.file, err.line, err.column
            if err.o ~= nil then
              local f, l, c = tostring(err.o):match("^(.*):(%%d+):(%%d+)$")
              file, line, column = f, l, c
            end
            print("ERR|" .. tostring(err.code) .. "|" .. tostring(message)
              .. "|" .. tostring(file) .. "|" .. tostring(line) .. "|"
              .. tostring(column))
            local counter = __exportSurfaces["ffi.valid"] == nil and nil
              or __exportSurfaces["ffi.valid"]["fixture_call_count"]
            if counter == nil then
              print("COUNTER|<unavailable>")
            else
              print("COUNTER|" .. tostring(counter.f(nil, nil, nil)))
            end
            """.formatted(artifactName);
    }

    /** The source line named by one 1-based line number. */
    private static String sourceLine(String source, int line) {
        String[] lines = source.split("\n", -1);
        return line >= 1 && line <= lines.length ? lines[line - 1] : "";
    }

    // =========================================================================
    // 5. The validator deviation battery and the JVM arm
    // =========================================================================

    private static void testValidatorDeviationBattery() throws Exception {
        System.out.println("-- the validator deviation battery: the seed-layout"
            + " admission and each deviation fails CONSTRUCTION_COHERENCE --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp target = constructionOf(project);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) target.payload();
            LoweredModuleUnit unit = unitOf(project, target);
            StructuredBodyTable table = lowered.tables().get(unit.moduleId());
            ClassFactoryRegistry registry =
                lowered.registries().get(unit.moduleId());
            ExternalModuleInterface ownInterface =
                project.interfaceIndex().modules().get(unit.moduleId());

            // (a) The admitted shape over the seeds.
            Optional<CompilerDiagnostic> admitted = ClassConstructionValidator
                .validate(unit, table, registry,
                    new JsonDefaultChildTable(Map.of()), ownInterface, Map.of(),
                    lowered.seeds().registrations());
            check(admitted.isEmpty(),
                "the composed validator admits the FFI_PLAN shape over the"
                    + " seed-layout input: "
                    + admitted.map(CompilerDiagnostic::message).orElse(""));

            // (b) The pre-change outcome: without the seed-layout input the
            // extern-C class resolves in no context.
            Optional<CompilerDiagnostic> unseeded = ClassConstructionValidator
                .validate(unit, table, registry,
                    new JsonDefaultChildTable(Map.of()), ownInterface, Map.of());
            check(unseeded.isPresent()
                    && unseeded.get().message().contains("CONSTRUCTION_COHERENCE"),
                "an extern-C construction without the seed-layout input fails"
                    + " closed: "
                    + unseeded.map(CompilerDiagnostic::message).orElse("admitted"));

            // (c) Each deviation of the realized shape.
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(),
                    foreignLayout(payload), payload.providedFields(),
                    payload.defaultOwner(), payload.classDefaultOpIds(),
                    payload.classFactoryRef(), payload.fieldBoundaries()),
                "a layout that differs from the registered seed layout");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), DefaultOwner.HOST_DEFAULTS,
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    payload.fieldBoundaries()),
                "the HOST_DEFAULTS owner over an extern-C class");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), payload.defaultOwner(),
                    List.of(target.opId()), payload.classFactoryRef(),
                    payload.fieldBoundaries()),
                "a non-empty default-op list");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), payload.defaultOwner(),
                    payload.classDefaultOpIds(), new ClassFactoryId(0),
                    payload.fieldBoundaries()),
                "a non-null factory ref");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), payload.defaultOwner(),
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    List.of(new KindPayload.FieldBoundary(
                        payload.fieldBoundaries().get(0).field(),
                        BoundaryKind.CLASS_DEFAULT_FIELD,
                        payload.fieldBoundaries().get(0).boundaryOpId()),
                        payload.fieldBoundaries().get(1))),
                "a CLASS_DEFAULT_FIELD boundary");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), payload.defaultOwner(),
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    List.of(payload.fieldBoundaries().get(0))),
                "a missing provided-field boundary");
            expectRejected(lowered, unit, table, registry, ownInterface, target,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), payload.defaultOwner(),
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    List.of(payload.fieldBoundaries().get(1),
                        payload.fieldBoundaries().get(0))),
                "a wrong boundary order");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** One rejected payload through the composed validator. */
    private static void expectRejected(SemanticLowerer.ProjectLoweringResult lowered,
            LoweredModuleUnit unit, StructuredBodyTable table,
            ClassFactoryRegistry registry, ExternalModuleInterface ownInterface,
            SemanticOp target, KindPayload doctored, String what) {
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        ops.set(ops.indexOf(target), rebuildOp(target, doctored));
        Optional<CompilerDiagnostic> failure = ClassConstructionValidator.validate(
            withOps(unit, ops), table, registry,
            new JsonDefaultChildTable(Map.of()), ownInterface, Map.of(),
            lowered.seeds().registrations());
        check(failure.isPresent()
                && "E6005".equals(failure.get().code())
                && failure.get().message()
                    .contains(ClassConstructionValidator.CONSTRUCTION_COHERENCE),
            what + " fails CONSTRUCTION_COHERENCE: "
                + failure.map(CompilerDiagnostic::message).orElse("admitted"));
    }

    /** A layout of the same class identity with a different field set. */
    private static ClassLayout foreignLayout(KindPayload.ClassNewPayload payload) {
        ClassLayout layout = payload.layout();
        List<ClassLayout.FieldLayout> fields = new ArrayList<>(layout.fields());
        fields.add(new ClassLayout.FieldLayout("extra",
            layout.fields().get(0).descriptor(), true, DefaultOwner.FFI_PLAN));
        return new ClassLayout(layout.classId(), fields);
    }

    private static void testJvmArmKeepsProducerDefect() throws Exception {
        System.out.println("-- the JVM arm keeps its fail-closed FFI_PLAN"
            + " producer defect (the phase-3.9 E6006 precedes any lowering) --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp construction = constructionOf(project);
            LoweredModuleUnit unit = unitOf(project, construction);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) construction.payload();
            // The production project entry fails closed on the extern-C
            // declaration import (no JVM realization of the FFI load
            // exists; the phase-3.9 E6006 rejects a JVM compile of an
            // extern-C closure before any lowering).
            boolean projectThrew = false;
            try {
                JvmSemanticEmitter.emitProductionProject(project,
                    lowered.tables(), lowered.registries(), "Main",
                    fixture.surface());
            } catch (IllegalStateException expected) {
                projectThrew = true;
                check(expected.getMessage().contains("extern-C"),
                    "the JVM project entry rejects the extern-C declaration"
                        + " import fail-closed: " + expected.getMessage());
            }
            check(projectThrew, "the JVM production project entry rejects an"
                + " extern-C closure (no JVM FFI realization)");
            // The owner arm itself (the wiki's direct unit assertion): the
            // declaration-class layout resolution gains the payload's own
            // registered C-struct layout, so the walk reaches the
            // FFI_PLAN owner arm and the emitter keeps its fail-closed
            // producer defect.
            boolean ownerThrew = false;
            try {
                JvmSemanticEmitter.emitProductionModule(
                    withClassLayout(unit, payload.classId(), payload.layout()),
                    lowered.tables().get(unit.moduleId()), true, "FfiPlanModule");
            } catch (IllegalStateException expected) {
                ownerThrew = true;
                check(expected.getMessage().contains("FFI_PLAN")
                        && expected.getMessage().contains("fail-closed"),
                    "the JVM owner arm names the owner and keeps the"
                        + " fail-closed defect: " + expected.getMessage());
            }
            check(ownerThrew, "the JVM emitter rejects the FFI_PLAN construction"
                + " fail-closed");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Op/unit rebuild helpers (the established test-side pattern)
    // =========================================================================

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    /**
     * One unit copy carrying one extra layout in its resolution context —
     * the test-side probe that lets the JVM emitter's walk reach the
     * declaration-class construction arm (the production lowering never
     * merges the seeds into a unit's layouts; the probe changes nothing
     * about the emitted defect).
     */
    private static LoweredModuleUnit withClassLayout(LoweredModuleUnit unit,
            ClassId classId, ClassLayout layout) {
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>(unit.classLayouts());
        layouts.put(classId, layout);
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), layouts,
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), unit.ops());
    }

    private static SemanticOp rebuildOp(SemanticOp original, KindPayload payload) {
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, original.kind(),
            original.resultType(), original.operandTypes(), null, payload,
            original.failurePolicy(), List.of(), "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, original.kind(),
            original.resultType(), original.operandTypes(), null, payload,
            original.failurePolicy(), List.of(), digest);
        return new SemanticOp(original.opId(), original.kind(), original.origin(),
            original.result(), original.resultType(), original.operands(),
            original.operandTypes(), payload, original.failurePolicy(), contract);
    }

    // =========================================================================
    // Gate
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Struct Construction Tests (ISSUE-0666) ===");
        System.out.println();
        testCorpusStructConstructionDrive();
        testConstructionShape();
        testEvaluatorOnceDrive();
        testExtraKeyE8007Drive();
        testValidatorDeviationBattery();
        testJvmArmKeepsProducerDefect();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Struct Construction Tests Passed ===");
    }

    // =========================================================================
    // Process, tool, and filesystem helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.environment().putAll(environment);
        builder.redirectErrorStream(false);
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static boolean toolAvailable(String tool, String probe) {
        try {
            Process process = new ProcessBuilder(tool, probe)
                .redirectErrorStream(true).start();
            process.getInputStream().readAllBytes();
            return process.waitFor() == 0;
        } catch (Exception e) {
            return false;
        }
    }

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    /** The LuaJIT failure probe of one artifact (the deferred entry). */
    private static String failureProbe(String artifactName) {
        return """
            local function fail(message)
              print("PROBE-FAIL|" .. message)
              os.exit(1)
            end
            local surface = dofile("%s")
            if type(surface) ~= "table" then fail("the chunk returns no surface") end
            local ok, err = __dealMain()
            if ok then fail("the module init succeeded") end
            if type(err) ~= "table" or err.code == nil then
              fail("the raised value is not a runtime error table")
            end
            local message = err.message or err.m
            local file, line, column = err.file, err.line, err.column
            if err.o ~= nil then
              local f, l, c = tostring(err.o):match("^(.*):(%%d+):(%%d+)$")
              file, line, column = f, l, c
            end
            print("ERR|" .. tostring(err.code) .. "|" .. tostring(message)
              .. "|" .. tostring(file) .. "|" .. tostring(line) .. "|"
              .. tostring(column))
            """.formatted(artifactName);
    }

    /** The pinned LuaJIT execution expectation of the corpus sidecar. */
    private static SidecarExpectations.RuntimeExpectation.Executed
            luajitExpectation() throws Exception {
        String json = Files.readString(Path.of(CORPUS_FFI_DIR + "/" + CORPUS_CASE
            + ".expect.json"), StandardCharsets.UTF_8);
        SidecarExpectations.StructuredExpectationSidecar sidecar =
            SidecarExpectations.StructuredExpectationSidecar.parse(json);
        SidecarExpectations.RuntimeExpectation expectation =
            sidecar.byBackend().get("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
            throw new IllegalStateException("the LuaJIT sidecar of " + CORPUS_CASE
                + " is not an executed expectation: " + json);
        }
        return executed;
    }

    private static int lineOf(String source, String needle) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(needle)) {
                return i + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + needle + "'");
    }

    private static int columnOf(String source, String needle) {
        String[] lines = source.split("\n", -1);
        for (String line : lines) {
            int at = line.indexOf(needle);
            if (at >= 0) {
                return at + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + needle + "'");
    }

    /**
     * The emitted construction region of one C-struct site: from the
     * site's provided-table initialization to its result projection — the
     * region the site's own anchor (its plan call or its extra-key guard)
     * belongs to, so the shape assertions never read another site's
     * emission or a prelude comment.
     */
    private static String constructionRegion(String artifact, String anchor) {
        int at = artifact.indexOf(anchor);
        if (at < 0) {
            return "";
        }
        int start = artifact.lastIndexOf("__provT = {}", at);
        if (start < 0) {
            return "";
        }
        int end = artifact.indexOf("__hostDealProject(\"@$external/", at);
        if (end < 0) {
            end = Math.min(artifact.length(), at + 4000);
        }
        return artifact.substring(start, end);
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
}
