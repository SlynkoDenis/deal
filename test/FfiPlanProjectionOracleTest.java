package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.project.ProjectLocator;
import deal.publication.PublicationStager;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
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
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0667: the oracle plan-projection seam and the FFI construction
 * execution
 * ({@code luajit-ffi-struct-plan-construction-and-oracle-projection} F4
 * and the oracle plan-projection contract; {@code
 * luajit-ffi-shared-emission-and-jvm-rejection} F6;
 * {@code luajit-ffi-class-plan-consumption-verification} D4; sequencing
 * step 6).
 *
 * <ol>
 *   <li><b>The provided-only parity drive.</b>
 *       {@code ffi/019-ffi-struct-copy-isolation} runs through the oracle:
 *       the closed plan-projection terminal is requested with the resolved
 *       claiming module, the class's declared name, and its class
 *       descriptor; the construction publishes a declaration-order
 *       instance whose fields are the provided values; the host call
 *       receives exactly that instance and the fixture's own checks hold —
 *       and the same fixture's production artifact (the T5 construction
 *       site) executes under {@code luajit} with the sidecar-pinned
 *       {@code runtime-ok} transcript. The oracle's CLASS_NEW events (the
 *       provided fields' {@code CLASS_LITERAL_FIELD} boundary children in
 *       declaration order, then the op's terminal) are asserted.</li>
 *   <li><b>The omitted-field parity drive.</b> The focused declaration
 *       whose struct fields carry native-counting defaults runs through
 *       the oracle's projection suppliers: zero evaluations at load, one
 *       supplier per omitted field per attempt in class source order,
 *       provided-field suppression, and the counter sequence the artifact
 *       pins through the real generated evaluators
 *       ({@code 0, 2, 3, 5}) — while the same project's production
 *       artifact (real native evaluators) executes under {@code luajit}
 *       with exit 0.</li>
 *   <li><b>The projection agreement negatives.</b> A mutated entry order,
 *       a mutated descriptor, a short projection, and an absent projection
 *       each fail closed as a producer defect before any phase runs — the
 *       deferred suppliers (the phase-2 canary) are never invoked.</li>
 *   <li><b>The phase-3 descriptor projections.</b> A plan-supplied default
 *       of the wrong kind raises E8001 and an out-of-range integral number
 *       raises E8004, both at the literal origin, through the same
 *       canonical-matcher projections the artifact's runtime entry
 *       raises.</li>
 *   <li><b>The doctored extra-key parity.</b> A doctored
 *       {@code CLASS_NEW(FFI_PLAN)} payload carrying extra provided names
 *       yields the identical E8007 (code, message, origin) through the
 *       oracle and through the emitted artifact.</li>
 *   <li><b>The surface's closed owner set.</b> The new executor surface
 *       accepts only {@code FFI_PLAN} and rejects every other owner, a
 *       non-null factory ref, a non-empty default-op list, and an absent
 *       projection as producer defects.</li>
 *   <li><b>No generated evaluator content and no native code.</b> The
 *       negative drives compile the focused fixture without building its
 *       native library at all; the construction still executes through the
 *       seam — the oracle resolves no library, loads no symbol, and runs
 *       no generated evaluator text.</li>
 * </ol>
 */
public class FfiPlanProjectionOracleTest {

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

    /** The corpus FFI fixture project of this slice (ffi/019). */
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
        Path root = Files.createTempDirectory("ffi-plan-corpus");
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

    /** The registered declaration-class layouts of the lowering's seeds. */
    private static Map<ClassId, ClassLayout> declarationLayouts(
            SemanticLowerer.ProjectLoweringResult result) {
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>();
        for (Map.Entry<ClassId, deal.semantic.ClassRegistrationSeeds.ClassRegistration>
                entry : result.seeds().registrations().entrySet()) {
            layouts.put(entry.getKey(), entry.getValue().layout());
        }
        return layouts;
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

    /** The oracle events of one construction: the op and its boundary children. */
    private static List<SemanticRuntimeModel.TraceEvent> planEvents(
            SemanticRuntimeModel.ConsumerRun run, SemanticOp construction) {
        List<SemanticRuntimeModel.TraceEvent> events = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(construction.opId())
                    || construction.opId().equals(event.parentOp())) {
                events.add(event);
            }
        }
        return events;
    }

    private static String eventShape(SemanticRuntimeModel.TraceEvent event) {
        return event.kind() + "/" + event.phase();
    }

    // =========================================================================
    // 1. The provided-only parity drive (ffi/019)
    // =========================================================================

    /**
     * The corpus drive's seamed plan projection and host terminals: the
     * loaded {@code Pair_plan} entry (both fields provided in the fixture,
     * so its suppliers are canaries that must never run) and the declared
     * {@code ffi_pair_swap} by-value copy (the C function mutates its copy
     * and returns it; the original stays untouched).
     */
    private static final class PairResponder implements SemanticOracle.HostResponder {

        final List<String> projectionRequests = new ArrayList<>();
        final List<String> evaluatorInvocations = new ArrayList<>();
        final List<SemanticOracle.Value> swappedArguments = new ArrayList<>();
        final List<String> calls = new ArrayList<>();

        @Override
        public List<PlanEntry> planProjection(ModuleId module, String className,
                RuntimeDescriptor.Class declaredClass) {
            projectionRequests.add(module.path() + "." + className + " "
                + declaredClass.classId().text());
            if (!module.path().equals(NATIVE_DOTTED) || !className.equals("Pair")
                    || !declaredClass.classId().text().equals(PAIR_DESC)) {
                throw new IllegalStateException("the seam requested an unexpected"
                    + " plan projection: " + module.path() + "." + className + " "
                    + declaredClass.classId());
            }
            return List.of(
                new PlanEntry("left", RuntimeDescriptor.Int.INSTANCE, false, () -> {
                    evaluatorInvocations.add("left");
                    return new SemanticOracle.Value.IntValue(1);
                }),
                new PlanEntry("right", RuntimeDescriptor.Int.INSTANCE, false, () -> {
                    evaluatorInvocations.add("right");
                    return new SemanticOracle.Value.IntValue(2);
                }));
        }

        @Override
        public SyncOutcome call(ModuleId module, String export,
                RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
            calls.add(module.path() + "." + export);
            if (export.equals("ffi_pair_swap")) {
                SemanticOracle.Value argument = args.get(0);
                swappedArguments.add(argument);
                if (!(argument instanceof SemanticOracle.Value.ClassValue pair)) {
                    throw new IllegalStateException("ffi_pair_swap did not receive a"
                        + " class instance: " + argument);
                }
                List<SemanticOracle.Value.ClassFieldState> fields = new ArrayList<>();
                fields.add(new SemanticOracle.Value.ClassFieldState.Present(
                    new SemanticOracle.Value.IntValue(
                        ((SemanticOracle.Value.IntValue) presentField(pair, 0))
                            .value() + 1000)));
                fields.add(new SemanticOracle.Value.ClassFieldState.Present(
                    new SemanticOracle.Value.IntValue(
                        ((SemanticOracle.Value.IntValue) presentField(pair, 1))
                            .value() + 2000)));
                return new SyncOutcome.Returned(new SemanticOracle.Value.ClassValue(
                    new ClassId("$external/" + NATIVE, "Pair"), fields));
            }
            throw new IllegalStateException("the drive scripts no host terminal for "
                + module.path() + "." + export);
        }

        private static SemanticOracle.Value presentField(
                SemanticOracle.Value.ClassValue instance, int index) {
            return switch (instance.fields().get(index)) {
                case SemanticOracle.Value.ClassFieldState.Present present ->
                    present.value();
                case SemanticOracle.Value.ClassFieldState.Missing ignored ->
                    throw new IllegalStateException("field " + index
                        + " of the constructed Pair is absent");
            };
        }
    }

    private static void testProvidedOnlyParity() throws Exception {
        System.out.println("-- ffi/019: the oracle constructs native.Pair through"
            + " the plan projection; the artifact executes runtime-ok --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp construction = constructionOf(project);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) construction.payload();
            PairResponder responder = new PairResponder();

            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));

            // (a) The closed terminal is requested with the resolved
            // declaring module, the class's declared name, and its class
            // descriptor.
            checkEq(List.of(NATIVE_DOTTED + ".Pair " + PAIR_DESC),
                responder.projectionRequests,
                "the plan projection is requested once with the resolved module,"
                    + " the class name, and the class descriptor");
            checkEq(List.of("candidate.native.ffi_pair_swap"),
                responder.calls,
                "the fixture's host call runs once through the seam");
            check(responder.evaluatorInvocations.isEmpty(),
                "both fields are provided: no plan default runs (the suppliers are"
                    + " canaries): " + responder.evaluatorInvocations);
            checkEq(1, responder.swappedArguments.size(),
                "the host call receives exactly one constructed instance");

            // (b) The construction published the declaration-order instance
            // with the provided values — the host call's argument.
            if (!responder.swappedArguments.isEmpty()) {
                SemanticOracle.Value argument = responder.swappedArguments.get(0);
                check(argument instanceof SemanticOracle.Value.ClassValue instance
                        && instance.classId().text().equals(PAIR_DESC),
                    "the call's argument is an instance of " + PAIR_DESC + ": "
                        + argument);
                if (argument instanceof SemanticOracle.Value.ClassValue instance) {
                    checkEq(new SemanticOracle.Value.IntValue(4),
                        PairResponder.presentField(instance, 0),
                        "the instance's first declaration-order field is the"
                            + " provided left value");
                    checkEq(new SemanticOracle.Value.IntValue(9),
                        PairResponder.presentField(instance, 1),
                        "the instance's second declaration-order field is the"
                            + " provided right value");
                }
            }

            // (c) The oracle's construction events: the provided fields'
            // CLASS_LITERAL_FIELD boundary children in declaration order,
            // then the op's terminal.
            List<SemanticRuntimeModel.TraceEvent> events =
                planEvents(run, construction);
            List<String> shape = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : events) {
                shape.add(eventShape(event));
            }
            checkEq(List.of(
                    "CLASS_NEW/START",
                    "BOUNDARY/START", "BOUNDARY/SUCCESS",
                    "BOUNDARY/START", "BOUNDARY/SUCCESS",
                    "CLASS_NEW/SUCCESS"),
                shape,
                "the construction runs the two provided boundary children in"
                    + " declaration order and publishes last");
            if (events.size() == 6) {
                checkEq(List.of("int:4"), events.get(1).inputs(),
                    "the left boundary child checks the provided left value");
                checkEq(List.of("int:9"), events.get(3).inputs(),
                    "the right boundary child checks the provided right value");
                check(events.get(5).output() != null
                        && events.get(5).output().startsWith("ref:"),
                    "the construction publishes one heap instance: "
                        + events.get(5).output());
            }
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle's ffi/019 drive succeeds (the fixture's own"
                    + " copy-isolation checks hold): " + run.terminal());

            // (d) The artifact parity: the T5 construction site of the same
            // fixture executes under luajit with the pinned runtime-ok
            // transcript, and the construction region keeps the boundary
            // children before the runtime entry call.
            Artifact emitted = emitAndPublish(fixture, fixture.outputRoot());
            String constructionRegion = constructionRegion(emitted.text(),
                "pcall(__rt.class_plan_, \"" + PAIR_DESC + "\"");
            check(constructionRegion.indexOf("__provT[\"left\"] = ")
                    < constructionRegion.indexOf("pcall(__rt.class_plan_, "),
                "the artifact runs both provided boundary children before the"
                    + " runtime entry call: " + constructionRegion);
            SidecarExpectations.RuntimeExpectation.Executed expectation =
                luajitExpectation();
            checkEq("runtime-ok", expectation.mode(),
                "ffi/019 is a runtime-ok fixture");
            ProcessOutcome artifactRun = runProcess(
                List.of("luajit", emitted.name()), fixture.outputRoot(), Map.of());
            checkEq(expectation.exitCode(), artifactRun.exitCode(),
                "the artifact's exit code matches the sidecar: stderr="
                    + escaped(artifactRun.stderr()));
            checkEq(new String(expectation.stdout(), StandardCharsets.UTF_8),
                artifactRun.stdout(), "the artifact's stdout transcript");
            checkEq(new String(expectation.stderr(), StandardCharsets.UTF_8),
                artifactRun.stderr(), "the artifact's stderr transcript");
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    && artifactRun.exitCode() == 0,
                "the oracle and the artifact agree on the fixture's outcome");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The omitted-field parity drive
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

    private static final String OMITTED_APP = """
        import * as native from "ffi/valid"

        export function main(): null {
          let probe: native.Probe = {};
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
     * Compiles the focused project through the production arm. The native
     * library is built only when {@code buildNative} is set: the oracle
     * drives never need it (no generated evaluator content and no native
     * code runs there).
     */
    private static Fixture compileFocused(Path root, String appName,
            String appSource, boolean buildNative) throws Exception {
        if (buildNative) {
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
        }
        String app = ConformanceHarnessMetadata
            .stripClassificationHeaders(appSource);
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

    /**
     * The focused drive's seamed plan projection and native-counter
     * emulation: the loaded {@code Probe_plan} entry (the deferred
     * evaluators are the seam's suppliers, advancing the same in-process
     * counter the fixture's real generated evaluators advance through the
     * native {@code fixture_count_call_int}).
     */
    private static final class ProbeResponder implements SemanticOracle.HostResponder {

        final List<String> evaluatorLog = new ArrayList<>();
        final List<Integer> counterReads = new ArrayList<>();
        final List<String> calls = new ArrayList<>();
        final List<String> projectionRequests = new ArrayList<>();
        private int counter = 0;

        @Override
        public List<PlanEntry> planProjection(ModuleId module, String className,
                RuntimeDescriptor.Class declaredClass) {
            projectionRequests.add(module.path() + "." + className + " "
                + declaredClass.classId().text());
            if (!module.path().equals(FOCUSED_DOTTED) || !className.equals("Probe")
                    || !declaredClass.classId().text().equals(FOCUSED_PROBE_DESC)) {
                throw new IllegalStateException("the seam requested an unexpected"
                    + " plan projection: " + module.path() + "." + className + " "
                    + declaredClass.classId());
            }
            return List.of(
                new PlanEntry("a", RuntimeDescriptor.Int.INSTANCE, false,
                    this::evaluateA),
                new PlanEntry("b", RuntimeDescriptor.Int.INSTANCE, false,
                    this::evaluateB));
        }

        private SemanticOracle.Value evaluateA() {
            evaluatorLog.add("a");
            return new SemanticOracle.Value.IntValue(++counter);
        }

        private SemanticOracle.Value evaluateB() {
            evaluatorLog.add("b");
            return new SemanticOracle.Value.IntValue(++counter);
        }

        @Override
        public SyncOutcome call(ModuleId module, String export,
                RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
            calls.add(export);
            return switch (export) {
                case "fixture_count_call_int" -> {
                    evaluatorLog.add("native:count");
                    yield new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(++counter));
                }
                case "fixture_call_count" -> {
                    counterReads.add(counter);
                    yield new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(counter));
                }
                case "fixture_reset_counter" -> {
                    counter = 0;
                    yield new SyncOutcome.Returned(
                        SemanticOracle.Value.NullValue.INSTANCE);
                }
                default -> throw new IllegalStateException(
                    "the drive scripts no host terminal for " + export);
            };
        }
    }

    private static void testOmittedFieldParity() throws Exception {
        System.out.println("-- the omitted-field parity: one supplier per omitted"
            + " field per attempt in source order, the artifact's counter sequence,"
            + " and the artifact runtime-ok --");
        Path root = Files.createTempDirectory("ffi-plan-counting");
        try {
            Fixture fixture;
            try {
                fixture = compileFocused(root, "struct-counting", COUNTING_APP, true);
            } catch (IllegalStateException failure) {
                fail(failure.getMessage());
                return;
            }
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the focused fixture lowers: " + lowered.diagnostics());
                return;
            }
            ProbeResponder responder = new ProbeResponder();
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                lowered.project(), lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));

            checkEq(List.of(FOCUSED_DOTTED + ".Probe " + FOCUSED_PROBE_DESC,
                    FOCUSED_DOTTED + ".Probe " + FOCUSED_PROBE_DESC,
                    FOCUSED_DOTTED + ".Probe " + FOCUSED_PROBE_DESC),
                responder.projectionRequests,
                "the plan projection is requested once per construction attempt"
                    + " with the resolved module, the class name, and the class"
                    + " descriptor");
            checkEq(List.of("a", "b", "b", "a", "b"),
                responder.evaluatorLog,
                "one supplier per omitted field per attempt in class source order"
                    + " (a provided field suppresses exactly its own evaluator, and"
                    + " no evaluator runs at load)");
            checkEq(List.of(0, 2, 3, 5), responder.counterReads,
                "the counter reads observe the artifact's pinned sequence"
                    + " (zero at load, then the per-attempt evaluator counts)");
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle's counting drive succeeds (the fixture's own pinned"
                    + " assertions hold): " + run.terminal());

            // The oracle records each native counter read as the same host
            // value sequence the artifact's native implementation returns.
            List<String> counterReturns = new ArrayList<>();
            for (SemanticRuntimeModel.EffectEvent effect : run.effects()) {
                if (effect.kind() == SemanticRuntimeModel.EffectEvent.Kind.HOST_RETURN
                        && effect.text().startsWith(FOCUSED_DOTTED
                            + ".fixture_call_count=")) {
                    counterReturns.add(effect.text().substring(
                        effect.text().indexOf('=') + 1));
                }
            }
            checkEq(List.of("int:0", "int:2", "int:3", "int:5"), counterReturns,
                "the oracle's host returns carry the same counter values the"
                    + " artifact's native calls return");

            // The artifact parity: the same project through the production
            // artifact with the real generated evaluators.
            Path artifact = fixture.outputRoot().resolve(
                fixture.appFileName().replace(".deal", ".lua"));
            check(Files.isRegularFile(artifact),
                "the focused project publishes its production artifact: "
                    + artifact);
            if (Files.isRegularFile(artifact)) {
                String text = Files.readString(artifact, StandardCharsets.UTF_8);
                String region = constructionRegion(text,
                    "pcall(__rt.class_plan_, \"" + FOCUSED_PROBE_DESC + "\"");
                check(region.contains("__ffiClassPlan(\"" + FOCUSED_DOTTED
                        + "\", \"Probe\")"),
                    "the artifact constructs through the loaded Probe plan entry: "
                        + region);
                ProcessOutcome artifactRun = runProcess(
                    List.of("luajit", fixture.appFileName().replace(".deal", ".lua")),
                    fixture.outputRoot(), Map.of());
                check(artifactRun.exitCode() == 0,
                    "the artifact's real generated evaluators run the same counter"
                        + " sequence (exit 0): exit=" + artifactRun.exitCode()
                        + " stdout=" + escaped(artifactRun.stdout())
                        + " stderr=" + escaped(artifactRun.stderr()));
                check(run.terminal()
                        instanceof SemanticRuntimeModel.Terminal.Success
                        && artifactRun.exitCode() == 0,
                    "the oracle's events and outcome equal the artifact's");
            }
        } finally {
            deleteRecursively(root);
        }
    }

    /**
     * The recovery drive's application: the `broken` literal's provided field
     * is the doctored site (the guard raises E8007 after the declared provided
     * field's boundary child and before any default, so no deferred evaluator
     * runs for the failed attempt and no partial instance is published), and
     * the `after` literal's omitted fields re-execute the evaluators once the
     * attempt's own recovery completed.
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
          // The failed attempt ran no evaluator and published no instance:
          // the counter is unchanged, and the next attempt takes the first
          // values.
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

    private static void testDoctoredAttemptRecovery() throws Exception {
        System.out.println("-- the doctored attempt's recovery: the provided field's"
            + " boundary child, then the E8007 guard, then no default and no"
            + " partial instance; the recovered attempt evaluates once per omitted"
            + " field --");
        Path root = Files.createTempDirectory("ffi-plan-recovery");
        try {
            Fixture fixture;
            try {
                fixture = compileFocused(root, "struct-recovery", DOCTORED_APP, false);
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
            SemanticOp broken = null;
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
                }
            }
            check(broken != null, "the app's `broken` construction is in the"
                + " closure");
            if (broken == null) {
                return;
            }
            ExecutableLoweredProject doctored = doctoredProject(project,
                unitOf(project, broken), broken, List.of("zzz", "yyy"));
            ProbeResponder responder = new ProbeResponder();
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                doctored, lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));

            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the app catches the doctored attempt's E8007 and the recovered"
                    + " attempt succeeds: " + run.terminal());
            checkEq(List.of("a", "b"), responder.evaluatorLog,
                "no default runs for the failed attempt; the recovered attempt's"
                    + " two omitted fields evaluate once each in class source order");
            checkEq(List.of(0, 0, 2), responder.counterReads,
                "the failed attempt published nothing and ran no evaluator (the"
                    + " counter is unchanged), and the recovered attempt's"
                    + " evaluators advance it once each");

            List<SemanticRuntimeModel.TraceEvent> events = planEvents(run, broken);
            List<String> shape = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : events) {
                shape.add(eventShape(event));
            }
            checkEq(List.of("CLASS_NEW/START", "BOUNDARY/START", "BOUNDARY/SUCCESS",
                    "CLASS_NEW/FAILURE"),
                shape,
                "the failed construction runs the provided field's boundary child"
                    + " and then fails: " + shape);
            if (events.size() == 4) {
                check(events.get(3).error() != null
                        && "E8007".equals(events.get(3).error().code()),
                    "the failed construction's terminal is the E8007 guard: "
                        + (events.get(3).error() == null ? "null"
                            : events.get(3).error().code()));
                check(events.get(3).error() != null
                        && ("extra field 'zzz' in class '" + FOCUSED_PROBE_DESC + "'")
                            .equals(events.get(3).error().message()),
                    "the failed construction's terminal names the first"
                        + " provided-source extra: "
                        + (events.get(3).error() == null ? "null"
                            : events.get(3).error().message()));
            }
        } finally {
            deleteRecursively(root);
        }
    }

    /** The source line named by one 1-based line number. */
    private static String sourceLine(String source, int line) {
        String[] lines = source.split("\n", -1);
        return line >= 1 && line <= lines.length ? lines[line - 1] : "";
    }

    /**
     * One project copy with the named construction's provided-field list
     * extended by the extra names (each reusing the construction's first
     * provided value prior step).
     */
    private static ExecutableLoweredProject doctoredProject(
            ExecutableLoweredProject project, LoweredModuleUnit unit,
            SemanticOp target, List<String> extraFields) {
        KindPayload.ClassNewPayload payload =
            (KindPayload.ClassNewPayload) target.payload();
        ValueId reused = payload.fieldBoundaries().isEmpty()
            ? firstValueId(unit)
            : ((KindPayload.BoundaryPayload) opOf(project,
                payload.fieldBoundaries().get(0).boundaryOpId()).payload()).input();
        List<KindPayload.ProvidedField> extended =
            new ArrayList<>(payload.providedFields());
        for (String name : extraFields) {
            extended.add(new KindPayload.ProvidedField(name, reused));
        }
        KindPayload.ClassNewPayload doctored = new KindPayload.ClassNewPayload(
            payload.classId(), payload.layout(), extended, payload.defaultOwner(),
            payload.classDefaultOpIds(), payload.classFactoryRef(),
            payload.fieldBoundaries());
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        ops.set(ops.indexOf(target), rebuildOp(target, doctored));
        Map<ModuleId, LoweredModuleUnit> modules =
            new LinkedHashMap<>(project.modules());
        modules.put(unit.moduleId(), withOps(unit, ops));
        return new ExecutableLoweredProject(project.semanticProfile(),
            project.interfaceIndex(), modules, project.entryModule());
    }

    /** The first published value id of one unit. */
    private static ValueId firstValueId(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId id) {
                return id;
            }
        }
        throw new IllegalStateException("the unit publishes no value to reuse");
    }

    // =========================================================================
    // 3. The projection agreement negatives
    // =========================================================================

    /** One responder returning a doctored plan projection. */
    private static SemanticOracle.HostResponder projectionResponder(
            List<SemanticOracle.HostResponder.PlanEntry> projection) {
        return new SemanticOracle.HostResponder() {
            @Override
            public List<PlanEntry> planProjection(ModuleId module, String className,
                    RuntimeDescriptor.Class declaredClass) {
                return projection;
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                throw new IllegalStateException("the agreement drives make no host"
                    + " call (got " + export + ")");
            }
        };
    }

    private static SemanticOracle.HostResponder.PlanEntry entry(String name,
            RuntimeDescriptor descriptor, List<String> evaluatorLog) {
        return new SemanticOracle.HostResponder.PlanEntry(name, descriptor, false,
            () -> {
                evaluatorLog.add(name);
                return new SemanticOracle.Value.IntValue(1);
            });
    }

    private static void testProjectionAgreementNegatives() throws Exception {
        System.out.println("-- the projection agreement: a mutated order, a mutated"
            + " descriptor, a short projection, and an absent projection fail"
            + " closed before any phase --");
        Path root = Files.createTempDirectory("ffi-plan-agreement");
        try {
            Fixture fixture;
            try {
                fixture = compileFocused(root, "struct-agreement", OMITTED_APP, false);
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

            // The agreement runs before any phase: the deferred suppliers
            // are the canary, and they must never be invoked.
            List<String> swappedLog = new ArrayList<>();
            expectOracleDefect(project, lowered, projectionResponder(List.of(
                    entry("b", RuntimeDescriptor.Int.INSTANCE, swappedLog),
                    entry("a", RuntimeDescriptor.Int.INSTANCE, swappedLog))),
                "plan entry 0",
                "a mutated entry order");
            check(swappedLog.isEmpty(),
                "a mutated entry order runs no phase (the suppliers never ran): "
                    + swappedLog);

            List<String> descriptorLog = new ArrayList<>();
            expectOracleDefect(project, lowered, projectionResponder(List.of(
                    entry("a", RuntimeDescriptor.Number.INSTANCE, descriptorLog),
                    entry("b", RuntimeDescriptor.Int.INSTANCE, descriptorLog))),
                "seed layout's field 'a'",
                "a mutated descriptor");

            List<String> shortLog = new ArrayList<>();
            expectOracleDefect(project, lowered, projectionResponder(List.of(
                    entry("a", RuntimeDescriptor.Int.INSTANCE, shortLog))),
                "projects 1 plan entries",
                "a short projection");
            check(shortLog.isEmpty(),
                "a short projection runs no phase (the suppliers never ran): "
                    + shortLog);

            // The absent projection is the fail-closed producer defect.
            expectOracleDefect(project, lowered, projectionResponder(null),
                "without the loaded plan projection",
                "an absent projection");
        } finally {
            deleteRecursively(root);
        }
    }

    private static void expectOracleDefect(ExecutableLoweredProject project,
            SemanticLowerer.ProjectLoweringResult lowered,
            SemanticOracle.HostResponder responder, String needle, String what) {
        try {
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));
            fail(what + " did not fail closed (terminal " + run.terminal() + ")");
        } catch (IllegalStateException | ClassOpsExecutor.Defect expected) {
            check(expected.getMessage() != null
                    && expected.getMessage().contains(needle),
                what + " fails closed naming '" + needle + "': "
                    + expected.getMessage());
        }
    }

    // =========================================================================
    // 4. The phase-3 descriptor projections
    // =========================================================================

    private static void testPhaseThreeProjections() throws Exception {
        System.out.println("-- the phase-3 descriptor checks: a wrong-kind"
            + " plan-supplied default raises E8001 and an out-of-range integral"
            + " number raises E8004 at the literal origin --");
        Path root = Files.createTempDirectory("ffi-plan-phase3");
        try {
            Fixture fixture;
            try {
                fixture = compileFocused(root, "struct-phase3", OMITTED_APP, false);
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
            SemanticOp construction = constructionOf(project);
            String origin = construction.origin().sourceId() + ":"
                + construction.origin().span().startLine() + ":"
                + construction.origin().span().startColumn();

            SemanticOracle.HostResponder fractional =
                defaultResponder(new SemanticOracle.Value.NumValue(2.5),
                    new SemanticOracle.Value.IntValue(2));
            SemanticRuntimeModel.ConsumerRun wrongKind =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), fractional, declarationLayouts(lowered));
            check(wrongKind.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the wrong-kind plan default fails the run: "
                    + wrongKind.terminal());
            if (wrongKind.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure) {
                checkEq("E8001", failure.error().code(),
                    "the wrong-kind plan default raises E8001");
                checkEq("expected int, got non-integer number",
                    failure.error().message(),
                    "the E8001 text is the canonical matcher's");
                checkEq(origin, failure.error().origin(),
                    "the E8001 origin is the literal origin");
            }

            SemanticOracle.HostResponder outOfRange =
                defaultResponder(new SemanticOracle.Value.NumValue(3000000000.0),
                    new SemanticOracle.Value.IntValue(2));
            SemanticRuntimeModel.ConsumerRun overRange =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), outOfRange, declarationLayouts(lowered));
            check(overRange.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the out-of-range plan default fails the run: "
                    + overRange.terminal());
            if (overRange.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure) {
                checkEq("E8004", failure.error().code(),
                    "the out-of-range plan default raises E8004");
                checkEq("int out of safe range", failure.error().message(),
                    "the E8004 text is the canonical matcher's");
                checkEq(origin, failure.error().origin(),
                    "the E8004 origin is the literal origin");
            }
        } finally {
            deleteRecursively(root);
        }
    }

    private static void testEvaluatorFailurePropagation() throws Exception {
        System.out.println("-- the deferred-default proxy's own failure crosses as"
            + " that exact DEAL failure and publishes no instance; the later"
            + " field's supplier never runs --");
        Path root = Files.createTempDirectory("ffi-plan-evaluator-failure");
        try {
            Fixture fixture;
            try {
                fixture = compileFocused(root, "struct-evaluator-failure",
                    OMITTED_APP, false);
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
            SemanticOp construction = constructionOf(project);
            String origin = construction.origin().sourceId() + ":"
                + construction.origin().span().startLine() + ":"
                + construction.origin().span().startColumn();
            List<String> log = new ArrayList<>();
            SemanticOracle.HostResponder responder =
                new SemanticOracle.HostResponder() {
                    @Override
                    public List<PlanEntry> planProjection(ModuleId module,
                            String className, RuntimeDescriptor.Class declaredClass) {
                        return List.of(
                            new PlanEntry("a", RuntimeDescriptor.Int.INSTANCE, false,
                                () -> {
                                    log.add("a");
                                    throw SemanticOracle.evaluatorFailure("E8001",
                                        "the Probe.a evaluator's host call failed",
                                        construction.origin());
                                }),
                            new PlanEntry("b", RuntimeDescriptor.Int.INSTANCE, false,
                                () -> {
                                    log.add("b");
                                    return new SemanticOracle.Value.IntValue(2);
                                }));
                    }

                    @Override
                    public SyncOutcome call(ModuleId module, String export,
                            RuntimeDescriptor.Func descriptor,
                            List<SemanticOracle.Value> args) {
                        throw new IllegalStateException("the evaluator-failure drive"
                            + " makes no host call (got " + export + ")");
                    }
                };
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));
            check(run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the failing evaluator proxy fails the run: " + run.terminal());
            if (run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure) {
                checkEq("E8001", failure.error().code(),
                    "the evaluator's own code crosses unchanged");
                checkEq("the Probe.a evaluator's host call failed",
                    failure.error().message(),
                    "the evaluator's own message crosses unchanged");
                checkEq(origin, failure.error().origin(),
                    "the evaluator's own origin crosses unchanged");
            }
            checkEq(List.of("a"), log,
                "the failing evaluator's later sibling never runs (class source"
                    + " order, one supplier per attempt) and no instance is"
                    + " published");
        } finally {
            deleteRecursively(root);
        }
    }

    /** One responder projecting the Probe plan with scripted default values. */
    private static SemanticOracle.HostResponder defaultResponder(
            SemanticOracle.Value a, SemanticOracle.Value b) {
        return new SemanticOracle.HostResponder() {
            @Override
            public List<PlanEntry> planProjection(ModuleId module, String className,
                    RuntimeDescriptor.Class declaredClass) {
                return List.of(
                    new PlanEntry("a", RuntimeDescriptor.Int.INSTANCE, false, () -> a),
                    new PlanEntry("b", RuntimeDescriptor.Int.INSTANCE, false, () -> b));
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                throw new IllegalStateException("the descriptor drives make no host"
                    + " call (got " + export + ")");
            }
        };
    }

    // =========================================================================
    // 5. The doctored extra-key parity
    // =========================================================================

    private static void testDoctoredExtraKeyParity() throws Exception {
        System.out.println("-- a doctored CLASS_NEW(FFI_PLAN) payload yields the"
            + " identical E8007 through the oracle and the artifact --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp construction = constructionOf(project);

            // The doctored payload: the two declared provided fields plus
            // the extra names zzz and yyy, each reusing the first provided
            // value's prior step (the runtime arm defends the boundary
            // payload the validator rejects).
            ExecutableLoweredProject doctoredProject = doctoredProject(project,
                unitOf(project, construction), construction, List.of("zzz", "yyy"));

            PairResponder responder = new PairResponder();
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                doctoredProject, lowered.tables(), lowered.registries(), responder,
                declarationLayouts(lowered));
            check(run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the doctored construction fails the oracle run: "
                    + run.terminal());
            String expectedMessage = "extra field 'zzz' in class '" + PAIR_DESC + "'";
            String expectedOrigin = construction.origin().sourceId() + ":"
                + construction.origin().span().startLine() + ":"
                + construction.origin().span().startColumn();
            if (run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure) {
                checkEq("E8007", failure.error().code(),
                    "the doctored construction raises E8007 through the oracle");
                checkEq(expectedMessage, failure.error().message(),
                    "the oracle's E8007 names the first provided-source extra");
                checkEq(expectedOrigin, failure.error().origin(),
                    "the oracle's E8007 origin is the literal origin");
            }
            check(responder.evaluatorInvocations.isEmpty(),
                "the guard runs before any default (no supplier ran): "
                    + responder.evaluatorInvocations);

            // The artifact parity: the same doctored construction emitted
            // and executed under luajit reports the identical error facts.
            Path out = fixture.root().resolve("out-doctored");
            emitDoctored(fixture, lowered, doctoredProject, out);
            ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"), out,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(probe.exitCode() == 0,
                "the doctored artifact's failure probe runs: exit="
                    + probe.exitCode() + " stdout=" + escaped(probe.stdout())
                    + " stderr=" + escaped(probe.stderr()));
            if (probe.exitCode() == 0) {
                String[] lines = probe.stdout().trim().split("\\n", -1);
                String[] parts = lines[0].split("\\|", -1);
                checkEq("ERR", parts.length > 0 ? parts[0] : null,
                    "the doctored artifact raises a DEAL error");
                checkEq("E8007", parts.length > 1 ? parts[1] : null,
                    "the doctored artifact raises E8007");
                checkEq(expectedMessage, parts.length > 2 ? parts[2] : null,
                    "the artifact's E8007 names the first provided-source extra");
                checkEq(expectedOrigin, parts.length > 5
                        ? parts[3] + ":" + parts[4] + ":" + parts[5] : null,
                    "the artifact's E8007 origin is the literal origin");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** Emits the doctored project and materializes its failure probe. */
    private static void emitDoctored(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult lowered,
            ExecutableLoweredProject doctoredProject, Path out) throws Exception {
        String chunk = LuaSemanticEmitter.emitProductionProject(doctoredProject,
            lowered.tables(), lowered.registries(), fixture.surface(),
            new FfiEmissionInput(fixture.externCModules(),
                fixture.root().toString()));
        Files.createDirectories(out.resolve("deal"));
        Files.copy(Path.of("deal", "runtime.lua"),
            out.resolve("deal").resolve("runtime.lua"));
        Files.writeString(out.resolve(CORPUS_CASE + ".lua"), chunk,
            StandardCharsets.UTF_8);
        Files.writeString(out.resolve("probe.lua"),
            failureProbe(CORPUS_CASE + ".lua"), StandardCharsets.UTF_8);
    }

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

    // =========================================================================
    // 6. The surface's closed owner set
    // =========================================================================

    private static void testSurfaceRejectsForeignOwners() throws Exception {
        System.out.println("-- the FFI-plan executor surface accepts only FFI_PLAN;"
            + " every other owner, a factory ref, a default child list, and an"
            + " absent projection are producer defects --");
        Fixture fixture = compileCorpus();
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            SemanticOp construction = constructionOf(project);
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) construction.payload();
            LoweredModuleUnit unit = unitOf(project, construction);

            // The provided values' prior steps resolve with any closed-view
            // value: a foreign owner is rejected before phase 1 reads them.
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                priorValues.put(field.valueOpId(), new ClassOpsExecutor.Value.Int(0));
            }
            Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY) {
                    boundaryOps.put(op.opId(), op);
                }
            }
            ClassLayout layout = payload.layout();
            Map<ClassId, ClassLayout> layouts = declarationLayouts(lowered);

            List<ClassOpsExecutor.FfiPlanEntry> plan = List.of(
                new ClassOpsExecutor.FfiPlanEntry("left",
                    RuntimeDescriptor.Int.INSTANCE, false,
                    () -> new ClassOpsExecutor.Value.Int(0)),
                new ClassOpsExecutor.FfiPlanEntry("right",
                    RuntimeDescriptor.Int.INSTANCE, false,
                    () -> new ClassOpsExecutor.Value.Int(0)));
            ClassOpsExecutor.FfiPlanCheckRunner pass = (boundary, descriptor, input) ->
                new ClassOpsExecutor.BoundaryResult.Pass(input);

            for (DefaultOwner owner : List.of(DefaultOwner.LOCAL,
                    DefaultOwner.SHARED_FACTORY, DefaultOwner.HOST_DEFAULTS,
                    DefaultOwner.BUILTIN_DEFAULTS, DefaultOwner.RETAINED_ABI)) {
                SemanticOp foreign = rebuildOp(construction,
                    new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                        payload.providedFields(), owner, payload.classDefaultOpIds(),
                        payload.classFactoryRef(), payload.fieldBoundaries()));
                expectDefect(() -> ClassOpsExecutor.executeClassNewFfiPlan(foreign,
                        priorValues, boundaryOps, layouts, plan, pass),
                    "foreign owner reaching executeClassNewFfiPlan",
                    "the " + owner + " owner");
            }
            expectDefect(() -> ClassOpsExecutor.executeClassNewFfiPlan(
                    rebuildOp(construction, new KindPayload.ClassNewPayload(
                        payload.classId(), payload.layout(), payload.providedFields(),
                        payload.defaultOwner(), payload.classDefaultOpIds(),
                        new deal.semantic.ir.ClassFactoryId(0),
                        payload.fieldBoundaries())),
                    priorValues, boundaryOps, layouts, plan, pass),
                "non-null classFactoryRef", "a non-null factory ref");
            expectDefect(() -> ClassOpsExecutor.executeClassNewFfiPlan(
                    rebuildOp(construction, new KindPayload.ClassNewPayload(
                        payload.classId(), payload.layout(), payload.providedFields(),
                        payload.defaultOwner(), List.of(construction.opId()),
                        payload.classFactoryRef(), payload.fieldBoundaries())),
                    priorValues, boundaryOps, layouts, plan, pass),
                "empty default-op list", "a non-empty default-op list");
            expectDefect(() -> ClassOpsExecutor.executeClassNewFfiPlan(construction,
                    priorValues, boundaryOps, layouts, null, pass),
                "without the loaded plan projection", "an absent projection");
            checkEq(layout, payload.layout(),
                "the surface drives the realized corpus construction layout");
            ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> accepted =
                ClassOpsExecutor.executeClassNewFfiPlan(construction, priorValues,
                    boundaryOps, layouts, plan, pass);
            check(accepted instanceof ClassOpsExecutor.Outcome.Success
                        <ClassOpsExecutor.Value> success
                    && success.value() instanceof ClassOpsExecutor.Value.Class instance
                    && instance.classId().equals(payload.classId())
                    && instance.fields().size() == 2,
                "the surface accepts the realized FFI_PLAN construction: " + accepted);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void expectDefect(Runnable drive, String needle, String what) {
        try {
            drive.run();
            fail(what + " did not fail closed");
        } catch (ClassOpsExecutor.Defect | IllegalStateException expected) {
            check(expected.getMessage() != null
                    && expected.getMessage().contains(needle),
                what + " fails closed naming '" + needle + "': "
                    + expected.getMessage());
        }
    }

    // =========================================================================
    // Op/unit rebuild helpers
    // =========================================================================

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
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

    /**
     * The emitted construction region of one C-struct site: from the
     * site's provided-table initialization to its result projection.
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

    // =========================================================================
    // Gate
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Plan Projection Oracle Tests (ISSUE-0667) ===");
        System.out.println();
        testProvidedOnlyParity();
        testOmittedFieldParity();
        testDoctoredAttemptRecovery();
        testProjectionAgreementNegatives();
        testPhaseThreeProjections();
        testEvaluatorFailurePropagation();
        testDoctoredExtraKeyParity();
        testSurfaceRejectsForeignOwners();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Plan Projection Oracle Tests Passed ===");
    }
}
