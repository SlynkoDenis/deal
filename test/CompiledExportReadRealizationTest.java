package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

/**
 * ISSUE-0646: the compiled export read realization across the three
 * consumers plus the oracle's per-run published-surface registry
 * (design source
 * {@code module-export-reads-and-in-project-class-construction} M2, M3,
 * M6, the read execution contract, and the export-read contract;
 * {@code semantic-ir-construct-coverage-cutover} K2;
 * {@code luajit-jvm-single-lowering-production-cutover} C1/C2).
 *
 * <ol>
 *   <li><b>The emitted read (M2/M6).</b> A probe project whose entry
 *       reads a compiled companion's declared function export twice into
 *       function-typed bindings (no cross-module invocation) lowers
 *       through the one project entry and validates. Both project
 *       sessions emit the same read operation parameterized only by the
 *       mode flag: the LuaJIT read is the nil-safe accessor of the
 *       program-scoped surface registry resolving the publication
 *       entry's compiler-owned {@code __val} field, the JVM read is the
 *       uniform {@code exportSurface(module).read(name)} over the
 *       runtime-hosted program registry, and the STDLIB/HOST placeholder
 *       text never appears in the read arm. The publication entry keeps
 *       the retained-caller ABI's raw callable under {@code f} and gains
 *       {@code __val} beside it. Repeated emissions are byte-identical.</li>
 *   <li><b>The oracle read realization (M3).</b> The full project drive
 *       records each module's published surface and resolves the
 *       COMPILED read from it: the read's trace SUCCESS atom equals the
 *       publication's own atom (the published value's creation
 *       allocation — no fresh allocation), both reads publish the
 *       identical value, the {@code export:<module>.<name>} placeholder
 *       is gone, and the value-keyed binding map stays the producing
 *       allocation's (the owner unit keeps the {@code LoweredBody}
 *       registration keyed by the published value's identity; the read's
 *       own {@code ExternalFunction(SHARED_BODY)} registration stays
 *       addressable by the read result's identity). A doctored
 *       re-keying of the shared value onto the read's identity fails the
 *       closed gate.</li>
 *   <li><b>The absent-slot projection in all three consumers.</b> The
 *       landed partial-drive state (only the entry module initialized)
 *       projects {@code Value.MissingValue} / {@code __MISSING} /
 *       {@code JvmRuntime.MISSING} — all atomizing as {@code missing} —
 *       so the landed async-entry matrix stays green unmodified.</li>
 *   <li><b>The three-consumer trace matrix.</b> The probe project runs
 *       through the semantic oracle and both shared artifacts under the
 *       real toolchains; every consumer's two read SUCCESS atoms equal
 *       each other and the publication's atom, and the differential
 *       verdict passes event-for-event.</li>
 *   <li><b>The per-unit program-scoped registry.</b> A per-unit
 *       (per-chunk / per-class) drive resolves the owner's published
 *       value after the owner artifact ran: the two reads publish the
 *       identical object, and the JVM class-level
 *       {@code EXPORT_SURFACES} view is the runtime-hosted registry
 *       instance the owner published into (never a session-local map).</li>
 *   <li><b>The production artifacts.</b> The production arm stages one
 *       project artifact per target; the LuaJIT chunk runs under
 *       {@code luajit} and the JVM class compiles with
 *       {@code javac --release 25 -proc:none} and runs under
 *       {@code java}. The emitted read resolves the surface entry, the
 *       published entry's {@code .f}/{@code .fn} projection still calls
 *       the module function, the JVM read value is the published
 *       {@code JvmRuntime.FunctionValue} carrier object, and the
 *       class-level field view resolves the program registry.</li>
 *   <li><b>The project-session ownership guard.</b> A COMPILED read whose
 *       owner module is not among a project session's units fails the
 *       emission closed (both targets); a per-unit session never fails
 *       closed for a foreign owner; the production arm realizes this
 *       fixture's cross-module sync call through the {@code CALL(EXTERNAL)}
 *       {@code SHARED_BODY} arm (ISSUE-0654) and stages its one project
 *       artifact; the emitter-side rejections of hand-built inconsistent
 *       facts (asserted by the calls child's focused suite) feed the
 *       production arm's fail-closed E6005 {@code SHARED_EMITTER_COVERAGE}
 *       mapping, which stages nothing.</li>
 * </ol>
 */
public class CompiledExportReadRealizationTest {

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
    // The fixture: a two-module project whose entry reads the compiled
    // companion's declared function export (no cross-module invocation)
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId APP = new ModuleId("app");
    private static final String EXPORT_NAME = "tag";
    private static final String EXPORT_SPEC = "(int)->string";

    private static final String LIB_SOURCE = """
        export function tag(v: int): string {
          return "t";
        }
        """;

    private static final String APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let f: (v: int) => string = lib.tag
          let g: (v: int) => string = lib.tag
          return null
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome) {
    }

    /** The harness invocation of the fixture compile (the arm builds either way). */
    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** The release-owned production invocation this leaf's unit is driven with. */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        Path root = Files.createTempDirectory("compiled-read-probe");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), new LinkedHashMap<>(),
            new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(src.toString()));
    }

    private static Fixture twoModuleFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", LIB_SOURCE);
        sources.put("src/app.deal", APP_SOURCE);
        return compileProject(sources);
    }

    /** The one project lowering over the real checked project. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    private static SemanticIrValidator.ComparisonFacts facts(Fixture fixture) {
        return new SemanticIrValidator.ComparisonFacts(
            fixture.index().interfaceIndexDigest(), SemanticProfile.DEAL_V1_2_INT32,
            productionInvocation().capabilityRegistryHash());
    }

    /** One copy of a block-membership table with a publication op repeated. */
    private static Map<deal.semantic.ir.BlockId, List<OpId>> duplicatedPublishTable(
            StructuredBodyTable table, OpId publishOp) {
        Map<deal.semantic.ir.BlockId, List<OpId>> blocks =
            new LinkedHashMap<>(table.blockOps());
        for (Map.Entry<deal.semantic.ir.BlockId, List<OpId>> entry : blocks.entrySet()) {
            if (!entry.getValue().contains(publishOp)) {
                continue;
            }
            List<OpId> doubled = new ArrayList<>(entry.getValue());
            doubled.add(publishOp);
            blocks.put(entry.getKey(), doubled);
            return blocks;
        }
        return blocks;
    }

    // =========================================================================
    // Op helpers
    // =========================================================================

    private static List<SemanticOp> readsOf(LoweredModuleUnit unit) {
        List<SemanticOp> reads = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXPORT_READ) {
                reads.add(op);
            }
        }
        return reads;
    }

    private static KindPayload.ExportReadPayload readPayload(SemanticOp read) {
        return (KindPayload.ExportReadPayload) read.payload();
    }

    private static SemanticOp publishOpOf(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                return op;
            }
        }
        return null;
    }

    /** The MODULE_EXPORT boundary child of one publication op, or null. */
    private static SemanticOp exportBoundaryOf(LoweredModuleUnit unit, OpId publishOp) {
        for (SemanticOp candidate : unit.ops()) {
            if (candidate.kind() != SemanticOpKind.BOUNDARY) {
                continue;
            }
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) candidate.payload();
            if (publishOp.equals(candidate.origin().parentOpId())
                    && payload.kind() == deal.semantic.ir.BoundaryKind.MODULE_EXPORT) {
                return candidate;
            }
        }
        return null;
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit, ValueId value) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + needle.length());
        }
        return count;
    }

    // =========================================================================
    // 1. The emitted read: both project sessions, one read operation
    // =========================================================================

    static void testEmittedReadOperation() throws Exception {
        System.out.println("-- the emitted read: both project sessions carry the one "
            + "surface-resolving read operation --");
        Fixture fixture = twoModuleFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(!result.hasErrors() && result.project() != null,
                "the probe project lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(Optional.empty(), SemanticIrValidator.validate(project, facts(fixture)),
                "the lowered project passes the closed project gate");
            checkEq(List.of(LIB, APP), List.copyOf(project.modules().keySet()),
                "the closure carries the companion then the entry module");
            Map<ModuleId, StructuredBodyTable> tables = result.tables();
            Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> registries =
                result.registries();

            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            List<SemanticOp> reads = readsOf(appUnit);
            checkEq(2, reads.size(),
                "the entry unit carries exactly one EXPORT_READ per source occurrence");
            for (SemanticOp read : reads) {
                KindPayload.ExportReadPayload payload = readPayload(read);
                check(payload.module().equals(LIB) && payload.name().equals(EXPORT_NAME)
                        && payload.descriptor().canonicalSpecText().equals(EXPORT_SPEC),
                    "the read names the compiled companion's declared function export "
                        + "with the checked descriptor; got " + payload.module() + "/"
                        + payload.name() + " " + payload.descriptor().canonicalSpecText());
                check(bindingOf(appUnit, payload.value())
                        instanceof FunctionExecutionBinding.ExternalFunction external
                        && external.moduleId().equals(LIB)
                        && external.exportName().equals(EXPORT_NAME)
                        && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                    "exactly one ExternalFunction(compiled module, tag, descriptor, "
                        + "SHARED_BODY) registration keyed by the read's result identity; "
                        + "got " + bindingOf(appUnit, payload.value()));
            }
            // The value-position arm is the read's producer (the combined
            // T2 + this leaf composition): the read is threaded into the
            // function-typed binding cell of its `let`, and the owner-side
            // registration keyed by the published value's identity — the
            // creation allocation — stays the owner's LoweredBody (the
            // read never re-keys it).
            SemanticOp publish = publishOpOf(libUnit);
            check(publish != null, "the companion publishes its declared export");
            if (publish == null) {
                return;
            }
            KindPayload.ExportPublishPayload publishPayload =
                (KindPayload.ExportPublishPayload) publish.payload();
            check(bindingOf(libUnit, publishPayload.value())
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the owner-side registration of the published value is the owner's "
                    + "LoweredBody, keyed by the published value's creation identity; got "
                    + bindingOf(libUnit, publishPayload.value()));
            check(appUnit.functionBindings().keySet().stream().noneMatch(key ->
                    key.id() == publishPayload.value().id()),
                "no read registration is keyed by the shared published value's identity "
                    + "(the read's registration stays addressable by the read result's "
                    + "allocation identity)");

            // The LuaJIT emission: the __val publication field, the
            // nil-safe accessor read, the unchanged f projection.
            String traceLua = LuaSemanticEmitter.emitProject(project, tables, registries);
            String productionLua = LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface());
            String publication = "__exportSurfaces[\"lib\"][\"tag\"] = "
                + "{__kind = \"function\", sig = \"" + EXPORT_SPEC + "\", f = __unfn(S.v"
                + publishPayload.value().id() + "), __val = S.v"
                + publishPayload.value().id() + "}";
            checkEq(1, countOccurrences(traceLua, publication),
                "the trace-mode publication writes the landed entry shape plus the "
                    + "compiler-owned __val field: " + publication);
            checkEq(1, countOccurrences(productionLua, publication),
                "the production publication writes the same entry shape");
            check(traceLua.contains("local function __exportValue(module, name)"),
                "the prelude carries the nil-safe program-scoped surface accessor");
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                String assignment = "S.v" + id + " = __exportValue(\"lib\", \"tag\")";
                checkEq(1, countOccurrences(traceLua, assignment),
                    "the trace-mode read resolves the surface entry's __val: " + assignment);
                checkEq(1, countOccurrences(productionLua, assignment),
                    "the production read operation is the identical surface lookup: "
                        + assignment);
                check(!traceLua.contains("S.v" + id + " = __intrinsicFn()"),
                    "the compiled read is never the landed placeholder arm");
            }
            checkEq(traceLua, LuaSemanticEmitter.emitProject(project, tables, registries),
                "the repeated trace-mode project emission is byte-identical");

            // The JVM emission: the uniform program-scoped surface read over
            // the class-level view of the runtime-hosted registry.
            JvmSemanticEmitter.EmissionResult traceJvm = JvmSemanticEmitter.emitProject(
                project, tables, registries);
            JvmSemanticEmitter.EmissionResult productionJvm =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    JvmBackend.classNameFor(APP.path()), fixture.surface());
            check(productionJvm.source().contains(
                    "static final java.util.LinkedHashMap<String, JvmRuntime.Table> "
                        + "EXPORT_SURFACES = JvmRuntime.EXPORT_SURFACES;"),
                "the emitted class's field is the compatible class-level view of the "
                    + "runtime-hosted program-scoped registry");
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                String assignment = "v" + id + " = exportSurface(\"lib\").read(\"tag\");";
                checkEq(1, countOccurrences(traceJvm.source(), assignment),
                    "the trace-mode JVM read is the uniform surface read: " + assignment);
                checkEq(1, countOccurrences(productionJvm.source(), assignment),
                    "the production JVM read operation is the identical surface read: "
                        + assignment);
                check(!traceJvm.source().contains("v" + id + " = new JvmRuntime.Intrinsic()"),
                    "the compiled read is never the landed JVM placeholder arm");
            }
            checkEq(productionJvm.source(), JvmSemanticEmitter.emitProductionProject(
                    project, tables, registries, JvmBackend.classNameFor(APP.path()),
                    fixture.surface()).source(),
                "the repeated production project emission is byte-identical");

            // The interim boundary: no STDLIB/HOST read exists in this
            // fixture, so the placeholder arms are untouched by this leaf.
            check(appUnit.ops().stream().noneMatch(op ->
                    op.kind() == SemanticOpKind.MODULE_IMPORT
                        && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                            != ModuleImportKind.COMPILED),
                "the probe closure imports the compiled companion only");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The oracle read realization and the value-keyed invariant
    // =========================================================================

    static void testOracleReadRealization() throws Exception {
        System.out.println("-- the oracle: the per-run published-surface registry, the "
            + "COMPILED resolution, and the value-keyed invariant --");
        Fixture fixture = twoModuleFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            SemanticOp publish = publishOpOf(libUnit);
            SemanticOp boundary = exportBoundaryOf(libUnit, publish.opId());
            List<SemanticOp> reads = readsOf(appUnit);
            check(boundary != null, "the publication carries its MODULE_EXPORT child");

            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the full project drive succeeds: " + run.terminal());
            String publicationAtom = null;
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.op().equals(boundary.opId())
                        && event.phase() == SemanticRuntimeModel.Phase.START
                        && !event.inputs().isEmpty()) {
                    publicationAtom = event.inputs().get(0);
                }
            }
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the publication boundary's input atom is the published value's creation "
                    + "allocation; got " + publicationAtom);
            List<String> readAtoms = new ArrayList<>();
            for (SemanticOp read : reads) {
                for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                    if (event.op().equals(read.opId())
                            && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        readAtoms.add(event.output());
                    }
                }
            }
            checkEq(2, readAtoms.size(),
                "both reads execute and publish exactly one terminal each");
            checkEq(publicationAtom, readAtoms.get(0),
                "the read's trace SUCCESS atom is the published value's creation atom "
                    + "(no fresh allocation)");
            checkEq(readAtoms.get(0), readAtoms.get(1),
                "two reads of one export publish the identical value object");
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                check(event.output() == null || !event.output().startsWith("export:"),
                    "no export:<module>.<name> placeholder atom remains in the oracle "
                        + "trace: " + event.output());
            }

            // The absent-slot projection of the landed partial drive: the
            // entry-only walk resolves no surface entry, so the read
            // publishes Value.MissingValue (atomizing as missing); the
            // function-typed binding boundary then rejects the absent-slot
            // value with the pinned E8001 (a state a full execution never
            // reaches).
            SemanticRuntimeModel.ConsumerRun partial = SemanticOracle.execute(project,
                result.tables(), result.registries(), null);
            List<String> partialAtoms = new ArrayList<>();
            for (SemanticOp read : reads) {
                for (SemanticRuntimeModel.TraceEvent event : partial.trace()) {
                    if (event.op().equals(read.opId())
                            && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        partialAtoms.add(event.output());
                    }
                }
            }
            checkEq(List.of("missing"), partialAtoms,
                "an entry-only drive projects the absent-slot value for the compiled "
                    + "read (Value.MissingValue, atomizing as missing)");
            check(partial.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                    failure && "E8001".equals(failure.error().code()),
                "the entry-only drive fails at the function-typed binding boundary (the "
                    + "absent-slot value is never an invocation target): "
                    + partial.terminal());

            // The publication record is written exactly once per export per
            // run: a doctored walk that publishes one name twice is a
            // producer defect, never a silent rewrite.
            StructuredBodyTable doctoredTable = new StructuredBodyTable(
                duplicatedPublishTable(result.tables().get(LIB), publish.opId()),
                result.tables().get(LIB).opBlocks());
            RuntimeException doublePublish = null;
            try {
                SemanticOracle.executeProjectInits(project,
                    Map.of(LIB, doctoredTable, APP, result.tables().get(APP)),
                    result.registries(), null);
            } catch (RuntimeException expected) {
                doublePublish = expected;
            }
            check(doublePublish instanceof IllegalStateException
                    && doublePublish.getMessage().contains("published twice"),
                "a second publication of one name in one run is a producer defect: "
                    + (doublePublish == null ? "no failure" : doublePublish.getMessage()));

            // The value-keyed binding invariant, both directions: the
            // owner's producing allocation keeps its LowedBody
            // registration, the read's own identity carries the external
            // registration, and a doctored re-keying of the shared value
            // fails the closed gate.
            ValueId publishedValue = ((KindPayload.ExportPublishPayload) publish.payload())
                .value();
            check(bindingOf(libUnit, publishedValue)
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the owner-side runtime resolution of the published value stays the "
                    + "owner's LoweredBody");
            KindPayload.ExportReadPayload first = readPayload(reads.get(0));
            check(bindingOf(appUnit, first.value())
                    instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                "the read's registration stays addressable by the read result's "
                    + "allocation identity");
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> doctored =
                new LinkedHashMap<>(appUnit.functionBindings());
            doctored.remove(new FunctionAllocationIdentity(first.value().id()));
            doctored.put(new FunctionAllocationIdentity(publishedValue.id()),
                new FunctionExecutionBinding.ExternalFunction(LIB, EXPORT_NAME,
                    (deal.semantic.ir.RuntimeDescriptor.Func) first.descriptor(),
                    ExternalExecutionOwner.SHARED_BODY));
            LoweredModuleUnit mutated = new LoweredModuleUnit(appUnit.formatVersion(),
                appUnit.semanticProfile(), appUnit.moduleId(), appUnit.interfaceHash(),
                appUnit.loweringContextHash(), appUnit.requiredCapabilities(),
                appUnit.constructCoverage(), appUnit.classLayouts(), appUnit.functions(),
                appUnit.moduleInit(), appUnit.exportPlan(), doctored, appUnit.ops());
            Optional<deal.diagnostics.CompilerDiagnostic> failure =
                SemanticIrValidator.validate(mutated, facts(fixture));
            check(failure.isPresent()
                    && failure.get().message().contains("R-FUNCTION-BINDING"),
                "a doctored re-keying of the shared value (the read's registration moved "
                    + "onto the published value's identity) fails the closed gate with "
                    + "R-FUNCTION-BINDING; got "
                    + (failure.isEmpty() ? "no diagnostic" : failure.get().message()));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The three-consumer trace matrix over the probe project
    // =========================================================================

    static void testThreeConsumerProjectMatrix() throws Exception {
        System.out.println("-- the probe project runs through the oracle and both shared "
            + "artifacts under the real toolchains --");
        Fixture fixture = twoModuleFixture();
        Path workspace = Files.createTempDirectory("compiled-read-matrix");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            List<SemanticOp> reads = readsOf(project.modules().get(APP));
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success("compiled export read",
                        List.of(), "null"),
                    workspace);
            check(verdict.pass(), "the three consumers agree event-for-event (the read's "
                + "identity included):\n" + verdict.report());
            if (!verdict.pass()) {
                return;
            }
            for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                List<String> atoms = new ArrayList<>();
                for (SemanticOp read : reads) {
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.op().equals(read.opId())
                                && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                            atoms.add(event.output());
                        }
                    }
                }
                checkEq(2, atoms.size(), run.consumer() + " executes both reads");
                check(atoms.size() == 2 && atoms.get(0).equals(atoms.get(1))
                        && atoms.get(0).startsWith("ref:"),
                    run.consumer() + " publishes the identical published value for both "
                        + "reads; got " + atoms);
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The per-unit program-scoped registry
    // =========================================================================

    static void testPerUnitProgramRegistry() throws Exception {
        System.out.println("-- the per-unit sessions resolve the owner's published value "
            + "through the program-scoped registry --");
        Fixture fixture = twoModuleFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            List<SemanticOp> reads = readsOf(appUnit);
            List<String> readOps = new ArrayList<>();
            for (SemanticOp read : reads) {
                readOps.add(read.opId().module().path() + "#" + read.opId().id());
            }
            testPerUnitLua(project, libUnit, appUnit, result.tables(), readOps);
            testPerUnitJvm(project, libUnit, appUnit, result.tables(), reads, readOps);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The two-chunk LuaJIT per-unit drive: the owner chunk, then the entry chunk. */
    private static void testPerUnitLua(ExecutableLoweredProject project,
            LoweredModuleUnit libUnit, LoweredModuleUnit appUnit,
            Map<ModuleId, StructuredBodyTable> tables, List<String> readOps)
            throws Exception {
        Path workspace = Files.createTempDirectory("compiled-read-per-unit-lua");
        try {
            Path libChunk = workspace.resolve("lib.lua");
            Path appChunk = workspace.resolve("app.lua");
            Files.writeString(libChunk, LuaSemanticEmitter.emitModule(libUnit,
                tables.get(LIB)), StandardCharsets.UTF_8);
            Files.writeString(appChunk, LuaSemanticEmitter.emitModule(appUnit,
                tables.get(APP)), StandardCharsets.UTF_8);
            // The partial drive (the absent-slot projection): only the entry
            // chunk runs — the owner never publishes.
            Path absentDriver = workspace.resolve("absent.lua");
            Files.writeString(absentDriver, "dofile(" + luaString(
                    appChunk.toAbsolutePath().toString()) + ")\n", StandardCharsets.UTF_8);
            ProcessOutcome absent = runProcess(List.of("luajit",
                absentDriver.toAbsolutePath().toString()), workspace);
            checkEq(0, absent.exitCode(), "the entry-only per-unit chunk runs: "
                + absent.output());
            checkEq(List.of("missing"), luaReadAtoms(absent.stderr(), readOps),
                "the entry-only per-unit chunk projects the __MISSING sentinel for the "
                    + "compiled read");
            check(absent.stderr().contains("!E8001;expected function, got missing"),
                "the entry-only per-unit chunk's function-typed binding boundary rejects "
                    + "the absent-slot value: " + absent.stderr().replace("\n", "\\n"));

            // The program-scoped drive: the owner chunk publishes, then the
            // entry chunk (deferred) resolves the same object for both reads.
            Path driver = workspace.resolve("per-unit.lua");
            StringBuilder lua = new StringBuilder();
            lua.append("local __libOk, __libErr = pcall(dofile, ")
                .append(luaString(libChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __libOk then print(\"PROBE-FAIL: \"..tostring(__libErr)) "
                + "os.exit(1) end\n");
            lua.append("local __ok, __err = pcall(__dealMain)\n");
            lua.append("if not __ok then print(\"PROBE-FAIL: \"..tostring(__err)) "
                + "os.exit(1) end\n");
            lua.append("local __appOk, __appErr = pcall(dofile, ")
                .append(luaString(appChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __appOk then print(\"PROBE-FAIL: \"..tostring(__appErr)) "
                + "os.exit(1) end\n");
            lua.append("local __ok2, __err2 = pcall(__dealMain)\n");
            lua.append("if not __ok2 then print(\"PROBE-FAIL: \"..tostring(__err2)) "
                + "os.exit(1) end\n");
            lua.append("if __exportSurfaces[\"lib\"][\"tag\"].__val == nil then "
                + "print(\"PROBE-FAIL: no published value\") os.exit(1) end\n");
            lua.append("print(\"PROBE-OK\")\n");
            Files.writeString(driver, lua.toString(), StandardCharsets.UTF_8);
            ProcessOutcome run = runProcessWithEnv(List.of("luajit",
                driver.toAbsolutePath().toString()), workspace,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the two-chunk per-unit drive runs: exit=" + run.exitCode()
                    + " stdout=" + run.stdout().replace("\n", "\\n") + " stderr="
                    + run.stderr().replace("\n", "\\n"));
            String publicationAtom = luaPublicationAtom(run.stderr(), LIB.path(),
                libUnit);
            List<String> atoms = luaReadAtoms(run.stderr(), readOps);
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the owner chunk's publication atom is observable: " + publicationAtom);
            checkEq(2, atoms.size(), "both per-unit reads execute");
            check(atoms.size() == 2 && atoms.get(0).equals(atoms.get(1))
                    && atoms.get(0).equals(publicationAtom),
                "the per-unit entry chunk resolves the owner chunk's published value "
                    + "(the program-scoped registry, not a session-local map); got "
                    + atoms + " vs " + publicationAtom);
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The two-class JVM per-unit drive: the owner class, then the entry class. */
    private static void testPerUnitJvm(ExecutableLoweredProject project,
            LoweredModuleUnit libUnit, LoweredModuleUnit appUnit,
            Map<ModuleId, StructuredBodyTable> tables, List<SemanticOp> reads,
            List<String> readOps) throws Exception {
        Path workspace = Files.createTempDirectory("compiled-read-per-unit-jvm");
        try {
            JvmSemanticEmitter.EmissionResult lib = JvmSemanticEmitter.emitModule(
                libUnit, tables.get(LIB));
            JvmSemanticEmitter.EmissionResult app = JvmSemanticEmitter.emitModule(
                appUnit, tables.get(APP));
            Path libSource = workspace.resolve(lib.className() + ".java");
            Path appSource = workspace.resolve(app.className() + ".java");
            Files.writeString(libSource, lib.source(), StandardCharsets.UTF_8);
            Files.writeString(appSource, app.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();

            // The partial drive: the entry class alone (the owner class
            // exists but its walk never ran) projects MISSING at the
            // read and fails at the function-typed binding boundary.
            String absentDriver = "CompiledReadAbsentProbe";
            Files.writeString(workspace.resolve(absentDriver + ".java"),
                absentProbeSource(app.className(), reads), StandardCharsets.UTF_8);
            ProcessOutcome absentCompile = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                appSource.toAbsolutePath().toString(),
                workspace.resolve(absentDriver + ".java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, absentCompile.exitCode(), "the entry-only per-unit class compiles: "
                + absentCompile.output());
            if (absentCompile.exitCode() == 0) {
                ProcessOutcome absent = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, absentDriver), workspace);
                checkEq(0, absent.exitCode(), "the entry-only per-unit class runs: "
                    + absent.output());
                check(absent.stdout().contains("PROBE-OK"),
                    "the entry-only per-unit class projects JvmRuntime.MISSING for the "
                        + "compiled read; stdout=" + absent.stdout().replace("\n", "\\n")
                        + " stderr=" + absent.stderr().replace("\n", "\\n"));
            }

            // The program-scoped drive: the owner class runs first.
            String driver = "CompiledReadRegistryProbe";
            Files.writeString(workspace.resolve(driver + ".java"),
                perUnitProbeSource(lib.className(), app.className(), reads),
                StandardCharsets.UTF_8);
            ProcessOutcome compile = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                libSource.toAbsolutePath().toString(),
                appSource.toAbsolutePath().toString(),
                workspace.resolve(driver + ".java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, compile.exitCode(),
                "the per-unit classes compile with javac --release 25 -proc:none: "
                    + compile.output());
            if (compile.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, driver), workspace);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the per-unit classes resolve the owner's published value through the "
                    + "runtime-hosted registry; exit=" + run.exitCode() + " stdout="
                    + run.stdout().replace("\n", "\\n") + " stderr="
                    + run.stderr().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The entry-only JVM probe: the two reads project the MISSING sentinel. */
    private static String absentProbeSource(String appClass, List<SemanticOp> reads) {
        StringBuilder source = new StringBuilder();
        source.append("public class CompiledReadAbsentProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    try {\n");
        source.append("      ").append(appClass).append(".dealMain();\n");
        source.append("      check(false, \"the entry-only drive fails at the "
            + "function-typed binding boundary\");\n");
        source.append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n");
        source.append("      check(\"E8001\".equals(e.code), \"the binding boundary "
            + "raises the pinned E8001; got \" + e.code);\n");
        source.append("    }\n");
        for (int i = 0; i < reads.size(); i++) {
            long id = ((ValueId) reads.get(i).result()).id();
            if (i == 0) {
                source.append("    check(").append(appClass).append(".v").append(id)
                    .append(" == deal.codegen.jvm.JvmRuntime.MISSING, \"the entry-only "
                        + "read projects the absent-slot sentinel; got \" + ")
                    .append(appClass).append(".v").append(id).append(");\n");
            } else {
                source.append("    check(").append(appClass).append(".v").append(id)
                    .append(" == null, \"the function-typed binding boundary fails before "
                        + "the second read executes; got \" + ")
                    .append(appClass).append(".v").append(id).append(");\n");
            }
        }
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    /** The per-unit registry probe: the two read values and the published carrier. */
    private static String perUnitProbeSource(String libClass, String appClass,
            List<SemanticOp> reads) {
        StringBuilder source = new StringBuilder();
        source.append("public class CompiledReadRegistryProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(libClass).append(".dealMain();\n");
        source.append("    ").append(appClass).append(".dealMain();\n");
        source.append("    Object read1 = ").append(appClass).append(".v")
            .append(((ValueId) reads.get(0).result()).id()).append(";\n");
        source.append("    Object read2 = ").append(appClass).append(".v")
            .append(((ValueId) reads.get(1).result()).id()).append(";\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"tag\");\n");
        source.append("    check(").append(appClass).append(".EXPORT_SURFACES == "
            + "deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES, \"the class-level field view "
            + "is the runtime-hosted program-scoped registry\");\n");
        source.append("    check(read1 != null && read1 == read2, \"the two per-unit "
            + "reads publish the identical object; got \" + read1 + \" and \" + read2);\n");
        source.append("    check(read1 == published, \"the per-unit entry class resolves "
            + "the owner class's published value; got \" + read1 + \" vs \" + published);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 5. The production artifacts under the real toolchains
    // =========================================================================

    static void testProductionArtifacts() throws Exception {
        System.out.println("-- the production arm stages one project artifact per target; "
            + "both run under the real toolchains --");
        Fixture fixture = twoModuleFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            List<SemanticOp> reads = readsOf(result.project().modules().get(APP));

            Path luaOut = fixture.root().resolve("out-lua");
            writeFileIn(luaOut, "app.lua", "-- previous artifact\n");
            Map<String, String> before = snapshotTree(luaOut);
            PublicationStager luaStager = PublicationStager.forRoot(luaOut);
            ProductionProjectEmission.Result luaResult;
            try {
                luaResult = emit(fixture, Backend.LUAJIT, luaStager, false);
                luaStager.publish();
            } catch (Exception exception) {
                luaStager.discard();
                throw exception;
            } finally {
                luaStager.discard();
            }
            check(luaResult.emitted(), "the LuaJIT production arm emits: "
                + luaResult.diagnostics());
            if (!luaResult.emitted()) {
                return;
            }
            String lua = Files.readString(luaOut.resolve(luaResult.artifactRelativePath()));
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                checkEq(1, countOccurrences(lua,
                        "S.v" + id + " = __exportValue(\"lib\", \"tag\")"),
                    "the production LuaJIT artifact carries the surface-resolving read");
                check(!lua.contains("S.v" + id + " = __intrinsicFn()"),
                    "the production LuaJIT artifact carries no placeholder read");
            }
            check(!lua.contains("export:lib.tag"),
                "the production LuaJIT artifact carries no placeholder token");
            Map<String, String> afterLua = snapshotTree(luaOut);
            check(!afterLua.equals(before),
                "the emitted run replaced the previous artifact set");

            Path luaProbe = fixture.root().resolve("lua-probe.lua");
            Files.writeString(luaProbe, luaProductionProbe(luaOut.resolve(
                luaResult.artifactRelativePath())), StandardCharsets.UTF_8);
            ProcessOutcome luaRun = runProcess(List.of("luajit",
                luaProbe.toAbsolutePath().toString()), fixture.root());
            check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK"),
                "the production LuaJIT chunk resolves the surface entry and its .f "
                    + "projection still calls the module function: exit="
                    + luaRun.exitCode() + " stdout="
                    + luaRun.stdout().replace("\n", "\\n") + " stderr="
                    + luaRun.stderr().replace("\n", "\\n"));

            Path jvmOut = fixture.root().resolve("out-jvm");
            writeFileIn(jvmOut, "App.java", "// previous artifact\n");
            PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result jvmResult;
            try {
                jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
                jvmStager.publish();
            } finally {
                jvmStager.discard();
            }
            check(jvmResult.emitted(), "the JVM production arm emits: "
                + jvmResult.diagnostics());
            if (!jvmResult.emitted()) {
                return;
            }
            Path jvmSource = jvmOut.resolve(jvmResult.artifactRelativePath());
            String jvmText = Files.readString(jvmSource);
            for (SemanticOp read : reads) {
                long id = ((ValueId) read.result()).id();
                checkEq(1, countOccurrences(jvmText,
                        "v" + id + " = exportSurface(\"lib\").read(\"tag\");"),
                    "the production JVM artifact carries the uniform surface read");
                check(!jvmText.contains("v" + id + " = new JvmRuntime.Intrinsic()"),
                    "the production JVM artifact carries no placeholder read");
            }
            check(!jvmText.contains("export:lib.tag"),
                "the production JVM artifact carries no placeholder token");

            String driver = "CompiledReadProductionProbe";
            Files.writeString(jvmOut.resolve(driver + ".java"),
                productionProbeSource(JvmBackend.classNameFor(APP.path()), reads),
                StandardCharsets.UTF_8);
            Path classes = jvmOut.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmSource.toAbsolutePath().toString(),
                jvmOut.resolve(driver + ".java").toAbsolutePath().toString()),
                fixture.root());
            checkEq(0, javacRun.exitCode(),
                "the production JVM artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, driver), fixture.root());
            check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK"),
                "the production JVM artifact's read value is the published "
                    + "JvmRuntime.FunctionValue carrier and its .fn projection still "
                    + "calls the module function; exit=" + javaRun.exitCode() + " stdout="
                    + javaRun.stdout().replace("\n", "\\n") + " stderr="
                    + javaRun.stderr().replace("\n", "\\n"));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The production LuaJIT probe: the surface entry, __val, and the .f ABI. */
    private static String luaProductionProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("local __lib = __exportSurfaces[\"lib\"]\n");
        lua.append("if __lib == nil then __fail(\"no lib surface\") end\n");
        lua.append("local __entry = __lib[\"tag\"]\n");
        lua.append("if type(__entry) ~= \"table\" then __fail(\"no tag entry\") end\n");
        lua.append("if __entry.__kind ~= \"function\" then __fail(\"entry kind\") end\n");
        lua.append("if __entry.sig ~= \"(int)->string\" then __fail(\"entry sig \".."
            + "tostring(__entry.sig)) end\n");
        lua.append("if type(__entry.f) ~= \"function\" then __fail(\"entry .f ABI\") end\n");
        lua.append("local __ok, __value = pcall(__entry.f, 1)\n");
        lua.append("if not __ok or __value ~= \"t\" then __fail(\"the retained-caller .f "
            + "projection calls the module function; got \"..tostring(__value)) end\n");
        lua.append("if __entry.__val == nil then __fail(\"no published __val\") end\n");
        lua.append("if __entry.__val ~= __entry.__val then __fail(\"unstable __val\") end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /** The production JVM probe: the read values, the carrier, and the .fn ABI. */
    private static String productionProbeSource(String className, List<SemanticOp> reads) {
        StringBuilder source = new StringBuilder();
        source.append("public class CompiledReadProductionProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    Object read1 = ").append(className).append(".v")
            .append(((ValueId) reads.get(0).result()).id()).append(";\n");
        source.append("    Object read2 = ").append(className).append(".v")
            .append(((ValueId) reads.get(1).result()).id()).append(";\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"tag\");\n");
        source.append("    check(").append(className).append(".EXPORT_SURFACES == "
            + "deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES, \"the class-level field view "
            + "is the runtime-hosted program-scoped registry\");\n");
        source.append("    check(published instanceof deal.codegen.jvm.JvmRuntime."
            + "FunctionValue, \"the published entry is the JvmRuntime.FunctionValue "
            + "carrier; got \" + published);\n");
        source.append("    check(read1 != null && read1 == read2 && read1 == published, "
            + "\"the emitted read resolves the published carrier object; got \" + read1 "
            + "+ \" and \" + read2);\n");
        source.append("    Object value = ((deal.codegen.jvm.JvmRuntime.FunctionValue) "
            + "published).fn.invoke(new Object[] {1L});\n");
        source.append("    check(\"t\".equals(value), \"the retained-caller .fn "
            + "projection still calls the module function; got \" + value);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 6. The project-session ownership guard
    // =========================================================================

    static void testProjectSessionOwnershipGuard() throws Exception {
        System.out.println("-- the project-session ownership guard: a foreign owner fails "
            + "the emission closed; a per-unit session never does --");
        Fixture fixture = twoModuleFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            StructuredBodyTable appTable = result.tables().get(APP);
            Map<ModuleId, StructuredBodyTable> onlyEntryTables = Map.of(APP, appTable);
            Map<ModuleId, deal.semantic.ir.ClassFactoryRegistry> onlyEntryRegistries =
                Map.of(APP, result.registries().get(APP));
            ExecutableLoweredProject doctored = new ExecutableLoweredProject(
                SemanticProfile.DEAL_V1_2_INT32, project.interfaceIndex(),
                Map.of(APP, appUnit), APP);

            IllegalStateException luaGuard = null;
            try {
                LuaSemanticEmitter.emitProject(doctored, onlyEntryTables,
                    onlyEntryRegistries);
            } catch (IllegalStateException expected) {
                luaGuard = expected;
            }
            check(luaGuard != null && luaGuard.getMessage().contains("lib")
                    && luaGuard.getMessage().contains("tag")
                    && luaGuard.getMessage().contains("closure"),
                "the LuaJIT project session fails closed for a compiled read whose owner "
                    + "is outside its units: " + (luaGuard == null ? "no failure"
                        : luaGuard.getMessage()));
            IllegalStateException jvmGuard = null;
            try {
                JvmSemanticEmitter.emitProject(doctored, onlyEntryTables,
                    onlyEntryRegistries);
            } catch (IllegalStateException expected) {
                jvmGuard = expected;
            }
            check(jvmGuard != null && jvmGuard.getMessage().contains("lib")
                    && jvmGuard.getMessage().contains("tag")
                    && jvmGuard.getMessage().contains("closure"),
                "the JVM project session fails closed for the same doctored project: "
                    + (jvmGuard == null ? "no failure" : jvmGuard.getMessage()));

            // The per-unit sessions must never fail closed for a foreign
            // owner: they emit the surface lookup of the same program.
            String perUnitLua = LuaSemanticEmitter.emitModule(appUnit, appTable);
            check(perUnitLua.contains("__exportValue(\"lib\", \"tag\")"),
                "the per-unit LuaJIT session emits the surface read for the foreign owner");
            JvmSemanticEmitter.EmissionResult perUnitJvm = JvmSemanticEmitter.emitModule(
                appUnit, appTable);
            check(perUnitJvm.source().contains("exportSurface(\"lib\").read(\"tag\")"),
                "the per-unit JVM session emits the surface read for the foreign owner");

            // ISSUE-0654 supersedes the emission-gap reading of this
            // fixture: the production arm now realizes the cross-module
            // sync call through the callee unit's EXTERNAL_ENTRY, so the
            // same fixture emits one project artifact and publishes it
            // (the emitter's fail-closed producer-defect family is
            // asserted by the calls child's focused suite).
            Fixture syncFixture = compileProject(new LinkedHashMap<>(Map.of(
                "src/lib.deal", LIB_SOURCE,
                "src/app.deal", "import * as lib from \"./lib\"\n\n"
                    + "export function main(): null {\n  let x: string = lib.tag(1)\n"
                    + "  return null\n}\n")));
            try {
                Path out = syncFixture.root().resolve("out-arm");
                writeFileIn(out, "app.lua", "-- previous artifact\n");
                PublicationStager stager = PublicationStager.forRoot(out);
                ProductionProjectEmission.Result arm;
                try {
                    arm = emit(syncFixture, Backend.LUAJIT, stager, false);
                    check(arm.emitted(),
                        "the cross-module sync call emits through the realized "
                            + "EXTERNAL_ENTRY arm: " + arm.diagnostics());
                    check(stager.stagedSet().artifact("app.lua").isPresent(),
                        "the emitted compile stages its one project artifact");
                } finally {
                    stager.discard();
                }
            } finally {
                deleteRecursively(syncFixture.root());
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // The production-arm driver
    // =========================================================================

    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager, boolean sourceMapExplicit)
            throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, sourceMapExplicit, fixture.distributionHome(), stager);
    }

    // =========================================================================
    // Trace parsing and process helpers
    // =========================================================================

    /**
     * The SUCCESS output atoms of the given read ops in a LuaJIT trace
     * stream, in stream order.
     */
    private static List<String> luaReadAtoms(String stderr, List<String> readOps) {
        List<String> atoms = new ArrayList<>();
        for (String line : stderr.split("\n")) {
            String[] fields = line.split("\\|", -1);
            if (fields.length < 9 || !"T".equals(fields[0]) || !"SUCCESS".equals(fields[4])) {
                continue;
            }
            if (!readOps.contains(fields[3])) {
                continue;
            }
            for (int i = 8; i < fields.length; i++) {
                if (fields[i].startsWith("=>")) {
                    atoms.add(fields[i].substring(2));
                }
            }
        }
        return atoms;
    }

    /** The publication boundary's input atom of the owner module, or null. */
    private static String luaPublicationAtom(String stderr, String modulePath,
            LoweredModuleUnit libUnit) {
        SemanticOp publish = publishOpOf(libUnit);
        SemanticOp boundary = publish == null ? null : exportBoundaryOf(libUnit,
            publish.opId());
        if (boundary == null) {
            return null;
        }
        String key = modulePath + "#" + boundary.opId().id();
        for (String line : stderr.split("\n")) {
            String[] fields = line.split("\\|", -1);
            if (fields.length < 9 || !"T".equals(fields[0]) || !"START".equals(fields[4])
                    || !"BOUNDARY".equals(fields[5]) || !key.equals(fields[3])) {
                continue;
            }
            for (int i = 8; i < fields.length; i++) {
                if (!fields[i].startsWith("=>")) {
                    return fields[i];
                }
            }
        }
        return null;
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
    }

    private static ProcessOutcome runProcess(List<String> command, Path workspace)
            throws Exception {
        return runProcessWithEnv(command, workspace, Map.of());
    }

    private static ProcessOutcome runProcessWithEnv(List<String> command, Path workspace,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workspace.toFile());
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

    /** The build-output classpath of this test process. */
    private static String absoluteClasspath() {
        String classpath = System.getProperty("java.class.path", "build");
        List<String> entries = new ArrayList<>();
        for (String entry : classpath.split(File.pathSeparator)) {
            entries.add(Path.of(entry).toAbsolutePath().normalize().toString());
        }
        return String.join(File.pathSeparator, entries);
    }

    private static String luaString(String text) {
        return "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    /** A recursive path → content snapshot of one tree (the staging assertions). */
    private static Map<String, String> snapshotTree(Path root) throws Exception {
        Map<String, String> snapshot = new TreeMap<>();
        if (!Files.exists(root)) {
            return snapshot;
        }
        try (var paths = Files.walk(root)) {
            for (Path path : paths.sorted().toList()) {
                if (Files.isRegularFile(path)) {
                    snapshot.put(root.relativize(path).toString(),
                        Files.readString(path, StandardCharsets.UTF_8));
                }
            }
        }
        return snapshot;
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path root) {
        if (root == null || !Files.exists(root)) {
            return;
        }
        try (var paths = Files.walk(root)) {
            paths.sorted(java.util.Comparator.reverseOrder()).forEach(path -> {
                try {
                    Files.deleteIfExists(path);
                } catch (java.io.IOException ignored) {
                    // best effort
                }
            });
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Driver
    // =========================================================================

    public static void main(String[] args) throws Exception {
        testEmittedReadOperation();
        testOracleReadRealization();
        testThreeConsumerProjectMatrix();
        testPerUnitProgramRegistry();
        testProductionArtifacts();
        testProjectSessionOwnershipGuard();
        System.out.println();
        System.out.println("CompiledExportReadRealizationTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
