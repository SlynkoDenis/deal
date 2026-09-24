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
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
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
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;

/**
 * ISSUE-0648: the HOST/FFI export-read execution realization across the
 * three consumers (design source
 * {@code module-export-reads-and-in-project-class-construction} M5, M3's
 * HOST branch, M6, the host/FFI read boundary contract, and the read
 * execution contract; {@code semantic-ir-construct-coverage-cutover} K15
 * item 1 — a HOST module's surface is the loaded module table;
 * {@code luajit-jvm-single-lowering-production-cutover} C1/C2).
 *
 * <ol>
 *   <li><b>The lowering, validation, and registration (the shared T2
 *       arm, asserted here over the checker-valid declaration-only
 *       fixtures).</b> The two conformance declaration-only fixtures
 *       ({@code declaration-only-import-compile.deal},
 *       {@code declaration-only-not-executed.deal}) and one
 *       callee-position companion over the same declaration module lower
 *       through the one project entry to exactly one {@code EXPORT_READ}
 *       per source occurrence carrying {@code {resolvedModule, name,
 *       checked descriptor}} plus exactly one
 *       {@code HostFunction(resolvedModule, name, descriptor)}
 *       registration keyed by the read result's allocation identity; the
 *       composed project gate admits the project with no diagnostic.</li>
 *   <li><b>The emitted read (M5/M6).</b> Both project sessions of both
 *       targets carry the same host read operation in trace and
 *       production mode: LuaJIT {@code S.v<id> =
 *       __exportHostValue(<module>, <name>)} (the program-scoped surface
 *       entry itself — no {@code __intrinsicFn()} placeholder), JVM
 *       {@code v<id> = exportSurface(<module>).read(<name>);} (the
 *       uniform read, absent key → {@code JvmRuntime.MISSING}); the
 *       per-unit sessions emit the identical operation; repeated
 *       emissions are byte-identical.</li>
 *   <li><b>The oracle (M3/M5).</b> The full project drive resolves the
 *       HOST read from the per-run surface registry: an absent surface or
 *       entry — the landed state, the host load surface is the calls
 *       child's — projects {@code Value.MissingValue}, atomizing as
 *       {@code missing}; a surface holding the recorded entries
 *       (simulated by re-typing the HOST import onto a compiled
 *       companion's identity, the not-yet-landed load's effect) resolves
 *       the entry itself: the publication's own creation atom, the
 *       identical object, no wrap and no copy. No
 *       {@code export:<module>.<name>} placeholder atom remains; the read
 *       writes no value-keyed binding entry and its registration stays
 *       addressable by the read result's allocation identity (doctored
 *       zero-registration and re-keyed seeds fail the closed gate with
 *       R-FUNCTION-BINDING).</li>
 *   <li><b>The combined composition (T2 + T3 + this leaf).</b> A focused
 *       per-unit probe whose entry carries both a compiled read (T3) and
 *       a HOST read resolves both consistently across the oracle and both
 *       per-unit artifacts: the compiled read publishes the owner's
 *       published value object (its creation atom), the HOST read
 *       projects the absent-slot value, and all three consumers fail
 *       identically at the HOST read's function-typed binding boundary
 *       with the pinned E8001. With the loaded module table's entry seeded
 *       under the module identity, the LuaJIT and JVM artifacts resolve
 *       exactly that entry (never the absent slot, never a re-wrap). The
 *       assertions fail if the read arm, the program-scoped surface
 *       registry, or the host projection is broken.</li>
 *   <li><b>The production arm's host surface.</b> The HOST-importing
 *       closure emits and stages its one project artifact (ISSUE-0656:
 *       the narrowed guard no longer blocks the host load): the emitted
 *       chunk carries the declared-map {@code __rt.load_host} call of the
 *       HOST declaration module in the module init walk, so the
 *       value-position HOST read resolves the loaded table's entry
 *       through the same read arm the per-unit sessions use (the host load
 *       surface and the executable drive are the calls child's).</li>
 * </ol>
 *
 * <p>No operation kind or payload shape is added, no loader surface is
 * implemented, and no load-time E8011 check is forked.</p>
 */
public class HostExportReadRealizationTest {

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
        check(Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    /** The conformance declaration-only fixture directory. */
    private static final Path CONFORMANCE_MODULES =
        Path.of("test", "conformance", "backend-runtime", "modules");

    private static final String VALUE_POSITION_FIXTURE =
        "declaration-only-import-compile.deal";
    private static final String SECOND_FIXTURE = "declaration-only-not-executed.deal";
    private static final String DECLARATION_FILE = "declaration_only_lib.d.deal";
    private static final String SECOND_DECLARATION_FILE = "runtime_missing_decl.d.deal";

    /**
     * The callee-position companion over the same checker-valid
     * declaration module (the fixture's own entry stays untouched in the
     * repository): the declared export is invoked, so the callee arm
     * materializes the same one read.
     */
    private static final String CALLEE_POSITION_ENTRY = """
        import * as Decl from "./declaration_only_lib"

        export function test_decl_call(): int {
          let v: int = Decl.declaredAdd(1, 2);
          return v;
        }

        export function main(): null { return null; }
        """;

    /** The HOST declaration module of the combined probe (externals-declared). */
    private static final String HOST_SPECIFIER = "host/read_probe";
    private static final String HOST_MODULE_PATH = "host.read_probe";
    private static final String HOST_DECLARATION_SOURCE = """
        export function ping(v: int): string;
        """;

    // The combined probe (T3's compiled companion + this leaf's HOST read).
    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId APP = new ModuleId("app");
    private static final String EXPORT_NAME = "ping";

    private static final String LIB_SOURCE = """
        export function ping(v: int): string {
          return "t";
        }
        """;

    private static final String COMBINED_APP_SOURCE = """
        import * as host from "host/read_probe"
        import * as lib from "./lib"

        export function main(): null {
          let f: (v: int) => string = lib.ping
          let g: (v: int) => string = host.ping
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

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * Builds a fixture from the given {@code src/}-relative sources (plus,
     * when requested, the copied conformance declaration fixtures) and the
     * externals map (external key → root-relative declaration path).
     */
    private static Fixture compileProject(Map<String, String> sources,
            Map<String, String> externals, String entryRelative) throws Exception {
        Path root = Files.createTempDirectory("host-read-fixture");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            resolvedExternals.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().toString());
        }
        Path entry = src.resolve(entryRelative).toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, resolvedExternals,
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
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            String specifier = null;
            for (Map.Entry<String, String> external : externals.entrySet()) {
                if (external.getKey().replace('/', '.').equals(declarationModule.path())
                        || external.getKey().equals(declarationModule.path())) {
                    specifier = external.getKey();
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            surface, externCModules, identities,
            DistributionHome.forManifestDirectory(src.toString()));
    }

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

    /**
     * The declaration-only fixture project: the repository's checker-valid
     * fixtures copied verbatim (the declaration companion included), plus
     * the optional callee-position entry.
     */
    private static Fixture declarationOnlyFixture(String entryName, String extraEntry)
            throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        for (String fixture : List.of(VALUE_POSITION_FIXTURE, SECOND_FIXTURE,
                DECLARATION_FILE, SECOND_DECLARATION_FILE)) {
            String text = Files.readString(CONFORMANCE_MODULES.resolve(fixture),
                StandardCharsets.UTF_8);
            // The harness's own seam: classification headers are stripped
            // before the compiler ever sees the corpus bytes (the fixture
            // text is otherwise copied verbatim).
            sources.put("src/" + fixture,
                ConformanceHarnessMetadata.stripClassificationHeaders(text));
        }
        if (extraEntry != null) {
            sources.put("src/" + entryName, extraEntry);
        }
        Fixture fixture = compileProject(sources, Map.of(), entryName);
        return fixture;
    }

    /** The combined probe: compiled companion + HOST declaration import. */
    private static Fixture combinedFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/lib.deal", LIB_SOURCE);
        sources.put("src/read_probe.d.deal", HOST_DECLARATION_SOURCE);
        sources.put("src/app.deal", COMBINED_APP_SOURCE);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(HOST_SPECIFIER, "src/read_probe.d.deal");
        return compileProject(sources, externals, "app.deal");
    }

    // =========================================================================
    // Read and registration helpers
    // =========================================================================

    /** The EXPORT_READ ops of one unit in op order. */
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

    /** The unit's registration keyed by the given value's allocation identity. */
    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit, ValueId value) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
    }

    /** The unit's HOST-kind import payloads in op order. */
    private static List<KindPayload.ModuleImportPayload> hostImportsOf(
            LoweredModuleUnit unit) {
        List<KindPayload.ModuleImportPayload> imports = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.MODULE_IMPORT) {
                continue;
            }
            KindPayload.ModuleImportPayload payload =
                (KindPayload.ModuleImportPayload) op.payload();
            if (payload.kind() == ModuleImportKind.HOST) {
                imports.add(payload);
            }
        }
        return imports;
    }

    /** The unit's EXPORT_READ ops whose module is the given identity. */
    private static List<SemanticOp> readsOfModule(LoweredModuleUnit unit, ModuleId module) {
        List<SemanticOp> reads = new ArrayList<>();
        for (SemanticOp read : readsOf(unit)) {
            if (readPayload(read).module().equals(module)) {
                reads.add(read);
            }
        }
        return reads;
    }

    /** The trace SUCCESS output atoms of the given read ops, in stream order. */
    private static List<String> readAtoms(SemanticRuntimeModel.ConsumerRun run,
            List<SemanticOp> reads) {
        List<String> atoms = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.phase() != SemanticRuntimeModel.Phase.SUCCESS) {
                continue;
            }
            for (SemanticOp read : reads) {
                if (event.op().equals(read.opId())) {
                    atoms.add(event.output());
                }
            }
        }
        return atoms;
    }

    /** The SUCCESS output atoms of the given read op keys in a LuaJIT trace. */
    private static List<String> luaReadAtoms(String stderr, List<String> readOps) {
        List<String> atoms = new ArrayList<>();
        for (String line : stderr.split("\n")) {
            String[] fields = line.split("\\|", -1);
            if (fields.length < 9 || !"T".equals(fields[0])
                    || !"SUCCESS".equals(fields[4])) {
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

    /** The trace op key of one op (its own emitting module + op id). */
    private static String traceOpKey(SemanticOp op) {
        return op.opId().module().path() + "#" + op.opId().id();
    }

    // =========================================================================
    // 1. The lowering, validation, and registration over the checker-valid
    //    declaration-only fixtures, in both positions
    // =========================================================================

    static void testDeclarationOnlyFixtures() throws Exception {
        System.out.println("-- the checker-valid declaration-only fixtures: one read and "
            + "one HostFunction per position, the project gate admits --");

        Fixture valueFixture = declarationOnlyFixture(VALUE_POSITION_FIXTURE, null);
        try {
            checkReadArmOverFixture(valueFixture, VALUE_POSITION_FIXTURE, "declaredAdd",
                "the value position");
        } finally {
            deleteRecursively(valueFixture.root());
        }

        Fixture secondFixture = declarationOnlyFixture(SECOND_FIXTURE, null);
        try {
            checkReadArmOverFixture(secondFixture, SECOND_FIXTURE, "declaredOnly",
                "the value position (the second fixture)");
        } finally {
            deleteRecursively(secondFixture.root());
        }

        Fixture calleeFixture = declarationOnlyFixture("callee_entry.deal",
            CALLEE_POSITION_ENTRY);
        try {
            checkReadArmOverFixture(calleeFixture, "callee_entry.deal", "declaredAdd",
                "the callee position");
        } finally {
            deleteRecursively(calleeFixture.root());
        }
    }

    /**
     * One fixture drive: the project lowers to exactly one read of the
     * declaration module's function export with exactly one
     * {@code HostFunction} registration, and the composed project gate
     * admits the project.
     */
    private static void checkReadArmOverFixture(Fixture fixture, String fixtureName,
            String exportName, String position) throws Exception {
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        if (result.project() == null) {
            fail("the " + fixtureName + " fixture lowers: " + result.diagnostics());
            return;
        }
        ExecutableLoweredProject project = result.project();
        Optional<deal.diagnostics.CompilerDiagnostic> gate =
            SemanticIrValidator.validate(project, facts(fixture));
        check(gate.isEmpty(),
            "the composed project gate admits the " + fixtureName + " fixture ("
                + position + "): " + gate.orElse(null));
        if (gate.isPresent()) {
            return;
        }
        ModuleId entry = project.entryModule();
        LoweredModuleUnit entryUnit = project.modules().get(entry);
        check(entryUnit != null, "the lowered project carries the entry unit of "
            + entry.path());
        if (entryUnit == null) {
            return;
        }
        List<KindPayload.ModuleImportPayload> hostImports = hostImportsOf(entryUnit);
        checkEq(1, hostImports.size(), "the " + fixtureName + " unit records exactly one "
            + "HOST-kind import");
        if (hostImports.size() != 1) {
            return;
        }
        ModuleId hostModule = hostImports.get(0).resolvedModule();
        List<SemanticOp> reads = readsOfModule(entryUnit, hostModule);
        checkEq(1, reads.size(), "the " + fixtureName + " fixture carries exactly one "
            + "EXPORT_READ of " + hostModule.path() + " (" + position + ")");
        if (reads.size() != 1) {
            return;
        }
        KindPayload.ExportReadPayload payload = readPayload(reads.get(0));
        checkEq(exportName, payload.name(), "the read names the declared export");
        check(payload.descriptor() instanceof deal.semantic.ir.RuntimeDescriptor.Func,
            "the read carries the declared function descriptor; got "
                + payload.descriptor());
        FunctionExecutionBinding binding = bindingOf(entryUnit, payload.value());
        check(binding instanceof FunctionExecutionBinding.HostFunction host
                && host.hostModuleId().equals(hostModule)
                && host.exportName().equals(exportName)
                && host.descriptor().equals(payload.descriptor()),
            "exactly one HostFunction(resolved module, declared export, checked "
                + "descriptor) registration is keyed by the read result's allocation "
                + "identity (" + position + "); got " + binding);
        checkEq(1, importRegistrations(entryUnit).size(),
            "the unit carries exactly one import registration (R-FUNCTION-BINDING's "
                + "closed gate holds by construction); got "
                + importRegistrations(entryUnit));
    }

    /** The unit's import registrations (HostFunction/ExternalFunction), in key order. */
    private static List<FunctionExecutionBinding> importRegistrations(
            LoweredModuleUnit unit) {
        List<FunctionExecutionBinding> imports = new ArrayList<>();
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.HostFunction
                    || binding instanceof FunctionExecutionBinding.ExternalFunction) {
                imports.add(binding);
            }
        }
        return imports;
    }

    // =========================================================================
    // 2. The emitted read in both sessions and both modes
    // =========================================================================

    static void testEmittedRead() throws Exception {
        System.out.println("-- the emitted host read: the surface-entry lookup in both "
            + "project sessions, both modes, and the per-unit sessions --");
        Fixture fixture = combinedFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the combined probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId hostModule = hostImportModule(project);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            List<SemanticOp> reads = readsOfModule(appUnit, hostModule);
            checkEq(1, reads.size(), "the entry unit carries the one HOST read");
            if (reads.size() != 1) {
                return;
            }
            SemanticOp read = reads.get(0);
            long id = ((ValueId) read.result()).id();

            String traceLua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            String productionLua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            String hostRead = "S.v" + id + " = __exportHostValue(\""
                + hostModule.path() + "\", \"" + EXPORT_NAME + "\")";
            checkEq(1, countOccurrences(traceLua, hostRead),
                "the trace-mode LuaJIT project session emits the host surface-entry "
                    + "lookup: " + hostRead);
            checkEq(1, countOccurrences(productionLua, hostRead),
                "the production LuaJIT project session emits the identical read operation");
            check(traceLua.contains("local function __exportHostValue(module, name)"),
                "the prelude carries the host surface accessor");
            check(!traceLua.contains("S.v" + id + " = __intrinsicFn()"),
                "the host read is never the landed placeholder arm");
            checkEq(traceLua, LuaSemanticEmitter.emitProject(project, result.tables(),
                    result.registries()),
                "the repeated trace-mode emission is byte-identical");

            String traceJvm = JvmSemanticEmitter.emitProject(project, result.tables(),
                result.registries()).source();
            String productionJvm = JvmSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(),
                JvmBackend.classNameFor(APP.path()), fixture.surface()).source();
            String jvmRead = "v" + id + " = exportSurface(\"" + hostModule.path()
                + "\").read(\"" + EXPORT_NAME + "\");";
            checkEq(1, countOccurrences(traceJvm, jvmRead),
                "the trace-mode JVM project session emits the uniform surface read: "
                    + jvmRead);
            checkEq(1, countOccurrences(productionJvm, jvmRead),
                "the production JVM project session emits the identical read operation");
            check(!traceJvm.contains("v" + id + " = new JvmRuntime.Intrinsic()"),
                "the host read is never the landed JVM placeholder arm");
            checkEq(productionJvm, JvmSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(),
                    JvmBackend.classNameFor(APP.path()), fixture.surface()).source(),
                "the repeated production JVM emission is byte-identical");

            // The per-unit sessions of both targets emit the same read
            // operation (the owner module's publication is another chunk's /
            // class's of the same program).
            String perUnitLua = LuaSemanticEmitter.emitModule(appUnit,
                result.tables().get(APP));
            checkEq(1, countOccurrences(perUnitLua, hostRead),
                "the per-unit LuaJIT session emits the identical host read");
            String perUnitJvm = JvmSemanticEmitter.emitModule(appUnit,
                result.tables().get(APP)).source();
            checkEq(1, countOccurrences(perUnitJvm, jvmRead),
                "the per-unit JVM session emits the identical host read");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The oracle: the per-run surface resolution and the registration
    //    discipline
    // =========================================================================

    static void testOracleResolution() throws Exception {
        System.out.println("-- the oracle: the HOST read resolves the per-run surface "
            + "registry entry and stays addressable by its own allocation identity --");
        Fixture fixture = combinedFixture();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the combined probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId hostModule = hostImportModule(project);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            List<SemanticOp> hostReads = readsOfModule(appUnit, hostModule);
            List<SemanticOp> compiledReads = readsOfModule(appUnit, LIB);
            checkEq(1, hostReads.size(), "the entry carries the one HOST read");
            checkEq(1, compiledReads.size(), "the entry carries the one compiled read");

            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
                project, result.tables(), result.registries(), null);
            checkEq(List.of("missing"), readAtoms(run, hostReads),
                "the full drive projects the absent-slot value for the HOST read (the "
                    + "loaded module table is recorded by the calls child's host load; "
                    + "an absent surface or entry is Value.MissingValue, atomizing as "
                    + "missing)");
            checkEq(1, readAtoms(run, compiledReads).size(),
                "the combined probe's compiled read publishes its one terminal");
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                check(event.output() == null || !event.output().startsWith("export:"),
                    "no export:<module>.<name> placeholder atom remains in the oracle "
                        + "trace: " + event.output());
            }

            // The value-keyed map is not re-keyed by the read: the read's
            // registration is addressed by the read result's allocation
            // identity (the static channel), and the owner-side
            // registration of the compiled companion's published value
            // stays its LoweredBody.
            KindPayload.ExportReadPayload hostPayload = readPayload(hostReads.get(0));
            check(bindingOf(appUnit, hostPayload.value())
                    instanceof FunctionExecutionBinding.HostFunction host
                    && host.hostModuleId().equals(hostModule)
                    && host.exportName().equals(EXPORT_NAME),
                "the HOST read's registration stays addressable by the read result's "
                    + "allocation identity");
            SemanticOp publish = publishOpOf(libUnit);
            ValueId publishedValue = ((KindPayload.ExportPublishPayload) publish.payload())
                .value();
            check(bindingOf(libUnit, publishedValue)
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the owner-side runtime resolution of the published value stays the "
                    + "owner's LoweredBody");

            // The doctored seeds: a zero registration on the read result
            // identity and a re-keyed registration both fail the closed
            // gate; a duplicate registration is rejected at registration
            // time.
            LoweredModuleUnit noRegistration = withBindings(appUnit,
                withoutReadBinding(appUnit, hostPayload.value()));
            Optional<deal.diagnostics.CompilerDiagnostic> zeroGate =
                SemanticIrValidator.validate(noRegistration, facts(fixture));
            check(zeroGate.isPresent()
                    && zeroGate.get().message().contains("R-FUNCTION-BINDING"),
                "a doctored zero registration on the HOST read result identity fails the "
                    + "closed gate with R-FUNCTION-BINDING; got "
                    + (zeroGate.isEmpty() ? "no diagnostic" : zeroGate.get().message()));

            Map<FunctionAllocationIdentity, FunctionExecutionBinding> rekeyed =
                new LinkedHashMap<>(appUnit.functionBindings());
            rekeyed.remove(new FunctionAllocationIdentity(hostPayload.value().id()));
            rekeyed.put(new FunctionAllocationIdentity(publishedValue.id()),
                new FunctionExecutionBinding.HostFunction(hostModule, EXPORT_NAME,
                    (deal.semantic.ir.RuntimeDescriptor.Func) hostPayload.descriptor()));
            LoweredModuleUnit mutated = withBindings(appUnit, rekeyed);
            Optional<deal.diagnostics.CompilerDiagnostic> rekeyGate =
                SemanticIrValidator.validate(mutated, facts(fixture));
            check(rekeyGate.isPresent()
                    && rekeyGate.get().message().contains("R-FUNCTION-BINDING"),
                "a doctored re-keying of the HOST read's registration off the read "
                    + "result identity fails the closed gate with R-FUNCTION-BINDING; got "
                    + (rekeyGate.isEmpty() ? "no diagnostic" : rekeyGate.get().message()));

            // The populated state — the calls child's host load is not
            // landed, so the module surface the read resolves is seeded by
            // re-typing the HOST import and the HOST read onto the compiled
            // companion's identity: the recorded publication stands in for
            // the loaded module table's entry. The read then publishes the
            // entry itself — the identical recorded object (the
            // publication's own creation atom, never a wrap or a copy) —
            // and the invocation-free program succeeds.
            OpId hostReadOp = hostReads.get(0).opId();
            LoweredModuleUnit populatedApp = retypedHostImport(appUnit, hostModule, LIB,
                hostReadOp);
            ExecutableLoweredProject populatedProject = new ExecutableLoweredProject(
                project.semanticProfile(), project.interfaceIndex(),
                modulesWith(project, APP, populatedApp), project.entryModule());
            Optional<deal.diagnostics.CompilerDiagnostic> populatedGate =
                SemanticIrValidator.validate(populatedProject, facts(fixture));
            check(populatedGate.isEmpty(),
                "the populated seed's doctored unit still passes the closed gate: "
                    + populatedGate.orElse(null));
            SemanticRuntimeModel.ConsumerRun populatedRun =
                SemanticOracle.executeProjectInits(populatedProject, result.tables(),
                    result.registries(), null);
            String publicationAtom = boundaryAtom(populatedRun, libUnit);
            List<String> populatedAtoms = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : populatedRun.trace()) {
                if (event.op().equals(hostReadOp)
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                    populatedAtoms.add(event.output());
                }
            }
            check(publicationAtom != null && publicationAtom.startsWith("ref:"),
                "the populated seed's publication atom is the published value's creation "
                    + "allocation; got " + publicationAtom);
            checkEq(List.of(publicationAtom), populatedAtoms,
                "a populated HOST surface resolves to the recorded entry itself: the "
                    + "read's atom is the publication's own creation atom (the identical "
                    + "object, no wrap, no copy)");
            check(populatedRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the populated seed's invocation-free program succeeds: "
                    + populatedRun.terminal());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * The populated-surface seed's doctored unit: the HOST import and the
     * HOST read re-typed onto the compiled companion's identity (the
     * not-yet-landed load's effect — the module surface holds the recorded
     * entries under the module identity).
     */
    private static LoweredModuleUnit retypedHostImport(LoweredModuleUnit unit,
            ModuleId hostModule, ModuleId target, OpId hostReadOp) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                if (payload.kind() == ModuleImportKind.HOST
                        && payload.resolvedModule().equals(hostModule)) {
                    ops.add(withPayload(op, new KindPayload.ModuleImportPayload(
                        payload.rawSpecifier(), target, ModuleImportKind.HOST,
                        payload.aliasCells())));
                    continue;
                }
            }
            if (op.kind() == SemanticOpKind.EXPORT_READ && op.opId().equals(hostReadOp)) {
                KindPayload.ExportReadPayload payload =
                    (KindPayload.ExportReadPayload) op.payload();
                ops.add(withPayload(op, new KindPayload.ExportReadPayload(target,
                    payload.name(), payload.descriptor(), payload.value())));
                continue;
            }
            ops.add(op);
        }
        return withOps(unit, ops);
    }

    /** One rebuilt op with a replaced payload (its contract re-digested). */
    private static SemanticOp withPayload(SemanticOp op, KindPayload payload) {
        OperationContractSnapshot old = op.contract();
        OperationContractSnapshot blanked = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, old.opKind(), old.resultType(),
            old.operandTypes(), old.selector(), payload, old.failurePolicy(),
            old.referencedSemanticIds(), "");
        OperationContractSnapshot wired = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, old.opKind(), old.resultType(),
            old.operandTypes(), old.selector(), payload, old.failurePolicy(),
            old.referencedSemanticIds(),
            ContractSnapshotCanonicalizer.digest(blanked));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), wired);
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    private static Map<ModuleId, LoweredModuleUnit> modulesWith(
            ExecutableLoweredProject project, ModuleId module, LoweredModuleUnit unit) {
        Map<ModuleId, LoweredModuleUnit> modules =
            new LinkedHashMap<>(project.modules());
        modules.put(module, unit);
        return modules;
    }

    /** The owner publication's MODULE_EXPORT boundary input atom, or null. */
    private static String boundaryAtom(SemanticRuntimeModel.ConsumerRun run,
            LoweredModuleUnit owner) {
        SemanticOp publish = publishOpOf(owner);
        if (publish == null) {
            return null;
        }
        OpId boundaryOp = null;
        for (SemanticOp candidate : owner.ops()) {
            if (candidate.kind() == SemanticOpKind.BOUNDARY
                    && publish.opId().equals(candidate.origin().parentOpId())
                    && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                        == deal.semantic.ir.BoundaryKind.MODULE_EXPORT) {
                boundaryOp = candidate.opId();
            }
        }
        if (boundaryOp == null) {
            return null;
        }
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(boundaryOp)
                    && event.phase() == SemanticRuntimeModel.Phase.START
                    && !event.inputs().isEmpty()) {
                return event.inputs().get(0);
            }
        }
        return null;
    }

    private static Map<FunctionAllocationIdentity, FunctionExecutionBinding>
            withoutReadBinding(LoweredModuleUnit unit, ValueId readValue) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.remove(new FunctionAllocationIdentity(readValue.id()));
        return bindings;
    }

    private static LoweredModuleUnit withBindings(LoweredModuleUnit unit,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), bindings,
            unit.ops());
    }

    private static SemanticOp publishOpOf(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                return op;
            }
        }
        return null;
    }

    private static ModuleId hostImportModule(ExecutableLoweredProject project) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.MODULE_IMPORT) {
                    continue;
                }
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                if (payload.kind() == ModuleImportKind.HOST) {
                    return payload.resolvedModule();
                }
            }
        }
        throw new IllegalStateException("no HOST import in the project");
    }

    // =========================================================================
    // 4. The combined composition: the oracle and both per-unit artifacts
    // =========================================================================

    static void testCombinedPerUnitResolution() throws Exception {
        System.out.println("-- the combined per-unit probe: the compiled read and the "
            + "HOST read resolve consistently across the oracle and both per-unit "
            + "artifacts --");
        Fixture fixture = combinedFixture();
        Path workspace = Files.createTempDirectory("host-read-per-unit");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the combined probe lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId hostModule = hostImportModule(project);
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            List<SemanticOp> hostReads = readsOfModule(appUnit, hostModule);
            List<SemanticOp> compiledReads = readsOfModule(appUnit, LIB);
            if (hostReads.size() != 1 || compiledReads.size() != 1) {
                fail("the combined probe carries one compiled read and one HOST read");
                return;
            }
            String hostKey = traceOpKey(hostReads.get(0));
            String compiledKey = traceOpKey(compiledReads.get(0));

            // The oracle (the reference consumer).
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.executeProjectInits(project, result.tables(),
                    result.registries(), null);
            List<String> oracleCompiled = readAtoms(oracleRun, compiledReads);
            List<String> oracleHost = readAtoms(oracleRun, hostReads);
            checkEq(1, oracleCompiled.size(),
                "the oracle executes the compiled read exactly once");
            check(oracleCompiled.size() == 1 && oracleCompiled.get(0).startsWith("ref:"),
                "the oracle's compiled read publishes the owner's published value; got "
                    + oracleCompiled);
            checkEq(List.of("missing"), oracleHost,
                "the oracle's HOST read projects the absent-slot value (no load runs in "
                    + "the oracle)");

            // LuaJIT: the owner chunk first, then the entry chunk's deferred
            // main (the same program's chunk-global registry).
            Path libChunk = workspace.resolve("lib.lua");
            Path appChunk = workspace.resolve("app.lua");
            Files.writeString(libChunk, LuaSemanticEmitter.emitModule(libUnit,
                result.tables().get(LIB)), StandardCharsets.UTF_8);
            Files.writeString(appChunk, LuaSemanticEmitter.emitModule(appUnit,
                result.tables().get(APP)), StandardCharsets.UTF_8);
            Path driver = workspace.resolve("per-unit.lua");
            StringBuilder lua = new StringBuilder();
            lua.append("local __libOk, __libErr = pcall(dofile, ")
                .append(luaString(libChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __libOk then print(\"PROBE-FAIL: \"..tostring(__libErr)) "
                + "os.exit(1) end\n");
            lua.append("local __lPcallOk, __lOk, __lErr = pcall(__dealMain)\n");
            lua.append("if not __lPcallOk or not __lOk then print(\"PROBE-FAIL: \".."
                + "tostring(__lErr)) os.exit(1) end\n");
            lua.append("local __appOk, __appErr = pcall(dofile, ")
                .append(luaString(appChunk.toAbsolutePath().toString())).append(")\n");
            lua.append("if not __appOk then print(\"PROBE-FAIL: \"..tostring(__appErr)) "
                + "os.exit(1) end\n");
            lua.append("local __pOk, __ok, __err = pcall(__dealMain)\n");
            lua.append("if not __pOk then print(\"PROBE-FAIL: the entry main raised "
                + "\"..tostring(__ok)) os.exit(1) end\n");
            lua.append("if __ok then print(\"PROBE-FAIL: the entry main succeeded over "
                + "the absent host slot\") os.exit(1) end\n");
            lua.append("print(\"PROBE-OK\")\n");
            Files.writeString(driver, lua.toString(), StandardCharsets.UTF_8);
            ProcessOutcome luaRun = runProcessWithEnv(List.of("luajit",
                driver.toAbsolutePath().toString()), workspace,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(luaRun.exitCode() == 0 && luaRun.stdout().contains("PROBE-OK"),
                "the two-chunk per-unit drive runs: exit=" + luaRun.exitCode()
                    + " stdout=" + luaRun.stdout().replace("\n", "\\n") + " stderr="
                    + luaRun.stderr().replace("\n", "\\n"));
            checkEq(oracleCompiled, luaReadAtoms(luaRun.stderr(), List.of(compiledKey)),
                "the LuaJIT per-unit entry chunk resolves the owner chunk's published "
                    + "value (the identical atom)");
            checkEq(List.of("missing"), luaReadAtoms(luaRun.stderr(), List.of(hostKey)),
                "the LuaJIT per-unit entry chunk projects __MISSING for the HOST read");
            check(luaRun.stderr().contains("!E8001;expected function, got missing"),
                "the LuaJIT run fails at the function-typed binding boundary of the HOST "
                    + "read: " + luaRun.stderr().replace("\n", "\\n"));

            // The surface-populated state: the calls child's host load is
            // not landed, so the loaded module table's entry is seeded
            // directly under the module identity. The HOST read must
            // resolve exactly that entry — never a wrap, a copy, or the
            // absent sentinel.
            Path populatedDriver = workspace.resolve("populated.lua");
            StringBuilder seeded = new StringBuilder();
            seeded.append("__exportSurfaces = { [")
                .append(luaString(hostModule.path())).append("] = { ")
                .append(EXPORT_NAME).append(" = \"host-sentinel\" } }\n");
            seeded.append("local __libOk = pcall(dofile, ")
                .append(luaString(libChunk.toAbsolutePath().toString()))
                .append(")  if not __libOk then print(\"PROBE-FAIL: lib\") os.exit(1) "
                    + "end\n");
            seeded.append("local __lOk = select(2, pcall(__dealMain)) if not __lOk then "
                + "print(\"PROBE-FAIL: lib main\") os.exit(1) end\n");
            seeded.append("local __appOk = pcall(dofile, ")
                .append(luaString(appChunk.toAbsolutePath().toString()))
                .append(")  if not __appOk then print(\"PROBE-FAIL: app\") os.exit(1) "
                    + "end\n");
            seeded.append("local __pOk, __ok = pcall(__dealMain)\n");
            seeded.append("if not __pOk or __ok then print(\"PROBE-FAIL: the populated "
                + "entry main must fail at the seeded entry's boundary\") os.exit(1) end\n");
            seeded.append("print(\"PROBE-OK\")\n");
            Files.writeString(populatedDriver, seeded.toString(), StandardCharsets.UTF_8);
            ProcessOutcome populatedRun = runProcessWithEnv(List.of("luajit",
                populatedDriver.toAbsolutePath().toString()), workspace,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(populatedRun.exitCode() == 0 && populatedRun.stdout().contains("PROBE-OK"),
                "the surface-populated LuaJIT drive runs: exit="
                    + populatedRun.exitCode() + " stdout="
                    + populatedRun.stdout().replace("\n", "\\n") + " stderr="
                    + populatedRun.stderr().replace("\n", "\\n"));
            List<String> populatedAtoms = luaReadAtoms(populatedRun.stderr(),
                List.of(hostKey));
            check(populatedAtoms.size() == 1 && !"missing".equals(populatedAtoms.get(0)),
                "the LuaJIT HOST read resolves the seeded surface entry — never the "
                    + "absent slot; got " + populatedAtoms);
            check(populatedRun.stderr().contains("!E8001;expected function, got string"),
                "the LuaJIT boundary sees exactly the seeded entry's kind (the read "
                    + "returns the entry itself, never a wrap): "
                    + populatedRun.stderr().replace("\n", "\\n"));

            // JVM: the owner class first, then the entry class (the
            // program-scoped registry hosted with the runtime).
            JvmSemanticEmitter.EmissionResult libClass =
                JvmSemanticEmitter.emitModule(libUnit, result.tables().get(LIB));
            JvmSemanticEmitter.EmissionResult appClass =
                JvmSemanticEmitter.emitModule(appUnit, result.tables().get(APP));
            Path libSource = workspace.resolve(libClass.className() + ".java");
            Path appSource = workspace.resolve(appClass.className() + ".java");
            Files.writeString(libSource, libClass.source(), StandardCharsets.UTF_8);
            Files.writeString(appSource, appClass.source(), StandardCharsets.UTF_8);
            String driverClass = "HostReadPerUnitProbe";
            String populatedClass = "HostReadPopulatedProbe";
            Files.writeString(workspace.resolve(driverClass + ".java"),
                jvmProbeSource(libClass.className(), appClass.className(),
                    compiledReads.get(0), hostReads.get(0)),
                StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(populatedClass + ".java"),
                jvmPopulatedProbeSource(libClass.className(), appClass.className(),
                    hostReads.get(0), hostModule.path()),
                StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                libSource.toAbsolutePath().toString(),
                appSource.toAbsolutePath().toString(),
                workspace.resolve(driverClass + ".java").toAbsolutePath().toString(),
                workspace.resolve(populatedClass + ".java").toAbsolutePath().toString()),
                workspace);
            checkEq(0, javacRun.exitCode(),
                "the per-unit classes compile with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, driverClass), workspace);
                check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK"),
                    "the JVM per-unit drive: the compiled read resolves the owner's "
                        + "published value, the HOST read projects JvmRuntime.MISSING, "
                        + "and the binding boundary raises the pinned E8001; exit="
                        + javaRun.exitCode() + " stdout="
                        + javaRun.stdout().replace("\n", "\\n") + " stderr="
                        + javaRun.stderr().replace("\n", "\\n"));
                ProcessOutcome populatedJavaRun = runProcess(List.of("java", "-cp",
                    classpath + File.pathSeparator + classes, populatedClass), workspace);
                check(populatedJavaRun.exitCode() == 0
                        && populatedJavaRun.stdout().contains("PROBE-OK"),
                    "the surface-populated JVM drive "
                        + "runs: exit=" + populatedJavaRun.exitCode() + " stdout="
                        + populatedJavaRun.stdout().replace("\n", "\\n") + " stderr="
                        + populatedJavaRun.stderr().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The JVM per-unit probe: the two read slots and the pinned boundary. */
    private static String jvmProbeSource(String libClass, String appClass,
            SemanticOp compiledRead, SemanticOp hostRead) {
        StringBuilder source = new StringBuilder();
        source.append("public class HostReadPerUnitProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(libClass).append(".dealMain();\n");
        source.append("    try {\n");
        source.append("      ").append(appClass).append(".dealMain();\n");
        source.append("      check(false, \"the entry class fails at the HOST read's "
            + "function-typed binding boundary\");\n");
        source.append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n");
        source.append("      check(\"E8001\".equals(e.code), \"the binding boundary "
            + "raises the pinned E8001; got \" + e.code);\n");
        source.append("      check(String.valueOf(e.getMessage()).contains("
            + "\"expected function, got missing\"), \"the boundary names the absent-slot "
            + "value; got \" + e.getMessage());\n");
        source.append("    }\n");
        source.append("    Object published = deal.codegen.jvm.JvmRuntime.EXPORT_SURFACES"
            + ".get(\"lib\").entries.get(\"" + EXPORT_NAME + "\");\n");
        source.append("    Object compiled = ").append(appClass).append(".v")
            .append(((ValueId) compiledRead.result()).id()).append(";\n");
        source.append("    check(compiled != null && compiled == published, \"the per-unit "
            + "compiled read resolves the owner class's published object; got \" + "
            + "compiled + \" vs \" + published);\n");
        source.append("    Object host = ").append(appClass).append(".v")
            .append(((ValueId) hostRead.result()).id()).append(";\n");
        source.append("    check(host == deal.codegen.jvm.JvmRuntime.MISSING, \"the "
            + "per-unit HOST read projects JvmRuntime.MISSING; got \" + host);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    /**
     * The surface-populated JVM probe: the loaded module table's entry is
     * seeded under the module identity (the not-yet-landed load's effect),
     * and the HOST read must resolve exactly that entry.
     */
    private static String jvmPopulatedProbeSource(String libClass, String appClass,
            SemanticOp hostRead, String hostModulePath) {
        StringBuilder source = new StringBuilder();
        source.append("public class HostReadPopulatedProbe {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(libClass).append(".dealMain();\n");
        source.append("    deal.codegen.jvm.JvmRuntime.exportSurface(\"")
            .append(hostModulePath).append("\").write(\"")
            .append(EXPORT_NAME).append("\", \"host-sentinel\");\n");
        source.append("    try {\n");
        source.append("      ").append(appClass).append(".dealMain();\n");
        source.append("      check(false, \"the populated entry class fails at the seeded "
            + "entry's boundary\");\n");
        source.append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n");
        source.append("      check(\"E8001\".equals(e.code), \"the boundary raises the "
            + "pinned E8001; got \" + e.code);\n");
        source.append("      check(String.valueOf(e.getMessage()).contains("
            + "\"expected function, got string\"), \"the boundary sees exactly the "
            + "seeded entry; got \" + e.getMessage());\n");
        source.append("    }\n");
        source.append("    Object host = ").append(appClass).append(".v")
            .append(((ValueId) hostRead.result()).id()).append(";\n");
        source.append("    check(\"host-sentinel\".equals(host), \"the JVM HOST read "
            + "resolves the surface entry itself; got \" + host);\n");
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // 5. The production arm's host surface
    // =========================================================================

    static void testProductionGuard() throws Exception {
        System.out.println("-- the production arm: the HOST-importing closure "
            + "emits its declared-map load and stages the one project "
            + "artifact --");
        Fixture fixture = combinedFixture();
        try {
            Path out = fixture.root().resolve("out-arm");
            writeFileIn(out, "app.lua", "-- previous artifact\n");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            String chunk;
            try {
                result = ProductionProjectEmission.run(productionInvocation(),
                    fixture.checkedProject(), fixture.index(), fixture.manifests(),
                    fixture.surface(), fixture.declarationIdentities(),
                    fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                        fixture.checkedProject().modules().get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                    Set.of(), Backend.LUAJIT, false, fixture.distributionHome(), stager);
                check(result.emitted(),
                    "the HOST-importing closure emits: " + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the HOST-importing closure carries no diagnostic: "
                        + result.diagnostics());
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the HOST-importing closure stages its one project artifact");
                chunk = new String(stager.stagedSet().artifact("app.lua")
                    .orElseThrow().content(), StandardCharsets.UTF_8);
                stager.publish();
            } finally {
                stager.discard();
            }
            Map<String, String> after = snapshotTree(out);
            check(!after.containsKey("lib.lua")
                    && !after.containsKey("host/read_probe.lua"),
                "the HOST-importing closure stages no per-module sibling: "
                    + after.keySet());
            check(after.containsKey("app.lua")
                    && !"-- previous artifact\n".equals(after.get("app.lua")),
                "the one project artifact replaces the previous app.lua");
            check(chunk.contains("__rt.load_host(\"" + HOST_SPECIFIER + "\", "),
                "the emitted artifact carries the declared-map host load");
            check(chunk.contains("__exportSurfaces[\"" + HOST_MODULE_PATH + "\"]"),
                "the loaded table is published under the resolved module "
                    + "identity");
            check(!chunk.contains(ProductionProjectEmission.HOST_MODULE_IMPORT),
                "the emitted artifact carries no guard token");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Process and filesystem helpers
    // =========================================================================

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

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + needle.length());
        }
        return count;
    }

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
        testDeclarationOnlyFixtures();
        testEmittedRead();
        testOracleResolution();
        testCombinedPerUnitResolution();
        testProductionGuard();
        System.out.println();
        System.out.println("HostExportReadRealizationTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
