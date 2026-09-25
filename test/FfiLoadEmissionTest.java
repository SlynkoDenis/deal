package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaFfiBindingGenerator;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiCompilerClassDefaultPlan;
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
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticProfile;
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
 * ISSUE-0662: the extern-C admission and the emitted FFI load prelude
 * ({@code luajit-ffi-load-emission-and-typed-crossings} F1/F2 and the FFI
 * import and load contract; {@code ffi-admission-and-jvm-e6006-rejection}
 * A1; sequencing step 1).
 *
 * <ol>
 *   <li>the closure guard's merged state: the extern-C declaration
 *       import is admitted (the corpus drive emits its {@code load_ffi}
 *       prelude) and the HOST declaration import is admitted by the
 *       calls child's realized declared-map load (ISSUE-0656), while the
 *       guard's stable {@code HOST_MODULE_IMPORT} token, its
 *       whole-closure step, and its E6005
 *       {@code SHARED_EMITTER_COVERAGE} producer stay landed (a
 *       superseded shape is replaced, never deleted);</li>
 *   <li>the corpus fixtures {@code ffi/025}, {@code ffi/026}, and
 *       {@code ffi/027} compile through the production arm with the
 *       corpus's production FFI metadata
 *       ({@code CorpusFfi.module(...).generatedModule()}) and execute under
 *       {@code luajit} with the sidecar-pinned outcomes: the emitted
 *       {@code load_ffi} prelude carries the descriptor's module key, the
 *       generated bundle/plans/bindings literals, and the import
 *       statement's span triplet; {@code FFI_SYMBOL_MISSING} and
 *       {@code FFI_LIBRARY_LOAD} carry the import origin; {@code ffi/027}
 *       runs clean;</li>
 *   <li>the load happens once per module per program and both aliases of a
 *       two-alias import observe the one loaded surface value;</li>
 *   <li>the fail-closed seeds — a missing generated-module entry, a
 *       provider module outside the declaration surface, and an
 *       unserializable generated module — each fail with E6005 and stage
 *       nothing, and the emission input's presence rule throws at the
 *       emitter;</li>
 *   <li>no compile-time library access: the {@code ffi/026} load is
 *       emitted although the wiring's library is never built, the artifact
 *       carries no {@code ffi.C}/cdef text, and no provider {@code require}
 *       line is emitted.</li>
 * </ol>
 */
public class FfiLoadEmissionTest {

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
    // The corpus fixtures
    // =========================================================================

    private static final String CORPUS_FFI_DIR = "test/conformance/backend-runtime/ffi";
    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");

    /** One corpus FFI fixture of the production drive. */
    private record CorpusCase(String name, String specifier) {

        String corpusFixture() {
            return CORPUS_FFI_DIR + "/" + name + ".deal";
        }

        String sidecar() {
            return CORPUS_FFI_DIR + "/" + name + ".expect.json";
        }

        String dotted() {
            return specifier.replace('/', '.');
        }
    }

    private static final CorpusCase MISSING_SYMBOL =
        new CorpusCase("025-ffi-missing-symbol", "candidate/native-missing-symbol");
    private static final CorpusCase MISSING_LIBRARY =
        new CorpusCase("026-ffi-library-load-failure", "candidate/native-missing-library");
    private static final CorpusCase UNSUPPORTED_BACKENDS =
        new CorpusCase("027-ffi-unsupported-backends", "candidate/native");

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        Path sourceRoot,
        String specifier,
        String dotted,
        int headerLinesStripped,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** Compiles one corpus fixture project through the real frontend. */
    private static Fixture compileCorpus(CorpusCase corpusCase) throws Exception {
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT,
            corpusCase.specifier());
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + corpusCase.specifier() + "'");
        }
        String declaration = Files.readString(CONFORMANCE_ROOT
            .resolve(CorpusFfi.FFI_DIR).resolve(wiring.declarationCorpusPath()),
            StandardCharsets.UTF_8);
        String rawFixture = Files.readString(Path.of(corpusCase.corpusFixture()),
            StandardCharsets.UTF_8);
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT,
            corpusCase.specifier(), SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException("the corpus declaration of '"
                + corpusCase.specifier() + "' does not validate: "
                + module.validationDiagnostics());
        }
        Fixture fixture = compileSource(corpusCase.name(),
            "native.d.deal", declaration,
            corpusCase.specifier(), rawFixture, Map.of());
        Map<ModuleId, FfiGeneratedModule> modules = new LinkedHashMap<>();
        modules.put(new ModuleId(fixture.dotted()), module.generatedModule());
        return new Fixture(fixture.root(), fixture.sourceRoot(),
            fixture.specifier(), fixture.dotted(),
            fixture.headerLinesStripped(), fixture.checkedProject(),
            fixture.index(), fixture.manifests(), fixture.surface(), modules,
            fixture.declarationIdentities());
    }

    /**
     * Materializes one-declaration project and compiles it through the
     * real frontend (the declaration is externals-wired; the entry named
     * for the case imports it). The classification headers are stripped
     * from every corpus source and the stripped line count is returned for
     * the raw-coordinate pins.
     */
    private static Fixture compileSource(String name, String declarationFile,
            String declarationRaw, String specifier, String fixtureRaw,
            Map<String, String> extraSources) throws Exception {
        String declaration = ConformanceHarnessMetadata
            .stripClassificationHeaders(declarationRaw);
        String app = ConformanceHarnessMetadata.stripClassificationHeaders(fixtureRaw);
        int stripped = fixtureRaw.split("\n", -1).length
            - app.split("\n", -1).length;
        Path root = Files.createTempDirectory("ffi-load-emission");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(declarationFile), declaration,
            StandardCharsets.UTF_8);
        for (Map.Entry<String, String> extra : extraSources.entrySet()) {
            Path target = src.resolve(extra.getKey());
            Files.createDirectories(target.getParent());
            Files.writeString(target, extra.getValue(), StandardCharsets.UTF_8);
        }
        Files.writeString(src.resolve(name + ".deal"), app, StandardCharsets.UTF_8);
        Path entry = src.resolve(name + ".deal").toAbsolutePath();
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(specifier,
            src.resolve(declarationFile).toAbsolutePath().toString());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, false, false, false, Backend.LUAJIT,
            externals, List.of(src.toAbsolutePath()), null, null,
            harnessInvocation());
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
            throw new IllegalStateException("the FFI fixture '" + name
                + "' did not build: " + detail + " / " + orchestrator.diagnostics());
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
                new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, src, specifier, specifier.replace('/', '.'),
            stripped, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
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

    /** Runs the production arm with the fixture's own metadata. */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            PublicationStager stager) throws Exception {
        return emit(fixture, stager, fixture.externCModules());
    }

    private static ProductionProjectEmission.Result emit(Fixture fixture,
            PublicationStager stager,
            Map<ModuleId, FfiGeneratedModule> externCModules)
            throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(), externCModules,
            fixture.sourceRoot().toString(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), Backend.LUAJIT, false,
            deal.distribution.DistributionHome.forManifestDirectory(
                fixture.sourceRoot().toString()),
            stager);
    }

    // =========================================================================
    // 1. The corpus production drive (025 / 026 / 027 under luajit)
    // =========================================================================

    private static void testCorpusProductionDrive() throws Exception {
        System.out.println("-- the corpus FFI fixtures compile through the "
            + "production arm and execute under luajit --");
        for (CorpusCase corpusCase : List.of(MISSING_SYMBOL, MISSING_LIBRARY,
                UNSUPPORTED_BACKENDS)) {
            Fixture fixture = compileCorpus(corpusCase);
            Path out = fixture.root().resolve("out-prod");
            try {
                PublicationStager stager = PublicationStager.forRoot(out);
                ProductionProjectEmission.Result result;
                try {
                    result = emit(fixture, stager);
                    if (result.emitted()) {
                        stager.publish();
                    }
                } finally {
                    stager.discard();
                }
                check(result.emitted(), "the extern-C fixture '"
                    + corpusCase.name() + "' emits one project artifact: "
                    + result.diagnostics());
                if (!result.emitted()) {
                    continue;
                }
                checkEq(corpusCase.name() + ".lua",
                    result.artifactRelativePath(),
                    "the one project artifact is named for the entry module");
                String artifact = Files.readString(
                    out.resolve(corpusCase.name() + ".lua"),
                    StandardCharsets.UTF_8);
                String key = "__exportSurfaces[\"" + fixture.dotted() + "\"]";
                check(artifact.contains(key + " = " + key + " or __rt.load_ffi("
                        + "\"ffi:@$external/" + corpusCase.specifier() + "\", "),
                    "the artifact publishes the loaded table through the "
                        + "load_ffi call at the import's MODULE_IMPORT: "
                        + corpusCase.name());
                check(artifact.contains("local __ffi_bindings_1 = { moduleKey = "
                        + "\"ffi:@$external/" + corpusCase.specifier() + "\","),
                    "the bindings literal comes from the generated metadata: "
                        + corpusCase.name());
                check(artifact.contains("nativeLibrary = { kind = "),
                    "the bundle literal carries the native-library reference: "
                        + corpusCase.name());
                int stripped = fixture.headerLinesStripped();
                check(artifact.contains(", \""
                        + fixture.sourceRoot().resolve(corpusCase.name()
                            + ".deal").toAbsolutePath() + "\", "
                        + (6 - stripped) + ", 1)"),
                    "the load carries the import statement's span triplet "
                        + "(the sidecar's raw 6:1 rebased by the stripped "
                        + "headers): " + corpusCase.name());
                check(!artifact.contains("require(\"candidate"),
                    "no provider require line is emitted: " + corpusCase.name());
                check(!artifact.contains("ffi.C") && !artifact.contains("cdef("),
                    "the artifact carries no ffi.C/cdef text: "
                        + corpusCase.name());

                SidecarExpectations.RuntimeExpectation.Executed expectation =
                    luajitExpectation(corpusCase);
                if ("runtime-ok".equals(expectation.mode())) {
                    ProcessOutcome run = runProcess(List.of("luajit",
                        corpusCase.name() + ".lua"), out, Map.of());
                    check(run.exitCode() == 0 && run.stdout().isEmpty()
                            && run.stderr().isEmpty(),
                        "the runtime-ok fixture '" + corpusCase.name()
                            + "' executes clean: exit=" + run.exitCode()
                            + " stdout=" + escaped(run.stdout())
                            + " stderr=" + escaped(run.stderr()));
                } else {
                    Files.writeString(out.resolve("probe.lua"),
                        failureProbe(corpusCase.name() + ".lua"),
                        StandardCharsets.UTF_8);
                    ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"),
                        out, Map.of("DEAL_DEFER_MAIN", "1"));
                    check(run.exitCode() == 0,
                        "the failure probe of '" + corpusCase.name()
                            + "' runs: exit=" + run.exitCode() + " "
                            + escaped(run.stderr()));
                    if (run.exitCode() != 0) {
                        continue;
                    }
                    String[] parts = run.stdout().trim().split("\\|", -1);
                    checkEq("ERR", parts[0], corpusCase.name()
                        + " raises a DEAL error");
                    if (!"ERR".equals(parts[0])) {
                        continue;
                    }
                    checkEq(expectation.error().code(), parts[1],
                        corpusCase.name() + " pinned code");
                    checkEq(expectation.error().message(), parts[2],
                        corpusCase.name() + " pinned message");
                    checkEq(String.valueOf(expectation.error().line()
                            - stripped), parts[4],
                        corpusCase.name() + " pinned origin line (rebased)");
                    checkEq(String.valueOf(expectation.error().column()),
                        parts[5], corpusCase.name() + " pinned origin column");
                    check(parts[3].endsWith(corpusCase.name() + ".deal"),
                        corpusCase.name() + " pinned origin file: " + parts[3]);
                }
            } finally {
                deleteRecursively(fixture.root());
            }
        }
    }

    /** The pinned LuaJIT execution expectation of one corpus sidecar. */
    private static SidecarExpectations.RuntimeExpectation.Executed
            luajitExpectation(CorpusCase corpusCase) throws Exception {
        String json = Files.readString(Path.of(corpusCase.sidecar()),
            StandardCharsets.UTF_8);
        SidecarExpectations.StructuredExpectationSidecar sidecar =
            SidecarExpectations.StructuredExpectationSidecar.parse(json);
        SidecarExpectations.RuntimeExpectation expectation =
            sidecar.byBackend().get("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
            throw new IllegalStateException("the LuaJIT sidecar of "
                + corpusCase.name() + " is not an executed expectation: " + json);
        }
        return executed;
    }

    /**
     * The LuaJIT failure probe: the deferred main's DEAL failure projected
     * to {@code ERR|code|message|file|line|column} (the production chunk's
     * deferred entry, never the chunk's own terminal).
     */
    /**
     * The LuaJIT failure probe of one artifact: the deferred main's DEAL
     * failure projected to {@code ERR|code|message|file|line|column} (the
     * production chunk's deferred entry, never the chunk's own terminal).
     */
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
            print("ERR|" .. tostring(err.code) .. "|" .. tostring(err.message)
              .. "|" .. tostring(err.file) .. "|" .. tostring(err.line) .. "|"
              .. tostring(err.column))
            """.formatted(artifactName);
    }

    // =========================================================================
    // 2. One load per module, shared by aliases
    // =========================================================================

    private static final String HOST_DECLARATION = """
        export function ping(): string;
        """;

    private static final String HOST_APP = """
        import * as host from "host/probe"

        export function main(): null {
          return null
        }
        """;

    private static void testAdmittedImportsAndRetainedGuardProducer()
            throws Exception {
        System.out.println("-- the admitted declaration imports (the calls "
            + "child's load_host) and the retained HOST_MODULE_IMPORT "
            + "producer --");
        Fixture fixture = compileSource("host-guard", "probe.d.deal",
            HOST_DECLARATION, "host/probe", HOST_APP, Map.of());
        try {
            Path out = fixture.root().resolve("out-host");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            String artifact;
            try {
                result = emit(fixture, stager);
                check(result.emitted(),
                    "the HOST declaration import is admitted (ISSUE-0656's "
                        + "realized host load): " + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the admitted HOST declaration import carries no "
                        + "guard diagnostic: " + result.diagnostics());
                check(stager.stagedSet().artifact("host-guard.lua").isPresent(),
                    "the admitted HOST declaration import stages its one "
                        + "project artifact");
                artifact = new String(stager.stagedSet().artifact("host-guard.lua")
                    .orElseThrow().content(), StandardCharsets.UTF_8);
            } finally {
                stager.discard();
            }
            check(result.emitted()
                    && "host-guard.lua".equals(result.artifactRelativePath()),
                "the HOST declaration import stages the entry module's chunk");
            check(artifact.contains("__rt.load_host(\"host/probe\", "),
                "the admitted HOST declaration import emits its "
                    + "declared-map load: " + artifact);
            check(!artifact.contains("__rt.load_ffi("),
                "the HOST declaration import selects no FFI load");
            check(!artifact.contains(
                    ProductionProjectEmission.HOST_MODULE_IMPORT),
                "the emitted chunk carries no guard token");
        } finally {
            deleteRecursively(fixture.root());
        }

        // The retained producer: the guard step, the stable
        // HOST_MODULE_IMPORT token, and the E6005 SHARED_EMITTER_COVERAGE
        // builder stay in the production unit (a superseded shape is
        // replaced, never deleted).
        String unit = Files.readString(
            Path.of("deal", "module", "ProductionProjectEmission.java"),
            StandardCharsets.UTF_8);
        check(unit.contains("hostImportGuard")
                && unit.contains(ProductionProjectEmission.HOST_MODULE_IMPORT)
                && unit.contains("hostModuleImportFailure")
                && unit.contains("SHARED_EMITTER_COVERAGE"),
            "the production unit keeps the guard step, its stable token, "
                + "and its E6005 producer");

        // The retained producer's pinned projection: the E6005
        // SHARED_EMITTER_COVERAGE / HOST_MODULE_IMPORT text with the
        // emitting module, the import's raw specifier, and the resolved
        // module — the landed detail fields, kept though no HOST-kind
        // shape fires after the two realizations.
        java.lang.reflect.Method failureBuilder =
            ProductionProjectEmission.class.getDeclaredMethod(
                "hostModuleImportFailure", ModuleId.class, String.class,
                String.class, CompilerInvocation.class);
        failureBuilder.setAccessible(true);
        deal.diagnostics.CompilerDiagnostic diagnostic =
            (deal.diagnostics.CompilerDiagnostic) failureBuilder.invoke(
                null, new ModuleId("app"), "host/probe", "host.probe",
                productionInvocation());
        check(diagnostic != null && "E6005".equals(diagnostic.code())
                && diagnostic.message().contains(
                    ProductionProjectEmission.SHARED_EMITTER_COVERAGE)
                && diagnostic.message().contains(
                    ProductionProjectEmission.HOST_MODULE_IMPORT)
                && diagnostic.message().contains("'host/probe'")
                && diagnostic.message().contains("'host.probe'"),
            "the retained guard producer keeps the E6005 "
                + "SHARED_EMITTER_COVERAGE/HOST_MODULE_IMPORT projection "
                + "naming the raw specifier and the resolved module: "
                + diagnostic);
    }

    private static final String TWO_ALIAS_DECLARATION = """
        // @extern-c
        export function ffi_identity_int(value: int): int;
        """;

    private static final String TWO_ALIAS_APP = """
        import * as first from "candidate/native"
        import * as second from "candidate/native"

        export function main(): null {
          return null
        }
        """;

    private static void testLoadOnceSharedByAliases() throws Exception {
        System.out.println("-- the two-alias import: one load per module, one "
            + "shared surface value --");
        Fixture fixture = compileSource("two-alias", "native.d.deal",
            TWO_ALIAS_DECLARATION, "candidate/native", TWO_ALIAS_APP, Map.of());
        Path out = fixture.root().resolve("out-prod");
        try {
            CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT,
                "candidate/native", SemanticProfile.DEAL_V1_2_INT32);
            Map<ModuleId, FfiGeneratedModule> modules = new LinkedHashMap<>();
            modules.put(new ModuleId(fixture.dotted()),
                module.generatedModule());
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(fixture, stager, modules);
                if (result.emitted()) {
                    stager.publish();
                }
            } finally {
                stager.discard();
            }
            check(result.emitted(), "the two-alias extern-C closure emits: "
                + result.diagnostics());
            if (!result.emitted()) {
                return;
            }
            String artifact = Files.readString(out.resolve("two-alias.lua"),
                StandardCharsets.UTF_8);
            checkEq(2, countOccurrences(artifact, "__rt.load_ffi("),
                "the two aliases emit the guarded load twice at their own "
                    + "import positions");
            check(Files.readString(Path.of("deal/runtime.lua"),
                    StandardCharsets.UTF_8).contains("__rt.load_ffi = function"),
                "the deployed runtime serves load_ffi");

            Files.writeString(out.resolve("probe.lua"), """
                package.path = "./?.lua;./std/?.lua;" .. package.path
                local rt = require("deal.runtime")
                local loads = 0
                local real = rt.load_ffi
                rt.load_ffi = function(...)
                  loads = loads + 1
                  return real(...)
                end
                local surface = dofile("two-alias.lua")
                local ok, err = __dealMain()
                if not ok then
                  print("PROBE-FAIL|" .. tostring(err and err.code))
                  os.exit(1)
                end
                if loads ~= 1 then
                  print("PROBE-FAIL|loads=" .. loads)
                  os.exit(1)
                end
                if type(__exportSurfaces["candidate.native"]) ~= "table" then
                  print("PROBE-FAIL|no surface")
                  os.exit(1)
                end
                print("PROBE-OK")
                """, StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"), out,
                Map.of("DEAL_DEFER_MAIN", "1"));
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "one load per module and one shared surface value: exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The fail-closed seeds
    // =========================================================================

    private static void testMissingMetadataSeed() throws Exception {
        System.out.println("-- the missing generated-module entry fails closed "
            + "--");
        Fixture fixture = compileCorpus(UNSUPPORTED_BACKENDS);
        try {
            // The arm: the compile's extern-C metadata is absent, so the
            // lowering's declaration-kind agreement fails E6005 and nothing
            // stages.
            Path out = fixture.root().resolve("out-missing");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(fixture, stager, Map.of());
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the missing-metadata compile stages nothing");
            } finally {
                stager.discard();
            }
            check(!result.emitted(),
                "the extern-C closure without generated metadata fails closed");
            check(result.firstDiagnostic() != null
                    && "E6005".equals(result.firstDiagnostic().code()),
                "the missing-metadata failure is E6005: " + result.diagnostics());
            check(result.firstDiagnostic() != null
                    && result.firstDiagnostic().message()
                        .contains(fixture.dotted()),
                "the failure names the declaration module: "
                    + result.diagnostics());

            // The emission input's presence rule: a session carrying the
            // input whose extern-C import resolves no generated module is a
            // producer defect, never a silently omitted load.
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the fixture lowers: " + lowered.diagnostics());
                return;
            }
            boolean threw = false;
            try {
                LuaSemanticEmitter.emitProductionProject(lowered.project(),
                    lowered.tables(), lowered.registries(), fixture.surface(),
                    new FfiEmissionInput(Map.of(), fixture.sourceRoot().toString()));
            } catch (IllegalStateException expected) {
                threw = true;
                check(expected.getMessage().contains(fixture.dotted())
                        && expected.getMessage().contains("FFI emission input"),
                    "the presence rule names the module and the input: "
                        + expected.getMessage());
            }
            check(threw, "the emission input's presence rule throws");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testProviderGapSeed() throws Exception {
        System.out.println("-- a provider outside the declaration surface "
            + "fails the compile closed --");
        Fixture fixture = compileSource("provider-gap", "probe.d.deal", """
            import * as util from "./util"

            // @extern-c

            // @c-struct
            export class Pair {
              left: int = util.helper();
            }

            export function probe(): int;
            """, "native/probe", """
            import * as native from "native/probe"

            export function main(): null {
              return null
            }
            """, Map.of("util.deal", """
            export function helper(): int {
              return 1;
            }
            """));
        try {
            check(!fixture.externCModules().isEmpty(),
                "the provider-gap fixture publishes its generated metadata");
            for (FfiGeneratedModule module
                    : fixture.externCModules().values()) {
                checkEq(1, module.bindings().importedFunctions().size(),
                    "the generated metadata carries the imported reference");
            }
            Path out = fixture.root().resolve("out-gap");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(fixture, stager);
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the provider-gap compile stages nothing");
            } finally {
                stager.discard();
            }
            check(!result.emitted(),
                "a provider outside the declaration surface fails closed");
            String message = result.firstDiagnostic() == null ? ""
                : result.firstDiagnostic().message();
            check(result.firstDiagnostic() != null
                    && "E6005".equals(result.firstDiagnostic().code())
                    && message.contains("SHARED_EMITTER_COVERAGE")
                    && message.contains("util")
                    && message.contains("wrapper surface"),
                "the provider gap is E6005 SHARED_EMITTER_COVERAGE naming the "
                    + "provider: " + result.diagnostics());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testGeneratorFailureSeed() throws Exception {
        System.out.println("-- an unserializable generated module fails the "
            + "compile closed --");
        Fixture fixture = compileCorpus(UNSUPPORTED_BACKENDS);
        try {
            CorpusFfi.Module corpusModule = CorpusFfi.module(CONFORMANCE_ROOT,
                "candidate/native", SemanticProfile.DEAL_V1_2_INT32);
            FfiGeneratedModule original = corpusModule.generatedModule();
            Map<String, FfiCompilerClassDefaultPlan> plans =
                new LinkedHashMap<>(original.plans());
            String identity = plans.keySet().iterator().next();
            FfiCompilerClassDefaultPlan plan = plans.get(identity);
            List<FfiCompilerClassDefaultPlan.Entry> entries = new ArrayList<>();
            for (FfiCompilerClassDefaultPlan.Entry entry : plan.entries()) {
                entries.add(new FfiCompilerClassDefaultPlan.Entry(
                    entry.name(), entry.canonicalDescriptor(), entry.optional(),
                    entry.hasDefaultEvaluator(), "{\"k\":\"unsupported\"}"));
            }
            plans.put(identity, new FfiCompilerClassDefaultPlan(
                plan.classIdentityText(), entries, plan.canonicalPlanContent(),
                plan.semanticDefaultContents(),
                plan.evaluatorImplementationContents(), plan.planDigest()));
            FfiGeneratedModule doctored = new FfiGeneratedModule(
                original.modulePath(), original.descriptor(),
                original.cdefBundle(), plans, original.bindings());
            Map<ModuleId, FfiGeneratedModule> modules = new LinkedHashMap<>();
            modules.put(new ModuleId(fixture.dotted()), doctored);

            Path out = fixture.root().resolve("out-generator");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(fixture, stager, modules);
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the generator-failure compile stages nothing");
            } finally {
                stager.discard();
            }
            check(!result.emitted(),
                "an unserializable generated module fails closed");
            String message = result.firstDiagnostic() == null ? ""
                : result.firstDiagnostic().message();
            check(result.firstDiagnostic() != null
                    && "E6005".equals(result.firstDiagnostic().code())
                    && message.contains("SHARED_EMITTER_COVERAGE")
                    && message.contains("cannot be serialized"),
                "the generator failure is E6005 SHARED_EMITTER_COVERAGE: "
                    + result.diagnostics());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The trace session and the provider binding
    // =========================================================================

    private static void testTraceSessionAndProviderBindings() throws Exception {
        System.out.println("-- a trace session over an extern-C closure emits "
            + "no load; the provider bindings resolve through the surface "
            + "registry --");
        Fixture fixture = compileCorpus(UNSUPPORTED_BACKENDS);
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            String trace = LuaSemanticEmitter.emitProject(project,
                lowered.tables(), lowered.registries(), fixture.surface());
            check(!trace.contains("__rt.load_ffi(")
                    && !trace.contains("__rt.load_host("),
                "the trace session emits no FFI load call (its surface is the "
                    + "scenario seam's)");
            check(trace.contains("local __rt = require(\"deal.runtime\")"),
                "the trace session still binds the runtime for the FFI arms");
            check(LuaFfiBindingGenerator.providerBindings(
                    CorpusFfi.module(CONFORMANCE_ROOT, "candidate/native",
                        SemanticProfile.DEAL_V1_2_INT32).generatedModule()
                        .bindings()).isEmpty(),
                "the corpus declaration carries no provider bindings");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // The gate
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Load Emission Tests (ISSUE-0662) ===");
        System.out.println();
        testCorpusProductionDrive();
        testAdmittedImportsAndRetainedGuardProducer();
        testLoadOnceSharedByAliases();
        testMissingMetadataSeed();
        testProviderGapSeed();
        testGeneratorFailureSeed();
        testTraceSessionAndProviderBindings();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Load Emission Tests Passed ===");
    }

    // =========================================================================
    // Process and filesystem helpers
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

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        for (int at = text.indexOf(needle); at >= 0;
                at = text.indexOf(needle, at + needle.length())) {
            count++;
        }
        return count;
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
