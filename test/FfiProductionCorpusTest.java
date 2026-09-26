package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.LuaFfiBindingGenerator;
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
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticProfile;
import deal.test.conformance.CorpusDiscovery;
import deal.test.conformance.CorpusFfi;
import deal.test.conformance.ErrorSnapshot;
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
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Stream;

/**
 * ISSUE-0670: the consolidated FFI production-corpus drive
 * ({@code luajit-ffi-load-emission-and-typed-crossings} Verification 1–4
 * and 7–8; {@code luajit-ffi-struct-plan-construction-and-oracle-projection}
 * Verification 1; {@code luajit-ffi-shared-emission-and-jvm-rejection}
 * Verification 1–4 and 7; the epic criteria).
 *
 * <p>One drive compiles every LuaJIT-executing FFI fixture
 * ({@code 012}, {@code 013}, {@code 014}, {@code 019}, {@code 020},
 * {@code 022}–{@code 027}, {@code 048}, {@code 049}, {@code 050},
 * {@code 051}) through the production pipeline with the corpus's
 * production FFI metadata
 * ({@code CorpusFfi.module(...).generatedModule()} and the bootstrapped
 * loader text) and executes each published artifact under {@code luajit}:
 * the {@code runtime-ok} fixtures compare exit code and both transcript
 * streams with their sidecars, and the {@code runtime-error} fixtures
 * compare the artifact's exit code, the captured
 * {@code code}/{@code message}/{@code sourceFile}/{@code line}/
 * {@code column} (transported from the deferred module-init entry
 * exactly as the corpus lane does), and the reconstructed canonical
 * {@code DEAL_ERROR_CODE}/{@code DEAL_ERROR_SNAPSHOT} transcript with
 * their sidecars — plus the production terminal's own
 * {@code DEAL_ERROR_CODE} line for the call-expression legs, whose
 * failures cross the host arm's error conversion.</p>
 *
 * <ol>
 *   <li>the corpus inventory is the pinned closed list: no fixture or
 *       sidecar is deleted or reshaped, {@code ffi/051} is the only
 *       addition, and {@code ffi/016} (the bytes child ISSUE-0626) is
 *       present and unclaimed;</li>
 *   <li>every driven artifact carries the {@code load_ffi} prelude with
 *       the metadata's module key, the generated bindings literal, and
 *       the import statement's span triplet, and carries no
 *       {@code require} of a dotted provider path;</li>
 *   <li>the six {@code FFI_*} codes keep their pinned origins: the two
 *       load codes ({@code FFI_SYMBOL_MISSING}, {@code FFI_LIBRARY_LOAD})
 *       at the import statement and the four call codes
 *       ({@code FFI_NULL_STRING}, {@code FFI_INVALID_UTF8},
 *       {@code FFI_NULL_POINTER}, {@code FFI_INVALID_STRING}) at the call
 *       expression;</li>
 *   <li>no compile-time library access: the fixtures whose configured
 *       library is never built and whose declared symbol is absent from
 *       the library both compile and emit, the emitted plan literal
 *       carries the deferred evaluator closures, and the generator's
 *       literals are byte-deterministic;</li>
 *   <li>no {@code ffi.C}/{@code ffi.cdef}/{@code dlopen}/{@code dlsym}
 *       text appears in any artifact.</li>
 * </ol>
 *
 * <p>This file is the integration verification of the FFI slice; the
 * per-slice drives ({@code FfiLoadEmissionTest},
 * {@code FfiTypedCrossingTest}, {@code FfiSixCodeCompletionTest},
 * {@code FfiValueReadInvocationTest}, {@code FfiStructConstructionTest})
 * remain those slices' verification.</p>
 */
public class FfiProductionCorpusTest {

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
    // The corpus
    // =========================================================================

    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String CORPUS_FFI_DIR =
        "test/conformance/" + CorpusFfi.FFI_DIR;
    private static final String NATIVE = "candidate/native";
    private static final String MISSING_SYMBOL = "candidate/native-missing-symbol";
    private static final String MISSING_LIBRARY =
        "candidate/native-missing-library";

    /** The bytes-value fixture the bytes child (ISSUE-0626) owns. */
    private static final String BYTES_FIXTURE = "016-ffi-bytes-pointer-length";

    /** The corpus-relative bytes-value fixture path. */
    private static final String BYTES_FIXTURE_PATH =
        CORPUS_FFI_DIR + "/" + BYTES_FIXTURE + ".deal";

    /** The declaration-negative fixture (a compile-time rejection). */
    private static final String ASYNC_DECLARATION =
        "047-ffi-async-declaration-rejected";

    /** The fixture ISSUE-0664 added (the only addition of the slice). */
    private static final String INVALID_STRING = "051-ffi-invalid-string";

    /** The closed six-code set of the FFI surface (spec :2916-2925). */
    private static final TreeSet<String> SIX_CODES = new TreeSet<>(List.of(
        "FFI_LIBRARY_LOAD", "FFI_SYMBOL_MISSING", "FFI_INVALID_STRING",
        "FFI_INVALID_UTF8", "FFI_NULL_STRING", "FFI_NULL_POINTER"));

    /** The origin class one sidecar's error span pins. */
    private enum Origin {
        IMPORT_STATEMENT, CALL_EXPRESSION
    }

    /** One corpus FFI fixture of the consolidated drive. */
    private record CorpusCase(String name, String specifier, Origin origin) {

        String corpusFixture() {
            return CORPUS_FFI_DIR + "/" + name + ".deal";
        }

        String sidecar() {
            return CORPUS_FFI_DIR + "/" + name + ".expect.json";
        }

        String dotted() {
            return specifier.replace('/', '.');
        }

        String moduleKey() {
            return "ffi:@$external/" + specifier;
        }
    }

    private static CorpusCase caseOf(String name, String specifier,
            Origin origin) {
        return new CorpusCase(name, specifier, origin);
    }

    /** The pinned fixture inventory of the corpus FFI directory. */
    private static final List<String> CORPUS_FIXTURES = List.of(
        "012-ffi-double-roundtrip",
        "013-ffi-boolean-roundtrip",
        "014-ffi-string-utf8-parameter",
        BYTES_FIXTURE,
        "019-ffi-struct-copy-isolation",
        "020-ffi-pointer-token",
        "022-ffi-null-string",
        "023-ffi-invalid-utf8",
        "024-ffi-null-pointer",
        "025-ffi-missing-symbol",
        "026-ffi-library-load-failure",
        "027-ffi-unsupported-backends",
        ASYNC_DECLARATION,
        "048-ffi-int32-minimum-roundtrip",
        "049-ffi-void-null-return",
        "050-ffi-borrowed-string-copy",
        INVALID_STRING);

    /** The sidecar inventory (the declaration negative carries none). */
    private static final List<String> CORPUS_SIDECARS = CORPUS_FIXTURES.stream()
        .filter(name -> !name.equals(ASYNC_DECLARATION))
        .toList();

    private static final CorpusCase CASE_DOUBLE =
        caseOf("012-ffi-double-roundtrip", NATIVE, null);
    private static final CorpusCase CASE_BOOLEAN =
        caseOf("013-ffi-boolean-roundtrip", NATIVE, null);
    private static final CorpusCase CASE_UTF8_PARAMETER =
        caseOf("014-ffi-string-utf8-parameter", NATIVE, null);
    private static final CorpusCase CASE_STRUCT =
        caseOf("019-ffi-struct-copy-isolation", NATIVE, null);
    private static final CorpusCase CASE_POINTER =
        caseOf("020-ffi-pointer-token", NATIVE, null);
    private static final CorpusCase CASE_NULL_STRING =
        caseOf("022-ffi-null-string", NATIVE, Origin.CALL_EXPRESSION);
    private static final CorpusCase CASE_INVALID_UTF8 =
        caseOf("023-ffi-invalid-utf8", NATIVE, Origin.CALL_EXPRESSION);
    private static final CorpusCase CASE_NULL_POINTER =
        caseOf("024-ffi-null-pointer", NATIVE, Origin.CALL_EXPRESSION);
    private static final CorpusCase CASE_MISSING_SYMBOL =
        caseOf("025-ffi-missing-symbol", MISSING_SYMBOL,
            Origin.IMPORT_STATEMENT);
    private static final CorpusCase CASE_MISSING_LIBRARY =
        caseOf("026-ffi-library-load-failure", MISSING_LIBRARY,
            Origin.IMPORT_STATEMENT);
    private static final CorpusCase CASE_UNSUPPORTED_BACKENDS =
        caseOf("027-ffi-unsupported-backends", NATIVE, null);
    private static final CorpusCase CASE_INT32_MINIMUM =
        caseOf("048-ffi-int32-minimum-roundtrip", NATIVE, null);
    private static final CorpusCase CASE_VOID_NULL =
        caseOf("049-ffi-void-null-return", NATIVE, null);
    private static final CorpusCase CASE_BORROWED_STRING =
        caseOf("050-ffi-borrowed-string-copy", NATIVE, null);
    private static final CorpusCase CASE_INVALID_STRING =
        caseOf(INVALID_STRING, NATIVE, Origin.CALL_EXPRESSION);
    private static final CorpusCase CASE_BYTES =
        caseOf(BYTES_FIXTURE, NATIVE, null);

    /**
     * The driven set: every LuaJIT-executing fixture. {@code ffi/016} is
     * the bytes child's ({@code ISSUE-0626}) and is not claimed or driven
     * here; {@code ffi/047} is a compile-time declaration negative with no
     * runtime leg.
     */
    private static final List<CorpusCase> DRIVEN = List.of(
        CASE_DOUBLE, CASE_BOOLEAN, CASE_UTF8_PARAMETER, CASE_STRUCT,
        CASE_POINTER, CASE_NULL_STRING, CASE_INVALID_UTF8, CASE_NULL_POINTER,
        CASE_MISSING_SYMBOL, CASE_MISSING_LIBRARY, CASE_UNSUPPORTED_BACKENDS,
        CASE_INT32_MINIMUM, CASE_VOID_NULL, CASE_BORROWED_STRING,
        CASE_INVALID_STRING);

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        Path mirror,
        Path entry,
        int strippedHeaderLines,
        String strippedSource,
        String specifier,
        String dotted,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    /** One published production artifact. */
    private record Artifact(String name, String text) {
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

    /**
     * Compiles one corpus FFI fixture project through the real frontend.
     * The fixture is materialized at its corpus-relative path inside a
     * temp mirror (so the emitted error {@code sourceFile} normalizes to
     * the sidecar's pin exactly as the corpus lane's deployment map
     * does), with the classification headers stripped from both the
     * fixture and its declaration (the emitted coordinates are the
     * stripped ones; the drive rebases them onto the raw fixture for the
     * sidecar comparison).
     */
    private static Fixture compile(CorpusCase corpusCase) throws Exception {
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT,
            corpusCase.specifier());
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + corpusCase.specifier() + "'");
        }
        String declaration = ConformanceHarnessMetadata
            .stripClassificationHeaders(Files.readString(CONFORMANCE_ROOT
                .resolve(CorpusFfi.FFI_DIR)
                .resolve(wiring.declarationCorpusPath()), StandardCharsets.UTF_8));
        String rawFixture = Files.readString(Path.of(corpusCase.corpusFixture()),
            StandardCharsets.UTF_8);
        String app = ConformanceHarnessMetadata.stripClassificationHeaders(rawFixture);
        int stripped = rawFixture.split("\n", -1).length
            - app.split("\n", -1).length;
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT,
            corpusCase.specifier(), SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException("the corpus declaration of '"
                + corpusCase.specifier() + "' does not validate: "
                + module.validationDiagnostics());
        }

        Path root = Files.createTempDirectory("ffi-production-corpus");
        Path mirror = root.resolve("corpus");
        Path entry = mirror.resolve(CorpusFfi.FFI_DIR)
            .resolve(corpusCase.name() + ".deal");
        Files.createDirectories(entry.getParent());
        Files.writeString(entry, app, StandardCharsets.UTF_8);
        Path declarationFile = root.resolve("native.d.deal");
        Files.writeString(declarationFile, declaration, StandardCharsets.UTF_8);

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, false, false, false, Backend.LUAJIT,
            Map.of(corpusCase.specifier(), declarationFile.toString()),
            List.of(entry.getParent()), null, null, harnessInvocation());
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
            throw new IllegalStateException("the FFI fixture '"
                + corpusCase.name() + "' did not build: " + detail + " / "
                + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        externCModules.put(new ModuleId(corpusCase.dotted()),
            module.generatedModule());
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(corpusCase.specifier()));
        }
        return new Fixture(root, mirror, entry, stripped, app,
            corpusCase.specifier(), corpusCase.dotted(), built.input(),
            built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
    }

    /** Emits one fixture through the production arm and publishes it. */
    private static Artifact emit(Fixture fixture, Path out) throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = ProductionProjectEmission.run(productionInvocation(),
                fixture.checkedProject(), fixture.index(), fixture.manifests(),
                fixture.surface(), fixture.declarationIdentities(),
                fixture.externCModules(), fixture.mirror().toString(),
                BuiltinErrorDeclaration.synthesized(
                    fixture.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                Set.of(), Backend.LUAJIT, false,
                deal.distribution.DistributionHome.forManifestDirectory(
                    fixture.mirror().toString()),
                stager);
            if (result.emitted()) {
                stager.publish();
            }
        } finally {
            stager.discard();
        }
        if (!result.emitted()) {
            throw new IllegalStateException("the FFI fixture artifact did not "
                + "emit: " + result.diagnostics());
        }
        String name = result.artifactRelativePath();
        return new Artifact(name,
            Files.readString(out.resolve(name), StandardCharsets.UTF_8));
    }

    // =========================================================================
    // Sidecar access and corpus-lane normalization
    // =========================================================================

    private static SidecarExpectations.StructuredExpectationSidecar sidecar(
            CorpusCase corpusCase) throws Exception {
        return SidecarExpectations.StructuredExpectationSidecar.parse(
            Files.readString(Path.of(corpusCase.sidecar()), StandardCharsets.UTF_8));
    }

    /** The pinned LuaJIT execution expectation of one corpus sidecar. */
    private static SidecarExpectations.RuntimeExpectation.Executed luajit(
            CorpusCase corpusCase) throws Exception {
        SidecarExpectations.RuntimeExpectation expectation =
            sidecar(corpusCase).expectationFor("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
            throw new IllegalStateException("the LuaJIT leg of "
                + corpusCase.name() + " is not an executed expectation");
        }
        return executed;
    }

    /**
     * Normalizes one captured origin file into the corpus-relative form
     * (the corpus lane's deployment-map normalization).
     */
    private static String corpusSourceFile(Fixture fixture, String capturedFile) {
        Path mirror = fixture.mirror().toAbsolutePath().normalize();
        Path captured = Path.of(capturedFile).toAbsolutePath().normalize();
        if (!captured.startsWith(mirror)) {
            throw new IllegalStateException("the captured origin file '"
                + capturedFile + "' is outside the corpus mirror '" + mirror + "'");
        }
        return CorpusDiscovery.slash(mirror.relativize(captured));
    }

    private static int lineOf(String source, String text) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(text)) {
                return i + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + text + "'");
    }

    private static int columnOf(String source, String text) {
        for (String line : source.split("\n", -1)) {
            int at = line.indexOf(text);
            if (at >= 0) {
                return at + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + text + "'");
    }

    private static String expectedTagOf(String source) {
        for (String line : source.split("\n", -1)) {
            String trimmed = line.trim();
            if (trimmed.startsWith("// @expected:")) {
                return trimmed.substring("// @expected:".length()).trim();
            }
        }
        throw new IllegalStateException("the fixture carries no @expected tag");
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
    // 1. The corpus inventory
    // =========================================================================

    private static void testCorpusInventory() throws Exception {
        System.out.println("-- the corpus inventory: no fixture or sidecar is "
            + "deleted or reshaped, ffi/051 is the only addition, and "
            + "ffi/016 stays unclaimed --");
        Path ffiDir = CONFORMANCE_ROOT.resolve(CorpusFfi.FFI_DIR);
        List<String> fixtureNames;
        List<String> sidecarNames;
        try (Stream<Path> entries = Files.list(ffiDir)) {
            List<String> files = entries
                .map(path -> path.getFileName().toString())
                .sorted()
                .toList();
            fixtureNames = files.stream()
                .filter(name -> name.endsWith(".deal"))
                .map(name -> name.substring(0, name.length() - ".deal".length()))
                .toList();
            sidecarNames = files.stream()
                .filter(name -> name.endsWith(".expect.json"))
                .map(name -> name.substring(0,
                    name.length() - ".expect.json".length()))
                .toList();
        }
        checkEq(CORPUS_FIXTURES, fixtureNames,
            "the corpus FFI fixture inventory is the pinned closed list");
        checkEq(CORPUS_SIDECARS, sidecarNames,
            "the corpus FFI sidecar inventory is the pinned closed list");
        check(fixtureNames.contains(INVALID_STRING)
                && sidecarNames.contains(INVALID_STRING),
            "ffi/051 is present as the slice's addition (the only member of "
                + "the pinned list outside the pre-ISSUE-0664 set)");
        check(fixtureNames.contains(BYTES_FIXTURE)
                && sidecarNames.contains(BYTES_FIXTURE),
            "ffi/016 is present and unclaimed (the bytes child ISSUE-0626 "
                + "owns its row)");
        check(!DRIVEN.stream().map(CorpusCase::name).toList()
                .contains(BYTES_FIXTURE),
            "the drive never drives ffi/016");

        // The claimed set is exactly the executing set minus the bytes
        // child's fixture: every other fixture with a LuaJIT execution leg
        // is driven here.
        List<String> driven = DRIVEN.stream().map(CorpusCase::name).toList();
        checkEq(CORPUS_FIXTURES.stream()
                .filter(name -> !name.equals(BYTES_FIXTURE))
                .filter(name -> !name.equals(ASYNC_DECLARATION))
                .toList(),
            driven,
            "the driven set is exactly the LuaJIT-executing fixtures "
                + "(ffi/016 excluded to the bytes child)");
        // ffi/016 stays authored: the bytes child (ISSUE-0626) owns its
        // row, and this drive neither claims nor executes it.
        String bytesSource = Files.readString(
            Path.of(BYTES_FIXTURE_PATH), StandardCharsets.UTF_8);
        checkEq("runtime-ok", expectedTagOf(bytesSource).split(" ")[0],
            "ffi/016 keeps its authored runtime-ok classification");
        checkEq("runtime-ok", luajit(CASE_BYTES).mode(),
            "ffi/016 keeps its authored LuaJIT sidecar leg");

        // Every driven fixture's classification tag agrees with its
        // sidecar's LuaJIT leg, and the sanctioned jvm/js legs stay the
        // E6006 compile rejections.
        for (CorpusCase corpusCase : DRIVEN) {
            String source = Files.readString(Path.of(corpusCase.corpusFixture()),
                StandardCharsets.UTF_8);
            SidecarExpectations.RuntimeExpectation.Executed expectation =
                luajit(corpusCase);
            checkEq(expectation.mode(), expectedTagOf(source).split(" ")[0],
                corpusCase.name() + " keeps its classification and sidecar mode "
                    + "in agreement");
            check(corpusCase.origin() == null || expectation.isRuntimeError(),
                corpusCase.name() + " is the runtime-error case its origin "
                    + "class names");
            for (String backend : List.of("jvm", "js")) {
                SidecarExpectations.RuntimeExpectation leg =
                    sidecar(corpusCase).expectationFor(backend);
                check(leg instanceof SidecarExpectations.RuntimeExpectation.Rejected,
                    corpusCase.name() + " keeps its " + backend
                        + " compile-reject leg");
                if (leg instanceof SidecarExpectations.RuntimeExpectation.Rejected
                        rejected) {
                    checkEq("compile-reject", rejected.mode(),
                        corpusCase.name() + " " + backend + " mode");
                    checkEq("E6006", rejected.code(),
                        corpusCase.name() + " " + backend + " diagnostic code");
                }
            }
        }

        // The declaration negative keeps its pinned compile-time
        // rejection and carries no runtime sidecar.
        String asyncSource = Files.readString(Path.of(CORPUS_FFI_DIR + "/"
            + ASYNC_DECLARATION + ".deal"), StandardCharsets.UTF_8);
        checkEq("compile-error", expectedTagOf(asyncSource).split(" ")[0],
            "ffi/047 stays the E7002 declaration negative");
        checkEq("E7002", expectedTagOf(asyncSource).split(" ")[1],
            "ffi/047 pins the declaration diagnostic code");
        check(!sidecarNames.contains(ASYNC_DECLARATION),
            "ffi/047 carries no runtime sidecar and is not driven");
    }

    // =========================================================================
    // 2. The consolidated production drive
    // =========================================================================

    private static Map<String, String> testConsolidatedDrive() throws Exception {
        System.out.println("-- the consolidated production-corpus drive: every "
            + "LuaJIT-executing FFI fixture compiles through the production arm "
            + "and executes under luajit --");
        Map<String, String> executedCodes = new TreeMap<>();
        List<String> preludeCases = new ArrayList<>();
        int okCases = 0;
        int errorCases = 0;
        for (CorpusCase corpusCase : DRIVEN) {
            Fixture fixture = compile(corpusCase);
            Path out = fixture.root().resolve("out-prod");
            try {
                Artifact artifact = emit(fixture, out);
                String text = artifact.text();
                checkEq(corpusCase.name() + ".lua", artifact.name(),
                    "the entry module's chunk is the one staged artifact");

                // T1 — the emitted FFI load at the owning MODULE_IMPORT,
                // with the metadata's module key and the generated
                // bindings literal.
                String surfaceKey = "__exportSurfaces[\""
                    + corpusCase.dotted() + "\"]";
                check(text.contains(surfaceKey + " = " + surfaceKey
                        + " or __rt.load_ffi(\"" + corpusCase.moduleKey()
                        + "\", "),
                    "the artifact publishes the loaded table through the "
                        + "load_ffi prelude: " + corpusCase.name());
                check(text.contains("local __ffi_bindings_1 = { moduleKey = \""
                        + corpusCase.moduleKey() + "\","),
                    "the load carries the generated bindings literal from the "
                        + "compile's metadata: " + corpusCase.name());
                check(text.contains("nativeLibrary = { kind = "),
                    "the load carries the generated cdef bundle literal: "
                        + corpusCase.name());
                int importLine = lineOf(fixture.strippedSource(),
                    "import * as native");
                int importColumn = columnOf(fixture.strippedSource(),
                    "import * as native");
                check(text.contains(", \"" + fixture.entry() + "\", "
                        + importLine + ", " + importColumn + ")"),
                    "the load carries the import statement's span triplet: "
                        + corpusCase.name());
                check(!text.contains("require(\"candidate"),
                    "no dotted provider require line is emitted: "
                        + corpusCase.name());
                check(!text.contains("ffi.cdef") && !text.contains("ffi.C[")
                        && !text.contains("ffi.C.") && !text.contains("ffi.new")
                        && !text.contains("ffi.cast") && !text.contains("dlopen")
                        && !text.contains("dlsym"),
                    "the artifact carries no ffi.C/cdef or loader-symbol text: "
                        + corpusCase.name());
                preludeCases.add(corpusCase.name());

                SidecarExpectations.RuntimeExpectation.Executed expectation =
                    luajit(corpusCase);
                if (!expectation.isRuntimeError()) {
                    okCases++;
                    ProcessOutcome run = runProcess(
                        List.of("luajit", artifact.name()), out, Map.of());
                    checkEq(expectation.exitCode(), run.exitCode(),
                        corpusCase.name() + " exit code matches the sidecar");
                    checkEq(new String(expectation.stdout(),
                            StandardCharsets.UTF_8),
                        run.stdout(), corpusCase.name() + " stdout transcript");
                    checkEq(new String(expectation.stderr(),
                            StandardCharsets.UTF_8),
                        run.stderr(), corpusCase.name() + " stderr transcript");
                } else {
                    errorCases++;
                    SidecarExpectations.ErrorExpectation pinned =
                        expectation.error();

                    // The production terminal exits with the sidecar's
                    // exit code (the run terminal for a failed module-init
                    // or call).
                    ProcessOutcome terminal = runProcess(
                        List.of("luajit", artifact.name()), out, Map.of());
                    checkEq(expectation.exitCode(), terminal.exitCode(),
                        corpusCase.name() + " exit code matches the sidecar");
                    if (corpusCase.origin() == Origin.CALL_EXPRESSION) {
                        // A call-expression failure crosses the host arm's
                        // error conversion, so the artifact's own terminal
                        // publishes the DEAL_ERROR_CODE line.
                        checkEq("", terminal.stderr(),
                            corpusCase.name() + " writes no stderr");
                        checkEq(ErrorSnapshot.CODE_LINE_PREFIX + pinned.code()
                                + "\n",
                            terminal.stdout(),
                            "the production terminal publishes the "
                                + "DEAL_ERROR_CODE line: " + corpusCase.name());
                    }

                    // The deferred probe (the module-init entry suppressed
                    // as the corpus lane does) captures the error fields;
                    // each one compares with the sidecar under the corpus
                    // lane's normalization.
                    Files.writeString(out.resolve("probe.lua"),
                        failureProbe(artifact.name()), StandardCharsets.UTF_8);
                    ProcessOutcome probe = runProcess(
                        List.of("luajit", "probe.lua"), out,
                        Map.of("DEAL_DEFER_MAIN", "1"));
                    checkEq(0, probe.exitCode(), corpusCase.name()
                        + " failure probe runs: " + escaped(probe.stderr()));
                    String[] parts = probe.stdout().trim().split("\\|", -1);
                    if (parts.length != 6) {
                        fail(corpusCase.name() + " failure probe projected "
                            + parts.length + " fields: "
                            + escaped(probe.stdout()));
                        continue;
                    }
                    checkEq("ERR", parts[0], corpusCase.name()
                        + " raises a DEAL error");
                    checkEq(pinned.code(), parts[1],
                        corpusCase.name() + " code matches the sidecar");
                    checkEq(pinned.message(), parts[2],
                        corpusCase.name() + " message matches the sidecar");
                    String normalizedFile = corpusSourceFile(fixture, parts[3]);
                    checkEq(pinned.sourceFile(), normalizedFile,
                        corpusCase.name() + " sourceFile matches the sidecar "
                            + "(corpus-relative)");
                    int rawLine = Integer.parseInt(parts[4])
                        + fixture.strippedHeaderLines();
                    checkEq(pinned.line(), Integer.valueOf(rawLine),
                        corpusCase.name() + " line matches the sidecar "
                            + "(rebased onto raw fixture coordinates)");
                    checkEq(pinned.column(), Integer.valueOf(parts[5]),
                        corpusCase.name() + " column matches the sidecar");

                    // The pinned origin class: the import statement for
                    // the two load codes, the call expression for the
                    // four call codes.
                    String anchor = corpusCase.origin()
                        == Origin.IMPORT_STATEMENT
                            ? "import * as native" : "native.ffi_";
                    String raw = Files.readString(
                        Path.of(corpusCase.corpusFixture()),
                        StandardCharsets.UTF_8);
                    checkEq(lineOf(raw, anchor), pinned.line(),
                        corpusCase.name() + " pins the " + corpusCase.origin()
                            + " line");
                    checkEq(columnOf(raw, anchor), pinned.column(),
                        corpusCase.name() + " pins the " + corpusCase.origin()
                            + " column");

                    // The captured fields reproduce the sidecar's
                    // transcript byte-for-byte (the DEAL_ERROR_CODE line
                    // plus the canonical snapshot).
                    SidecarExpectations.ErrorExpectation captured =
                        new SidecarExpectations.ErrorExpectation(parts[1],
                            parts[2], normalizedFile, rawLine,
                            Integer.parseInt(parts[5]), Optional.empty(),
                            Optional.empty(), Optional.empty(),
                            Optional.empty());
                    String framing = ErrorSnapshot.CODE_LINE_PREFIX
                        + captured.code() + "\n"
                        + ErrorSnapshot.SNAPSHOT_LINE_PREFIX
                        + ErrorSnapshot.canonicalJson(captured) + "\n";
                    checkEq(new String(expectation.stdout(),
                            StandardCharsets.UTF_8),
                        framing,
                        corpusCase.name() + " reproduces the sidecar transcript "
                            + "byte-for-byte");
                    checkEq(new String(expectation.stderr(),
                            StandardCharsets.UTF_8),
                        "",
                        corpusCase.name() + " pins an empty stderr transcript");
                    executedCodes.put(captured.code(), corpusCase.name());
                }
            } finally {
                deleteRecursively(fixture.root());
            }
        }
        checkEq(DRIVEN.size(), preludeCases.size(),
            "every driven artifact carries the load_ffi prelude");
        checkEq(9, okCases, "the drive's runtime-ok cases");
        checkEq(6, errorCases, "the drive's runtime-error cases");
        return executedCodes;
    }

    // =========================================================================
    // 3. The six-code coverage and origins
    // =========================================================================

    private static void testSixCodeCoverage(Map<String, String> executedCodes) {
        System.out.println("-- the drive executes exactly the closed six FFI_* "
            + "codes with their pinned origins --");
        checkEq(SIX_CODES, new TreeSet<>(executedCodes.keySet()),
            "the executed FFI_* code set is the closed six");
        checkEq("025-ffi-missing-symbol", executedCodes.get("FFI_SYMBOL_MISSING"),
            "FFI_SYMBOL_MISSING keeps the import-statement origin (025)");
        checkEq("026-ffi-library-load-failure",
            executedCodes.get("FFI_LIBRARY_LOAD"),
            "FFI_LIBRARY_LOAD keeps the import-statement origin (026)");
        checkEq("022-ffi-null-string", executedCodes.get("FFI_NULL_STRING"),
            "FFI_NULL_STRING keeps the call-expression origin (022)");
        checkEq("023-ffi-invalid-utf8", executedCodes.get("FFI_INVALID_UTF8"),
            "FFI_INVALID_UTF8 keeps the call-expression origin (023)");
        checkEq("024-ffi-null-pointer", executedCodes.get("FFI_NULL_POINTER"),
            "FFI_NULL_POINTER keeps the call-expression origin (024)");
        checkEq(INVALID_STRING, executedCodes.get("FFI_INVALID_STRING"),
            "FFI_INVALID_STRING is the 051 fixture's production-artifact "
                + "method (the call-expression origin)");
    }

    // =========================================================================
    // 4. No compile-time library, symbol, or evaluator access
    // =========================================================================

    private static void testNoCompileTimeAccess() throws Exception {
        System.out.println("-- no library, symbol, or evaluator at compile: the "
            + "never-built library and the absent symbol both emit, and the "
            + "plan literal stays deferred --");

        // (1) The missing-library wiring: the configured library is never
        // built, yet the compile and the emission both succeed — a
        // compile-time library open would fail here. The emitted loader
        // text is the never-built path; only the runtime open reports
        // FFI_LIBRARY_LOAD (the 026 case above).
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT,
            MISSING_LIBRARY);
        String loaderText = CorpusFfi.loaderTextFor(CONFORMANCE_ROOT, wiring);
        check(!Files.exists(Path.of(loaderText)),
            "the 026 configured library is never built: " + loaderText);
        Fixture libraryFixture = compile(CASE_MISSING_LIBRARY);
        try {
            Artifact artifact = emit(libraryFixture,
                libraryFixture.root().resolve("out-no-library"));
            check(artifact.text().contains(loaderText),
                "the compile emits the load prelude although the library does "
                    + "not exist (no library open at compile)");
        } finally {
            deleteRecursively(libraryFixture.root());
        }

        // (2) The missing-symbol wiring: the declaration names a symbol
        // absent from the library, yet validation and generation both
        // succeed — symbol resolution happens only at load (the 025 case
        // above).
        CorpusFfi.Module missingSymbolModule = CorpusFfi.module(
            CONFORMANCE_ROOT, MISSING_SYMBOL, SemanticProfile.DEAL_V1_2_INT32);
        check(missingSymbolModule.generatedModule() != null,
            "the absent symbol still compiles to a generated module");
        check(missingSymbolModule.generatedModule().descriptor().functions()
                .stream().anyMatch(fn -> "ffi_missing_symbol".equals(
                    fn.dealName())),
            "the generated module carries the absent symbol's declaration "
                + "(no symbol resolution at compile)");
        check(!missingSymbolModule.generatedModule().cdefBundle()
                .nativeLibraryLoaderText().isEmpty(),
            "the generated module carries its native-library loader text "
                + "verbatim");

        // (3) The plan literal stays deferred: the generated plan model
        // carries the evaluator content and the emitted literal carries
        // the closures — no evaluator value is precomputed at compile.
        CorpusFfi.Module nativeModule = CorpusFfi.module(CONFORMANCE_ROOT,
            NATIVE, SemanticProfile.DEAL_V1_2_INT32);
        FfiCompilerClassDefaultPlan pairPlan =
            nativeModule.generatedModule().plans().values().stream()
                .filter(plan -> plan.classIdentityText().endsWith("/Pair"))
                .findFirst()
                .orElseThrow(() -> new IllegalStateException(
                    "the corpus declaration carries no Pair plan"));
        checkEq(List.of("left", "right"),
            pairPlan.entries().stream().map(
                FfiCompilerClassDefaultPlan.Entry::name).toList(),
            "the Pair plan carries its fields in declaration order");
        check(pairPlan.entries().stream()
                .allMatch(FfiCompilerClassDefaultPlan.Entry::hasDefaultEvaluator),
            "every Pair field carries a deferred default evaluator");
        check(pairPlan.entries().stream()
                .allMatch(entry -> entry.evaluatorContent() != null),
            "the evaluators stay canonical content, never a computed value");
        Fixture structFixture = compile(CASE_STRUCT);
        try {
            Artifact artifact = emit(structFixture,
                structFixture.root().resolve("out-deferred"));
            check(artifact.text().contains("evaluator = function() return 0 end"),
                "the emitted plan literal carries the deferred evaluator "
                    + "closures (never a precomputed value)");
            check(artifact.text().contains("local function __ffiClassPlan(module, class)")
                    && artifact.text().contains("return surface[class..\"_plan\"]"),
                "the plan reference resolves through the chunk's export-surface "
                    + "registry (never a dotted-path require)");
            check(artifact.text().contains("pcall(__rt.class_plan_, "),
                "the construction site calls the runtime plan entry");
            check(artifact.text().contains("__hostDealProject("),
                "the constructed instance is projected into the chunk "
                    + "representation");
        } finally {
            deleteRecursively(structFixture.root());
        }

        // (4) The generator's literals are byte-deterministic: two
        // generations of the same module produce equal parts (no
        // evaluator side effect, no address or ordinal in the literals).
        LuaFfiBindingGenerator.Generation first = LuaFfiBindingGenerator
            .generate(nativeModule.generatedModule(), "", "__ffi_bindings_1",
                "__ffi_provider_1_");
        LuaFfiBindingGenerator.Generation second = LuaFfiBindingGenerator
            .generate(nativeModule.generatedModule(), "", "__ffi_bindings_1",
                "__ffi_provider_1_");
        check(first.failure() == null && second.failure() == null,
            "the corpus module generates without a failure");
        checkEq(first.parts(), second.parts(),
            "the generated loader literals are byte-deterministic");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Production-Corpus Integration Tests "
            + "(ISSUE-0670) ===");
        testCorpusInventory();
        Map<String, String> executedCodes = testConsolidatedDrive();
        testSixCodeCoverage(executedCodes);
        testNoCompileTimeAccess();
        System.out.println();
        System.out.println("passed: " + passed + ", failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
