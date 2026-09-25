package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.ffi.FfiCdefBundle;
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
import deal.test.conformance.SidecarSchemaValidator;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

/**
 * ISSUE-0664: the new {@code ffi/051-ffi-invalid-string} fixture and the
 * six-code completion ({@code luajit-ffi-load-emission-and-typed-crossings}
 * Verification 3; the FFI typed call and value-read contract's
 * {@code FFI_INVALID_STRING} row; sequencing step 3).
 *
 * <ol>
 *   <li>the fixture imports {@code candidate/native} and {@code std/json},
 *       obtains a U+0000-bearing string through
 *       {@code json.parse("{\"s\":\"\\u0000\"}")} (the retained FFIGEN
 *       scenario — the spec pins no source-literal escape for U+0000),
 *       passes it to {@code native.ffi_echo}, and pins
 *       {@code runtime-error FFI_INVALID_STRING} at the call
 *       expression;</li>
 *   <li>the sidecar carries the LuaJIT runtime-error expectation (the
 *       code, the runtime's embedded-NUL message, and the call-expression
 *       origin) plus the {@code jvm}/{@code js} {@code compile-reject}
 *       E6006 entries, and validates clean in the sanctioned divergent C6
 *       form;</li>
 *   <li>the drive compiles the fixture through the production arm with the
 *       corpus's production FFI metadata and executes the emitted artifact
 *       under {@code luajit}: the artifact carries the {@code load_ffi}
 *       prelude (the T1 load) and the string parameter's
 *       {@code DEAL_TO_HOST} + {@code HOST_PARAMETER} crossing plus the
 *       loaded wrapper's {@code .f} invocation (the T2 string crossing);
 *       the run's captured error compares field-exact with the sidecar
 *       ({@code code}, {@code message}, {@code sourceFile}, {@code line},
 *       {@code column}) and its canonical G4.6 framing reproduces the
 *       sidecar transcript with the {@code DEAL_ERROR_CODE} line;</li>
 *   <li>the scenario's dependency on both halves is proven: with the
 *       generated module's library missing the run fails on the FFI load
 *       (never {@code FFI_INVALID_STRING}), and the same fixture with a
 *       NUL-free payload executes the native echo clean;</li>
 *   <li>the corpus's LuaJIT FFI sidecars cover exactly the closed six
 *       {@code FFI_*} codes with their pinned origins (the import statement
 *       for the two load codes, the call expression for the four call
 *       codes), {@code FFI_INVALID_STRING} supplied by this fixture — the
 *       sixth and final production-artifact method.</li>
 * </ol>
 */
public class FfiSixCodeCompletionTest {

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

    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String FFI_DIR = CorpusFfi.FFI_DIR;
    private static final String NATIVE = "candidate/native";
    private static final String NATIVE_DOTTED = "candidate.native";
    private static final String NATIVE_MODULE_KEY = "ffi:@$external/candidate/native";
    private static final String NAME = "051-ffi-invalid-string";
    private static final String FIXTURE_PATH = FFI_DIR + "/" + NAME + ".deal";
    private static final String SIDECAR_PATH = FFI_DIR + "/" + NAME + ".expect.json";
    private static final String NUL_MESSAGE =
        "string argument contains an embedded NUL character";

    /** The closed six-code set of the epic's completion (spec :2916-2925). */
    private static final Set<String> SIX_CODES = Set.of(
        "FFI_LIBRARY_LOAD", "FFI_SYMBOL_MISSING", "FFI_INVALID_STRING",
        "FFI_INVALID_UTF8", "FFI_NULL_STRING", "FFI_NULL_POINTER");

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

    // =========================================================================
    // The compile harness
    // =========================================================================

    /**
     * One compiled fixture project: the temp root, the corpus mirror whose
     * relative layout reproduces the corpus coordinates (so the emitted
     * error {@code sourceFile} normalizes to the sidecar's pin exactly as
     * the corpus lane's deployment map does), the entry file, and the
     * checked-project inputs the production arm consumes.
     */
    private record Fixture(
        Path root,
        Path mirror,
        Path entry,
        int strippedHeaderLines,
        String strippedSource,
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

    private static Fixture compile(String fixtureSource) throws Exception {
        String app = ConformanceHarnessMetadata
            .stripClassificationHeaders(fixtureSource);
        int stripped = fixtureSource.split("\n", -1).length
            - app.split("\n", -1).length;
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT, NATIVE);
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + NATIVE + "'");
        }
        String declaration = ConformanceHarnessMetadata.stripClassificationHeaders(
            Files.readString(CONFORMANCE_ROOT.resolve(FFI_DIR)
                .resolve(wiring.declarationCorpusPath()), StandardCharsets.UTF_8));
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT, NATIVE,
            SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException(
                "the corpus declaration of '" + NATIVE + "' does not validate: "
                    + module.validationDiagnostics());
        }
        Path root = Files.createTempDirectory("ffi-six-code");
        Path mirror = root.resolve("corpus");
        Path entry = mirror.resolve(FIXTURE_PATH);
        Files.createDirectories(entry.getParent());
        Files.writeString(entry, app, StandardCharsets.UTF_8);
        Path declarationFile = root.resolve("native.d.deal");
        Files.writeString(declarationFile, declaration, StandardCharsets.UTF_8);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, false, false, false, Backend.LUAJIT,
            Map.of(NATIVE, declarationFile.toString()),
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
            throw new IllegalStateException("the FFI fixture did not build: "
                + detail + " / " + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        externCModules.put(new ModuleId(NATIVE_DOTTED), module.generatedModule());
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(NATIVE));
        }
        return new Fixture(root, mirror, entry, stripped, app, built.input(),
            built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
    }

    /** Emits one fixture through the production arm and publishes it. */
    private static Artifact emit(Fixture fixture,
            Map<ModuleId, FfiGeneratedModule> externCModules, Path out)
            throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = ProductionProjectEmission.run(productionInvocation(),
                fixture.checkedProject(), fixture.index(), fixture.manifests(),
                fixture.surface(), fixture.declarationIdentities(), externCModules,
                fixture.mirror().toString(),
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

    /** One generated module whose native library text names a missing file. */
    private static FfiGeneratedModule withMissingLibrary(FfiGeneratedModule module,
            Path missing) {
        FfiCdefBundle bundle = module.cdefBundle();
        return new FfiGeneratedModule(module.modulePath(), module.descriptor(),
            new FfiCdefBundle(bundle.bundleDigest(), bundle.identityDigest(),
                bundle.fullContent(), bundle.entries(), bundle.nativeLibraryKind(),
                missing.toAbsolutePath().toString(), bundle.functions(),
                bundle.classes()),
            module.plans(), module.bindings());
    }

    // =========================================================================
    // 1. The fixture and its sidecar
    // =========================================================================

    private static String fixtureSource() throws Exception {
        return Files.readString(CONFORMANCE_ROOT.resolve(FIXTURE_PATH),
            StandardCharsets.UTF_8);
    }

    private static SidecarExpectations.StructuredExpectationSidecar sidecar()
            throws Exception {
        return SidecarExpectations.StructuredExpectationSidecar.parse(
            Files.readString(CONFORMANCE_ROOT.resolve(SIDECAR_PATH),
                StandardCharsets.UTF_8));
    }

    private static SidecarExpectations.ErrorExpectation luajitError(
            SidecarExpectations.StructuredExpectationSidecar sidecar) {
        SidecarExpectations.RuntimeExpectation expectation =
            sidecar.expectationFor("luajit");
        if (!(expectation
                instanceof SidecarExpectations.RuntimeExpectation.Executed executed)
                || !executed.isRuntimeError() || executed.error() == null) {
            throw new IllegalStateException("the LuaJIT leg of the 051 sidecar "
                + "is not a pinned runtime-error expectation");
        }
        return executed.error();
    }

    private static String expectedTagOf(String source) {
        for (String line : source.split("\n", -1)) {
            String trimmed = line.trim();
            if (trimmed.startsWith("// @expected:")) {
                return trimmed.substring("// @expected:".length()).trim();
            }
        }
        throw new IllegalStateException("the 051 fixture carries no @expected "
            + "tag");
    }

    private static void testFixtureAndSidecar() throws Exception {
        System.out.println("-- the fixture text and the sanctioned divergent "
            + "sidecar --");
        String source = fixtureSource();
        checkEq("runtime-error FFI_INVALID_STRING", expectedTagOf(source),
            "the fixture pins the sixth code");
        check(source.contains("import * as native from \"candidate/native\";"),
            "the fixture imports the extern-C declaration module");
        check(source.contains("import * as json from \"std/json\";"),
            "the fixture imports std/json for the U+0000 payload");
        check(source.contains("json.parse(\"{\\\"s\\\":\\\"\\\\u0000\\\"}\")"),
            "the payload's string field is the backslash-u0000 escape");
        check(source.contains("let value: string = doc.s;"),
            "the parsed field is carried as a DEAL string");
        check(source.contains("native.ffi_echo(value)"),
            "the string is passed to the declared native export");

        // The call-expression origin the sidecar pins is the call itself.
        int callLine = lineOf(source, "native.ffi_echo");
        int callColumn = columnOf(source, "native.ffi_echo");
        check(source.split("\n", -1)[callLine - 1]
                .substring(callColumn - 1)
                .startsWith("native.ffi_echo(value)"),
            "the pinned column is the start of the call expression");

        SidecarExpectations.StructuredExpectationSidecar sidecar = sidecar();
        SidecarExpectations.ErrorExpectation error = luajitError(sidecar);
        checkEq("FFI_INVALID_STRING", error.code(), "the sidecar pins the code");
        checkEq(NUL_MESSAGE, error.message(),
            "the sidecar pins the runtime's embedded-NUL message");
        checkEq(FIXTURE_PATH, error.sourceFile(),
            "the sidecar pins the fixture as the error origin");
        checkEq(callLine, error.line(), "the sidecar pins the call line");
        checkEq(callColumn, error.column(), "the sidecar pins the call column");

        // The jvm/js legs are the sanctioned C6 split.
        SidecarExpectations.RuntimeExpectation jvm = sidecar.expectationFor("jvm");
        SidecarExpectations.RuntimeExpectation js = sidecar.expectationFor("js");
        check(jvm instanceof SidecarExpectations.RuntimeExpectation.Rejected,
            "the jvm leg is a compile-reject expectation");
        check(js instanceof SidecarExpectations.RuntimeExpectation.Rejected,
            "the js leg is a compile-reject expectation");
        if (jvm instanceof SidecarExpectations.RuntimeExpectation.Rejected rejected) {
            checkEq("compile-reject", rejected.mode(), "the jvm mode");
            checkEq("E6006", rejected.code(), "the jvm diagnostic code");
        }
        if (js instanceof SidecarExpectations.RuntimeExpectation.Rejected rejected) {
            checkEq("compile-reject", rejected.mode(), "the js mode");
            checkEq("E6006", rejected.code(), "the js diagnostic code");
        }

        // The production-side schema validator accepts the divergent form
        // (the C6 trigger rides the declaration module's @extern-c).
        String sidecarJson = Files.readString(CONFORMANCE_ROOT.resolve(SIDECAR_PATH),
            StandardCharsets.UTF_8);
        String declarationRaw = Files.readString(CONFORMANCE_ROOT.resolve(FFI_DIR)
            .resolve(CorpusFfi.wiringFor(CONFORMANCE_ROOT, NATIVE)
                .declarationCorpusPath()), StandardCharsets.UTF_8);
        SidecarSchemaValidator.ValidationContext context =
            new SidecarSchemaValidator.ValidationContext(FIXTURE_PATH,
                expectedTagOf(source),
                List.of(new SidecarSchemaValidator.CompilationModule(
                        FIXTURE_PATH, source),
                    new SidecarSchemaValidator.CompilationModule(
                        FFI_DIR + "/support/native.d.deal", declarationRaw)),
                Set.of());
        Optional<SidecarSchemaValidator.ClassificationFailure> failure =
            SidecarSchemaValidator.validate(context, sidecarJson);
        check(failure.isEmpty(),
            "the 051 sidecar validates clean in the sanctioned divergent form: "
                + failure.map(SidecarSchemaValidator.ClassificationFailure::message)
                    .orElse(""));
    }

    // =========================================================================
    // 2. The production-artifact drive
    // =========================================================================

    private static void testProductionArtifactDrive() throws Exception {
        System.out.println("-- the 051 fixture through the production artifact "
            + "under luajit --");
        String source = fixtureSource();
        SidecarExpectations.ErrorExpectation sidecarError =
            luajitError(sidecar());
        SidecarExpectations.RuntimeExpectation.Executed luajit =
            (SidecarExpectations.RuntimeExpectation.Executed)
                sidecar().expectationFor("luajit");
        Fixture fixture = compile(source);
        Path out = fixture.root().resolve("out-prod");
        try {
            Artifact artifact = emit(fixture, fixture.externCModules(), out);
            String text = artifact.text();
            checkEq(NAME + ".lua", artifact.name(),
                "the entry module's chunk is the one staged artifact");
            String entryText = fixture.entry().toAbsolutePath().toString();

            // T1 — the emitted FFI load at the owning MODULE_IMPORT, with
            // the import statement's span triplet.
            int importLine = lineOf(fixture.strippedSource(),
                "import * as native");
            checkEq(1, columnOf(fixture.strippedSource(), "import * as native"),
                "the native import sits at column 1 of its line");
            check(text.contains("__exportSurfaces[\"" + NATIVE_DOTTED + "\"] = "
                    + "__exportSurfaces[\"" + NATIVE_DOTTED + "\"] or "
                    + "__rt.load_ffi(\"" + NATIVE_MODULE_KEY + "\", "),
                "the artifact emits the load_ffi prelude at the import");
            check(text.contains("\"" + entryText + "\", " + importLine + ", 1)"),
                "the load carries the import statement's span triplet: "
                    + entryText + ", " + importLine + ", 1");
            check(!text.contains("require(\"" + NATIVE_DOTTED + "\")")
                    && !text.contains("ffi.cdef") && !text.contains("ffi.C["),
                "the artifact emits no dotted provider require and no "
                    + "compile-time cdef/C access");

            // T2 — the string parameter's DEAL_TO_HOST + HOST_PARAMETER
            // cell, the post-cell projection, the loaded wrapper's .f
            // invocation with the literal span triplet, and the single
            // HOST_TO_DEAL + HOST_SYNC_RETURN cell at the call origin.
            int callLine = lineOf(fixture.strippedSource(), "native.ffi_echo");
            int callColumn = columnOf(fixture.strippedSource(), "native.ffi_echo");
            int parameterCell = text.indexOf(
                "pcall(__hostParamCell, \"string\", 1, S.v");
            int projection = text.indexOf(
                "__hbT[1] = __hostProjectArg(\"string\", nil, __chkB)");
            int invocation = text.indexOf(
                "__exportSurfaces[\"" + NATIVE_DOTTED + "\"][\"ffi_echo\"].f, "
                    + "__hbT[1], \"" + entryText + "\", " + callLine + ", "
                    + callColumn + ")");
            int returnCell = text.indexOf(
                "pcall(__hostReturnCell, \"string\", __resT, \"" + entryText + ":"
                    + callLine + ":" + callColumn + "\", false)");
            check(parameterCell >= 0,
                "the string parameter runs the DEAL_TO_HOST + HOST_PARAMETER "
                    + "cell");
            check(projection > parameterCell,
                "the post-cell parameter projection runs after the cell");
            check(invocation > projection,
                "the loaded wrapper is invoked through .f with the span triplet "
                    + "after the cell");
            check(returnCell > invocation,
                "the HOST_TO_DEAL + HOST_SYNC_RETURN cell runs at the call origin");
            check(!text.contains("ffi.cast") && !text.contains("ffi.new")
                    && !text.contains("ffi.copy"),
                "the artifact carries no ABI conversion text (the conversions "
                    + "stay owned by deal/runtime.lua)");

            // The artifact's own production terminal publishes the
            // DEAL_ERROR_CODE line.
            ProcessOutcome terminal = runProcess(
                List.of("luajit", artifact.name()), out, Map.of());
            checkEq(1, terminal.exitCode(),
                "the fixture exits 1 (the sidecar's exit code)");
            checkEq("", terminal.stderr(), "the fixture writes no stderr");
            checkEq(ErrorSnapshot.CODE_LINE_PREFIX + "FFI_INVALID_STRING\n",
                terminal.stdout(),
                "the production terminal publishes the DEAL_ERROR_CODE line");

            // The deferred-main probe captures the error fields; each one
            // compares with the sidecar under the corpus lane's
            // normalization (the mirror-relative file, the header-rebased
            // line).
            Files.writeString(out.resolve("probe.lua"),
                failureProbe(artifact.name()), StandardCharsets.UTF_8);
            ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"),
                out, Map.of("DEAL_DEFER_MAIN", "1"));
            checkEq(0, probe.exitCode(), "the failure probe runs: "
                + escaped(probe.stderr()));
            String[] parts = probe.stdout().trim().split("\\|", -1);
            if (parts.length != 6) {
                fail("the failure probe projected " + parts.length
                    + " fields: " + escaped(probe.stdout()));
                return;
            }
            checkEq("ERR", parts[0], "the fixture raises a DEAL error");
            checkEq(sidecarError.code(), parts[1], "code matches the sidecar");
            checkEq(sidecarError.message(), parts[2], "message matches the sidecar");
            String normalizedFile = corpusSourceFile(fixture, parts[3]);
            checkEq(sidecarError.sourceFile(), normalizedFile,
                "sourceFile matches the sidecar (corpus-relative)");
            int rawLine = Integer.parseInt(parts[4]) + fixture.strippedHeaderLines();
            checkEq(sidecarError.line(), rawLine,
                "line matches the sidecar (rebased onto raw fixture coordinates)");
            checkEq(sidecarError.column(), Integer.valueOf(parts[5]),
                "column matches the sidecar");

            // The captured fields reproduce the sidecar's G4.6 transcript
            // byte-for-byte (the DEAL_ERROR_CODE line plus the canonical
            // snapshot).
            SidecarExpectations.ErrorExpectation captured =
                new SidecarExpectations.ErrorExpectation(parts[1], parts[2],
                    normalizedFile, rawLine, Integer.parseInt(parts[5]),
                    Optional.empty(), Optional.empty(), Optional.empty(),
                    Optional.empty());
            String framing = ErrorSnapshot.CODE_LINE_PREFIX + captured.code()
                + "\n" + ErrorSnapshot.SNAPSHOT_LINE_PREFIX
                + ErrorSnapshot.canonicalJson(captured) + "\n";
            checkEq(new String(luajit.stdout(), StandardCharsets.UTF_8), framing,
                "the captured fields frame the sidecar's transcript");
            check(terminal.stdout().startsWith(ErrorSnapshot.CODE_LINE_PREFIX
                    + captured.code() + "\n"),
                "the terminal's line carries the sidecar's code");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The scenario's dependency on the T1 load and the T2 crossing
    // =========================================================================

    private static void testLoadDependency() throws Exception {
        System.out.println("-- the scenario fails if the T1 load is broken --");
        Fixture fixture = compile(fixtureSource());
        try {
            Path out = fixture.root().resolve("out-broken-load");
            Map<ModuleId, FfiGeneratedModule> broken =
                new LinkedHashMap<>(fixture.externCModules());
            broken.put(new ModuleId(NATIVE_DOTTED), withMissingLibrary(
                fixture.externCModules().get(new ModuleId(NATIVE_DOTTED)),
                fixture.root().resolve("libcandidate_missing.so")));
            Artifact artifact = emit(fixture, broken, out);
            check(artifact.text().contains("__rt.load_ffi(\"" + NATIVE_MODULE_KEY
                    + "\", "),
                "the broken-library variant still emits the load prelude");
            Files.writeString(out.resolve("probe.lua"),
                failureProbe(artifact.name()), StandardCharsets.UTF_8);
            ProcessOutcome probe = runProcess(List.of("luajit", "probe.lua"),
                out, Map.of("DEAL_DEFER_MAIN", "1"));
            checkEq(0, probe.exitCode(), "the broken-load probe runs: "
                + escaped(probe.stderr()));
            String[] parts = probe.stdout().trim().split("\\|", -1);
            check(parts.length == 6 && "FFI_LIBRARY_LOAD".equals(parts[1]),
                "with the library missing the run fails on the FFI load before "
                    + "the string crossing, never FFI_INVALID_STRING: "
                    + escaped(probe.stdout()));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testStringCrossingDependency() throws Exception {
        System.out.println("-- the scenario executes the T2 string crossing "
            + "with a NUL-free payload --");
        String clean = fixtureSource()
            .replace("\\\\u0000", "\\\\u0041")
            .replace("  return null;", "  if (echoed !== \"A\") {\n"
                + "    throw { code: \"TEST_FAIL\", message: \"the echoed "
                + "string\" };\n  }\n  return null;");
        check(!clean.contains("\\\\u0000") && clean.contains("\\\\u0041"),
            "the clean variant carries the NUL-free payload: " + clean);
        Fixture fixture = compile(clean);
        Path out = fixture.root().resolve("out-clean");
        try {
            Artifact artifact = emit(fixture, fixture.externCModules(), out);
            check(artifact.text().contains(
                    "__exportSurfaces[\"" + NATIVE_DOTTED + "\"][\"ffi_echo\"].f, "),
                "the clean variant still crosses through the loaded wrapper");
            ProcessOutcome run = runProcess(List.of("luajit", artifact.name()),
                out, Map.of());
            check(run.exitCode() == 0 && run.stdout().isEmpty()
                    && run.stderr().isEmpty(),
                "the NUL-free payload executes the native echo clean: exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The six-code completion over the corpus sidecars
    // =========================================================================

    private static void testSixCodeCoverage() throws Exception {
        System.out.println("-- the corpus's FFI sidecars cover exactly the "
            + "six FFI_* codes with their pinned origins --");
        Path dir = CONFORMANCE_ROOT.resolve(FFI_DIR);
        Set<String> codes = new TreeSet<>();
        Map<String, String> providers = new LinkedHashMap<>();
        List<Path> sidecars;
        try (Stream<Path> entries = Files.list(dir)) {
            sidecars = entries
                .filter(path -> path.getFileName().toString().endsWith(".expect.json"))
                .sorted()
                .toList();
        }
        for (Path sidecarPath : sidecars) {
            SidecarExpectations.StructuredExpectationSidecar sidecar =
                SidecarExpectations.StructuredExpectationSidecar.parse(
                    Files.readString(sidecarPath, StandardCharsets.UTF_8));
            SidecarExpectations.RuntimeExpectation expectation =
                sidecar.expectationFor("luajit");
            if (!(expectation
                    instanceof SidecarExpectations.RuntimeExpectation.Executed executed)
                    || !executed.isRuntimeError() || executed.error() == null) {
                continue;
            }
            SidecarExpectations.ErrorExpectation error = executed.error();
            codes.add(error.code());
            String sidecarName = sidecarPath.getFileName().toString();
            providers.put(error.code(), sidecarName);
            // The pinned origin: the import statement for the two load
            // codes, the call expression for the four call codes.
            String fixturePath = FFI_DIR + "/" + sidecarName.replace(
                ".expect.json", ".deal");
            String fixture = Files.readString(CONFORMANCE_ROOT.resolve(fixturePath),
                StandardCharsets.UTF_8);
            String callee = error.code().equals("FFI_SYMBOL_MISSING")
                    || error.code().equals("FFI_LIBRARY_LOAD")
                ? "import * as" : "native.ffi_";
            checkEq(lineOf(fixture, callee), error.line(), error.code()
                + " pins the origin line of its "
                + (callee.equals("import * as") ? "import statement"
                    : "call expression"));
            checkEq(columnOf(fixture, callee), error.column(), error.code()
                + " pins the origin column of its "
                + (callee.equals("import * as") ? "import statement"
                    : "call expression"));
        }
        checkEq(SIX_CODES, codes,
            "the LuaJIT legs of the FFI corpus sidecars pin exactly the closed "
                + "six FFI_* codes");
        checkEq(NAME + ".expect.json", providers.get("FFI_INVALID_STRING"),
            "the 051 sidecar is the FFI_INVALID_STRING production-artifact "
                + "method");
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /**
     * Normalizes one captured origin file into the corpus-relative form:
     * the mirror-relative path (the corpus lane's deployment-map
     * normalization).
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
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI 051 Invalid String / Six-Code Completion "
            + "Tests (ISSUE-0664) ===");
        testFixtureAndSidecar();
        testProductionArtifactDrive();
        testLoadDependency();
        testStringCrossingDependency();
        testSixCodeCoverage();
        System.out.println();
        System.out.println("passed: " + passed + ", failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
