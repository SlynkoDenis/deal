package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SemanticTraceProtocol;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0651: the sync host call arms and the host-boundary crossings
 * (design source {@code host-module-load-and-host-call-realization} H3,
 * H7, the sync host call contract, and the host-boundary carrier
 * projection contract; {@code semantic-ir-construct-coverage-cutover} K4;
 * {@code luijit-jvm-single-lowering-production-cutover} C2).
 *
 * <ol>
 *   <li><b>LuaJIT arms.</b> {@code CALL(HOST)}, the {@code HostFunction}
 *       {@code CALL(INDIRECT)}, and a host {@code CALLBACK_INVOKE} invoke
 *       the loaded surface entry through the landed wrapper's {@code .f}
 *       calling convention with the trailing span triplet; the declared
 *       parameter cells run in one-based order at the call origin and the
 *       pinned E8010 texts surface; function-typed arguments are projected
 *       into host-facing wrappers whose bridge runs the DEAL carrier.</li>
 *   <li><b>JVM arms.</b> The same calls invoke the emitted per-export
 *       wrapper with the import's origin triple and the declared parameter
 *       classes, and every crossed value is projected between the
 *       production value carriers and the {@code $DealRt} carrier set
 *       (the {@code FnValue} bridges, the declared element-shape array
 *       carriers with the normal-return copy-back, the declared return
 *       projection); the declared array positions include the nullable
 *       {@code ?[T]} form.</li>
 *   <li><b>Pinned corpus outcomes.</b> The admitted sync host fixture set
 *       compiles through the production emission and executes under
 *       {@code luajit} and {@code java} with the sidecar-pinned outcome
 *       and origin.</li>
 *   <li><b>Fail-closed seeds.</b> A call of an unloaded surface, a
 *       declared position crossed by a value carrying no matching shape,
 *       a raw host-returned function value, and a bytes position crossed
 *       by a non-bytes value each fail with the pinned projection.</li>
 *   <li><b>The hand-built {@code HostFunctionValue} arm.</b> No DEAL source
 *       registers a {@code HostFunctionValue} binding today, so the closed
 *       IR of the host-materialized crossing (the declared host call with
 *       its {@code HOST_TO_DEAL} return crossing, the exactly-one
 *       registration, the {@code CALL(INDIRECT)} on the value, and the
 *       declared null-return callback record) is hand-built, validated,
 *       and emitted: the LuaJIT chunk runs the materialized value's
 *       declared cells under {@code luajit}, and the JVM artifact is
 *       compiled by {@code javac} and executed under {@code java}, where
 *       the scalar declared return is reconciled with the production
 *       carrier, the host-returned array crosses back into the production
 *       array, and the void callback wrapper is never assigned.</li>
 *   <li><b>The bridge's carrier resolution.</b> A declared function-typed
 *       host position is crossed by a production
 *       {@code JvmRuntime.AdapterValue} (a checker-valid arity extension
 *       over a DEAL body), whose host-invoked bridge must run the D15
 *       protocol instead of the adapter's throwing stub, and by a plain
 *       DEAL-body carrier whose host-invoked error snapshot must carry the
 *       closure's own frame; the same fixture drives both targets.</li>
 *   <li><b>The trace-mode oracle agreement.</b> The trace-mode project
 *       sessions of both targets carry the compile's host declaration
 *       surface (the {@code MODULE_IMPORT(HOST)} load and the host arms),
 *       and the oracle resolves the loaded surface entry through the
 *       host seam ({@code HostResponder.loadedExport}); the fixtures whose
 *       three consumers agree are driven event-for-event (the trace events
 *       and the pinned terminal snapshot fields), and the oracle's side of
 *       the composite contextual read's deferral is asserted directly.</li>
 * </ol>
 */
public class HostCallRealizationTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Fixtures: the corpus sync host set
    // =========================================================================

    /** One admitted sync host fixture: the corpus path, the host stem, the pins. */
    private record SyncFixture(String name, String hostStem, String hostSpecifier) {

        String corpusFixture() {
            return "test/conformance/backend-runtime/host-abi/" + name + ".deal";
        }

        String corpusHost() {
            return "test/conformance/host-fixtures/" + hostStem;
        }

        String corpusSidecar() {
            return "test/conformance/backend-runtime/host-abi/" + name + ".expect.json";
        }
    }

    /**
     * The admitted sync host fixture set of this slice: the fixtures whose
     * declarations, calls, and boundary cells the sync arms realize. The
     * three byte-value fixtures and the declaration-owned construction
     * fixtures are sibling children's and are not claimed here.
     */
    private static final List<String> SYNC_FIXTURES = List.of(
        "host-bad-return",
        "host-prewrapped-bad",
        "host-prewrapped-ok",
        "host-extra-export-ignored",
        "host-boundary-boolean-roundtrip",
        "host-boundary-int-minimum-param",
        "host-boundary-null-narrowing",
        "host-boundary-nullable-int-null-roundtrip",
        "host-boundary-nullable-int-value-roundtrip",
        "host-boundary-number-roundtrip",
        "host-boundary-repeat-call",
        "host-boundary-unicode-string-roundtrip",
        "host-null-return-bad",
        "host-null-return-ok",
        "host-nullable-function-param",
        "host-nullable-function-param-bad",
        "host-nullable-function-return-bad",
        "host-nullable-function-return-ok",
        "host-nullable-return-bad",
        "host-nullable-return-ok",
        "host-rest-bad",
        "host-rest-ok",
        "host-array-return-ok",
        "host-empty-return-bad",
        "host-surrogate-utf8-e8010",
        "host-invalid-utf8-e8010",
        "host-bytes-param-mismatch-e8010",
        "host-bytes-return-mismatch-e8010",
        "host-boundary-apply-function");

    /** The host stems of the boundary claims sharing one declaration (the audit). */
    private static final Map<String, String> BOUNDARY_HOSTS = Map.of(
        "host-boundary-boolean-roundtrip", "boundary",
        "host-boundary-int-minimum-param", "boundary",
        "host-boundary-null-narrowing", "boundary",
        "host-boundary-nullable-int-null-roundtrip", "boundary",
        "host-boundary-nullable-int-value-roundtrip", "boundary",
        "host-boundary-number-roundtrip", "boundary",
        "host-boundary-repeat-call", "boundary",
        "host-boundary-unicode-string-roundtrip", "boundary",
        "host-boundary-apply-function", "boundary_apply");

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
        Path root,
        String entryPath,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        Map<String, String> externals,
        int headerLinesStripped) {
    }

    private record Outcome(int exitCode, String stdout, String stderr, String value) {
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32,
            deal.semantic.ir.ReleaseState.V1_2_ACTIVE,
            deal.semantic.CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            deal.semantic.ReleaseConfiguration.CURRENT_RELEASE_STATE,
            deal.semantic.ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compile(SyncFixture fixture) throws Exception {
        return compileWith(fixture.name(), fixture.hostStem(),
            ConformanceHarnessMetadata.stripClassificationHeaders(Files.readString(
                Path.of(fixture.corpusHost() + ".d.deal"), StandardCharsets.UTF_8)),
            Files.readString(Path.of(fixture.corpusFixture()), StandardCharsets.UTF_8));
    }

    /** One synthetic fixture: a host stem, the declaration text, and the app source. */
    private static Fixture compileSource(String name, String hostStem,
            String declarationSource, String appSource) throws Exception {
        return compileWith(name, hostStem, declarationSource, appSource);
    }

    private static Fixture compileWith(String name, String hostStem,
            String declarationSource, String rawApp) throws Exception {
        String hostSpecifier = "host/" + hostStem;
        String appSource = ConformanceHarnessMetadata.stripClassificationHeaders(rawApp);
        int headerLinesStripped = rawApp.split("\n", -1).length
            - appSource.split("\n", -1).length;
        Path root = Files.createTempDirectory("host-call-fixture");
        Path src = root.resolve("src");
        writeFileIn(root, "src/" + hostStem + ".d.deal",
            ConformanceHarnessMetadata.stripClassificationHeaders(declarationSource));
        writeFileIn(root, "src/" + name + ".deal", appSource);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(hostSpecifier, root.resolve("src/" + hostStem + ".d.deal")
            .toAbsolutePath().toString());
        Path entry = src.resolve(name + ".deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, externals,
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
            throw new IllegalStateException("the host fixture '" + name
                + "' did not build: " + detail + " / " + orchestrator.diagnostics());
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
            for (String key : externals.keySet()) {
                if (key.replace('/', '.').equals(declarationModule.path())
                        || key.equals(declarationModule.path())) {
                    specifier = key;
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        String entryPath = null;
        for (ModuleId module : built.input().modules().stream()
                .map(module -> module.moduleId()).toList()) {
            if (module.path().endsWith(name)) {
                entryPath = module.path();
            }
        }
        if (entryPath == null) {
            throw new IllegalStateException("the entry module path is not derived");
        }
        return new Fixture(root, entryPath, built.input(), built.index(),
            manifests.manifests(), surface, externCModules, identities, externals,
            headerLinesStripped);
    }

    /**
     * The corpus fixture source without its classification header lines
     * (every compiler-facing surface consumes header-free source; the
     * pins are authored in raw-file coordinates and rebased by the
     * stripped header-line count).
     */
    private static String stripDirectives(String source) {
        return ConformanceHarnessMetadata.stripClassificationHeaders(source);
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

    /** The single host import of the lowered project. */
    private static ModuleId hostImportModule(ExecutableLoweredProject project) {
        for (ModuleId module : project.modules().keySet()) {
            for (SemanticOp op : project.modules().get(module).ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT
                        && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                            == ModuleImportKind.HOST) {
                    return ((KindPayload.ModuleImportPayload) op.payload())
                        .resolvedModule();
                }
            }
        }
        throw new IllegalStateException("the fixture carries no host import");
    }

    // =========================================================================
    // 1. The LuaJIT artifact under real luajit
    // =========================================================================

    private static void testLuaFixtureSet() throws Exception {
        System.out.println("-- the sync host fixture set under luajit (production "
            + "emission, pinned outcomes) --");
        for (String name : SYNC_FIXTURES) {
            SyncFixture fixture = syncFixture(name);
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("host-call-lua");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + name + "' lowers: " + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                Path artifact = workspace.resolve("project.lua");
                Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                    project, result.tables(), result.registries(), compiled.surface()),
                    StandardCharsets.UTF_8);
                deployRuntime(workspace);
                deployHostLua(workspace, fixture);
                Path probe = workspace.resolve("probe.lua");
                Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                    StandardCharsets.UTF_8);
                Outcome outcome = runLua(probe, workspace);
                checkFixtureOutcome(name, outcome, "luajit",
                    compiled.headerLinesStripped());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
    }

    private static void testJvmFixtureSet() throws Exception {
        System.out.println("-- the sync host fixture set under javac + java (production "
            + "emission, pinned outcomes) --");
        for (String name : SYNC_FIXTURES) {
            SyncFixture fixture = syncFixture(name);
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("host-call-jvm");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + name + "' lowers: " + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                String className = JvmBackend.classNameFor(project.entryModule().path());
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                        result.registries(), className, compiled.surface());
                Files.writeString(workspace.resolve(className + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("HostCallProbe.java"),
                    jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
                String hostSource = Files.readString(
                    Path.of(fixture.corpusHost() + ".java"), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve(
                    JvmBackend.classNameFor(fixture.hostSpecifier()) + ".java"),
                    hostSource, StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java",
                    JvmBackend.classNameFor(fixture.hostSpecifier()) + ".java",
                    "HostCallProbe.java"), workspace);
                check(javacRun.exitCode() == 0,
                    "the fixture '" + name + "' compiles under javac: "
                        + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() != 0) {
                    continue;
                }
                Outcome outcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, "HostCallProbe"),
                    workspace);
                checkFixtureOutcome(name, outcome, "java",
                    compiled.headerLinesStripped());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
    }

    /**
     * The host declaration of one admitted fixture: the stem comes from
     * the fixture's own raw import specifier (the corpus's single
     * fixture-to-declaration join), never a name derivation.
     */
    private static SyncFixture syncFixture(String name) throws Exception {
        String source = Files.readString(
            Path.of("test/conformance/backend-runtime/host-abi/" + name + ".deal"),
            StandardCharsets.UTF_8);
        int at = source.indexOf("from \"host/");
        if (at < 0) {
            throw new IllegalStateException("the fixture '" + name
                + "' carries no host import");
        }
        int start = at + "from \"".length();
        int end = source.indexOf('"', start);
        String specifier = source.substring(start, end);
        String stem = specifier.substring("host/".length());
        return new SyncFixture(name, stem, specifier);
    }

    // =========================================================================
    // The sidecar pins
    // =========================================================================

    private record Expectation(String mode, String code, String message, int line,
                               int column, String expected, String actual) {
    }

    /** The pinned expectation of one corpus sidecar (the authoritative record). */
    private static Expectation expectationOf(String name) throws Exception {
        String json = Files.readString(
            Path.of("test/conformance/backend-runtime/host-abi/" + name + ".expect.json"),
            StandardCharsets.UTF_8);
        String mode = field(json, "\"mode\"");
        String code = field(json, "\"code\"");
        String message = field(json, "\"message\"");
        // The attained expected/actual pair lives in the sidecar's error
        // object (a runtime-ok sidecar has none); the transcript's escaped
        // copy of the same names must not be matched, so the search starts
        // at the error key.
        int errorAt = json.indexOf("\"error\"");
        String errorBlock = errorAt < 0 ? "" : json.substring(errorAt);
        String expected = field(errorBlock, "\"expected\"");
        String actual = field(errorBlock, "\"actual\"");
        Integer line = number(json, "\"line\"");
        Integer column = number(json, "\"column\"");
        return new Expectation(mode, code, message,
            line == null ? -1 : line, column == null ? -1 : column, expected, actual);
    }

    private static String field(String json, String key) {
        int at = json.indexOf(key);
        if (at < 0) {
            return null;
        }
        int start = json.indexOf('"', json.indexOf(':', at) + 1);
        StringBuilder text = new StringBuilder();
        for (int i = start + 1; i < json.length(); i++) {
            char c = json.charAt(i);
            if (c == '\\' && i + 1 < json.length()) {
                char next = json.charAt(++i);
                switch (next) {
                    case 'n' -> text.append('\n');
                    case '"' -> text.append('"');
                    case '\\' -> text.append('\\');
                    default -> text.append(next);
                }
                continue;
            }
            if (c == '"') {
                break;
            }
            text.append(c);
        }
        return text.toString();
    }

    private static Integer number(String json, String key) {
        int at = json.indexOf(key);
        if (at < 0) {
            return null;
        }
        int start = json.indexOf(':', at) + 1;
        StringBuilder digits = new StringBuilder();
        for (int i = start; i < json.length(); i++) {
            char c = json.charAt(i);
            if (Character.isDigit(c) || (c == '-' && digits.length() == 0)) {
                digits.append(c);
            } else if (digits.length() > 0) {
                break;
            }
        }
        return digits.length() == 0 ? null : Integer.valueOf(digits.toString());
    }

    /**
     * Asserts one fixture run against its sidecar pin: a runtime-ok fixture
     * exits OK with no error line; a runtime-error fixture reports the
     * pinned code, message, and origin line/column.
     */
    private static void checkFixtureOutcome(String name, Outcome outcome,
            String target, int headerLinesStripped) throws Exception {
        Expectation expectation = expectationOf(name);
        if ("runtime-ok".equals(expectation.mode())) {
            check(outcome.exitCode() == 0 && outcome.value().startsWith("OK"),
                "the " + target + " fixture '" + name + "' is runtime-ok: exit="
                    + outcome.exitCode() + " value=" + escaped(outcome.value())
                    + " stderr=" + escaped(outcome.stderr()));
            return;
        }
        check(outcome.value().startsWith("ERR:"),
            "the " + target + " fixture '" + name + "' raises the pinned error: value="
                + escaped(outcome.value()) + " stderr=" + escaped(outcome.stderr()));
        if (!outcome.value().startsWith("ERR:")) {
            return;
        }
        String[] parts = outcome.value().substring(4).split("\\|", -1);
        checkEq(expectation.code(), parts[0],
            name + " (" + target + ") pinned code");
        checkEq(expectation.message(), parts[1],
            name + " (" + target + ") pinned message");
        String origin = parts[2];
        int lastColon = origin.lastIndexOf(':');
        int prevColon = origin.lastIndexOf(':', lastColon - 1);
        checkEq(expectation.line(),
            Integer.valueOf(origin.substring(prevColon + 1, lastColon))
                + headerLinesStripped,
            name + " (" + target + ") pinned origin line");
        checkEq(expectation.column(), Integer.valueOf(origin.substring(lastColon + 1)),
            name + " (" + target + ") pinned origin column");
        check(origin.substring(0, prevColon).endsWith(name + ".deal"),
            name + " (" + target + ") pinned origin file: " + origin);
        // The sidecar's attained expected/actual pair (the pinned
        // snapshot fields): the probe prints the raised error's own pair
        // and the assertion is null-aware (a row without an attained pair
        // prints the "-" placeholder).
        checkEq(expectation.expected(), "-".equals(parts[3]) ? null : parts[3],
            name + " (" + target + ") pinned expected");
        checkEq(expectation.actual(), "-".equals(parts[4]) ? null : parts[4],
            name + " (" + target + ") pinned actual");
    }

    // =========================================================================
    // 3. Combined behavior: the load in the same run, two aliases, one entry
    // =========================================================================

    /**
     * A two-alias project whose two aliases both call the one loaded
     * surface: the drive asserts exactly one load per module, one shared
     * entry for both aliases, and the calls' pinned results in the same run
     * that executes the load.
     */
    private static final String TWO_ALIAS_SOURCE = """
        import * as first from "host/extra_export"
        import * as second from "host/extra_export"

        export function test_two_aliases(): string {
          let a: string = first.ping();
          let b: string = second.ping();
          if (a !== "pong" || b !== "pong") {
            throw { code: "TEST_FAIL", message: "two-alias call mismatch" };
          }
          return a;
        }

        export function main(): null {
          return null;
        }
        """;

    private static void testTwoAliasCall() throws Exception {
        System.out.println("-- the two-alias call drive: one load, one shared entry, "
            + "both aliases' calls in the same run --");
        Fixture compiled = compileSource("host-extra-export-ignored", "extra_export",
            Files.readString(Path.of("test/conformance/host-fixtures/extra_export.d.deal"),
                StandardCharsets.UTF_8),
            TWO_ALIAS_SOURCE);
        Path workspace = Files.createTempDirectory("host-call-alias");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the two-alias fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Files.createDirectories(workspace.resolve("host"));
            Files.writeString(workspace.resolve("host/extra_export.lua"),
                HOST_EXTRA_EXPORT_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaLoadCountDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome outcome = runLua(probe, workspace);
            check(outcome.exitCode() == 0 && outcome.value().contains("OK"),
                "the two-alias drive executes the calls through the one loaded entry: "
                    + escaped(outcome.value()) + " stderr=" + escaped(outcome.stderr()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** The deployed Lua host of the two-alias drive: it counts its own loads. */
    private static final String HOST_EXTRA_EXPORT_LUA = """
        _HOST_EXTRA_LOADS = (_HOST_EXTRA_LOADS or 0) + 1
        return {
          ping = function() return "pong" end,
          extra = 42,
        }
        """;

    /** The LuaJIT two-alias probe: one load, one entry, both calls. */
    private static String luaLoadCountDriver(Path artifact, String entryPath) {
        return """
            local chunk = dofile("%s")
            local rt = require("deal.runtime")
            local loads = 0
            local realLoad = rt.load_host
            rt.load_host = function(...)
              loads = loads + 1
              return realLoad(...)
            end
            local ok, err = __dealMain()
            if not ok then print("ERR:INIT|-") os.exit(0) end
            local surface = __exportSurfaces["%s"]
            local host = __exportSurfaces["host.extra_export"]
            if host == nil or host["ping"] == nil then
              print("ERR:NO_ENTRY|-") os.exit(0)
            end
            local ok2, err2 = pcall(surface["test_two_aliases"].f)
            if not ok2 then print("ERR:TEST|-") os.exit(0) end
            local ok2, err2 = pcall(surface["test_two_aliases"].f)
            if loads ~= 1 then print("ERR:LOADS|" .. loads) os.exit(0) end
            if (_HOST_EXTRA_LOADS or 0) ~= 1 then
              print("ERR:HOST_LOADS|" .. tostring(_HOST_EXTRA_LOADS)) os.exit(0)
            end
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    // =========================================================================
    // 4. The JVM crossing projection: the bridge and the array copy-back
    // =========================================================================

    /**
     * One JVM crossing drive: a deployed host that echoes the bridge
     * carrier's observed class and mutates a declared array parameter, so
     * the probe can assert the production carrier reached the host method
     * and the host's element writes were copied back into the production
     * array after the normal return. The declared positions include a
     * nullable-array parameter and return ({@code int[] | null}), whose
     * declared descriptor text carries the {@code ?} prefix, so the
     * crossing is exercised over that form too.
     */
    private static final String CROSSING_DECLARATION = """
        export function apply(f: (x: int) => int, v: int): int;
        export function bump(parts: int[]): int;
        export function bumpMaybe(parts: int[] | null): int[] | null;
        export function sumMaybe(parts: int[] | null): int;
        """;

    private static final String CROSSING_SOURCE = """
        import * as host from "host/crossing_probe"

        function plusOne(x: int): int {
          return x + 1;
        }

        export function test_crossing(): int {
          let applied: int = host.apply(plusOne, 41);
          if (applied !== 42) {
            throw { code: "TEST_FAIL", message: "bridge result" };
          }
          let parts: int[] = [1, 2, 3];
          let total: int = host.bump(parts);
          if (total !== 9) {
            throw { code: "TEST_FAIL", message: "copy-back result" };
          }
          if (parts[0] !== 1 || parts[1] !== 3 || parts[2] !== 5) {
            throw { code: "TEST_FAIL", message: "copy-back observability" };
          }
          return applied;
        }

        export function test_nullable_array_crossing(): int {
          let parts: int[] = [4, 5];
          let returned: int[] | null = host.bumpMaybe(parts);
          if (returned === null) {
            throw { code: "TEST_FAIL", message: "nullable array return" };
          }
          let total: int = host.sumMaybe(returned);
          if (total !== 15) {
            throw { code: "TEST_FAIL", message: "nullable array return values" };
          }
          if (parts[0] !== 14 || parts[1] !== 15) {
            throw { code: "TEST_FAIL", message: "nullable array copy-back" };
          }
          let nothing: int[] | null = host.bumpMaybe(null);
          if (nothing !== null) {
            throw { code: "TEST_FAIL", message: "nullable array null roundtrip" };
          }
          return total;
        }

        export function main(): null {
          return null;
        }
        """;

    private static final String CROSSING_HOST_JAVA = """
        final class HostCrossing_probe {
          static final java.util.List<java.lang.String> OBSERVED =
              new java.util.ArrayList<>();

          public static Object apply($DealRt.Fn1_I_R_I f, int v) {
            OBSERVED.add(f.getClass().getName());
            return Integer.valueOf(f.invoke(v));
          }

          public static Object bump($DealRt.__IntArray parts) {
            OBSERVED.add("array:" + parts.getClass().getName());
            int total = 0;
            for (int i = 0; i < parts.data.length; i++) {
              total += parts.data[i];
              parts.data[i] = parts.data[i] + i;
            }
            return Integer.valueOf(total + 3);
          }

          public static Object bumpMaybe($DealRt.__IntArray parts) {
            if (parts == null) {
              OBSERVED.add("maybearray:null");
              return null;
            }
            OBSERVED.add("maybearray:" + parts.getClass().getName());
            for (int i = 0; i < parts.data.length; i++) {
              parts.data[i] = parts.data[i] + 10;
            }
            return new $DealRt.__IntArray(new int[] { 7, 8 });
          }

          public static Object sumMaybe($DealRt.__IntArray parts) {
            if (parts == null) {
              OBSERVED.add("maybearray:sum:null");
              return Integer.valueOf(-1);
            }
            OBSERVED.add("maybearray:sum:" + parts.data.length + ":"
                + parts.data[0] + "," + parts.data[1]);
            return Integer.valueOf(parts.data[0] + parts.data[1]);
          }
        }
        """;

    private static void testJvmCrossingProjection() throws Exception {
        System.out.println("-- the JVM crossing projection: the bridge runs the "
            + "production carrier and the array carrier is materialized and "
            + "copied back --");
        Fixture compiled = compileSource("host-crossing", "crossing_probe",
            CROSSING_DECLARATION, CROSSING_SOURCE);
        Path workspace = Files.createTempDirectory("host-call-crossing");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the crossing fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostCrossing_probe.java"),
                CROSSING_HOST_JAVA, StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("CrossingProbe.java"),
                crossingProbe(className, compiled.entryPath()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostCrossing_probe.java", "CrossingProbe.java"),
                workspace);
            check(javacRun.exitCode() == 0,
                "the crossing artifact compiles with the deployed host: "
                    + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() != 0) {
                return;
            }
            Outcome outcome = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "CrossingProbe"),
                workspace);
            check(outcome.exitCode() == 0 && outcome.value().startsWith("OK"),
                "the crossing drive runs: " + escaped(outcome.value())
                    + " stderr=" + escaped(outcome.stderr()));
            check(outcome.value().contains("BRIDGE:$DealRt$__Bridge$Fn1_I_R_I"),
                "the production FunctionValue reached the wrapper's invoke through "
                    + "the declared bridge: " + escaped(outcome.value()));
            check(outcome.value().contains("BRIDGE:array:$DealRt$__IntArray"),
                "the declared array carrier was materialized from the production "
                    + "array: " + escaped(outcome.value()));
            check(outcome.value().contains("BRIDGE:maybearray:$DealRt$__IntArray"),
                "the declared nullable array carrier was materialized from the "
                    + "production array: " + escaped(outcome.value()));
            check(outcome.value().contains("BRIDGE:maybearray:sum:2:7,8"),
                "the nullable declared return was projected into the production "
                    + "array and re-crossed with its elements: "
                    + escaped(outcome.value()));
            check(outcome.value().contains("BRIDGE:maybearray:null"),
                "a declared null crossed into the nullable array position as Java "
                    + "null: " + escaped(outcome.value()));
            check(emission.source().contains("__hostArrayFromDeal(inner, v)")
                    && emission.source().contains("__hostArrayToDeal(inner, v)"),
                "the emitted array crossing dispatches the stripped descriptor "
                    + "(the declared ?[T] form)");
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /** The JVM crossing probe: the bridge's observed class and the copy-back. */
    private static String crossingProbe(String className, String entryPath) {
        return """
            final class CrossingProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.out.println("ERR:" + error.code + "|" + error.msg);
                  return;
                }
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.exportSurface(%s);
                for (java.lang.String name : surface.keys) {
                  if (!name.startsWith("test_")) { continue; }
                  try {
                    ((deal.codegen.jvm.JvmRuntime.FunctionValue) surface.read(
                        name)).fn.invoke(new java.lang.Object[]{ });
                  } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                    System.out.println("ERR:" + error.code + "|" + error.msg);
                    return;
                  }
                }
                System.out.println("OK");
                for (java.lang.String observed : HostCrossing_probe.OBSERVED) {
                  System.out.println("BRIDGE:" + observed);
                }
              }
            }
            """.formatted(className, className, quoted(entryPath));
    }

    // =========================================================================
    // 5. The fail-closed seeds
    // =========================================================================

    private static void testFailClosedSeeds() throws Exception {
        System.out.println("-- the fail-closed seeds: an unloaded surface is never a "
            + "silent call, and an unresolved binding stays a producer defect --");
        // Seed 1: the surface-entry load is removed from the emitted chunk, so
        // the call resolves an unloaded surface: the chunk fails, never a
        // silent call.
        SyncFixture fixture = syncFixture("host-extra-export-ignored");
        Fixture compiled = compile(fixture);
        Path workspace = Files.createTempDirectory("host-call-unloaded");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the unloaded-surface fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), compiled.surface());
            String mutated = lua.replaceAll(
                "__exportSurfaces\\[\"host\\.extra_export\"\\] = "
                    + "__exportSurfaces\\[\"host\\.extra_export\"\\] or "
                    + "__rt\\.load_host\\([^\n]*\\)\n", "");
            check(!mutated.equals(lua), "the unloaded-surface seed mutates the load");
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, mutated, StandardCharsets.UTF_8);
            deployRuntime(workspace);
            deployHostLua(workspace, fixture);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome outcome = runLua(probe, workspace);
            check(outcome.value().startsWith("ERR:"),
                "a call of an unloaded surface fails loudly, never silently: "
                    + escaped(outcome.value()) + " stderr="
                    + escaped(outcome.stderr()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 6. The hand-built HostFunctionValue sync call
    // =========================================================================

    /**
     * The hand-built {@code HostFunctionValue} sync-call drive: the exact IR
     * the host-materialized-crossing producer records for a declared
     * function-typed host return (the {@code CALL(HOST)} with its
     * {@code HOST_TO_DEAL} crossing boundary plus the exactly-one
     * {@code HostFunctionValue} registration), followed by the
     * {@code CALL(INDIRECT)} on the materialized value. No DEAL source
     * registers a {@code HostFunctionValue} binding today, so the corpus seed
     * builds the closed shape directly and the emitted arm is compiled and
     * executed by the real toolchain — the scalar return carrier and the
     * host-to-DEAL array projection both drive.
     */
    private static final ModuleId HOST_VALUE_MODULE = new ModuleId("main");
    private static final String HOST_VALUE_SOURCE_ID = "host-value-call.deal";

    private static final String HOST_VALUE_DECLARATION = """
        export function pick(): (x: int) => int;
        export function gather(): (x: int) => string[];
        export function signal(): null;
        """;

    private static final String HOST_VALUE_SOURCE = """
        import * as host from "host/pick_fn"

        export function main(): null {
          return null;
        }
        """;

    /**
     * The deployed host implementation of the drive: {@code pick} returns a
     * host function value with a scalar return, {@code gather} one with a
     * declared array return (the declared element-shape carrier the
     * host-to-DEAL projection materializes back into the production array),
     * and {@code notify} is the callback record's declared null return (the
     * emitted wrapper is void, so the callback arm must not assign it).
     */
    private static final String HOST_VALUE_HOST_JAVA = """
        final class HostPick_fn {
          public static Object pick() {
            return new $DealRt.Fn1_I_R_I() {
              @Override
              int invoke(int x) { return x + 1; }
            };
          }

          public static Object gather() {
            return new $DealRt.Fn1_I_R_$$Bstring$E() {
              @Override
              java.lang.Object invoke(int x) {
                return new $DealRt.__StringArray(
                    new java.lang.String[]{ "n" + x });
              }
            };
          }

          public static Object signal() {
            return null;
          }
        }
        """;

    /** The hand-built callback record's op id (the emitted {@code cb<id>} entry). */
    private static final long HOST_VALUE_CALLBACK_OP = 9;

    /**
     * The deployed Lua host of the hand-built drive: each export returns a
     * declared function value through the runtime's wrapper factory (the
     * declared cells then run through the materialized wrapper), and the
     * declared null return is the runtime's null sentinel.
     */
    private static final String HOST_VALUE_HOST_LUA = """
        local rt = require("deal.runtime")

        return {
          pick = function()
            return rt.function_("(int)->int", function(x) return x + 1 end)
          end,
          gather = function()
            return rt.function_("(int)->[string]", function(x) return { "n" .. x } end)
          end,
          signal = function()
            return rt.__NULL
          end,
        }
        """;

    /** The declared host module of the hand-built drive's compile. */
    private static ModuleId hostValueHostModule(Fixture compiled) {
        for (ModuleId module : compiled.surface().moduleIds()) {
            if (module.path().endsWith("pick_fn")) {
                return module;
            }
        }
        throw new IllegalStateException("the hand-built drive resolves no"
            + " declared host module (a test-producer defect)");
    }

    private static void testLuaHostFunctionValueCall() throws Exception {
        System.out.println("-- the hand-built HostFunctionValue sync call under "
            + "luajit: the materialized value runs its declared cells at the call "
            + "origin --");
        Fixture compiled = compileSource("host-value-call-lua", "pick_fn",
            HOST_VALUE_DECLARATION, HOST_VALUE_SOURCE);
        try {
            ModuleId hostModule = hostValueHostModule(compiled);
            hostValueLuaCase(compiled, hostModule, "pick",
                new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE),
                    RuntimeDescriptor.Int.INSTANCE, false),
                RuntimeDescriptor.Int.INSTANCE, "RESULT:42");
            hostValueLuaCase(compiled, hostModule, "gather",
                new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE),
                    new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE),
                    false),
                new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE),
                "RESULT:[n41]");
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    /** One hand-built unit emitted for LuaJIT and executed under real luajit. */
    private static void hostValueLuaCase(Fixture compiled, ModuleId hostModule,
            String exportName, RuntimeDescriptor.Func descriptor,
            RuntimeDescriptor resultType, String expected) throws Exception {
        LoweredModuleUnit unit = hostValueUnit(hostModule, exportName, descriptor,
            resultType, "interface", "lowering-context");
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32,
            new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(HOST_VALUE_MODULE, new ExternalModuleInterface(
                    HOST_VALUE_MODULE, ExternalModuleKind.IMPLEMENTATION, List.of(),
                    List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES))),
            Map.of(HOST_VALUE_MODULE, unit), HOST_VALUE_MODULE);
        Path workspace = Files.createTempDirectory("host-value-call-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, Map.of(HOST_VALUE_MODULE, hostValueTable(unit)),
                Map.of(HOST_VALUE_MODULE, new ClassFactoryRegistry(Map.of())),
                compiled.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve("host/pick_fn.lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, HOST_VALUE_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaHostValueDriver(artifact), StandardCharsets.UTF_8);
            Outcome outcome = runLua(probe, workspace);
            check(outcome.exitCode() == 0 && outcome.value().contains(expected),
                "the LuaJIT " + exportName + " arm runs the materialized value: "
                    + escaped(outcome.value()) + " stderr="
                    + escaped(outcome.stderr()));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The LuaJIT probe of the hand-built drive: init walk, then the published result. */
    private static String luaHostValueDriver(Path artifact) {
        return """
            local function emitError(e)
              if type(e) == "table" and (e.__d or e.code ~= nil) then
                print("ERR:" .. tostring(e.code) .. "|" .. tostring(e.m or e.message))
                return
              end
              print("ERR:E9999|" .. tostring(e))
            end
            dofile("%s")
            local ok, err = __dealMain()
            if not ok then emitError(err) os.exit(0) end
            -- The emitted export entry is the publication wrapper; its `f`
            -- is the published value itself (__unfn of a non-function value
            -- is the value).
            local value = __exportSurfaces["main"]["result"].f
            if type(value) == "table" then
              print("RESULT:[" .. tostring(value[1]) .. "]")
            else
              print("RESULT:" .. tostring(value))
            end
            """.formatted(artifact.toAbsolutePath().toString());
    }

    private static void testJvmHostFunctionValueCall() throws Exception {
        System.out.println("-- the hand-built HostFunctionValue sync call: the "
            + "declared scalar carrier and the host-to-DEAL array projection "
            + "compile and run --");
        Fixture compiled = compileSource("host-value-call", "pick_fn",
            HOST_VALUE_DECLARATION, HOST_VALUE_SOURCE);
        ModuleId hostModule = hostValueHostModule(compiled);
        RuntimeDescriptor.Func scalarDescriptor = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Int.INSTANCE,
            false);
        RuntimeDescriptor.Func arrayDescriptor = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE),
            new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE), false);
        testJvmHostFunctionValueUnit(compiled, hostModule, "pick",
            scalarDescriptor, RuntimeDescriptor.Int.INSTANCE,
            "RESULT:42|java.lang.Long",
            "the scalar declared return is reconciled with the production carrier");
        testJvmHostFunctionValueUnit(compiled, hostModule, "gather",
            arrayDescriptor,
            new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE),
            "RESULT:[n41]|deal.codegen.jvm.JvmRuntime$Array",
            "the host-returned array crosses back into the production array");
        deleteRecursively(compiled.root());
    }

    /** One hand-built {@code HostFunctionValue} unit drive under javac + java. */
    private static void testJvmHostFunctionValueUnit(Fixture compiled,
            ModuleId hostModule, String exportName, RuntimeDescriptor.Func descriptor,
            RuntimeDescriptor resultType, String expected, String what)
            throws Exception {
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(HOST_VALUE_MODULE,
                new ExternalModuleInterface(HOST_VALUE_MODULE,
                    ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
                    InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        String interfaceHash = index.interfaceIndexDigest();
        String registryHash = deal.semantic.CapabilityRegistry.releaseRegistry()
            .capabilityRegistryHash();
        LoweredModuleUnit unit = hostValueUnit(hostModule, exportName, descriptor,
            resultType, interfaceHash,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, registryHash));
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> validation =
            SemanticIrValidator.validate(unit,
                new SemanticIrValidator.ComparisonFacts(interfaceHash,
                    SemanticProfile.DEAL_V1_2_INT32, registryHash));
        check(validation.isEmpty(), "the hand-built HostFunctionValue unit of '"
            + exportName + "' passes validation: " + validation);
        if (validation.isPresent()) {
            return;
        }
        StructuredBodyTable table = hostValueTable(unit);
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, index,
            Map.of(HOST_VALUE_MODULE, unit), HOST_VALUE_MODULE);
        String className = JvmBackend.classNameFor(HOST_VALUE_MODULE.path());
        JvmSemanticEmitter.EmissionResult emission =
            JvmSemanticEmitter.emitProductionProject(project,
                Map.of(HOST_VALUE_MODULE, table),
                Map.of(HOST_VALUE_MODULE, new ClassFactoryRegistry(Map.of())),
                className, compiled.surface());
        check(emission.source().contains("(JvmRuntime.FunctionValue)"),
            "the " + exportName + " arm invokes the materialized production "
                + "function carrier");
        check(emission.source().contains("Object cb" + HOST_VALUE_CALLBACK_OP),
            "the " + exportName + " unit carries the host callback record entry");
        Path workspace = Files.createTempDirectory("host-value-call");
        try {
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostPick_fn.java"),
                HOST_VALUE_HOST_JAVA, StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostValueProbe.java"),
                hostValueProbe(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostPick_fn.java", "HostValueProbe.java"),
                workspace);
            check(javacRun.exitCode() == 0, "the hand-built " + exportName
                + " arm compiles: " + javacRun.stdout() + javacRun.stderr());
            if (javacRun.exitCode() != 0) {
                return;
            }
            Outcome outcome = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "HostValueProbe"),
                workspace);
            check(outcome.exitCode() == 0 && outcome.value().contains(expected),
                what + ": " + escaped(outcome.value()) + " stderr="
                    + escaped(outcome.stderr()));
            check(outcome.value().contains("CALLBACK:null"),
                "the declared null-return callback arm runs its void wrapper: "
                    + escaped(outcome.value()));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM probe of the hand-built drive: init walk, then the published result. */
    private static String hostValueProbe(String className) {
        return """
            final class HostValueProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                      + error.origin);
                  return;
                }
                Object value = %s.exportSurface("main").read("result");
                String text = value instanceof deal.codegen.jvm.JvmRuntime.Array array
                    ? String.valueOf(array.elements) : String.valueOf(value);
                System.out.println("RESULT:" + text + "|"
                    + (value == null ? "null" : value.getClass().getName()));
                try {
                  System.out.println("CALLBACK:" + %s.cb%s(new java.lang.Object[]{ }));
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.out.println("CALLBACK:" + error.code + "|" + error.msg);
                }
              }
            }
            """.formatted(className, className, className,
                String.valueOf(HOST_VALUE_CALLBACK_OP));
    }

    /**
     * The hand-built unit of one {@code HostFunctionValue} sync call: the
     * import load, the declared host call whose function-typed return
     * materializes the crossing, the {@code CALL(INDIRECT)} on the registered
     * value (published under {@code result}), and the unattached callback
     * record of the declared null-returning export.
     */
    private static LoweredModuleUnit hostValueUnit(ModuleId hostModule,
            String exportName, RuntimeDescriptor.Func descriptor,
            RuntimeDescriptor resultType, String interfaceHash,
            String loweringContextHash) {
        OpId importOp = new OpId(HOST_VALUE_MODULE, 1);
        OpId callHostOp = new OpId(HOST_VALUE_MODULE, 2);
        OpId crossingOp = new OpId(HOST_VALUE_MODULE, 3);
        OpId constOp = new OpId(HOST_VALUE_MODULE, 4);
        OpId callOp = new OpId(HOST_VALUE_MODULE, 5);
        OpId parameterBoundaryOp = new OpId(HOST_VALUE_MODULE, 6);
        OpId returnBoundaryOp = new OpId(HOST_VALUE_MODULE, 7);
        OpId publishOp = new OpId(HOST_VALUE_MODULE, 8);
        OpId callbackOp = new OpId(HOST_VALUE_MODULE, HOST_VALUE_CALLBACK_OP);
        OpId callbackReturnBoundaryOp = new OpId(HOST_VALUE_MODULE, 10);
        ValueId functionValue = new ValueId(1);
        ValueId argument = new ValueId(2);
        ValueId result = new ValueId(3);
        ValueId callbackValue = new ValueId(4);
        BlockId initBlock = new BlockId(1);
        FunctionExecutionBinding.HostFunctionValue registration =
            new FunctionExecutionBinding.HostFunctionValue(hostModule, crossingOp,
                descriptor);
        RuntimeDescriptor.Func hostSignature = new RuntimeDescriptor.Func(List.of(),
            descriptor, false);
        RuntimeDescriptor.Func callbackSignature = new RuntimeDescriptor.Func(List.of(),
            RuntimeDescriptor.Null.INSTANCE, false);
        FunctionExecutionBinding.HostFunction callbackRegistration =
            new FunctionExecutionBinding.HostFunction(hostModule, "signal",
                callbackSignature);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(hostValueOp(importOp, SemanticOpKind.MODULE_IMPORT,
            new KindPayload.ModuleImportPayload(hostModule.path(), hostModule,
                ModuleImportKind.HOST, List.of()),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueOp(callHostOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.HOST,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.HostFunction(hostModule, exportName,
                        hostSignature)),
                hostSignature, List.of(), crossingOp, null, null, null),
            functionValue, descriptor, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueBoundary(crossingOp, BoundaryKind.HOST_TO_DEAL, descriptor,
            functionValue, FailurePolicyId.HOST_SYNC_RETURN, callHostOp));
        ops.add(hostValueOp(constOp, SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(41)), argument,
            RuntimeDescriptor.Int.INSTANCE, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueOp(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Static(registration), descriptor,
                List.of(parameterBoundaryOp), returnBoundaryOp, null, null, null),
            result, resultType, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueBoundary(parameterBoundaryOp, BoundaryKind.DEAL_TO_HOST,
            RuntimeDescriptor.Int.INSTANCE, argument, FailurePolicyId.HOST_PARAMETER,
            callOp));
        ops.add(hostValueBoundary(returnBoundaryOp, BoundaryKind.HOST_TO_DEAL,
            resultType, result, FailurePolicyId.HOST_SYNC_RETURN, callOp));
        ops.add(hostValueOp(publishOp, SemanticOpKind.EXPORT_PUBLISH,
            new KindPayload.ExportPublishPayload(HOST_VALUE_MODULE, "result",
                resultType, result),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueOp(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
            new KindPayload.CallbackInvokePayload(callbackValue, callbackSignature,
                List.of(), callbackReturnBoundaryOp),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(hostValueBoundary(callbackReturnBoundaryOp, BoundaryKind.DEAL_TO_HOST,
            RuntimeDescriptor.Null.INSTANCE, callbackValue,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, HOST_VALUE_MODULE, interfaceHash,
            loweringContextHash, Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(hostModule), initBlock), ExportPlan.empty(),
            Map.of(new FunctionAllocationIdentity(functionValue.id()), registration,
                new FunctionAllocationIdentity(callbackValue.id()),
                callbackRegistration),
            ops);
    }

    /** The block-membership table of the hand-built unit (init block only). */
    private static StructuredBodyTable hostValueTable(LoweredModuleUnit unit) {
        List<OpId> membership = new ArrayList<>();
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    || op.kind() == SemanticOpKind.CALLBACK_INVOKE) {
                // The boundary children are payload-owned and the callback
                // record is unattached (its static entry is emitted at class
                // level, never by the module walk).
                continue;
            }
            membership.add(op.opId());
            opBlocks.put(op.opId(), unit.moduleInit().initBlock());
        }
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        blockOps.put(unit.moduleInit().initBlock(), membership);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    private static SemanticOp hostValueBoundary(OpId id, BoundaryKind kind,
            RuntimeDescriptor descriptor, ValueId input, FailurePolicyId policy,
            OpId parent) {
        return hostValueOp(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    /** One hand-built op with its canonical contract snapshot (the closed digest). */
    private static SemanticOp hostValueOp(OpId id, SemanticOpKind kind,
            KindPayload payload, SemanticValue result, OpResultType resultType,
            FailurePolicyId policy, OpId parent) {
        SourceOrigin origin = new SourceOrigin(HOST_VALUE_SOURCE_ID,
            SourceSpan.synthetic(HOST_VALUE_SOURCE_ID), SourceOriginKind.SYNTHETIC,
            new AnchorId(0), parent);
        OperationContractSnapshot contract = hostValueContract(kind, payload,
            resultType, policy, "placeholder");
        contract = hostValueContract(kind, payload, resultType, policy,
            ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(id, kind, origin, result, resultType, List.of(),
            List.of(), payload, policy, contract);
    }

    private static OperationContractSnapshot hostValueContract(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType, FailurePolicyId policy,
            String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, List.of(), selector, payload, policy, List.of(), digest);
    }

    /** The LuaJIT probe: the init walk, then the fixture's test export. */
    private static String luaDriver(Path artifact, String entryPath) {
            String luaEntry = entryPath;
        return """
            local function emitError(e)
              if type(e) == "table" and e.__d then
                print("ERR:" .. e.code .. "|" .. tostring(e.m) .. "|" .. tostring(e.o)
                  .. "|" .. tostring(e.e or "-") .. "|" .. tostring(e.a or "-"))
                return
              end
              if type(e) == "table" and e.code ~= nil then
                print("ERR:" .. e.code .. "|" .. tostring(e.message) .. "|"
                  .. tostring(e.file) .. ":" .. tostring(e.line) .. ":"
                  .. tostring(e.column) .. "|" .. tostring(e.expected or "-") .. "|"
                  .. tostring(e.actual or "-"))
                return
              end
              print("ERR:E9999|" .. tostring(e) .. "|-|-|-")
            end
            local chunk = dofile("%s")
            local ok, err = __dealMain()
            if not ok then emitError(err) os.exit(0) end
            local surface = nil
            if type(chunk) == "table" then surface = chunk end
            if surface == nil then surface = __exportSurfaces["%s"] end
            if surface ~= nil then
              local ordered = {}
              for name, candidate in pairs(surface) do ordered[#ordered + 1] = name end
              table.sort(ordered)
              for _, name in ipairs(ordered) do
                if string.sub(name, 1, 5) == "test_" then
                  local ok2, err2 = pcall(surface[name].f)
                  if not ok2 then emitError(err2) os.exit(0) end
                end
              end
            end
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    /** The JVM probe: the init walk, then the fixture's test export. */
    private static String jvmDriver(String className, String entryPath) {
        return """
            final class HostCallProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  report(error);
                  return;
                }
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.exportSurface(%s);
                boolean invoked = false;
                for (java.lang.String name : surface.keys) {
                  if (!name.startsWith("test_")) { continue; }
                  invoked = true;
                  try {
                    ((deal.codegen.jvm.JvmRuntime.FunctionValue) surface.read(
                        name)).fn.invoke(new java.lang.Object[]{ });
                  } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                    report(error);
                    return;
                  }
                }
                if (!invoked) { System.out.println("OK"); return; }
                System.out.println("OK");
              }

              private static void report(deal.codegen.jvm.JvmRuntime.DealError error) {
                System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                    + error.origin + "|" + (error.expected == null ? "-"
                        : error.expected) + "|" + (error.actual == null ? "-"
                        : error.actual));
              }
            }
            """.formatted(className, className, quoted(entryPath));
    }

    // =========================================================================
    // 7. The adapter carrier and the carrier frame push through the bridge
    // =========================================================================

    /**
     * The adapter-crossing drive: the declared function-typed host
     * positions are crossed by a production {@code JvmRuntime.AdapterValue}
     * (a checker-valid arity extension over a DEAL body) and by a plain
     * DEAL-body carrier whose body raises, so the bridge's carrier
     * resolution (the D15 protocol for an adapter, the carried function id
     * pushed around a plain carrier) is exercised by the real toolchain on
     * both targets.
     */
    private static final String ADAPTER_DECLARATION = """
        export function apply2(f: (x: int, y: int) => int, v: int): int;
        export function frames(f: (x: int) => int, v: int): int;
        export function visit(f: (x: int) => null, v: int): int;
        """;

    private static final String ADAPTER_SOURCE = """
        import * as host from "host/adapter_probe"

        function one(x: int): int {
          return x + 1;
        }

        function boom(x: int): int {
          throw { code: "TEST_FAIL", message: "boom" };
        }

        function noop(x: int): null {
          return null;
        }

        export function test_adapter_crossing(): int {
          let f: (x: int, y: int) => int = one;
          let applied: int = host.apply2(f, 41);
          if (applied !== 42) {
            throw { code: "TEST_FAIL", message: "adapter crossing result" };
          }
          return applied;
        }

        export function test_carrier_frames(): int {
          return host.frames(boom, 1);
        }

        export function test_null_return_bridge(): int {
          return host.visit(noop, 7);
        }

        export function main(): null {
          return null;
        }
        """;

    private static final String ADAPTER_HOST_JAVA = """
        final class HostAdapter_probe {
          static final java.util.List<java.lang.String> OBSERVED =
              new java.util.ArrayList<>();

          public static Object apply2($DealRt.Fn2_I_I_R_I f, int v) {
            OBSERVED.add("adapter:" + f.getClass().getName());
            return Integer.valueOf(f.invoke(v, 1000));
          }

          public static Object frames($DealRt.Fn1_I_R_I f, int v) {
            OBSERVED.add("frames:" + f.getClass().getName());
            return Integer.valueOf(f.invoke(v));
          }

          public static Object visit($DealRt.Fn1_I_R_V f, int v) {
            OBSERVED.add("void:" + f.getClass().getName());
            f.invoke(v);
            return Integer.valueOf(v + 1);
          }
        }
        """;

    private static final String ADAPTER_HOST_LUA = """
        return {
          apply2 = function(f, v)
            return f(v, 1000)
          end,
          frames = function(f, v)
            return f(v)
          end,
          visit = function(f, v)
            f(v)
            return v + 1
          end,
        }
        """;

    private static void testAdapterCarrierCrossing() throws Exception {
        System.out.println("-- the adapter carrier crossing and the carrier frame "
            + "push through the declared bridge --");
        Fixture compiled = compileSource("host-adapter", "adapter_probe",
            ADAPTER_DECLARATION, ADAPTER_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the adapter crossing fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            check(emission.source().contains(
                    "if (this.$carrier instanceof JvmRuntime.AdapterValue __a)"),
                "the emitted bridge resolves an adapter carrier through the D15"
                    + " protocol");
            check(emission.source().contains(
                    "JvmRuntime.invokeAdapter(__a, \"-\", new java.lang.Object[]{"),
                "the emitted bridge runs JvmRuntime.invokeAdapter on an adapter"
                    + " carrier");
            check(emission.source().contains(
                    "if (__pushed) JvmRuntime.pushFrame(this.$carrier.fid);"),
                "the emitted bridge pushes the carried function id around a plain"
                    + " carrier invocation");
            check(emission.source().contains(
                    "if (__pushed) JvmRuntime.popFrame();"),
                "the emitted bridge pops the pushed frame on every path");
            Path workspace = Files.createTempDirectory("host-call-adapter");
            try {
                Files.writeString(workspace.resolve(className + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("HostAdapter_probe.java"),
                    ADAPTER_HOST_JAVA, StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("AdapterProbe.java"),
                    adapterProbe(className, compiled.entryPath()), StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java", "HostAdapter_probe.java", "AdapterProbe.java"),
                    workspace);
                check(javacRun.exitCode() == 0,
                    "the adapter crossing artifact compiles with the deployed host: "
                        + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() == 0) {
                    Outcome outcome = runProcess(List.of("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes, "AdapterProbe"),
                        workspace);
                    check(outcome.exitCode() == 0 && outcome.value().contains("OK"),
                        "the adapter crossing drive runs to completion: "
                            + escaped(outcome.value()) + " stderr="
                            + escaped(outcome.stderr()));
                    check(outcome.value().contains("ADAPTER:42"),
                        "the host-invoked bridge ran the adapter's D15 protocol"
                            + " (the source body with the leading argument): "
                            + escaped(outcome.value()));
                    check(outcome.value().contains(
                            "OBSERVED:adapter:$DealRt$__Bridge$Fn2_I_I_R_I"),
                        "the host received the declared two-parameter bridge: "
                            + escaped(outcome.value()));
                    check(outcome.value().contains("FRAMES:")
                            && !outcome.value().contains("FRAMES:-"),
                        "a DEAL body the host invoked through the bridge carries its"
                            + " own frame: " + escaped(outcome.value()));
                    check(outcome.value().contains(
                            "OBSERVED:void:$DealRt$__Bridge$Fn1_I_R_V"),
                        "the host received the declared null-return bridge: "
                            + escaped(outcome.value()));
                    check(outcome.value().contains("NULLRET:8"),
                        "the declared null-return bridge compiles and runs its"
                            + " carrier: " + escaped(outcome.value()));
                }
            } finally {
                deleteRecursively(workspace);
            }
            adapterLuaDrive(compiled);
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    /** The same crossing under real luajit (the shared carrier in both directions). */
    private static void adapterLuaDrive(Fixture compiled) throws Exception {
        SemanticLowerer.ProjectLoweringResult result = lower(compiled);
        if (result.project() == null) {
            fail("the adapter crossing fixture lowers for LuaJIT: "
                + result.diagnostics());
            return;
        }
        Path workspace = Files.createTempDirectory("host-call-adapter-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                compiled.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve("host/adapter_probe.lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, ADAPTER_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, adapterLuaDriver(artifact, compiled.entryPath()),
                StandardCharsets.UTF_8);
            Outcome outcome = runLua(probe, workspace);
            check(outcome.exitCode() == 0 && outcome.value().contains("OK"),
                "the LuaJIT adapter crossing drive runs to completion: "
                    + escaped(outcome.value()) + " stderr="
                    + escaped(outcome.stderr()));
            check(outcome.value().contains("ADAPTER:42"),
                "the LuaJIT bridge runs the adapter carrier through the D15"
                    + " protocol: " + escaped(outcome.value()));
            check(outcome.value().contains("ERR:TEST_FAIL|boom"),
                "the LuaJIT bridge runs the plain carrier and its DEAL error"
                    + " propagates unchanged: " + escaped(outcome.value()));
            check(outcome.value().contains("NULLRET:8"),
                "the LuaJIT null-return bridge runs its carrier: "
                    + escaped(outcome.value()));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM probe of the adapter crossing: the two exports and the observed bridge. */
    private static String adapterProbe(String className, String entryPath) {
        return """
            final class AdapterProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                      + error.origin);
                  return;
                }
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.exportSurface(%s);
                java.lang.Object applied = invoke(surface, "test_adapter_crossing");
                System.out.println("ADAPTER:" + applied);
                try {
                  invoke(surface, "test_carrier_frames");
                  System.out.println("FRAMES:none");
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  System.out.println("FRAMES:" + error.frames);
                }
                java.lang.Object visited = invoke(surface, "test_null_return_bridge");
                System.out.println("NULLRET:" + visited);
                for (java.lang.String observed : HostAdapter_probe.OBSERVED) {
                  System.out.println("OBSERVED:" + observed);
                }
                System.out.println("OK");
              }

              private static java.lang.Object invoke(
                  deal.codegen.jvm.JvmRuntime.Table surface, java.lang.String name) {
                return ((deal.codegen.jvm.JvmRuntime.FunctionValue) surface.read(name))
                    .fn.invoke(new java.lang.Object[]{ });
              }
            }
            """.formatted(className, className, quoted(entryPath));
    }

    /** The LuaJIT probe of the adapter crossing. */
    private static String adapterLuaDriver(Path artifact, String entryPath) {
        return """
            local function emitError(e)
              if type(e) == "table" and (e.__d or e.code ~= nil) then
                print("ERR:" .. tostring(e.code) .. "|" .. tostring(e.m or e.message))
                return
              end
              print("ERR:E9999|" .. tostring(e))
            end
            dofile("%s")
            local ok, err = __dealMain()
            if not ok then emitError(err) os.exit(0) end
            local surface = __exportSurfaces["%s"]
            local ok1, applied = pcall(surface["test_adapter_crossing"].f)
            if not ok1 then emitError(applied) os.exit(0) end
            print("ADAPTER:" .. tostring(applied))
            local ok2, frames = pcall(surface["test_carrier_frames"].f)
            if ok2 then print("FRAMES:none") else emitError(frames) end
            local ok3, visited = pcall(surface["test_null_return_bridge"].f)
            if not ok3 then emitError(visited) os.exit(0) end
            print("NULLRET:" .. tostring(visited))
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static void deployRuntime(Path workspace) throws Exception {
        Path runtime = Path.of("deal", "runtime.lua");
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(runtime, runtimeTarget);
        Path stdTarget = workspace.resolve("std");
        Files.createDirectories(stdTarget);
        try (var listing = Files.list(Path.of("std"))) {
            for (Path file : listing.sorted().toList()) {
                if (file.getFileName().toString().endsWith(".lua")) {
                    Files.copy(file, stdTarget.resolve(file.getFileName()));
                }
            }
        }
    }

    /** Deploys one corpus host implementation where the raw specifier resolves it. */
    private static void deployHostLua(Path workspace, SyncFixture fixture)
            throws Exception {
        Path target = workspace.resolve(fixture.hostSpecifier() + ".lua");
        Files.createDirectories(target.getParent());
        Files.copy(Path.of(fixture.corpusHost() + ".lua"), target);
    }

    private static Outcome runLua(Path probe, Path workspace) throws Exception {
        ProcessBuilder builder = new ProcessBuilder("luajit",
            probe.toAbsolutePath().toString());
        builder.directory(workspace.toFile());
        // The probe drives the module init itself (the chunk's own terminal
        // is suppressed), exactly like the corpus lane runner.
        builder.environment().put("DEAL_DEFER_MAIN", "1");
        return run(builder);
    }

    private static Outcome runProcess(List<String> command, Path workDir)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        return run(builder);
    }

    private static Outcome run(ProcessBuilder builder) throws Exception {
        Path stderrFile = Files.createTempFile("host-call-err", ".txt");
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        String value = stdout.strip();
        return new Outcome(exit, stdout, stderr, value);
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(java.io.File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(java.io.File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static String quoted(String text) {
        StringBuilder literal = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> literal.append("\\\"");
                case '\\' -> literal.append("\\\\");
                default -> literal.append(c);
            }
        }
        return literal.append('"').toString();
    }

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    // =========================================================================
    // 8. The trace-mode oracle agreement (the combined host drive)
    // =========================================================================

    /**
     * The admitted fixtures excluded from the trace-drive comparison, each
     * with the structural reason it cannot be compared event-for-event.
     * The map is asserted (every key is a member of the admitted set and
     * absent from the drive), so no fixture is silently skipped. The
     * reasons are three classes, none of them a missing host-call arm —
     * the excluded fixtures' host calls execute on both artifacts through
     * the same arms, and their pinned outcomes and origins are asserted by
     * the fixture-set drives above:
     * <ul>
     *   <li><b>The oracle's deterministic seam or closed value model
     *       cannot express the host terminal</b>: the deployed host
     *       invokes a crossed DEAL closure, returns a raw host function
     *       value, returns no value, returns invalid UTF-8, or crosses a
     *       declared bytes position (the oracle's closed boundary
     *       projector carries no bytes cell — the bytes representation is
     *       the sibling child's).</li>
     *   <li><b>The failing cell is inside the loaded wrapper</b> (the
     *       single check authority): the artifact cannot emit the return
     *       boundary child's START — the wrapper checks the value it
     *       received — and the oracle projects the shared closed-boundary
     *       row where the artifacts project the corpus-pinned runtime
     *       wrapper text. The artifact emits the boundary child's FAILURE
     *       with the wrapper's error on both targets.</li>
     *   <li><b>A text projection or value identity differs by
     *       construction</b>: the parameter-cell text the oracle's closed
     *       row projects differs from the pinned runtime text the wrapper
     *       produces, and the H7 per-crossing array materialization
     *       allocates its own carrier on LuaJIT (the oracle keeps the
     *       single seam value).</li>
     * </ul>
     */
    private static final Map<String, String> TRACE_DRIVE_EXCLUSIONS = Map.ofEntries(
        Map.entry("host-boundary-apply-function",
            "the deployed host invokes the crossed DEAL closure; the oracle's "
                + "HostResponder carries no invocation handle for a crossed function value"),
        Map.entry("host-nullable-function-param",
            "the deployed host invokes the crossed nullable-function closure (same "
                + "missing invocation handle)"),
        Map.entry("host-nullable-function-return-bad",
            "the deployed host returns a raw host function value; every oracle value "
                + "that is a function for the actual-kind projection also carries a "
                + "signature, so the pinned raw-function rejection row is not "
                + "expressible (the emitters pin it)"),
        Map.entry("host-empty-return-bad",
            "the deployed host returns zero results; the seam's SyncOutcome has no "
                + "\"no value\" terminal and the oracle's closed value model has no "
                + "nothing view"),
        Map.entry("host-bytes-param-mismatch-e8010",
            "the oracle's closed boundary projector has no bytes cell (the bytes "
                + "representation is the sibling child's) — the contextual bytes read "
                + "reaches it as a producer defect"),
        Map.entry("host-bytes-return-mismatch-e8010",
            "the declared bytes return cell reaches the same absent oracle boundary cell"),
        Map.entry("host-invalid-utf8-e8010",
            "the deployed host returns raw invalid UTF-8 bytes; the oracle's string "
                + "value is a Java String (valid UTF-16), so the invalid-encoding "
                + "classification is not expressible (the UTF-16 surrogate row is)"),
        Map.entry("host-bad-return",
            "the declared return cell fails inside the loaded wrapper (the single "
                + "check authority): the artifact emits the boundary child's FAILURE "
                + "with the wrapper's error but cannot emit its START (the checked "
                + "value is the wrapper's own), and the oracle's HOST_SYNC_RETURN "
                + "projection text differs from the corpus-pinned runtime text the "
                + "artifacts produce"),
        Map.entry("host-prewrapped-bad", "same return-cell failure path"),
        Map.entry("host-null-return-bad", "same return-cell failure path"),
        Map.entry("host-nullable-return-bad", "same return-cell failure path"),
        Map.entry("host-surrogate-utf8-e8010",
            "same return-cell failure path (the oracle also projects the invalid "
                + "string as invalid-unicode, the pinned corpus text is the runtime's "
                + "UTF-16 surrogate reason)"),
        Map.entry("host-rest-bad",
            "the oracle's landed HOST_PARAMETER projection text/actual (the shared "
                + "closed-boundary row) differs from the corpus-pinned runtime text "
                + "(\"expected array\" / actual number) the artifacts produce; the "
                + "deferred read's own events (the composite-read drive below) and "
                + "the event prefix through them match on all three consumers"),
        Map.entry("host-nullable-function-param-bad",
            "same parameter-cell projection text (the oracle's row vs the pinned "
                + "runtime signature-mismatch text)"),
        Map.entry("host-array-return-ok",
            "the H7 per-crossing array materialization allocates a second value on "
                + "LuaJIT, so the CALL SUCCESS identity atom differs from the "
                + "oracle's single carrier value (the JVM crossing is compared)"));

    /** The trace-drivable fixtures of the admitted set (declaration order). */
    private static final List<String> TRACE_DRIVE_FIXTURES = traceDriveFixtures();

    private static List<String> traceDriveFixtures() {
        List<String> fixtures = new ArrayList<>();
        for (String name : SYNC_FIXTURES) {
            if (!TRACE_DRIVE_EXCLUSIONS.containsKey(name)) {
                fixtures.add(name);
            }
        }
        return List.copyOf(fixtures);
    }

    /**
     * The trace-drive app source of one fixture: its own host-call body on
     * the entry path, so the oracle's init walk and the trace-mode
     * artifacts execute the identical host calls. A fixture whose host
     * calls already sit in {@code main} keeps its source; a fixture whose
     * calls sit in a {@code test_*} export has that function's body
     * (statements unchanged) moved onto the entry path: the export prefix
     * is dropped (an exported body invoked through both its external entry
     * and a source call has no single invocation shape) and the original
     * main invokes it.
     */
    private static String traceDriveSource(String rawApp) {
        String app = stripDirectives(rawApp);
        int at = app.indexOf("export function test_");
        if (at < 0) {
            return app;
        }
        int nameStart = at + "export function ".length();
        String testName = app.substring(nameStart, app.indexOf('(', nameStart));
        String unexported = app.substring(0, at) + "function "
            + app.substring(nameStart);
        String mainBody = "export function main(): null {\n  return null;\n}";
        if (!unexported.contains(mainBody)) {
            throw new IllegalStateException("the fixture carries no plain main: "
                + unexported);
        }
        return unexported.replace(mainBody, "export function main(): null {\n  "
            + testName + "();\n  return null;\n}");
    }

    /** One decoded trace protocol run: the ordered events and the terminal. */
    private record TraceRun(java.util.List<String> events,
        SemanticRuntimeModel.Terminal terminal) {
    }

    /** Decodes one artifact's protocol stream (events and the single terminal). */
    private static TraceRun decodeTrace(String stderr) {
        java.util.List<String> events = new ArrayList<>();
        SemanticRuntimeModel.Terminal terminal = null;
        for (String line : stderr.split("\n", -1)) {
            if (line.isEmpty()) {
                continue;
            }
            Object decoded;
            try {
                decoded = SemanticTraceProtocol.decode(line);
            } catch (RuntimeException exception) {
                throw new IllegalStateException("the trace protocol does not decode '"
                    + line + "': " + exception.getMessage());
            }
            if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                events.add(event.text());
            } else if (decoded instanceof SemanticRuntimeModel.Terminal term) {
                if (terminal != null) {
                    throw new IllegalStateException("two terminal records: " + line);
                }
                terminal = term;
            }
        }
        if (terminal == null) {
            throw new IllegalStateException("the artifact published no terminal record");
        }
        return new TraceRun(java.util.List.copyOf(events), terminal);
    }

    /** The canonical text of one terminal (the pinned snapshot fields). */
    private static String terminalText(SemanticRuntimeModel.Terminal terminal) {
        return switch (terminal) {
            case SemanticRuntimeModel.Terminal.Success success ->
                "success:" + success.resultAtom();
            case SemanticRuntimeModel.Terminal.DealFailure failure -> {
                SemanticRuntimeModel.ErrorSnapshot error = failure.error();
                yield "failure:" + error.code() + "|" + error.message() + "|"
                    + error.origin() + "|" + error.expected() + "|" + error.actual();
            }
        };
    }

    /** Asserts one artifact trace equals the oracle's event-for-event. */
    private static void checkTraceParity(String name, String target,
            TraceRun oracle, TraceRun artifact) {
        java.util.List<String> expected = oracle.events();
        java.util.List<String> actual = artifact.events();
        if (!expected.equals(actual)) {
            failed++;
            int limit = Math.min(expected.size(), actual.size());
            for (int i = 0; i < limit; i++) {
                if (!expected.get(i).equals(actual.get(i))) {
                    System.err.println("FAIL: " + name + " (" + target
                        + ") trace event " + i + " oracle [" + expected.get(i)
                        + "] vs artifact [" + actual.get(i) + "]");
                    return;
                }
            }
            System.err.println("FAIL: " + name + " (" + target + ") trace length "
                + expected.size() + " (oracle) vs " + actual.size() + " (artifact)");
            return;
        }
        passed++;
    }

    // -- the scripted host terminals (the deployed host's own behavior) -------

    private static SemanticOracle.Value str(String value) {
        return new SemanticOracle.Value.StrValue(value);
    }

    private static SemanticOracle.Value intValue(long value) {
        return new SemanticOracle.Value.IntValue(value);
    }

    private static SemanticOracle.Value nullValue() {
        return SemanticOracle.Value.NullValue.INSTANCE;
    }

    private static String stringArg(List<SemanticOracle.Value> args, int index) {
        return ((SemanticOracle.Value.StrValue) args.get(index)).value();
    }

    /** The joined text of the declared string[] argument (the rest_join host). */
    private static String joinedParts(String separator, SemanticOracle.Value value) {
        SemanticOracle.Value.ArrayValue parts =
            (SemanticOracle.Value.ArrayValue) value;
        StringBuilder joined = new StringBuilder();
        for (int i = 0; i < parts.elements().size(); i++) {
            if (i > 0) {
                joined.append(separator);
            }
            joined.append(((SemanticOracle.Value.StrValue) parts.elements().get(i))
                .value());
        }
        return joined.toString();
    }

    /**
     * The scripted host seam of one trace drive: the deployed host
     * implementation's own terminals (the values, the state transitions,
     * and the loaded surface entries) expressed through the deterministic
     * seam, so the oracle executes the identical host behavior the
     * artifacts run against the real host module.
     */
    private static SemanticOracle.HostResponder traceHostResponder(String name) {
        return new SemanticOracle.HostResponder() {
            private final Map<String, SemanticOracle.Value> entries =
                new LinkedHashMap<>();
            private int nextValue = 0;

            @Override
            public SemanticOracle.Value loadedExport(ModuleId module, String export,
                    RuntimeDescriptor descriptor) {
                return entries.computeIfAbsent(module.path() + "." + export,
                    key -> new SemanticOracle.Value.IntrinsicValue("host:" + key));
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                String key = name + " " + module.path() + "." + export;
                return switch (key) {
                    case "host-bad-return host.bad_return.getNumber" ->
                        new SyncOutcome.Returned(str("not a number"));
                    case "host-prewrapped-bad host.prewrapped_bad.ping" ->
                        new SyncOutcome.Returned(str("junk"));
                    case "host-prewrapped-ok host.prewrapped_ok.greet" ->
                        new SyncOutcome.Returned(str("hello " + stringArg(args, 0)));
                    case "host-prewrapped-ok host.prewrapped_ok.ping" ->
                        new SyncOutcome.Returned(nullValue());
                    case "host-extra-export-ignored host.extra_export.ping" ->
                        new SyncOutcome.Returned(str("pong"));
                    case "host-boundary-boolean-roundtrip host.boundary.echoBoolean",
                        "host-boundary-int-minimum-param host.boundary.echoInt",
                        "host-boundary-null-narrowing host.boundary.echoString",
                        "host-boundary-nullable-int-null-roundtrip host.boundary.nullableInt",
                        "host-boundary-nullable-int-value-roundtrip host.boundary.nullableInt",
                        "host-boundary-number-roundtrip host.boundary.echoNumber",
                        "host-boundary-unicode-string-roundtrip host.boundary.echoString" ->
                        new SyncOutcome.Returned(args.get(0));
                    case "host-boundary-repeat-call host.boundary.nextValue" ->
                        new SyncOutcome.Returned(intValue(++nextValue));
                    case "host-null-return-bad host.nullreturn_bad.ping" ->
                        new SyncOutcome.Returned(str("junk"));
                    case "host-null-return-ok host.nullreturn_ok.ping" ->
                        new SyncOutcome.Returned(nullValue());
                    case "host-nullable-function-return-ok host.nullable_fn_return.getCallback" ->
                        new SyncOutcome.Returned(nullValue());
                    case "host-nullable-return-bad host.nullable_return.find" ->
                        new SyncOutcome.Returned(intValue(42));
                    case "host-nullable-return-ok host.nullable_return.find" ->
                        "__NULL__".equals(stringArg(args, 0))
                            ? new SyncOutcome.Returned(nullValue())
                            : new SyncOutcome.Returned(args.get(0));
                    case "host-rest-ok host.rest_join.join" ->
                        new SyncOutcome.Returned(str(joinedParts(stringArg(args, 0),
                            args.get(1))));
                    case "host-array-return-ok host.array_return.split" ->
                        new SyncOutcome.Returned(new SemanticOracle.Value.ArrayValue(
                            List.of(str("a"), str("b"), str("c")),
                            ((RuntimeDescriptor.Array) descriptor.returnType())
                                .element()));
                    case "host-surrogate-utf8-e8010 host.bad_string.surrogateString" ->
                        new SyncOutcome.Returned(str("\uD800"));
                    default -> throw new IllegalStateException(
                        "the trace drive scripts no host terminal for '" + key
                            + "' (a host call the deployed host never receives, or"
                            + " an unscripted terminal)");
                };
            }
        };
    }

    // -- the drive -----------------------------------------------------------

    private static void testOracleTraceAgreement() throws Exception {
        System.out.println("-- the trace-mode oracle agreement: the sync host calls run "
            + "through the oracle and both trace-mode artifacts event-for-event --");
        for (String name : TRACE_DRIVE_FIXTURES) {
            SyncFixture fixture = syncFixture(name);
            String rawApp = Files.readString(Path.of(fixture.corpusFixture()),
                StandardCharsets.UTF_8);
            Fixture compiled = compileWith(fixture.name(), fixture.hostStem(),
                Files.readString(Path.of(fixture.corpusHost() + ".d.deal"),
                    StandardCharsets.UTF_8),
                traceDriveSource(rawApp));
            Path workspace = Files.createTempDirectory("host-trace");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the trace drive fixture '" + name + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                SemanticRuntimeModel.ConsumerRun oracleRun =
                    SemanticOracle.executeProjectInits(project, result.tables(),
                        result.registries(), traceHostResponder(name));
                java.util.List<String> oracleEvents = new ArrayList<>();
                for (SemanticRuntimeModel.TraceEvent event : oracleRun.trace()) {
                    oracleEvents.add(event.text());
                }
                TraceRun oracle = new TraceRun(java.util.List.copyOf(oracleEvents),
                    oracleRun.terminal());

                // The LuaJIT trace artifact: the host module on package.path,
                // the chunk's own init walk (the entry main drives the host
                // calls), the trace protocol on stderr.
                Path luaArtifact = workspace.resolve("project.lua");
                Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(
                    project, result.tables(), result.registries(),
                    compiled.surface()), StandardCharsets.UTF_8);
                deployRuntime(workspace);
                deployHostLua(workspace, fixture);
                Outcome luaOutcome = runProcess(List.of("luajit",
                    luaArtifact.toAbsolutePath().toString()), workspace);
                check(luaOutcome.exitCode() == 0, "the trace drive fixture '" + name
                    + "' runs under luajit: " + escaped(luaOutcome.stderr()));
                TraceRun lua = decodeTrace(luaOutcome.stderr());
                checkTraceParity(name, "luajit", oracle, lua);
                checkEq(terminalText(oracle.terminal()), terminalText(lua.terminal()),
                    name + " (luajit) terminal parity");

                // The JVM trace artifact: compiled with the deployed host
                // implementation, the trace protocol on stderr.
                JvmSemanticEmitter.EmissionResult jvmEmission =
                    JvmSemanticEmitter.emitProject(project, result.tables(),
                        result.registries(), compiled.surface());
                String jvmClass = jvmEmission.className();
                String hostClass = JvmBackend.classNameFor(fixture.hostSpecifier());
                Files.writeString(workspace.resolve(jvmClass + ".java"),
                    jvmEmission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve(hostClass + ".java"),
                    Files.readString(Path.of(fixture.corpusHost() + ".java")),
                    StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    jvmClass + ".java", hostClass + ".java"), workspace);
                check(javacRun.exitCode() == 0, "the trace drive fixture '" + name
                    + "' compiles under javac with the deployed host: "
                    + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() != 0) {
                    continue;
                }
                Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, jvmClass),
                    workspace);
                check(jvmOutcome.exitCode() == 0, "the trace drive fixture '" + name
                    + "' runs under java: exit=" + jvmOutcome.exitCode() + " "
                    + escaped(jvmOutcome.stderr()));
                TraceRun jvm = decodeTrace(jvmOutcome.stderr());
                checkTraceParity(name, "java", oracle, jvm);
                checkEq(terminalText(oracle.terminal()), terminalText(jvm.terminal()),
                    name + " (java) terminal parity");
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
        for (Map.Entry<String, String> exclusion : TRACE_DRIVE_EXCLUSIONS.entrySet()) {
            check(SYNC_FIXTURES.contains(exclusion.getKey())
                    && !TRACE_DRIVE_FIXTURES.contains(exclusion.getKey()),
                "the trace-drive exclusion '" + exclusion.getKey()
                    + "' is a member of the admitted set: " + exclusion.getValue());
        }
    }

    /**
     * The composite contextual read's parity (the ISSUE-0651 deferral): a
     * function/array contextual read whose value carries no matching shape
     * passes through in the oracle and in both emitted arms, so the
     * consuming declared cell — the host parameter cell — carries the
     * pinned E8010 at the call origin and the read never fails. The
     * trace-mode artifacts of the same run are compared event-for-event
     * through the read's own SUCCESS event on both targets (the wrong-kind
     * fixture's consuming cell is one of the trace-drive exclusions: the
     * oracle projects the shared closed-boundary row there while the
     * artifacts project the corpus-pinned runtime wrapper text, so the
     * comparison stops where the consuming cell starts).
     */
    private static void testCompositeReadOracleDeferral() throws Exception {
        System.out.println("-- the composite contextual read defers in the oracle exactly "
            + "like both emitted arms: the wrong-kind value reaches the host "
            + "parameter cell, never the read --");
        for (String name : List.of("host-rest-bad")) {
            SyncFixture fixture = syncFixture(name);
            Fixture compiled = compileWith(fixture.name(), fixture.hostStem(),
                Files.readString(Path.of(fixture.corpusHost() + ".d.deal"),
                    StandardCharsets.UTF_8),
                traceDriveSource(Files.readString(Path.of(fixture.corpusFixture()),
                    StandardCharsets.UTF_8)));
            Path workspace = Files.createTempDirectory("host-composite-read");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the composite-read fixture '" + name + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                SemanticRuntimeModel.ConsumerRun oracleRun =
                    SemanticOracle.executeProjectInits(project, result.tables(),
                        result.registries(), traceHostResponder(name));
                java.util.List<String> events = new ArrayList<>();
                for (SemanticRuntimeModel.TraceEvent event : oracleRun.trace()) {
                    events.add(event.text());
                }
                // The read boundary's terminal is a SUCCESS (the value
                // passed through; a failure there would have emitted a
                // FAILURE with the read's origin).
                long boundaryOp = compositeBoundaryOp(project);
                long readOp = compositeReadOp(project, boundaryOp);
                boolean readPassed = false;
                boolean readFailed = false;
                for (SemanticRuntimeModel.TraceEvent event : oracleRun.trace()) {
                    if (event.op().id() == boundaryOp
                            && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        readPassed = true;
                    }
                    if (event.op().id() == boundaryOp
                            && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                        readFailed = true;
                    }
                }
                check(readPassed && !readFailed, "the oracle's composite contextual read "
                    + "of '" + name + "' passes the wrong-kind value through (the "
                    + "consuming declared cell carries the pinned projection); "
                    + "events=" + events);

                // The read-side event prefix (the deferral's three-consumer
                // parity): identical through the read's own SUCCESS event on
                // both trace-mode artifacts.
                int readSuccessIndex = -1;
                for (int i = 0; i < oracleRun.trace().size(); i++) {
                    SemanticRuntimeModel.TraceEvent event = oracleRun.trace().get(i);
                    if (event.op().id() == readOp
                            && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        readSuccessIndex = i;
                        break;
                    }
                }
                check(readSuccessIndex >= 0, "the oracle publishes the composite read's "
                    + "SUCCESS event");
                if (readSuccessIndex < 0) {
                    continue;
                }
                java.util.List<String> oraclePrefix = new ArrayList<>();
                for (int i = 0; i <= readSuccessIndex; i++) {
                    oraclePrefix.add(oracleRun.trace().get(i).text());
                }

                Path luaArtifact = workspace.resolve("project.lua");
                Files.writeString(luaArtifact, LuaSemanticEmitter.emitProject(project,
                    result.tables(), result.registries(), compiled.surface()),
                    StandardCharsets.UTF_8);
                deployRuntime(workspace);
                deployHostLua(workspace, fixture);
                Outcome luaOutcome = runProcess(List.of("luajit",
                    luaArtifact.toAbsolutePath().toString()), workspace);
                checkTracePrefix(name, "luajit", oraclePrefix,
                    decodeTrace(luaOutcome.stderr()).events());

                JvmSemanticEmitter.EmissionResult jvmEmission =
                    JvmSemanticEmitter.emitProject(project, result.tables(),
                        result.registries(), compiled.surface());
                String jvmClass = jvmEmission.className();
                String hostClass = JvmBackend.classNameFor(fixture.hostSpecifier());
                Files.writeString(workspace.resolve(jvmClass + ".java"),
                    jvmEmission.source(), StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve(hostClass + ".java"),
                    Files.readString(Path.of(fixture.corpusHost() + ".java")),
                    StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    jvmClass + ".java", hostClass + ".java"), workspace);
                check(javacRun.exitCode() == 0, "the composite-read fixture '" + name
                    + "' compiles under javac: " + javacRun.stdout() + javacRun.stderr());
                if (javacRun.exitCode() == 0) {
                    Outcome jvmOutcome = runProcess(List.of("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes, jvmClass),
                        workspace);
                    checkTracePrefix(name, "java", oraclePrefix,
                        decodeTrace(jvmOutcome.stderr()).events());
                }
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
    }

    /** Asserts one artifact's event stream begins with the oracle's prefix. */
    private static void checkTracePrefix(String name, String target,
            List<String> expectedPrefix, List<String> actual) {
        for (int i = 0; i < expectedPrefix.size(); i++) {
            if (i >= actual.size() || !expectedPrefix.get(i).equals(actual.get(i))) {
                failed++;
                System.err.println("FAIL: " + name + " (" + target
                    + ") trace prefix event " + i + " oracle ["
                    + expectedPrefix.get(i) + "] vs artifact ["
                    + (i < actual.size() ? actual.get(i) : "<absent>") + "]");
                return;
            }
        }
        passed++;
    }

    /** The read op parenting the one composite contextual-read boundary child. */
    private static long compositeReadOp(ExecutableLoweredProject project,
            long boundaryOpId) {
        LoweredModuleUnit unit = project.modules().get(project.entryModule());
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.MEMBER_READ
                    || op.kind() == SemanticOpKind.OPTIONAL_READ) {
                for (SemanticOp candidate : unit.ops()) {
                    if (candidate.opId().id() == boundaryOpId
                            && op.opId().equals(candidate.origin().parentOpId())) {
                        return op.opId().id();
                    }
                }
            }
        }
        throw new IllegalStateException("the composite read from boundary "
            + boundaryOpId + " is missing");
    }

    /** The op id of the one composite contextual-read boundary child of the entry. */
    private static long compositeBoundaryOp(ExecutableLoweredProject project) {
        LoweredModuleUnit unit = project.modules().get(project.entryModule());
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.MEMBER_READ
                    && op.kind() != SemanticOpKind.OPTIONAL_READ) {
                continue;
            }
            for (SemanticOp candidate : unit.ops()) {
                if (!op.opId().equals(candidate.origin().parentOpId())) {
                    continue;
                }
                if (candidate.kind() != SemanticOpKind.BOUNDARY
                        || !(candidate.payload()
                            instanceof KindPayload.BoundaryPayload boundary)) {
                    continue;
                }
                RuntimeDescriptor descriptor = boundary.descriptor();
                RuntimeDescriptor inner = descriptor instanceof RuntimeDescriptor.Nullable nullable
                    ? nullable.inner() : descriptor;
                if (inner instanceof RuntimeDescriptor.Func
                        || inner instanceof RuntimeDescriptor.Array
                        || inner instanceof RuntimeDescriptor.Bytes) {
                    return candidate.opId().id();
                }
            }
        }
        throw new IllegalStateException("the fixture carries no composite contextual read");
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

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Sync Host Call Realization Tests (ISSUE-0651) ===\n");
        String dump = System.getenv("DEAL_DUMP_FIXTURE");
        if (dump != null) {
            dumpFixture(dump);
            return;
        }
        testLuaFixtureSet();
        testJvmFixtureSet();
        testTwoAliasCall();
        testJvmCrossingProjection();
        testAdapterCarrierCrossing();
        testFailClosedSeeds();
        testJvmHostFunctionValueCall();
        testLuaHostFunctionValueCall();
        testOracleTraceAgreement();
        testCompositeReadOracleDeferral();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Sync Host Call Realization Tests Passed ===");
    }

    /** A debugging dump of one fixture's emitted artifacts (never a verdict). */
    private static void dumpFixture(String name) throws Exception {
        SyncFixture fixture = syncFixture(name);
        Fixture compiled = compile(fixture);
        SemanticLowerer.ProjectLoweringResult result = lower(compiled);
        if (result.project() == null) {
            System.out.println("LOWERING FAILED: " + result.diagnostics());
            return;
        }
        ExecutableLoweredProject project = result.project();
        String lua = LuaSemanticEmitter.emitProductionProject(project, result.tables(),
            result.registries(), compiled.surface());
        Path luaOut = Path.of("/tmp/deal-dump-" + name + ".lua");
        Files.writeString(luaOut, lua, StandardCharsets.UTF_8);
        System.out.println("LUA: " + luaOut);
        String className = JvmBackend.classNameFor(project.entryModule().path());
        JvmSemanticEmitter.EmissionResult emission = JvmSemanticEmitter
            .emitProductionProject(project, result.tables(), result.registries(),
                className, compiled.surface());
        Path javaOut = Path.of("/tmp/deal-dump-" + name + ".java");
        Files.writeString(javaOut, emission.source(), StandardCharsets.UTF_8);
        System.out.println("JAVA: " + javaOut);
        System.out.println("ENTRY: " + compiled.entryPath());
        System.out.println("HOST: " + fixture.hostSpecifier());
    }
}
