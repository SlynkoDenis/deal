package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.test.conformance.SidecarExpectations;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0683: the named fixture and origin battery — the pinned rows, the
 * pinned origins, and the JS reference program (design sources
 * {@code function-typed-value-materialization-and-dispatch} M7 item 3 and M8;
 * {@code conversion-intrinsic-function-values} J6 item 2; the materialization,
 * dynamic call, and dynamic DEAL-body cell contracts).
 *
 * <ol>
 *   <li><b>The corpus pins are unchanged.</b> Each named fixture and its
 *       sidecar carry their pinned outcome: the two failure rows with their
 *       code, message stem and texts, {@code expected}/{@code actual} fields
 *       and the declared type annotation's span
 *       ({@code dynamic-nonfunction-to-function-e8001}: E8001 at line 8
 *       column 10; {@code canonical-sig-mismatch-e8010}: E8010 with the two
 *       canonical signature texts at line 12 column 10), and the four
 *       {@code runtime-ok} outcomes ({@code closure-returned-from-module},
 *       {@code intrinsic-as-function-value}, {@code intrinsic-as-callback},
 *       {@code intrinsic-arity-extension}). A sidecar's legacy message tail or
 *       actual-kind token is the lane cutover's ({@code ISSUE-0628}), never a
 *       route-specific row fork: the drive asserts the sidecars verbatim and
 *       the shared producers against the pinned texts.</li>
 *   <li><b>The failure fixtures through the production entry.</b> The corpus
 *       fixture text (classification headers stripped, the corpus entry shim
 *       replaced by the drive's own entry) compiles through the real
 *       orchestrator, lowers through the production project entry with zero
 *       diagnostics, and passes the closed schema and bindings gates; the
 *       free declaration boundary fails with the pinned row at the declared
 *       annotation's span on the oracle, the LuaJIT artifact under real
 *       {@code luajit}, and the JVM artifact under
 *       {@code javac --release 25 -proc:none} plus {@code java}, with exactly
 *       one FAILURE terminal per consumer (the three-consumer comparison
 *       includes the origin).</li>
 *   <li><b>The runtime-ok fixtures through the production entry.</b> The
 *       returned-closure fixture (a runtime-resolved cross-module closure
 *       factory result dispatched on its carrier's own class; its recorded
 *       call-owned cell executed exactly once by the invocation site) and the
 *       three intrinsic fixtures run to their pinned outcomes on all three
 *       consumers.</li>
 *   <li><b>The JS reference program.</b> The stdlib function-value program of
 *       {@code test/JsBackendTest.java} (the intrinsic and stdlib-value forms)
 *       is reproduced as a focused drive on both targets and the oracle,
 *       asserting the conversion results and the console effect.</li>
 * </ol>
 */
public class NamedFixtureAndOriginBatteryTest {

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
        check(Objects.equals(expected, actual), message + " (expected " + expected
            + ", got " + actual + ")");
    }

    private static final Path CORPUS = Path.of("test", "conformance");
    private static final String BACKEND_RUNTIME = "backend-runtime";

    // =========================================================================
    // 1. The corpus pins
    // =========================================================================

    /** One named fixture of the battery with its pinned outcome. */
    private record NamedFixture(
        String relativePath,
        String exportName,
        String resultType,
        String expectedAtom,
        List<String> companions,
        String pinnedCode,
        String pinnedMessage,
        String pinnedExpected,
        String pinnedActual,
        int pinnedLine,
        int pinnedColumn) {

        String fixtureFile() {
            return BACKEND_RUNTIME + "/" + relativePath + ".deal";
        }

        String sidecarFile() {
            return BACKEND_RUNTIME + "/" + relativePath + ".expect.json";
        }

        boolean runtimeOk() {
            return pinnedCode == null;
        }

        String what() {
            return relativePath;
        }
    }

    private static NamedFixture runtimeOk(String path, String export, String type,
                                          String atom, String... companions) {
        return new NamedFixture(path, export, type, atom, List.of(companions),
            null, null, null, null, 0, 0);
    }

    private static NamedFixture runtimeError(String path, String export, String code,
                                             String message, String expected,
                                             String actual, int line, int column) {
        return new NamedFixture(path, export, "int", null, List.of(), code, message,
            expected, actual, line, column);
    }

    /** The function-typed declaration crossing with a non-function value. */
    private static final NamedFixture NONFUNCTION_TO_FUNCTION =
        runtimeError("type-system/dynamic-nonfunction-to-function-e8001",
            "test_dynamic_nonfunction_to_function_runtime_error", "E8001",
            "expected function", "function", "number", 8, 10);

    /** The differing carried signature (the canonical descriptor text pin). */
    private static final NamedFixture CANONICAL_SIG_MISMATCH =
        runtimeError("descriptors/canonical-sig-mismatch-e8010",
            "test_canonical_sig_mismatch", "E8010",
            "function signature mismatch: expected (int)->int, got (int)->string",
            "(int)->int", "(int)->string", 12, 10);

    /** The closure returned from an imported factory (its captured state). */
    private static final NamedFixture CLOSURE_RETURNED_FROM_MODULE =
        runtimeOk("closures/closure-returned-from-module",
            "test_closure_returned_from_module", "int", "12",
            "closures/closure_batch2_lib");

    private static final NamedFixture INTRINSIC_AS_FUNCTION_VALUE =
        runtimeOk("functions/intrinsic-as-function-value",
            "test_intrinsic_as_function_value", "int", "3");

    private static final NamedFixture INTRINSIC_AS_CALLBACK =
        runtimeOk("functions/intrinsic-as-callback",
            "test_intrinsic_as_callback", "number", "7.0");

    private static final NamedFixture INTRINSIC_ARITY_EXTENSION =
        runtimeOk("functions/intrinsic-arity-extension",
            "test_intrinsic_arity_extension", "int", "9");

    /** The JS reference program's own drive (no corpus sidecar). */
    private static final NamedFixture JS_REFERENCE =
        runtimeOk("functions/js-reference-program", "test", "int", "1");

    private static final List<NamedFixture> NAMED = List.of(
        NONFUNCTION_TO_FUNCTION, CANONICAL_SIG_MISMATCH,
        CLOSURE_RETURNED_FROM_MODULE, INTRINSIC_AS_FUNCTION_VALUE,
        INTRINSIC_AS_CALLBACK, INTRINSIC_ARITY_EXTENSION);

    private static void testCorpusPins() throws Exception {
        System.out.println("-- the named fixtures and their pinned sidecars --");
        for (NamedFixture fixture : NAMED) {
            Path file = CORPUS.resolve(fixture.fixtureFile());
            Path sidecar = CORPUS.resolve(fixture.sidecarFile());
            check(Files.exists(file), fixture.what() + " is a corpus fixture");
            check(Files.exists(sidecar), fixture.what() + " carries its sidecar");
            if (!Files.exists(file) || !Files.exists(sidecar)) {
                continue;
            }
            String raw = Files.readString(file, StandardCharsets.UTF_8);
            SidecarExpectations.StructuredExpectationSidecar parsed =
                SidecarExpectations.StructuredExpectationSidecar.parse(
                    Files.readString(sidecar, StandardCharsets.UTF_8));
            for (String backend : List.of("luajit", "jvm", "js")) {
                check(parsed.byBackend().containsKey(backend), fixture.what()
                    + ": the sidecar pins the '" + backend + "' lane");
            }
            SidecarExpectations.RuntimeExpectation expectation =
                parsed.expectationFor("luajit");
            check(expectation instanceof SidecarExpectations.RuntimeExpectation.Executed,
                fixture.what() + ": the LuaJIT leg is an executed expectation");
            if (!(expectation instanceof SidecarExpectations.RuntimeExpectation.Executed
                    executed)) {
                continue;
            }
            if (fixture.runtimeOk()) {
                checkEq("runtime-ok", executed.mode(), fixture.what()
                    + ": the pinned mode");
                checkEq(0, executed.exitCode(), fixture.what()
                    + ": the pinned exit code");
                checkEq("", new String(executed.stdout(), StandardCharsets.UTF_8),
                    fixture.what() + ": the pinned stdout");
                checkEq("", new String(executed.stderr(), StandardCharsets.UTF_8),
                    fixture.what() + ": the pinned stderr");
                check(executed.error() == null, fixture.what()
                    + ": a runtime-ok fixture pins no error snapshot");
                continue;
            }
            // The two failure rows: the sidecar's own fields are the pins this
            // drive asserts (the drive never rewrites a sidecar).
            checkEq("runtime-error", executed.mode(), fixture.what()
                + ": the pinned mode");
            SidecarExpectations.ErrorExpectation error = executed.error();
            check(error != null, fixture.what() + ": the pinned error snapshot");
            if (error == null) {
                continue;
            }
            checkEq(fixture.pinnedCode(), error.code(), fixture.what()
                + ": the pinned code");
            checkEq(fixture.pinnedMessage(), error.message(), fixture.what()
                + ": the pinned message");
            checkEq(fixture.pinnedExpected(), error.expected().orElse(null),
                fixture.what() + ": the pinned expected field");
            checkEq(fixture.pinnedActual(), error.actual().orElse(null),
                fixture.what() + ": the pinned actual field");
            checkEq(fixture.pinnedLine(), error.line(), fixture.what()
                + ": the pinned line");
            checkEq(fixture.pinnedColumn(), error.column(), fixture.what()
                + ": the pinned column");
            checkEq(fixture.fixtureFile(), error.sourceFile(), fixture.what()
                + ": the pinned source file");
            // The declared type annotation's span is the pinned origin.
            List<String> lines = raw.lines().toList();
            String annotated = lines.get(fixture.pinnedLine() - 1);
            check(annotated.startsWith("  let f: ("), fixture.what()
                + ": the pinned span is the declaration's type annotation: '"
                + annotated + "'");
            check(annotated.substring(fixture.pinnedColumn() - 1).startsWith("("),
                fixture.what() + ": the pinned column is the annotation's first "
                    + "character: '" + annotated + "'");
        }
        // The returned-closure fixture's companion factory is part of the
        // corpus closure the drive compiles.
        check(Files.exists(CORPUS.resolve(BACKEND_RUNTIME + "/closures/"
                + "closure_batch2_lib.deal")),
            "the returned-closure fixture's companion factory is part of the corpus");
    }

    // =========================================================================
    // 2. The production-entry drive harness
    // =========================================================================

    /** One compiled project (the production entry's checked input). */
    private record Compiled(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, CanonicalModuleIdentity> identities,
        int strippedHeaderLines) {
    }

    /** One lowered, validated fixture drive. */
    private record Drive(
        Compiled compiled,
        SemanticLowerer.ProjectLoweringResult result,
        LoweredModuleUnit unit,
        NamedFixture spec) {

        ExecutableLoweredProject project() {
            return result.project();
        }

        Map<ModuleId, StructuredBodyTable> tables() {
            return result.tables();
        }

        Map<ModuleId, ClassFactoryRegistry> registries() {
            return result.registries();
        }
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * Strips the corpus classification headers (the lane's metadata comments: a
     * production compile would reject them as unknown directives, E1044) and
     * counts the dropped lines so the pinned raw coordinates rebase onto the
     * compiled source exactly as the corpus lane's deployment map does.
     */
    private static String stripHeaders(String raw, int[] strippedLines) {
        String stripped = ConformanceHarnessMetadata.stripClassificationHeaders(raw);
        strippedLines[0] = raw.split("\n", -1).length
            - stripped.split("\n", -1).length;
        return stripped;
    }

    private static final String CORPUS_ENTRY_SHIM =
        "export function main(): null {\n  return null;\n}\n";

    /**
     * Materializes one corpus fixture (headers stripped, the corpus entry shim
     * removed) at its corpus-relative path inside a temp mirror, adds the
     * drive's own entry module (which imports the fixture and calls its test
     * export), and compiles the project through the real orchestrator — the
     * production entry.
     */
    private static Compiled compileFixture(NamedFixture fixture) throws Exception {
        Path root = Files.createTempDirectory("named-fixture-battery");
        Path corpusRoot = root.resolve("corpus");
        Path fixtureFile = corpusRoot.resolve(fixture.fixtureFile());
        Files.createDirectories(fixtureFile.getParent());
        String raw = Files.readString(CORPUS.resolve(fixture.fixtureFile()),
            StandardCharsets.UTF_8);
        int[] strippedLines = new int[1];
        String source = stripHeaders(raw, strippedLines);
        // The corpus entry shim is the lane's entry (the lane invokes every
        // zero-arity export of the fixture as its own entry module); the
        // drive supplies its own entry module and calls the fixture's test
        // export, so the shim is removed — the fixture module then carries no
        // ENTRY_INVOKE of its own (the emitters never run a non-entry module's
        // entry delegation).
        check(source.contains(CORPUS_ENTRY_SHIM), fixture.what()
            + ": the corpus entry shim is present for the drive's own entry");
        source = source.replace(CORPUS_ENTRY_SHIM, "");
        Files.writeString(fixtureFile, source, StandardCharsets.UTF_8);
        for (String companion : fixture.companions()) {
            Path companionFile = corpusRoot.resolve(BACKEND_RUNTIME)
                .resolve(companion + ".deal");
            Files.createDirectories(companionFile.getParent());
            int[] ignored = new int[1];
            String companionRaw = Files.readString(
                CORPUS.resolve(BACKEND_RUNTIME).resolve(companion + ".deal"),
                StandardCharsets.UTF_8);
            Files.writeString(companionFile, stripHeaders(companionRaw, ignored),
                StandardCharsets.UTF_8);
        }
        Path entry = root.resolve("app.deal");
        Files.writeString(entry, driver(fixture), StandardCharsets.UTF_8);
        return compile(root, entry, fixture.what(), strippedLines[0]);
    }

    /** The drive's own entry: it imports the fixture and calls its test export. */
    private static String driver(NamedFixture fixture) {
        String call = "  let r: " + fixture.resultType() + " = fx."
            + fixture.exportName() + "()\n";
        String body = fixture.runtimeOk()
            ? call + "  if (r !== " + fixture.expectedAtom() + ") {\n"
                + "    throw { code: \"TEST_FAIL\", message: \""
                + fixture.relativePath() + " fixture drive\" }\n"
                + "  }\n"
            : call;
        String specifier = fixture.fixtureFile();
        if (specifier.endsWith(".deal")) {
            specifier = specifier.substring(0, specifier.length() - ".deal".length());
        }
        return "import * as fx from \"./corpus/" + specifier + "\"\n\n"
            + "export function main(): null {\n" + body + "  return null\n}\n";
    }

    /** The real orchestrator over one project root (the production entry). */
    private static Compiled compile(Path root, Path entry, String what,
                                    int strippedHeaderLines) throws Exception {
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry.toAbsolutePath(), root.resolve("out").toAbsolutePath(),
            false, false, false, false, Backend.LUAJIT, null,
            List.of(root.toAbsolutePath()), null, null, productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        check(compiled, what + ": the production orchestrator compiles the "
            + "project: " + orchestrator.diagnostics());
        check(built != null && built.input() != null && built.index() != null
                && !built.hasErrors(),
            what + ": the checked project builds: "
                + (built == null ? "null" : built.diagnostics()));
        check(manifests != null && manifests.manifests() != null,
            what + ": the requirement manifests compute");
        check(orchestrator.hostDeclarationSurface() != null,
            what + ": the host declaration surface exists");
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declaration : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declaration,
                new CanonicalModuleIdentity.ExternalModule(declaration.path()));
        }
        return new Compiled(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), identities, strippedHeaderLines);
    }

    /** The production project lowering entry over one compiled project. */
    private static Drive lower(Compiled compiled, ModuleId moduleId,
                               NamedFixture spec) {
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), compiled.checkedProject(), compiled.index(),
            compiled.manifests(), compiled.surface(), compiled.identities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                compiled.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null, spec.what() + ": the production project "
            + "entry lowers the fixture with zero diagnostics: "
            + result.diagnostics());
        if (result.project() == null) {
            return null;
        }
        LoweredModuleUnit unit = result.project().modules().get(moduleId);
        check(unit != null, spec.what() + ": the fixture module '" + moduleId.path()
            + "' is part of the closure: " + result.project().modules().keySet());
        if (unit == null) {
            return null;
        }
        Optional<CompilerDiagnostic> gate = SemanticIrValidator.validate(
            result.project(), new SemanticIrValidator.ComparisonFacts(
                unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                ReleaseConfiguration.releaseCapabilityRegistry()
                    .capabilityRegistryHash()));
        check(gate.isEmpty(), spec.what() + ": the closed schema and bindings gates "
            + "accept the produced closure: "
            + gate.map(CompilerDiagnostic::message).orElse("admission"));
        if (gate.isPresent()) {
            return null;
        }
        return new Drive(compiled, result, unit, spec);
    }

    /** The compiled source coordinate of one pinned raw coordinate. */
    private static String compiledOrigin(Drive drive, int rawLine, int rawColumn) {
        Path mirror = drive.compiled().root().resolve("corpus")
            .resolve(drive.spec().fixtureFile()).toAbsolutePath();
        return mirror + ":" + (rawLine - drive.compiled().strippedHeaderLines())
            + ":" + rawColumn;
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
    // 3. The producer rule's registrations in the produced fixture
    // =========================================================================

    private static List<SemanticOp> opsOfKind(LoweredModuleUnit unit,
                                              SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit,
                                                      ValueId identity) {
        return unit.functionBindings().get(
            new FunctionAllocationIdentity(identity.id()));
    }

    private static ValueId resultIdentity(SemanticOp op) {
        return op.result() instanceof ValueId value ? value : null;
    }

    /**
     * The function-typed materializations the closed producer rule registers as
     * {@code DynamicFunctionValue} in the fixture module (one per
     * runtime-resolved producing op).
     */
    private static List<SemanticOp> dynamicMaterializations(LoweredModuleUnit unit) {
        // One entry per registered identity: an identity-preserving load
        // republishes the producing op's identity (the same registration, never
        // a second one), so the materializations are counted by identity.
        java.util.Set<ValueId> seen = new java.util.LinkedHashSet<>();
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ValueId identity = resultIdentity(op);
            if (identity == null
                    || !(op.resultType() instanceof RuntimeDescriptor.Func)) {
                continue;
            }
            if (bindingOf(unit, identity)
                    instanceof FunctionExecutionBinding.DynamicFunctionValue
                    && seen.add(identity)) {
                found.add(op);
            }
        }
        return found;
    }

    private static void assertDynamicProducer(LoweredModuleUnit unit,
                                              SemanticOpKind producingKind,
                                              String what) {
        List<SemanticOp> dynamics = dynamicMaterializations(unit);
        checkEq(1, dynamics.size(), what + ": exactly one DynamicFunctionValue "
            + "registration in the fixture module");
        if (dynamics.size() != 1) {
            return;
        }
        SemanticOp producing = dynamics.get(0);
        checkEq(producingKind, producing.kind(), what + ": the producing op's kind");
        FunctionExecutionBinding binding = bindingOf(unit, resultIdentity(producing));
        check(binding instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic
                && dynamic.materializingOpId().equals(producing.opId())
                && dynamic.descriptor().equals(producing.resultType()),
            what + ": the registration is keyed by the producing op's result "
                + "identity with its own descriptor and materializing op: " + binding);
    }

    private static void assertIntrinsicSeeds(LoweredModuleUnit unit, String what) {
        Map<IntrinsicKind, FunctionExecutionBinding.IntrinsicFunction> seeds =
            new LinkedHashMap<>();
        Set<ValueId> seedIdentities = new java.util.HashSet<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue()
                    instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic) {
                check(seeds.put(intrinsic.kind(), intrinsic) == null, what
                    + ": exactly one IntrinsicFunction registration per kind");
                seedIdentities.add(new ValueId(entry.getKey().id()));
            }
        }
        checkEq(2, seeds.size(), what + ": the two conversion intrinsics register "
            + "exactly once each");
        for (IntrinsicKind kind : List.of(IntrinsicKind.INT_CONVERT,
                IntrinsicKind.NUMBER_CONVERT)) {
            FunctionExecutionBinding.IntrinsicFunction seed = seeds.get(kind);
            check(seed != null && seed.descriptor().equals(kind.declaredSignature()),
                what + ": the '" + kind + "' seed carries its declared signature: "
                    + seed);
        }
        for (SemanticOp op : dynamicMaterializations(unit)) {
            check(!seedIdentities.contains(resultIdentity(op)), what + ": the "
                + "seeded intrinsic identities are never re-registered as "
                + "DynamicFunctionValue: " + op.opId());
        }
    }

    // =========================================================================
    // 4. The three-consumer drives
    // =========================================================================

    private static void driveFixture(NamedFixture spec) throws Exception {
        Compiled compiled = compileFixture(spec);
        if (compiled == null) {
            return;
        }
        try {
            ModuleId fixtureModule = new ModuleId(
                "corpus." + BACKEND_RUNTIME.replace('/', '.') + "."
                    + spec.relativePath().replace('/', '.'));
            Drive drive = lower(compiled, fixtureModule, spec);
            if (drive == null) {
                return;
            }
            routeRegistrationAssertions(drive);
            if (spec.runtimeOk()) {
                driveRuntimeOk(drive);
            } else {
                driveFailureRow(drive);
            }
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    private static void routeRegistrationAssertions(Drive drive) {
        NamedFixture spec = drive.spec();
        switch (spec.relativePath()) {
            case "type-system/dynamic-nonfunction-to-function-e8001",
                 "descriptors/canonical-sig-mismatch-e8010" ->
                assertDynamicProducer(drive.unit(), SemanticOpKind.MEMBER_READ,
                    spec.what());
            case "closures/closure-returned-from-module" ->
                assertDynamicProducer(drive.unit(), SemanticOpKind.CALL, spec.what());
            default -> assertIntrinsicSeeds(drive.unit(), spec.what());
        }
    }

    /** The three-consumer differential verdict of one drive. */
    private static SemanticDifferentialHarness.Verdict runMatrix(Drive drive,
            SemanticDifferentialHarness.Expectation expectation) throws Exception {
        Path workspace = Files.createTempDirectory("named-fixture-matrix");
        try {
            return SemanticDifferentialHarness.runProject(drive.project(),
                drive.tables(), drive.registries(), expectation, workspace);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static int eventCount(SemanticRuntimeModel.ConsumerRun run, OpId op,
                                  SemanticRuntimeModel.Phase phase) {
        int count = 0;
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op) && event.phase() == phase) {
                count++;
            }
        }
        return count;
    }

    private static SemanticRuntimeModel.TraceEvent failureEvent(
            SemanticRuntimeModel.ConsumerRun run, OpId op) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op)
                    && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                return event;
            }
        }
        return null;
    }

    // -- 4a. the two failure rows ---------------------------------------------

    private static void driveFailureRow(Drive drive) throws Exception {
        NamedFixture spec = drive.spec();
        // The declaration crossing is a free boundary: unparented, and the only
        // FAILURE terminal the run emits at the annotation's span.
        int declarationLine = spec.pinnedLine()
            - drive.compiled().strippedHeaderLines();
        SemanticOp declaration = null;
        for (SemanticOp op : opsOfKind(drive.unit(), SemanticOpKind.BOUNDARY)) {
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) op.payload();
            if (payload.kind() == BoundaryKind.VARIABLE_DECLARATION
                    && op.origin().parentOpId() == null
                    && op.origin().span() != null
                    && op.origin().span().startLine() == declarationLine
                    && op.origin().span().startColumn() == spec.pinnedColumn()) {
                check(declaration == null, spec.what() + ": exactly one free "
                    + "declaration boundary sits at the annotation's span");
                declaration = op;
            }
        }
        check(declaration != null, spec.what() + ": the free declaration boundary "
            + "carries the declared annotation's span as its origin");
        if (declaration == null) {
            return;
        }
        String expectedOrigin = compiledOrigin(drive, spec.pinnedLine(),
            spec.pinnedColumn());
        checkEq(expectedOrigin, originText(declaration), spec.what() + ": the free "
            + "declaration boundary's origin is the annotation's span");

        SemanticDifferentialHarness.Verdict verdict = runMatrix(drive,
            SemanticDifferentialHarness.Expectation.failure(spec.what(), List.of(),
                spec.pinnedCode(), expectedOrigin));
        checkEq(3, verdict.runs().size(), spec.what() + ": the drive produced the "
            + "three consumers: " + verdict.failures());
        check(verdict.pass(), spec.what() + ": the three-consumer differential "
            + "verdict passes (the pinned row at the annotation's span, the traces "
            + "event-for-event): " + verdict.failures());

        String expectedMessage = sharedMessage(spec);
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            checkEq(1, eventCount(run, declaration.opId(),
                SemanticRuntimeModel.Phase.FAILURE), run.consumer() + ": exactly one "
                + "FAILURE terminal for the free declaration boundary");
            SemanticRuntimeModel.TraceEvent failure =
                failureEvent(run, declaration.opId());
            check(failure != null && failure.error() != null
                    && spec.pinnedCode().equals(failure.error().code())
                    && expectedOrigin.equals(failure.error().origin())
                    && expectedMessage.equals(failure.error().message())
                    && sharedExpected(spec).equals(failure.error().expected())
                    && sharedActual(spec).equals(failure.error().actual()),
                run.consumer() + ": the boundary row is the pinned function row at "
                    + "the annotation's span: " + failure);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure
                    terminal && spec.pinnedCode().equals(terminal.error().code())
                    && expectedOrigin.equals(terminal.error().origin())
                    && expectedMessage.equals(terminal.error().message())
                    && sharedExpected(spec).equals(terminal.error().expected())
                    && sharedActual(spec).equals(terminal.error().actual()),
                run.consumer() + ": the terminal is the pinned row at the "
                    + "annotation's span: " + run.terminal());
        }

        // The production artifacts under the real toolchains.
        String expectedOutcome = "ERR:" + spec.pinnedCode() + "|" + expectedMessage
            + "|" + expectedOrigin + "|" + sharedExpected(spec) + "|"
            + sharedActual(spec);
        ArtifactRun lua = luaProduction(drive);
        checkEq(expectedOutcome, lua.outcome(), spec.what() + ": the LuaJIT "
            + "production artifact projects the pinned row at the annotation's span");
        checkEq("DEAL_ERROR_CODE: " + spec.pinnedCode(), lua.terminalLine(),
            spec.what() + ": the LuaJIT production artifact's pinned terminal line");
        ArtifactRun jvm = jvmProduction(drive);
        checkEq(expectedOutcome, jvm.outcome(), spec.what() + ": the JVM production "
            + "artifact projects the pinned row at the annotation's span");
        checkEq("DEAL_ERROR_CODE: " + spec.pinnedCode(), jvm.terminalLine(),
            spec.what() + ": the JVM production artifact's pinned terminal line");

        // Message parity: the drive asserts the shared producers against the
        // pinned texts; the sidecar's legacy tail / actual-kind token (the
        // retained route's type() classification) is the lane cutover's
        // (ISSUE-0628), never re-pinned here.
        check(expectedMessage.startsWith(spec.pinnedMessage()), spec.what()
            + ": the shared row keeps the pinned message stem: " + expectedMessage);
        if ("E8001".equals(spec.pinnedCode())) {
            checkEq("expected function, got int", expectedMessage, spec.what()
                + ": the shared classification carries the legacy tail the lane "
                + "cutover re-pins");
            checkEq("number", spec.pinnedActual(), spec.what() + ": the sidecar "
                + "keeps its legacy actual-kind token (the lane cutover's)");
        } else {
            checkEq(spec.pinnedMessage(), expectedMessage, spec.what() + ": the "
                + "shared row equals the pinned message exactly (the two canonical "
                + "signature texts)");
        }
    }

    /**
     * The shared function row's message of one fixture: the E8001 row carries
     * the shared actual-kind classification (the integral carrier is
     * {@code int}); the E8010 row carries the two canonical signature texts
     * (the pinned corpus texts).
     */
    private static String sharedMessage(NamedFixture spec) {
        return "E8001".equals(spec.pinnedCode())
            ? "expected function, got int"
            : spec.pinnedMessage();
    }

    private static String sharedExpected(NamedFixture spec) {
        return spec.pinnedExpected();
    }

    private static String sharedActual(NamedFixture spec) {
        return "E8001".equals(spec.pinnedCode()) ? "int" : spec.pinnedActual();
    }

    private static String originText(SemanticOp op) {
        if (op.origin().span() == null) {
            return "-";
        }
        return op.origin().sourceId() + ":" + op.origin().span().startLine() + ":"
            + op.origin().span().startColumn();
    }

    // -- 4b. the runtime-ok fixtures ------------------------------------------

    private static void driveRuntimeOk(Drive drive) throws Exception {
        NamedFixture spec = drive.spec();
        List<String> effects = switch (spec.relativePath()) {
            case "functions/js-reference-program" -> List.of(CONSOLE_EFFECT);
            default -> List.of();
        };
        SemanticDifferentialHarness.Verdict verdict = runMatrix(drive,
            SemanticDifferentialHarness.Expectation.success(spec.what(), effects,
                "null"));
        checkEq(3, verdict.runs().size(), spec.what() + ": the drive produced the "
            + "three consumers: " + verdict.failures());
        check(verdict.pass(), spec.what() + ": the three-consumer differential "
            + "verdict passes: " + verdict.failures());
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success
                    success && "null".equals(success.resultAtom()),
                run.consumer() + ": the drive's entry succeeds: " + run.terminal());
        }
        switch (spec.relativePath()) {
            case "closures/closure-returned-from-module" ->
                assertReturnedClosureExecution(drive, verdict);
            case "functions/intrinsic-as-function-value",
                 "functions/intrinsic-as-callback",
                 "functions/intrinsic-arity-extension" ->
                assertIntrinsicExecution(drive, verdict);
            case "functions/js-reference-program" ->
                assertReferenceProgramExecution(drive, verdict);
            default -> { }
        }
        // The production artifacts under the real toolchains run the fixture's
        // own pinned-outcome check.
        ArtifactRun lua = luaProduction(drive);
        checkEq("OK", lua.outcome(), spec.what() + ": the LuaJIT production "
            + "artifact runs the fixture to its pinned outcome");
        ArtifactRun jvm = jvmProduction(drive);
        checkEq("OK", jvm.outcome(), spec.what() + ": the JVM production artifact "
            + "runs the fixture to its pinned outcome");
        if ("functions/js-reference-program".equals(spec.relativePath())) {
            check(lua.stdout().contains(CONSOLE_EFFECT), spec.what() + ": the LuaJIT "
                + "production artifact's console effect is on stdout: " + lua.stdout());
            check(jvm.stdout().contains(CONSOLE_EFFECT), spec.what() + ": the JVM "
                + "production artifact's console effect is on stdout: " + jvm.stdout());
        }
    }

    /**
     * The returned-closure anchor: the dynamic call resolves a
     * {@code DynamicFunctionValue} callee to the lib module's body class, the
     * body's own {@code RETURN} runs the body-local cell, and the invocation
     * site runs the recorded call-owned cell exactly once (the K12 form).
     */
    private static void assertReturnedClosureExecution(
            Drive drive, SemanticDifferentialHarness.Verdict verdict) {
        NamedFixture spec = drive.spec();
        SemanticOp dynamicCall = null;
        for (SemanticOp op : opsOfKind(drive.unit(), SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Dynamic) {
                dynamicCall = op;
            }
        }
        check(dynamicCall != null, spec.what() + ": the fixture produces the "
            + "dynamic (runtime-resolved) invocation");
        if (dynamicCall == null) {
            return;
        }
        KindPayload.CallPayload payload =
            (KindPayload.CallPayload) dynamicCall.payload();
        KindPayload.DynamicReturnBoundary cells = payload.dynamicReturnBoundary();
        check(cells != null && cells.dealBodyBoundaryOpId() != null, spec.what()
            + ": the dynamic call records its DEAL-body cell");
        if (cells == null || cells.dealBodyBoundaryOpId() == null) {
            return;
        }
        OpId recordedCell = cells.dealBodyBoundaryOpId();
        SemanticOp cell = opById(drive.project(), recordedCell);
        check(cell != null
                && cell.payload() instanceof KindPayload.BoundaryPayload boundary
                && boundary.kind() == BoundaryKind.FUNCTION_RETURN,
            spec.what() + ": the recorded DEAL-body cell is a FUNCTION_RETURN");
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            checkEq(1, eventCount(run, dynamicCall.opId(),
                SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the "
                + "resolved class path executed exactly once");
            checkEq(1, eventCount(run, recordedCell,
                SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the recorded "
                + "call-owned cell executed exactly once per invocation");
        }
    }

    private static SemanticOp opById(ExecutableLoweredProject project, OpId opId) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(opId)) {
                    return op;
                }
            }
        }
        return null;
    }

    /**
     * The intrinsic value class path: the fixture's intrinsic invocation
     * resolves the seeded identity's own registration (the static indirect arm,
     * the intrinsic into a function-typed parameter, or the adapter-over-
     * intrinsic arity extension) and runs the closed conversion ladder exactly
     * once.
     */
    private static void assertIntrinsicExecution(
            Drive drive, SemanticDifferentialHarness.Verdict verdict) {
        NamedFixture spec = drive.spec();
        List<SemanticOp> calls = new ArrayList<>();
        for (SemanticOp op : opsOfKind(drive.unit(), SemanticOpKind.CALL)) {
            calls.add(op);
        }
        check(!calls.isEmpty(), spec.what() + ": the fixture produces its calls");
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            for (SemanticOp call : calls) {
                checkEq(1, eventCount(run, call.opId(),
                    SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the "
                    + "call " + call.opId() + " executed its class path exactly once");
            }
        }
    }

    /** The reference program's conversion results and its console effect. */
    private static void assertReferenceProgramExecution(
            Drive drive, SemanticDifferentialHarness.Verdict verdict) {
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            checkEq(1, eventCount(run,
                callOp(drive.unit(), FunctionExecutionBinding.IntrinsicFunction.class),
                SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the typed "
                + "intrinsic value call executed its class path exactly once");
            checkEq(1, eventCount(run,
                callOp(drive.unit(), FunctionExecutionBinding.AdapterBinding.class),
                SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the "
                + "arity-extension adapter call executed its class path exactly once");
            checkEq(1, eventCount(run,
                callOp(drive.unit(), FunctionExecutionBinding.HostFunction.class),
                SemanticRuntimeModel.Phase.SUCCESS), run.consumer() + ": the "
                + "stdlib-value call executed its class path exactly once");
            check(run.effects().stream().anyMatch(
                    effect -> effect.text().contains(CONSOLE_EFFECT)),
                run.consumer() + ": the console effect is the stdlib value's own "
                    + "invocation: " + run.effects());
        }
    }

    private static OpId callOp(LoweredModuleUnit unit, Class<?> bindingShape) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.CALL
                    || !(op.payload() instanceof KindPayload.CallPayload payload)) {
                continue;
            }
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                case KindPayload.CallCallee.Indirect ignored -> null;
                case KindPayload.CallCallee.Dynamic ignored -> null;
            };
            if (binding != null && bindingShape.isInstance(binding)) {
                return op.opId();
            }
        }
        return null;
    }

    // =========================================================================
    // 5. The production artifact runners (the real toolchains)
    // =========================================================================

    /**
     * One production artifact run: the outcome framing the probe prints
     * ({@code OK}, or {@code ERR:code|message|origin|expected|actual}), the
     * artifact's own stdout, and the artifact's retained
     * {@code DEAL_ERROR_CODE} terminal line (empty for a successful run).
     */
    private record ArtifactRun(String outcome, String stdout, String terminalLine) {
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    /**
     * The LuaJIT production artifact of one drive under the real {@code luajit}:
     * the deferred-entry probe's outcome framing, the artifact's stdout, and the
     * artifact's retained terminal line of a direct run (a failing drive exits 1
     * with its {@code DEAL_ERROR_CODE} line).
     */
    private static ArtifactRun luaProduction(Drive drive) throws Exception {
        Path workspace = Files.createTempDirectory("named-fixture-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                drive.project(), drive.tables(), drive.registries(),
                drive.compiled().surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                local chunk = dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                      .. tostring(err.o) .. "|" .. tostring(err.e) .. "|"
                      .. tostring(err.a))
                  else
                    print("ERR:" .. tostring(err))
                  end
                  os.exit(0)
                end
                print("OK")
                """.formatted(artifact.toAbsolutePath().toString()),
                StandardCharsets.UTF_8);
            String stdout = runLua(workspace, probe, true);
            String outcome = stdout.lines()
                .filter(line -> line.startsWith("ERR:") || line.equals("OK"))
                .reduce((first, second) -> second).orElse("");
            check(!outcome.isEmpty(), drive.spec().what() + " (luajit): the "
                + "production artifact publishes its outcome: " + stdout);
            String terminalLine = "";
            if (!drive.spec().runtimeOk()) {
                terminalLine = runLua(workspace, artifact, false).strip();
            }
            return new ArtifactRun(outcome, stdout, terminalLine);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static String runLua(Path workspace, Path script, boolean deferMain)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder("luajit",
            script.toAbsolutePath().toString());
        builder.directory(workspace.toFile());
        if (deferMain) {
            builder.environment().put("DEAL_DEFER_MAIN", "1");
        }
        Path stderrFile = Files.createTempFile(workspace, "stderr", ".txt");
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        check(deferMain ? exit == 0 : exit == 1,
            "the luajit run of " + script.getFileName() + " exits "
                + (deferMain ? 0 : 1) + ": stdout=" + stdout + " stderr="
                + Files.readString(stderrFile, StandardCharsets.UTF_8));
        return stdout;
    }

    private static void deployRuntime(Path workspace) throws Exception {
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(Path.of("deal", "runtime.lua"), runtimeTarget);
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

    /**
     * The JVM production artifact of one drive under {@code javac --release 25
     * -proc:none} plus {@code java}.
     */
    private static ArtifactRun jvmProduction(Drive drive) throws Exception {
        Path workspace = Files.createTempDirectory("named-fixture-jvm");
        try {
            String className = JvmBackend.classNameFor(drive.project().entryModule()
                .path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(drive.project(),
                    drive.tables(), drive.registries(), className,
                    drive.compiled().surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("Probe.java"), """
                final class Probe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin + "|" + error.expected + "|"
                          + error.actual);
                      return;
                    }
                    System.out.println("OK");
                  }
                }
                """.formatted(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "Probe.java");
            javac.directory(workspace.toFile());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            checkEq(0, compileExit, drive.spec().what() + ": the JVM production "
                + "artifact compiles (javac --release 25 -proc:none): " + compileOut);
            if (compileExit != 0) {
                return new ArtifactRun("", "", "");
            }
            String stdout = runJava(classpath, classes, "Probe",
                drive.spec().runtimeOk() ? 0 : 0);
            String outcome = stdout.lines()
                .filter(line -> line.startsWith("ERR:") || line.equals("OK"))
                .reduce((first, second) -> second).orElse("");
            check(!outcome.isEmpty(), drive.spec().what() + " (java): the "
                + "production artifact publishes its outcome: " + stdout);
            String terminalLine = "";
            if (!drive.spec().runtimeOk()) {
                terminalLine = runJava(classpath, classes, className, 1).strip();
            }
            return new ArtifactRun(outcome, stdout, terminalLine);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static String runJava(String classpath, Path classes, String mainClass,
                                  int expectedExit) throws Exception {
        ProcessBuilder builder = new ProcessBuilder("java", "-cp",
            classpath + File.pathSeparator + classes, mainClass);
        builder.directory(classes.getParent().toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        checkEq(expectedExit, exit, "the java run of " + mainClass + " exits "
            + expectedExit + ": stdout=" + stdout + " stderr=" + stderr);
        return stdout;
    }

    // =========================================================================
    // 6. The JS reference program (the intrinsic and stdlib-value forms)
    // =========================================================================

    /** The stdlib function-value program of {@code test/JsBackendTest.java}. */
    private static final String JS_REFERENCE_PROGRAM = """
        import * as console from "std/console"

        function applyInt(f: (x: number) => int, v: number): int { return f(v); }
        function applyNumber(f: (x: int) => number, v: int): number { return f(v); }

        function test(): int {
          let f: (x: number) => int = int;
          let a: int = f(3.0);
          let b: int = applyInt(int, 4.0);
          let nb: number = applyNumber(number, 7);
          let wide: (x: number, y: number) => int = int;
          let c: int = wide(9.0, 1.0);
          let g: (x: string) => null = console.log;
          g("intrinsic-console-value");
          if (a === 3 && b === 4 && nb === 7.0 && c === 9) { return 1; }
          return 0;
        }

        export function main(): null {
          let r: int = test();
          if (r !== 1) {
            throw { code: "TEST_FAIL", message: "js reference program" };
          }
          return null;
        }
        """;

    private static final String CONSOLE_EFFECT = "intrinsic-console-value";

    private static void testJsReferenceProgram() throws Exception {
        System.out.println("-- the JS reference program: the intrinsic and "
            + "stdlib-value forms on both targets and the oracle --");
        Path root = Files.createTempDirectory("js-reference-program");
        try {
            Path entry = root.resolve("app.deal");
            Files.writeString(entry, JS_REFERENCE_PROGRAM, StandardCharsets.UTF_8);
            Compiled compiled = compile(root, entry, "js reference program", 0);
            if (compiled == null) {
                return;
            }
            Drive drive = lower(compiled, new ModuleId("app"), JS_REFERENCE);
            if (drive == null) {
                return;
            }
            assertIntrinsicSeeds(drive.unit(), "js reference program");
            boolean stdlibValue = false;
            for (FunctionExecutionBinding binding : drive.unit()
                    .functionBindings().values()) {
                if (binding instanceof FunctionExecutionBinding.HostFunction host
                        && "std.console".equals(host.hostModuleId().path())
                        && "log".equals(host.exportName())) {
                    stdlibValue = true;
                }
            }
            check(stdlibValue, "js reference program: the stdlib callable "
                + "materializes as a function-typed value (the read's HostFunction "
                + "registration)");
            boolean adapter = false;
            for (SemanticOp op : drive.unit().ops()) {
                if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                    adapter = true;
                }
            }
            check(adapter, "js reference program: the arity extension materializes "
                + "as one adapter over the intrinsic");
            driveRuntimeOk(drive);
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Named Fixture and Origin Battery Tests "
            + "(ISSUE-0683) ===\n");

        testCorpusPins();
        System.out.println();
        for (NamedFixture fixture : NAMED) {
            System.out.println("-- " + fixture.relativePath() + " --");
            driveFixture(fixture);
            System.out.println();
        }
        testJsReferenceProgram();

        System.out.println("\nNamed fixture battery: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
