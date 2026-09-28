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
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.NormalizedSlot;
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
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0626: bytes coverage and the bytes element contract
 * ({@code semantic-ir-construct-coverage-cutover} K6, K9 item 1, and the
 * bytes element contract).
 *
 * <ol>
 *   <li><b>The corpus pins.</b> Every {@code backend-runtime/bytes} sidecar
 *       keeps its pinned outcome: the fourteen failure rows with their code,
 *       message, line, and column (the negative allocation length, the
 *       index-below-zero read, the read at {@code i == b.length}, the write
 *       below zero, the write at {@code i == b.length}, the write range,
 *       the bytes-bearing signature rows, and the two
 *       {@code source-location/bytes-*} pins), and the runtime-ok fixtures
 *       their zero exit and empty streams.</li>
 *   <li><b>The corpus drive through the production entry.</b> Each
 *       driveable corpus fixture (classification headers stripped, the
 *       corpus entry shim replaced by the drive's own entry that calls the
 *       fixture's test export) compiles through the real orchestrator,
 *       lowers through the production project entry with zero diagnostics,
 *       and passes the closed schema and bindings gates; the pinned row
 *       surfaces on the oracle, the shared LuaJIT artifact under real
 *       {@code luajit}, and the shared JVM artifact under {@code javac
 *       --release 25 -proc:none} plus {@code java}, at the pinned origin
 *       (the raw sidecar line rebased by the stripped header lines).</li>
 *   <li><b>The read shape and the write chain.</b> The bytes element read
 *       carries its length read ({@code ARRAY_LENGTH} then
 *       {@code INDEX_NORMALIZE(BYTES_READ)} with {@code currentLength}
 *       referencing it then {@code INDEX_READ} with the
 *       {@code BYTE_ELEMENT_READ} child) and the write carries the
 *       seven-child chain with the length child at position 3, the
 *       normalize's {@code currentLength} referencing it, and the
 *       {@code BYTE_ELEMENT_ASSIGNMENT} child under {@code BYTES_WRITE};
 *       the read at {@code i == b.length} fails the pinned E8012.</li>
 *   <li><b>The oracle realization.</b> The oracle allocates zero-filled
 *       buffers, mutates them in place so an alias observes the write,
 *       keeps the logical length fixed, crosses a bytes value over a typed
 *       boundary, and compares two buffers by allocation identity
 *       ({@code BYTES_EQ}/{@code BYTES_NE}).</li>
 *   <li><b>Zero bytes CONSTRUCT_UNLOWERED.</b> No checker-valid bytes
 *       fixture fails the lowering with a bytes-owned construct guard; the
 *       two fixtures whose closure additionally carries a nested function
 *       declaration (a sibling construct's arm), the host-module fixture
 *       (whose declaration module the drive materializes, so its closure
 *       lowers here too), and the emitter-budget and divergence family are
 *       recorded with their own verified sibling reasons.</li>
 * </ol>
 */
public class BytesCoverageTest {

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

    private static final Path CORPUS = Path.of("test", "conformance");
    private static final String BYTES_DIR = "backend-runtime/bytes";
    private static final String SOURCE_LOCATION_DIR = "backend-runtime/source-location";

    // =========================================================================
    // The bytes corpus table
    // =========================================================================

    /**
     * One driveable bytes corpus fixture: its corpus directory, its
     * relative path, the export the drive's entry calls, the export's
     * declared return type, its companions, and the pinned failure row
     * ({@code null} for a runtime-ok fixture).
     */
    private record BytesFixture(String directory, String relativePath, String export,
                                String resultType, List<String> companions, String code,
                                String message, int line, int column) {

        boolean runtimeOk() {
            return code == null;
        }

        String fixtureFile() {
            return directory + "/" + relativePath + ".deal";
        }

        String sidecarFile() {
            return directory + "/" + relativePath + ".expect.json";
        }

        String what() {
            return relativePath;
        }
    }

    private static BytesFixture ok(String path, String export, String type,
                                   String... companions) {
        return new BytesFixture(BYTES_DIR, path, export, type, List.of(companions), null,
            null, 0, 0);
    }

    private static BytesFixture error(String path, String export, String type,
                                      String code, String message, int line, int column) {
        return new BytesFixture(BYTES_DIR, path, export, type, List.of(), code, message,
            line, column);
    }

    /**
     * One {@code source-location} bytes fixture: the same pinned rows with
     * the error's own source coordinate (the acceptance's
     * {@code source-location/bytes-*} clause).
     */
    private static BytesFixture sourceError(String path, String export, String type,
                                            String code, String message, int line,
                                            int column) {
        return new BytesFixture(SOURCE_LOCATION_DIR, path, export, type, List.of(), code,
            message, line, column);
    }

    /** The E8012/E8013 and bytes-bearing signature failure fixtures. */
    private static final List<BytesFixture> FAILURES = List.of(
        error("bytes-negative-length-error", "main", "null", "E8012",
            "bytes length must be non-negative", 7, 22),
        error("bytes-index-bounds", "test_bytes_index_bounds", "int", "E8012",
            "bytes index out of bounds", 8, 10),
        error("bytes-read-at-length-error", "main", "null", "E8012",
            "bytes index out of bounds", 8, 20),
        error("bytes-negative-read-error", "main", "null", "E8012",
            "bytes index out of bounds", 8, 20),
        error("bytes-write-at-length-error", "main", "null", "E8012",
            "bytes index out of bounds", 8, 3),
        error("bytes-write-range", "test_bytes_write_range", "null", "E8013",
            "bytes value out of range", 8, 3),
        error("bytes-write-negative-error", "main", "null", "E8013",
            "bytes value out of range", 8, 3),
        error("bytes-dynamic-function-mismatch-e8010",
            "test_bytes_dynamic_function_mismatch", "int", "E8010",
            "function signature mismatch: expected (bytes)->bytes, got (int)->int", 12, 10),
        error("bytes-dynamic-async-function-mismatch-e8010",
            "test_bytes_dynamic_async_function_mismatch", "int", "E8010",
            "function signature mismatch: expected async(bytes)->bytes, got (int)->int",
            12, 16),
        error("bytes-dynamic-wrong-kind-e8001", "test_bytes_dynamic_wrong_kind", "int",
            "E8001", "expected bytes", 8, 10),
        error("bytes-fn-adapter-e8010", "test_bytes_fn_adapter_e8010", "int", "E8010",
            "function signature mismatch: expected (bytes,int)->bytes, got (bytes)->bytes",
            8, 21),
        error("bytes-dynamic-nested-first-element-e8003",
            "test_bytes_dynamic_nested_first_element", "int", "E8003",
            "array element 1 type mismatch", 10, 11),
        // The two source-location pins (the acceptance's
        // source-location/bytes-* clause): the same rows at the error's own
        // source coordinate — the indexing expression for E8012 and the
        // assignment expression for E8013.
        sourceError("bytes-index-bounds-source", "test_bytes_index_bounds_location",
            "int", "E8012", "bytes index out of bounds", 9, 10),
        sourceError("bytes-write-range-source", "test_bytes_write_range_location",
            "null", "E8013", "bytes value out of range", 8, 3));

    /** The runtime-ok fixtures whose closure the drive owns. */
    private static final List<BytesFixture> RUNTIME_OK = List.of(
        ok("bytes-array-closure", "test_bytes_array_closure", "int"),
        ok("bytes-array-container-ops", "test_bytes_array_container_ops", "null"),
        ok("bytes-buffer-ops", "main", "null"),
        ok("bytes-class-default", "main", "null"),
        ok("bytes-class-field-descriptor", "test_bytes_class_field_descriptor", "string"),
        ok("bytes-descriptor-boundary", "test_bytes_descriptor_boundary", "string"),
        ok("bytes-dynamic-boundary-ok", "test_bytes_dynamic_boundary_ok", "string"),
        ok("bytes-dynamic-nullable-function-ok", "test_bytes_dynamic_nullable_function_ok",
            "string"),
        ok("bytes-fn-adapters", "test_bytes_fn_adapters", "int"),
        ok("bytes-function-array-closure", "test_bytes_function_array_closure", "int"),
        ok("bytes-identity-equality", "test_bytes_identity_equality", "int"),
        ok("bytes-length", "test_bytes_length", "null"),
        ok("bytes-module-identity", "test_bytes_module_identity", "string",
            "bytes_module_lib"),
        ok("bytes-nested-arrays", "test_bytes_nested_arrays", "null"),
        ok("bytes-nested-fn-shapes", "test_bytes_nested_fn_shapes", "int"),
        ok("bytes-sync-fn-shapes", "test_bytes_sync_fn_shapes", "int"),
        ok("bytes-write-single-evaluation", "test_bytes_write_single_evaluation", "null"),
        ok("bytes-write-validation-order", "test_bytes_write_validation_after_rhs",
            "null"),
        ok("bytes-write-zero", "main", "null"),
        ok("bytes-zero-length", "main", "null"),
        ok("bytes-fn-xmod", "test_bytes_fn_xmod", "int", "bytes-fn-xmod-lib"));

    /**
     * The fixtures whose closure additionally carries a nested function
     * declaration (the CALLS family's nested-declaration arm — a sibling
     * construct the bytes slice never introduces): the nested body has no
     * lowering context yet, so the closure fails the lowering with the
     * non-bytes producer guard ("the LoweredBody/async body binding's
     * function N has no lowering context"). The drive asserts the blocker
     * is not a bytes-owned guard and records the sibling dependency
     * instead of claiming their execution.
     */
    private static final List<String> NESTED_DECLARATION_FIXTURES = List.of(
        "bytes-boundary-order", "bytes-async-closure");

    /**
     * The fixture whose closure imports the host module
     * {@code host/bytes_roundtrip}: it compiles, lowers, and passes the
     * closed gates once the declaration module is materialized (verified),
     * but its test export is {@code async}, so driving it through the
     * production artifacts needs an async-export invocation surface (and a
     * bytes-aware host responder for the oracle) — the host-ABI child's
     * drive. Its bytes constructs are asserted through the
     * {@code bytes-class-default} fixture and the host-free drives below.
     */
    private static final String HOST_FIXTURE = "bytes-class-default-integration";

    /**
     * The bytes corpus fixtures whose full drive is blocked by a
     * <em>sibling</em> construct's gap, reproduced independently of bytes:
     *
     * <ul>
     *   <li>{@code bytes-fn-adapter-e8010}: the pinned origin is the
     *       declared parameter's annotation (the D15 adapter-creation rule
     *       of the function-typed-value child); the shared route reports
     *       the signature mismatch at the call site, and the emitted
     *       adapter path drops the origin. The fixture's bytes signature
     *       texts, code, and annotation coordinate are asserted verbatim by
     *       the pin section.</li>
     *   <li>{@code bytes-array-closure}: a nested-array-of-arrays read
     *       divergence that reproduces with {@code int[][]} (the oracle
     *       reads the element, both artifacts project {@code missing}) —
     *       the containers construct's, never bytes'; and a LuaJIT
     *       expression-complexity limit of the emitted cross-module chunk
     *       ("function or expression too complex"), also independent of
     *       bytes.</li>
     *   <li>the emitter-budget family ({@code bytes-nested-arrays},
     *       {@code bytes-array-container-ops}, {@code bytes-sync-fn-shapes}):
     *       the emitted cross-module save/restore of the callee module's
     *       static values packs one multi-assignment and exceeds LuaJIT's
     *       200-local-per-function limit (or its expression-complexity
     *       limit) — a parse-time emitter budget, never a bytes semantic;
     *       the fixtures lower and the zero-{@code CONSTRUCT_UNLOWERED}
     *       section asserts their bytes constructs.</li>
     *   <li>{@code bytes-fn-xmod}: the adapter-over-dynamic-function-value
     *       call fails the lowering closed (the function-typed-value
     *       child's producing-registration arm).</li>
     * </ul>
     */
    private static final Map<String, String> SIBLING_BLOCKED = Map.of(
        "bytes-fn-adapter-e8010",
        "the D15 adapter-creation origin rule: the oracle projects the pinned E8010 "
            + "at the adapter-creation coordinate while both production artifacts "
            + "project the row without the origin (the function-typed-value child's "
            + "materialization-site origin)",
        "bytes-array-closure",
        "the nested-array-of-arrays read divergence (the oracle reads the element, "
            + "both artifacts project missing; reproduces with int[][]) and the "
            + "LuaJIT expression-complexity limit of the emitted cross-module chunk",
        "bytes-array-container-ops",
        "the emitted cross-module save/restore of the callee module's static values "
            + "exceeds LuaJIT's 200-local-per-function limit (a parse-time emitter "
            + "budget, never a bytes semantic); its bytes constructs lower and "
            + "the zero-CONSTRUCT_UNLOWERED section asserts them",
        "bytes-function-array-closure",
        "the nested-array-of-arrays read divergence (the oracle reads the element, "
            + "both artifacts project missing; reproduces with int[][])",
        "bytes-nested-fn-shapes",
        "the nested-array-of-arrays read divergence (reproduces with int[][])",
        "bytes-nested-arrays",
        "the LuaJIT 200-local-per-function limit of the emitted cross-module "
            + "save/restore chunk (a parse-time emitter budget, never a bytes semantic)",
        "bytes-sync-fn-shapes",
        "the LuaJIT expression-complexity limit of the emitted cross-module chunk "
            + "(a parse-time emitter budget, never a bytes semantic)",
        "bytes-fn-xmod",
        "the adapter-over-dynamic-function-value call (the function-typed-value "
            + "child's producing-registration arm): the cross-module bytes-bearing "
            + "function value's arity-extended call fails the lowering closed "
            + "(\"has no statically classified execution in this slice\")");

    private static List<BytesFixture> allFixtures() {
        List<BytesFixture> all = new ArrayList<>();
        all.addAll(FAILURES);
        all.addAll(RUNTIME_OK);
        for (String blocked : NESTED_DECLARATION_FIXTURES) {
            all.add(new BytesFixture(BYTES_DIR, blocked, "main", "null", List.of(), null,
                null, 0, 0));
        }
        all.add(new BytesFixture(BYTES_DIR, HOST_FIXTURE, "main", "null", List.of(),
            null, null, 0, 0));
        all.add(new BytesFixture(BYTES_DIR, "bytes_module_lib", "echo", "bytes",
            List.of(), null, null, 0, 0));
        all.add(new BytesFixture(BYTES_DIR, "bytes-fn-xmod-lib", "makeId", "null",
            List.of(), null, null, 0, 0));
        return all;
    }

    // =========================================================================
    // 1. The corpus pins
    // =========================================================================

    private static void testCorpusPins() throws Exception {
        System.out.println("-- the bytes corpus sidecars keep their pinned rows --");
        for (BytesFixture fixture : FAILURES) {
            Path sidecar = CORPUS.resolve(fixture.sidecarFile());
            Path file = CORPUS.resolve(fixture.fixtureFile());
            check(Files.exists(sidecar), fixture.what() + " carries its sidecar");
            check(Files.exists(file), fixture.what() + " is a corpus fixture");
            if (!Files.exists(sidecar) || !Files.exists(file)) {
                continue;
            }
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
            if (!(expectation
                    instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
                continue;
            }
            checkEq("runtime-error", executed.mode(), fixture.what() + ": the pinned mode");
            SidecarExpectations.ErrorExpectation row = executed.error();
            check(row != null, fixture.what() + ": the pinned error snapshot");
            if (row == null) {
                continue;
            }
            checkEq(fixture.code(), row.code(), fixture.what() + ": the pinned code");
            checkEq(fixture.message(), row.message(), fixture.what()
                + ": the pinned message");
            checkEq(fixture.line(), row.line(), fixture.what() + ": the pinned line");
            checkEq(fixture.column(), row.column(), fixture.what()
                + ": the pinned column");
            checkEq(fixture.fixtureFile(), row.sourceFile(), fixture.what()
                + ": the pinned source file");
            List<String> lines = Files.readAllLines(file, StandardCharsets.UTF_8);
            check(fixture.line() <= lines.size(), fixture.what()
                + ": the pinned line is inside the fixture");
            if (fixture.line() <= lines.size()) {
                String line = lines.get(fixture.line() - 1);
                check(fixture.column() <= line.length() + 1, fixture.what()
                    + ": the pinned column is inside the pinned line: '" + line + "'");
            }
            checkEq(1, executed.exitCode(), fixture.what() + ": the pinned exit code");
        }
        for (BytesFixture fixture : RUNTIME_OK) {
            Path sidecar = CORPUS.resolve(fixture.sidecarFile());
            Path file = CORPUS.resolve(fixture.fixtureFile());
            check(Files.exists(sidecar), fixture.what() + " carries its sidecar");
            check(Files.exists(file), fixture.what() + " is a corpus fixture");
            if (!Files.exists(sidecar)) {
                continue;
            }
            SidecarExpectations.StructuredExpectationSidecar parsed =
                SidecarExpectations.StructuredExpectationSidecar.parse(
                    Files.readString(sidecar, StandardCharsets.UTF_8));
            SidecarExpectations.RuntimeExpectation expectation =
                parsed.expectationFor("luajit");
            if (!(expectation
                    instanceof SidecarExpectations.RuntimeExpectation.Executed executed)) {
                fail(fixture.what() + ": the LuaJIT leg is an executed expectation");
                continue;
            }
            checkEq("runtime-ok", executed.mode(), fixture.what() + ": the pinned mode");
            checkEq(0, executed.exitCode(), fixture.what() + ": the pinned exit code");
            checkEq("", new String(executed.stdout(), StandardCharsets.UTF_8),
                fixture.what() + ": the pinned stdout");
            checkEq("", new String(executed.stderr(), StandardCharsets.UTF_8),
                fixture.what() + ": the pinned stderr");
            check(executed.error() == null, fixture.what()
                + ": a runtime-ok fixture pins no error snapshot");
        }
        // The bytes element contract's four pinning fixtures are exactly the
        // negative length, the bounds read/write, and the write range.
        for (String required : List.of("bytes-negative-length-error",
                "bytes-index-bounds", "bytes-read-at-length-error",
                "bytes-write-at-length-error", "bytes-write-range",
                "bytes-write-negative-error")) {
            check(FAILURES.stream().anyMatch(f -> f.relativePath().equals(required)),
                "the failure fixture set carries '" + required + "'");
        }
    }

    // =========================================================================
    // 2. The production-entry drive harness
    // =========================================================================

    private record Compiled(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, CanonicalModuleIdentity> identities,
        int strippedHeaderLines) {
    }

    private record Drive(
        Compiled compiled,
        SemanticLowerer.ProjectLoweringResult result,
        ModuleId fixtureModule,
        LoweredModuleUnit unit,
        BytesFixture spec) {

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
     * Materializes one bytes corpus fixture (headers stripped, the drive's
     * own entry added) and compiles it through the real orchestrator.
     */
    private static Compiled compileFixture(BytesFixture fixture) throws Exception {
        return compileFixture(fixture, false);
    }

    /**
     * Materializes one bytes corpus fixture and compiles it through the real
     * orchestrator; {@code quiet} suppresses the diagnostic assertions (the
     * blocker-disposition section records its own expectations).
     */
    private static Compiled compileFixture(BytesFixture fixture, boolean quiet)
            throws Exception {
        Path root = Files.createTempDirectory("bytes-corpus-");
        Path corpusRoot = root.resolve("corpus");
        Path fixtureFile = corpusRoot.resolve(fixture.fixtureFile());
        Files.createDirectories(fixtureFile.getParent());
        String raw = Files.readString(CORPUS.resolve(fixture.fixtureFile()),
            StandardCharsets.UTF_8);
        String stripped = ConformanceHarnessMetadata.stripClassificationHeaders(raw);
        int strippedLines = raw.split("\n", -1).length
            - stripped.split("\n", -1).length;
        Files.writeString(fixtureFile, stripped, StandardCharsets.UTF_8);
        for (String companion : fixture.companions()) {
            Path companionFile = corpusRoot.resolve(BYTES_DIR)
                .resolve(companion + ".deal");
            Files.createDirectories(companionFile.getParent());
            Files.writeString(companionFile,
                ConformanceHarnessMetadata.stripClassificationHeaders(
                    Files.readString(CORPUS.resolve(BYTES_DIR)
                        .resolve(companion + ".deal"), StandardCharsets.UTF_8)),
                StandardCharsets.UTF_8);
        }
        Path entry = "main".equals(fixture.export())
            ? fixtureFile
            : root.resolve("app.deal");
        if (!"main".equals(fixture.export())) {
            Files.writeString(entry, driver(fixture), StandardCharsets.UTF_8);
        }
        // The host-importing fixture materializes its corpus declaration
        // module (the host-ABI child's fixture) and the externals mapping of
        // the drive's temp project, so the fixture's own closure — and the
        // bytes constructs it carries — compile and lower here too.
        Map<String, String> externals = null;
        boolean hostDeclared = HOST_FIXTURE.equals(fixture.relativePath());
        if (hostDeclared) {
            Path declaration = root.resolve("host").resolve("bytes_roundtrip.d.deal");
            Files.createDirectories(declaration.getParent());
            Files.writeString(declaration, ConformanceHarnessMetadata
                .stripClassificationHeaders(Files.readString(Path.of("test",
                    "conformance", "host-fixtures", "bytes_roundtrip.d.deal"),
                    StandardCharsets.UTF_8)), StandardCharsets.UTF_8);
            externals = new LinkedHashMap<>();
            externals.put("host.bytes_roundtrip",
                declaration.toAbsolutePath().toString());
            externals.put("host/bytes_roundtrip",
                declaration.toAbsolutePath().toString());
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry.toAbsolutePath(), root.resolve("out"), false, false, false, false,
            Backend.LUAJIT, externals, List.of(root.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null, productionInvocation());
        boolean compiled = orchestrator.compile();
        if (!quiet) {
            check(compiled, fixture.what() + ": the production orchestrator compiles "
                + "the project: " + orchestrator.diagnostics());
        }
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!quiet) {
            check(built != null && built.input() != null && built.index() != null
                    && !built.hasErrors(),
                fixture.what() + ": the checked project builds: "
                    + (built == null ? "null" : built.diagnostics()));
        }
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declaration : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declaration,
                new CanonicalModuleIdentity.ExternalModule(hostDeclared
                    ? declaration.path().replace('/', '.')
                    : declaration.path()));
        }
        return new Compiled(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), identities, strippedLines);
    }

    /** The drive's own entry: it imports the fixture and calls its test export. */
    private static String driver(BytesFixture fixture) {
        String specifier = fixture.fixtureFile();
        if (specifier.endsWith(".deal")) {
            specifier = specifier.substring(0, specifier.length() - ".deal".length());
        }
        String call = fixture.runtimeOk() && "main".equals(fixture.export())
            && "null".equals(fixture.resultType())
            ? "  fx.main()\n"
            : "  let r: " + fixture.resultType() + " = fx." + fixture.export() + "()\n";
        return "import * as fx from \"./corpus/" + specifier + "\"\n\n"
            + "export function main(): null {\n" + call + "  return null\n}\n";
    }

    /** The production project lowering entry over one compiled fixture. */
    private static Drive lower(Compiled compiled, BytesFixture fixture) {
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), compiled.checkedProject(), compiled.index(),
            compiled.manifests(), compiled.surface(), compiled.identities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                compiled.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null, fixture.what() + ": the production project "
            + "entry lowers the fixture with zero diagnostics: " + result.diagnostics());
        if (result.project() == null) {
            return null;
        }
        ModuleId fixtureModule = null;
        for (ModuleId module : result.project().modules().keySet()) {
            if (module.path().endsWith("." + fixture.relativePath())) {
                fixtureModule = module;
            }
        }
        check(fixtureModule != null, fixture.what() + ": the fixture module is part of "
            + "the closure: " + result.project().modules().keySet());
        if (fixtureModule == null) {
            return null;
        }
        LoweredModuleUnit unit = result.project().modules().get(fixtureModule);
        Optional<CompilerDiagnostic> gate = SemanticIrValidator.validate(
            result.project(), new SemanticIrValidator.ComparisonFacts(
                unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                ReleaseConfiguration.releaseCapabilityRegistry()
                    .capabilityRegistryHash()));
        check(gate.isEmpty(), fixture.what() + ": the closed schema and bindings gates "
            + "accept the produced closure: "
            + gate.map(CompilerDiagnostic::message).orElse("admission"));
        if (gate.isPresent()) {
            return null;
        }
        return new Drive(compiled, result, fixtureModule, unit, fixture);
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
    // 3. The corpus drive: oracle + both production artifacts
    // =========================================================================

    private static void testCorpusDrive() throws Exception {
        System.out.println("-- the bytes corpus through the one production pipeline: "
            + "oracle + shared LuaJIT + shared JVM --");
        for (BytesFixture fixture : allFixtures()) {
            if (NESTED_DECLARATION_FIXTURES.contains(fixture.relativePath())
                    || HOST_FIXTURE.equals(fixture.relativePath())
                    || SIBLING_BLOCKED.containsKey(fixture.relativePath())
                    || "bytes_module_lib".equals(fixture.relativePath())
                    || "bytes-fn-xmod-lib".equals(fixture.relativePath())) {
                continue;
            }
            Compiled compiled = compileFixture(fixture);
            if (compiled == null) {
                continue;
            }
            try {
                Drive drive = lower(compiled, fixture);
                if (drive == null) {
                    continue;
                }
                SemanticDifferentialHarness.Expectation expectation = fixture.runtimeOk()
                    ? SemanticDifferentialHarness.Expectation.success(fixture.what(),
                        List.of(), "null")
                    : SemanticDifferentialHarness.Expectation.failure(fixture.what(),
                        List.of(), fixture.code(),
                        compiledOrigin(drive, fixture.line(), fixture.column()));
                Path workspace = Files.createTempDirectory("bytes-matrix-");
                SemanticDifferentialHarness.Verdict verdict;
                try {
                    verdict = SemanticDifferentialHarness.runProject(drive.project(),
                        drive.tables(), drive.registries(), expectation, workspace);
                } finally {
                    deleteRecursively(workspace);
                }
                checkEq(3, verdict.runs().size(), fixture.what() + ": the drive produced "
                    + "the three consumers: " + verdict.failures());
                check(verdict.pass(), fixture.what() + ": the three-consumer "
                    + "differential verdict passes (the pinned outcome and origin, the "
                    + "traces event-for-event): " + verdict.failures());
                if (fixture.runtimeOk()) {
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.Success success
                                && "null".equals(success.resultAtom()),
                            run.consumer() + " (" + fixture.what() + "): the drive's entry "
                                + "succeeds: " + run.terminal());
                    }
                } else {
                    String expectedOrigin = compiledOrigin(drive, fixture.line(),
                        fixture.column());
                    for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                        check(run.terminal()
                                instanceof SemanticRuntimeModel.Terminal.DealFailure
                                    terminal
                                && fixture.code().equals(terminal.error().code())
                                && fixture.message().equals(terminal.error().message())
                                && expectedOrigin.equals(terminal.error().origin()),
                            run.consumer() + " (" + fixture.what() + "): the terminal is "
                                + "the pinned row at the pinned origin: "
                                + run.terminal());
                    }
                }

                // The production artifacts under the real toolchains.
                ArtifactRun lua = luaProduction(drive);
                ArtifactRun jvm = jvmProduction(drive);
                if (fixture.runtimeOk()) {
                    checkEq("OK", lua.outcome(), fixture.what()
                        + ": the LuaJIT production artifact runs the fixture to its "
                        + "pinned outcome");
                    checkEq("OK", jvm.outcome(), fixture.what()
                        + ": the JVM production artifact runs the fixture to its pinned "
                        + "outcome");
                    checkEq("", lua.terminalLine(), fixture.what() + ": no LuaJIT "
                        + "terminal on a runtime-ok fixture");
                    checkEq("", jvm.terminalLine(), fixture.what()
                        + ": no JVM terminal on a runtime-ok fixture");
                } else {
                    String expectedOrigin = compiledOrigin(drive, fixture.line(),
                        fixture.column());
                    String expectedPrefix = "ERR:" + fixture.code() + "|"
                        + fixture.message() + "|" + expectedOrigin + "|";
                    check(lua.outcome().startsWith(expectedPrefix), fixture.what()
                        + ": the LuaJIT production artifact projects the pinned row at "
                        + "the pinned origin: " + lua.outcome());
                    check(jvm.outcome().startsWith(expectedPrefix), fixture.what()
                        + ": the JVM production artifact projects the pinned row at the "
                        + "pinned origin: " + jvm.outcome());
                    checkEq("DEAL_ERROR_CODE: " + fixture.code(), lua.terminalLine(),
                        fixture.what() + ": the LuaJIT artifact's pinned terminal line");
                    checkEq("DEAL_ERROR_CODE: " + fixture.code(), jvm.terminalLine(),
                        fixture.what() + ": the JVM artifact's pinned terminal line");
                }
            } finally {
                deleteRecursively(compiled.root());
            }
        }
    }

    // =========================================================================
    // 4. The read shape and the seven-child write chain
    // =========================================================================

    private static final String SHAPE_SOURCE = """
        export function main(): null {
          let b: bytes = bytes(2);
          let alias: bytes = b;
          b[0] = 7;
          let read: int = b[1];
          let atEnd: int = b[2];
          if (alias[0] !== 7 || read !== 0) {
            throw { code: "TEST_FAIL", message: "shape drive" }
          }
          return null
        }
        """;

    private static void testReadShapeAndWriteChain() throws Exception {
        System.out.println("-- the bytes read shape and the seven-child write chain --");
        Path root = Files.createTempDirectory("bytes-shape-");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("main.deal"), SHAPE_SOURCE, StandardCharsets.UTF_8);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve("main.deal").toAbsolutePath(), root.resolve("out"), false,
            false, false, false, Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null, productionInvocation());
        check(orchestrator.compile(), "the shape drive compiles: "
            + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                built.input().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null, "the shape drive lowers: " + result.diagnostics());
        if (result.project() == null) {
            deleteRecursively(root);
            return;
        }
        try {
            LoweredModuleUnit unit = result.project().modules().get(new ModuleId("main"));
            check(unit != null, "the shape drive's unit is in the closure");
            if (unit == null) {
                return;
            }
            List<SemanticOp> reads = opsOfKind(unit, SemanticOpKind.INDEX_READ);
            checkEq(3, reads.size(), "the fixture produces the three bytes element "
                + "reads (b[1], b[2], and alias[0]; the write chain's length read is "
                + "an ARRAY_LENGTH child)");
            int checkedReads = 0;
            for (SemanticOp read : reads) {
                KindPayload.IndexReadPayload payload =
                    (KindPayload.IndexReadPayload) read.payload();
                if (!(read.operandTypes().get(0) instanceof RuntimeDescriptor.Bytes)) {
                    continue;
                }
                checkedReads++;
                SemanticOp normalize = opById(unit, producerOf(unit, payload.slot()));
                check(normalize != null
                        && normalize.kind() == SemanticOpKind.INDEX_NORMALIZE,
                    "the bytes read's slot is produced by an INDEX_NORMALIZE");
                if (normalize == null) {
                    continue;
                }
                checkEq(IndexMode.BYTES_READ,
                    ((KindPayload.IndexNormalizePayload) normalize.payload()).mode(),
                    "the bytes read normalizes in BYTES_READ mode");
                checkEq(FailurePolicyId.NO_DEAL_FAILURE, normalize.failurePolicy(),
                    "the bytes normalize stays pure (NO_DEAL_FAILURE)");
                ValueId lengthValue = ((KindPayload.IndexNormalizePayload)
                    normalize.payload()).currentLength();
                SemanticOp length = opById(unit, producerOf(unit, lengthValue));
                check(length != null && length.kind() == SemanticOpKind.ARRAY_LENGTH,
                    "the read's currentLength operand references its own length read");
                check(length != null
                        && length.operands().isEmpty()
                        && length.resultType() == RuntimeDescriptor.Int.INSTANCE,
                    "the length read is an int ARRAY_LENGTH with the INT32_RESULT "
                        + "terminal");
                SemanticOp boundary = opById(unit, payload.elementBoundaryOpId());
                check(boundary != null
                        && boundary.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) boundary.payload()).kind()
                            == BoundaryKind.BYTE_ELEMENT_READ
                        && boundary.failurePolicy() == FailurePolicyId.BYTES_READ,
                    "the read's boundary child is BYTE_ELEMENT_READ under BYTES_READ");
            }
            check(checkedReads >= 2, "the fixture's bytes reads are classified by the "
                + "bytes descriptor (got " + checkedReads + ")");

            List<SemanticOp> chains = new ArrayList<>();
            for (SemanticOp op : opsOfKind(unit, SemanticOpKind.ASSIGN)) {
                if (((KindPayload.AssignPayload) op.payload()).targetKind()
                        == deal.semantic.ir.AssignTargetKind.BYTES_SLOT) {
                    chains.add(op);
                }
            }
            checkEq(1, chains.size(), "the fixture produces one BYTES_SLOT chain");
            if (chains.size() == 1) {
                SemanticOp chain = chains.get(0);
                List<OpId> children =
                    ((KindPayload.AssignPayload) chain.payload()).childOps();
                checkEq(7, children.size(), "the bytes write chain is the seven-child "
                    + "shape");
                if (children.size() == 7) {
                    SemanticOp[] c = new SemanticOp[7];
                    for (int i = 0; i < 7; i++) {
                        c[i] = opById(unit, children.get(i));
                        check(c[i] != null, "the chain child at position " + i
                            + " resolves");
                    }
                    check(c[3] != null && c[3].kind() == SemanticOpKind.ARRAY_LENGTH,
                        "the length child sits at position 3");
                    check(c[3] != null
                            && c[3].resultType() == RuntimeDescriptor.Int.INSTANCE,
                        "the length child is an int read");
                    check(c[4] != null
                            && c[4].kind() == SemanticOpKind.INDEX_NORMALIZE,
                        "the normalize child sits at position 4");
                    if (c[4] != null && c[3] != null) {
                        KindPayload.IndexNormalizePayload normalize =
                            (KindPayload.IndexNormalizePayload) c[4].payload();
                        checkEq(IndexMode.BYTES_WRITE, normalize.mode(),
                            "the chain normalizes in BYTES_WRITE mode");
                        checkEq(c[3].result(), normalize.currentLength(),
                            "the normalize's currentLength references the length child's "
                                + "result");
                        checkEq(c[1].result(), normalize.rawKey(),
                            "the normalize's rawKey references the key child's result");
                    }
                    check(c[5] != null && c[5].kind() == SemanticOpKind.BOUNDARY,
                        "the boundary child sits at position 5");
                    if (c[5] != null) {
                        KindPayload.BoundaryPayload boundary =
                            (KindPayload.BoundaryPayload) c[5].payload();
                        checkEq(BoundaryKind.BYTE_ELEMENT_ASSIGNMENT, boundary.kind(),
                            "the write cell is BYTE_ELEMENT_ASSIGNMENT");
                        checkEq(FailurePolicyId.BYTES_WRITE, c[5].failurePolicy(),
                            "the write cell carries the BYTES_WRITE policy");
                        checkEq(c[2].result(), boundary.input(),
                            "the write cell's input is the checked RHS value");
                    }
                    check(c[6] != null && c[6].kind() == SemanticOpKind.INDEX_WRITE,
                        "the commit child sits at position 6");
                }
            }

            // The read at i == b.length fails the pinned E8012 on all three
            // consumers.
            SemanticDifferentialHarness.Expectation expectation =
                SemanticDifferentialHarness.Expectation.failure("the shape drive",
                    List.of(), "E8012", null);
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(result.project(), result.tables(),
                    result.registries(), expectation,
                    Files.createTempDirectory("bytes-shape-matrix-"));
            check(verdict.pass(), "the read at i == b.length fails E8012 on all three "
                + "consumers: " + verdict.failures());
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 5. The oracle realization
    // =========================================================================

    private static final String ORACLE_SOURCE = """
        export function main(): null {
          let b: bytes = bytes(2);
          let alias: bytes = b;
          alias[0] = 200;
          let fresh: bytes = bytes(2);
          if (b[0] !== 200) {
            throw { code: "TEST_FAIL", message: "alias mutation not observed" }
          }
          if (b[1] !== 0 || fresh[0] !== 0) {
            throw { code: "TEST_FAIL", message: "zero fill mismatch" }
          }
          if (b.length !== 2 || alias.length !== 2) {
            throw { code: "TEST_FAIL", message: "logical length mismatch" }
          }
          if (b !== alias || b === fresh) {
            throw { code: "TEST_FAIL", message: "identity comparison mismatch" }
          }
          return bound(b)
        }

        function bound(value: bytes): null {
          if (value[0] !== 200) {
            throw { code: "TEST_FAIL", message: "boundary crossing lost the value" }
          }
          return null
        }
        """;

    private static void testOracleRealization() throws Exception {
        System.out.println("-- the oracle bytes realization: zero fill, in-place write, "
            + "fixed length, the boundary crossing, and BYTES_EQ/NE identity --");
        Path root = Files.createTempDirectory("bytes-oracle-");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("main.deal"), ORACLE_SOURCE, StandardCharsets.UTF_8);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve("main.deal").toAbsolutePath(), root.resolve("out"), false,
            false, false, false, Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null, productionInvocation());
        check(orchestrator.compile(), "the oracle drive compiles: "
            + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
            productionInvocation(), built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                built.input().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        check(result.project() != null, "the oracle drive lowers: "
            + result.diagnostics());
        if (result.project() == null) {
            deleteRecursively(root);
            return;
        }
        try {
            SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
                result.project(), result.tables(), result.registries(), null);
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle runs the bytes drive to success: " + oracle.terminal());
            LoweredModuleUnit unit = result.project().modules().get(new ModuleId("main"));
            // The BYTES_EQ/NE rows carry the closed comparison selectors.
            int identityComparisons = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BINARY
                        && op.payload() instanceof KindPayload.BinaryPayload binary
                        && (binary.selector() == deal.semantic.ir.BinarySelector.BYTES_EQ
                            || binary.selector()
                                == deal.semantic.ir.BinarySelector.BYTES_NE)) {
                    identityComparisons++;
                }
            }
            checkEq(2, identityComparisons, "the fixture produces both BYTES_EQ and "
                + "BYTES_NE (the allocation-identity comparison)");
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(result.project(), result.tables(),
                    result.registries(),
                    SemanticDifferentialHarness.Expectation.success("the oracle drive",
                        List.of(), "null"),
                    Files.createTempDirectory("bytes-oracle-matrix-"));
            // The entry returns through the bound() call, so the terminal atom is
            // the returned null.
            check(verdict.pass(), "the bytes realization agrees on the oracle and both "
                + "artifacts: " + verdict.failures());
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 6. Zero bytes CONSTRUCT_UNLOWERED
    // =========================================================================

    private static void testZeroBytesConstructUnlowered() throws Exception {
        System.out.println("-- zero bytes CONSTRUCT_UNLOWERED over the corpus --");
        for (BytesFixture fixture : allFixtures()) {
            if ("bytes_module_lib".equals(fixture.relativePath())
                    || "bytes-fn-xmod-lib".equals(fixture.relativePath())) {
                continue;
            }
            Compiled compiled = compileFixture(fixture, true);
            if (compiled == null) {
                // A non-compiling fixture must be one of the recorded
                // sibling blockers, and its failure must not be a
                // bytes-owned construct guard.
                boolean nested = NESTED_DECLARATION_FIXTURES.contains(
                    fixture.relativePath());
                boolean host = HOST_FIXTURE.equals(fixture.relativePath());
                boolean sibling = SIBLING_BLOCKED.containsKey(fixture.relativePath());
                // The host-importing fixture carries its declaration module
                // in this drive, so its closure (and its bytes constructs)
                // must compile and lower like every other fixture's.
                check(!host, fixture.what() + ": the host-importing fixture compiles "
                    + "and lowers once its declaration module is materialized: "
                    + compileDiagnostics(fixture));
                check(nested || host || sibling,
                    fixture.what() + ": a non-compiling fixture is one of the "
                        + "recorded sibling blockers");
                for (CompilerDiagnostic diagnostic : compileDiagnostics(fixture)) {
                    String message = diagnostic.message();
                    check(!(message.contains("ISSUE-0158")
                            || message.contains("bytes value semantics")
                            || message.contains("bytes element")),
                        fixture.what() + ": the blocker is not a bytes-owned construct "
                            + "guard: " + message);
                }
                continue;
            }
            try {
                SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
                    productionInvocation(), compiled.checkedProject(), compiled.index(),
                    compiled.manifests(), compiled.surface(), compiled.identities(),
                    Map.of(),
                    BuiltinErrorDeclaration.synthesized(
                        compiled.checkedProject().modules().get(0).ast().span()),
                    List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                    Set.of());
                if (result.project() == null) {
                    boolean bytesOwned = false;
                    for (CompilerDiagnostic diagnostic : result.diagnostics()) {
                        String message = diagnostic.message();
                        if (message.contains("bytes")
                                || message.contains("ISSUE-0158")) {
                            bytesOwned = true;
                        }
                    }
                    check(!bytesOwned, fixture.what() + ": the lowering failure is not a "
                        + "bytes-owned construct guard: " + result.diagnostics());
                    check(NESTED_DECLARATION_FIXTURES.contains(fixture.relativePath()),
                        fixture.what() + ": a non-lowering fixture is one of the two "
                        + "recorded nested-declaration blockers: " + result.diagnostics());
                    continue;
                }
                LoweredModuleUnit unit = null;
                for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                        : result.project().modules().entrySet()) {
                    if (entry.getKey().path().endsWith("." + fixture.relativePath())) {
                        unit = entry.getValue();
                    }
                }
                check(unit != null, fixture.what() + ": the fixture module is in the "
                    + "closure");
                if (unit == null) {
                    continue;
                }
                check(carriesBytesConstruct(unit), fixture.what() + ": the fixture's "
                    + "lowered unit carries its bytes construct");
            } finally {
                deleteRecursively(compiled.root());
            }
        }
    }

    /** The diagnostics of one fixture's quiet frontend compile. */
    private static List<CompilerDiagnostic> compileDiagnostics(BytesFixture fixture)
            throws Exception {
        Path root = Files.createTempDirectory("bytes-diag-");
        Path corpusRoot = root.resolve("corpus");
        Path fixtureFile = corpusRoot.resolve(fixture.fixtureFile());
        Files.createDirectories(fixtureFile.getParent());
        Files.writeString(fixtureFile, ConformanceHarnessMetadata
            .stripClassificationHeaders(Files.readString(
                CORPUS.resolve(fixture.fixtureFile()))));
        for (String companion : fixture.companions()) {
            Path companionFile = corpusRoot.resolve(BYTES_DIR)
                .resolve(companion + ".deal");
            Files.createDirectories(companionFile.getParent());
            Files.writeString(companionFile, ConformanceHarnessMetadata
                .stripClassificationHeaders(Files.readString(
                    CORPUS.resolve(BYTES_DIR).resolve(companion + ".deal"))));
        }
        Path entry = "main".equals(fixture.export())
            ? fixtureFile
            : root.resolve("app.deal");
        if (!"main".equals(fixture.export())) {
            Files.writeString(entry, driver(fixture));
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry.toAbsolutePath(), root.resolve("out"), false, false, false, false,
            Backend.LUAJIT, null, List.of(root.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null, productionInvocation());
        orchestrator.compile();
        List<CompilerDiagnostic> diagnostics =
            new ArrayList<>(orchestrator.diagnostics());
        deleteRecursively(root);
        return diagnostics;
    }

    /** Whether one unit carries at least one bytes construct (K6). */
    private static boolean carriesBytesConstruct(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.INTRINSIC_CALL
                    && op.payload() instanceof KindPayload.IntrinsicCallPayload intrinsic
                    && intrinsic.kind() == IntrinsicKind.BYTES_NEW) {
                return true;
            }
            if (op.payload() instanceof KindPayload.IndexNormalizePayload normalize
                    && (normalize.mode() == IndexMode.BYTES_READ
                        || normalize.mode() == IndexMode.BYTES_WRITE)) {
                return true;
            }
            if (op.payload() instanceof KindPayload.BoundaryPayload boundary
                    && (boundary.kind() == BoundaryKind.BYTE_ELEMENT_READ
                        || boundary.kind() == BoundaryKind.BYTE_ELEMENT_ASSIGNMENT)) {
                return true;
            }
            if (op.kind() == SemanticOpKind.ASSIGN
                    && op.payload() instanceof KindPayload.AssignPayload assign
                    && assign.targetKind() == deal.semantic.ir.AssignTargetKind.BYTES_SLOT) {
                return true;
            }
            if (op.failurePolicy() == FailurePolicyId.BYTES_ALLOCATE
                    || op.failurePolicy() == FailurePolicyId.BYTES_READ
                    || op.failurePolicy() == FailurePolicyId.BYTES_WRITE) {
                return true;
            }
            if (op.resultType() instanceof RuntimeDescriptor resultDescriptor
                    && containsBytes(resultDescriptor)) {
                return true;
            }
            for (RuntimeDescriptor descriptor : op.operandTypes()) {
                if (containsBytes(descriptor)) {
                    return true;
                }
            }
            if (op.payload() instanceof KindPayload.BoundaryPayload boundary
                    && containsBytes(boundary.descriptor())) {
                return true;
            }
            if (op.kind() == SemanticOpKind.INDEX_READ
                    && op.payload() instanceof KindPayload.IndexReadPayload read) {
                for (SemanticOp candidate : unit.ops()) {
                    if (read.slot().equals(candidate.result())
                            && candidate.resultType()
                                instanceof RuntimeDescriptor.Bytes) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /** Whether one descriptor contains the bytes carrier at any depth. */
    private static boolean containsBytes(RuntimeDescriptor descriptor) {
        return switch (descriptor) {
            case null -> false;
            case RuntimeDescriptor.Bytes ignored -> true;
            case RuntimeDescriptor.Array array -> containsBytes(array.element());
            case RuntimeDescriptor.Nullable nullable -> containsBytes(nullable.inner());
            case RuntimeDescriptor.Func func -> {
                boolean found = containsBytes(func.returnType());
                for (RuntimeDescriptor parameter : func.paramTypes()) {
                    found = found || containsBytes(parameter);
                }
                yield found;
            }
            default -> false;
        };
    }

    // =========================================================================
    // Shared helpers
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

    private static OpId producerOf(LoweredModuleUnit unit, ValueId value) {
        for (SemanticOp op : unit.ops()) {
            if (value.equals(op.result())) {
                return op.opId();
            }
        }
        return null;
    }

    private static SemanticOp opById(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // The production artifact runners (the real toolchains)
    // =========================================================================

    /**
     * One production artifact run: the probe's outcome framing ({@code OK}
     * or {@code ERR:code|message|origin|expected|actual}), the artifact's
     * stdout, and the artifact's {@code DEAL_ERROR_CODE} terminal line of a
     * direct run (empty for a runtime-ok drive).
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

    private static ArtifactRun luaProduction(Drive drive) throws Exception {
        Path workspace = Files.createTempDirectory("bytes-lua");
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
            check(!outcome.isEmpty(), drive.spec().what() + " (luajit): the production "
                + "artifact publishes its outcome: " + stdout);
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

    private static ArtifactRun jvmProduction(Drive drive) throws Exception {
        Path workspace = Files.createTempDirectory("bytes-jvm");
        try {
            String className = JvmBackend.classNameFor(
                drive.project().entryModule().path());
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
            String stdout = runJava(classpath, classes, "Probe");
            String outcome = stdout.lines()
                .filter(line -> line.startsWith("ERR:") || line.equals("OK"))
                .reduce((first, second) -> second).orElse("");
            check(!outcome.isEmpty(), drive.spec().what() + " (java): the production "
                + "artifact publishes its outcome: " + stdout);
            String terminalLine = "";
            if (!drive.spec().runtimeOk()) {
                terminalLine = runJava(classpath, classes, className).strip();
            }
            return new ArtifactRun(outcome, stdout, terminalLine);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static String runJava(String classpath, Path classes, String mainClass)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder("java", "-cp",
            classpath + File.pathSeparator + classes, mainClass);
        builder.directory(classes.getParent().toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        check(exit == 0 || exit == 1, "the java run of " + mainClass + " exits 0 or 1: "
            + "stdout=" + stdout + " stderr=" + stderr);
        return stdout;
    }

    // =========================================================================
    // Entry point
    // =========================================================================

    public static void main(String[] args) throws Exception {
        testCorpusPins();
        testCorpusDrive();
        testReadShapeAndWriteChain();
        testOracleRealization();
        testZeroBytesConstructUnlowered();
        System.out.println();
        System.out.println("BytesCoverageTest: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
