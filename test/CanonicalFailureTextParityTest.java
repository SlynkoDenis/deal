package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmRuntime;
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
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.SharedValueSemantics;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.UnicodeScalars;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0618 canonical v1.2 failure-text parity test
 * ({@code semantic-ir-construct-coverage-cutover} K8 and Verification 9).
 *
 * <ol>
 *   <li><b>Message parity.</b> The {@code INT32_RESULT} row template and
 *       every row-driven shared producer render exactly
 *       {@code int out of safe range}; the {@code JSON_TO_ERROR} row
 *       carries the corpus-aligned {@code STDLIB_CALL(JSON_STRINGIFY)}
 *       rejection template {@code unsupported type for JSON encoding:
 *       {actual}}; the emitted Lua prelude and the shared JVM runtime
 *       carry the same pinned literals and the pinned expected text, and
 *       no shared v1.2 producer renders the legacy {@code int out of
 *       range}.</li>
 *   <li><b>Int32-overflow probe.</b> One project lowers through the one
 *       project lowering and drives the oracle, the production LuaJIT
 *       artifact under real {@code luajit}, and the production JVM
 *       artifact under {@code javac --release 25 -proc:none} plus
 *       {@code java}; every consumer publishes the pinned code, message,
 *       and call origin.</li>
 *   <li><b>{@code json.stringify} rejection probe.</b> The same drive for
 *       the std/json rejection: the pinned message, the expected/actual
 *       pair, and the {@code json.stringify} call origin.</li>
 *   <li><b>Unchanged surfaces.</b> The legacy-profile corpus pin, the
 *       unchanged JS runtime and {@code std/json.lua} texts, the retained
 *       backends' legacy arm, and the four {@code std/json} corpus
 *       sidecars stay exactly as they are.</li>
 * </ol>
 */
public class CanonicalFailureTextParityTest {

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
    // The pinned v1.2 texts
    // =========================================================================

    /** The pinned E8004 text of the {@code INT32_RESULT} row and its producers. */
    private static final String INT32_TEMPLATE = "int out of safe range";

    /** The pinned std/json rejection template of the {@code JSON_TO_ERROR} row. */
    private static final String JSON_ENCODING_TEMPLATE =
        "unsupported type for JSON encoding: {actual}";

    /** The legacy-profile template the v1.2 shared path never renders. */
    private static final String LEGACY_INT32_TEMPLATE = "int out of range";

    // =========================================================================
    // The probes (each one project through the production pipeline)
    // =========================================================================

    /** The int32-overflow probe: E8004 at the addition origin (2:16). */
    private static final String INT32_OVERFLOW_SOURCE = """
        export function main(): null {
          let x: int = 2147483647 + 1
          return null
        }
        """;

    /** The json.stringify rejection probe: E8001 at the call origin (5:19). */
    private static final String JSON_REJECTION_SOURCE = """
        import * as json from "std/json"

        export function main(): null {
          let t: table = { n: 0.0 / 0.0 }
          let s: string = json.stringify(t)
          return null
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface) {
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    /** The release-owned production invocation (the cutover's production record). */
    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** The synthetic operation origin of the primitive-level checks. */
    private static SourceOrigin origin() {
        return new SourceOrigin("failure-text-parity", SourceSpan.synthetic("stdlib"),
            SourceOriginKind.SYNTHETIC, new AnchorId(1), null);
    }

    private static UnicodeScalars.Valid valid(String text) {
        return (UnicodeScalars.Valid) UnicodeScalars.validate(text);
    }

    /** Compiles one single-module project through the real orchestrator. */
    private static Fixture compileProject(String source) throws Exception {
        Path root = Files.createTempDirectory("failure-text-parity");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Path entry = src.resolve("main.deal");
        Files.writeString(entry, source, StandardCharsets.UTF_8);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry,
            root.resolve("out"), false, null, List.of(src.toAbsolutePath()), null);
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the probe project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface());
    }

    /** The one project lowering over the real checked project. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(invocation(), fixture.checkedProject(),
            fixture.index(), fixture.manifests(), fixture.surface(),
            new LinkedHashMap<ModuleId, CanonicalModuleIdentity>(),
            new LinkedHashMap<ModuleId, FfiGeneratedModule>(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** The distinct deal codes of the unit's ops (the probe's subject op check). */
    private static boolean hasOp(ExecutableLoweredProject project, SemanticOpKind kind) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == kind) {
                    return true;
                }
            }
        }
        return false;
    }

    // =========================================================================
    // 1. Message parity of the named shared producers
    // =========================================================================

    static void testMessageParity() {
        System.out.println("-- Message parity: the rows, the row-driven producers, and the "
            + "target literals --");

        // The INT32_RESULT row and its row-driven consumers.
        FailurePolicyRow int32Row = FailureContractRegistry.row(
            FailurePolicyId.INT32_RESULT);
        checkEq(List.of(INT32_TEMPLATE), int32Row.templates(),
            "the INT32_RESULT row template is exactly '" + INT32_TEMPLATE + "'");

        SourceOrigin origin = origin();
        checkTemplate(SharedValueSemantics.int32Add(2147483647, 1, origin),
            "int32Add(2147483647, 1)");
        checkTemplate(SharedValueSemantics.int32Sub(-2147483648, 1, origin),
            "int32Sub(-2147483648, 1)");
        checkTemplate(SharedValueSemantics.int32Mul(65536, 65536, origin),
            "int32Mul(65536, 65536)");
        checkTemplate(SharedValueSemantics.int32Neg(Integer.MIN_VALUE, origin),
            "int32Neg(-2147483648)");
        checkTemplate(SharedValueSemantics.int32Div(Integer.MIN_VALUE, -1, origin),
            "int32Div(-2147483648, -1)");
        checkTemplate(SharedValueSemantics.int32Pow(2, 31, origin), "int32Pow(2, 31)");
        checkTemplate(SharedValueSemantics.checkInt32Integral(2147483648L, origin),
            "checkInt32Integral(2147483648)");
        checkTemplate(SharedValueSemantics.intFromNumber(2147483648.0, origin),
            "intFromNumber(2147483648.0)");

        // The stdlib row-driven producer: MATH_ABS_INT's terminal.
        SharedStdlibSemantics.Outcome<SharedStdlibSemantics.Value> abs =
            SharedStdlibSemantics.mathAbsInt(origin, Integer.MIN_VALUE);
        check(abs instanceof SharedStdlibSemantics.Outcome.Failure<
                    SharedStdlibSemantics.Value> failure
                && failure.failure().failure().code() == deal.diagnostics.DiagnosticCode.E8004
                && failure.failure().failure().message().equals(INT32_TEMPLATE)
                && failure.failure().origin().equals(origin),
            "absInt(-2147483648) renders the pinned E8004 text at the call origin: "
                + (abs instanceof SharedStdlibSemantics.Outcome.Failure<?> f
                    ? f.failure().failure().message() : abs));

        // The JSON_TO_ERROR row: the @jsonable projection stays first, the
        // corpus-aligned std/json rejection is the second template.
        FailurePolicyRow jsonRow = FailureContractRegistry.row(
            FailurePolicyId.JSON_TO_ERROR);
        checkEq(List.of("value at {fieldPath} is not JSON serializable: {actual}",
                JSON_ENCODING_TEMPLATE),
            jsonRow.templates(),
            "the JSON_TO_ERROR row pins the @jsonable template first and the "
                + "corpus-aligned std/json rejection second");
        checkEq(List.of("fieldPath", "actual"), jsonRow.metadataKeys(),
            "the JSON_TO_ERROR row keeps the fieldPath/actual metadata keys");
        checkEq("call origin", jsonRow.originRule(),
            "the JSON_TO_ERROR row pins the call origin");

        // The std/json walker's projection: the pinned message, expected
        // text, actual token, and internal metadata.
        SharedStdlibSemantics.Value table = SharedStdlibSemantics.Value.table();
        SharedStdlibSemantics.Value.Table tableView =
            (SharedStdlibSemantics.Value.Table) table;
        tableView.table().put("n", new SharedStdlibSemantics.Value.Number(Double.NaN));
        SharedStdlibSemantics.Outcome<SharedStdlibSemantics.Value> stringify =
            SharedStdlibSemantics.jsonStringify(origin,
                tableView.table());
        if (stringify instanceof SharedStdlibSemantics.Outcome.Failure<
                SharedStdlibSemantics.Value> failure) {
            checkEq("E8001", failure.failure().failure().code().name(),
                "the std/json rejection is E8001");
            checkEq("unsupported type for JSON encoding: number",
                failure.failure().failure().message(),
                "the std/json rejection renders the pinned message");
            checkEq(SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED,
                failure.failure().failure().expected(),
                "the std/json rejection renders the pinned expected text");
            checkEq("number", failure.failure().failure().actual(),
                "the std/json rejection renders the canonical actual-kind token");
            checkEq(Map.of("fieldPath", "n", "actual", "number"),
                failure.failure().failure().metadata(),
                "the walker's fieldPath stays internal metadata");
            checkEq(origin, failure.failure().origin(),
                "the std/json rejection carries the call origin");
        } else {
            fail("jsonStringify over a NaN member must fail, got " + stringify);
        }

        // The pinned expected text itself.
        checkEq("string, number, boolean, or table",
            SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED,
            "the shared expected text is the corpus-pinned descriptor list");
    }

    /** Asserts one int32 primitive failure carries the pinned row template. */
    private static void checkTemplate(SharedValueSemantics.Int32Result result,
                                      String what) {
        check(result instanceof SharedValueSemantics.Int32Result.Fail failure
                && failure.template().equals(INT32_TEMPLATE),
            what + " renders the pinned E8004 template: "
                + (result instanceof SharedValueSemantics.Int32Result.Fail f
                    ? f.template() : result));
    }

    // =========================================================================
    // 2. The int32-overflow probe through the production pipeline
    // =========================================================================

    static void testInt32OverflowProbe() throws Exception {
        System.out.println("-- Int32-overflow probe: oracle + production LuaJIT + production "
            + "JVM --");
        Fixture fixture = compileProject(INT32_OVERFLOW_SOURCE);
        Path workspace = Files.createTempDirectory("failure-text-parity-int32");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null,
                "the int32 probe lowers through the one project lowering: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            check(hasOp(result.project(), SemanticOpKind.BINARY),
                "the int32 probe carries the overflowing BINARY op");

            SemanticRuntimeModel.ErrorSnapshot error = oracleFailure(result);
            if (error != null) {
                checkEq("E8004", error.code(), "the oracle terminal is E8004");
                checkEq(INT32_TEMPLATE, error.message(),
                    "the oracle publishes the pinned message");
                check(error.origin().replace(java.io.File.separatorChar, '/')
                        .endsWith("src/main.deal:2:16"),
                    "the oracle publishes the addition origin (2:16): " + error.origin());
                check(!error.frames().isEmpty(),
                    "the oracle carries the active DEAL frames: " + error.frames());
            }

            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            check(lua.contains("\"" + INT32_TEMPLATE + "\""),
                "the production LuaJIT artifact carries the pinned literal");
            check(!lua.contains(LEGACY_INT32_TEMPLATE),
                "the production LuaJIT artifact renders no legacy template");
            ProcessOutcome luaRun = runLua(lua, workspace.resolve("lua"));
            checkEq(1, luaRun.exitCode(),
                "the LuaJIT artifact exits 1: stdout=" + escaped(luaRun.stdout())
                    + " stderr=" + escaped(luaRun.stderr()));
            checkEq("DEAL_ERROR_CODE: E8004\n", luaRun.stdout(),
                "the LuaJIT artifact publishes the E8004 terminal on stdout");
            checkEq("", luaRun.stderr(),
                "the LuaJIT artifact publishes no trace on stderr");

            ProcessOutcome jvmRun = runJvm(result.project(), result.tables(),
                result.registries(), fixture.surface(), workspace.resolve("jvm"));
            checkEq(1, jvmRun.exitCode(),
                "the JVM artifact exits 1: " + jvmRun.stdout() + jvmRun.stderr());
            check(jvmRun.stdout().contains("DEAL_ERROR_CODE: E8004"),
                "the JVM artifact publishes the E8004 terminal on stdout: "
                    + escaped(jvmRun.stdout()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The json.stringify rejection probe through the production pipeline
    // =========================================================================

    static void testJsonStringifyRejectionProbe() throws Exception {
        System.out.println("-- json.stringify rejection probe: oracle + production LuaJIT + "
            + "production JVM --");
        Fixture fixture = compileProject(JSON_REJECTION_SOURCE);
        Path workspace = Files.createTempDirectory("failure-text-parity-json");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null,
                "the json probe lowers through the one project lowering: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            check(hasOp(result.project(), SemanticOpKind.STDLIB_CALL),
                "the json probe carries the STDLIB_CALL(JSON_STRINGIFY) op");

            SemanticRuntimeModel.ErrorSnapshot error = oracleFailure(result);
            if (error != null) {
                checkEq("E8001", error.code(), "the oracle terminal is E8001");
                checkEq("unsupported type for JSON encoding: number", error.message(),
                    "the oracle publishes the pinned std/json rejection message");
                checkEq(SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, error.expected(),
                    "the oracle publishes the pinned expected text");
                checkEq("number", error.actual(),
                    "the oracle publishes the canonical actual-kind token");
                check(error.origin().replace(java.io.File.separatorChar, '/')
                        .endsWith("src/main.deal:5:19"),
                    "the oracle publishes the json.stringify call origin (5:19): "
                        + error.origin());
                check(!error.frames().isEmpty(),
                    "the oracle carries the active DEAL frames: " + error.frames());
            }

            String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
                result.tables(), result.registries(), fixture.surface());
            check(lua.contains("unsupported type for JSON encoding: "),
                "the production LuaJIT artifact carries the pinned rejection message");
            check(lua.contains(SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED),
                "the production LuaJIT artifact carries the pinned expected text");
            check(!lua.contains("not JSON serializable"),
                "the production LuaJIT artifact renders no internal fieldPath spelling");
            ProcessOutcome luaRun = runLua(lua, workspace.resolve("lua"));
            checkEq(1, luaRun.exitCode(),
                "the LuaJIT artifact exits 1: stdout=" + escaped(luaRun.stdout())
                    + " stderr=" + escaped(luaRun.stderr()));
            checkEq("DEAL_ERROR_CODE: E8001\n", luaRun.stdout(),
                "the LuaJIT artifact publishes the E8001 terminal on stdout");

            ProcessOutcome jvmRun = runJvm(result.project(), result.tables(),
                result.registries(), fixture.surface(), workspace.resolve("jvm"));
            checkEq(1, jvmRun.exitCode(),
                "the JVM artifact exits 1: " + jvmRun.stdout() + jvmRun.stderr());
            check(jvmRun.stdout().contains("DEAL_ERROR_CODE: E8001"),
                "the JVM artifact publishes the E8001 terminal on stdout: "
                    + escaped(jvmRun.stdout()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The literal-carrying shared JVM runtime producers
    // =========================================================================

    static void testSharedJvmRuntimeProducers() {
        System.out.println("-- Shared JVM runtime producers: the literal-carrying sites --");
        JvmRuntime.setTraceEnabled(false);

        // The int boundary ladder and the int arithmetic gates (every
        // literal-carrying site: bcheck, int32Result, the INT32_POW
        // long-overflow arm, the conversion ladder, and the stdlib gate).
        try {
            JvmRuntime.bcheck("int", "int", Double.valueOf(2147483648.0));
            fail("bcheck(int) must reject 2147483648.0");
        } catch (JvmRuntime.DealError e) {
            checkEq("E8004", e.code, "bcheck(int) is E8004");
            checkEq(INT32_TEMPLATE, e.msg, "bcheck(int) renders the pinned template");
        }
        expectJvmInt32Failure("arith(INT32_ADD) overflow", () ->
            JvmRuntime.arith("INT32_ADD", Long.valueOf(2147483647), Long.valueOf(1),
                "op", "digest", "parent", originAtom()));
        expectJvmInt32Failure("arith(INT32_POW) long overflow", () ->
            JvmRuntime.arith("INT32_POW", Long.valueOf(2), Long.valueOf(63),
                "op", "digest", "parent", originAtom()));
        expectJvmInt32Failure("unary(INT32_NEG)", () ->
            JvmRuntime.unary("INT32_NEG", Long.valueOf(Integer.MIN_VALUE),
                "op", "digest", "parent", originAtom()));
        expectJvmInt32Failure("intConv out of range", () ->
            JvmRuntime.intConv(Double.valueOf(2147483648.0), "number",
                "op", "digest", "parent", originAtom()));
        expectJvmInt32Failure("absInt(-2147483648)", () ->
            JvmRuntime.stdlib("MATH_ABS_INT", "op", "digest", "parent", originAtom(),
                new Object[] {Long.valueOf(Integer.MIN_VALUE)}));

        // The std/json walker's rejection.
        JvmRuntime.Table table = new JvmRuntime.Table();
        table.write("n", Double.valueOf(Double.NaN));
        try {
            JvmRuntime.stdlib("JSON_STRINGIFY", "op", "digest", "parent", originAtom(),
                new Object[] {table});
            fail("json.stringify over a NaN member must fail");
        } catch (JvmRuntime.DealError e) {
            checkEq("E8001", e.code, "the JVM std/json rejection is E8001");
            checkEq("unsupported type for JSON encoding: number", e.msg,
                "the JVM std/json rejection renders the pinned message");
            checkEq(SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, e.expected,
                "the JVM std/json rejection renders the pinned expected text");
            checkEq("number", e.actual,
                "the JVM std/json rejection renders the canonical actual-kind token");
        }
    }

    /** Asserts one shared JVM runtime producer raises the pinned E8004 projection. */
    private static void expectJvmInt32Failure(String what, java.util.concurrent.Callable<?> run) {
        try {
            run.call();
            fail(what + " must raise E8004");
        } catch (JvmRuntime.DealError e) {
            checkEq("E8004", e.code, what + " is E8004");
            checkEq(INT32_TEMPLATE, e.msg, what + " renders the pinned template");
        } catch (Exception e) {
            fail(what + " threw " + e + " instead of the pinned E8004 projection");
        }
    }

    private static String originAtom() {
        return "failure-text-parity:1:1";
    }

    // =========================================================================
    // 5. The unchanged surfaces (legacy profile, JS, corpus pins, retained
    //    backends)
    // =========================================================================

    static void testUnchangedSurfaces() throws Exception {
        System.out.println("-- Unchanged surfaces: legacy profile, JS, corpus pins, "
            + "retained backends --");

        // The legacy-profile corpus pin keeps the legacy text.
        String legacyPin = Files.readString(Path.of("test", "conformance",
            "backend-runtime", "runtime", "int-convert-range.expect.json"),
            StandardCharsets.UTF_8);
        check(legacyPin.contains("\"message\": \"" + LEGACY_INT32_TEMPLATE + "\""),
            "the legacy-profile sidecar keeps the legacy template");
        check(legacyPin.contains("\"sourceFile\": \"backend-runtime/runtime/"
                + "int-convert-range.deal\""),
            "the legacy-profile sidecar is the fixture's authority");

        // The unchanged JS runtime keeps its profile split.
        String js = Files.readString(Path.of("deal", "runtime.js"),
            StandardCharsets.UTF_8);
        check(js.contains("\"int out of safe range\" : \"" + LEGACY_INT32_TEMPLATE + "\""),
            "the JS runtime keeps the profile split (v1.2 vs legacy)");
        check(js.contains("unsupported type for JSON encoding: "),
            "the JS runtime keeps the std/json rejection spelling");

        // The unchanged deployed std/json keeps the corpus spelling.
        String stdJson = Files.readString(Path.of("std", "json.lua"),
            StandardCharsets.UTF_8);
        check(stdJson.contains("unsupported type for JSON encoding: "),
            "the deployed std/json.lua keeps the corpus spelling");

        // The retained JVM backend keeps its legacy arm.
        String jvmBackend = Files.readString(Path.of("deal", "codegen", "jvm",
            "JvmBackend.java"), StandardCharsets.UTF_8);
        check(jvmBackend.contains("\"" + LEGACY_INT32_TEMPLATE + "\""),
            "the retained JVM backend keeps its legacy-safe-int arm");
        check(jvmBackend.contains("\"" + INT32_TEMPLATE + "\""),
            "the retained JVM backend keeps its signed-int32 arm");

        // The four std/json rejection sidecars keep the pinned corpus text.
        for (String sidecar : List.of(
                "test/conformance/backend-runtime/stdlib/json/"
                    + "json-stringify-bytes-error.expect.json",
                "test/conformance/backend-runtime/stdlib/json/"
                    + "json-stringify-nested-bytes-error.expect.json",
                "test/conformance/backend-runtime/runtime-errors/"
                    + "json-stringify-function-e8001.expect.json",
                "test/conformance/backend-runtime/source-location/"
                    + "json-error-source.expect.json")) {
            String text = Files.readString(Path.of(sidecar), StandardCharsets.UTF_8);
            check(text.contains("\"message\": \"unsupported type for JSON encoding: ")
                    && text.contains("\"expected\": \"string, number, boolean, or table\""),
                sidecar + " keeps the pinned message/expected pair");
        }

        // The int-overflow sidecars keep the pinned v1.2 text.
        for (String sidecar : List.of(
                "test/conformance/backend-runtime/arithmetic/int-add-overflow.expect.json",
                "test/conformance/backend-runtime/arithmetic/"
                    + "int32-pow-overflow.expect.json",
                "test/conformance/backend-runtime/stdlib/math/"
                    + "int-abs-min-overflow.expect.json",
                "test/conformance/backend-runtime/source-location/"
                    + "int32-overflow-source.expect.json")) {
            String text = Files.readString(Path.of(sidecar), StandardCharsets.UTF_8);
            check(text.contains("\"message\": \"" + INT32_TEMPLATE + "\""),
                sidecar + " keeps the pinned v1.2 template");
        }
    }

    // =========================================================================
    // The production target runners
    // =========================================================================

    /** The oracle terminal failure of the probe project, or null with a diagnostic. */
    private static SemanticRuntimeModel.ErrorSnapshot oracleFailure(
            SemanticLowerer.ProjectLoweringResult result) {
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(result.project(),
            result.tables(), result.registries(), null);
        if (run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure failure) {
            return failure.error();
        }
        fail("expected a DealFailure terminal, got " + run.terminal());
        return null;
    }

    /** Writes the LuaJIT artifact, deploys the runtime, and runs real luajit. */
    private static ProcessOutcome runLua(String lua, Path workspace) throws Exception {
        Files.createDirectories(workspace);
        Path artifact = workspace.resolve("project.lua");
        Files.writeString(artifact, lua, StandardCharsets.UTF_8);
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
        return runProcess(List.of("luajit", artifact.toAbsolutePath().toString()),
            workspace);
    }

    /** Writes the JVM artifact, compiles it with javac, and runs real java. */
    private static ProcessOutcome runJvm(ExecutableLoweredProject project,
                                         Map<ModuleId, StructuredBodyTable> tables,
                                         Map<ModuleId, ClassFactoryRegistry> registries,
                                         HostDeclarationSurface declarationSurface,
                                         Path workspace) throws Exception {
        Files.createDirectories(workspace);
        String className = JvmBackend.classNameFor(project.entryModule().path());
        JvmSemanticEmitter.EmissionResult emission =
            JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                className, declarationSurface);
        Path source = workspace.resolve(className + ".java");
        Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
        Path classes = workspace.resolve("classes");
        Files.createDirectories(classes);
        String classpath = Path.of("build").toAbsolutePath().normalize().toString();
        ProcessOutcome javac = runProcess(List.of("javac", "--release", "25",
            "-proc:none", "-cp", classpath, "-d", classes.toString(),
            source.toAbsolutePath().toString()), workspace);
        if (javac.exitCode() != 0) {
            fail("the production JVM artifact compiles with javac --release 25 "
                + "-proc:none: " + javac.stdout() + javac.stderr());
            return javac;
        }
        return runProcess(List.of("java", "-cp",
            classpath + java.io.File.pathSeparator + classes, className), workspace);
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir)
            throws Exception {
        Path stderrFile = Files.createTempFile(workDir, "stderr", ".txt");
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static String escaped(String text) {
        return text.replace("\n", "\\n");
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
        System.out.println("=== Canonical Failure-Text Parity Tests (ISSUE-0618) ===\n");
        testMessageParity();
        testInt32OverflowProbe();
        testJsonStringifyRejectionProbe();
        testSharedJvmRuntimeProducers();
        testUnchangedSurfaces();
        System.out.println("passed=" + passed + " failed=" + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
