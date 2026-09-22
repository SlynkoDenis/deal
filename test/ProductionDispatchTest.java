package deal.test;

import deal.codegen.Backend;
import deal.module.CompilationOrchestrator;
import deal.project.CliOverrides;
import deal.project.ProjectLocator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticProfile;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

/**
 * ISSUE-0643: the phase-4 production dispatch and the atomic cutover
 * acceptance tests
 * ({@code production-project-emission-and-atomic-cutover} P4/P6/P7/P8/
 * P10/P11 and the production-arm, source-map, zero-retained-reachability,
 * publication, and fail-closed producer-guard contracts;
 * {@code luajit-jvm-single-lowering-production-cutover} C3/C5/C7/C8;
 * {@code conformance-lane-production-cutover} L1/L4).
 *
 * <ol>
 *   <li>the production-invocation predicate is record identity: true
 *       exactly for the record {@code Main} and {@code defaultInvocation}
 *       resolve, false for both harness purposes and for the test-only
 *       {@code PUBLIC_BUILD} records that carry another release state or
 *       another capability-registry digest;</li>
 *   <li>a release-owned LuaJIT and JVM production compile emits exactly
 *       one project artifact named for the entry module, with
 *       {@code semanticEmissionCount() == 1},
 *       {@code retainedEmissionCount() == 0}, {@code routePlan() == null},
 *       an empty {@code jvmGeneratedResults()}, no per-module siblings,
 *       byte-identical repeated compiles, and real-toolchain execution
 *       ({@code luajit}; {@code javac --release 25 -proc:none} plus
 *       {@code java});</li>
 *   <li>the two-module realizable fixture (a {@code COMPILED} import with
 *       no cross-module call) emits one artifact per target carrying the
 *       per-module export surfaces, and the entry {@code main} runs
 *       exactly once;</li>
 *   <li>a failing lowering (a later-slice construct) and a failing
 *       emission (a cross-module sync call) each publish nothing and leave
 *       the previous artifact set byte-identical;</li>
 *   <li>the fail-closed families: a HOST-kind import
 *       ({@code HOST_MODULE_IMPORT}), a cross-module async call
 *       ({@code EXTERNAL_ASYNC_CALL}), a cross-module sync call, bytes,
 *       and
 *       function-typed materializations each fail with their named E6005
 *       and publish nothing, while a {@code STDLIB}/{@code COMPILED}-only
 *       closure, the builtin Error construction (ISSUE-0619), the
 *       {@code time.nowMillis} coverage (ISSUE-0623: the emitted artifacts
 *       publish the pinned E8004 terminal), and a
 *       same-module async call emit and execute;</li>
 *   <li>the C9 source-map disposition: an explicit {@code --source-map}
 *       LuaJIT and JVM production compile succeeds, publishes the project
 *       artifact, writes no sidecar, and prints the pinned warning exactly
 *       once; a {@code --dump-ir}-only compile prints none;</li>
 *   <li>the dispatch: every other LuaJIT/JVM invocation (both harness
 *       purposes and the two test-only {@code PUBLIC_BUILD} record
 *       families) keeps the harness arm — phase 3.7 route planning, the
 *       retained per-module artifacts, and the retained counters.</li>
 * </ol>
 */
public class ProductionDispatchTest {

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
    // Fixture helpers
    // =========================================================================

    private static final String DEAL_JSON_LUA = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "output": "out",
          "backend": "luajit"
        }
        """;

    private static final String DEAL_JSON_JVM = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "output": "out",
          "backend": "jvm"
        }
        """;

    private static final String HOST_DEAL_JSON_LUA = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "output": "out",
          "backend": "luajit",
          "externals": {
            "host/cfg": { "declaration": "cfg.d.deal" }
          }
        }
        """;

    /** The covered library module: no call, no later-slice construct. */
    private static final String LIB_SOURCE = """
        export function value(): int {
          return 42
        }

        export function label(): string {
          return "lib"
        }
        """;

    /** The covered two-module entry: a COMPILED import, no call. */
    private static final String APP_SOURCE = """
        import * as lib from "./lib"
        import * as console from "std/console"

        export function main(): null {
          console.log("PROBE|MAIN-ONCE")
          return null
        }

        export function label(): string {
          return "app"
        }
        """;

    /** The overflow fixture: the production DEAL_ERROR_CODE terminal. */
    private static final String OVERFLOW_SOURCE = """
        export function main(): null {
          let x: int = 2147483647 + 1
          return null
        }
        """;

    /** The bytes-bearing fixture: the lowering fails CONSTRUCT_UNLOWERED. */
    private static final String BYTES_SOURCE = """
        export function main(): null {
          let n: int = 3
          let b: bytes = bytes(n)
          return null
        }
        """;

    /** The builtin-Error-construction fixture (ISSUE-0619's covered slice). */
    private static final String ERROR_SOURCE = """
        export function main(): null {
          let e: Error = { code: "E1", message: "m" }
          return null
        }
        """;

    /** The {@code time.nowMillis} fixture (ISSUE-0623's covered construct). */
    private static final String TIME_SOURCE = """
        import * as time from "std/time"

        export function main(): null {
          let t: int = time.nowMillis()
          return null
        }
        """;

    /** The function-typed materialization (a later slice's construct). */
    private static final String FUNCTION_VALUE_SOURCE = """
        export function main(): null {
          let f: (a: int) => int = one
          let x: int = f(1)
          return null
        }

        function one(x: int): int {
          return x
        }
        """;

    /** The cross-module sync call: the emission covers no such arm. */
    private static final String SYNC_CALL_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let x: int = lib.value()
          return null
        }
        """;

    /** The cross-module async library. */
    private static final String ASYNC_LIB_SOURCE = """
        export async function getValue(): int {
          return 42
        }
        """;

    /** The cross-module async call (a never-invoked body carries it). */
    private static final String CROSS_ASYNC_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          return null
        }

        async function worker(): int {
          return await lib.getValue()
        }
        """;

    /**
     * The same-module async call: accepted, emitted, and executable. The
     * awaiting call sits in an exported zero-arity async function, so a
     * runner can invoke it through the artifact's published entry surface
     * and actually execute the ASYNC_START(DEAL_BODY)/AWAIT path.
     */
    private static final String SAME_ASYNC_SOURCE = """
        export function main(): null {
          return null
        }

        async function compute(): int {
          return 1
        }

        export async function worker(): int {
          return await compute()
        }
        """;

    /** The host declaration of the HOST-import fixture. */
    private static final String HOST_DECLARATION = """
        export function version(): int;
        """;

    /** The host-import fixture: the import is never called. */
    private static final String HOST_IMPORT_SOURCE = """
        import * as cfg from "host/cfg"

        export function main(): null {
          return null
        }
        """;

    private static void write(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(path -> {
                    try {
                        Files.deleteIfExists(path);
                    } catch (Exception ignored) {
                    }
                });
        } catch (Exception ignored) {
        }
    }

    private record ProjectOutcome(int exitCode, String stderr) {
    }

    /** Runs the release-owned production CLI in-process. */
    private static ProjectOutcome runProductionCli(String... args)
            throws Exception {
        return runCli(() -> deal.Main.run(args));
    }

    /** Runs the test-scope harness compile entry in-process. */
    private static ProjectOutcome runHarnessCli(String... args)
            throws Exception {
        return runCli(() -> HarnessCompileEntry.run(args));
    }

    private interface CliCall {
        int run() throws Exception;
    }

    private static ProjectOutcome runCli(CliCall call) throws Exception {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = call.run();
            System.err.flush();
        } finally {
            System.setErr(originalErr);
        }
        return new ProjectOutcome(exitCode,
            err.toString(StandardCharsets.UTF_8).trim());
    }

    private record ProcessOutcome(int exitCode, String output) {
    }

    private static ProcessOutcome runProcess(Path directory, String... command)
            throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(directory.toFile());
        builder.redirectErrorStream(true);
        Process process = builder.start();
        String output = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exitCode = process.waitFor();
        return new ProcessOutcome(exitCode, output);
    }

    /**
     * One orchestrator compile of the given project through the compile's
     * own manifest with an explicit invocation (the dispatch seam).
     */
    private record ArmCompile(CompilationOrchestrator orchestrator,
                              boolean success) {
    }

    private static ArmCompile compileWithInvocation(Path project, String entry,
            CompilerInvocation invocation) throws Exception {
        Path entryFile = project.resolve(entry).toAbsolutePath().normalize();
        ProjectLocator.LocateResult located = ProjectLocator.locate(
            entryFile.toString(), new CliOverrides(null, null));
        if (located.context() == null) {
            throw new IllegalStateException("locate failed: " + located);
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, false, false, false, false, null,
            invocation);
        return new ArmCompile(orchestrator, orchestrator.compile());
    }

    private static ProjectOutcome productionCompile(Path project, String entry,
            String output) throws Exception {
        return runProductionCli("compile",
            project.resolve(entry).toAbsolutePath().toString(),
            "--output", project.resolve(output).toAbsolutePath().toString());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static CompilerInvocation commonShadow() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static CompilerInvocation legacyRegression() {
        return CompilerProfileProvider.resolveLegacyRegression(
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.V1_2_ACTIVE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** The test-only PUBLIC_BUILD record of another release state. */
    private static CompilerInvocation publicBuildPreActivation() {
        return CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** The test-only PUBLIC_BUILD record of another registry digest. */
    private static CompilerInvocation publicBuildShadowRegistry() {
        return CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static List<String> artifactFiles(Path root) throws Exception {
        if (!Files.isDirectory(root)) {
            return List.of();
        }
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(Files::isRegularFile)
                .map(path -> root.relativize(path).toString()
                    .replace(File.separatorChar, '/'))
                .sorted().toList();
        }
    }

    /** Byte-for-byte snapshot of one artifact tree. */
    private static Map<String, byte[]> snapshotTree(Path root) throws Exception {
        Map<String, byte[]> snapshot = new java.util.LinkedHashMap<>();
        for (String relative : artifactFiles(root)) {
            snapshot.put(relative, Files.readAllBytes(root.resolve(relative)));
        }
        return snapshot;
    }

    private static void checkTreeIdentical(Map<String, byte[]> before,
            Path root, String context) throws Exception {
        Map<String, byte[]> after = snapshotTree(root);
        boolean same = before.keySet().equals(after.keySet());
        if (same) {
            for (Map.Entry<String, byte[]> entry : before.entrySet()) {
                same = Arrays.equals(entry.getValue(),
                    after.get(entry.getKey()));
                if (!same) {
                    break;
                }
            }
        }
        check(same, context + ": the previous artifact set is byte-identical");
    }

    // =========================================================================
    // 1. The production-invocation predicate
    // =========================================================================

    private static void testInvocationPredicate() {
        System.out.println("-- the production-invocation predicate: record "
            + "identity, never a purpose-only test --");

        check(CompilationOrchestrator.isProductionInvocation(
                productionInvocation()),
            "the release-owned production record is the production invocation");
        checkEq(productionInvocation(),
            CompilerProfileProvider.resolve(
                ReleaseConfiguration.CURRENT_RELEASE_STATE,
                ReleaseConfiguration.releaseCapabilityRegistry()),
            "the predicate's reference record is the release-state resolution");

        check(!CompilationOrchestrator.isProductionInvocation(commonShadow()),
            "the COMMON_SHADOW harness record is not the production invocation");
        check(!CompilationOrchestrator.isProductionInvocation(
                legacyRegression()),
            "the LEGACY_REGRESSION harness record is not the production "
                + "invocation");
        check(!CompilationOrchestrator.isProductionInvocation(
                publicBuildPreActivation()),
            "a test-only PUBLIC_BUILD record of another release state is not "
                + "the production invocation");
        check(!CompilationOrchestrator.isProductionInvocation(
                publicBuildShadowRegistry()),
            "a test-only PUBLIC_BUILD record of another registry digest is "
                + "not the production invocation");

        check(productionInvocation().purpose()
                == deal.semantic.ir.InvocationPurpose.PUBLIC_BUILD
                && productionInvocation().semanticProfile()
                    == SemanticProfile.DEAL_V1_2_INT32,
            "the production invocation is the release-derived PUBLIC_BUILD "
                + "record of the active release");
    }

    // =========================================================================
    // 2. One production compile: one artifact, no route plan, real toolchain
    // =========================================================================

    private static void testProductionLuaJitSingleModule() throws Exception {
        System.out.println("-- LuaJIT production compile: one project artifact, "
            + "one emission, no route plan --");

        Path project = Files.createTempDirectory("production-dispatch-lua-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", """
                import * as console from "std/console"

                export function main(): null {
                  console.log("PROBE|MAIN-ONCE")
                  return null
                }

                export function label(): string {
                  return "single"
                }
                """);

            ArmCompile arm = compileWithInvocation(project, "src/main.deal",
                productionInvocation());
            check(arm.success(), "the production LuaJIT compile succeeds: "
                + arm.orchestrator().diagnostics());
            if (!arm.success()) {
                return;
            }
            CompilationOrchestrator orchestrator = arm.orchestrator();
            checkEq(1, orchestrator.semanticEmissionCount(),
                "the production arm records exactly one project emission");
            checkEq(0, orchestrator.retainedEmissionCount(),
                "the production arm increments no retained counter");
            check(orchestrator.routePlan() == null,
                "the production arm computes and consults no route plan");
            check(orchestrator.jvmGeneratedResults().isEmpty(),
                "the production arm populates no per-module backend results");

            Path out = project.resolve("out");
            List<String> artifacts = artifactFiles(out);
            check(artifacts.contains("main.lua"),
                "the one project artifact is named for the entry module: "
                    + artifacts);
            check(!artifacts.contains("lib.lua"),
                "the published set carries no per-module sibling: "
                    + artifacts);
            check(artifacts.stream().noneMatch(
                    file -> file.endsWith(".deal.map.json")),
                "the production set carries no source-map sidecar: "
                    + artifacts);

            ProcessOutcome run = runProcess(out, "luajit", "main.lua");
            check(run.exitCode() == 0,
                "the production LuaJIT artifact runs clean: exit="
                    + run.exitCode() + " output=" + run.output());
            checkEq(1, countOccurrences(run.output(), "PROBE|MAIN-ONCE"),
                "the entry main runs exactly once per chunk execution");

            // Byte-identical repeated compiles.
            Map<String, byte[]> first = snapshotTree(out);
            ProjectOutcome repeat = productionCompile(project, "src/main.deal",
                "out-repeat");
            check(repeat.exitCode() == 0, "the repeated compile succeeds: "
                + repeat.stderr());
            Map<String, byte[]> second = snapshotTree(
                project.resolve("out-repeat"));
            checkEq(first.keySet(), second.keySet(),
                "the repeated compile publishes the same artifact set");
            for (String relative : first.keySet()) {
                check(Arrays.equals(first.get(relative), second.get(relative)),
                    "the repeated compile is byte-identical for " + relative);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testProductionJvmTwoModule() throws Exception {
        System.out.println("-- JVM production compile: one project artifact, "
            + "javac --release 25 -proc:none plus java --");

        Path project = Files.createTempDirectory("production-dispatch-jvm-");
        try {
            write(project, "deal.json", DEAL_JSON_JVM);
            write(project, "src/lib.deal", LIB_SOURCE);
            write(project, "src/main.deal", APP_SOURCE);

            ArmCompile arm = compileWithInvocation(project, "src/main.deal",
                productionInvocation());
            check(arm.success(), "the production JVM compile succeeds: "
                + arm.orchestrator().diagnostics());
            if (!arm.success()) {
                return;
            }
            CompilationOrchestrator orchestrator = arm.orchestrator();
            checkEq(1, orchestrator.semanticEmissionCount(),
                "the production arm records exactly one project emission");
            checkEq(0, orchestrator.retainedEmissionCount(),
                "the production arm increments no retained counter");
            check(orchestrator.routePlan() == null,
                "the production arm computes and consults no route plan");
            check(orchestrator.jvmGeneratedResults().isEmpty(),
                "the production arm populates no per-module backend results");

            Path out = project.resolve("out");
            List<String> artifacts = artifactFiles(out);
            check(artifacts.equals(List.of("Main.java")),
                "the one project artifact is the entry class source: "
                    + artifacts);

            // The export surfaces of both modules are in the artifact, keyed
            // by the dotted module path.
            String source = Files.readString(out.resolve("Main.java"));
            check(source.contains("\"lib\"") && source.contains("\"main\""),
                "the artifact carries one export surface per module keyed by "
                    + "module identity");
            check(source.contains("public static void main(String[] args)"),
                "the project class publishes public static void main");
            check(source.contains("public final class Main"),
                "the project class is one public final class");

            String buildCp = Path.of("build").toAbsolutePath().normalize()
                .toString();
            ProcessOutcome javac = runProcess(project, "javac", "--release",
                "25", "-proc:none", "-cp", buildCp, "-d", out.toString(),
                out.resolve("Main.java").toString());
            check(javac.exitCode() == 0,
                "the production JVM artifact compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(out, "java", "-cp",
                buildCp + File.pathSeparator + out, "Main");
            check(run.exitCode() == 0,
                "the production JVM artifact runs clean: exit="
                    + run.exitCode() + " output=" + run.output());
            checkEq(1, countOccurrences(run.output(), "PROBE|MAIN-ONCE"),
                "the entry main runs exactly once under java");
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testProductionLuaJitTwoModuleSurfaces()
            throws Exception {
        System.out.println("-- LuaJIT two-module realizable fixture: one "
            + "artifact per target and the executed export surfaces --");

        Path project = Files.createTempDirectory("production-dispatch-surf-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/lib.deal", LIB_SOURCE);
            write(project, "src/main.deal", APP_SOURCE);

            ArmCompile arm = compileWithInvocation(project, "src/main.deal",
                productionInvocation());
            check(arm.success(), "the two-module production compile succeeds: "
                + arm.orchestrator().diagnostics());
            if (!arm.success()) {
                return;
            }
            CompilationOrchestrator orchestrator = arm.orchestrator();
            checkEq(1, orchestrator.semanticEmissionCount(),
                "the two-module compile records one project emission");
            checkEq(0, orchestrator.retainedEmissionCount(),
                "the two-module compile increments no retained counter");
            check(orchestrator.routePlan() == null,
                "the two-module compile consults no route plan");
            List<String> artifacts = artifactFiles(project.resolve("out"));
            check(artifacts.contains("main.lua")
                    && !artifacts.contains("lib.lua"),
                "the two-module compile publishes one artifact named for the "
                    + "entry module: " + artifacts);

            // The executed surfaces: the entry surface is returned by the
            // chunk; a runner probe asserts both per-module surfaces and
            // their declaration-order entries after execution.
            write(project, "probe.lua", """
                local surfaces = dofile("out/main.lua")
                assert(type(surfaces) == "table", "the chunk returns the entry surface")
                assert(type(surfaces.label) == "table", "the entry surface carries label")
                assert(surfaces.label.__kind == "function", "the landed entry shape")
                local lib = __exportSurfaces["lib"]
                assert(type(lib) == "table", "the lib surface exists")
                assert(type(lib.value) == "table" and lib.value.__kind == "function",
                  "the lib surface carries value")
                assert(type(lib.label) == "table" and lib.label.__kind == "function",
                  "the lib surface carries label")
                return surfaces
                """);
            ProcessOutcome probe = runProcess(project, "luajit", "probe.lua");
            check(probe.exitCode() == 0,
                "the executed entry surface carries its declared exports: "
                    + probe.output());
            ProcessOutcome run = runProcess(project.resolve("out"), "luajit",
                "main.lua");
            checkEq(1, countOccurrences(run.output(), "PROBE|MAIN-ONCE"),
                "the two-module entry main runs exactly once");
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testConversionOverflowTerminal() throws Exception {
        System.out.println("-- the production conversion-overflow fixture: the "
            + "DEAL_ERROR_CODE terminal --");

        Path project = Files.createTempDirectory("production-dispatch-ovf-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", OVERFLOW_SOURCE);
            ProjectOutcome compile = productionCompile(project, "src/main.deal",
                "out");
            check(compile.exitCode() == 0,
                "the overflow fixture compiles: " + compile.stderr());
            if (compile.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(project.resolve("out"), "luajit",
                "main.lua");
            check(run.exitCode() == 1
                    && run.output().contains("DEAL_ERROR_CODE: E8004"),
                "the production artifact prints DEAL_ERROR_CODE: E8004 and "
                    + "exits 1: exit=" + run.exitCode() + " output="
                    + run.output());
        } finally {
            deleteRecursively(project);
        }
    }

    private static int countOccurrences(String haystack, String needle) {
        int count = 0;
        int index = 0;
        while ((index = haystack.indexOf(needle, index)) >= 0) {
            count++;
            index += needle.length();
        }
        return count;
    }

    // =========================================================================
    // 3. Atomic failure through the dispatch
    // =========================================================================

    private static void testAtomicFailureThroughDispatch() throws Exception {
        System.out.println("-- atomic failure: a failing lowering and a failing "
            + "emission publish nothing and preserve the previous set --");

        Path project = Files.createTempDirectory("production-dispatch-atomic-");
        try {
            Path out = project.resolve("out");
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", BYTES_SOURCE);
            // A previous artifact set in the live output root.
            write(out, "main.lua", "-- previous artifact\n");
            write(out, "deal/runtime.lua", "-- previous runtime\n");
            Map<String, byte[]> before = snapshotTree(out);
            ProjectOutcome compile = productionCompile(project, "src/main.deal",
                "out");
            check(compile.exitCode() != 0,
                "the bytes-bearing production compile fails closed");
            check(compile.stderr().contains("E6005")
                    && compile.stderr().contains("CONSTRUCT_UNLOWERED"),
                "the failing lowering names the construct rule: "
                    + compile.stderr());
            checkTreeIdentical(before, out,
                "the failing lowering preserves the previous set");

            // The failing emission: a cross-module sync call lowers but the
            // production emission covers no external-call arm.
            Path sync = Files.createTempDirectory(
                "production-dispatch-atomic-sync-");
            try {
                write(sync, "deal.json", DEAL_JSON_LUA);
                write(sync, "src/lib.deal", LIB_SOURCE);
                write(sync, "src/main.deal", SYNC_CALL_SOURCE);
                Path syncOut = sync.resolve("out");
                write(syncOut, "main.lua", "-- previous artifact\n");
                write(syncOut, "lib.lua", "-- previous sibling\n");
                Map<String, byte[]> syncBefore = snapshotTree(syncOut);
                ProjectOutcome syncCompile = productionCompile(sync,
                    "src/main.deal", "out");
                check(syncCompile.exitCode() != 0,
                    "the cross-module sync call fails closed at emission");
                check(syncCompile.stderr().contains("E6005")
                        && syncCompile.stderr().contains(
                            "SHARED_EMITTER_COVERAGE"),
                    "the failing emission names the emitter-coverage rule: "
                        + syncCompile.stderr());
                checkTreeIdentical(syncBefore, syncOut,
                    "the failing emission preserves the previous set");
            } finally {
                deleteRecursively(sync);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    // =========================================================================
    // 4. The fail-closed families and the accepted closures
    // =========================================================================

    private static void testFailClosedFamilies() throws Exception {
        System.out.println("-- fail-closed families: HOST import, "
            + "cross-module async, bytes, Error, time, function values --");

        // (a) A HOST-kind declaration import (never called) fails closed
        // with the import's raw specifier and resolved module.
        Path host = Files.createTempDirectory("production-dispatch-host-");
        try {
            write(host, "deal.json", HOST_DEAL_JSON_LUA);
            write(host, "cfg.d.deal", HOST_DECLARATION);
            write(host, "src/main.deal", HOST_IMPORT_SOURCE);
            ProjectOutcome compile = productionCompile(host, "src/main.deal",
                "out");
            check(compile.exitCode() != 0,
                "the HOST-importing closure fails closed");
            check(compile.stderr().contains("E6005")
                    && compile.stderr().contains("SHARED_EMITTER_COVERAGE")
                    && compile.stderr().contains("HOST_MODULE_IMPORT")
                    && compile.stderr().contains("'host/cfg'")
                    && compile.stderr().contains("'host.cfg'"),
                "the guard names the stable token, the raw specifier, and the "
                    + "resolved module: " + compile.stderr());
            check(!Files.exists(host.resolve("out")),
                "the guarded compile stages no artifact");
        } finally {
            deleteRecursively(host);
        }

        // (b) A cross-module async call fails closed with the emitting
        // module, the callee module, and the export name.
        Path async = Files.createTempDirectory("production-dispatch-async-");
        try {
            write(async, "deal.json", DEAL_JSON_LUA);
            write(async, "src/lib.deal", ASYNC_LIB_SOURCE);
            write(async, "src/main.deal", CROSS_ASYNC_SOURCE);
            ProjectOutcome compile = productionCompile(async, "src/main.deal",
                "out");
            check(compile.exitCode() != 0,
                "the cross-module async closure fails closed");
            check(compile.stderr().contains("E6005")
                    && compile.stderr().contains("SHARED_EMITTER_COVERAGE")
                    && compile.stderr().contains("EXTERNAL_ASYNC_CALL")
                    && compile.stderr().contains("'main'")
                    && compile.stderr().contains("'lib'")
                    && compile.stderr().contains("'getValue'"),
                "the guard names the token, the emitting module, the callee "
                    + "module, and the export name: " + compile.stderr());
            check(!Files.exists(async.resolve("out")),
                "the guarded async compile stages no artifact");
        } finally {
            deleteRecursively(async);
        }

        // (c) The same-module async call emits and executes on both
        // targets. The awaiting call is reachable through the exported
        // zero-arity async function's published surface, so the runner's
        // invocation really runs the ASYNC_START(DEAL_BODY)/AWAIT path
        // (never merely compiling a never-invoked body).
        Path same = Files.createTempDirectory("production-dispatch-sameasync-");
        try {
            write(same, "deal.json", DEAL_JSON_LUA);
            write(same, "src/main.deal", SAME_ASYNC_SOURCE);

            // LuaJIT: the entry chunk executes under luajit and the
            // runner invokes the exported async function.
            ProjectOutcome luaCompile = productionCompile(same, "src/main.deal",
                "out");
            check(luaCompile.exitCode() == 0,
                "the same-module async closure emits: " + luaCompile.stderr());
            if (luaCompile.exitCode() != 0) {
                return;
            }
            write(same, "probe.lua", """
                local surfaces = dofile("out/main.lua")
                assert(type(surfaces) == "table",
                  "the chunk returns the entry surface")
                local worker = surfaces.worker
                assert(type(worker) == "table" and worker.__kind == "function",
                  "the entry surface publishes the same-module async export")
                local completion = worker.f()
                assert(completion == 1,
                  "the awaiting call completes with 1, got "
                    .. tostring(completion))
                """);
            ProcessOutcome probe = runProcess(same, "luajit", "probe.lua");
            check(probe.exitCode() == 0,
                "the same-module await path executes under luajit: "
                    + probe.output());

            // JVM: the artifact compiles with javac --release 25
            // -proc:none and the runner executes the exported async
            // function through the artifact's published surface.
            Path jvmOut = same.resolve("out-jvm");
            ProjectOutcome jvmCompile = runProductionCli("compile",
                same.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--output",
                jvmOut.toAbsolutePath().toString());
            check(jvmCompile.exitCode() == 0,
                "the same-module async JVM closure emits: "
                    + jvmCompile.stderr());
            if (jvmCompile.exitCode() != 0) {
                return;
            }
            write(jvmOut, "AsyncWorkerRunner.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class AsyncWorkerRunner {
                  public static void main(String[] args) {
                    Main.main(new String[0]);
                    JvmRuntime.Table surface = Main.EXPORT_SURFACES.get("main");
                    JvmRuntime.FunctionValue worker =
                        (JvmRuntime.FunctionValue) surface.read("worker");
                    Object completion = worker.fn.invoke(new Object[0]);
                    System.out.println("PROBE|ASYNC-RESULT|" + completion);
                  }
                }
                """);
            String buildCp = Path.of("build").toAbsolutePath().normalize()
                .toString();
            ProcessOutcome javac = runProcess(same, "javac", "--release", "25",
                "-proc:none", "-cp", buildCp, "-d", jvmOut.toString(),
                jvmOut.resolve("Main.java").toString(),
                jvmOut.resolve("AsyncWorkerRunner.java").toString());
            check(javac.exitCode() == 0,
                "the same-module async JVM artifact compiles: "
                    + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            ProcessOutcome jvmRun = runProcess(jvmOut, "java", "-cp",
                buildCp + File.pathSeparator + jvmOut, "AsyncWorkerRunner");
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().contains("PROBE|ASYNC-RESULT|1"),
                "the same-module await path executes under java: exit="
                    + jvmRun.exitCode() + " output=" + jvmRun.output());
        } finally {
            deleteRecursively(same);
        }

        // (d) The later-slice constructs each fail with their named E6005;
        // the builtin Error construction is covered by ISSUE-0619 and
        // executes its production artifact on both targets.
        checkLaterSliceConstruct("bytes", Map.of("src/main.deal", BYTES_SOURCE),
            "CONSTRUCT_UNLOWERED");
        checkTimeNowMillisCoverage();
        checkLaterSliceConstruct("function-typed materialization",
            Map.of("src/main.deal", FUNCTION_VALUE_SOURCE),
            "CONSTRUCT_UNLOWERED");
        checkBuiltinErrorConstruction();

        // (e) The extern-C declaration import on LuaJIT fails with
        // HOST_MODULE_IMPORT (the FFI child owns the realization).
        Path externC = Files.createTempDirectory("production-dispatch-ffi-");
        try {
            write(externC, "deal.json", """
                {
                  "languageVersion": "1.2",
                  "moduleRoots": ["src"],
                  "output": "out",
                  "backend": "luajit",
                  "externals": {
                    "native/math": {
                      "declaration": "native.d.deal",
                      "nativeLibrary": "libs/libnative.so"
                    }
                  }
                }
                """);
            write(externC, "native.d.deal", """
                // @extern-c
                export function add(a: int, b: int): int;
                """);
            write(externC, "src/main.deal", """
                import * as math from "native/math"

                export function main(): null {
                  return null
                }
                """);
            ProjectOutcome compile = productionCompile(externC,
                "src/main.deal", "out");
            check(compile.exitCode() != 0,
                "the extern-C declaration import fails closed on LuaJIT");
            check(compile.stderr().contains("E6005")
                    && compile.stderr().contains("SHARED_EMITTER_COVERAGE")
                    && compile.stderr().contains("HOST_MODULE_IMPORT")
                    && compile.stderr().contains("'native/math'")
                    && compile.stderr().contains("'native.math'"),
                "the extern-C guard names the raw specifier and the resolved "
                    + "module: " + compile.stderr());
            check(!Files.exists(externC.resolve("out")),
                "the extern-C guarded compile stages no artifact");

            // The JVM target keeps the phase-3.9 E6006 rejection.
            ProjectOutcome jvmCompile = runProductionCli("compile",
                externC.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--output",
                externC.resolve("out-jvm").toAbsolutePath().toString());
            check(jvmCompile.exitCode() != 0
                    && jvmCompile.stderr().contains("E6006"),
                "the JVM extern-C case keeps the phase-3.9 E6006: "
                    + jvmCompile.stderr());
        } finally {
            deleteRecursively(externC);
        }
    }

    private static void checkLaterSliceConstruct(String name,
            Map<String, String> sources, String expectedRule) throws Exception {
        Path project = Files.createTempDirectory("production-dispatch-slice-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            for (Map.Entry<String, String> source : sources.entrySet()) {
                write(project, source.getKey(), source.getValue());
            }
            ProjectOutcome compile = productionCompile(project, "src/main.deal",
                "out");
            check(compile.exitCode() != 0,
                name + ": the later-slice construct fails closed");
            check(compile.stderr().contains("E6005")
                    && compile.stderr().contains(expectedRule),
                name + ": the failure names " + expectedRule + ": "
                    + compile.stderr());
            check(!Files.exists(project.resolve("out")),
                name + ": the failure stages no artifact");
        } finally {
            deleteRecursively(project);
        }
    }

    /**
     * The K7 {@code time.nowMillis} coverage through the release-owned
     * production invocation (the fixture this battery pinned fail-closed):
     * the closure emits exactly one project artifact per target and both
     * artifacts execute under their real toolchains with the pinned E8004
     * {@code int out of safe range} terminal — the declared {@code int}
     * boundary is the single terminal of the target-clock read.
     */
    private static void checkTimeNowMillisCoverage() throws Exception {
        Path project = Files.createTempDirectory("production-dispatch-time-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", TIME_SOURCE);
            ProjectOutcome luaCompile = productionCompile(project, "src/main.deal",
                "out");
            check(luaCompile.exitCode() == 0,
                "the time.nowMillis closure emits one project artifact: "
                    + luaCompile.stderr());
            if (luaCompile.exitCode() == 0) {
                ProcessOutcome run = runProcess(project.resolve("out"),
                    "luajit", "main.lua");
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E8004"),
                    "the LuaJIT artifact publishes the pinned E8004 terminal: exit="
                        + run.exitCode() + " output=" + run.output());
            }

            Path jvmOut = project.resolve("out-jvm");
            ProjectOutcome jvmCompile = runProductionCli("compile",
                project.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--output",
                jvmOut.toAbsolutePath().toString());
            check(jvmCompile.exitCode() == 0,
                "the time.nowMillis JVM closure emits one project artifact: "
                    + jvmCompile.stderr());
            if (jvmCompile.exitCode() != 0) {
                return;
            }
            String buildCp = Path.of("build").toAbsolutePath().normalize()
                .toString();
            ProcessOutcome javac = runProcess(project, "javac", "--release", "25",
                "-proc:none", "-cp", buildCp, "-d", jvmOut.toString(),
                jvmOut.resolve("Main.java").toString());
            check(javac.exitCode() == 0,
                "the JVM time.nowMillis artifact compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            ProcessOutcome javaRun = runProcess(jvmOut, "java", "-cp",
                buildCp + File.pathSeparator + jvmOut, "Main");
            check(javaRun.exitCode() == 1
                    && javaRun.output().contains("DEAL_ERROR_CODE: E8004"),
                "the JVM artifact publishes the pinned E8004 terminal: exit="
                    + javaRun.exitCode() + " output=" + javaRun.output());
        } finally {
            deleteRecursively(project);
        }
    }

    /**
     * The builtin Error construction through the release-owned production
     * invocation (ISSUE-0619's retargeted pin; the fixture the ISSUE-0643
     * cutover battery pinned fail-closed): the closure emits exactly one
     * project artifact per target, the emitted carriers are the canonical
     * err values ({@code {__d = true, ...}} on LuaJIT,
     * {@code JvmRuntime.ErrorValue} on the JVM), and both artifacts execute
     * under their real toolchains with the empty success output.
     */
    private static void checkBuiltinErrorConstruction() throws Exception {
        Path project = Files.createTempDirectory("production-dispatch-error-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", ERROR_SOURCE);
            ProjectOutcome luaCompile = productionCompile(project, "src/main.deal",
                "out");
            check(luaCompile.exitCode() == 0,
                "the builtin Error closure emits one project artifact: "
                    + luaCompile.stderr());
            if (luaCompile.exitCode() == 0) {
                String lua = Files.readString(project.resolve("out/main.lua"));
                check(lua.contains("__instT = {__d = true, code = ")
                        && lua.contains(", m = ")
                        && lua.contains("\"E1\"")
                        && lua.contains("\"m\""),
                    "the LuaJIT artifact carries the canonical err carrier built "
                        + "from the provided fields: " + lua);
                ProcessOutcome run = runProcess(project.resolve("out"),
                    "luajit", "main.lua");
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the LuaJIT builtin Error artifact runs clean: exit="
                        + run.exitCode() + " output=" + run.output());
            }

            Path jvmOut = project.resolve("out-jvm");
            ProjectOutcome jvmCompile = runProductionCli("compile",
                project.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--output",
                jvmOut.toAbsolutePath().toString());
            check(jvmCompile.exitCode() == 0,
                "the builtin Error JVM closure emits one project artifact: "
                    + jvmCompile.stderr());
            if (jvmCompile.exitCode() != 0) {
                return;
            }
            String java = Files.readString(jvmOut.resolve("Main.java"));
            check(java.contains("new JvmRuntime.ErrorValue("),
                "the JVM artifact publishes the canonical ErrorValue carrier: "
                    + java);
            String buildCp = Path.of("build").toAbsolutePath().normalize()
                .toString();
            ProcessOutcome javac = runProcess(project, "javac", "--release", "25",
                "-proc:none", "-cp", buildCp, "-d", jvmOut.toString(),
                jvmOut.resolve("Main.java").toString());
            check(javac.exitCode() == 0,
                "the JVM builtin Error artifact compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            ProcessOutcome javaRun = runProcess(jvmOut, "java", "-cp",
                buildCp + File.pathSeparator + jvmOut, "Main");
            check(javaRun.exitCode() == 0 && javaRun.output().isEmpty(),
                "the JVM builtin Error artifact runs clean: exit="
                    + javaRun.exitCode() + " output=" + javaRun.output());
        } finally {
            deleteRecursively(project);
        }
    }

    // =========================================================================
    // 5. The C9 source-map disposition
    // =========================================================================

    private static void testSourceMapDisposition() throws Exception {
        System.out.println("-- source map: an explicit --source-map warns once "
            + "and stages no sidecar; --dump-ir is silent --");

        Path project = Files.createTempDirectory("production-dispatch-map-");
        try {
            write(project, "deal.json", DEAL_JSON_JVM);
            write(project, "src/lib.deal", LIB_SOURCE);
            write(project, "src/main.deal", APP_SOURCE);

            ProjectOutcome explicit = runProductionCli("compile",
                project.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--source-map", "--output",
                project.resolve("out-map").toAbsolutePath().toString());
            check(explicit.exitCode() == 0,
                "the explicit --source-map production compile succeeds: "
                    + explicit.stderr());
            checkEq(1, countOccurrences(explicit.stderr(),
                    deal.module.ProductionProjectEmission.WARNING_JVM),
                "the pinned JVM warning prints exactly once");
            check(artifactFiles(project.resolve("out-map"))
                    .contains("Main.java"),
                "the explicit --source-map compile publishes its project "
                    + "artifact");
            check(artifactFiles(project.resolve("out-map")).stream()
                    .noneMatch(file -> file.endsWith(".deal.map.json")),
                "the explicit --source-map compile writes no sidecar");

            ProjectOutcome dumpIr = runProductionCli("compile",
                project.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "jvm", "--dump-ir", "--output",
                project.resolve("out-dump").toAbsolutePath().toString());
            check(dumpIr.exitCode() == 0,
                "the --dump-ir-only production compile succeeds: "
                    + dumpIr.stderr());
            check(!dumpIr.stderr().contains("source-map"),
                "a --dump-ir-derived flag prints no warning: "
                    + dumpIr.stderr());

            // The LuaJIT target pins the LuaJIT warning text.
            Path luaProject = Files.createTempDirectory(
                "production-dispatch-map-lua-");
            try {
                write(luaProject, "deal.json", DEAL_JSON_LUA);
                write(luaProject, "src/main.deal", """
                    export function main(): null {
                      return null
                    }
                    """);
                ProjectOutcome lua = runProductionCli("compile",
                    luaProject.resolve("src/main.deal").toAbsolutePath()
                        .toString(),
                    "--source-map", "--output",
                    luaProject.resolve("out-map").toAbsolutePath().toString());
                check(lua.exitCode() == 0,
                    "the explicit --source-map LuaJIT compile succeeds: "
                        + lua.stderr());
                checkEq(1, countOccurrences(lua.stderr(),
                        deal.module.ProductionProjectEmission.WARNING_LUAJIT),
                    "the pinned LuaJIT warning prints exactly once");
                check(artifactFiles(luaProject.resolve("out-map"))
                        .contains("main.lua"),
                    "the LuaJIT --source-map compile publishes its project "
                        + "artifact");
            } finally {
                deleteRecursively(luaProject);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    // =========================================================================
    // 6. The dispatch: every other invocation keeps the harness arm
    // =========================================================================

    private static void testHarnessArmDispatch() throws Exception {
        System.out.println("-- dispatch: every non-release invocation keeps the "
            + "harness arm --");

        Path project = Files.createTempDirectory("production-dispatch-arm-");
        try {
            // A multi-module fixture with a cross-module call: the harness
            // arm routes it LEGACY and publishes per-module artifacts, while
            // the production arm would fail it closed.
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/lib.deal", LIB_SOURCE);
            write(project, "src/main.deal", SYNC_CALL_SOURCE);

            checkHarnessRow(project, "COMMON_SHADOW", commonShadow(), true);
            checkHarnessRow(project, "LEGACY_REGRESSION",
                legacyRegression(), false);
            checkHarnessRow(project, "PUBLIC_BUILD + PRE_ACTIVATION",
                publicBuildPreActivation(), false);
            checkHarnessRow(project,
                "PUBLIC_BUILD + V1_2_ACTIVE + all-SHADOW registry digest",
                publicBuildShadowRegistry(), true);
        } finally {
            deleteRecursively(project);
        }
    }

    private static void checkHarnessRow(Path project, String name,
            CompilerInvocation invocation, boolean expectLegacyArtifacts)
            throws Exception {
        ArmCompile arm = compileWithInvocation(project, "src/main.deal",
            invocation);
        check(arm.success(), name + ": the harness-arm compile succeeds: "
            + arm.orchestrator().diagnostics());
        if (!arm.success()) {
            return;
        }
        CompilationOrchestrator orchestrator = arm.orchestrator();
        check(orchestrator.routePlan() != null
                && !orchestrator.routePlan().hasErrors()
                && orchestrator.routePlan().plan() != null,
            name + ": the harness arm computes the route plan");
        if (expectLegacyArtifacts) {
            check(orchestrator.retainedEmissionCount() >= 1,
                name + ": the harness arm keeps the retained per-module "
                    + "emission (retained="
                    + orchestrator.retainedEmissionCount() + ")");
        }
        check(!CompilationOrchestrator.isProductionInvocation(invocation),
            name + ": the record is not the release-owned production "
                + "invocation");
        Path out = project.resolve("out");
        check(Files.exists(out.resolve("main.lua"))
                && Files.exists(out.resolve("lib.lua")),
            name + ": the harness arm publishes the per-module artifact set: "
                + artifactFiles(out));
        ProcessOutcome run = runProcess(out, "luajit", "main.lua");
        check(run.exitCode() == 0,
            name + ": the retained per-module artifact set runs: exit="
                + run.exitCode() + " output=" + run.output());
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Production Dispatch and Cutover Acceptance "
            + "Tests (ISSUE-0643) ===\n");

        testInvocationPredicate();
        testProductionLuaJitSingleModule();
        testProductionJvmTwoModule();
        testProductionLuaJitTwoModuleSurfaces();
        testConversionOverflowTerminal();
        testAtomicFailureThroughDispatch();
        testFailClosedFamilies();
        testSourceMapDisposition();
        testHarnessArmDispatch();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
