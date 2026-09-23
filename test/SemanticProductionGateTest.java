package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.module.CompilationOrchestrator;
import deal.project.CliOverrides;
import deal.project.ProjectLocator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ModuleRoute;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.RoutePlanResult;
import deal.semantic.ir.ReleaseState;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.lang.reflect.Parameter;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileVisitOption;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

/**
 * The ISSUE-0239 E10 production gate: real post-flip orchestrator
 * compiles through the full production pipeline (ProjectLocator →
 * CompilationOrchestrator) on both retained targets and executes the
 * emitted artifacts through the real toolchains (luajit;
 * {@code javac --release 25 -proc:none} + {@code java}), pinning:
 *
 * <ul>
 *   <li>the production emitter seam — {@code LoweredModuleUnit} +
 *       {@code StructuredBodyTable}, never AST/CheckResult;</li>
 *   <li>the {@code ModuleRoutePlan} selection without fallback — one
 *       semantic/zero retained artifacts for the all-shared
 *       single-module projects, zero semantic/two retained for the
 *       multi-module graph, and the dual-shape plan-time reroute
 *       (never E6005, never a within-run fallback);</li>
 *   <li>the retained {@code DEAL_ERROR_CODE: <code>} terminal contract
 *       (E8004 out of the shared artifact);</li>
 *   <li>the plan-time LEGACY reroute of every named shape without a
 *       shared representation — the adapter-invocation module and the
 *       stored/embedded function-expression shapes (binding, array
 *       literal, table literal) compile through the retained route with
 *       zero semantic/one retained artifact and an all-LEGACY plan
 *       (never E6005, never a within-run fallback);</li>
 *   <li>the SHARED table member read — the emitted {@code __member}
 *       helper resolves present and absent keys identically to
 *       {@code JvmRuntime.Table.read} on both targets and the published
 *       artifacts load and run;</li>
 *   <li>the atomic publication failure preservation — a failing compile
 *       drives the residual public shared-lowering E6005 (the
 *       function-typed table member read, R-FUNCTION-BINDING), publishes
 *       nothing, and preserves the prior artifact set byte-for-byte with
 *       no staging/retired siblings surviving.</li>
 * </ul>
 */
public class SemanticProductionGateTest {

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

    private static void write(Path root, String relative, String content)
            throws IOException {
        Path target = root.resolve(relative);
        Files.createDirectories(target.getParent());
        Files.writeString(target, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (Stream<Path> walk = Files.walk(path, FileVisitOption.values())) {
            walk.sorted(Comparator.reverseOrder()).forEach(p -> {
                try {
                    Files.deleteIfExists(p);
                } catch (IOException ignored) {
                }
            });
        } catch (IOException ignored) {
        }
    }

    private record ProcessOutcome(int exitCode, String output) {
    }

    private static ProcessOutcome runProcess(Path directory, List<String> command)
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

    /** The production compilation path of the gate (E10): ProjectLocator +
     * the context-taking orchestrator constructor with the release-owned
     * record — the same surface the CLI uses. */
    private static CompilationOrchestrator compileProject(Path project,
                                                          String entry,
                                                          String output)
            throws IOException {
        CompilationOrchestrator orchestrator =
            compileProjectAllowingFailure(project, entry, output);
        if (orchestrator.diagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))) {
            throw new IllegalStateException("compile failed: "
                + orchestrator.diagnostics());
        }
        return orchestrator;
    }

    /**
     * One release-owned production compile that returns the orchestrator
     * even when the compile fails (the retargeted production-invocation
     * pins: the project-artifact outcome for a covered fixture, the named
     * fail-closed outcome otherwise; ISSUE-0643 P10 item 1).
     */
    private static CompilationOrchestrator compileProjectAllowingFailure(
            Path project, String entry, String output) throws IOException {
        Path entryFile = project.resolve(entry).toAbsolutePath().normalize();
        ProjectLocator.LocateResult located = ProjectLocator.locate(
            entryFile.toString(), new CliOverrides(null, null));
        if (located.context() == null) {
            throw new IllegalStateException("locate failed: " + located);
        }
        CompilerInvocation invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE,
            ReleaseConfiguration.releaseCapabilityRegistry());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, false, false, false, false, null,
            invocation);
        orchestrator.compile();
        return orchestrator;
    }

    /**
     * One harness-invocation compile of the same fixture (ISSUE-0643 P10
     * item 3): the retained-subject sections keep their route-plan,
     * bytes-exception, and per-module artifact assertions through the
     * harness arm, while the release-owned record's outcome is asserted
     * separately.
     */
    private static CompilationOrchestrator compileHarnessProject(Path project,
                                                                 String entry,
                                                                 String output)
            throws IOException {
        Path entryFile = project.resolve(entry).toAbsolutePath().normalize();
        ProjectLocator.LocateResult located = ProjectLocator.locate(
            entryFile.toString(), new CliOverrides(null, null));
        if (located.context() == null) {
            throw new IllegalStateException("locate failed: " + located);
        }
        CompilerInvocation invocation = ConformanceHarnessMetadata.invocation(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, false, false, false, false, null,
            invocation);
        boolean success = orchestrator.compile();
        if (!success) {
            throw new IllegalStateException("harness compile failed: "
                + orchestrator.diagnostics());
        }
        return orchestrator;
    }

    /**
     * The production-invocation fail-closed assertion of one fixture whose
     * construct is owned by a later slice (ISSUE-0643 P10 item 2): the
     * release-owned compile fails with E6005 SHARED_EMITTER_COVERAGE or the
     * named construct rule and stages no artifact.
     */
    private static void checkProductionFailClosed(Path project, String entry,
            String output, String expectedRule, String context)
            throws IOException {
        CompilationOrchestrator production =
            compileProjectAllowingFailure(project, entry, output);
        check(production.diagnostics().stream().anyMatch(d ->
                "E6005".equals(d.code())
                    && d.message().contains(expectedRule)),
            context + ": the release-owned production invocation fails closed "
                + "with E6005 " + expectedRule + ": "
                + production.diagnostics());
        check(!Files.exists(project.resolve(output)),
            context + ": the production failure stages no artifact");
    }

    /**
     * The production-invocation emitted-and-staged assertion of one
     * fixture the realized production arm covers (ISSUE-0654): the
     * release-owned compile succeeds, emits exactly one project artifact,
     * retains none, and publishes its artifact set.
     */
    private static void checkProductionEmits(Path project, String entry,
            String output, String context) throws IOException {
        CompilationOrchestrator production =
            compileProjectAllowingFailure(project, entry, output);
        check(production.diagnostics().isEmpty(),
            context + ": the release-owned production invocation compiles: "
                + production.diagnostics());
        check(production.semanticEmissionCount() == 1
                && production.retainedEmissionCount() == 0,
            context + ": the production compile emits one project artifact "
                + "and no retained artifact: semantic="
                + production.semanticEmissionCount() + " retained="
                + production.retainedEmissionCount());
        check(Files.exists(project.resolve(output)),
            context + ": the production compile publishes its artifact set");
    }

    private static void testEmitterSeam() {
        System.out.println("-- Production emitter seam: unit + table, never AST/CheckResult --");

        Method luaEmit = null;
        for (Method method : LuaEmitterClass().getDeclaredMethods()) {
            if (method.getName().equals("emitProductionModule")) {
                luaEmit = method;
            }
        }
        Method jvmEmit = null;
        for (Method method : JvmEmitterClass().getDeclaredMethods()) {
            if (method.getName().equals("emitProductionModule")) {
                jvmEmit = method;
            }
        }
        check(luaEmit != null && jvmEmit != null,
            "both shared emitters publish a production entry point");
        for (Method method : new Method[] {luaEmit, jvmEmit}) {
            if (method == null) {
                continue;
            }
            boolean hasUnit = false;
            boolean hasTable = false;
            for (Parameter parameter : method.getParameters()) {
                if (parameter.getType()
                        == deal.semantic.ir.LoweredModuleUnit.class) {
                    hasUnit = true;
                }
                if (parameter.getType()
                        == deal.semantic.ir.StructuredBodyTable.class) {
                    hasTable = true;
                }
                if (parameter.getType().getName().startsWith("deal.ast.")
                        || parameter.getType().getName().startsWith("deal.checker.")) {
                    fail(method.getDeclaringClass().getSimpleName()
                        + ".emitProductionModule takes AST/checker state: "
                        + parameter.getType().getName());
                }
            }
            check(hasUnit && hasTable,
                method.getDeclaringClass().getSimpleName()
                    + ".emitProductionModule consumes the validated unit + table");
        }
    }

    private static Class<?> LuaEmitterClass() {
        return deal.codegen.lua.LuaSemanticEmitter.class;
    }

    private static Class<?> JvmEmitterClass() {
        return deal.codegen.jvm.JvmSemanticEmitter.class;
    }

    private static final String DEAL_JSON_LUA =
        "{\n  \"languageVersion\": \"1.2\",\n  \"moduleRoots\": [\"src\"],\n"
            + "  \"output\": \"out\",\n  \"backend\": \"luajit\"\n}\n";
    private static final String DEAL_JSON_JVM =
        "{\n  \"languageVersion\": \"1.2\",\n  \"moduleRoots\": [\"src\"],\n"
            + "  \"output\": \"out\",\n  \"backend\": \"jvm\"\n}\n";

    private static final String ADD_MAIN_SOURCE =
        "export function add(x: int, y: int): int {\n  return x + y\n}\n\n"
            + "export function main(): null {\n  return null\n}\n";

    private static final String OVERFLOW_SOURCE =
        "export function main(): null {\n  let x: int = 2147483647 + 1\n"
            + "  return null\n}\n";

    private static final String TABLE_MEMBER_READ_SOURCE =
        "export function main(): null {\n  let t: table = { a: 1 }\n"
            + "  let x: int = t.a\n  return null\n}\n";

    private static final String BYTES_SOURCE =
        "export function test_bytes_length(): null {\n"
            + "  let n: int = 3;\n"
            + "  let b: bytes = bytes(n);\n"
            + "  if (b.length !== 3) {\n"
            + "    throw { code: \"TEST_FAIL\", message: \"bytes: length mismatch\" };\n"
            + "  }\n"
            + "  return null;\n"
            + "}\n"
            + "export function main(): null {\n  return null\n}\n";

    private static void testAllSharedLuaJit() throws Exception {
        System.out.println("-- All-shared LuaJIT: semantic IR artifact runs (success + E8004) --");

        Path project = Files.createTempDirectory("deal-e10-lua-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", ADD_MAIN_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(project, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "one semantic/zero retained artifacts: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");

            Path out = project.resolve("out");
            check(Files.isRegularFile(out.resolve("main.lua")),
                "the semantic artifact main.lua is staged and published");
            ProcessOutcome run = runProcess(out, List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT artifact runs clean: exit=" + run.exitCode()
                    + " output=" + run.output().replace("\n", "\\n"));

            Path overflowProject = Files.createTempDirectory("deal-e10-lua-ovf-");
            try {
                write(overflowProject, "deal.json", DEAL_JSON_LUA);
                write(overflowProject, "src/main.deal", OVERFLOW_SOURCE);
                CompilationOrchestrator overflow =
                    compileProject(overflowProject, "src/main.deal", "out");
                check(overflow.semanticEmissionCount() == 1
                        && overflow.retainedEmissionCount() == 0,
                    "the overflow project emits exactly one semantic artifact");
                ProcessOutcome overflowRun = runProcess(
                    overflowProject.resolve("out"), List.of("luajit", "main.lua"));
                check(overflowRun.exitCode() == 1
                        && overflowRun.output().contains("DEAL_ERROR_CODE: E8004"),
                    "the shared LuaJIT artifact publishes the retained DEAL_ERROR_CODE "
                        + "terminal: exit=" + overflowRun.exitCode() + " output="
                        + overflowRun.output().replace("\n", "\\n"));
            } finally {
                deleteRecursively(overflowProject);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testAllSharedJvm() throws Exception {
        System.out.println("-- All-shared JVM: semantic IR artifact compiles and runs (success + E8004) --");

        Path project = Files.createTempDirectory("deal-e10-jvm-");
        try {
            write(project, "deal.json", DEAL_JSON_JVM);
            write(project, "src/main.deal", ADD_MAIN_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(project, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "one semantic/zero retained artifacts: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());

            Path out = project.resolve("out");
            check(Files.isRegularFile(out.resolve("Main.java")),
                "the semantic artifact Main.java is staged and published");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(project, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM artifact compiles: " + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM artifact runs clean: exit=" + run.exitCode()
                        + " output=" + run.output().replace("\n", "\\n"));
            }

            Path overflowProject = Files.createTempDirectory("deal-e10-jvm-ovf-");
            try {
                write(overflowProject, "deal.json", DEAL_JSON_JVM);
                write(overflowProject, "src/main.deal", OVERFLOW_SOURCE);
                CompilationOrchestrator overflow =
                    compileProject(overflowProject, "src/main.deal", "out");
                check(overflow.semanticEmissionCount() == 1
                        && overflow.retainedEmissionCount() == 0,
                    "the overflow project emits exactly one semantic artifact");
                Path overflowOut = overflowProject.resolve("out");
                ProcessOutcome overflowJavac = runProcess(overflowProject, List.of(
                    "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                    "-d", overflowOut.toString(),
                    overflowOut.resolve("Main.java").toString()));
                if (overflowJavac.exitCode() == 0) {
                    ProcessOutcome overflowRun = runProcess(overflowOut, List.of(
                        "java", "-cp", buildCp + File.pathSeparator + overflowOut,
                        "Main"));
                    check(overflowRun.exitCode() == 1
                            && overflowRun.output().contains("DEAL_ERROR_CODE: E8004"),
                        "the shared JVM artifact publishes the retained DEAL_ERROR_CODE "
                            + "terminal: exit=" + overflowRun.exitCode() + " output="
                            + overflowRun.output().replace("\n", "\\n"));
                } else {
                    fail("the overflow shared JVM artifact compiles: "
                        + overflowJavac.output().replace("\n", "\\n"));
                }
            } finally {
                deleteRecursively(overflowProject);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testSharedTableMemberReadRuns() throws Exception {
        System.out.println("-- SHARED table member read: the emitted __member helper "
            + "runs on both targets --");

        // The cycle-2 critical shape: any MEMBER_READ references the
        // prelude helper __member, so a program reading a table field
        // publishes an artifact that runs clean (never a nil-global
        // crash). Present-key reads yield the stored value on both
        // targets, exactly JvmRuntime.Table.read's split.
        Path project = Files.createTempDirectory("deal-e10-tmember-lua-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal", TABLE_MEMBER_READ_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(project, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the table-member-read module emits one semantic/zero retained "
                    + "artifacts: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            ProcessOutcome run = runProcess(project.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT table-member-read artifact runs clean: exit="
                    + run.exitCode() + " output=" + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(project);
        }

        Path jvmProject = Files.createTempDirectory("deal-e10-tmember-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", TABLE_MEMBER_READ_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the JVM table-member-read module emits one semantic/zero retained "
                    + "artifacts: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM table-member-read artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM table-member-read artifact runs clean: exit="
                        + run.exitCode() + " output=" + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }
    }

    private static void testRouteSelectionWithoutFallback() throws Exception {
        System.out.println("-- Route selection: the production project emission and the "
            + "retained harness route --");

        Path project = Files.createTempDirectory("deal-e10-routes-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/lib.deal",
                "export function value(): int {\n  return 42\n}\n");
            write(project, "src/main.deal",
                "import * as lib from \"./lib\"\n\n"
                    + "export function probe(): int {\n  return lib.value()\n}\n\n"
                    + "export function main(): null {\n  return null\n}\n");
            // ISSUE-0654: the release-owned production invocation realizes
            // the cross-module call through the callee unit's
            // EXTERNAL_ENTRY inside the one project artifact, so the
            // multi-module closure compiles and stages its one project
            // artifact.
            checkProductionEmits(project, "src/main.deal", "out",
                "the multi-module cross-module call");

            // The retained all-LEGACY multi-module route stays the harness
            // subject: zero semantic/two retained artifacts, an all-LEGACY
            // plan, and the retained artifact set runs.
            CompilationOrchestrator orchestrator =
                compileHarnessProject(project, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 2,
                "the multi-module graph emits zero semantic/two retained artifacts: "
                    + "semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                "the multi-module plan is all-LEGACY at plan time (never E6005, "
                    + "never a within-run fallback)");
            ProcessOutcome run = runProcess(project.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0,
                "the retained multi-module artifact set runs: exit=" + run.exitCode()
                    + " output=" + run.output().replace("\n", "\\n"));

            Path dualProject = Files.createTempDirectory("deal-e10-dual-");
            try {
                write(dualProject, "deal.json", DEAL_JSON_LUA);
                write(dualProject, "src/main.deal",
                    "export function add(x: int, y: int): int {\n  return x + y\n}\n\n"
                        + "export function main(): null {\n  add(2, 3)\n"
                        + "  return null\n}\n");
                // ISSUE-0654: the dual-shape module (an exported function
                // called from source) compiles through the release-owned
                // production invocation — the source call runs the
                // exported function's recorded EXTERNAL_ENTRY (the closed
                // CALL(EXTERNAL) SHARED_BODY cell) — and stages its one
                // project artifact instead of claiming a second invocation
                // shape.
                checkProductionEmits(dualProject, "src/main.deal", "out",
                    "the dual-shape module");
            } finally {
                deleteRecursively(dualProject);
            }
        } finally {
            deleteRecursively(project);
        }
    }

    private static void testAdapterShapeReroutesLegacy() throws Exception {
        System.out.println("-- Plan-time reroute: shapes without a shared representation "
            + "are LEGACY, never E6005 --");

        // The review-verified corpus shapes (directive lines stripped) plus
        // the adapter-invocation shape and the stored/embedded
        // function-expression shapes: every module without a shared
        // representation claims its owning capability at plan time, so F4
        // rule 4 reroutes it LEGACY — zero semantic/one retained artifact,
        // an all-LEGACY plan, and the retained v1.2 route compiles and
        // runs the program as before (the parent epic's "unsupported
        // capabilities choose legacy and are not errors").
        Map<String, String> fixtures = Map.of(
            "adapter", "export function main(): null {\n"
                + "  let f: (a: int, b: int) => int = one\n"
                + "  f(1, 2)\n"
                + "  return null\n"
                + "}\n"
                + "function one(x: int): int {\n  return x\n}\n",
            "bytes-length", "export function test_bytes_length(): null {\n"
                + "  let n: int = 3;\n"
                + "  let b: bytes = bytes(n);\n"
                + "  if (b.length !== 3) {\n"
                + "    throw { code: \"TEST_FAIL\", message: \"bytes: length mismatch\" };\n"
                + "  }\n"
                + "  return null;\n"
                + "}\n"
                + "export function main(): null {\n  return null\n}\n",
            "direct-recursion", "export function test_direct_recursion(): int {\n"
                + "  let downCalls: int = 0;\n"
                + "  function down(n: int): int {\n"
                + "    downCalls = downCalls + 1;\n"
                + "    if (n === 0) { return 0; }\n"
                + "    return down(n - 1);\n"
                + "  }\n"
                + "  let result: int = down(8);\n"
                + "  return 0;\n"
                + "}\n"
                + "export function main(): null {\n  return null\n}\n",
            "closure-capture", "export function test_closure(): int {\n"
                + "  let x: int = 1;\n"
                + "  let f: () => int = function(): int { return x; };\n"
                + "  x = 2;\n"
                + "  let result: int = f();\n"
                + "  if (result !== 2) {\n"
                + "    throw { code: \"TEST_FAIL\", message: \"closure capture result mismatch after x = 2\" };\n"
                + "  }\n"
                + "  return result;\n"
                + "}\n"
                + "export function main(): null {\n  return null\n}\n",
            // The cycle-2 stored/embedded function-expression shapes: a
            // closure stored in a binding initializer, an array literal
            // element, or a table literal field whose body has no direct
            // invocation — its RETURN boundary names no invocation shape
            // (R-BOUNDARY-TRIPLE), so the scan arm claims CALLS and F4
            // rule 4 reroutes the module LEGACY at plan time (never
            // E6005, never a within-run fallback).
            "stored-closure-binding", "export function main(): null {\n"
                + "  let g: () => int = function(): int { return 7 }\n"
                + "  return null\n"
                + "}\n",
            "stored-closure-array", "export function main(): null {\n"
                + "  let fs: (() => int)[] = [function(): int { return 7 }]\n"
                + "  return null\n"
                + "}\n",
            "stored-closure-table", "export function main(): null {\n"
                + "  let t: table = { f: function(): int { return 7 } }\n"
                + "  return null\n"
                + "}\n");
        for (Map.Entry<String, String> fixture : fixtures.entrySet()) {
            Path project = Files.createTempDirectory(
                "deal-e10-reroute-" + fixture.getKey() + "-");
            try {
                write(project, "deal.json", DEAL_JSON_LUA);
                write(project, "src/main.deal", fixture.getValue());
                // ISSUE-0643 P10 item 2, retargeted by ISSUE-0619: the
                // release-owned production invocation's outcome for this
                // fixture — the named fail-closed rule for a later-slice
                // construct, or the one project artifact for the shapes the
                // production lowering covers (the stored/embedded function
                // expressions and the builtin Error construction of the
                // closure-capture fixture, whose only remaining blocker was
                // the builtin Error construct).
                boolean productionCovered = fixture.getKey().startsWith("stored-closure")
                    || fixture.getKey().equals("closure-capture");
                if (productionCovered) {
                    CompilationOrchestrator production =
                        compileProject(project, "src/main.deal", "out");
                    check(production.semanticEmissionCount() == 1
                            && production.retainedEmissionCount() == 0,
                        fixture.getKey() + ": the production arm emits one project "
                            + "artifact: semantic="
                            + production.semanticEmissionCount() + " retained="
                            + production.retainedEmissionCount());
                    check(production.routePlan() == null,
                        fixture.getKey() + ": the production arm consults no "
                            + "route plan");
                    Path productionOut = project.resolve("out");
                    ProcessOutcome productionRun = runProcess(productionOut,
                        List.of("luajit", "main.lua"));
                    check(productionRun.exitCode() == 0,
                        fixture.getKey() + ": the production project artifact "
                            + "runs: exit=" + productionRun.exitCode()
                            + " output="
                            + productionRun.output().replace("\n", "\\n"));
                } else {
                    checkProductionFailClosed(project, "src/main.deal", "out",
                        "CONSTRUCT_UNLOWERED", fixture.getKey());
                }
                // The retained plan-time route stays the harness subject.
                CompilationOrchestrator orchestrator =
                    compileHarnessProject(project, "src/main.deal", "out");
                check(orchestrator.semanticEmissionCount() == 0
                        && orchestrator.retainedEmissionCount() == 1,
                    fixture.getKey() + ": the module reroutes LEGACY at plan time: "
                        + "semantic=" + orchestrator.semanticEmissionCount()
                        + " retained=" + orchestrator.retainedEmissionCount());
                RoutePlanResult plan = orchestrator.routePlan();
                check(plan != null && !plan.hasErrors() && plan.plan() != null
                        && plan.plan().entries().values().stream()
                            .allMatch(route -> route == ModuleRoute.LEGACY),
                    fixture.getKey() + ": the plan is all-LEGACY at plan time "
                        + "(never E6005, never a within-run fallback)");
                ProcessOutcome run = runProcess(project.resolve("out"),
                    List.of("luajit", "main.lua"));
                check(run.exitCode() == 0,
                    fixture.getKey() + ": the retained artifact set runs: exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            } finally {
                deleteRecursively(project);
            }
        }
    }

    private static void testBytesBearingRetainedRoute() throws Exception {
        System.out.println("-- Rule 2b (ISSUE-0574): the bytes-bearing route stays "
            + "the harness subject; the release-owned invocation fails the bytes "
            + "construct closed --");

        // LuaJIT: the release-owned production invocation fails the
        // bytes-bearing module closed with its named construct rule and
        // stages nothing (the bytes realization belongs to the bytes
        // child); the harness invocation keeps the retained route report
        // (all-LEGACY, the recorded bytes exception, the bytesBearing
        // manifest row, and the retained artifact running as before).
        Path luaProject = Files.createTempDirectory("deal-e10-bytes-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(luaProject, "src/main.deal", "out",
                "CONSTRUCT_UNLOWERED", "the bytes-bearing LuaJIT module");

            CompilationOrchestrator orchestrator =
                compileHarnessProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing LuaJIT module emits zero semantic/one retained "
                    + "artifact: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                "the bytes-bearing LuaJIT plan is all-LEGACY at plan time "
                    + "(never E6005, never a within-run fallback)");
            if (plan != null && !plan.hasErrors() && plan.plan() != null) {
                check(plan.plan().bytesExceptions().size() == 1
                        && plan.plan().bytesExceptions().stream()
                            .anyMatch(id -> id.path().equals("main")),
                    "the route report records the bytes exception for module "
                        + "main: " + plan.plan().bytesExceptions());
                check(plan.plan().canonicalText().contains("\"bytesExceptions\""),
                    "the plan's canonical route report carries the "
                        + "bytesExceptions key");
            }
            check(orchestrator.diagnostics().isEmpty(),
                "no E6005 under the harness arm (rule 2b is never an error): "
                    + orchestrator.diagnostics());
            RequirementManifestResult manifests =
                orchestrator.requirementManifests();
            check(manifests != null && !manifests.hasErrors()
                    && manifests.manifests().stream().anyMatch(manifest ->
                        manifest.moduleId().path().equals("main")
                            && manifest.bytesBearing()),
                "the production manifest marks the bytes-bearing module "
                    + "(bytesBearing=true)");
            ProcessOutcome run = runProcess(luaProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0,
                "the retained LuaJIT bytes artifact runs as before: exit="
                    + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // JVM: the same split — the release-owned production invocation
        // fails the bytes construct closed, while the harness artifact
        // compiles under javac --release 25 -proc:none and runs under java
        // as before.
        Path jvmProject = Files.createTempDirectory("deal-e10-bytes-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(jvmProject, "src/main.deal", "out",
                "CONSTRUCT_UNLOWERED", "the bytes-bearing JVM module");

            CompilationOrchestrator orchestrator =
                compileHarnessProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing JVM module emits zero semantic/one retained "
                    + "artifact: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && plan.plan().bytesExceptions().size() == 1
                    && plan.plan().bytesExceptions().stream()
                        .anyMatch(id -> id.path().equals("main")),
                "the bytes-bearing JVM plan is all-LEGACY and records the bytes "
                    + "exception: " + (plan == null ? "null" : plan.plan()));
            check(orchestrator.diagnostics().isEmpty(),
                "no E6005 on the JVM retained route: "
                    + orchestrator.diagnostics());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the retained JVM bytes artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the retained JVM bytes artifact runs as before: exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }
    }

    private static final String OPTIONAL_READ_SOURCE =
        "export function test_optional_read(): null {\n"
            + "  let t: table = { a: 1 }\n"
            + "  let x: int | null = t.a\n"
            + "  let y: int | null = t.b\n"
            + "  return null;\n"
            + "}\n"
            + "export function main(): null { return null }\n";

    private static void testStep1CutoverPromotion() throws Exception {
        System.out.println("-- Step-1 cutover: CONTAINERS_AND_STRINGS promoted; a "
            + "container/optional-read module routes SHARED and runs on both targets --");

        // The release registry carries the step-1 promotion in the pinned
        // capability order (CONTAINERS_AND_STRINGS after SIGNED_INT32,
        // LUAJIT before JVM) with a recomputed digest.
        CapabilityRegistry registry = ReleaseConfiguration.releaseCapabilityRegistry();
        check(registry.state(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && registry.state(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes CONTAINERS_AND_STRINGS for LUAJIT and JVM");
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        check(promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT))
                > promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                    deal.semantic.Target.JVM))
                && promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.LUAJIT))
                    < promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                        deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                        deal.semantic.Target.JVM)),
            "the step-1 promotion sits in the pinned capability order with LUAJIT "
                + "before JVM");

        // LuaJIT: the production PUBLIC_BUILD + V1_2_ACTIVE compile of a
        // container/optional-read module (no stdlib call, no user call,
        // no bytes) routes SHARED, emits exactly one semantic artifact,
        // and the OPTIONAL_READ envelope executes under the real toolchain.
        Path luaProject = Files.createTempDirectory("deal-e10-optional-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", OPTIONAL_READ_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the optional-read LuaJIT module emits one semantic/zero retained "
                    + "artifact: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            ProcessOutcome run = runProcess(luaProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT optional-read artifact runs clean (the "
                    + "OPTIONAL_READ envelope executes): exit=" + run.exitCode()
                    + " output=" + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // JVM: the same production compile routes SHARED; the artifact
        // compiles under javac --release 25 -proc:none and runs under java.
        Path jvmProject = Files.createTempDirectory("deal-e10-optional-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", OPTIONAL_READ_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the optional-read JVM module emits one semantic/zero retained "
                    + "artifact: semantic=" + orchestrator.semanticEmissionCount()
                    + " retained=" + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM optional-read artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM optional-read artifact runs clean (the "
                        + "OPTIONAL_READ envelope executes): exit=" + run.exitCode()
                        + " output=" + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }
    }

    private static void testStep1RegistryDigestRecomputation() {
        System.out.println("-- Step-1 registry digest: recomputed over its own entries; "
            + "differs from the pre-step-1 (E12) release digest --");

        // The pre-step-1 release registry: the committed E12 promotion list
        // (FOUNDATION_VALUES and SIGNED_INT32 for both targets) composed
        // from the all-SHADOW release default through the single withState
        // transition surface — the exact prior release state the step-1
        // promotion extends.
        CapabilityRegistry preStep1 = CapabilityRegistry.releaseRegistry()
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String preStep1Hash = preStep1.capabilityRegistryHash();
        check(preStep1.state(
                deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.SHADOW
                && preStep1.state(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.SHADOW,
            "the pre-step-1 registry keeps CONTAINERS_AND_STRINGS SHADOW for "
                + "both targets");

        // The step-1 release registry: the committed E12 pairs plus the
        // step-1 cutover promotion (CONTAINERS_AND_STRINGS for both
        // targets) composed from the all-SHADOW release default through
        // the single withState transition surface — the exact prior
        // release state the step-2 promotion (ISSUE-0577) extends. The
        // step-2 live registry is derived in the step-2 digest test, so
        // this historical pin stays truthful at every later cutover step.
        CapabilityRegistry step1 = preStep1
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String step1Hash = step1.capabilityRegistryHash();

        // The promotion is a real registry transition: the digest over the
        // promoted entries recomputes and differs from the prior release
        // digest.
        check(!step1Hash.equals(preStep1Hash),
            "the step-1 release digest differs from the pre-step-1 (E12) "
                + "release digest: " + preStep1Hash + " -> " + step1Hash);

        // The step-1 digest is the canonical recomputation over the
        // registry's own entries — never a hand-rolled constant.
        check(step1Hash.equals(deal.semantic.ir.CanonicalJson.sha256Hex(
                deal.semantic.ir.CanonicalJson.serializeBytes(step1.canonicalJson()))),
            "the step-1 digest equals the canonical SHA-256 recomputation over "
                + "the registry's own canonical JSON");

        // The transition changes exactly the two step-1 entries: the
        // registries differ in exactly two entries, both
        // CONTAINERS_AND_STRINGS carrying PROMOTED; every other entry is
        // byte-identical.
        List<CapabilityRegistry.Entry> preEntries = preStep1.entries();
        List<CapabilityRegistry.Entry> stepEntries = step1.entries();
        check(preEntries.size() == stepEntries.size()
                && stepEntries.size() == CapabilityRegistry.ENTRY_COUNT,
            "both registries keep the closed " + CapabilityRegistry.ENTRY_COUNT
                + "-entry cross product");
        int differing = 0;
        for (int i = 0; i < preEntries.size() && i < stepEntries.size(); i++) {
            CapabilityRegistry.Entry pre = preEntries.get(i);
            CapabilityRegistry.Entry step = stepEntries.get(i);
            if (pre.capability() != step.capability()
                    || pre.target() != step.target()
                    || pre.state() != step.state()) {
                differing++;
            }
        }
        check(differing == 2
                && step1.state(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && step1.state(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the step-1 registry differs from the pre-step-1 registry in exactly "
                + "the two CONTAINERS_AND_STRINGS x LUAJIT/JVM entries, both "
                + "carrying PROMOTED (differing=" + differing + ")");

        // The E12 pairs stay PROMOTED and every other capability stays
        // SHADOW: the step-1 promotion flips nothing else.
        boolean promotedExactly = true;
        boolean shadowExactly = true;
        for (CapabilityRegistry.Entry entry : step1.entries()) {
            boolean step1Capability = entry.capability()
                    == deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.SIGNED_INT32;
            if (step1Capability) {
                promotedExactly &= entry.state() == CapabilityRegistry.State.PROMOTED;
            } else {
                shadowExactly &= entry.state() == CapabilityRegistry.State.SHADOW;
            }
        }
        check(promotedExactly && shadowExactly,
            "the step-1 registry promotes exactly FOUNDATION_VALUES, SIGNED_INT32, "
                + "and CONTAINERS_AND_STRINGS for both targets; every other "
                + "capability stays SHADOW");

        // Anti-hollow: re-deriving the step-1 promotion list prefix (the
        // first six release promotions) through the withState surface
        // reproduces the step-1 release digest — the step-1 registry is
        // exactly the composed prefix, never a hand-written digest
        // constant.
        CapabilityRegistry recomposed = CapabilityRegistry.releaseRegistry();
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        for (int i = 0; i < 6 && i < promotions.size(); i++) {
            ReleaseConfiguration.ReleasePromotion promotion = promotions.get(i);
            recomposed = recomposed.withState(promotion.capability(),
                promotion.target(), CapabilityRegistry.State.PROMOTED);
        }
        check(recomposed.capabilityRegistryHash().equals(step1Hash),
            "re-deriving the step-1 promotion list prefix through withState "
                + "reproduces the step-1 release registry digest");
        check(!recomposed.capabilityRegistryHash().equals(preStep1Hash),
            "the recomposed step-1 digest still differs from the pre-step-1 "
                + "digest (the prior release digest is left behind)");
    }

    private static final String DESCRIPTOR_BOUNDARY_SOURCE =
        "export function main(): null {\n"
            + "  let t: table = { a: 1, n: null }\n"
            + "  let x: int | null = t.a\n"
            + "  let w: int | null = t.n\n"
            + "  let y: int | null = t.b\n"
            + "  return null;\n"
            + "}\n";

    private static final String DESCRIPTOR_BOUNDARY_FAIL_SOURCE =
        "export function main(): null {\n"
            + "  let t: table = { a: \"s\" }\n"
            + "  let x: int | null = t.a\n"
            + "  return null;\n"
            + "}\n";

    private static void testStep2CutoverPromotion() throws Exception {
        System.out.println("-- Step-2 cutover: DESCRIPTORS promoted; descriptor-boundary "
            + "modules route SHARED and the BOUNDARY emission runs on both targets --");

        // The release registry carries the step-2 promotion in the pinned
        // capability order (DESCRIPTORS after CONTAINERS_AND_STRINGS,
        // LUAJIT before JVM) with a recomputed digest.
        CapabilityRegistry registry = ReleaseConfiguration.releaseCapabilityRegistry();
        check(registry.state(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && registry.state(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes DESCRIPTORS for LUAJIT and JVM");
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        check(promotions.size() == 14,
            "the release promotion list carries exactly the E12, step-1, "
                + "step-2, step-3, step-4, and step-5 pairs (14 entries); got "
                + promotions.size());
        check(promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT))
                > promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                    deal.semantic.Target.JVM))
                && promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.LUAJIT))
                    < promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                        deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                        deal.semantic.Target.JVM)),
            "the step-2 promotion sits in the pinned capability order with LUAJIT "
                + "before JVM");

        // LuaJIT, passing descriptor boundaries: the production
        // PUBLIC_BUILD + V1_2_ACTIVE compile of a descriptor-exercising
        // module (present value validated, present null, missing key —
        // the descriptor-kind rule's optional-read cell) routes SHARED,
        // emits exactly one semantic artifact, and the BOUNDARY runtime
        // validation is realized in the shared artifact (__bcheck) and
        // executes under the real toolchain.
        Path luaProject = Files.createTempDirectory("deal-e10-desc-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", DESCRIPTOR_BOUNDARY_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the descriptor-boundary LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            Path out = luaProject.resolve("out");
            check(Files.readString(out.resolve("main.lua"))
                    .contains("__bcheck"),
                "the shared LuaJIT artifact realizes the BOUNDARY runtime "
                    + "validation (__bcheck) — never a stripped descriptor");
            ProcessOutcome run = runProcess(out, List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT descriptor-boundary artifact runs clean (the "
                    + "BOUNDARY emission validates present/present-null/missing): "
                    + "exit=" + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // LuaJIT, failing descriptor boundary: a wrong-kind present value
        // fails the BOUNDARY validation inside the emitted artifact — the
        // runtime E8001 terminal proves the descriptor boundary executes
        // (anti-hollow: a skipped boundary would exit 0).
        Path luaFailProject = Files.createTempDirectory("deal-e10-desc-lua-fail-");
        try {
            write(luaFailProject, "deal.json", DEAL_JSON_LUA);
            write(luaFailProject, "src/main.deal", DESCRIPTOR_BOUNDARY_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the wrong-kind descriptor module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            ProcessOutcome run = runProcess(luaFailProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 1
                    && run.output().contains("DEAL_ERROR_CODE: E8001"),
                "the shared LuaJIT artifact validates the wrong-kind value at "
                    + "the boundary and publishes DEAL_ERROR_CODE: E8001: exit="
                    + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaFailProject);
        }

        // JVM, passing descriptor boundaries: the same production compile
        // routes SHARED; the artifact compiles under javac --release 25
        // -proc:none and runs under java.
        Path jvmProject = Files.createTempDirectory("deal-e10-desc-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", DESCRIPTOR_BOUNDARY_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the descriptor-boundary JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM descriptor-boundary artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM descriptor-boundary artifact runs clean (the "
                        + "BOUNDARY emission validates present/present-null/missing): "
                        + "exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }

        // JVM, failing descriptor boundary: the emitted artifact validates
        // the wrong-kind value at the boundary and publishes E8001.
        Path jvmFailProject = Files.createTempDirectory("deal-e10-desc-jvm-fail-");
        try {
            write(jvmFailProject, "deal.json", DEAL_JSON_JVM);
            write(jvmFailProject, "src/main.deal", DESCRIPTOR_BOUNDARY_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the wrong-kind descriptor JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmFailProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmFailProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E8001"),
                    "the shared JVM artifact validates the wrong-kind value at "
                        + "the boundary and publishes DEAL_ERROR_CODE: E8001: "
                        + "exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            } else {
                fail("the wrong-kind descriptor JVM artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmFailProject);
        }

        // The bytes guard holds through the step-2 promotion: a
        // bytes-bearing module stays on the retained route (rule 2b beats
        // rule 4) with the bytes exception recorded — the T1/T3 state the
        // CONTAINERS_AND_STRINGS promotion established is untouched by the
        // DESCRIPTORS promotion.
        Path bytesProject = Files.createTempDirectory("deal-e10-desc-bytes-");
        try {
            write(bytesProject, "deal.json", DEAL_JSON_LUA);
            write(bytesProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(bytesProject, "src/main.deal",
                "out", "CONSTRUCT_UNLOWERED",
                "the bytes-bearing module (a later-slice promotion check)");
            CompilationOrchestrator orchestrator =
                compileHarnessProject(bytesProject, "src/main.deal",
                    "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing module still emits zero semantic/one retained "
                    + "artifact after the DESCRIPTORS promotion: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && plan.plan().bytesExceptions().size() == 1,
                "the bytes-bearing plan stays all-LEGACY with the bytes "
                    + "exception recorded (rule 2b beats rule 4): "
                    + (plan == null ? "null" : plan.plan()));
        } finally {
            deleteRecursively(bytesProject);
        }
    }

    private static void testStep2RegistryDigestRecomputation() {
        System.out.println("-- Step-2 registry digest: recomputed over its own entries; "
            + "differs from the post-step-1 release digest --");

        // The post-step-1 release registry: the committed E12 pairs plus
        // the step-1 cutover promotion (CONTAINERS_AND_STRINGS for both
        // targets) composed from the all-SHADOW release default through
        // the single withState transition surface — the exact prior
        // release state the step-2 promotion extends.
        CapabilityRegistry postStep1 = CapabilityRegistry.releaseRegistry()
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String postStep1Hash = postStep1.capabilityRegistryHash();
        check(postStep1.state(
                deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.SHADOW
                && postStep1.state(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.SHADOW,
            "the post-step-1 registry keeps DESCRIPTORS SHADOW for both targets");

        CapabilityRegistry step2 = postStep1
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String step2Hash = step2.capabilityRegistryHash();

        // The promotion is a real registry transition: the digest over the
        // promoted entries recomputes and differs from the prior release
        // digest.
        check(!step2Hash.equals(postStep1Hash),
            "the step-2 release digest differs from the post-step-1 release "
                + "digest: " + postStep1Hash + " -> " + step2Hash);

        // The step-2 digest is the canonical recomputation over the
        // registry's own entries — never a hand-rolled constant.
        check(step2Hash.equals(deal.semantic.ir.CanonicalJson.sha256Hex(
                deal.semantic.ir.CanonicalJson.serializeBytes(step2.canonicalJson()))),
            "the step-2 digest equals the canonical SHA-256 recomputation over "
                + "the registry's own canonical JSON");

        // The transition changes exactly the two step-2 entries: the
        // registries differ in exactly two entries, both DESCRIPTORS
        // carrying PROMOTED; every other entry is byte-identical.
        List<CapabilityRegistry.Entry> preEntries = postStep1.entries();
        List<CapabilityRegistry.Entry> stepEntries = step2.entries();
        check(preEntries.size() == stepEntries.size()
                && stepEntries.size() == CapabilityRegistry.ENTRY_COUNT,
            "both registries keep the closed " + CapabilityRegistry.ENTRY_COUNT
                + "-entry cross product");
        int differing = 0;
        for (int i = 0; i < preEntries.size() && i < stepEntries.size(); i++) {
            CapabilityRegistry.Entry pre = preEntries.get(i);
            CapabilityRegistry.Entry step = stepEntries.get(i);
            if (pre.capability() != step.capability()
                    || pre.target() != step.target()
                    || pre.state() != step.state()) {
                differing++;
            }
        }
        check(differing == 2
                && step2.state(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && step2.state(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the step-2 registry differs from the post-step-1 registry in exactly "
                + "the two DESCRIPTORS x LUAJIT/JVM entries, both carrying "
                + "PROMOTED (differing=" + differing + ")");

        // The E12, step-1, and step-2 pairs stay PROMOTED and every other
        // capability stays SHADOW: the step-2 promotion flips nothing else.
        boolean promotedExactly = true;
        boolean shadowExactly = true;
        for (CapabilityRegistry.Entry entry : step2.entries()) {
            boolean promotedCapability = entry.capability()
                    == deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.SIGNED_INT32
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.DESCRIPTORS;
            if (promotedCapability) {
                promotedExactly &= entry.state() == CapabilityRegistry.State.PROMOTED;
            } else {
                shadowExactly &= entry.state() == CapabilityRegistry.State.SHADOW;
            }
        }
        check(promotedExactly && shadowExactly,
            "the step-2 registry promotes exactly FOUNDATION_VALUES, SIGNED_INT32, "
                + "CONTAINERS_AND_STRINGS, and DESCRIPTORS for both targets; "
                + "every other capability stays SHADOW");

        // Anti-hollow: re-deriving the step-2 promotion list prefix (the
        // first eight release promotions) through the withState surface
        // reproduces the step-2 release digest — the step-2 registry is
        // exactly the composed prefix, never a hand-written digest
        // constant. (The full release list now carries the later
        // step-3 pairs, so the full-list recomposition is the step-3
        // digest test's proof.)
        CapabilityRegistry recomposed = CapabilityRegistry.releaseRegistry();
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        for (int i = 0; i < 8 && i < promotions.size(); i++) {
            ReleaseConfiguration.ReleasePromotion promotion = promotions.get(i);
            recomposed = recomposed.withState(promotion.capability(),
                promotion.target(), CapabilityRegistry.State.PROMOTED);
        }
        check(recomposed.capabilityRegistryHash().equals(step2Hash),
            "re-deriving the step-2 promotion list prefix through withState "
                + "reproduces the step-2 release registry digest");
        check(!recomposed.capabilityRegistryHash().equals(postStep1Hash),
            "the recomposed step-2 digest still differs from the post-step-1 "
                + "digest (the prior release digest is left behind)");
    }

    private static final String BOUNDARY_OPS_SOURCE =
        "export function main(): null {\n"
            + "  let xs: int[] = [1, 2, 3]\n"
            + "  let t: table = { a: 1, n: null }\n"
            + "  let a: int = xs[0]\n"
            + "  let b: int = xs[2]\n"
            + "  let c: int = t.a\n"
            + "  let d: int | null = t.n\n"
            + "  let e: int | null = t.z\n"
            + "  return null;\n"
            + "}\n";

    private static final String BOUNDARY_FAIL_SOURCE =
        "export function main(): null {\n"
            + "  let xs: int[] = [1, 2, 3]\n"
            + "  let a: int = xs[-1]\n"
            + "  return null;\n"
            + "}\n";

    private static void testStep3CutoverPromotion() throws Exception {
        System.out.println("-- Step-3 cutover: BOUNDARIES promoted; boundary-exercising "
            + "modules route SHARED and the BOUNDARY emission runs on both targets --");

        // The release registry carries the step-3 promotion in the pinned
        // capability order (BOUNDARIES after DESCRIPTORS, LUAJIT before
        // JVM) with a recomputed digest.
        CapabilityRegistry registry = ReleaseConfiguration.releaseCapabilityRegistry();
        check(registry.state(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && registry.state(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes BOUNDARIES for LUAJIT and JVM");
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        check(promotions.size() == 14,
            "the release promotion list carries exactly the E12, step-1, "
                + "step-2, step-3, step-4, and step-5 pairs (14 entries); got "
                + promotions.size());
        check(promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT))
                > promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                    deal.semantic.Target.JVM))
                && promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.LUAJIT))
                    < promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                        deal.semantic.ir.SemanticCapability.BOUNDARIES,
                        deal.semantic.Target.JVM)),
            "the step-3 promotion sits in the pinned capability order with LUAJIT "
                + "before JVM");
        // Capability order and the time lock stay enforced: no pair after
        // BINDINGS appears in the list, and the locked routing marker
        // STDLIB_TIME_CONFLICT is never a promotion pair (parent D8).
        check(promotions.stream().allMatch(promotion ->
                promotion.capability().ordinal()
                    <= deal.semantic.ir.SemanticCapability.BINDINGS.ordinal()),
            "the promotion list carries no capability after BINDINGS "
                + "(capability order enforced)");
        check(promotions.stream().noneMatch(promotion ->
                promotion.capability()
                    == deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
            "the promotion list never carries STDLIB_TIME_CONFLICT "
                + "(the time lock stays enforced)");

        // LuaJIT, passing boundary operations: the production
        // PUBLIC_BUILD + V1_2_ACTIVE compile of a module exercising the
        // closed boundary-assignment cells (ARRAY_LITERAL_ELEMENT int
        // validation, ARRAY_ELEMENT_READ index cells, the
        // CONTEXTUAL_TABLE_READ present-value cell, and the optional-read
        // present-null/missing cells) routes SHARED — every claim the
        // module carries is promoted — emits exactly one semantic
        // artifact, and the BOUNDARY runtime validation (__bcheck) is
        // realized in the shared artifact and executes under the real
        // toolchain.
        Path luaProject = Files.createTempDirectory("deal-e10-bound-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", BOUNDARY_OPS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the boundary-exercising LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            Path out = luaProject.resolve("out");
            check(Files.readString(out.resolve("main.lua"))
                    .contains("__bcheck"),
                "the shared LuaJIT artifact realizes the BOUNDARY runtime "
                    + "validation (__bcheck) — never a stripped boundary");
            ProcessOutcome run = runProcess(out, List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT boundary artifact runs clean (the BOUNDARY "
                    + "emission validates literal elements, index cells, the "
                    + "contextual present value, and present-null/missing): "
                    + "exit=" + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // LuaJIT, failing boundary operation: a negative index read fails
        // the ARRAY_ELEMENT_READ cell inside the emitted artifact — the
        // runtime E8002 terminal proves the boundary executes (anti-hollow:
        // a skipped boundary would exit 0).
        Path luaFailProject = Files.createTempDirectory("deal-e10-bound-lua-fail-");
        try {
            write(luaFailProject, "deal.json", DEAL_JSON_LUA);
            write(luaFailProject, "src/main.deal", BOUNDARY_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the negative-index boundary module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            ProcessOutcome run = runProcess(luaFailProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 1
                    && run.output().contains("DEAL_ERROR_CODE: E8002"),
                "the shared LuaJIT artifact validates the negative index at "
                    + "the boundary and publishes DEAL_ERROR_CODE: E8002: exit="
                    + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaFailProject);
        }

        // JVM, passing boundary operations: the same production compile
        // routes SHARED; the artifact compiles under javac --release 25
        // -proc:none and runs under java.
        Path jvmProject = Files.createTempDirectory("deal-e10-bound-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", BOUNDARY_OPS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the boundary-exercising JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM boundary artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM boundary artifact runs clean (the BOUNDARY "
                        + "emission validates literal elements, index cells, the "
                        + "contextual present value, and present-null/missing): "
                        + "exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }

        // JVM, failing boundary operation: the emitted artifact validates
        // the negative index at the boundary and publishes E8002.
        Path jvmFailProject = Files.createTempDirectory("deal-e10-bound-jvm-fail-");
        try {
            write(jvmFailProject, "deal.json", DEAL_JSON_JVM);
            write(jvmFailProject, "src/main.deal", BOUNDARY_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the negative-index boundary JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmFailProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmFailProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E8002"),
                    "the shared JVM artifact validates the negative index at "
                        + "the boundary and publishes DEAL_ERROR_CODE: E8002: "
                        + "exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            } else {
                fail("the negative-index boundary JVM artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmFailProject);
        }

        // The bytes guard holds through the step-3 promotion: a
        // bytes-bearing module stays on the retained route (rule 2b beats
        // rule 4) with the bytes exception recorded — the T1/T3 state the
        // CONTAINERS_AND_STRINGS promotion established is untouched by the
        // BOUNDARIES promotion.
        Path bytesProject = Files.createTempDirectory("deal-e10-bound-bytes-");
        try {
            write(bytesProject, "deal.json", DEAL_JSON_LUA);
            write(bytesProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(bytesProject, "src/main.deal",
                "out", "CONSTRUCT_UNLOWERED",
                "the bytes-bearing module (a later-slice promotion check)");
            CompilationOrchestrator orchestrator =
                compileHarnessProject(bytesProject, "src/main.deal",
                    "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing module still emits zero semantic/one retained "
                    + "artifact after the BOUNDARIES promotion: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && plan.plan().bytesExceptions().size() == 1,
                "the bytes-bearing plan stays all-LEGACY with the bytes "
                    + "exception recorded (rule 2b beats rule 4): "
                    + (plan == null ? "null" : plan.plan()));
        } finally {
            deleteRecursively(bytesProject);
        }
    }

    private static void testStep3RegistryDigestRecomputation() {
        System.out.println("-- Step-3 registry digest: recomputed over its own entries; "
            + "differs from the post-step-2 release digest --");

        // The post-step-2 release registry: the committed E12 pairs plus
        // the step-1 and step-2 cutover promotions composed from the
        // all-SHADOW release default through the single withState
        // transition surface — the exact prior release state the step-3
        // promotion extends.
        CapabilityRegistry postStep2 = CapabilityRegistry.releaseRegistry()
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String postStep2Hash = postStep2.capabilityRegistryHash();
        check(postStep2.state(
                deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.SHADOW
                && postStep2.state(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.SHADOW,
            "the post-step-2 registry keeps BOUNDARIES SHADOW for both targets");

        // The step-3 release registry: the post-step-2 registry composed
        // with the step-3 cutover promotion (BOUNDARIES for both
        // targets) through the single withState transition surface — the
        // exact release state the step-4 promotion (ISSUE-0579) extends.
        // (The live release registry now carries the later step-4 pairs,
        // so this historical pin composes the step-3 state explicitly.)
        CapabilityRegistry step3 = postStep2
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String step3Hash = step3.capabilityRegistryHash();

        // The promotion is a real registry transition: the digest over the
        // promoted entries recomputes and differs from the prior release
        // digest.
        check(!step3Hash.equals(postStep2Hash),
            "the step-3 release digest differs from the post-step-2 release "
                + "digest: " + postStep2Hash + " -> " + step3Hash);

        // The step-3 digest is the canonical recomputation over the
        // registry's own entries — never a hand-rolled constant.
        check(step3Hash.equals(deal.semantic.ir.CanonicalJson.sha256Hex(
                deal.semantic.ir.CanonicalJson.serializeBytes(step3.canonicalJson()))),
            "the step-3 digest equals the canonical SHA-256 recomputation over "
                + "the registry's own canonical JSON");

        // The transition changes exactly the two step-3 entries: the
        // registries differ in exactly two entries, both BOUNDARIES
        // carrying PROMOTED; every other entry is byte-identical.
        List<CapabilityRegistry.Entry> preEntries = postStep2.entries();
        List<CapabilityRegistry.Entry> stepEntries = step3.entries();
        check(preEntries.size() == stepEntries.size()
                && stepEntries.size() == CapabilityRegistry.ENTRY_COUNT,
            "both registries keep the closed " + CapabilityRegistry.ENTRY_COUNT
                + "-entry cross product");
        int differing = 0;
        for (int i = 0; i < preEntries.size() && i < stepEntries.size(); i++) {
            CapabilityRegistry.Entry pre = preEntries.get(i);
            CapabilityRegistry.Entry step = stepEntries.get(i);
            if (pre.capability() != step.capability()
                    || pre.target() != step.target()
                    || pre.state() != step.state()) {
                differing++;
            }
        }
        check(differing == 2
                && step3.state(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && step3.state(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the step-3 registry differs from the post-step-2 registry in exactly "
                + "the two BOUNDARIES x LUAJIT/JVM entries, both carrying "
                + "PROMOTED (differing=" + differing + ")");

        // The E12, step-1, step-2, and step-3 pairs stay PROMOTED and
        // every other capability stays SHADOW — including the locked
        // routing marker STDLIB_TIME_CONFLICT (parent D8): the step-3
        // promotion flips nothing else.
        boolean promotedExactly = true;
        boolean shadowExactly = true;
        for (CapabilityRegistry.Entry entry : step3.entries()) {
            boolean promotedCapability = entry.capability()
                    == deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.SIGNED_INT32
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.DESCRIPTORS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.BOUNDARIES;
            if (promotedCapability) {
                promotedExactly &= entry.state() == CapabilityRegistry.State.PROMOTED;
            } else {
                shadowExactly &= entry.state() == CapabilityRegistry.State.SHADOW;
            }
        }
        check(promotedExactly && shadowExactly,
            "the step-3 registry promotes exactly FOUNDATION_VALUES, SIGNED_INT32, "
                + "CONTAINERS_AND_STRINGS, DESCRIPTORS, and BOUNDARIES for both "
                + "targets; every other capability stays SHADOW");

        // Anti-hollow: re-deriving the step-3 promotion list prefix (the
        // first ten release promotions) through the withState surface
        // reproduces the step-3 release digest — the step-3 registry is
        // exactly the composed prefix, never a hand-written digest
        // constant. (The full release list now carries the later
        // step-4 pairs, so the full-list recomposition is the step-4
        // digest test's proof.)
        CapabilityRegistry recomposed = CapabilityRegistry.releaseRegistry();
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        for (int i = 0; i < 10 && i < promotions.size(); i++) {
            ReleaseConfiguration.ReleasePromotion promotion = promotions.get(i);
            recomposed = recomposed.withState(promotion.capability(),
                promotion.target(), CapabilityRegistry.State.PROMOTED);
        }
        check(recomposed.capabilityRegistryHash().equals(step3Hash),
            "re-deriving the step-3 promotion list prefix through withState "
                + "reproduces the step-3 release registry digest");
        check(!recomposed.capabilityRegistryHash().equals(postStep2Hash),
            "the recomposed step-3 digest still differs from the post-step-2 "
                + "digest (the prior release digest is left behind)");
    }

    private static final String EVALUATION_ORDER_PASS_SOURCE =
        "export function main(): null {\n"
            + "  let xs: int[] = [0, 1, 2]\n"
            + "  let n: int = 3\n"
            + "  let i: int = 0\n"
            + "  let sum: int = 0\n"
            + "  if (n > 0) {\n"
            + "    while (i < n) {\n"
            + "      if (i === 1) {\n"
            + "        i = i + 1\n"
            + "        continue\n"
            + "      }\n"
            + "      sum = sum + i\n"
            + "      i = i + 1\n"
            + "    }\n"
            + "  } else {\n"
            + "    sum = 100\n"
            + "  }\n"
            + "  if (sum !== 2) {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  sum === 2\n"
            + "  return null\n"
            + "}\n";

    private static final String EVALUATION_ORDER_SPEC_SOURCE =
        "export function main(): null {\n"
            + "  let xs: int[] = [0]\n"
            + "  let n: int = 0\n"
            + "  if (n === 0) {\n"
            + "    n = 1\n"
            + "  } else {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  n === 1\n"
            + "  return null\n"
            + "}\n";

    private static final String EVALUATION_ORDER_FAIL_SOURCE =
        "export function main(): null {\n"
            + "  let xs: int[] = [0, 1, 2]\n"
            + "  let sum: int = 100\n"
            + "  if (sum !== 3) {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  return null\n"
            + "}\n";

    private static void testStep4CutoverPromotion() throws Exception {
        System.out.println("-- Step-4 cutover: EVALUATION_ORDER promoted; branch/loop/"
            + "discard modules route SHARED and the control-flow emission runs on "
            + "both targets --");

        // The release registry carries the step-4 promotion in the pinned
        // capability order (EVALUATION_ORDER after BOUNDARIES, LUAJIT
        // before JVM) with a recomputed digest.
        CapabilityRegistry registry = ReleaseConfiguration.releaseCapabilityRegistry();
        check(registry.state(deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && registry.state(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes EVALUATION_ORDER for LUAJIT and JVM");
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        check(promotions.size() == 14,
            "the release promotion list carries exactly the E12, step-1, "
                + "step-2, step-3, step-4, and step-5 pairs (14 entries); got "
                + promotions.size());
        check(promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.LUAJIT))
                > promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.BOUNDARIES,
                    deal.semantic.Target.JVM))
                && promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.LUAJIT))
                    < promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                        deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                        deal.semantic.Target.JVM)),
            "the step-4 promotion sits in the pinned capability order with LUAJIT "
                + "before JVM");
        // Capability order and the time lock stay enforced: no pair after
        // BINDINGS appears in the list, and the locked routing marker
        // STDLIB_TIME_CONFLICT is never a promotion pair (parent D8).
        check(promotions.stream().allMatch(promotion ->
                promotion.capability().ordinal()
                    <= deal.semantic.ir.SemanticCapability.BINDINGS.ordinal()),
            "the promotion list carries no capability after BINDINGS "
                + "(capability order enforced)");
        check(promotions.stream().noneMatch(promotion ->
                promotion.capability()
                    == deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
            "the promotion list never carries STDLIB_TIME_CONFLICT "
                + "(the time lock stays enforced)");

        // LuaJIT, passing branch/loop/discard program: the production
        // PUBLIC_BUILD + V1_2_ACTIVE compile of a module exercising the
        // landed control-flow emission (comparison-selector BRANCH over
        // the if/else, the WHILE LOOP with a CONTINUE transfer, and the
        // DISCARD of a comparison expression statement) routes SHARED —
        // every claim the module carries is promoted — emits exactly one
        // semantic artifact, and the emitted branch/loop/continue/discard
        // machinery executes under the real toolchain (anti-hollow: the
        // negative-index boundary guard fires unless the else branch
        // stays untaken, the loop lands continue and reaches the correct
        // sum, and the discard stays side-effect free).
        Path luaProject = Files.createTempDirectory("deal-e10-eval-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", EVALUATION_ORDER_PASS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the branch/loop/discard LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            ProcessOutcome run = runProcess(luaProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT branch/loop/discard artifact runs clean "
                    + "(comparison-selector branches, the loop with its continue "
                    + "transfer, and the discard execute): exit=" + run.exitCode()
                    + " output=" + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // LuaJIT, no-speculative-execution pin: an untaken branch whose
        // body reads a negative index must never run — the shared
        // artifact exits 0 (a speculatively executed branch would hit
        // the ARRAY_ELEMENT_READ boundary, publish E8002, and exit 1).
        Path luaSpecProject = Files.createTempDirectory("deal-e10-eval-lua-spec-");
        try {
            write(luaSpecProject, "deal.json", DEAL_JSON_LUA);
            write(luaSpecProject, "src/main.deal", EVALUATION_ORDER_SPEC_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaSpecProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the no-speculation LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            ProcessOutcome run = runProcess(luaSpecProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT artifact never executes the untaken "
                    + "negative-index branch (no speculative execution): exit="
                    + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaSpecProject);
        }

        // LuaJIT, failing branch: a taken guard branch whose body reads
        // a negative index publishes the retained boundary terminal
        // inside the emitted artifact — the branch discriminates at
        // runtime (anti-hollow: a stripped branch would exit 0).
        Path luaFailProject = Files.createTempDirectory("deal-e10-eval-lua-fail-");
        try {
            write(luaFailProject, "deal.json", DEAL_JSON_LUA);
            write(luaFailProject, "src/main.deal", EVALUATION_ORDER_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the failing-branch LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            ProcessOutcome run = runProcess(luaFailProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 1
                    && run.output().contains("DEAL_ERROR_CODE: E8002"),
                "the shared LuaJIT artifact takes the guard branch and "
                    + "publishes the boundary terminal DEAL_ERROR_CODE: E8002: "
                    + "exit=" + run.exitCode() + " output="
                    + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaFailProject);
        }

        // JVM, passing branch/loop/discard program: the same production
        // compile routes SHARED; the artifact compiles under
        // javac --release 25 -proc:none and runs under java.
        Path jvmProject = Files.createTempDirectory("deal-e10-eval-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", EVALUATION_ORDER_PASS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the branch/loop/discard JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM branch/loop/discard artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM branch/loop/discard artifact runs clean "
                        + "(comparison-selector branches, the loop with its "
                        + "continue transfer, and the discard execute): exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }

        // JVM, no-speculative-execution pin: the untaken negative-index
        // branch never executes under the real JVM artifact either.
        Path jvmSpecProject = Files.createTempDirectory("deal-e10-eval-jvm-spec-");
        try {
            write(jvmSpecProject, "deal.json", DEAL_JSON_JVM);
            write(jvmSpecProject, "src/main.deal", EVALUATION_ORDER_SPEC_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmSpecProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the no-speculation JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmSpecProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmSpecProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM artifact never executes the untaken "
                        + "negative-index branch (no speculative execution): exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            } else {
                fail("the no-speculation JVM artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmSpecProject);
        }

        // JVM, failing branch: the taken guard branch publishes the
        // boundary terminal through the real JVM artifact.
        Path jvmFailProject = Files.createTempDirectory("deal-e10-eval-jvm-fail-");
        try {
            write(jvmFailProject, "deal.json", DEAL_JSON_JVM);
            write(jvmFailProject, "src/main.deal", EVALUATION_ORDER_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the failing-branch JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmFailProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmFailProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E8002"),
                    "the shared JVM artifact takes the guard branch and "
                        + "publishes the boundary terminal DEAL_ERROR_CODE: E8002: "
                        + "exit=" + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            } else {
                fail("the failing-branch JVM artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmFailProject);
        }

        // The bytes guard holds through the step-4 promotion: a
        // bytes-bearing module stays on the retained route (rule 2b beats
        // rule 4) with the bytes exception recorded — the T1/T3 state the
        // CONTAINERS_AND_STRINGS promotion established is untouched by the
        // EVALUATION_ORDER promotion (the bytes module exercises a branch,
        // so rule 2b must beat the promotion even for a module that would
        // otherwise be all-promoted).
        Path bytesProject = Files.createTempDirectory("deal-e10-eval-bytes-");
        try {
            write(bytesProject, "deal.json", DEAL_JSON_LUA);
            write(bytesProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(bytesProject, "src/main.deal",
                "out", "CONSTRUCT_UNLOWERED",
                "the bytes-bearing module (a later-slice promotion check)");
            CompilationOrchestrator orchestrator =
                compileHarnessProject(bytesProject, "src/main.deal",
                    "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing module still emits zero semantic/one retained "
                    + "artifact after the EVALUATION_ORDER promotion: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && plan.plan().bytesExceptions().size() == 1,
                "the bytes-bearing plan stays all-LEGACY with the bytes "
                    + "exception recorded (rule 2b beats rule 4): "
                    + (plan == null ? "null" : plan.plan()));
        } finally {
            deleteRecursively(bytesProject);
        }
    }

    private static void testStep4RegistryDigestRecomputation() {
        System.out.println("-- Step-4 registry digest: recomputed over its own entries; "
            + "differs from the post-step-3 release digest --");

        // The post-step-3 release registry: the committed E12 pairs plus
        // the step-1, step-2, and step-3 cutover promotions composed from
        // the all-SHADOW release default through the single withState
        // transition surface — the exact prior release state the step-4
        // promotion extends.
        CapabilityRegistry postStep3 = CapabilityRegistry.releaseRegistry()
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String postStep3Hash = postStep3.capabilityRegistryHash();
        check(postStep3.state(
                deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.SHADOW
                && postStep3.state(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.SHADOW,
            "the post-step-3 registry keeps EVALUATION_ORDER SHADOW for both "
                + "targets");

        // The step-4 release registry: the post-step-3 registry composed
        // with the step-4 cutover promotion (EVALUATION_ORDER for both
        // targets) through the single withState transition surface — the
        // exact release state the step-5 promotion (ISSUE-0581) extends.
        // (The live release registry now carries the later step-5 pairs,
        // so this historical pin composes the step-4 state explicitly.)
        CapabilityRegistry step4 = postStep3
            .withState(deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String step4Hash = step4.capabilityRegistryHash();

        // The promotion is a real registry transition: the digest over the
        // promoted entries recomputes and differs from the prior release
        // digest.
        check(!step4Hash.equals(postStep3Hash),
            "the step-4 release digest differs from the post-step-3 release "
                + "digest: " + postStep3Hash + " -> " + step4Hash);

        // The step-4 digest is the canonical recomputation over the
        // registry's own entries — never a hand-rolled constant.
        check(step4Hash.equals(deal.semantic.ir.CanonicalJson.sha256Hex(
                deal.semantic.ir.CanonicalJson.serializeBytes(step4.canonicalJson()))),
            "the step-4 digest equals the canonical SHA-256 recomputation over "
                + "the registry's own canonical JSON");

        // The transition changes exactly the two step-4 entries: the
        // registries differ in exactly two entries, both EVALUATION_ORDER
        // carrying PROMOTED; every other entry is byte-identical.
        List<CapabilityRegistry.Entry> preEntries = postStep3.entries();
        List<CapabilityRegistry.Entry> stepEntries = step4.entries();
        check(preEntries.size() == stepEntries.size()
                && stepEntries.size() == CapabilityRegistry.ENTRY_COUNT,
            "both registries keep the closed " + CapabilityRegistry.ENTRY_COUNT
                + "-entry cross product");
        int differing = 0;
        for (int i = 0; i < preEntries.size() && i < stepEntries.size(); i++) {
            CapabilityRegistry.Entry pre = preEntries.get(i);
            CapabilityRegistry.Entry step = stepEntries.get(i);
            if (pre.capability() != step.capability()
                    || pre.target() != step.target()
                    || pre.state() != step.state()) {
                differing++;
            }
        }
        check(differing == 2
                && step4.state(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && step4.state(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the step-4 registry differs from the post-step-3 registry in exactly "
                + "the two EVALUATION_ORDER x LUAJIT/JVM entries, both carrying "
                + "PROMOTED (differing=" + differing + ")");

        // The E12, step-1, step-2, step-3, and step-4 pairs stay PROMOTED
        // and every other capability stays SHADOW — including the locked
        // routing marker STDLIB_TIME_CONFLICT (parent D8): the step-4
        // promotion flips nothing else.
        boolean promotedExactly = true;
        boolean shadowExactly = true;
        for (CapabilityRegistry.Entry entry : step4.entries()) {
            boolean promotedCapability = entry.capability()
                    == deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.SIGNED_INT32
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.DESCRIPTORS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.BOUNDARIES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.EVALUATION_ORDER;
            if (promotedCapability) {
                promotedExactly &= entry.state() == CapabilityRegistry.State.PROMOTED;
            } else {
                shadowExactly &= entry.state() == CapabilityRegistry.State.SHADOW;
            }
        }
        check(promotedExactly && shadowExactly,
            "the step-4 registry promotes exactly FOUNDATION_VALUES, SIGNED_INT32, "
                + "CONTAINERS_AND_STRINGS, DESCRIPTORS, BOUNDARIES, and "
                + "EVALUATION_ORDER for both targets; every other capability stays "
                + "SHADOW");

        // Anti-hollow: re-deriving the step-4 promotion list prefix (the
        // first twelve release promotions) through the withState surface
        // reproduces the step-4 release digest — the step-4 registry is
        // exactly the composed prefix, never a hand-written digest
        // constant. (The full release list now carries the later
        // step-5 pairs, so the full-list recomposition is the step-5
        // digest test's proof.)
        CapabilityRegistry recomposed = CapabilityRegistry.releaseRegistry();
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        for (int i = 0; i < 12 && i < promotions.size(); i++) {
            ReleaseConfiguration.ReleasePromotion promotion = promotions.get(i);
            recomposed = recomposed.withState(promotion.capability(),
                promotion.target(), CapabilityRegistry.State.PROMOTED);
        }
        check(recomposed.capabilityRegistryHash().equals(step4Hash),
            "re-deriving the step-4 promotion list prefix through withState "
                + "reproduces the step-4 release registry digest");
        check(!recomposed.capabilityRegistryHash().equals(postStep3Hash),
            "the recomposed step-4 digest still differs from the post-step-3 "
                + "digest (the prior release digest is left behind)");
    }

    private static final String BINDINGS_GROUP_PASS_SOURCE =
        "function isEven(x: int): int {\n"
            + "  if (x === 0) {\n"
            + "    return 1\n"
            + "  }\n"
            + "  return isOdd(x - 1)\n"
            + "}\n"
            + "function isOdd(x: int): int {\n"
            + "  if (x === 0) {\n"
            + "    return 0\n"
            + "  }\n"
            + "  return isEven(x - 1)\n"
            + "}\n"
            + "export function main(): null {\n"
            + "  let xs: int[] = [0]\n"
            + "  if (isEven(10) !== 1) {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  if (isOdd(9) !== 1) {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  return null\n"
            + "}\n";

    private static final String BINDINGS_GROUP_FAIL_SOURCE =
        "function isEven(x: int): int {\n"
            + "  if (x === 0) {\n"
            + "    return 1\n"
            + "  }\n"
            + "  return isOdd(x - 1)\n"
            + "}\n"
            + "function isOdd(x: int): int {\n"
            + "  if (x === 0) {\n"
            + "    return 0\n"
            + "  }\n"
            + "  return isEven(x - 1)\n"
            + "}\n"
            + "export function main(): null {\n"
            + "  let xs: int[] = [0]\n"
            + "  if (isEven(10) !== 0) {\n"
            + "    let bad: int = xs[-1]\n"
            + "  }\n"
            + "  return null\n"
            + "}\n";

    private static void testStep5CutoverPromotion() throws Exception {
        System.out.println("-- Step-5 cutover: BINDINGS promoted; recursive-group/closure "
            + "modules route SHARED and the shared binding/closure emission runs on "
            + "both targets --");

        // The release registry carries the step-5 promotion in the pinned
        // capability order (BINDINGS after EVALUATION_ORDER, LUAJIT before
        // JVM) with a recomputed digest.
        CapabilityRegistry registry = ReleaseConfiguration.releaseCapabilityRegistry();
        check(registry.state(deal.semantic.ir.SemanticCapability.BINDINGS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && registry.state(
                    deal.semantic.ir.SemanticCapability.BINDINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes BINDINGS for LUAJIT and JVM");
        List<ReleaseConfiguration.ReleasePromotion> promotions =
            ReleaseConfiguration.activationPromotions();
        check(promotions.size() == 14,
            "the release promotion list carries exactly the E12, step-1, "
                + "step-2, step-3, step-4, and step-5 pairs (14 entries); got "
                + promotions.size());
        check(promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                deal.semantic.ir.SemanticCapability.BINDINGS,
                deal.semantic.Target.LUAJIT))
                > promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                    deal.semantic.Target.JVM))
                && promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                    deal.semantic.ir.SemanticCapability.BINDINGS,
                    deal.semantic.Target.LUAJIT))
                    < promotions.indexOf(new ReleaseConfiguration.ReleasePromotion(
                        deal.semantic.ir.SemanticCapability.BINDINGS,
                        deal.semantic.Target.JVM)),
            "the step-5 promotion sits in the pinned capability order with LUAJIT "
                + "before JVM");
        // Capability order and the time lock stay enforced: no pair after
        // BINDINGS appears in the list, and the locked routing marker
        // STDLIB_TIME_CONFLICT is never a promotion pair (parent D8).
        check(promotions.stream().allMatch(promotion ->
                promotion.capability().ordinal()
                    <= deal.semantic.ir.SemanticCapability.BINDINGS.ordinal()),
            "the promotion list carries no capability after BINDINGS "
                + "(capability order enforced)");
        check(promotions.stream().noneMatch(promotion ->
                promotion.capability()
                    == deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
            "the promotion list never carries STDLIB_TIME_CONFLICT "
                + "(the time lock stays enforced)");

        // LuaJIT, passing recursive-group program: the production
        // PUBLIC_BUILD + V1_2_ACTIVE compile of a module exercising the
        // BINDINGS family's shared emission (the mutual even/odd pair —
        // per-member closure identities over the shared capture cells,
        // published through the binding-cell arms, and the member loads
        // through main) routes SHARED — every claim the module carries
        // is promoted — emits exactly one semantic artifact, and the
        // emitted closure/binding machinery executes under the real
        // toolchain (anti-hollow: the negative-index boundary guard
        // fires unless the mutual recursion executes and lands the
        // correct parity results).
        Path luaProject = Files.createTempDirectory("deal-e10-bind-lua-");
        try {
            write(luaProject, "deal.json", DEAL_JSON_LUA);
            write(luaProject, "src/main.deal", BINDINGS_GROUP_PASS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the recursive-group LuaJIT module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            check(orchestrator.routePlan() == null,
                "the release-owned production invocation computes and"
                    + " consults no route plan (ISSUE-0643 P4: phase 3.7"
                    + " stays skipped)");
            Path out = luaProject.resolve("out");
            check(Files.readString(out.resolve("main.lua"))
                    .contains("CLOSURE_NEW"),
                "the shared LuaJIT artifact realizes the BINDINGS family's "
                    + "closure arm (CLOSURE_NEW over the member capture cells) — "
                    + "never a stripped binding");
            ProcessOutcome run = runProcess(out, List.of("luajit", "main.lua"));
            check(run.exitCode() == 0 && run.output().isEmpty(),
                "the shared LuaJIT recursive-group artifact runs clean (the "
                    + "mutual recursion executes through the published member "
                    + "identities and lands the correct parity): exit="
                    + run.exitCode() + " output=" + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaProject);
        }

        // LuaJIT, failing recursive-group program: the inverted guard
        // takes the negative-index branch and publishes the boundary
        // terminal inside the emitted artifact — the group machinery
        // discriminates at runtime (anti-hollow: a stripped recursion
        // returning a wrong value would exit 0, a stripped guard would
        // exit 0).
        Path luaFailProject = Files.createTempDirectory("deal-e10-bind-lua-fail-");
        try {
            write(luaFailProject, "deal.json", DEAL_JSON_LUA);
            write(luaFailProject, "src/main.deal", BINDINGS_GROUP_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(luaFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the failing-guard recursive-group LuaJIT module emits one "
                    + "semantic/zero retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            ProcessOutcome run = runProcess(luaFailProject.resolve("out"),
                List.of("luajit", "main.lua"));
            check(run.exitCode() == 1
                    && run.output().contains("DEAL_ERROR_CODE: E8002"),
                "the shared LuaJIT artifact executes the recursion, takes the "
                    + "guard branch, and publishes the boundary terminal "
                    + "DEAL_ERROR_CODE: E8002: exit=" + run.exitCode()
                    + " output=" + run.output().replace("\n", "\\n"));
        } finally {
            deleteRecursively(luaFailProject);
        }

        // JVM, passing recursive-group program: the same production
        // compile routes SHARED; the artifact compiles under
        // javac --release 25 -proc:none and runs under java.
        Path jvmProject = Files.createTempDirectory("deal-e10-bind-jvm-");
        try {
            write(jvmProject, "deal.json", DEAL_JSON_JVM);
            write(jvmProject, "src/main.deal", BINDINGS_GROUP_PASS_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the recursive-group JVM module emits one semantic/zero "
                    + "retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            check(Files.readString(out.resolve("Main.java"))
                    .contains("JvmRuntime.FunctionValue")
                    && Files.readString(out.resolve("Main.java"))
                        .contains("((Object[]) b"),
                "the shared JVM artifact realizes the BINDINGS family's closure "
                    + "and binding-cell arms (JvmRuntime.FunctionValue factories "
                    + "over the member capture cells, published into the cell "
                    + "arrays) — never a stripped binding");
            ProcessOutcome javac = runProcess(jvmProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            check(javac.exitCode() == 0,
                "the shared JVM recursive-group artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 0 && run.output().isEmpty(),
                    "the shared JVM recursive-group artifact runs clean (the "
                        + "mutual recursion executes through the published member "
                        + "identities and lands the correct parity): exit="
                        + run.exitCode() + " output="
                        + run.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmProject);
        }

        // JVM, failing recursive-group program: the inverted guard
        // publishes the boundary terminal through the real JVM artifact.
        Path jvmFailProject = Files.createTempDirectory("deal-e10-bind-jvm-fail-");
        try {
            write(jvmFailProject, "deal.json", DEAL_JSON_JVM);
            write(jvmFailProject, "src/main.deal", BINDINGS_GROUP_FAIL_SOURCE);
            CompilationOrchestrator orchestrator =
                compileProject(jvmFailProject, "src/main.deal", "out");
            check(orchestrator.semanticEmissionCount() == 1
                    && orchestrator.retainedEmissionCount() == 0,
                "the failing-guard recursive-group JVM module emits one "
                    + "semantic/zero retained artifact: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            Path out = jvmFailProject.resolve("out");
            String buildCp = Path.of("build").toAbsolutePath().normalize().toString();
            ProcessOutcome javac = runProcess(jvmFailProject, List.of(
                "javac", "--release", "25", "-proc:none", "-cp", buildCp,
                "-d", out.toString(), out.resolve("Main.java").toString()));
            if (javac.exitCode() == 0) {
                ProcessOutcome run = runProcess(out, List.of(
                    "java", "-cp", buildCp + File.pathSeparator + out, "Main"));
                check(run.exitCode() == 1
                        && run.output().contains("DEAL_ERROR_CODE: E8002"),
                    "the shared JVM artifact executes the recursion, takes the "
                        + "guard branch, and publishes the boundary terminal "
                        + "DEAL_ERROR_CODE: E8002: exit=" + run.exitCode()
                        + " output=" + run.output().replace("\n", "\\n"));
            } else {
                fail("the failing-guard recursive-group JVM artifact compiles: "
                    + javac.output().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(jvmFailProject);
        }

        // The bytes guard holds through the step-5 promotion: a
        // bytes-bearing module stays on the retained route (rule 2b beats
        // rule 4) with the bytes exception recorded — the T1/T3 state the
        // CONTAINERS_AND_STRINGS promotion established is untouched by the
        // BINDINGS promotion.
        Path bytesProject = Files.createTempDirectory("deal-e10-bind-bytes-");
        try {
            write(bytesProject, "deal.json", DEAL_JSON_LUA);
            write(bytesProject, "src/main.deal", BYTES_SOURCE);
            checkProductionFailClosed(bytesProject, "src/main.deal",
                "out", "CONSTRUCT_UNLOWERED",
                "the bytes-bearing module (a later-slice promotion check)");
            CompilationOrchestrator orchestrator =
                compileHarnessProject(bytesProject, "src/main.deal",
                    "out");
            check(orchestrator.semanticEmissionCount() == 0
                    && orchestrator.retainedEmissionCount() == 1,
                "the bytes-bearing module still emits zero semantic/one retained "
                    + "artifact after the BINDINGS promotion: semantic="
                    + orchestrator.semanticEmissionCount() + " retained="
                    + orchestrator.retainedEmissionCount());
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null
                    && plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && plan.plan().bytesExceptions().size() == 1,
                "the bytes-bearing plan stays all-LEGACY with the bytes "
                    + "exception recorded (rule 2b beats rule 4): "
                    + (plan == null ? "null" : plan.plan()));
        } finally {
            deleteRecursively(bytesProject);
        }
    }

    private static void testStep5RegistryDigestRecomputation() {
        System.out.println("-- Step-5 registry digest: recomputed over its own entries; "
            + "differs from the post-step-4 release digest --");

        // The post-step-4 release registry: the committed E12 pairs plus
        // the step-1 through step-4 cutover promotions composed from the
        // all-SHADOW release default through the single withState
        // transition surface — the exact prior release state the step-5
        // promotion extends.
        CapabilityRegistry postStep4 = CapabilityRegistry.releaseRegistry()
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.SIGNED_INT32,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.DESCRIPTORS,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.BOUNDARIES,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
            .withState(deal.semantic.ir.SemanticCapability.EVALUATION_ORDER,
                deal.semantic.Target.JVM, CapabilityRegistry.State.PROMOTED);
        String postStep4Hash = postStep4.capabilityRegistryHash();
        check(postStep4.state(
                deal.semantic.ir.SemanticCapability.BINDINGS,
                deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.SHADOW
                && postStep4.state(
                    deal.semantic.ir.SemanticCapability.BINDINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.SHADOW,
            "the post-step-4 registry keeps BINDINGS SHADOW for both targets");

        CapabilityRegistry step5 = ReleaseConfiguration.releaseCapabilityRegistry();
        String step5Hash = step5.capabilityRegistryHash();

        // The promotion is a real registry transition: the digest over the
        // promoted entries recomputes and differs from the prior release
        // digest.
        check(!step5Hash.equals(postStep4Hash),
            "the step-5 release digest differs from the post-step-4 release "
                + "digest: " + postStep4Hash + " -> " + step5Hash);

        // The step-5 digest is the canonical recomputation over the
        // registry's own entries — never a hand-rolled constant.
        check(step5Hash.equals(deal.semantic.ir.CanonicalJson.sha256Hex(
                deal.semantic.ir.CanonicalJson.serializeBytes(step5.canonicalJson()))),
            "the step-5 digest equals the canonical SHA-256 recomputation over "
                + "the registry's own canonical JSON");

        // The transition changes exactly the two step-5 entries: the
        // registries differ in exactly two entries, both BINDINGS carrying
        // PROMOTED; every other entry is byte-identical.
        List<CapabilityRegistry.Entry> preEntries = postStep4.entries();
        List<CapabilityRegistry.Entry> stepEntries = step5.entries();
        check(preEntries.size() == stepEntries.size()
                && stepEntries.size() == CapabilityRegistry.ENTRY_COUNT,
            "both registries keep the closed " + CapabilityRegistry.ENTRY_COUNT
                + "-entry cross product");
        int differing = 0;
        for (int i = 0; i < preEntries.size() && i < stepEntries.size(); i++) {
            CapabilityRegistry.Entry pre = preEntries.get(i);
            CapabilityRegistry.Entry step = stepEntries.get(i);
            if (pre.capability() != step.capability()
                    || pre.target() != step.target()
                    || pre.state() != step.state()) {
                differing++;
            }
        }
        check(differing == 2
                && step5.state(
                    deal.semantic.ir.SemanticCapability.BINDINGS,
                    deal.semantic.Target.LUAJIT) == CapabilityRegistry.State.PROMOTED
                && step5.state(
                    deal.semantic.ir.SemanticCapability.BINDINGS,
                    deal.semantic.Target.JVM) == CapabilityRegistry.State.PROMOTED,
            "the step-5 registry differs from the post-step-4 registry in exactly "
                + "the two BINDINGS x LUAJIT/JVM entries, both carrying PROMOTED "
                + "(differing=" + differing + ")");

        // The E12, step-1, step-2, step-3, step-4, and step-5 pairs stay
        // PROMOTED and every other capability stays SHADOW — including
        // the locked routing marker STDLIB_TIME_CONFLICT (parent D8): the
        // step-5 promotion flips nothing else.
        boolean promotedExactly = true;
        boolean shadowExactly = true;
        for (CapabilityRegistry.Entry entry : step5.entries()) {
            boolean promotedCapability = entry.capability()
                    == deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.SIGNED_INT32
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.CONTAINERS_AND_STRINGS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.DESCRIPTORS
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.BOUNDARIES
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.EVALUATION_ORDER
                || entry.capability()
                    == deal.semantic.ir.SemanticCapability.BINDINGS;
            if (promotedCapability) {
                promotedExactly &= entry.state() == CapabilityRegistry.State.PROMOTED;
            } else {
                shadowExactly &= entry.state() == CapabilityRegistry.State.SHADOW;
            }
        }
        check(promotedExactly && shadowExactly,
            "the step-5 registry promotes exactly FOUNDATION_VALUES, SIGNED_INT32, "
                + "CONTAINERS_AND_STRINGS, DESCRIPTORS, BOUNDARIES, "
                + "EVALUATION_ORDER, and BINDINGS for both targets; every other "
                + "capability stays SHADOW");

        // Anti-hollow: re-deriving the release promotion list through the
        // withState surface reproduces the committed release digest — the
        // release registry is exactly the composed list, never a
        // hand-written digest constant.
        CapabilityRegistry recomposed = CapabilityRegistry.releaseRegistry();
        for (ReleaseConfiguration.ReleasePromotion promotion
                : ReleaseConfiguration.activationPromotions()) {
            recomposed = recomposed.withState(promotion.capability(),
                promotion.target(), CapabilityRegistry.State.PROMOTED);
        }
        check(recomposed.capabilityRegistryHash().equals(step5Hash),
            "re-deriving the release promotion list through withState reproduces "
                + "the committed release registry digest");
        check(!recomposed.capabilityRegistryHash().equals(postStep4Hash),
            "the recomposed step-5 digest still differs from the post-step-4 "
                + "digest (the prior release digest is left behind)");
    }

    private static void testFailurePreservesPriorArtifacts() throws Exception {
        System.out.println("-- Atomic publication: a failing compile preserves the prior set --");

        Path project = Files.createTempDirectory("deal-e10-atomic-");
        try {
            write(project, "deal.json", DEAL_JSON_LUA);
            write(project, "src/main.deal",
                "export function main(): null {\n  return null\n}\n");
            CompilationOrchestrator first =
                compileProject(project, "src/main.deal", "out");
            check(first.semanticEmissionCount() == 1
                    && first.retainedEmissionCount() == 0,
                "the first compile publishes the semantic artifact set");
            Map<String, String> prior = fingerprint(project.resolve("out"));

            // A failing recompile through the same real pipeline: the
            // residual public shared-lowering E6005 shape — a
            // function-typed table member read (the MEMBER_READ result
            // resolves no FunctionExecutionBinding, R-FUNCTION-BINDING)
            // — routes SHARED and fails the compile inside the shared
            // lowering; nothing stages, nothing publishes, and the prior
            // artifact set stays byte-for-byte with no staging/retired
            // residue. The cycle-2 named reroute shapes (stored/embedded
            // function expressions, adapters, bytes, recursion, class
            // literals) reroute LEGACY at plan time — pinned by
            // testAdapterShapeReroutesLegacy — so this residual shape is
            // the public E6005 the atomicity contract is pinned against;
            // the stager-level discard paths stay pinned in
            // PublicationStagerTest.
            write(project, "src/main.deal",
                "function one2(): int {\n  return 1\n}\n\n"
                    + "export function main(): null {\n"
                    + "  let t: table = { f: one2 }\n"
                    + "  let g: () => int = t.f\n"
                    + "  one2()\n"
                    + "  return null\n"
                    + "}\n");
            Path entryFile = project.resolve("src/main.deal").toAbsolutePath()
                .normalize();
            ProjectLocator.LocateResult located = ProjectLocator.locate(
                entryFile.toString(), new CliOverrides(null, null));
            if (located.context() == null) {
                fail("locate failed: " + located);
                deleteRecursively(project);
                return;
            }
            CompilerInvocation invocation = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE,
                ReleaseConfiguration.releaseCapabilityRegistry());
            CompilationOrchestrator failing = new CompilationOrchestrator(
                located.context(), entryFile, false, false, false, false, null,
                invocation);
            boolean compiled = failing.compile();
            check(!compiled,
                "the shared-lowering E6005 recompile fails (nothing publishes)");
            check(failing.diagnostics().stream()
                    .anyMatch(d -> "E6005".equals(d.code())),
                "the failure is the shared-lowering E6005 (never a frontend "
                    + "rejection): " + failing.diagnostics());
            Map<String, String> after = fingerprint(project.resolve("out"));
            check(prior.equals(after),
                "the prior artifact set is preserved byte-for-byte after the failed "
                    + "compile");
            boolean residue = false;
            try (Stream<Path> entries = Files.list(project)) {
                for (Path entry : entries.toList()) {
                    String name = entry.getFileName().toString();
                    if (name.contains(".deal-stage-")
                            || name.contains(".deal-retired-")) {
                        residue = true;
                    }
                }
            }
            check(!residue,
                "no staging/retired siblings survive the failed publication");
        } finally {
            deleteRecursively(project);
        }
    }

    private static Map<String, String> fingerprint(Path root) throws Exception {
        Map<String, String> result = new TreeMap<>();
        if (!Files.isDirectory(root)) {
            return result;
        }
        try (Stream<Path> walk = Files.walk(root, FileVisitOption.values())) {
            for (Path path : walk.filter(Files::isRegularFile).toList()) {
                String relative = root.relativize(path).toString()
                    .replace(File.separatorChar, '/');
                result.put(relative, sha256Hex(Files.readAllBytes(path)));
            }
        }
        return result;
    }

    private static String sha256Hex(byte[] bytes) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256").digest(bytes);
        StringBuilder hex = new StringBuilder();
        for (byte b : digest) {
            hex.append(String.format("%02x", b));
        }
        return hex.toString();
    }

    public static void main(String[] args) throws Exception {
        System.out.println("=== Semantic Production Gate Test (ISSUE-0239 E10) ===\n");
        testEmitterSeam();
        testAllSharedLuaJit();
        testAllSharedJvm();
        testSharedTableMemberReadRuns();
        testRouteSelectionWithoutFallback();
        testAdapterShapeReroutesLegacy();
        testBytesBearingRetainedRoute();
        testStep1CutoverPromotion();
        testStep1RegistryDigestRecomputation();
        testStep2CutoverPromotion();
        testStep2RegistryDigestRecomputation();
        testStep3CutoverPromotion();
        testStep3RegistryDigestRecomputation();
        testStep4CutoverPromotion();
        testStep4RegistryDigestRecomputation();
        testStep5CutoverPromotion();
        testStep5RegistryDigestRecomputation();
        testFailurePreservesPriorArtifacts();
        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
