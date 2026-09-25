package deal.test;

import deal.module.CompilationOrchestrator;
import deal.module.CompilerClassDefaultEntry;
import deal.module.CompilerClassDefaultPlan;
import deal.module.PlannedDefaultClass;
import deal.module.ResolvedDefaultExpression;
import deal.codegen.Backend;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

/**
 * The ISSUE-0545 construction-phase consumption battery (design sources
 * {@code runtime-default-evaluators-and-construction-phases} D4-D6 and
 * {@code deal-v1.2-int32-and-bytes-architecture} D5): repeated real
 * constructions prove counts, ordering, freshness, isolation, retained
 * function/bytes references, optional omission, failure timing, retained
 * effects, and zero import-time evaluation across the normal, C-struct,
 * and JSON construction paths on the three production backends — plus
 * the end-to-end composition scenario over the semantic identity,
 * canonical descriptor, declaration marker, and bytes-value contracts.
 *
 * <p>Coverage:</p>
 * <ol>
 *   <li><b>Repeated normal construction (LuaJIT, JVM, JavaScript):</b>
 *       provided expressions evaluate left-to-right with a
 *       provided-value failure (E8002) raising before any default;
 *       provided required fields suppress their evaluators entirely;
 *       each omitted required default evaluates exactly once per
 *       attempt in declaration order (host-side call counters);
 *       fresh mutable table and bytes literals per attempt; absent
 *       optionals stay absent and never evaluate; a later default
 *       failure retains the completed evaluator effects, publishes no
 *       instance, and leaves the next attempt independent; zero
 *       evaluator invocations at module load.</li>
 *   <li><b>Repeated JSON construction (LuaJIT, JVM, JavaScript):</b>
 *       the parse/object/key/decode gates precede every default (each
 *       specified failure returns the DEAL null with the counter at
 *       zero); omitted required defaults evaluate once per attempt in
 *       declaration order; provided fields suppress their evaluators;
 *       fresh mutable table literals per attempt; optional omission
 *       and the three-state provided null; an evaluator failure
 *       returns the DEAL null, publishes no instance, and retains the
 *       completed earlier effects; zero evaluator invocations at
 *       module load.</li>
 *   <li><b>Repeated C-struct construction (LuaJIT):</b> a real
 *       extern-C declaration module with a {@code @c-struct} class
 *       whose default calls a native function — GCC-compiled committed
 *       fixture, production CLI compile, production
 *       {@code __rt.load_ffi}, and plan-driven construction through
 *       {@code __rt.class_plan_}: zero native calls at load, the
 *       default evaluates once per omitted attempt, a provided field
 *       suppresses the native call, and the native counter proves the
 *       per-attempt counts.</li>
 *   <li><b>End-to-end composition:</b> an out-of-root class-free
 *       provider (E2 private semantic identity) feeds a rooted class
 *       default and a {@code @jsonable} marker class (E5) through
 *       canonical descriptors (E4) with a bytes-value field (E6) on
 *       all three backends; the consumer default's semantic digest is
 *       stable across unchanged rebuilds, changes when the provider
 *       body changes (embedded provider digest), and a broken
 *       dependency (the import specifier renamed) fails the compile
 *       with no plan and no artifact.</li>
 * </ol>
 *
 * <p>Runs via main() using the repository's plain check()-helper
 * convention (no JUnit dependency; assertion failures exit non-zero).
 * The luajit, node, javac/java, and gcc tools are probed per section; a
 * missing tool fails the corresponding gate (never a silent skip).</p>
 */
public class RuntimeConstructionPhasesTest {

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

    /**
     * The harness invocation of this battery's compiles (ISSUE-0643 P10
     * item 3): every fixture of the A/B/D sections carries a construct
     * the release-owned production invocation does not realize at this
     * boundary (host declaration imports, bytes, {@code @jsonable}
     * construction), so the in-process compiles resolve the
     * COMMON_SHADOW harness invocation and keep the harness arm's
     * retained per-module artifacts and runtime assertions unchanged.
     */
    private static CompilerInvocation invocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
    }

    /**
     * Runs the test-scope harness compile entry in-process with
     * System.err captured (ISSUE-0643 P10 item 3, mechanism 1).
     */
    private static RunResult runHarnessCli(String[] args) throws Exception {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = HarnessCompileEntry.run(args);
            System.err.flush();
        } finally {
            System.setErr(originalErr);
        }
        return new RunResult(exitCode,
            err.toString(StandardCharsets.UTF_8).trim());
    }

    /**
     * Runs the release-owned production CLI in-process with System.err
     * captured (the production-invocation fail-closed assertions of this
     * battery).
     */
    private static RunResult runProductionCli(String[] args) throws Exception {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = deal.Main.run(args);
            System.err.flush();
        } finally {
            System.setErr(originalErr);
        }
        return new RunResult(exitCode,
            err.toString(StandardCharsets.UTF_8).trim());
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(f -> {
                    try {
                        Files.deleteIfExists(f);
                    } catch (Exception ignored) {
                    }
                });
        } catch (Exception ignored) {
        }
    }

    private static void write(Path root, String rel, String content)
            throws Exception {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
    }

    private static boolean toolAvailable(String... command) {
        try {
            return new ProcessBuilder(command).start().waitFor() == 0;
        } catch (Exception e) {
            return false;
        }
    }

    /**
     * One isolated-phase production compile over a scratch source tree:
     * the same tree compiles for the requested backend through the
     * production orchestrator (planner + serializer + graph +
     * lowerers).
     */
    private static final class Compile {
        final Path root;
        final Path entry;
        final Path outputRoot;
        final CompilationOrchestrator orchestrator;
        final boolean success;

        Compile(Path root, Path entry, Backend backend, String outputName,
                Map<String, String> externals) throws Exception {
            this.root = root;
            this.entry = entry;
            this.outputRoot = root.resolve("build-" + outputName);
            orchestrator = new CompilationOrchestrator(
                entry, outputRoot, false, false, false, false, backend,
                externals, List.of(root.resolve("src")), null, null,
                invocation());
            success = orchestrator.compile();
        }
    }

    private record RunResult(int exitCode, String output) {}

    private static RunResult runProcess(Path dir, String... command)
            throws Exception {
        ProcessBuilder pb = new ProcessBuilder(command);
        pb.directory(dir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes());
        int exit = p.waitFor();
        return new RunResult(exit, output.trim());
    }

    /** Runs the LuaJIT entry artifact from the published build root. */
    private static RunResult runLua(Compile compile) throws Exception {
        return runProcess(compile.outputRoot, "luajit", "main.lua");
    }

    /** Runs the JS entry artifact from the published build root. */
    private static RunResult runJs(Compile compile) throws Exception {
        return runProcess(compile.outputRoot, "node", "main.js");
    }

    /** Compiles every generated JVM artifact and runs the entry class. */
    private static RunResult runJvm(Compile compile) throws Exception {
        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(compile.outputRoot)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                .sorted()
                .forEach(p -> javaFiles.add(
                    p.getFileName().toString()));
        }
        List<String> javac = new ArrayList<>(List.of("javac"));
        javac.addAll(javaFiles);
        RunResult compileRun = runProcess(compile.outputRoot,
            javac.toArray(new String[0]));
        if (compileRun.exitCode() != 0) {
            return new RunResult(1, "javac failed: "
                + compileRun.output());
        }
        return runProcess(compile.outputRoot, "java", "Main");
    }

    /**
     * Writes the host probe trio beside a scratch project: the
     * declaration file plus the Lua/JS/Java implementations of the
     * mutable host-side invocation counters (the ISSUE-0545 phase
     * probe).
     */
    private static void writePhaseProbe(Path root) throws Exception {
        write(root, "host/phaseprobe.d.deal",
            "// Host probe declaration for the ISSUE-0545 construction"
                + " phases: mutable host-side invocation counters.\n"
                + "export function tick(): int;\n"
                + "export function count(): int;\n");
        write(root, "host/phaseprobe.lua",
            "-- Host fixture implementation for the ISSUE-0545"
                + " construction-phase fixtures. tick() increments a\n"
                + "-- module counter and returns the count * 10;"
                + " count() reads it — every evaluator invocation is\n"
                + "-- observable from the host side.\n"
                + "local n = 0\n"
                + "return {\n"
                + "  tick = function()\n"
                + "    n = n + 1\n"
                + "    return n * 10\n"
                + "  end,\n"
                + "  count = function()\n"
                + "    return n\n"
                + "  end,\n"
                + "}\n");
        write(root, "host/phaseprobe.js",
            "\"use strict\";\n"
                + "// Host fixture implementation for the ISSUE-0545"
                + " construction-phase fixtures (Node lane): the\n"
                + "// mutable counter mirror of the Lua host fixture.\n"
                + "let n = 0;\n"
                + "module.exports = {\n"
                + "  tick: function () {\n"
                + "    n = n + 1;\n"
                + "    return n * 10;\n"
                + "  },\n"
                + "  count: function () {\n"
                + "    return n;\n"
                + "  },\n"
                + "};\n");
        write(root, "host/HostPhaseprobe.java",
            "// Host fixture implementation for the ISSUE-0545"
                + " construction-phase fixtures (JVM lane): the\n"
                + "// mutable static counter mirror of the Lua host"
                + " fixture.\n"
                + "final class HostPhaseprobe {\n"
                + "  private static long n = 0L;\n"
                + "\n"
                + "  public static Object tick() {\n"
                + "    n = n + 1;\n"
                + "    return Long.valueOf(n * 10L);\n"
                + "  }\n"
                + "\n"
                + "  public static Object count() {\n"
                + "    return Long.valueOf(n);\n"
                + "  }\n"
                + "}\n");
    }

    /** Deploys the host probe implementation beside one backend's
     * published artifacts (the {@code host/} raw slash-form require
     * path for Lua/JS, the {@code HostPhaseprobe.java} artifact name
     * for the JVM host slice). */
    private static void deployPhaseProbe(Path outputRoot, String ext)
            throws Exception {
        Path root = Files.createTempDirectory("deal_phases_deploy_");
        try {
            writePhaseProbe(root);
            if (ext.equals("java")) {
                Files.copy(root.resolve("host/HostPhaseprobe.java"),
                    outputRoot.resolve("HostPhaseprobe.java"));
                return;
            }
            Files.createDirectories(outputRoot.resolve("host"));
            Files.copy(root.resolve("host/phaseprobe." + ext),
                outputRoot.resolve("host").resolve("phaseprobe." + ext));
        } finally {
            deleteRecursively(root);
        }
    }

    private static Map<String, String> phaseProbeExternals(Path root) {
        return Map.of("host/phaseprobe", root.resolve("host")
            .resolve("phaseprobe.d.deal").toString());
    }

    /** The published compiler plan of the named class in the main
     * module of the given compile. */
    private static CompilerClassDefaultPlan planOf(Compile compile,
                                                   String className) {
        List<PlannedDefaultClass> plans = compile.orchestrator
            .completedPlansByModulePath().get("main");
        if (plans == null) {
            return null;
        }
        for (PlannedDefaultClass planned : plans) {
            if (planned.declaration().name().equals(className)) {
                return planned.plan();
            }
        }
        return null;
    }

    /** The semantic digest of the named class's named field default. */
    private static String digestOf(Compile compile, String className,
                                   String fieldName) {
        CompilerClassDefaultPlan plan = planOf(compile, className);
        if (plan == null) {
            return null;
        }
        for (CompilerClassDefaultEntry entry : plan.orderedFields()) {
            if (entry.name().equals(fieldName)) {
                ResolvedDefaultExpression expression =
                    entry.defaultExpression();
                return expression == null ? null
                    : expression.semanticDigest();
            }
        }
        return null;
    }

    // =========================================================================
    // Section A: repeated normal construction on all three backends
    // =========================================================================

    private static void testRepeatedNormalConstruction() throws Exception {
        System.out.println("-- Repeated normal construction: counts,"
            + " order, freshness, optional omission, failure timing,"
            + " retained effects, zero load-time evaluation"
            + " (LuaJIT, JVM, JavaScript) --");
        Path root = Files.createTempDirectory("deal_phases_normal_");
        Path entry = root.resolve("src/main.deal").toAbsolutePath()
            .normalize();
        writePhaseProbe(root);
        write(root, "src/main.deal", """
                import * as probe from "host/phaseprobe"

                function boom(): int {
                  throw { code: "BOOM", message: "deferred evaluator failure" };
                }

                function pick(): int {
                  let xs: int[] = [1];
                  return xs[-1];
                }

                class Phase {
                  a: int = probe.tick();
                  b: int = probe.tick();
                  seed: table = { v: 1 };
                  payload: bytes = bytes(2);
                  opt?: string = "metadata-only";
                  boom: int = boom();
                }

                export function main(): null {
                  // Module load finished: no evaluator has run yet.
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "evaluator ran at load" };
                  }

                  // Provided expressions evaluate left-to-right at the
                  // construction site; a provided-value failure (E8002)
                  // raises before any default evaluation. (Boolean
                  // flags, never Error-typed locals — the JVM class
                  // contract keeps Error values out of local slots.)
                  let e8002: boolean = false;
                  try {
                    let c: Phase = { a: pick(), b: 7 };
                  } catch (e) {
                    e8002 = e.code === "E8002";
                  }
                  if (!e8002) {
                    throw { code: "TEST_FAIL", message: "provided-value failure did not raise E8002" };
                  }
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "default ran after a provided-value failure" };
                  }

                  // Provided required fields suppress their defaults
                  // entirely.
                  let full: Phase = { a: 5, b: 6, seed: { v: 9 }, payload: bytes(1), boom: 0 };
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "defaults evaluated for provided fields" };
                  }

                  // Omitted required defaults evaluate exactly once per
                  // attempt, in declaration order (a then b).
                  let p1: Phase = { boom: 0 };
                  if (probe.count() !== 2) {
                    throw { code: "TEST_FAIL", message: "defaults did not run once per attempt" };
                  }
                  if (p1.a !== 10 || p1.b !== 20) {
                    throw { code: "TEST_FAIL", message: "defaults ran out of declaration order" };
                  }
                  let p2: Phase = { boom: 0 };
                  if (probe.count() !== 4) {
                    throw { code: "TEST_FAIL", message: "second attempt count mismatch" };
                  }

                  // Fresh mutable table and bytes literals per attempt.
                  p1.seed.v = 42;
                  let p2v: int | null = p2.seed.v;
                  if (p2v !== null) {
                    if (p2v !== 1) {
                      throw { code: "TEST_FAIL", message: "table default shared across instances" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "table default read null" };
                  }
                  p1.payload[0] = 9;
                  if (p2.payload[0] !== 0) {
                    throw { code: "TEST_FAIL", message: "bytes default shared across instances" };
                  }

                  // Optional omissions stay absent and never evaluate.
                  if (has(p1.opt)) {
                    throw { code: "TEST_FAIL", message: "optional present without a provided value" };
                  }
                  let optRead: string | null = p1.opt;
                  if (optRead !== null) {
                    throw { code: "TEST_FAIL", message: "absent optional read is not null" };
                  }

                  // A later default failure keeps the completed
                  // evaluator effects and publishes nothing; the next
                  // attempt starts from independent unpublished slots.
                  let boomSeen: boolean = false;
                  try {
                    let bad: Phase = {};
                  } catch (e) {
                    boomSeen = e.code === "BOOM";
                  }
                  if (!boomSeen) {
                    throw { code: "TEST_FAIL", message: "evaluator failure did not raise BOOM" };
                  }
                  if (probe.count() !== 6) {
                    throw { code: "TEST_FAIL", message: "completed effects were rolled back" };
                  }
                  let p3: Phase = { boom: 0 };
                  if (probe.count() !== 8) {
                    throw { code: "TEST_FAIL", message: "clean attempt after failure did not re-run a/b once" };
                  }
                  if (p3.a !== 70 || p3.b !== 80) {
                    throw { code: "TEST_FAIL", message: "post-failure attempt defaults mismatch" };
                  }
                  return null;
                }
                """);
        try {
            Map<String, String> externals = phaseProbeExternals(root);
            Compile luajit = new Compile(root, entry, Backend.LUAJIT,
                "luajit", externals);
            Compile jvm = new Compile(root, entry, Backend.JVM,
                "jvm", externals);
            Compile js = new Compile(root, entry, Backend.JS,
                "js", externals);
            for (Compile compile : List.of(luajit, jvm, js)) {
                check(compile.success, "the normal fixture compiles ("
                    + compile.orchestrator.diagnostics() + ")");
            }
            if (!luajit.success || !jvm.success || !js.success) {
                return;
            }
            if (toolAvailable("luajit", "-v")) {
                deployPhaseProbe(luajit.outputRoot, "lua");
                RunResult lua = runLua(luajit);
                check(lua.exitCode() == 0,
                    "LuaJIT normal run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " normal gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                deployPhaseProbe(js.outputRoot, "js");
                RunResult jsRun = runJs(js);
                check(jsRun.exitCode() == 0,
                    "JS normal run exits 0: " + jsRun.output());
            } else {
                check(false, "node is unavailable — the JS normal"
                    + " gate cannot run");
            }
            deployPhaseProbe(jvm.outputRoot, "java");
            RunResult jvmRun = runJvm(jvm);
            check(jvmRun.exitCode() == 0,
                "JVM normal run exits 0: " + jvmRun.output());
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // Section B: repeated JSON construction on all three backends
    // =========================================================================

    private static void testRepeatedJsonConstruction() throws Exception {
        System.out.println("-- Repeated JSON construction: parse/object/"
            + "key/decode gates before defaults, null collapse, counts,"
            + " freshness, optional states, retained effects"
            + " (LuaJIT, JVM, JavaScript) --");
        Path root = Files.createTempDirectory("deal_phases_json_");
        Path entry = root.resolve("src/main.deal").toAbsolutePath()
            .normalize();
        writePhaseProbe(root);
        write(root, "src/main.deal", """
                import * as probe from "host/phaseprobe"

                function boom(): int {
                  throw { code: "BOOM", message: "deferred evaluator failure" };
                }

                // @jsonable
                export class Doc {
                  a: int = probe.tick();
                  b: int = probe.tick();
                  seed: table = { v: 1 };
                  opt?: string | null = "metadata-only";
                  boom: int = boom();
                }

                export function main(): null {
                  // Module load finished: no evaluator has run yet.
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "evaluator ran at load" };
                  }

                  // Parse/object/key gates precede every default: each
                  // specified failure returns the DEAL null. (Every
                  // fromJson call binds to a local first — the Lua
                  // null-comparison lowering duplicates an inline
                  // side-effecting operand, so an inline call would
                  // evaluate twice.)
                  let gate1: Doc | null = Doc$fromJson("not-json");
                  if (gate1 !== null) {
                    throw { code: "TEST_FAIL", message: "malformed input did not collapse" };
                  }
                  let gate2: Doc | null = Doc$fromJson("null");
                  if (gate2 !== null) {
                    throw { code: "TEST_FAIL", message: "null document did not collapse" };
                  }
                  let gate3: Doc | null = Doc$fromJson("[1,2]");
                  if (gate3 !== null) {
                    throw { code: "TEST_FAIL", message: "array document did not collapse" };
                  }
                  let gate4: Doc | null = Doc$fromJson("{\\"extra\\":1}");
                  if (gate4 !== null) {
                    throw { code: "TEST_FAIL", message: "extra key did not collapse" };
                  }
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "default ran after an input gate failure" };
                  }

                  // A provided-value decode failure precedes every
                  // default and returns the DEAL null.
                  let gate5: Doc | null = Doc$fromJson("{\\"a\\":\\"x\\"}");
                  if (gate5 !== null) {
                    throw { code: "TEST_FAIL", message: "decode failure did not collapse" };
                  }
                  if (probe.count() !== 0) {
                    throw { code: "TEST_FAIL", message: "default ran after a decode failure" };
                  }
                  // Omitted required defaults evaluate once per
                  // attempt, in declaration order (a then b).
                  let d1: Doc | null = Doc$fromJson("{\\"boom\\":9}");
                  if (d1 !== null) {
                    if (probe.count() !== 2) {
                      throw { code: "TEST_FAIL", message: "JSON defaults did not run once per attempt" };
                    }
                    if (d1.a !== 10 || d1.b !== 20) {
                      throw { code: "TEST_FAIL", message: "JSON defaults ran out of declaration order" };
                    }
                    if (d1.boom !== 9) {
                      throw { code: "TEST_FAIL", message: "provided boom decode mismatch" };
                    }
                    d1.seed.v = 7;
                  } else {
                    throw { code: "TEST_FAIL", message: "valid document decoded null" };
                  }

                  let d2: Doc | null = Doc$fromJson("{\\"boom\\":9}");
                  if (d2 !== null) {
                    if (probe.count() !== 4) {
                      throw { code: "TEST_FAIL", message: "second JSON attempt count mismatch" };
                    }
                    let d2v: int | null = d2.seed.v;
                    if (d2v !== null) {
                      if (d2v !== 1) {
                        throw { code: "TEST_FAIL", message: "table default shared across JSON attempts" };
                      }
                    } else {
                      throw { code: "TEST_FAIL", message: "JSON table default read null" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "second valid document decoded null" };
                  }

                  // Provided required fields suppress their defaults.
                  let d3: Doc | null = Doc$fromJson("{\\"a\\":1,\\"b\\":2,\\"boom\\":3}");
                  if (d3 !== null) {
                    if (probe.count() !== 4) {
                      throw { code: "TEST_FAIL", message: "defaults evaluated for JSON-provided fields" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "fully provided document decoded null" };
                  }

                  // Optional omissions stay absent and never evaluate.
                  if (d1 !== null) {
                    if (has(d1.opt)) {
                      throw { code: "TEST_FAIL", message: "JSON optional present without a provided value" };
                    }
                  }

                  // Three-state: a provided null stays present-null.
                  let d4: Doc | null = Doc$fromJson("{\\"a\\":1,\\"b\\":2,\\"boom\\":3,\\"opt\\":null}");
                  if (d4 !== null) {
                    if (!has(d4.opt) || d4.opt !== null) {
                      throw { code: "TEST_FAIL", message: "provided null optional state mismatch" };
                    }
                    if (probe.count() !== 4) {
                      throw { code: "TEST_FAIL", message: "provided null evaluated a default" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "provided-null document decoded null" };
                  }

                  // An evaluator failure returns the DEAL null,
                  // publishes no instance, and keeps the completed
                  // earlier effects (count 6 = 4 + a + b of the failed
                  // attempt).
                  let gate6: Doc | null = Doc$fromJson("{}");
                  if (gate6 !== null) {
                    throw { code: "TEST_FAIL", message: "evaluator failure did not collapse to null" };
                  }
                  if (probe.count() !== 6) {
                    throw { code: "TEST_FAIL", message: "JSON completed effects were rolled back" };
                  }
                  return null;
                }
                """);
        try {
            Map<String, String> externals = phaseProbeExternals(root);
            Compile luajit = new Compile(root, entry, Backend.LUAJIT,
                "luajit", externals);
            Compile jvm = new Compile(root, entry, Backend.JVM,
                "jvm", externals);
            Compile js = new Compile(root, entry, Backend.JS,
                "js", externals);
            for (Compile compile : List.of(luajit, jvm, js)) {
                check(compile.success, "the JSON fixture compiles ("
                    + compile.orchestrator.diagnostics() + ")");
            }
            if (!luajit.success || !jvm.success || !js.success) {
                return;
            }
            if (toolAvailable("luajit", "-v")) {
                deployPhaseProbe(luajit.outputRoot, "lua");
                RunResult lua = runLua(luajit);
                check(lua.exitCode() == 0,
                    "LuaJIT JSON run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " JSON gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                deployPhaseProbe(js.outputRoot, "js");
                RunResult jsRun = runJs(js);
                check(jsRun.exitCode() == 0,
                    "JS JSON run exits 0: " + jsRun.output());
            } else {
                check(false, "node is unavailable — the JS JSON"
                    + " gate cannot run");
            }
            deployPhaseProbe(jvm.outputRoot, "java");
            RunResult jvmRun = runJvm(jvm);
            check(jvmRun.exitCode() == 0,
                "JVM JSON run exits 0: " + jvmRun.output());
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // Section C: repeated C-struct construction (LuaJIT, real native)
    // =========================================================================

    private static void testRepeatedCStructConstruction() throws Exception {
        System.out.println("-- Repeated C-struct construction through"
            + " load_ffi: per-attempt defaults, provided-field"
            + " suppression, zero native calls at load (LuaJIT) --");
        if (!toolAvailable("gcc", "--version")) {
            check(false, "gcc is unavailable — the C-struct gate"
                + " cannot build its native fixture");
            return;
        }
        if (!toolAvailable("luajit", "-v")) {
            check(false, "luajit is unavailable — the C-struct gate"
                + " cannot run");
            return;
        }
        Path root = Files.createTempDirectory("deal_phases_cstruct_");
        Path buildDir = Path.of("build").toAbsolutePath().normalize();
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\",\n"
                    + "  \"externals\": {\n"
                    + "    \"ffi/valid\": {\n"
                    + "      \"declaration\": \"ffi.d.deal\",\n"
                    + "      \"nativeLibrary\": \"libs/phase-ffi.so\"\n"
                    + "    }\n  }\n}\n");
            write(root, "ffi.d.deal",
                "// @extern-c\n"
                    + "\n"
                    + "// @c-struct\n"
                    + "export class Probe {\n"
                    + "  count: int = fixture_count_call_int();\n"
                    + "}\n"
                    + "\n"
                    + "export function fixture_count_call(): null;\n"
                    + "export function fixture_count_call_int(): int;\n"
                    + "export function fixture_call_count(): int;\n"
                    + "export function fixture_reset_counter(): null;\n");
            write(root, "src/main.deal",
                "import * as ffi from \"ffi/valid\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  // Module load finished: load_ffi performed zero"
                    + " default evaluation and zero native calls.\n"
                    + "  if (ffi.fixture_call_count() !== 0) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"native call at load\" };\n"
                    + "  }\n"
                    + "  // The omitted required default evaluates once"
                    + " per attempt through the native forward cell.\n"
                    + "  let p1: ffi.Probe = {};\n"
                    + "  if (p1.count !== 1) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"first construction default\" };\n"
                    + "  }\n"
                    + "  // A provided field suppresses the native"
                    + " default call entirely.\n"
                    + "  let p2: ffi.Probe = { count: 99 };\n"
                    + "  if (p2.count !== 99) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"provided field\" };\n"
                    + "  }\n"
                    + "  if (ffi.fixture_call_count() !== 1) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"default ran for a provided field\" };\n"
                    + "  }\n"
                    + "  // A second attempt re-executes the default"
                    + " through the plan.\n"
                    + "  let p3: ffi.Probe = {};\n"
                    + "  if (p3.count !== 2) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"second construction default\" };\n"
                    + "  }\n"
                    + "  if (ffi.fixture_call_count() !== 2) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"per-attempt count mismatch\" };\n"
                    + "  }\n"
                    + "  return null;\n"
                    + "}\n");
            // Bootstrap the committed native fixture with GCC into the
            // manifest-relative loader path (the committed fixture
            // declares no real prototypes shared with DEAL; the cdef
            // bundle supplies the private types).
            Files.createDirectories(root.resolve("libs"));
            String eventsPath = root.resolve("events.log").toString();
            RunResult gcc = runProcess(root, "gcc", "-shared", "-fPIC",
                "-O2", "-DFIXTURE_EVENTS_PATH=\"" + eventsPath + "\"",
                "-o", "libs/phase-ffi.so",
                Path.of("test", "fixtures", "ffigen",
                    "ffigen-integration-fixture.c").toAbsolutePath()
                    .normalize().toString());
            check(gcc.exitCode() == 0,
                "the native fixture GCC compile succeeds: " + gcc.output());
            if (gcc.exitCode() != 0) {
                return;
            }
            // The extern-C project compiles in-process through the
            // test-scope harness invocation (ISSUE-0643 P10 item 3): the
            // fixture carries a HOST-kind extern-C declaration import, so
            // the harness arm produces the retained per-module artifact
            // set (main.lua) the run below executes.
            Path outDir = root.resolve("build/lua");
            RunResult cli = runHarnessCli(new String[]{
                "compile",
                root.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "lua", "--output", outDir.toString()});
            check(cli.exitCode() == 0,
                "the extern-C project compiles through the harness"
                    + " invocation: " + cli.output());
            if (cli.exitCode() != 0) {
                return;
            }

            // The extern-C admission slice (ISSUE-0662): the same fixture
            // through the release-owned production invocation is admitted
            // (the extern-C import no longer trips the host-kind guard) and
            // still fails closed with E6005 SHARED_EMITTER_COVERAGE on the
            // declaration-class construction (the CLASS_NEW over the
            // extern-C class resolves no layout before the construction
            // child lands), staging nothing.
            Path prodOut = root.resolve("build/prod-lua");
            RunResult prod = runProductionCli(new String[]{
                "compile",
                root.resolve("src/main.deal").toAbsolutePath().toString(),
                "--backend", "lua", "--output", prodOut.toString()});
            check(prod.exitCode() != 0
                    && prod.output().contains("E6005")
                    && prod.output().contains("CONSTRUCTION_COHERENCE"),
                "the release-owned production invocation fails the extern-C"
                    + " project closed with E6005 CONSTRUCTION_COHERENCE (the"
                    + " declaration-class construction is the construction"
                    + " child's): " + prod.output());
            check(!Files.exists(prodOut),
                "the production failure stages no artifact under " + prodOut);

            RunResult run = runProcess(outDir, "luajit", "main.lua");
            check(run.exitCode() == 0,
                "the C-struct repeated-construction run exits 0: "
                    + run.output());
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // Section D: end-to-end composition and the breaking-dependency arms
    // =========================================================================

    private static void testEndToEndComposition() throws Exception {
        System.out.println("-- End-to-end composition: out-of-root"
            + " class-free provider, jsonable marker, bytes values,"
            + " stable and provider-sensitive identity, broken"
            + " dependency fails (LuaJIT, JVM, JavaScript) --");
        Path root = Files.createTempDirectory("deal_phases_compose_");
        Path entry = root.resolve("src/main.deal").toAbsolutePath()
            .normalize();
        write(root, "src/main.deal", """
                import * as S from "../shared"

                class Comp {
                  n: int = S.double(21);
                  buf: bytes = bytes(1);
                }

                // @jsonable
                export class Tagged {
                  n: int = S.double(5);
                  note?: string | null;
                }

                export function main(): null {
                  let c: Comp = {};
                  if (c.n !== 42) {
                    throw { code: "TEST_FAIL", message: "out-of-root provider default" };
                  }
                  c.buf[0] = 7;
                  let t: Tagged | null = Tagged$fromJson("{}");
                  if (t !== null) {
                    if (t.n !== 10) {
                      throw { code: "TEST_FAIL", message: "jsonable provider default" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "jsonable fromJson null" };
                  }
                  let t2: Tagged | null = Tagged$fromJson("{\\"n\\":3,\\"note\\":null}");
                  if (t2 !== null) {
                    if (t2.n !== 3 || !has(t2.note) || t2.note !== null) {
                      throw { code: "TEST_FAIL", message: "jsonable provided decode" };
                    }
                  } else {
                    throw { code: "TEST_FAIL", message: "jsonable provided decode null" };
                  }
                  return null;
                }
                """);
        write(root, "shared.deal", """
                export function double(x: int): int {
                  return x * 2;
                }
                """);
        try {
            Compile luajit = new Compile(root, entry, Backend.LUAJIT,
                "luajit", Map.of());
            Compile jvm = new Compile(root, entry, Backend.JVM,
                "jvm", Map.of());
            Compile js = new Compile(root, entry, Backend.JS,
                "js", Map.of());
            for (Compile compile : List.of(luajit, jvm, js)) {
                check(compile.success, "the composition fixture compiles"
                    + " (" + compile.orchestrator.diagnostics() + ")");
            }
            if (!luajit.success || !jvm.success || !js.success) {
                return;
            }
            String digestBefore = digestOf(luajit, "Comp", "n");
            check(digestBefore != null && digestBefore.length() == 64,
                "the consumer default carries a semantic digest");
            // The plan carries the imported provider's resource
            // reference with a provider contract digest.
            CompilerClassDefaultPlan compPlan = planOf(luajit, "Comp");
            check(compPlan != null
                    && !compPlan.runtimeDependencies().isEmpty(),
                "the consumer plan carries the imported runtime"
                    + " dependency edge");
            if (toolAvailable("luajit", "-v")) {
                RunResult lua = runLua(luajit);
                check(lua.exitCode() == 0,
                    "LuaJIT composition run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " composition gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                RunResult jsRun = runJs(js);
                check(jsRun.exitCode() == 0,
                    "JS composition run exits 0: " + jsRun.output());
            } else {
                check(false, "node is unavailable — the JS composition"
                    + " gate cannot run");
            }
            RunResult jvmRun = runJvm(jvm);
            check(jvmRun.exitCode() == 0,
                "JVM composition run exits 0: " + jvmRun.output());

            // An unchanged rebuild keeps the consumer identity stable.
            Compile rebuild = new Compile(root, entry, Backend.LUAJIT,
                "rebuild", Map.of());
            check(rebuild.success, "the unchanged rebuild compiles");
            if (rebuild.success) {
                String digestRebuild = digestOf(rebuild, "Comp", "n");
                check(digestBefore.equals(digestRebuild),
                    "an unchanged provider leaves the consumer default"
                        + " digest stable across runs");
            }

            // A provider implementation change (behavior-preserving:
            // x * 2 -> x * 2 + 0) changes the provider digest and
            // thereby the consumer's semantic identity before any reuse.
            write(root, "shared.deal", """
                    export function double(x: int): int {
                      return x * 2 + 0;
                    }
                    """);
            Compile changed = new Compile(root, entry, Backend.LUAJIT,
                "changed", Map.of());
            check(changed.success, "the changed-provider fixture"
                + " compiles (" + changed.orchestrator.diagnostics()
                + ")");
            if (changed.success) {
                String digestChanged = digestOf(changed, "Comp", "n");
                check(digestChanged != null
                        && !digestBefore.equals(digestChanged),
                    "a provider implementation change changes the"
                        + " consumer default semantic digest");
                RunResult changedRun = runLua(changed);
                check(changedRun.exitCode() == 0,
                    "the changed-provider composition run still exits 0: "
                        + changedRun.output());
            }

            // A broken dependency — the import specifier renamed — fails
            // the compile with no plan and no artifact.
            Path broken = Files.createTempDirectory(
                "deal_phases_broken_");
            try {
                write(broken, "src/main.deal", """
                        import * as S from "../missing"

                        class Comp {
                          n: int = S.double(21);
                        }

                        export function main(): null {
                          return null;
                        }
                        """);
                Path brokenEntry = broken.resolve("src/main.deal")
                    .toAbsolutePath().normalize();
                Compile brokenCompile = new Compile(broken, brokenEntry,
                    Backend.LUAJIT, "broken", Map.of());
                check(!brokenCompile.success,
                    "the broken-dependency fixture fails to compile");
                check(brokenCompile.orchestrator.diagnostics()
                        .toString().contains("missing"),
                    "the broken-dependency failure names the unresolved"
                        + " specifier: " + brokenCompile.orchestrator
                        .diagnostics());
                check(!Files.exists(brokenCompile.outputRoot
                        .resolve("main.lua")),
                    "the broken-dependency compile publishes no entry"
                        + " artifact");
            } finally {
                deleteRecursively(broken);
            }
        } finally {
            deleteRecursively(root);
        }
    }

    public static void main(String[] args) throws Exception {
        testRepeatedNormalConstruction();
        testRepeatedJsonConstruction();
        testRepeatedCStructConstruction();
        testEndToEndComposition();
        System.out.println();
        if (failed > 0) {
            System.out.println("RuntimeConstructionPhasesTest: "
                + passed + " passed, " + failed + " failed");
            System.exit(1);
        }
        System.out.println("RuntimeConstructionPhasesTest: "
            + passed + " passed, 0 failed");
    }
}
