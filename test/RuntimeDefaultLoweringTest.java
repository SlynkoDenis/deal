package deal.test;

import deal.module.CompilationOrchestrator;
import deal.module.CompilerClassDefaultEntry;
import deal.module.CompilerClassDefaultPlan;
import deal.module.DefaultRuntimeAbiVersion;
import deal.module.PlannedDefaultClass;
import deal.module.RuntimeClassDefaultEntry;
import deal.module.RuntimeClassDefaultPlan;
import deal.module.RuntimeDefaultEvaluator;
import deal.module.RuntimeDefaultPlanLowering;
import deal.codegen.Backend;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;

import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

/**
 * The backend evaluator lowering and runtime plan realization battery of
 * ISSUE-0544 (design sources
 * {@code runtime-default-evaluators-and-construction-phases} D1-D3/D6 and
 * the task-pinned acceptance criteria): every published compiler default
 * plan realized as executable LuaJIT, JVM, and JavaScript runtime plans
 * — exercised through the real orchestrator path (the isolated-phase
 * constructor &rarr; production {@code CompilationOrchestrator} &rarr;
 * {@code compile()}) with the same source tree compiled for all three
 * backends, so the per-entry semantic digests stay byte-comparable
 * across backends.
 *
 * <p>Coverage:</p>
 * <ol>
 *   <li><b>Published-plan shape (all three backends):</b> entry order
 *       in class source order, field names, canonical descriptors,
 *       optional flags, and evaluators exactly on required-present
 *       entries — pinned over the generated Lua plan tables, the JS
 *       defaults thunks, the JVM static plan records, and the realized
 *       {@code RuntimeClassDefaultPlan} carriers.</li>
 *   <li><b>Evaluator signatures and labels:</b> zero-argument closures
 *       (Lua {@code function() ... end}, the JS thunk projection, the
 *       JVM static methods) labelled with the pinned
 *       {@code (classIdentity, fieldName, semanticDigest)} triple in
 *       the generated artifacts.</li>
 *   <li><b>Declaring-scope binding:</b> a module-local default
 *       function executes in the declaring module's scope, including
 *       imported construction through the provider's plan after
 *       dependency-ordered initialization (the JVM provider record
 *       path included).</li>
 *   <li><b>Order, freshness, zero import-time evaluation, and
 *       reference retention:</b> real artifact execution on luajit,
 *       node, and javac/java — per-construction default evaluation in
 *       class source order, fresh table literals per attempt, a shared
 *       {@code bytes} field default retained by reference across
 *       instances, and zero evaluator invocations at module load.</li>
 *   <li><b>Versioning:</b> the per-entry semantic digests equal the
 *       compiler plan's digests byte-for-byte on every backend; the
 *       implementation digests are 64-hex SHA-256 and differ across
 *       the three backends for the same semantics (D3); the epic
 *       constant {@code DefaultRuntimeAbiVersion.CURRENT} is
 *       {@code "1"}.</li>
 *   <li><b>Host exemption:</b> host-declared classes produce no
 *       compiler plan (the plans surface carries no host-module
 *       entry).</li>
 *   <li><b>JVM carrier invocation:</b> the JVM
 *       {@code RuntimeDefaultEvaluator.invoke()} seam reflectively
 *       executes the compiled generated evaluator and returns the real
 *       default value.</li>
 * </ol>
 *
 * <p>Runs via main() using the repository's plain check()-helper
 * convention (no JUnit dependency; assertion failures exit non-zero).
 * The luajit and node tools are probed once; a missing tool fails the
 * corresponding execution gates (never a silent skip).</p>
 */
public class RuntimeDefaultLoweringTest {

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
     * The harness invocation of this suite's compiles (ISSUE-0643 P10
     * item 3): the suite's subject — the runtime default lowering and
     * construction phases — is arm-independent, and the fixtures keep
     * the harness arm's retained artifact behavior.
     */
    private static CompilerInvocation invocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
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
     * the same tree compiles for all three backends with identical
     * inputs (the synthesized deployment identity is backend-independent),
     * so per-entry semantic digests stay byte-comparable.
     */
    private static class Compile {
        final Path root;
        final Path entry;
        final Path outputRoot;
        final CompilationOrchestrator orchestrator;
        final boolean success;

        Compile(Path root, Path entry, Backend backend, String outputName)
                throws Exception {
            this(root, entry, backend, outputName, Map.of());
        }

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

    /** The scratch project shape the whole battery shares. */
    private static final class Project {
        final Path root;
        final Path entry;
        final Compile luajit;
        final Compile jvm;
        final Compile js;

        Project(Map<String, String> files) throws Exception {
            root = Files.createTempDirectory("deal_lowering_");
            for (Map.Entry<String, String> file : files.entrySet()) {
                write(root, file.getKey(), file.getValue());
            }
            entry = root.resolve("src/main.deal").toAbsolutePath()
                .normalize();
            luajit = new Compile(root, entry, Backend.LUAJIT, "luajit");
            jvm = new Compile(root, entry, Backend.JVM, "jvm");
            js = new Compile(root, entry, Backend.JS, "js");
        }

        void delete() {
            deleteRecursively(root);
        }

        CompilerClassDefaultPlan planOf(String className) {
            List<PlannedDefaultClass> plans = luajit.orchestrator
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

        RuntimeClassDefaultPlan runtimePlanLua(String className) {
            for (RuntimeClassDefaultPlan plan : luajit.orchestrator
                    .luaGeneratedResults().get(entry.toString())
                    .runtimePlans()) {
                if (plan.classIdentity().className().equals(className)) {
                    return plan;
                }
            }
            return null;
        }

        RuntimeClassDefaultPlan runtimePlanJvm(String className) {
            for (RuntimeClassDefaultPlan plan : jvm.orchestrator
                    .jvmGeneratedResults().get(entry.toString())
                    .runtimePlans()) {
                if (plan.classIdentity().className().equals(className)) {
                    return plan;
                }
            }
            return null;
        }

        RuntimeClassDefaultPlan runtimePlanJs(String className) {
            for (RuntimeClassDefaultPlan plan : js.orchestrator
                    .jsGeneratedResults().get(entry.toString())
                    .runtimePlans()) {
                if (plan.classIdentity().className().equals(className)) {
                    return plan;
                }
            }
            return null;
        }
    }

    // =========================================================================
    // Execution helpers (real generated artifacts)
    // =========================================================================

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

    /** Runs the LuaJIT entry artifact from the published build root
     * (deal/runtime.lua is deployed next to it by the orchestrator). */
    private static RunResult runLua(Compile compile) throws Exception {
        return runProcess(compile.outputRoot, "luajit", "main.lua");
    }

    /** Runs the JS entry artifact from the published build root
     * (deal/runtime.js and std/*.js are deployed by the orchestrator). */
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

    // =========================================================================
    // Battery sections
    // =========================================================================

    /**
     * The plan-shape battery: one shape fixture compiled on all three
     * backends; every backend's generated artifact and realized runtime
     * plan carrier pins entry order, names, canonical descriptors,
     * optional flags, evaluator presence exactly on required-present
     * entries, the zero-argument evaluator signatures, the pinned
     * labels, and the D3 digests (semantic digests byte-equal to the
     * compiler plan and identical across backends; implementation
     * digests 64-hex SHA-256 and distinct across backends).
     */
    private static void testPlanShapeAndVersioning() throws Exception {
        System.out.println("-- Plan shape, labels, evaluator signatures,"
            + " and versioning (all three backends) --");
        Project project = new Project(Map.of(
            "src/main.deal", """
                class Shape {
                  x: int = 1;
                  t: table = { seed: 2 };
                  opt?: string;
                  call: int = localFn();
                }

                function localFn(): int {
                  return 3;
                }

                export function main(): null {
                  let s: Shape = {};
                  if (s.x !== 1 || s.call !== 3) {
                    throw { code: "TEST_FAIL", message: "shape defaults" };
                  }
                  let opt: string | null = s.opt;
                  if (opt !== null) {
                    throw { code: "TEST_FAIL", message: "optional present" };
                  }
                  return null;
                }
                """));
        try {
            for (Compile compile : List.of(project.luajit, project.jvm,
                    project.js)) {
                check(compile.success, "the shape fixture compiles ("
                    + compile.orchestrator.diagnostics() + ")");
            }
            CompilerClassDefaultPlan plan = project.planOf("Shape");
            check(plan != null, "Shape has a compiler default plan");
            if (plan == null) {
                return;
            }
            check(plan.orderedFields().stream()
                    .map(CompilerClassDefaultEntry::name).toList()
                    .equals(List.of("x", "t", "opt", "call")),
                "the published plan keeps entry order (x, t, opt, call)");
            check(plan.orderedFields().stream()
                    .map(CompilerClassDefaultEntry::runtimeTypeDescriptor)
                    .toList()
                    .equals(List.of("int", "table", "string", "int")),
                "the published plan carries canonical descriptors"
                    + " (the optional field resolves to its declared"
                    + " type text)");
            check(plan.orderedFields().get(2).optional()
                    && !plan.orderedFields().get(0).optional()
                    && !plan.orderedFields().get(1).optional()
                    && !plan.orderedFields().get(3).optional(),
                "the published plan carries the optional flags");
            check(plan.orderedFields().get(2).defaultExpression() == null
                    && plan.orderedFields().get(0).defaultExpression() != null,
                "the optional entry carries no default expression");

            // ---- Generated artifacts ----
            String lua = Files.readString(
                project.luajit.outputRoot.resolve("main.lua"));
            int idxX = lua.indexOf("name = \"x\"");
            int idxT = lua.indexOf("name = \"t\"");
            int idxOpt = lua.indexOf("name = \"opt\"");
            int idxCall = lua.indexOf("name = \"call\"");
            check(idxX >= 0 && idxT > idxX && idxOpt > idxT
                    && idxCall > idxOpt,
                "the Lua plan table keeps entry order (x, t, opt, call)");
            check(lua.contains("{ name = \"opt\", descriptor = \"string\","
                    + " optional = true }"),
                "the Lua optional entry carries no evaluator");
            check(lua.contains("evaluator = function() return 1 end")
                    && lua.contains("evaluator = function() return "
                        + "localFn.f("),
                "the Lua evaluators are zero-argument closures whose "
                    + "provider call forwards the call-site span "
                    + "(ISSUE-0598)");
            String semanticX = plan.orderedFields().get(0)
                .defaultExpression().semanticDigest();
            check(lua.contains("-- default evaluator (@src/Shape, x, "
                    + semanticX + ")"),
                "the Lua artifact carries the pinned x label");

            String js = Files.readString(
                project.js.outputRoot.resolve("main.js"));
            check(js.contains("/* default evaluator (@src/Shape, x, "
                    + semanticX + ") */ () => 1"),
                "the JS plan list carries the pinned x evaluator label"
                    + " on its zero-argument closure");
            int jsIdxX = js.indexOf("name: \"x\"");
            int jsIdxT = js.indexOf("name: \"t\"");
            int jsIdxOpt = js.indexOf("name: \"opt\"");
            int jsIdxCall = js.indexOf("name: \"call\"");
            check(jsIdxX >= 0 && jsIdxT > jsIdxX && jsIdxOpt > jsIdxT
                    && jsIdxCall > jsIdxOpt,
                "the JS plan list keeps entry order (x, t, opt, call)");
            check(js.contains("{ name: \"opt\", descriptor: \"string\","
                    + " optional: true }"),
                "the JS optional entry carries no evaluator");
            check(js.contains("$rt.classPlan(\"@src/Shape\", Shape$plan,"
                    + " provided, $file, $line, $column)"),
                "the JS construction closure consumes the plan through"
                    + " $rt.classPlan");

            String java = Files.readString(
                project.jvm.outputRoot.resolve("Main.java"));
            check(java.contains("// default evaluator (@src/Shape, x, "
                    + semanticX + ")"),
                "the JVM artifact carries the pinned x evaluator label");
            check(java.contains("static int $default$$C_Shape$x() {")
                    && java.contains("static int $default$$C_Shape$call()"
                        + " {"),
                "the JVM evaluators are zero-argument static methods");
            int jIdxX = java.indexOf(
                "new $DealRt.DefaultPlanEntry(\"x\"");
            int jIdxT = java.indexOf(
                "new $DealRt.DefaultPlanEntry(\"t\"");
            int jIdxOpt = java.indexOf(
                "new $DealRt.DefaultPlanEntry(\"opt\"");
            int jIdxCall = java.indexOf(
                "new $DealRt.DefaultPlanEntry(\"call\"");
            check(jIdxX >= 0 && jIdxT > jIdxX && jIdxOpt > jIdxT
                    && jIdxCall > jIdxOpt,
                "the JVM plan record keeps entry order (x, t, opt, call)");
            check(java.contains(
                    "new $DealRt.DefaultPlanEntry(\"opt\", \"string\","
                        + " true, null)"),
                "the JVM optional entry carries a null evaluator");
            check(java.contains(
                    "new $DealRt.DefaultPlanEntry(\"x\", \"int\", false,"
                        + " Main::$default$$C_Shape$x)"),
                "the JVM required entry references its evaluator method");

            // ---- Realized runtime plan carriers ----
            for (RuntimeClassDefaultPlan runtimePlan : List.of(
                    project.runtimePlanLua("Shape"),
                    project.runtimePlanJvm("Shape"),
                    project.runtimePlanJs("Shape"))) {
                check(runtimePlan != null,
                    "the backend realized a RuntimeClassDefaultPlan");
                if (runtimePlan == null) {
                    continue;
                }
                check(runtimePlan.orderedFields().stream()
                        .map(RuntimeClassDefaultEntry::name).toList()
                        .equals(List.of("x", "t", "opt", "call")),
                    "the runtime plan keeps entry order (x, t, opt, call)");
                check(runtimePlan.orderedFields().stream()
                        .map(RuntimeClassDefaultEntry::runtimeTypeDescriptor)
                        .toList()
                        .equals(List.of("int", "table", "string", "int")),
                    "the runtime plan carries the canonical descriptors");
                check(runtimePlan.orderedFields().get(2).optional()
                        && runtimePlan.orderedFields().get(2)
                            .defaultEvaluator() == null,
                    "the optional entry carries no evaluator");
                for (int i = 0; i < runtimePlan.orderedFields().size();
                        i++) {
                    RuntimeClassDefaultEntry entry =
                        runtimePlan.orderedFields().get(i);
                    CompilerClassDefaultEntry compiler =
                        plan.orderedFields().get(i);
                    if (!entry.optional()) {
                        check(entry.defaultEvaluator() != null,
                            "the required entry '" + entry.name()
                                + "' carries an evaluator");
                        check(compiler.defaultExpression()
                                .semanticDigest().equals(entry
                                    .defaultEvaluator().semanticDigest()),
                            "the evaluator's semantic digest equals the"
                                + " compiler plan's digest for '"
                                + entry.name() + "'");
                        String digest = entry.defaultEvaluator()
                            .implementationDigest();
                        check(digest != null
                                && digest.matches("[0-9a-f]{64}"),
                            "the implementation digest of '" + entry.name()
                                + "' is 64-hex SHA-256, got " + digest);
                    }
                }
            }

            // ---- D3 differential versioning ----
            RuntimeClassDefaultPlan luaPlan = project.runtimePlanLua("Shape");
            RuntimeClassDefaultPlan jvmPlan = project.runtimePlanJvm("Shape");
            RuntimeClassDefaultPlan jsPlan = project.runtimePlanJs("Shape");
            for (int i = 0; i < plan.orderedFields().size(); i++) {
                CompilerClassDefaultEntry compiler =
                    plan.orderedFields().get(i);
                if (compiler.optional()) {
                    continue;
                }
                String luaSemantic = luaPlan.orderedFields().get(i)
                    .defaultEvaluator().semanticDigest();
                String jvmSemantic = jvmPlan.orderedFields().get(i)
                    .defaultEvaluator().semanticDigest();
                String jsSemantic = jsPlan.orderedFields().get(i)
                    .defaultEvaluator().semanticDigest();
                check(luaSemantic.equals(jvmSemantic)
                        && jvmSemantic.equals(jsSemantic),
                    "the semantic digest of '" + compiler.name()
                        + "' is byte-identical across the three backends"
                        + " (identical semantics)");
                String luaImpl = luaPlan.orderedFields().get(i)
                    .defaultEvaluator().implementationDigest();
                String jvmImpl = jvmPlan.orderedFields().get(i)
                    .defaultEvaluator().implementationDigest();
                String jsImpl = jsPlan.orderedFields().get(i)
                    .defaultEvaluator().implementationDigest();
                check(!luaImpl.equals(jvmImpl)
                        && !jvmImpl.equals(jsImpl)
                        && !luaImpl.equals(jsImpl),
                    "the implementation digests of '" + compiler.name()
                        + "' differ across the three backends"
                        + " (distinct implementations)");
            }
            check("1".equals(DefaultRuntimeAbiVersion.CURRENT.version()),
                "the epic-owned runtime ABI version is \"1\", got "
                    + DefaultRuntimeAbiVersion.CURRENT.version());

            // ---- The JVM carrier invocation seam executes the real
            // generated evaluator ----
            RunResult javac = runJvm(project.jvm);
            check(javac.exitCode() == 0,
                "the shape fixture compiles and runs on the JVM: "
                    + javac.output());
            try (URLClassLoader loader = new URLClassLoader(
                    new URL[] {project.jvm.outputRoot.toUri().toURL()},
                    RuntimeDefaultLoweringTest.class.getClassLoader())) {
                ClassLoader saved = Thread.currentThread()
                    .getContextClassLoader();
                Thread.currentThread().setContextClassLoader(loader);
                try {
                    RuntimeDefaultEvaluator xEvaluator = jvmPlan
                        .orderedFields().get(0).defaultEvaluator();
                    Object value = xEvaluator.invoke().invoke();
                    check(value instanceof Integer
                            && ((Integer) value) == 1,
                        "the JVM carrier invocation seam executes the"
                            + " generated evaluator and returns 1, got "
                            + value);
                    RuntimeDefaultEvaluator callEvaluator = jvmPlan
                        .orderedFields().get(3).defaultEvaluator();
                    Object callValue = callEvaluator.invoke().invoke();
                    check(callValue instanceof Integer
                            && ((Integer) callValue) == 3,
                        "the JVM carrier invocation seam executes the"
                            + " call-valued evaluator and returns 3, got "
                            + callValue);
                } finally {
                    Thread.currentThread()
                        .setContextClassLoader(saved);
                }
            }
        } finally {
            project.delete();
        }
    }

    /**
     * The behavior battery: one fixture proving per-construction
     * default evaluation in class source order, fresh table literals
     * per attempt, a function/module-field {@code bytes} result
     * retained by reference (no deep copy), zero evaluator invocations
     * at module load, and evaluator execution deferred to construction
     * — executed on all three backends through the real generated
     * artifacts.
     */
    private static void testBehaviorThroughRealArtifacts()
            throws Exception {
        System.out.println("-- Order, freshness, reference retention,"
            + " and zero import-time evaluation (real artifacts) --");
        // Module-level lets are E1049 in v1.2 (no user-defined
        // globals), so the cross-call invocation state lives in the
        // host probe (the conformance planprobe triplet — copied into
        // the scratch project and deployed beside every backend's
        // artifact).
        Path hostFixtures = Path.of("test", "conformance", "host-fixtures");
        Path root = Files.createTempDirectory("deal_lowering_behave_");
        Path entry = root.resolve("src/main.deal").toAbsolutePath()
            .normalize();
        write(root, "src/main.deal", """
                import * as probe from "host/planprobe"

                function boom(): int {
                  throw { code: "BOOM", message: "eager default ran" };
                }

                class Order {
                  first: int = probe.nextValue();
                  second: int = probe.nextValue();
                  data: table = {};
                  payload: bytes = bytes(2);
                }

                class Eager {
                  v: int = boom();
                }

                export function main(): null {
                  // Module load finished: no evaluator has run yet.
                  if (probe.valueCount() !== 0) {
                    throw { code: "TEST_FAIL", message: "evaluator ran at load" };
                  }
                  let a: Order = {};
                  if (probe.valueCount() !== 2) {
                    throw { code: "TEST_FAIL", message: "defaults did not run once per attempt" };
                  }
                  if (a.first !== 10 || a.second !== 20) {
                    throw { code: "TEST_FAIL", message: "defaults ran out of source order" };
                  }
                  let b: Order = {};
                  if (probe.valueCount() !== 4) {
                    throw { code: "TEST_FAIL", message: "defaults did not re-execute per attempt" };
                  }
                  if (a.first !== 10 || b.first !== 30) {
                    throw { code: "TEST_FAIL", message: "per-attempt results mismatch" };
                  }
                  // Fresh mutable table and bytes literals per attempt.
                  a.data.x = 7;
                  let dx: int | null = b.data.x;
                  if (dx !== null) {
                    throw { code: "TEST_FAIL", message: "table default shared across instances" };
                  }
                  a.payload[0] = 9;
                  if (b.payload[0] !== 0) {
                    throw { code: "TEST_FAIL", message: "bytes default shared across instances" };
                  }
                  // The deferred evaluator executes at construction.
                  let raised: boolean = false;
                  try {
                    let e: Eager = {};
                  } catch (e) {
                    raised = e.code === "BOOM";
                  }
                  if (!raised) {
                    throw { code: "TEST_FAIL", message: "construction-time evaluator did not run" };
                  }
                  return null;
                }
                """);
        try {
            // The host probe declaration (written here: the corpus
            // .d.deal carries @expected/@description directive headers,
            // which the declaration-file parser rejects) plus the
            // planprobe implementations copied verbatim from the
            // conformance host fixtures.
            Files.createDirectories(root.resolve("host"));
            write(root, "host/planprobe.d.deal",
                "// Host probe declaration (the planprobe contract):"
                    + " mutable host-side invocation counters.\n"
                    + "export function nextValue(): int;\n"
                    + "export function valueCount(): int;\n");
            for (String stem : List.of("lua", "js", "java")) {
                Files.copy(hostFixtures.resolve("planprobe." + stem),
                    root.resolve("host").resolve(
                        "planprobe." + stem));
            }
            Compile luaHost = new HostCompile(root, entry, Backend.LUAJIT,
                "luajit");
            Compile jvmHost = new HostCompile(root, entry, Backend.JVM,
                "jvm");
            Compile jsHost = new HostCompile(root, entry, Backend.JS,
                "js");
            for (Compile compile : List.of(luaHost, jvmHost, jsHost)) {
                check(compile.success, "the behavior fixture compiles ("
                    + compile.orchestrator.diagnostics() + ")");
            }
            if (!luaHost.success || !jvmHost.success || !jsHost.success) {
                return;
            }
            if (toolAvailable("luajit", "-v")) {
                deployHost(luaHost.outputRoot, "lua");
                RunResult lua = runLua(luaHost);
                check(lua.exitCode() == 0,
                    "LuaJIT behavior run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " behavior gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                deployHost(jsHost.outputRoot, "js");
                RunResult js = runJs(jsHost);
                check(js.exitCode() == 0,
                    "JS behavior run exits 0: " + js.output());
            } else {
                check(false, "node is unavailable — the JS behavior"
                    + " gate cannot run");
            }
            deployHost(jvmHost.outputRoot, "java");
            RunResult jvm = runJvm(jvmHost);
            check(jvm.exitCode() == 0,
                "JVM behavior run exits 0: " + jvm.output());
        } finally {
            deleteRecursively(root);
        }
    }

    /** A compile of a scratch root with the {@code host/planprobe}
     * externals declaration wired (the raw specifier → declaration path
     * surface the conformance harness builds for host imports). */
    private static final class HostCompile extends Compile {
        HostCompile(Path root, Path entry, Backend backend,
                    String outputName) throws Exception {
            super(root, entry, backend, outputName,
                Map.of("host/planprobe", root.resolve("host")
                    .resolve("planprobe.d.deal").toString()));
        }
    }

    /** Deploys one host implementation beside a backend's artifacts:
     * the Lua triplet into {@code <build>/host/planprobe.lua} (the
     * raw slash-form require path), the JS triplet into
     * {@code <build>/host/planprobe.js} (the relative require), and the
     * Java triplet as {@code <build>/HostPlanprobe.java} (the
     * {@code classNameFor("host/planprobe")} artifact name the JVM
     * host slice references). */
    private static void deployHost(Path outputRoot, String ext)
            throws Exception {
        Path source = Path.of("test", "conformance", "host-fixtures",
            "planprobe." + ext);
        if (ext.equals("java")) {
            Files.copy(source, outputRoot.resolve("HostPlanprobe.java"));
            return;
        }
        Files.createDirectories(outputRoot.resolve("host"));
        Files.copy(source, outputRoot.resolve("host")
            .resolve("planprobe." + ext));
    }

    /**
     * The bytes-reference-retention battery (LuaJIT and JavaScript):
     * an imported provider function returning a SHARED host-held bytes
     * buffer — each construction stores the function result by
     * reference, so a write through one instance is visible through
     * the other (no generic deep copy of the evaluator result). The
     * JVM host ABI slice cannot return bytes (its closed host export
     * shapes are int/number/boolean/string and their nullable forms),
     * so the JVM bytes evaluator behavior is pinned through the
     * carrier invocation seam in the shape battery instead.
     */
    private static void testBytesReferenceRetention() throws Exception {
        System.out.println("-- Bytes reference retention through an"
            + " imported provider function (LuaJIT, JavaScript) --");
        Path root = Files.createTempDirectory("deal_lowering_bytes_");
        Path entry = root.resolve("src/main.deal").toAbsolutePath()
            .normalize();
        write(root, "src/main.deal", """
                import * as probe from "host/planbytes"

                class Holder {
                  buf: bytes = probe.sharedBytes();
                }

                export function main(): null {
                  let a: Holder = {};
                  let b: Holder = {};
                  a.buf[0] = 9;
                  if (b.buf[0] !== 9) {
                    throw { code: "TEST_FAIL", message: "bytes result was deep-copied" };
                  }
                  return null;
                }
                """);
        try {
            Files.createDirectories(root.resolve("host"));
            write(root, "host/planbytes.d.deal",
                "export function sharedBytes(): bytes;\n");
            write(root, "host/planbytes.lua",
                "-- Shared host-held bytes buffer: sharedBytes returns the"
                    + " SAME buffer object on every call.\n"
                    + "local rt = require(\"deal.runtime\")\n"
                    + "local buf = rt.bytes_new(2, nil, nil, nil)\n"
                    + "return {\n"
                    + "  sharedBytes = function()\n"
                    + "    return buf\n"
                    + "  end,\n"
                    + "}\n");
            write(root, "host/planbytes.js",
                "\"use strict\";\n"
                    + "// Shared host-held bytes buffer: sharedBytes"
                    + " returns the SAME buffer object on every call.\n"
                    + "const $rt = require(\"../deal/runtime\");\n"
                    + "const buf = $rt.bytes(2, null, null, null);\n"
                    + "module.exports = {\n"
                    + "  sharedBytes: function () {\n"
                    + "    return buf;\n"
                    + "  },\n"
                    + "};\n");
            Compile luaBytes = new Compile(root, entry,
                Backend.LUAJIT, "bytes-lua", Map.of("host/planbytes",
                    root.resolve("host").resolve(
                        "planbytes.d.deal").toString()));
            Compile jsBytes = new Compile(root, entry,
                Backend.JS, "bytes-js", Map.of("host/planbytes",
                    root.resolve("host").resolve(
                        "planbytes.d.deal").toString()));
            check(luaBytes.success,
                "the bytes-identity fixture compiles on LuaJIT ("
                    + luaBytes.orchestrator.diagnostics() + ")");
            check(jsBytes.success,
                "the bytes-identity fixture compiles on JS ("
                    + jsBytes.orchestrator.diagnostics() + ")");
            if (!luaBytes.success || !jsBytes.success) {
                return;
            }
            if (toolAvailable("luajit", "-v")) {
                Files.createDirectories(
                    luaBytes.outputRoot.resolve("host"));
                Files.copy(root.resolve("host/planbytes.lua"),
                    luaBytes.outputRoot.resolve("host")
                        .resolve("planbytes.lua"));
                RunResult lua = runLua(luaBytes);
                check(lua.exitCode() == 0,
                    "LuaJIT bytes-identity run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " bytes-identity gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                Files.createDirectories(
                    jsBytes.outputRoot.resolve("host"));
                Files.copy(root.resolve("host/planbytes.js"),
                    jsBytes.outputRoot.resolve("host")
                        .resolve("planbytes.js"));
                RunResult js = runJs(jsBytes);
                check(js.exitCode() == 0,
                    "JS bytes-identity run exits 0: " + js.output());
            } else {
                check(false, "node is unavailable — the JS"
                    + " bytes-identity gate cannot run");
            }
        } finally {
            deleteRecursively(root);
        }
    }

    /**
     * The imported-plan battery: the provider's module-local default
     * function executes in the provider's declaring scope on every
     * backend — imported construction accesses the provider's published
     * plan after dependency-ordered initialization (LuaJIT requires the
     * provider chunk and reads alias["&lt;C&gt;_plan"]; JS requires the
     * provider module and calls its exported &lt;C&gt;$new closure; the
     * JVM references the provider module class's static plan evaluators
     * after the import trigger).
     */
    private static void testImportedProviderPlans() throws Exception {
        System.out.println("-- Imported construction through provider"
            + " plans (all three backends) --");
        Project project = new Project(Map.of(
            "src/main.deal", """
                import * as P from "./plan_provider_lib"

                export function main(): null {
                  let a: P.Provider = {};
                  let b: P.Provider = {};
                  if (a.value !== 7 || b.value !== 7) {
                    throw { code: "TEST_FAIL", message: "provider-scope default result mismatch" };
                  }
                  return null;
                }
                """,
            "src/plan_provider_lib.deal", """
                function internalDefault(): int {
                  return 7;
                }

                export class Provider {
                  value: int = internalDefault();
                }
                """));
        try {
            for (Compile compile : List.of(project.luajit, project.jvm,
                    project.js)) {
                check(compile.success, "the imported-plan fixture"
                    + " compiles (" + compile.orchestrator.diagnostics()
                    + ")");
            }
            if (!project.luajit.success || !project.jvm.success
                    || !project.js.success) {
                return;
            }
            // The consumer module's plan surface carries the consumer's
            // plans; the provider's plans live under the provider's
            // module path (dependency-ordered initialization keyed
            // there).
            List<PlannedDefaultClass> providerPlans = project.jvm
                .orchestrator.completedPlansByModulePath()
                .get("plan_provider_lib");
            check(providerPlans != null
                    && providerPlans.stream().anyMatch(pc ->
                        pc.declaration().name().equals("Provider")),
                "the provider module publishes the Provider plan keyed"
                    + " by its module path");

            // The consumer's JVM artifact references the provider's
            // static evaluator methods.
            String consumer = Files.readString(
                project.jvm.outputRoot.resolve("Main.java"));
            check(consumer.contains(
                    "Plan_provider_lib.$default$$C_Provider$value()"),
                "the JVM consumer references the provider plan's"
                    + " evaluator method: " + consumer.lines()
                        .filter(l -> l.contains("$default$"))
                        .findFirst().orElse("<missing>"));

            if (toolAvailable("luajit", "-v")) {
                RunResult lua = runLua(project.luajit);
                check(lua.exitCode() == 0,
                    "LuaJIT imported-plan run exits 0: " + lua.output());
            } else {
                check(false, "luajit is unavailable — the LuaJIT"
                    + " imported-plan gate cannot run");
            }
            if (toolAvailable("node", "--version")) {
                RunResult js = runJs(project.js);
                check(js.exitCode() == 0,
                    "JS imported-plan run exits 0: " + js.output());
            } else {
                check(false, "node is unavailable — the JS"
                    + " imported-plan gate cannot run");
            }
            RunResult jvm = runJvm(project.jvm);
            check(jvm.exitCode() == 0,
                "JVM imported-plan run exits 0: " + jvm.output());
        } finally {
            project.delete();
        }
    }

    /**
     * The host exemption battery: a declaration (host) module never
     * publishes a compiler default plan — the plans surface carries no
     * host-module entry and the three backends keep the preserved
     * defaults-map seam for host-declared classes (no &lt;C&gt;_plan
     * artifact exists for them).
     */
    private static void testHostExemption() throws Exception {
        System.out.println("-- Host-declared classes stay exempt from"
            + " plan publication --");
        Path root = Files.createTempDirectory("deal_lowering_host_");
        try {
            write(root, "src/main.deal", """
                import * as cfg from "host/cfg"

                export function main(): null {
                  let s: cfg.ServerConfig = { port: 9090 };
                  if (s.port !== 9090) {
                    throw { code: "TEST_FAIL", message: "host field" };
                  }
                  return null;
                }
                """);
            write(root, "host/cfg.d.deal", """
                export class ServerConfig {
                  port: int;
                }
                """);
            Path entry = root.resolve("src/main.deal").toAbsolutePath()
                .normalize();
            Compile lua = new Compile(root, entry, Backend.LUAJIT,
                "host-lua", Map.of("host/cfg",
                    root.resolve("host/cfg.d.deal").toString()));
            check(lua.success, "the host-declaration project compiles"
                + " (host modules are declaration files): "
                + lua.orchestrator.diagnostics());
            if (!lua.success) {
                return;
            }
            check(lua.orchestrator.completedPlansByModulePath()
                    .get("host/cfg") == null
                    && lua.orchestrator.completedPlansByModulePath()
                        .get("main") == null,
                "no compiler default plan exists for the host module or"
                    + " the consumer (no class declarations): "
                    + lua.orchestrator.completedPlansByModulePath());
            String artifact = Files.readString(
                lua.outputRoot.resolve("main.lua"));
            check(!artifact.contains("ServerConfig_plan"),
                "the consumer artifact emits no <C>_plan for the"
                    + " host-declared class");
        } finally {
            deleteRecursively(root);
        }
    }

    /**
     * The label derivation unit pins: {@link
     * RuntimeDefaultPlanLowering#labelOf} produces the pinned triple
     * text and {@link RuntimeDefaultPlanLowering#implementationDigestOf}
     * is deterministic SHA-256 over the canonical label+content framing
     * (changed content changes the digest).
     */
    private static void testLabelAndDigestDerivation() {
        System.out.println("-- Label and implementation-digest"
            + " derivation pins --");
        String digest = "66aa35d25cf605365cc5864a2d89cef9827235e1a0e3e2d2d704cfb40b4f6629";
        String label = RuntimeDefaultPlanLowering.labelOf("@src/main/Shape",
            "x", digest);
        check(label.equals("(@src/main/Shape, x, " + digest + ")"),
            "the pinned label triple, got " + label);
        RuntimeDefaultPlanLowering.EvaluatorRealization realization =
            new RuntimeDefaultPlanLowering.EvaluatorRealization(label,
                "function() return 1 end",
                () -> 1);
        String impl = RuntimeDefaultPlanLowering
            .implementationDigestOf(realization);
        check(impl.matches("[0-9a-f]{64}"),
            "the implementation digest is 64-hex SHA-256, got " + impl);
        check(!impl.equals(digest),
            "the implementation digest differs from the semantic digest"
                + " (distinct derivations)");
        RuntimeDefaultPlanLowering.EvaluatorRealization changed =
            new RuntimeDefaultPlanLowering.EvaluatorRealization(label,
                "function() return 2 end",
                () -> 2);
        String changedImpl = RuntimeDefaultPlanLowering
            .implementationDigestOf(changed);
        check(!impl.equals(changedImpl),
            "an evaluator content change changes the implementation"
                + " digest");
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Runtime Default Lowering Tests"
            + " (ISSUE-0544) ===\n");

        testLabelAndDigestDerivation();
        testPlanShapeAndVersioning();
        testBehaviorThroughRealArtifacts();
        testBytesReferenceRetention();
        testImportedProviderPlans();
        testHostExemption();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
