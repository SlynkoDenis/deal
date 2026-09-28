package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.StructuredBodyTable;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * The Lua transfer protocol and loop-target label emission battery
 * ({@code dispatched-corpus-production-realization} R6 and the transfer and
 * loop-target-label contract; the task's rule 1 and rule 2).
 *
 * <ol>
 *   <li>The four named {@code runtime-ok} fixtures
 *       ({@code control-flow/nested-break-in-try},
 *       {@code control-flow/nested-continue-in-try},
 *       {@code control-flow/nested-try-break-continue}, and
 *       {@code control-flow/for-of-break-continue}) compile through the
 *       release-owned production invocation ({@code deal.Main.run}), publish
 *       their one project artifact, load under {@code luajit}, and execute
 *       every exported zero-arity function with their pinned outcomes (the
 *       fixtures' own internal {@code TEST_FAIL} guards would abort a wrong
 *       result).</li>
 *   <li>The static invariant over each emitted artifact: every {@code goto}
 *       reference resolves in the same emitted Lua function (the structural
 *       label check), and every loop op a {@code break}/{@code continue}
 *       targets defines the label its transfers use (the {@code FOR_EACH}
 *       exit label at the op's own {@code do … end} level).</li>
 *   <li>The two mechanism probes are load-bearing: re-introducing the
 *       protected-level jump (the superseded emission shape) or removing the
 *       {@code FOR_EACH} exit label is rejected by the label check, while the
 *       emitted artifacts pass it, and the hand-written transfer-protocol
 *       probes cover the shapes the corpus fixtures do not carry (a target
 *       loop inside the same protected body, a target loop between two
 *       protected bodies inside a function factory, and an async body
 *       factory).</li>
 *   <li>The three-consumer differential matrix runs every fixture's test
 *       function through the semantic oracle, the shared LuaJIT artifact
 *       (real {@code luajit}), and the shared JVM artifact (real
 *       {@code javac --release 25 -proc:none} plus {@code java})
 *       event-for-event, so the closed-success lines of the structures a
 *       transfer exits are emitted exactly once per transfer path.</li>
 *   <li>The invariant holds over the control-flow, control-flow-errors, and
 *       error-handling families of the dispatched corpus: every fixture that
 *       lowers and emits produces an artifact with no label violation.</li>
 * </ol>
 */
public class LoopTransferLabelEmissionTest {

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
    // The named fixtures
    // =========================================================================

    private static final Path FIXTURE_ROOT =
        Path.of("test/conformance/backend-runtime");

    /** The three protected-crossing fixtures (the re-raised marker). */
    private static final List<String> TRY_FIXTURES = List.of(
        "control-flow/nested-break-in-try",
        "control-flow/nested-continue-in-try",
        "control-flow/nested-try-break-continue");

    /** The FOR_EACH fixture (the exit label its transfers use). */
    private static final String FOR_OF_FIXTURE = "control-flow/for-of-break-continue";

    /** Every named fixture of the slice, in declaration order. */
    private static final List<String> NAMED_FIXTURES = List.of(
        "control-flow/nested-break-in-try",
        "control-flow/nested-continue-in-try",
        "control-flow/nested-try-break-continue",
        "control-flow/for-of-break-continue");

    /**
     * The pinned callback outcomes: one entry per zero-arity test function
     * of the four fixtures (the result atom the fixture's own guard pins).
     */
    private static final Map<String, String> CALLBACKS = new LinkedHashMap<>();

    static {
        CALLBACKS.put("control-flow/nested-break-in-try#test_nested_break",
            "int:4");
        CALLBACKS.put("control-flow/nested-continue-in-try#test_nested_continue",
            "int:8");
        CALLBACKS.put(
            "control-flow/nested-try-break-continue#test_nested_try_break_continue",
            "int:5");
        CALLBACKS.put("control-flow/for-of-break-continue#test_break", "int:3");
        CALLBACKS.put("control-flow/for-of-break-continue#test_continue", "int:12");
    }

    private static final ModuleId APP = new ModuleId("app");

    private static final String DEAL_JSON = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "output": "out",
          "backend": "luajit"
        }
        """;

    /**
     * The Luajit drive: the deferred module-init entry runs, then every
     * published zero-arity export (plus the async exports, invoked through
     * their published callables) — the pinned outcomes are the fixtures'
     * own guards, and {@code main} is invoked by the entry delegation only.
     */
    private static final String LUA_DRIVER = """
        local surface = dofile("app.lua")
        local function run()
          local ok, err = __dealMain()
          if not ok then error(err, 0) end
          local names = {}
          for name, entry in pairs(surface) do
            if type(entry) == "table" and type(entry.f) == "function"
                and name ~= "main" and name:sub(1, 1) ~= "$" then
              names[#names + 1] = name
            end
          end
          table.sort(names)
          for _, name in ipairs(names) do
            surface[name].f()
          end
        end
        local ok, err = pcall(run)
        if not ok then
          local message = type(err) == "table"
            and (err.message or err.m) or tostring(err)
          print("PROBE-ERR|" .. tostring(message))
          os.exit(1)
        end
        print("PROBE-OK")
        """;

    // =========================================================================
    // 1. The four fixtures through the release-owned production invocation
    // =========================================================================

    static void testNamedFixturesUnderLuaJit() throws Exception {
        System.out.println("-- the four named fixtures: the release-owned "
            + "production compile, the artifact load, and the pinned outcomes --");
        for (String fixture : NAMED_FIXTURES) {
            Path project = Files.createTempDirectory("loop-transfer-");
            try {
                writeFixtureProject(project, fixture);
                CliOutcome compile = runProductionCli(project);
                checkEq(0, compile.exitCode(), fixture
                    + ": the release-owned production compile succeeds: "
                    + compile.stderr());
                if (compile.exitCode() != 0) {
                    continue;
                }
                Path out = project.resolve("out");
                Path artifact = out.resolve("app.lua");
                check(Files.isRegularFile(artifact),
                    fixture + ": the one project artifact stages at the entry path");
                check(artifactFiles(out).stream()
                        .noneMatch(name -> name.endsWith(".deal.map.json")),
                    fixture + ": the production set carries no source-map sidecar");
                if (!Files.isRegularFile(artifact)) {
                    continue;
                }
                String lua = Files.readString(artifact, StandardCharsets.UTF_8);
                List<String> violations = labelViolations(lua);
                check(violations.isEmpty(), fixture + ": every goto's label is "
                    + "defined in the same emitted Lua function: " + violations);

                write(out, "probe.lua", LUA_DRIVER);
                ProcessOutcome run = runProcess(out, Map.of("DEAL_DEFER_MAIN", "1"),
                    "luajit", "probe.lua");
                checkEq(0, run.exitCode(), fixture + ": the artifact loads and "
                    + "executes under luajit: stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
                checkEq("PROBE-OK\n", run.stdout(), fixture
                    + ": the exported test functions ran to completion");
                checkEq("", run.stderr(), fixture
                    + ": the run publishes nothing on stderr");
            } finally {
                deleteRecursively(project);
            }
        }
    }

    /** Writes one fixture's header-stripped source as a single-module project. */
    private static void writeFixtureProject(Path project, String fixture)
            throws Exception {
        write(project, "deal.json", DEAL_JSON);
        write(project, "src/app.deal",
            ConformanceHarnessMetadata.stripClassificationHeaders(
                Files.readString(FIXTURE_ROOT.resolve(fixture + ".deal"),
                    StandardCharsets.UTF_8)));
    }

    /** The release-owned production CLI compile of one fixture project. */
    private static CliOutcome runProductionCli(Path project) throws Exception {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = deal.Main.run(new String[] {"compile",
                project.resolve("src/app.deal").toAbsolutePath().toString(),
                "--output", project.resolve("out").toAbsolutePath().toString()});
            System.out.flush();
            System.err.flush();
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new CliOutcome(exitCode, out.toString(StandardCharsets.UTF_8),
            err.toString(StandardCharsets.UTF_8));
    }

    /** One orchestrator compile with the compiler's report captured (never printed). */
    private static boolean compileQuietly(CompilationOrchestrator orchestrator)
            throws Exception {
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        try {
            System.setOut(new PrintStream(ByteArrayOutputStream.nullOutputStream(),
                true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(ByteArrayOutputStream.nullOutputStream(),
                true, StandardCharsets.UTF_8));
            return orchestrator.compile();
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
    }

    /**
     * The JVM drive: the production class's module init runs, then every
     * published zero-arity export (the pinned outcomes are the fixtures' own
     * guards), and {@code main} is invoked by the entry delegation only.
     */
    private static final String JVM_DRIVER = """
        import deal.codegen.jvm.JvmRuntime;

        public final class AppProbe {
          public static void main(String[] args) {
            App.main(new String[0]);
            JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
            if (surface == null) {
              throw new IllegalStateException("no app surface");
            }
            java.util.List<String> names = new java.util.ArrayList<>(surface.keys);
            java.util.Collections.sort(names);
            for (String name : names) {
              if (name.equals("main") || name.startsWith("$")) {
                continue;
              }
              Object value = surface.read(name);
              if (!(value instanceof JvmRuntime.FunctionValue function)) {
                throw new IllegalStateException("entry " + name
                    + " is not a function value");
              }
              function.fn.invoke(new Object[0]);
            }
            System.out.println("PROBE-OK");
          }
        }
        """;

    /**
     * The JVM target of the four fixtures: the release-owned production
     * compile emits the one project class, and the class compiles with
     * {@code javac --release 25 -proc:none} against the compiler's runtime and
     * executes every exported test function under {@code java} with the
     * pinned outcomes.
     */
    static void testNamedFixturesUnderJvm() throws Exception {
        System.out.println("-- the four named fixtures: the release-owned JVM "
            + "production compile, javac, and the pinned outcomes --");
        for (String fixture : NAMED_FIXTURES) {
            Path project = Files.createTempDirectory("loop-transfer-jvm-");
            Path classes = project.resolve("classes");
            try {
                writeFixtureProject(project, fixture);
                Path out = project.resolve("out");
                ByteArrayOutputStream cliOut = new ByteArrayOutputStream();
                ByteArrayOutputStream cliErr = new ByteArrayOutputStream();
                PrintStream originalOut = System.out;
                PrintStream originalErr = System.err;
                int exitCode;
                try {
                    System.setOut(new PrintStream(cliOut, true,
                        StandardCharsets.UTF_8));
                    System.setErr(new PrintStream(cliErr, true,
                        StandardCharsets.UTF_8));
                    exitCode = deal.Main.run(new String[] {"compile",
                        project.resolve("src/app.deal").toAbsolutePath().toString(),
                        "--backend", "jvm", "--output",
                        out.toAbsolutePath().toString()});
                    System.out.flush();
                    System.err.flush();
                } finally {
                    System.setOut(originalOut);
                    System.setErr(originalErr);
                }
                checkEq(0, exitCode, fixture
                    + ": the release-owned JVM production compile succeeds: "
                    + cliErr.toString(StandardCharsets.UTF_8));
                if (exitCode != 0) {
                    continue;
                }
                check(Files.isRegularFile(out.resolve("App.java")), fixture
                    + ": the one JVM project artifact stages");
                Files.createDirectories(classes);
                write(out, "AppProbe.java", JVM_DRIVER);
                ProcessOutcome javac = runProcess(out, Map.of(), "javac",
                    "--release", "25", "-proc:none", "-cp", absoluteClasspath(),
                    "-d",
                    classes.toString(), out.resolve("App.java").toString(),
                    out.resolve("AppProbe.java").toString());
                checkEq(0, javac.exitCode(), fixture
                    + ": the JVM artifact compiles: " + javac.stderr());
                if (javac.exitCode() != 0) {
                    continue;
                }
                ProcessOutcome run = runProcess(out, Map.of(), "java", "-cp",
                    absoluteClasspath() + java.io.File.pathSeparator + classes,
                    "AppProbe");
                checkEq(0, run.exitCode(), fixture
                    + ": the JVM artifact executes under java: stdout="
                    + escaped(run.stdout()) + " stderr=" + escaped(run.stderr()));
                checkEq("PROBE-OK\n", run.stdout(), fixture
                    + ": the exported test functions ran to completion on the JVM");
            } finally {
                deleteRecursively(project);
            }
        }
    }

    // =========================================================================
    // 2. The mechanism probes (the corrections are load-bearing)
    // =========================================================================

    static void testMechanismProbes() throws Exception {
        System.out.println("-- the two mechanism probes: the protected-level jump "
            + "and the FOR_EACH exit label --");

        // (a) The protected crossing: the three try fixtures emit the
        //     re-raised marker at the protected dispatch level instead of a
        //     jump whose label lives in the enclosing function.
        for (String fixture : TRY_FIXTURES) {
            Path project = Files.createTempDirectory("loop-transfer-probe-");
            try {
                writeFixtureProject(project, fixture);
                CliOutcome compile = runProductionCli(project);
                checkEq(0, compile.exitCode(), fixture + ": the probe compile "
                    + "succeeds: " + compile.stderr());
                if (compile.exitCode() != 0) {
                    continue;
                }
                String lua = Files.readString(project.resolve("out/app.lua"),
                    StandardCharsets.UTF_8);
                check(labelViolations(lua).isEmpty(), fixture
                    + ": the emitted artifact satisfies the invariant");
                Matcher exitLabel = Pattern.compile("goto (X\\d+)").matcher(lua);
                boolean hasExit = exitLabel.find();
                check(hasExit, fixture + ": the artifact carries the loop-exit jump");
                if (!hasExit) {
                    continue;
                }
                String exit = exitLabel.group(1);
                String mutated = lua.replaceFirst(
                    "      error\\(__resT, 0\\)\\n",
                    "      goto " + exit + "\n");
                check(!mutated.equals(lua), fixture + ": the probe re-introduces "
                    + "the guarded dispatch shape");
                check(!labelViolations(mutated).isEmpty(), fixture
                    + ": the protected-level jump is rejected by the invariant "
                    + "(the correction is load-bearing)");
            } finally {
                deleteRecursively(project);
            }
        }

        // (b) The FOR_EACH exit label: the label is the last statement of the
        //     op's own `do … end` block, ahead of the loop op's SUCCESS event.
        Path project = Files.createTempDirectory("loop-transfer-foreach-");
        try {
            writeFixtureProject(project, FOR_OF_FIXTURE);
            CliOutcome compile = runProductionCli(project);
            checkEq(0, compile.exitCode(), FOR_OF_FIXTURE + ": the probe compile "
                + "succeeds: " + compile.stderr());
            if (compile.exitCode() == 0) {
                String lua = Files.readString(project.resolve("out/app.lua"),
                    StandardCharsets.UTF_8);
                Lowered fixture = lowerFixture(FOR_OF_FIXTURE, Set.of());
                check(fixture != null, FOR_OF_FIXTURE
                    + ": the fixture lowers and emits in-process");
                if (fixture != null) {
                    for (SemanticOp op : fixture.unit().ops()) {
                        if (op.kind() != SemanticOpKind.FOR_EACH) {
                            continue;
                        }
                        String exit = "X" + op.opId().id();
                        String label = "  ::" + exit + "::\n";
                        check(lua.contains(label), FOR_OF_FIXTURE + ": the FOR_EACH "
                            + op.opId() + " defines its exit label at its own "
                            + "emission level");
                        int labelAt = lua.indexOf(label);
                        String success = "__ev(\"app#" + op.opId().id()
                            + "\", \"SUCCESS\", \"FOR_EACH\"";
                        int successAt = lua.indexOf(success);
                        check(labelAt >= 0 && successAt > labelAt,
                            FOR_OF_FIXTURE + ": the loop op's SUCCESS event stays "
                                + "after its exit label");
                        if (transfersTargeting(fixture.unit(), op.opId(),
                                SemanticOpKind.BREAK)) {
                            check(lua.contains("goto " + exit + "\n"), FOR_OF_FIXTURE
                                + ": the FOR_EACH " + op.opId() + " defines the "
                                + "label its break transfers use");
                            String withoutLabel = lua.replace(label, "");
                            check(!withoutLabel.equals(lua)
                                    && !labelViolations(withoutLabel).isEmpty(),
                                FOR_OF_FIXTURE + ": a missing exit label is "
                                    + "rejected by the invariant (the correction "
                                    + "is load-bearing)");
                        }
                    }
                    check(fixture.lua().contains("goto X"), FOR_OF_FIXTURE
                        + ": the in-process artifact carries the for-of transfer");
                }
            }
        } finally {
            deleteRecursively(project);
        }
    }

    /**
     * The transfer-protocol probes over the emitted shapes the four corpus
     * fixtures do not carry: a target loop inside the same protected body
     * (the transfer jumps directly), a target loop between two protected
     * bodies inside a function factory (the inner dispatch owns the jump),
     * and the same inside an async body factory.
     */
    private static final Map<String, String> PROBES = new LinkedHashMap<>();

    static {
        PROBES.put("loop-inside-try", """
            export function probe(): int {
              let total: int = 0;
              try {
                for (let i: int = 0; i < 5; i = i + 1) {
                  if (i === 3) { break; }
                  total = total + 1;
                }
              } catch (e) {
                total = total + 100;
              }
              if (total !== 3) {
                throw { code: "TEST_FAIL", message: "loop-inside-try mismatch" };
              }
              return total;
            }

            export function main(): null {
              return null;
            }
            """);
        PROBES.put("factory-nested-try", """
            export function probe(): int {
              let f: () => int = function(): int {
                let total: int = 0;
                for (let i: int = 0; i < 6; i = i + 1) {
                  try {
                    try {
                      if (i === 4) { break; }
                      if (i === 2) { continue; }
                    } catch (inner) {
                      total = total + 1000;
                    }
                    total = total + i;
                  } catch (outer) {
                    total = total + 100;
                  }
                }
                return total;
              };
              let value: int = f();
              if (value !== 4) {
                throw { code: "TEST_FAIL", message: "factory transfer mismatch" };
              }
              return value;
            }

            export function main(): null {
              return null;
            }
            """);
        PROBES.put("async-nested-try", """
            export async function probe(): int {
              let total: int = 0;
              for (let i: int = 0; i < 6; i = i + 1) {
                try {
                  try {
                    if (i === 4) { break; }
                    if (i === 2) { continue; }
                  } catch (inner) {
                    total = total + 1000;
                  }
                  total = total + i;
                } catch (outer) {
                  total = total + 100;
                }
              }
              if (total !== 4) {
                throw { code: "TEST_FAIL", message: "async transfer mismatch" };
              }
              return total;
            }

            export function main(): null {
              return null;
            }
            """);
    }

    /**
     * The transfer-protocol probes: the same invariant and load/pinned-outcome
     * checks over the emitted shapes the corpus fixtures do not carry — a
     * target loop inside the same protected body, a target loop between two
     * protected bodies inside a function factory, and an async body factory.
     * A local declared function body is the residual carrier shape of
     * {@code dispatched-corpus-production-realization} R4 mechanism 1 (a
     * sibling slice); it emits the same factory shape, so the factory probe
     * covers the emission rule.
     */
    static void testTransferProtocolProbes() throws Exception {
        System.out.println("-- the transfer-protocol probes: the protected "
            + "crossing inside factories and the direct target jump --");
        for (Map.Entry<String, String> probe : PROBES.entrySet()) {
            Path project = Files.createTempDirectory("loop-transfer-shape-");
            try {
                write(project, "deal.json", DEAL_JSON);
                write(project, "src/app.deal", probe.getValue());
                CliOutcome compile = runProductionCli(project);
                checkEq(0, compile.exitCode(), probe.getKey()
                    + ": the release-owned production compile succeeds: "
                    + compile.stderr());
                if (compile.exitCode() != 0) {
                    continue;
                }
                Path out = project.resolve("out");
                String lua = Files.readString(out.resolve("app.lua"),
                    StandardCharsets.UTF_8);
                List<String> violations = labelViolations(lua);
                check(violations.isEmpty(), probe.getKey() + ": every goto's "
                    + "label is defined in the same emitted Lua function: "
                    + violations);
                write(out, "probe.lua", LUA_DRIVER);
                ProcessOutcome run = runProcess(out, Map.of("DEAL_DEFER_MAIN", "1"),
                    "luajit", "probe.lua");
                checkEq(0, run.exitCode(), probe.getKey()
                    + ": the artifact loads and executes: stdout="
                    + escaped(run.stdout()) + " stderr=" + escaped(run.stderr()));
                checkEq("PROBE-OK\n", run.stdout(), probe.getKey()
                    + ": the probe's own pinned result holds");
                checkEq("", run.stderr(), probe.getKey()
                    + ": the run publishes nothing on stderr");
            } finally {
                deleteRecursively(project);
            }
        }
    }

    // =========================================================================
    // 3. The three-consumer transfer-path matrix
    // =========================================================================

    static void testThreeConsumerTransferPaths() throws Exception {
        System.out.println("-- the transfer paths on the oracle, the shared "
            + "LuaJIT artifact, and the shared JVM artifact, event-for-event --");
        for (Map.Entry<String, String> entry : CALLBACKS.entrySet()) {
            int separator = entry.getKey().lastIndexOf('#');
            String fixture = entry.getKey().substring(0, separator);
            String callback = entry.getKey().substring(separator + 1);
            Lowered lowered = lowerFixture(fixture, Set.of(callback));
            check(lowered != null, fixture + "#" + callback
                + ": the fixture lowers with the callback export");
            if (lowered == null) {
                continue;
            }
            SemanticOp callbackOp = null;
            for (SemanticOp op : lowered.unit().ops()) {
                if (op.kind() == SemanticOpKind.CALLBACK_INVOKE) {
                    callbackOp = op;
                }
            }
            check(callbackOp != null, fixture + "#" + callback
                + ": the unit records the callback dispatch entry");
            if (callbackOp == null) {
                continue;
            }
            KindPayload.CallbackInvokePayload payload =
                (KindPayload.CallbackInvokePayload) callbackOp.payload();
            Path workspace = Files.createTempDirectory("loop-transfer-matrix-");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runCallback(lowered.unit(),
                        lowered.table(), payload.function(), List.of(),
                        SemanticDifferentialHarness.Expectation.success(
                            fixture + "#" + callback, List.of(), entry.getValue()),
                        workspace);
                check(verdict.pass(), fixture + "#" + callback
                    + ": the three-consumer matrix passes event-for-event with the "
                    + "pinned result " + entry.getValue() + ":\n" + verdict.report());
                checkEq(3, verdict.runs().size(), fixture + "#" + callback
                    + ": every consumer produced a real run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(!run.trace().isEmpty(), fixture + "#" + callback + ": "
                        + run.consumer() + " produced real events");
                }
            } finally {
                deleteRecursively(workspace);
            }
        }
    }

    // =========================================================================
    // 4. The invariant over the control-flow and error-handling corpus families
    // =========================================================================

    static void testCorpusLabelInvariant() throws Exception {
        System.out.println("-- the label invariant over the control-flow, "
            + "control-flow-errors, and error-handling corpus families --");
        List<Path> fixtures = new ArrayList<>();
        for (String family : List.of("control-flow", "control-flow-errors",
                "error-handling")) {
            try (Stream<Path> walk = Files.walk(FIXTURE_ROOT.resolve(family))) {
                fixtures.addAll(walk.filter(path -> path.toString().endsWith(".deal"))
                    .sorted().toList());
            }
        }
        int emitted = 0;
        int notProducible = 0;
        for (Path fixture : fixtures) {
            String relative = FIXTURE_ROOT.relativize(fixture).toString()
                .replace('\\', '/').replace(".deal", "");
            Lowered lowered = lowerSource(fixture, Set.of());
            if (lowered == null) {
                notProducible++;
                continue;
            }
            emitted++;
            List<String> violations = labelViolations(lowered.lua());
            check(violations.isEmpty(), relative + ": every goto's label is "
                + "defined in the same emitted Lua function: " + violations);
            for (String loopViolation : loopLabelViolations(lowered)) {
                check(false, relative + ": " + loopViolation);
            }
        }
        check(emitted >= 20, "the family sweep emitted " + emitted
            + " artifacts (the invariant covers the family)");
        System.out.println("   family sweep: " + emitted + " emitted, "
            + notProducible + " not producible at this tree state");
    }

    // =========================================================================
    // The in-process production lowering of one fixture
    // =========================================================================

    /** One in-process lowered fixture: the unit, the table, and the artifact. */
    private record Lowered(LoweredModuleUnit unit, StructuredBodyTable table,
                           ExecutableLoweredProject project, String lua) {
    }

    /** The release-owned production invocation (the epic's production record). */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Lowered lowerFixture(String fixture, Set<String> callbacks)
            throws Exception {
        return lowerSource(FIXTURE_ROOT.resolve(fixture + ".deal"), callbacks);
    }

    /**
     * Lowers and emits one corpus fixture through the one project lowering
     * (the release-owned production invocation) and the production LuaJIT
     * entry; a fixture the frontend or the lowering refuses is not producible
     * and yields {@code null}.
     */
    private static Lowered lowerSource(Path fixture, Set<String> callbacks)
            throws Exception {
        Path root = Files.createTempDirectory("loop-transfer-lower-");
        try {
            Path src = root.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("app.deal"),
                ConformanceHarnessMetadata.stripClassificationHeaders(
                    Files.readString(fixture, StandardCharsets.UTF_8)));
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("app.deal").toAbsolutePath(), root.resolve("out"),
                false, false, false, Backend.LUAJIT, Map.of(),
                List.of(src.toAbsolutePath()), null);
            boolean compiled = compileQuietly(orchestrator);
            CheckedProjectBuildResult built = orchestrator.checkedProject();
            RequirementManifestResult manifests = orchestrator.requirementManifests();
            if (!compiled || built == null || built.input() == null
                    || built.index() == null || built.hasErrors() || manifests == null
                    || manifests.manifests() == null) {
                return null;
            }
            HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
            if (surface == null) {
                return null;
            }
            SemanticLowerer.ProjectLoweringResult lowered = SemanticLowerer.lowerProject(
                productionInvocation(), built.input(), built.index(),
                manifests.manifests(), surface, Map.of(), Map.of(),
                BuiltinErrorDeclaration.synthesized(
                    built.input().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                callbacks);
            if (lowered.hasErrors() || lowered.project() == null) {
                return null;
            }
            String lua = LuaSemanticEmitter.emitProductionProject(lowered.project(),
                lowered.tables(), lowered.registries(), surface,
                new FfiEmissionInput(Map.of(),
                    DistributionHome.forManifestDirectory(src.toString())
                        .manifestDirectoryText()));
            LoweredModuleUnit unit = lowered.project().modules().get(APP);
            StructuredBodyTable table = lowered.tableOf(APP);
            if (unit == null || table == null) {
                return null;
            }
            return new Lowered(unit, table, lowered.project(), lua);
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // The structural Lua label check
    // =========================================================================

    /** The Lua token shape the structural label check walks. */
    private static final Pattern LUA_TOKEN = Pattern.compile(
        "::[A-Za-z_][A-Za-z0-9_]*::|\\b\\w+\\b");

    /**
     * Masks every Lua string literal and comment with spaces of equal length,
     * so keyword and label offsets survive the masking.
     */
    private static String maskLua(String text) {
        StringBuilder out = new StringBuilder(text.length());
        int index = 0;
        int length = text.length();
        while (index < length) {
            char current = text.charAt(index);
            if (current == '"' || current == '\'') {
                int start = index;
                index++;
                while (index < length) {
                    if (text.charAt(index) == '\\') {
                        index += 2;
                        continue;
                    }
                    if (text.charAt(index) == current) {
                        index++;
                        break;
                    }
                    index++;
                }
                int end = Math.min(index, length);
                out.append(" ".repeat(Math.max(0, end - start)));
                continue;
            }
            if (current == '-' && index + 1 < length && text.charAt(index + 1) == '-') {
                int start = index;
                while (index < length && text.charAt(index) != '\n') {
                    index++;
                }
                out.append(" ".repeat(index - start));
                continue;
            }
            out.append(current);
            index++;
        }
        return out.toString();
    }

    /**
     * The structural label-visibility findings of one emitted Lua artifact:
     * every {@code goto} must reach a label of its own emitted function, i.e.
     * a label registered in its block or an enclosing block up to (and
     * including) the innermost enclosing {@code function} block. Lua exposes
     * no label of an enclosing function to a nested function, which is exactly
     * the defect this battery pins.
     */
    private static List<String> labelViolations(String lua) {
        String text = maskLua(lua);
        List<String> tokens = new ArrayList<>();
        List<Integer> positions = new ArrayList<>();
        Matcher matcher = LUA_TOKEN.matcher(text);
        while (matcher.find()) {
            tokens.add(matcher.group());
            positions.add(matcher.start());
        }
        List<Integer> parents = new ArrayList<>();
        List<String> kinds = new ArrayList<>();
        List<Set<String>> labels = new ArrayList<>();
        parents.add(null);
        kinds.add("chunk");
        labels.add(new LinkedHashSet<>());
        Deque<Integer> stack = new ArrayDeque<>();
        stack.push(0);
        List<String> gotoNames = new ArrayList<>();
        List<Integer> gotoBlocks = new ArrayList<>();
        List<Integer> gotoPositions = new ArrayList<>();
        List<String> violations = new ArrayList<>();
        boolean skipDo = false;
        for (int index = 0; index < tokens.size(); index++) {
            String token = tokens.get(index);
            if (token.startsWith("::")) {
                labels.get(stack.peek())
                    .add(token.substring(2, token.length() - 2));
                continue;
            }
            switch (token) {
                case "function", "if", "repeat", "do" -> {
                    if (token.equals("do") && skipDo) {
                        skipDo = false;
                        continue;
                    }
                    parents.add(stack.peek());
                    kinds.add(token);
                    labels.add(new LinkedHashSet<>());
                    stack.push(parents.size() - 1);
                }
                case "for", "while" -> {
                    parents.add(stack.peek());
                    kinds.add(token);
                    labels.add(new LinkedHashSet<>());
                    stack.push(parents.size() - 1);
                    skipDo = true;
                }
                case "end", "until" -> {
                    if (stack.size() > 1) {
                        stack.pop();
                    } else {
                        violations.add("unbalanced '" + token + "' at "
                            + positions.get(index));
                    }
                }
                case "goto" -> {
                    if (index + 1 < tokens.size()) {
                        gotoNames.add(tokens.get(index + 1));
                        gotoBlocks.add(stack.peek());
                        gotoPositions.add(positions.get(index));
                    }
                }
                default -> {
                }
            }
        }
        if (stack.size() != 1) {
            violations.add("unbalanced artifact: " + (stack.size() - 1)
                + " blocks left open");
        }
        for (int index = 0; index < gotoNames.size(); index++) {
            String name = gotoNames.get(index);
            boolean found = false;
            Integer current = gotoBlocks.get(index);
            while (current != null) {
                if (labels.get(current).contains(name)) {
                    found = true;
                    break;
                }
                if (kinds.get(current).equals("function")) {
                    break;
                }
                current = parents.get(current);
            }
            if (!found) {
                violations.add("goto '" + name + "' at " + gotoPositions.get(index)
                    + " has no label in its emitted function");
            }
        }
        return violations;
    }

    /**
     * The label-completeness findings of one emitted artifact against its
     * unit: every loop op a {@code break} or {@code continue} targets must
     * define the exit (or continue) label its transfers use, and the
     * emitted transfer jump must name that label.
     */
    private static List<String> loopLabelViolations(Lowered unit) {
        List<String> findings = new ArrayList<>();
        for (SemanticOp op : unit.unit().ops()) {
            if (op.kind() != SemanticOpKind.LOOP
                    && op.kind() != SemanticOpKind.FOR_EACH) {
                continue;
            }
            String id = String.valueOf(op.opId().id());
            if (transfersTargeting(unit.unit(), op.opId(), SemanticOpKind.BREAK)) {
                if (!unit.lua().contains("goto X" + id + "\n")) {
                    findings.add("the transfer jump of the break targeting "
                        + op.opId() + " is absent");
                }
                if (!unit.lua().contains("::X" + id + "::")) {
                    findings.add("the loop " + op.opId() + " defines no exit label");
                }
            }
            if (transfersTargeting(unit.unit(), op.opId(), SemanticOpKind.CONTINUE)) {
                if (!unit.lua().contains("goto Y" + id + "\n")) {
                    findings.add("the transfer jump of the continue targeting "
                        + op.opId() + " is absent");
                }
                if (!unit.lua().contains("::Y" + id + "::")
                        && !unit.lua().contains("::Y" + id + "T::")) {
                    findings.add("the loop " + op.opId()
                        + " defines no continue label");
                }
            }
        }
        return findings;
    }

    /** Whether one loop op is targeted by a transfer op of the given kind. */
    private static boolean transfersTargeting(LoweredModuleUnit unit, OpId loopOp,
                                              SemanticOpKind kind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != kind) {
                continue;
            }
            OpId target = kind == SemanticOpKind.BREAK
                ? ((KindPayload.BreakPayload) op.payload()).loopId()
                : ((KindPayload.ContinuePayload) op.payload()).loopId();
            if (loopOp.equals(target)) {
                return true;
            }
        }
        return false;
    }

    // =========================================================================
    // Process and file helpers
    // =========================================================================

    private record CliOutcome(int exitCode, String stdout, String stderr) {
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    private static ProcessOutcome runProcess(Path directory, Map<String, String> env,
            String... command) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(directory.toFile());
        builder.redirectErrorStream(false);
        builder.environment().putAll(env);
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        return new ProcessOutcome(exit, stdout, stderr);
    }

    /** The absolute compile classpath of this test JVM (never cwd-relative). */
    private static String absoluteClasspath() {
        StringBuilder joined = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(java.io.File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (joined.length() > 0) {
                joined.append(java.io.File.pathSeparator);
            }
            joined.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return joined.toString();
    }

    private static List<String> artifactFiles(Path root) throws Exception {        if (!Files.isDirectory(root)) {
            return List.of();
        }
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(Files::isRegularFile)
                .map(path -> root.relativize(path).toString().replace('\\', '/'))
                .sorted().toList();
        }
    }

    private static void write(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
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
        } catch (Exception ignored) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Lua Transfer Protocol and Loop-Target Label "
            + "Emission Tests (ISSUE-0700) ===\n");

        testNamedFixturesUnderLuaJit();
        testNamedFixturesUnderJvm();
        testMechanismProbes();
        testTransferProtocolProbes();
        testThreeConsumerTransferPaths();
        testCorpusLabelInvariant();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
