package deal.test.conformance;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Differential gate lanes corpus test (ISSUE-0357 Verification — the
 * cluster integration verification for the gate stage): the complete
 * three-lane gate over the real on-disk corpus through the gate core's
 * dispatch/verdict path — real {@code luajit}, {@code javac}+{@code java},
 * and {@code node} subprocesses — plus the six controlled divergence
 * experiments on scratch copies (never the committed corpus).
 *
 * <p>The full-run checks (Verification 1/8, lane accounting):</p>
 * <ul>
 *   <li>the designated converged subset
 *       ({@code control-flow/if-else.deal},
 *       {@code functions/direct-recursion.deal},
 *       {@code stdlib/string/length-unicode.deal},
 *       {@code error-handling/try-catch.deal} plus two more converged
 *       cases) passes byte-exact on all three lanes;</li>
 *   <li>the real corpus run converges green: the failure set is empty —
 *       an honest zero over the dispatched runtime cases on all three
 *       lanes — and a staged single-lane mismatch over the same corpus
 *       flips the verdict to FAIL with exactly that failure visible,
 *       naming fixture, backend, and the closed mismatch class with the
 *       first differing byte/field detail (never greenwashed);</li>
 *   <li>the per-backend pin of the luajit lane (ISSUE-0598, the LuaJIT
 *       lane convergence leaf): every runtime-classified case passes
 *       byte-exact on luajit ({@code 390/0}), zero luajit gate
 *       failures, and no luajit row in the pinned differential-failure
 *       enumeration;</li>
 *   <li>the per-backend pin of the js lane (ISSUE-0599, the JS lane
 *       convergence leaf): every runtime-classified case passes
 *       byte-exact on js ({@code 390/0}), zero js gate failures, and no
 *       js row in the pinned differential-failure enumeration (the
 *       retired pre-flip E8003 first-byte divergence is gone with its
 *       row);</li>
 *   <li>the ISSUE-0604 convergence class (the arithmetic/conversion/
 *       stdlib-int raise-site origins): every fixture of
 *       {@link #JVM_ARITHMETIC_CONVERGED} passes the jvm lane
 *       byte-exact against its on-disk sidecar, and the int-add-overflow
 *       framing is re-run on the real lane and pinned byte-for-byte;</li>
 *   <li>no {@code SKIP} verdict class appears anywhere (the gate has no
 *       skip branch; {@code Skipped: 0}).</li>
 * </ul>
 *
 * <p>The scratch experiments (Verification 1/4/5/6/7/8):</p>
 * <ol>
 *   <li>a passing fixture whose console output diverges on exactly one
 *       backend (a flagged perturbing lane double) fails naming that
 *       backend and the first differing byte;</li>
 *   <li>scratch lane variants printing a return value, invoking
 *       {@code main} twice, reordering exports, and writing framing to
 *       stderr fail the transcript comparison;</li>
 *   <li>scratch sidecars perturbing one error field, pinning an absent
 *       optional field, and violating the canonical serialization fail
 *       with the exact class and field/byte naming;</li>
 *   <li>scratch Compile Expectation Sidecars with a perturbed
 *       code/line/column/message fail
 *       {@code COMPILE_DIAGNOSTIC_MISMATCH} naming the fixture and the
 *       field; a second error diagnostic fails the fixture;</li>
 *   <li>scratch divergent sidecars for a non-FFI fixture or with a
 *       non-E6006 code are rejected by schema validation;</li>
 *   <li>a scratch slow fixture exceeds the harness-owned deadline and
 *       fails {@code LANE_TIMEOUT} with process termination on every
 *       lane.</li>
 * </ol>
 *
 * <p><b>Anti-hollow:</b> every lane of every run here is the production
 * lane — the LuaJIT lane compiles through the real frontend +
 * {@code LuaBackend} and executes real {@code luajit}, the JVM lane runs
 * the real whole-project orchestrator pipeline + {@code javac} +
 * {@code java}, and the JS lane runs the real {@code JsBackend} +
 * deployed runtime/stdlib + {@code node}. The only lane variations are
 * the flagged test-double subclasses of the real lanes used for the
 * controlled experiments, exactly as the lane suites do.</p>
 *
 * <p>The gate stays a dev-time tool in this stage (G5): the legacy
 * runners keep executing the corpus in {@code run_tests.sh} — the
 * temporary-coexistence window — and this test does not wire the gate
 * into the release surface.</p>
 */
public class DifferentialGateLanesCorpusTest {

    private static int passed = 0;
    private static int failed = 0;

    private static final Path CORPUS_ROOT = Path.of("test", "conformance");

    /** The harness-owned deadline of the full run (G7). */
    private static final Duration FULL_RUN_DEADLINE = Duration.ofSeconds(120);

    /** The designated converged subset (task criterion (a)): every lane
     * of every fixture here passes byte-exact. */
    private static final List<String> CONVERGED_SUBSET = List.of(
        "backend-runtime/control-flow/if-else.deal",
        "backend-runtime/functions/direct-recursion.deal",
        "backend-runtime/stdlib/string/length-unicode.deal",
        "backend-runtime/error-handling/try-catch.deal",
        "backend-runtime/error-handling/throw-error.deal",
        "backend-runtime/control-flow/continue.deal");

    /** The converged arithmetic-leaf framing of
     * {@code arithmetic/int-add-overflow.deal} (ISSUE-0604): the retired
     * missing-column PROCESS_FAILURE prefix's positive replacement. The
     * jvm leg now emits the exact sidecar-pinned snapshot — E8004 with
     * the closed message and the operator expression's origin (7:10) —
     * so the leaf pins the framed bytes instead of the absent-span
     * report. */
    private static final String JVM_ADD_OVERFLOW_FRAMING =
        "DEAL_ERROR_CODE: E8004\n"
            + "DEAL_ERROR_SNAPSHOT: {\"code\":\"E8004\","
            + "\"message\":\"int out of safe range\",\"sourceFile\":"
            + "\"backend-runtime/arithmetic/int-add-overflow.deal\","
            + "\"line\":7,\"column\":10}\n";

    /**
     * The ISSUE-0604 convergence class
     * (jvm-canonical-error-snapshot-convergence D3/D11): every
     * arithmetic, conversion, and stdlib-int raise site of the retained
     * JVM emitter now carries the authoritative node's origin (the
     * operator or intrinsic-call expression start) and the closed
     * message/projection literals, so each of these fixtures matches its
     * on-disk sidecar byte-exact on the jvm lane. The jvm-leg pin below
     * verifies the convergence through the real three-lane run.
     */
    private static final List<String> JVM_ARITHMETIC_CONVERGED = List.of(
        "backend-runtime/arithmetic/int-add-overflow.deal",
        "backend-runtime/arithmetic/int-sub-overflow.deal",
        "backend-runtime/arithmetic/int-mul-overflow.deal",
        "backend-runtime/arithmetic/int-neg-min.deal",
        "backend-runtime/arithmetic/int-div-zero.deal",
        "backend-runtime/arithmetic/int-pow-negative.deal",
        "backend-runtime/arithmetic/int32-pow-overflow.deal",
        "backend-runtime/arithmetic/int32-pow-infinity.deal",
        "backend-runtime/arithmetic/int-convert-fraction.deal",
        "backend-runtime/arithmetic/int-convert-infinity.deal",
        "backend-runtime/arithmetic/int-convert-nan.deal",
        "backend-runtime/arithmetic/int-conversion-out-of-range.deal",
        "backend-runtime/control-flow-errors/error-inside-for-of.deal",
        "backend-runtime/control-flow-errors/error-inside-while-loop.deal",
        "backend-runtime/runtime-errors/int-div-zero-e8005.deal",
        "backend-runtime/runtime-errors/rtc-035-remainder-zero-error.deal",
        "backend-runtime/runtime/int-convert-noninteger.deal",
        "backend-runtime/runtime/int-convert-null.deal",
        "backend-runtime/runtime/int-convert-range.deal",
        "backend-runtime/runtime/number-convert-null.deal",
        "backend-runtime/source-location/037-runtime-source-div-zero.deal",
        "backend-runtime/source-location/int32-overflow-source.deal",
        "backend-runtime/source-location/int-neg-min-source.deal",
        "backend-runtime/source-location-precision/closure-error-source.deal",
        "backend-runtime/source-location-precision/loop-error-source.deal",
        "backend-runtime/stdlib/math/int-abs-min-overflow.deal");

    public static void main(String[] args) throws Exception {
        System.out.println("=== Differential Gate Lanes Corpus Tests "
            + "(ISSUE-0357) ===\n");

        int jobs = Integer.getInteger("deal.test.jobs",
            Runtime.getRuntime().availableProcessors());
        System.out.println("Gate worker bound: " + jobs + " (deal.test.jobs="
            + System.getProperty("deal.test.jobs", "<unset>")
            + ", processors=" + Runtime.getRuntime().availableProcessors()
            + ")");

        fullGateCorpusRun(jobs);
        divergentConsoleStringProbe(jobs);
        printReturnValueDivergenceProbe(jobs);
        invokeMainTwiceDivergenceProbe(jobs);
        reorderedExportsDivergenceProbe(jobs);
        stderrFramingDivergenceProbe(jobs);
        perturbedErrorFieldProbe(jobs);
        pinnedAbsentOptionalProbe(jobs);
        serializationViolationProbe(jobs);
        compilePinPerturbationProbe(jobs);
        secondErrorDiagnosticProbe(jobs);
        divergentSidecarSchemaProbe(jobs);
        laneTimeoutProbe(jobs);

        deleteScratchRoots();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /** One scratch corpus: a fresh temp root with one fixture (plus its
     * sidecar when {@code sidecarJson} is non-null). */
    private record ScratchCorpus(Path root, Path file, String corpusPath,
                                 String strippedSource, String sidecarJson) {
        ScratchCorpus {
            Objects.requireNonNull(root, "root must not be null");
            Objects.requireNonNull(file, "file must not be null");
            Objects.requireNonNull(corpusPath, "corpusPath must not be null");
            Objects.requireNonNull(strippedSource,
                "strippedSource must not be null");
        }
    }

    private static final List<Path> scratchRoots = new ArrayList<>();

    private static ScratchCorpus writeScratchCorpus(String corpusPath,
            String rawSource, String sidecarJson) throws IOException {
        Path root = Files.createTempDirectory("gate_lanes_scratch_");
        scratchRoots.add(root);
        Path file = root.resolve(corpusPath);
        Files.createDirectories(file.getParent());
        Files.writeString(file, rawSource);
        if (sidecarJson != null) {
            Path sidecar = root.resolve(corpusPath.substring(0,
                corpusPath.length() - ".deal".length()) + ".expect.json");
            Files.writeString(sidecar, sidecarJson);
        }
        String stripped = deal.test.ConformanceHarnessMetadata
            .stripClassificationHeaders(rawSource);
        return new ScratchCorpus(root, file, corpusPath, stripped,
            sidecarJson);
    }

    private static void deleteScratchRoots() {
        for (Path root : scratchRoots) {
            try (var stream = Files.walk(root)) {
                for (Path path : stream.sorted(Collections.reverseOrder())
                        .toList()) {
                    Files.deleteIfExists(path);
                }
            } catch (IOException ignored) {
                // Best-effort scratch cleanup; the temp dirs are OS-scoped.
            }
        }
        scratchRoots.clear();
    }

    /** The three production lanes over one root, with the optional
     * lane-variant replacement for one backend. */
    private static Map<String, Lane> lanes(Path root, String replacedBackend,
            Lane replacement) {
        Map<String, Lane> lanes = new LinkedHashMap<>();
        lanes.put("luajit", "luajit".equals(replacedBackend)
            ? replacement : new LuaLane(root));
        lanes.put("jvm", "jvm".equals(replacedBackend)
            ? replacement : new JvmLane(root));
        lanes.put("js", "js".equals(replacedBackend)
            ? replacement : new JsLane(root));
        return lanes;
    }

    /** Runs the gate over a scratch corpus and returns the run. */
    private static DifferentialGate.GateRun runScratch(Path root,
            Map<String, Lane> lanes, Duration deadline) throws IOException {
        PrintStream capture = new PrintStream(new ByteArrayOutputStream(),
            true, StandardCharsets.UTF_8);
        return DifferentialGate.run(root, lanes, 4, deadline, capture);
    }

    private static GateDispatcher.CaseVerdict verdictOf(
            DifferentialGate.GateRun run, String fixturePath) {
        for (GateDispatcher.CaseVerdict verdict : run.verdicts()) {
            if (verdict.fixturePath().equals(fixturePath)) {
                return verdict;
            }
        }
        return null;
    }

    private static GateDispatcher.LaneOutcome outcomeOf(
            DifferentialGate.GateRun run, String fixturePath,
            String backend) {
        GateDispatcher.CaseVerdict verdict = verdictOf(run, fixturePath);
        if (verdict == null) {
            return null;
        }
        for (GateDispatcher.LaneOutcome outcome : verdict.outcomes()) {
            if (outcome.backend().equals(backend)) {
                return outcome;
            }
        }
        return null;
    }

    /** Executes a real corpus fixture on the production jvm lane and
     * returns the lane execution (used by the arithmetic-leaf
     * convergence pin to observe the exact framed bytes). */
    private static LaneExecution jvmLaneExecution(Path root,
            String corpusPath) throws Exception {
        CorpusDiscovery.DiscoveryResult discovery =
            CorpusDiscovery.discover(root);
        CorpusDiscovery.Fixture fixture =
            discovery.corpusByPath().get(corpusPath);
        SidecarGateLoader.LoadResult load = SidecarGateLoader.load(fixture,
            discovery.corpusByPath(), discovery.corpusModuleIndex(), root);
        return new JvmLane(root).execute(new LaneCase(corpusPath, "jvm",
            fixture.file(),
            CorpusDiscovery.compilationSet(fixture, discovery.corpusByPath(),
                root),
            load.runtime().get().expectationFor("jvm")));
    }

    private static String stdoutOf(LaneExecution execution) {
        return execution instanceof LaneExecution.Executed executed
            ? new String(executed.stdout(), StandardCharsets.UTF_8)
            : "<not executed>";
    }

    private static final String HEADER_RUNTIME_OK =
        "// @spec: Control flow — if-else\n"
        + "// @description: scratch differential gate probe\n"
        + "// @expected: runtime-ok\n"
        + "// @features: scratch\n"
        + "\n";

    private static final String HEADER_RUNTIME_ERROR_CODE =
        "// @spec: Error handling — try-catch\n"
        + "// @description: scratch differential gate probe\n"
        + "// @expected: runtime-error %s\n"
        + "// @features: scratch\n"
        + "\n";

    private static String uniformSidecar(String stdout) {
        return "{\n"
            + "  \"version\": 1,\n"
            + "  \"backends\": [\"luajit\", \"jvm\", \"js\"],\n"
            + "  \"expected\": {\n"
            + "    \"mode\": \"runtime-ok\",\n"
            + "    \"transcript\": { \"stdout\": " + jsonString(stdout)
            + ", \"stderr\": \"\" },\n"
            + "    \"exitCode\": 0\n"
            + "  }\n"
            + "}\n";
    }

    private static String jsonString(String value) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> sb.append(c);
            }
        }
        return sb.append('"').toString();
    }

    // =========================================================================
    // Full gate run over the real corpus (Verification 1 + 8, G8 accounting)
    // =========================================================================

    private static void fullGateCorpusRun(int jobs) throws Exception {
        System.out.println("-- Full three-lane gate over the real corpus --");
        long start = System.nanoTime();
        Map<String, Lane> lanes = Map.of(
            "luajit", new LuaLane(CORPUS_ROOT),
            "jvm", new JvmLane(CORPUS_ROOT),
            "js", new JsLane(CORPUS_ROOT));
        PrintStream capture = new PrintStream(new ByteArrayOutputStream(),
            true, StandardCharsets.UTF_8);
        DifferentialGate.GateRun run = DifferentialGate.run(CORPUS_ROOT,
            lanes, jobs, FULL_RUN_DEADLINE, capture);
        long elapsedMillis = (System.nanoTime() - start) / 1_000_000;

        check(elapsedMillis < FULL_RUN_DEADLINE.toMillis() * 4,
            "the full three-lane gate completes inside the budget "
                + "envelope (elapsed " + elapsedMillis + " ms)");
        long frontendFixtures = run.fixtures().stream()
            .filter(f -> f.classification() != null
                && (f.classification().kind() == CorpusDiscovery.Kind.COMPILE_OK
                    || f.classification().kind()
                        == CorpusDiscovery.Kind.COMPILE_ERROR))
            .count();
        long runtimeFixtures = run.fixtures().stream()
            .filter(CorpusDiscovery.Fixture::runtimeClassified).count();
        long compilePins = run.loadedFixtures().stream()
            .filter(f -> f.load().compilePin().isPresent()).count();
        check(run.loadedFixtures().size() == run.fixtures().size(),
            "every discovered fixture has a load result");
        check(run.classificationFailures().isEmpty(),
            "zero classification failures over the real corpus: "
                + run.classificationFailures());
        check(run.frontendCompiled() + run.compileDiagnosticComparisons()
                == frontendFixtures,
            "frontend execution and diagnostic comparisons account for every "
                + "discovered compile-classified case");
        check(run.compileDiagnosticComparisons() == compilePins,
            "every loaded Compile Diagnostic pin is compared");
        check(run.failures().stream().noneMatch(f ->
                "frontend-compile".equals(f.kind())
                    || "compile-diagnostic".equals(f.kind())),
            "zero frontend-compile and compile-diagnostic failures, got: "
                + run.failures());
        check(run.runtimeCasesDispatched() == runtimeFixtures
                && run.runtimeCasesWithoutLanes() == 0,
            "every discovered runtime case dispatches exactly once, got "
                + run.runtimeCasesDispatched() + "/"
                + run.runtimeCasesWithoutLanes());
        check(run.verdicts().size() == run.runtimeCasesDispatched(),
            "one verdict exists per dispatched case");

        // The designated converged subset passes byte-exact on all
        // three lanes (criterion (a)).
        for (String fixturePath : CONVERGED_SUBSET) {
            GateDispatcher.CaseVerdict verdict = verdictOf(run, fixturePath);
            check(verdict != null && verdict.passed(),
                fixturePath + " passes on all three lanes byte-exact, "
                    + "got: " + verdict);
        }

        int observedFailures = 0;
        for (GateDispatcher.CaseVerdict verdict : run.verdicts()) {
            for (GateDispatcher.LaneOutcome outcome : verdict.outcomes()) {
                if (outcome.passed()) {
                    continue;
                }
                observedFailures++;
                check(outcome.mismatch().isPresent()
                        && outcome.mismatch().get().detail() != null
                        && !outcome.mismatch().get().detail().isEmpty(),
                    verdict.fixturePath() + " " + outcome.backend()
                        + ": every failing outcome carries a bounded detail");
            }
        }
        long recordedFailures = run.failures().stream()
            .filter(f -> "lane".equals(f.kind())
                || "infrastructure".equals(f.kind()))
            .count();
        check(recordedFailures == observedFailures,
            "every lane mismatch is an ordinary gate failure, got "
                + recordedFailures + " recorded for " + observedFailures
                + " outcomes");

        for (String backend : SidecarSchemaValidator.BACKEND_NAMES) {
            int[] counts = run.perBackend().get(backend);
            check(counts[0] + counts[1] == run.runtimeCasesDispatched(),
                backend + " pass/fail counters account for every dispatched "
                    + "runtime case, got " + counts[0] + " / " + counts[1]);
        }
        // ISSUE-0598 (the LuaJIT lane convergence leaf): the luajit
        // lane passes every runtime-classified case byte-exact — the
        // per-backend pin {390, 0}, and the pinned differential-failure
        // enumeration above carries no luajit row anymore.
        int[] luajitCounts = run.perBackend().get("luajit");
        check(run.runtimeCasesDispatched() == 390
                && luajitCounts[0] == 390 && luajitCounts[1] == 0,
            "the luajit lane passes every dispatched runtime case "
                + "byte-exact (390/0), got " + luajitCounts[0] + " / "
                + luajitCounts[1] + " over "
                + run.runtimeCasesDispatched() + " dispatched");
        // ISSUE-0599 (the JS lane convergence leaf): the js lane passes
        // every runtime-classified case byte-exact.
        int[] jsCounts = run.perBackend().get("js");
        check(run.runtimeCasesDispatched() == 390
                && jsCounts[0] == 390 && jsCounts[1] == 0,
            "the js lane passes every dispatched runtime case "
                + "byte-exact (390/0), got " + jsCounts[0] + " / "
                + jsCounts[1] + " over "
                + run.runtimeCasesDispatched() + " dispatched");
        check(run.failures().stream().noneMatch(f ->
                f.subject().startsWith("js ")),
            "zero js gate failures after the lane convergence, got: "
                + run.failures().stream()
                    .filter(f -> f.subject().startsWith("js "))
                    .map(DifferentialGate.GateFailure::message)
                    .toList());

        // The shared time fixture's js leg passes after the
        // disposition-application unit (ISSUE-0536 remediation): the
        // lane suppresses the captured call-site span against the
        // sanctioned span-less sidecar, so the transcript matches the
        // pinned expectation field-exactly — the JS half of the
        // combined-behavior proof on the differential gate.
        GateDispatcher.CaseVerdict timeVerdict = verdictOf(run,
            "backend-runtime/stdlib-edge/time-now-millis-positive.deal");
        check(timeVerdict != null,
            "the time fixture is dispatched, got: " + timeVerdict);
        GateDispatcher.LaneOutcome timeJs = timeVerdict == null ? null
            : timeVerdict.outcomes().stream()
                .filter(o -> "js".equals(o.backend())).findFirst()
                .orElse(null);
        check(timeJs != null && timeJs.passed(),
            "the time fixture's js leg passes byte-exact against the "
                + "span-less sidecar, got: " + timeJs);
        if (timeJs != null && timeJs.passed()) {
            check(timeJs.mismatch().isEmpty(),
                "the time fixture's js leg carries no mismatch, got: "
                    + timeJs.mismatch());
        }
        GateDispatcher.LaneOutcome timeJvm = timeVerdict == null ? null
            : timeVerdict.outcomes().stream()
                .filter(o -> "jvm".equals(o.backend())).findFirst()
                .orElse(null);
        check(timeJvm != null && timeJvm.passed(),
            "the time fixture's jvm leg passes byte-exact against the "
                + "span-less sidecar under the code+message-mandatory "
                + "span-all-or-nothing gate (an honest pass, never a "
                + "skip), got: " + timeJvm);
        if (timeJvm != null && timeJvm.passed()) {
            check(timeJvm.mismatch().isEmpty(),
                "the time fixture's jvm leg carries no mismatch, got: "
                    + timeJvm.mismatch());
        }

        // The shared int32 remainder fixture's js leg passes after
        // the js-v12-int32-bytes lane closure (ISSUE-0324): the JS
        // runtime's intMod carries the I4 int32 branch —
        // MIN_VALUE % -1 computes the truncated remainder 0 — so
        // the transcript matches the uniform runtime-ok sidecar
        // byte-exact (the lane compiles the fixture under
        // COMMON_SHADOW + DEAL_V1_2_INT32, A5).
        GateDispatcher.CaseVerdict modVerdict = verdictOf(run,
            "backend-runtime/arithmetic/int32-mod-min-neg-one.deal");
        check(modVerdict != null,
            "the int32 remainder fixture is dispatched, got: "
                + modVerdict);
        GateDispatcher.LaneOutcome modJs = modVerdict == null ? null
            : modVerdict.outcomes().stream()
                .filter(o -> "js".equals(o.backend())).findFirst()
                .orElse(null);
        check(modJs != null && modJs.passed(),
            "the int32 remainder fixture's js leg passes byte-exact "
                + "against the runtime-ok sidecar, got: " + modJs);
        if (modJs != null && modJs.passed()) {
            check(modJs.mismatch().isEmpty(),
                "the int32 remainder fixture's js leg carries no "
                    + "mismatch, got: " + modJs.mismatch());
        }

        // ISSUE-0598: the luajit lane converged — int-add-overflow
        // passes byte-exact. ISSUE-0599: the js lane converged the same
        // way and carries zero gate failures.
        check(run.failures().stream().noneMatch(f ->
                f.subject().startsWith("luajit ")),
            "zero luajit gate failures after the lane convergence, got: "
                + run.failures().stream()
                    .filter(f -> f.subject().startsWith("luajit "))
                    .map(DifferentialGate.GateFailure::message)
                    .toList());

        // ISSUE-0604 (the arithmetic/conversion/stdlib-int origin leaf):
        // the retired missing-column spot-pin is replaced by the positive
        // convergence proof. The per-site origin literals and the closed
        // message/projection literals landed for every int arithmetic/
        // conversion/stdlib-int raise site, so the int-add-overflow jvm
        // leg converges byte-exact (E8004 "int out of safe range" at the
        // operator expression's 7:10) and no PROCESS_FAILURE remains to
        // pin. The replacement assertions re-run the real lane and pin
        // the exact framed bytes.
        DifferentialGate.GateFailure jvmAddOverflow = run.failures().stream()
            .filter(f -> f.subject().equals("jvm "
                + "backend-runtime/arithmetic/int-add-overflow.deal"))
            .findFirst().orElse(null);
        // D10 sidecar-correction authority (recorded with the correction):
        // the int-add-overflow sidecar pins the raising expression's raw
        // line 7 (the `2147483647 + 1` site; every sibling arithmetic pin
        // names raw line 7) — the source-authoritative value under
        // docs/spec-v1.2.md:2068-2075, "Runtime errors use generated
        // check metadata to report original `.deal` location" — never
        // fabricated by the lane. The arithmetic leaf's origin literals
        // flip the jvm leg to the converged byte comparison below.
        check(jvmAddOverflow == null,
            "the retired jvm int-add-overflow spot-pin is gone: the "
                + "fixture converges after the origin literals landed "
                + "(no gate failure names it), got: " + jvmAddOverflow);
        GateDispatcher.CaseVerdict addOverflowVerdict = verdictOf(run,
            "backend-runtime/arithmetic/int-add-overflow.deal");
        check(addOverflowVerdict != null && addOverflowVerdict.passed(),
            "the int-add-overflow fixture passes on all three lanes "
                + "byte-exact against the on-disk 7:10 pin, got: "
                + addOverflowVerdict);
        LaneExecution addOverflowExecution = jvmLaneExecution(CORPUS_ROOT,
            "backend-runtime/arithmetic/int-add-overflow.deal");
        check(addOverflowExecution instanceof LaneExecution.Executed executed
                && executed.exitCode() == 1
                && new String(executed.stdout(), StandardCharsets.UTF_8)
                    .equals(JVM_ADD_OVERFLOW_FRAMING),
            "the real jvm lane emits the exact pinned int-add-overflow "
                + "framing (E8004 at 7:10), got: " + addOverflowExecution);

        // ISSUE-0604: every fixture of the convergence class matches its
        // on-disk sidecar byte-exact on the jvm lane through the real
        // run (the class-wide form of the criterion above).
        for (String fixturePath : JVM_ARITHMETIC_CONVERGED) {
            GateDispatcher.LaneOutcome arithmeticJvm = outcomeOf(run,
                fixturePath, "jvm");
            check(arithmeticJvm != null && arithmeticJvm.passed(),
                "the ISSUE-0604 arithmetic/conversion/stdlib-int fixture "
                    + fixturePath + " passes the jvm lane byte-exact "
                    + "against its sidecar, got: " + arithmeticJvm);
        }
        // ISSUE-0604: the convergence class is visible in the jvm
        // lane's accounting — every fixture of the class is one of the
        // lane's passes. The leaf pins no fixed pass/fail population:
        // the remaining pre-flip jvm rows belong to the not-yet-landed
        // class leaves (array/bytes/table access), and a fixed
        // population pin would go stale with every canonical advance
        // (the engine boundary excludes fixed population pins). The
        // counters' honesty over the dispatched set is asserted above.
        int[] jvmCounts = run.perBackend().get("jvm");
        check(jvmCounts[0] >= JVM_ARITHMETIC_CONVERGED.size(),
            "the jvm lane's pass count covers the converged arithmetic/"
                + "conversion/stdlib-int class ("
                + JVM_ARITHMETIC_CONVERGED.size() + " fixtures), got "
                + jvmCounts[0] + " / " + jvmCounts[1] + " over "
                + run.runtimeCasesDispatched() + " dispatched");

        // The pre-flip staging is over: the step-7 cutover and the
        // per-class origin leaves (this leaf's arithmetic/conversion/
        // stdlib-int class last) converged the jvm lane, so the real
        // three-lane corpus run is green. The PASS is asserted as an
        // honest zero — no failing outcome, no failure row — with the
        // per-backend counters accounting for every dispatched case (the
        // assertions above).
        check(run.ok() && observedFailures == 0 && run.failures().isEmpty(),
            "the real three-lane corpus run converges green with an "
                + "honest zero (no failing outcome, no failure row), got "
                + observedFailures + " failing outcomes and "
                + run.failures().size() + " failure rows: "
                + run.failures());
        // Never greenwashed (the retired pre-flip staging pin's binding
        // goal, preserved): a genuine single-lane mismatch staged on the
        // real corpus — one fixture's transcript perturbed on the luajit
        // leg only — flips the same harness to FAIL with exactly that
        // failure visible, and shifts no other lane's counters.
        String stagedPath = "backend-runtime/arithmetic/int-add-overflow.deal";
        DifferentialGate.GateRun staged = DifferentialGate.run(CORPUS_ROOT,
            Map.of("luajit",
                    new SingleCasePerturbingLuaLane(CORPUS_ROOT, stagedPath),
                "jvm", new JvmLane(CORPUS_ROOT),
                "js", new JsLane(CORPUS_ROOT)),
            jobs, FULL_RUN_DEADLINE, capture);
        int[] stagedLuajit = staged.perBackend().get("luajit");
        int[] realLuajit = run.perBackend().get("luajit");
        GateDispatcher.LaneOutcome stagedOutcome = outcomeOf(staged,
            stagedPath, "luajit");
        DifferentialGate.GateFailure stagedFailure = staged.failures()
            .size() == 1 ? staged.failures().get(0) : null;
        check(!staged.ok() && stagedFailure != null
                && "lane".equals(stagedFailure.kind())
                && stagedFailure.subject().equals("luajit " + stagedPath)
                && stagedOutcome != null && !stagedOutcome.passed()
                && stagedLuajit[0] == realLuajit[0] - 1
                && stagedLuajit[1] == realLuajit[1] + 1
                && Arrays.equals(staged.perBackend().get("jvm"),
                    run.perBackend().get("jvm"))
                && Arrays.equals(staged.perBackend().get("js"),
                    run.perBackend().get("js")),
            "the staged single-lane mismatch flips the verdict to FAIL "
                + "with exactly that failure visible and every other "
                + "lane counter unchanged, got: " + staged.failures()
                + " / luajit " + stagedLuajit[0] + "/" + stagedLuajit[1]);
        System.out.println("    full run: " + elapsedMillis + " ms, "
            + run.verdicts().size() + " verdicts, "
            + observedFailures + " lane failures");
    }

    // =========================================================================
    // Experiment 1: a divergent console string on exactly one backend
    // (Verification 1)
    // =========================================================================

    /** TEST DOUBLE — a scratch Lua lane perturbing one console byte of
     * the captured transcript (the controlled single-backend divergence;
     * flagged as a double, the other two lanes stay production). */
    private static final class ConsolePerturbingLuaLane extends LuaLane {
        ConsolePerturbingLuaLane(Path conformanceRoot) {
            super(conformanceRoot);
        }

        @Override
        public LaneExecution execute(LaneCase laneCase) throws Exception {
            LaneExecution base = super.execute(laneCase);
            if (base instanceof LaneExecution.Executed executed) {
                byte[] stdout = new String(executed.stdout(),
                    StandardCharsets.UTF_8).replace("beta", "gamma")
                    .getBytes(StandardCharsets.UTF_8);
                return new LaneExecution.Executed(stdout, executed.stderr(),
                    executed.exitCode());
            }
            return base;
        }
    }

    /** TEST DOUBLE — a real-corpus LuaJIT lane perturbing exactly one
     * designated fixture's transcript (the staged single-lane mismatch
     * of the never-greenwashed pin; every other case and lane stays
     * production). */
    private static final class SingleCasePerturbingLuaLane extends LuaLane {
        private final String target;

        SingleCasePerturbingLuaLane(Path conformanceRoot, String target) {
            super(conformanceRoot);
            this.target = target;
        }

        @Override
        public LaneExecution execute(LaneCase laneCase) throws Exception {
            LaneExecution base = super.execute(laneCase);
            if (base instanceof LaneExecution.Executed executed
                    && laneCase.fixturePath().equals(target)) {
                byte[] stdout = new String(executed.stdout(),
                    StandardCharsets.UTF_8).concat("staged-mismatch\n")
                    .getBytes(StandardCharsets.UTF_8);
                return new LaneExecution.Executed(stdout, executed.stderr(),
                    executed.exitCode());
            }
            return base;
        }
    }

    private static final String DIVERGENCE_PROBE_SOURCE =
        "import * as console from \"std/console\"\n"
        + "\n"
        + "export function first_export(): null {\n"
        + "  console.log(\"alpha\");\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function second_export(): null {\n"
        + "  console.log(\"beta\");\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  return null;\n"
        + "}\n";

    private static void divergentConsoleStringProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 1: divergent console string on "
            + "exactly one backend --");
        String corpusPath = "backend-runtime/scratch/divergence-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + DIVERGENCE_PROBE_SOURCE,
            uniformSidecar("alpha\nbeta\n"));
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), "luajit",
                new ConsolePerturbingLuaLane(scratch.root())),
            Duration.ofSeconds(60));
        check(!run.ok() && run.failures().size() == 1,
            "the divergent case fails with exactly one gate failure, got: "
                + run.failures());
        GateDispatcher.LaneOutcome luajit = outcomeOf(run, corpusPath,
            "luajit");
        check(luajit != null && !luajit.passed()
                && luajit.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && luajit.mismatch().get().subject().equals("luajit")
                && luajit.mismatch().get().detail().contains(
                    "stdout differs at byte 6: expected 0x62, got 0x67"),
            "the divergence fails exactly the luajit lane with the first "
                + "differing byte, got: " + luajit);
        GateDispatcher.LaneOutcome jvm = outcomeOf(run, corpusPath, "jvm");
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(jvm != null && jvm.passed() && js != null && js.passed(),
            "the jvm and js lanes match byte-exact (only the perturbed "
                + "backend diverges), got jvm=" + jvm + " js=" + js);
        DifferentialGate.GateFailure failure = run.failures().get(0);
        check("lane".equals(failure.kind())
                && failure.subject().equals("luajit " + corpusPath),
            "the gate failure names backend, fixture, and class, got: "
                + failure);
    }

    // =========================================================================
    // Experiment 2: lane-contract divergences (Verification 4)
    // =========================================================================

    private static final String VALUE_PROBE_SOURCE =
        "export function test_value(): int {\n"
        + "  return 42;\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  return null;\n"
        + "}\n";

    /** TEST DOUBLE — a scratch JS lane whose runner prints every
     * invocation's non-null return value (the G4.4 divergence). */
    private static final class PrintReturnValueLane extends JsLane {
        PrintReturnValueLane(Path conformanceRoot) {
            super(conformanceRoot);
        }

        @Override
        protected String buildRunner(String entryModule,
                List<String> orderedZeroArityExports) {
            return super.runnerPreamble(entryModule,
                    orderedZeroArityExports)
                + "const $rt = require(\"./deal/runtime\");\n"
                + "(async () => {\n"
                + "  const $mod = require(\"./" + entryModule + "\");\n"
                + "  if ($mod.main && $mod.main.$kind === \"function\") "
                + "{ $mod.main.$f(); }\n"
                + "  for (const $k of $zeroAry) {\n"
                + "    const $v = $mod[$k];\n"
                + "    if ($v && $v.$kind === \"function\") {\n"
                + "      const $r = await $v.$f();\n"
                + "      if ($r !== null && $r !== $rt.undefined) {\n"
                + "        console.log($r);\n"
                + "      }\n"
                + "    }\n"
                + "  }\n"
                + "})().catch(($e) => { process.exitCode = 1; });\n";
        }
    }

    private static void printReturnValueDivergenceProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 2a: a lane printing a return "
            + "value --");
        String corpusPath = "backend-runtime/scratch/value-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + VALUE_PROBE_SOURCE, uniformSidecar(""));
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), "js",
                new PrintReturnValueLane(scratch.root())),
            Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && js.mismatch().get().subject().equals("js")
                && js.mismatch().get().detail().contains(
                    "stdout differs at byte 0"),
            "a lane printing a return value fails the pinned transcript "
                + "(TRANSCRIPT_MISMATCH naming the backend and the first "
                + "differing byte), got: " + js);
        check(outcomeOf(run, corpusPath, "luajit").passed()
                && outcomeOf(run, corpusPath, "jvm").passed(),
            "the luajit and jvm lanes discard results and pass");
    }

    private static final String MAIN_PROBE_SOURCE =
        "import * as console from \"std/console\"\n"
        + "\n"
        + "export function test_nothing(): null {\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  console.log(\"main\");\n"
        + "  return null;\n"
        + "}\n";

    private static void invokeMainTwiceDivergenceProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 2b: a lane invoking main twice --");
        String corpusPath = "backend-runtime/scratch/main-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + MAIN_PROBE_SOURCE, uniformSidecar("main\n"));
        JsLane doubleMainLane = new JsLane(scratch.root()) {
            @Override
            protected String buildRunner(String entryModule,
                    List<String> orderedZeroArityExports) {
                return super.buildRunner(entryModule,
                    orderedZeroArityExports).replace(
                        "  for (const $k of $zeroAry) {",
                        "  if ($mod.main && $mod.main.$kind"
                            + " === \"function\") { $mod.main.$f(); }\n"
                            + "  for (const $k of $zeroAry) {");
            }
        };
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), "js", doubleMainLane),
            Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && js.mismatch().get().detail().contains(
                    "stdout differs at byte 5: expected end of stream, "
                        + "got byte 0x6D"),
            "a lane invoking main twice fails the pinned \"main\\n\" "
                + "transcript naming the backend and the first differing "
                + "byte, got: " + js);
        check(outcomeOf(run, corpusPath, "luajit").passed()
                && outcomeOf(run, corpusPath, "jvm").passed(),
            "the luajit and jvm lanes invoke main exactly once and pass");
    }

    private static final String ORDER_PROBE_SOURCE =
        "import * as console from \"std/console\"\n"
        + "\n"
        + "export function first_export(): null {\n"
        + "  console.log(\"first\");\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function second_export(): null {\n"
        + "  console.log(\"second\");\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  return null;\n"
        + "}\n";

    /** TEST DOUBLE — a scratch JS lane whose runner invokes the exports
     * in reverse declaration order (the G4.4 divergence). */
    private static final class ReorderedExportsLane extends JsLane {
        ReorderedExportsLane(Path conformanceRoot) {
            super(conformanceRoot);
        }

        @Override
        protected String buildRunner(String entryModule,
                List<String> orderedZeroArityExports) {
            List<String> reversed = new ArrayList<>(orderedZeroArityExports);
            Collections.reverse(reversed);
            return super.buildRunner(entryModule, reversed);
        }
    }

    private static void reorderedExportsDivergenceProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 2c: a lane reordering export "
            + "invocation --");
        String corpusPath = "backend-runtime/scratch/order-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + ORDER_PROBE_SOURCE,
            uniformSidecar("first\nsecond\n"));
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), "js",
                new ReorderedExportsLane(scratch.root())),
            Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && js.mismatch().get().detail().contains(
                    "stdout differs at byte 0: expected 0x66, got 0x73"),
            "a lane reordering export invocation fails the declaration-"
                + "order transcript naming the backend and the first "
                + "differing byte, got: " + js);
        check(outcomeOf(run, corpusPath, "luajit").passed()
                && outcomeOf(run, corpusPath, "jvm").passed(),
            "the luajit and jvm lanes invoke in declaration order and "
                + "pass");
    }

    private static void stderrFramingDivergenceProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 2d: a lane writing framing to "
            + "stderr --");
        String corpusPath = "backend-runtime/scratch/order-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + ORDER_PROBE_SOURCE,
            uniformSidecar("first\nsecond\n"));
        JsLane stderrFramingLane = new JsLane(scratch.root()) {
            @Override
            protected String buildRunner(String entryModule,
                    List<String> orderedZeroArityExports) {
                return super.buildRunner(entryModule,
                    orderedZeroArityExports)
                    + "\nprocess.stderr.write("
                    + "\"DEAL_ERROR_CODE: LANE_LEAK\\n\");\n";
            }
        };
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), "js", stderrFramingLane),
            Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && js.mismatch().get().detail().contains(
                    "stderr differs at byte 0"),
            "a lane writing framing to stderr fails the pinned empty "
                + "stderr naming the backend and the first differing "
                + "byte, got: " + js);
        check(outcomeOf(run, corpusPath, "luajit").passed()
                && outcomeOf(run, corpusPath, "jvm").passed(),
            "the luajit and jvm lanes keep framing on stdout and pass");
    }

    // =========================================================================
    // Experiment 3: error-snapshot enforcement (Verification 5)
    // =========================================================================

    /** TEST DOUBLE — a scratch JS lane whose deployment lookup rebases
     * the captured line by one extra header line (perturbing exactly the
     * snapshot's line field). */
    private static final class LinePerturbingJsLane extends JsLane {
        LinePerturbingJsLane(Path conformanceRoot) {
            super(conformanceRoot);
        }

        @Override
        protected JsLane.DeploymentEntry deploymentEntryFor(
                String capturedFile, JsLane.JsCompilation compilation) {
            JsLane.DeploymentEntry entry =
                super.deploymentEntryFor(capturedFile, compilation);
            if (entry == null) {
                return null;
            }
            return new JsLane.DeploymentEntry(entry.corpusPath(),
                entry.headerLinesStripped() + 1);
        }
    }

    private static final String FRAME_PROBE_SOURCE =
        "export function test_frame_probe(): null {\n"
        + "  throw { code: \"FRAME_PROBE\", message: \"frame probe\" };\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  return null;\n"
        + "}\n";

    /** The canonical runtime-error sidecar of the scratch frame probe
     * (raw-file coordinates: the throw sits at raw line 7, column 3). */
    private static String frameProbeSidecar(String snapshotJson,
            String errorJson) {
        return "{\n"
            + "  \"version\": 1,\n"
            + "  \"backends\": [\"luajit\", \"jvm\", \"js\"],\n"
            + "  \"expected\": {\n"
            + "    \"mode\": \"runtime-error\",\n"
            + "    \"transcript\": {\n"
            + "      \"stdout\": \"DEAL_ERROR_CODE: FRAME_PROBE\\n"
            + "DEAL_ERROR_SNAPSHOT: " + snapshotJson + "\\n\",\n"
            + "      \"stderr\": \"\"\n"
            + "    },\n"
            + "    \"exitCode\": 1,\n"
            + "    \"error\": " + errorJson + "\n"
            + "  }\n"
            + "}\n";
    }

    private static final String CANONICAL_SNAPSHOT =
        "{\\\"code\\\":\\\"FRAME_PROBE\\\",\\\"message\\\":"
            + "\\\"frame probe\\\",\\\"sourceFile\\\":"
            + "\\\"backend-runtime/scratch/frame-probe.deal\\\","
            + "\\\"line\\\":7,\\\"column\\\":3}";
    private static final String CANONICAL_ERROR =
        "{ \"code\": \"FRAME_PROBE\", \"message\": "
            + "\"frame probe\", \"sourceFile\": "
            + "\"backend-runtime/scratch/frame-probe.deal\", "
            + "\"line\": 7, \"column\": 3 }";

    private static void perturbedErrorFieldProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 3a: a sidecar perturbing one "
            + "error field --");
        String corpusPath = "backend-runtime/scratch/frame-probe.deal";
        String raw = String.format(HEADER_RUNTIME_ERROR_CODE, "FRAME_PROBE")
            + FRAME_PROBE_SOURCE;
        // The transcript stays canonical and the code stays the pinned
        // FRAME_PROBE (the classification cross-check); the error
        // object's message is perturbed — schema-valid, so the
        // comparison reaches the field-exact snapshot check.
        String sidecar = frameProbeSidecar(CANONICAL_SNAPSHOT,
            "{ \"code\": \"FRAME_PROBE\", \"message\": "
                + "\"frame probe X\", \"sourceFile\": "
                + "\"backend-runtime/scratch/frame-probe.deal\", "
                + "\"line\": 7, \"column\": 3 }");
        ScratchCorpus scratch = writeScratchCorpus(corpusPath, raw, sidecar);
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), null, null), Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome luajit = outcomeOf(run, corpusPath,
            "luajit");
        check(luajit != null && !luajit.passed()
                && luajit.mismatch().get().clazz()
                    == MismatchClass.ERROR_SNAPSHOT_MISMATCH
                && luajit.mismatch().get().subject().equals("luajit")
                && luajit.mismatch().get().detail().contains(
                    "error.message must be \"frame probe X\", got "
                        + "\"frame probe\""),
            "the perturbed message fails the luajit lane with "
                + "ERROR_SNAPSHOT_MISMATCH naming the field, got: "
                + luajit);
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.ERROR_SNAPSHOT_MISMATCH
                && js.mismatch().get().detail().contains(
                    "error.message must be"),
            "the perturbed message fails the js lane with "
                + "ERROR_SNAPSHOT_MISMATCH naming the field, got: " + js);
        GateDispatcher.LaneOutcome jvm = outcomeOf(run, corpusPath, "jvm");
        check(jvm != null && !jvm.passed()
                && jvm.mismatch().get().clazz()
                    == MismatchClass.ERROR_SNAPSHOT_MISMATCH
                && jvm.mismatch().get().subject().equals("jvm")
                && jvm.mismatch().get().detail().contains(
                    "error.message must be \"frame probe X\", got "
                        + "\"frame probe\""),
            "the perturbed message fails the jvm lane with "
                + "ERROR_SNAPSHOT_MISMATCH naming the field (the converged "
                + "user-throw capture), got: " + jvm);

        // The "on one backend" form (Verification 5): a flagged lane
        // double rebases exactly the captured line by one on the js
        // lane — the consistent sidecar then fails only that backend's
        // byte comparison naming the first differing byte.
        String consistentSidecar = frameProbeSidecar(CANONICAL_SNAPSHOT,
            CANONICAL_ERROR);
        ScratchCorpus scratchLane = writeScratchCorpus(corpusPath, raw,
            consistentSidecar);
        DifferentialGate.GateRun runLane = runScratch(scratchLane.root(),
            lanes(scratchLane.root(), "js",
                new LinePerturbingJsLane(scratchLane.root())),
            Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome perturbedJs = outcomeOf(runLane, corpusPath,
            "js");
        check(perturbedJs != null && !perturbedJs.passed()
                && perturbedJs.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && perturbedJs.mismatch().get().subject().equals("js")
                && perturbedJs.mismatch().get().detail().contains(
                    "stdout differs at byte"),
            "a lane perturbing one snapshot field on one backend fails "
                + "exactly that backend naming the first differing byte, "
                + "got: " + perturbedJs);
        check(outcomeOf(runLane, corpusPath, "luajit").passed(),
            "the unperturbed luajit lane passes the consistent sidecar");
    }

    private static void pinnedAbsentOptionalProbe(int jobs)
            throws Exception {
        System.out.println("-- Experiment 3b: a sidecar pinning an absent "
            + "optional field --");
        String corpusPath = "backend-runtime/scratch/frame-probe.deal";
        String raw = String.format(HEADER_RUNTIME_ERROR_CODE, "FRAME_PROBE")
            + FRAME_PROBE_SOURCE;
        // frames=2 pinned in the transcript and the error object; the
        // real captured error carries none and the lane never fabricates.
        String snapshotWithFrames = CANONICAL_SNAPSHOT.substring(0,
            CANONICAL_SNAPSHOT.length() - 1)
                + ",\\\"frames\\\":2}";
        String sidecar = frameProbeSidecar(snapshotWithFrames,
            "{ \"code\": \"FRAME_PROBE\", \"message\": "
                + "\"frame probe\", \"sourceFile\": "
                + "\"backend-runtime/scratch/frame-probe.deal\", "
                + "\"line\": 7, \"column\": 3, "
                + "\"frames\": 2 }");
        ScratchCorpus scratch = writeScratchCorpus(corpusPath, raw, sidecar);
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), null, null), Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome luajit = outcomeOf(run, corpusPath,
            "luajit");
        check(luajit != null && !luajit.passed()
                && luajit.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && luajit.mismatch().get().detail().contains(
                    "expected 0x2C, got 0x7D"),
            "the frames-pinned sidecar fails honestly on the luajit lane "
                + "(the emitted snapshot omits frames; the first "
                + "differing byte is the pinned comma vs the emitted "
                + "brace), got: " + luajit);
        check(!stdoutOf(luajitLaneExecution(scratch.root(), corpusPath))
                .contains("frames"),
            "the luajit lane never fabricates the frames field");
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH,
            "the frames-pinned sidecar fails honestly on the js lane, "
                + "got: " + js);
        GateDispatcher.LaneOutcome jvm = outcomeOf(run, corpusPath, "jvm");
        check(jvm != null && !jvm.passed()
                && jvm.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && jvm.mismatch().get().subject().equals("jvm"),
            "the frames-pinned sidecar fails honestly on the jvm lane "
                + "(the captured error carries no frames field and the "
                + "lane never fabricates one), got: " + jvm);
    }

    private static void serializationViolationProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 3c: a snapshot violating the "
            + "canonical serialization --");
        String corpusPath = "backend-runtime/scratch/frame-probe.deal";
        String raw = String.format(HEADER_RUNTIME_ERROR_CODE, "FRAME_PROBE")
            + FRAME_PROBE_SOURCE;
        // The transcript's snapshot reorders the canonical keys — a
        // serialization violation the byte comparison catches.
        String violatedSnapshot =
            "{\\\"message\\\":\\\"frame probe\\\",\\\"code\\\":"
                + "\\\"FRAME_PROBE\\\",\\\"sourceFile\\\":"
                + "\\\"backend-runtime/scratch/frame-probe.deal\\\","
                + "\\\"line\\\":7,\\\"column\\\":3}";
        String sidecar = frameProbeSidecar(violatedSnapshot,
            CANONICAL_ERROR);
        ScratchCorpus scratch = writeScratchCorpus(corpusPath, raw, sidecar);
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), null, null), Duration.ofSeconds(60));
        GateDispatcher.LaneOutcome luajit = outcomeOf(run, corpusPath,
            "luajit");
        check(luajit != null && !luajit.passed()
                && luajit.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && luajit.mismatch().get().detail().contains(
                    "stdout differs at byte"),
            "the serialization violation fails the byte comparison "
                + "naming the backend and the first differing byte, got: "
                + luajit);
        GateDispatcher.LaneOutcome js = outcomeOf(run, corpusPath, "js");
        check(js != null && !js.passed()
                && js.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH,
            "the serialization violation fails the js lane's byte "
                + "comparison, got: " + js);
        GateDispatcher.LaneOutcome jvm = outcomeOf(run, corpusPath, "jvm");
        check(jvm != null && !jvm.passed()
                && jvm.mismatch().get().clazz()
                    == MismatchClass.TRANSCRIPT_MISMATCH
                && jvm.mismatch().get().subject().equals("jvm")
                && jvm.mismatch().get().detail().contains(
                    "stdout differs at byte"),
            "the serialization violation fails the jvm lane's byte "
                + "comparison naming the first differing byte, got: "
                + jvm);
    }

    /** Executes the scratch frame probe on the production luajit lane
     * and returns the captured execution (used to prove the lane never
     * fabricates the frames field). */
    private static LaneExecution luajitLaneExecution(Path root,
            String corpusPath) throws Exception {
        CorpusDiscovery.DiscoveryResult discovery =
            CorpusDiscovery.discover(root);
        CorpusDiscovery.Fixture fixture =
            discovery.corpusByPath().get(corpusPath);
        SidecarGateLoader.LoadResult load = SidecarGateLoader.load(fixture,
            discovery.corpusByPath(), discovery.corpusModuleIndex(), root);
        return new LuaLane(root).execute(new LaneCase(corpusPath, "luajit",
            fixture.file(),
            CorpusDiscovery.compilationSet(fixture, discovery.corpusByPath(),
                root),
            load.runtime().get().expectationFor("luajit")));
    }

    // =========================================================================
    // Experiment 4: compile pins (Verification 7)
    // =========================================================================

    private static final String PIN_PROBE_RAW =
        "// @spec: Diagnostics\n"
        + "// @description: scratch compile pin probe\n"
        + "// @expected: compile-error %s\n"
        + "// @features: scratch\n"
        + "\n"
        + "export function main(): null {\n"
        + "  let x: int = \"nope\";\n"
        + "  return null;\n"
        + "}\n";

    private static String compilePinSidecar(String code, String line,
            String column, String message) {
        return "{\n"
            + "  \"version\": 1,\n"
            + "  \"mode\": \"compile-error\",\n"
            + "  \"diagnostic\": { \"code\": \"" + code + "\", \"line\": "
            + line + ", \"column\": " + column + ", \"message\": "
            + jsonString(message) + " }\n"
            + "}\n";
    }

    private static void compilePinPerturbationProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 4a: perturbed Compile "
            + "Expectation Sidecar fields --");
        // The real frontend emits E3001 at raw line 7, column 16 with
        // the exact message below; each variant perturbs exactly one pin
        // field and must fail COMPILE_DIAGNOSTIC_MISMATCH naming the
        // fixture and the first differing field.
        checkCompilePinVariant("E9999", "E9999", "7", "16",
            "Cannot assign string to int",
            "diagnostic.code must be \"E9999\", got \"E3001\"",
            "code");
        checkCompilePinVariant("E3001", "E3001", "8", "16",
            "Cannot assign string to int",
            "diagnostic.line must be 8, got 7", "line");
        checkCompilePinVariant("E3001", "E3001", "7", "17",
            "Cannot assign string to int",
            "diagnostic.column must be 17, got 16", "column");
        checkCompilePinVariant("E3001", "E3001", "7", "16",
            "Cannot assign int to string",
            "diagnostic.message must be \"Cannot assign int to string\", "
                + "got \"Cannot assign string to int\"",
            "message");
    }

    private static void checkCompilePinVariant(String expectedCode,
            String pinCode, String pinLine, String pinColumn,
            String pinMessage, String expectedDetail, String field)
            throws IOException {
        String corpusPath = "frontend/scratch/pin-probe-" + field + ".deal";
        // The pin's code must equal the fixture's @expected code (schema
        // cross-check), so the code variant flips both together.
        String raw = String.format(PIN_PROBE_RAW, expectedCode);
        String sidecar = compilePinSidecar(pinCode, pinLine, pinColumn,
            pinMessage);
        ScratchCorpus scratch = writeScratchCorpus(corpusPath, raw, sidecar);
        DifferentialGate.GateRun run = runScratch(scratch.root(), Map.of(),
            Duration.ofSeconds(60));
        check(run.classificationFailures().isEmpty(),
            "the perturbed pin sidecar stays schema-valid (field: "
                + field + "), got: " + run.classificationFailures());
        check(run.failures().stream()
                .anyMatch(f -> "compile-diagnostic".equals(f.kind())
                    && f.subject().equals(corpusPath)
                    && f.detail().equals(expectedDetail)),
            "the perturbed " + field + " pin fails "
                + "COMPILE_DIAGNOSTIC_MISMATCH naming fixture and field, "
                + "expected detail [" + expectedDetail + "], got: "
                + run.failures());
        check(run.compileDiagnosticComparisons() == 1,
            "the variant runs exactly one Compile Diagnostic comparison");
    }

    private static void secondErrorDiagnosticProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 4b: a second error diagnostic --");
        String corpusPath = "frontend/scratch/pin-probe-second.deal";
        String raw =
            "// @spec: Diagnostics\n"
            + "// @description: scratch two-error compile pin probe\n"
            + "// @expected: compile-error E3001\n"
            + "// @features: scratch\n"
            + "\n"
            + "export function main(): null {\n"
            + "  let x: int = \"nope\";\n"
            + "  let y: int = \"also\";\n"
            + "  return null;\n"
            + "}\n";
        // The pin describes the first diagnostic; the frontend emits two.
        String sidecar = compilePinSidecar("E3001", "7", "16",
            "Cannot assign string to int");
        ScratchCorpus scratch = writeScratchCorpus(corpusPath, raw, sidecar);
        DifferentialGate.GateRun run = runScratch(scratch.root(), Map.of(),
            Duration.ofSeconds(60));
        check(run.failures().stream()
                .anyMatch(f -> "compile-diagnostic".equals(f.kind())
                    && f.subject().equals(corpusPath)
                    && f.detail().contains(
                        "the fixture must emit exactly one error "
                            + "diagnostic, got 2")),
            "a fixture emitting a second error diagnostic fails "
                + "COMPILE_DIAGNOSTIC_MISMATCH naming the fixture, got: "
                + run.failures());
    }

    // =========================================================================
    // Experiment 5: divergent sidecar schema rejection (Verification 6)
    // =========================================================================

    private static void divergentSidecarSchemaProbe(int jobs)
            throws IOException {
        System.out.println("-- Experiment 5: divergent sidecar schema "
            + "rejection --");
        // (5a) the sanctioned split shape on a non-FFI fixture: the
        // compilation set carries no @extern-c import, so no divergence
        // is sanctioned.
        String corpusPath = "backend-runtime/scratch/divergent-a.deal";
        String divergent = "{\n"
            + "  \"version\": 1,\n"
            + "  \"backends\": {\n"
            + "    \"luajit\": { \"mode\": \"runtime-ok\", \"transcript\": "
            + "{ \"stdout\": \"\", \"stderr\": \"\" }, \"exitCode\": 0 },\n"
            + "    \"jvm\": { \"mode\": \"compile-reject\", \"diagnostic\": "
            + "{ \"code\": \"E6006\" } },\n"
            + "    \"js\": { \"mode\": \"compile-reject\", \"diagnostic\": "
            + "{ \"code\": \"E6006\" } }\n"
            + "  }\n"
            + "}\n";
        ScratchCorpus scratchA = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + ORDER_PROBE_SOURCE, divergent);
        DifferentialGate.GateRun runA = runScratch(scratchA.root(),
            lanes(scratchA.root(), null, null), Duration.ofSeconds(60));
        check(runA.classificationFailures().size() == 1
                && runA.classificationFailures().get(0).detail().contains(
                    "a divergent form is valid only for the C6 "
                        + "rejection: the fixture's compilation set "
                        + "contains no @extern-c import directive"),
            "a divergent sidecar on a non-FFI fixture is rejected by "
                + "schema validation naming the sidecar, got: "
                + runA.classificationFailures());
        check(runA.runtimeCasesDispatched() == 0,
            "the rejected sidecar dispatches no lane (no silent default)");

        // (5b) a divergent sidecar pinning a non-E6006 rejection code:
        // the sanctioned C6 divergence pins E6006 and no other code.
        String corpusPathB = "backend-runtime/scratch/divergent-b.deal";
        String divergentB = "{\n"
            + "  \"version\": 1,\n"
            + "  \"backends\": {\n"
            + "    \"luajit\": { \"mode\": \"runtime-ok\", \"transcript\": "
            + "{ \"stdout\": \"\", \"stderr\": \"\" }, \"exitCode\": 0 },\n"
            + "    \"jvm\": { \"mode\": \"compile-reject\", \"diagnostic\": "
            + "{ \"code\": \"E6005\" } },\n"
            + "    \"js\": { \"mode\": \"compile-reject\", \"diagnostic\": "
            + "{ \"code\": \"E6006\" } }\n"
            + "  }\n"
            + "}\n";
        ScratchCorpus scratchB = writeScratchCorpus(corpusPathB,
            HEADER_RUNTIME_OK + ORDER_PROBE_SOURCE, divergentB);
        DifferentialGate.GateRun runB = runScratch(scratchB.root(),
            lanes(scratchB.root(), null, null), Duration.ofSeconds(60));
        check(runB.classificationFailures().stream()
                .anyMatch(f -> f.detail().contains(
                    "the sanctioned C6 divergence pins the exact "
                        + "diagnostic code E6006 (FFI_UNSUPPORTED_BACKEND), "
                        + "got E6005")),
            "a divergent sidecar with a non-E6006 code is rejected by "
                + "schema validation, got: " + runB.classificationFailures());
        check(runB.runtimeCasesDispatched() == 0,
            "the rejected sidecar dispatches no lane (no silent default)");
    }

    // =========================================================================
    // Experiment 6: the harness-owned deadline (Verification 8)
    // =========================================================================

    private static final String HANG_PROBE_SOURCE =
        "export function test_hang(): null {\n"
        + "  while (true) {\n"
        + "  }\n"
        + "  return null;\n"
        + "}\n"
        + "\n"
        + "export function main(): null {\n"
        + "  return null;\n"
        + "}\n";

    private static void laneTimeoutProbe(int jobs) throws IOException {
        System.out.println("-- Experiment 6: a hung lane exceeds the "
            + "harness-owned deadline --");
        String corpusPath = "backend-runtime/scratch/hang-probe.deal";
        ScratchCorpus scratch = writeScratchCorpus(corpusPath,
            HEADER_RUNTIME_OK + HANG_PROBE_SOURCE, uniformSidecar(""));
        long start = System.nanoTime();
        DifferentialGate.GateRun run = runScratch(scratch.root(),
            lanes(scratch.root(), null, null), Duration.ofMillis(10_000));
        long elapsedMillis = (System.nanoTime() - start) / 1_000_000;
        check(elapsedMillis < 60_000,
            "the deadline releases the case instead of blocking on the "
                + "hung subprocesses (elapsed " + elapsedMillis + " ms)");
        int timeouts = 0;
        for (String backend : SidecarSchemaValidator.BACKEND_NAMES) {
            GateDispatcher.LaneOutcome outcome = outcomeOf(run, corpusPath,
                backend);
            if (outcome != null && !outcome.passed()
                    && outcome.mismatch().get().clazz()
                        == MismatchClass.LANE_TIMEOUT
                    && outcome.mismatch().get().subject().equals(backend)
                    && outcome.mismatch().get().detail().contains(
                        "exceeded the harness-owned deadline of 10000 ms")
                    && outcome.mismatch().get().detail().contains(
                        "the gate never retries a lane")) {
                timeouts++;
            }
        }
        check(timeouts == 3,
            "all three hung lanes fail LANE_TIMEOUT with process "
                + "termination and no retry, got " + timeouts + " of 3");
        check(run.failures().size() == 3
                && run.failures().stream().allMatch(
                    f -> "infrastructure".equals(f.kind())),
            "the three lane timeouts are infrastructure failures (never "
                + "satisfying the case), got: " + run.failures());
    }
}
