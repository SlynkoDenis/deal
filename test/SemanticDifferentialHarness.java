package deal.test;

import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticTraceProtocol;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SharedStdlibSemantics;

import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The differential harness of the decomposition-tail integration
 * verification (ISSUE-0410): runs the identical validated
 * {@link LoweredModuleUnit} + {@link StructuredBodyTable} through the
 * semantic oracle and both shared emitters' real artifacts and compares
 * the three reports event-for-event (semantic-lowering-differential-
 * conformance D2/D4/D7 — no common-consumer skip, no hollow pass).
 *
 * <p><b>Run sequence per consumer.</b> The oracle executes in-process
 * ({@link SemanticOracle}). The shared LuaJIT artifact is emitted by
 * {@link LuaSemanticEmitter}, written to an isolated workspace, executed
 * by the real {@code luajit} binary with the pinned runtime, and its
 * protocol lines are decoded. The shared JVM artifact is emitted by
 * {@link JvmSemanticEmitter}, compiled with the real {@code javac
 * --release 25 -proc:none}, executed by the real {@code java} on the
 * compiled classes, and decoded the same way. Real console effect bytes
 * on each artifact's stdout are cross-checked against its recorded
 * effects. A tool failure is an infrastructure failure of the harness
 * verdict, never a pass.</p>
 *
 * <p><b>Verdict gates (all must hold).</b></p>
 * <ol>
 *   <li>Gate 0 (pre-run): the address-chain protocol over every unit the
 *       harness consumes — the single-evaluation rule and the closed chain
 *       shapes (exactly one commit child, always last). A corrupted chain
 *       (a duplicated commit, a re-wired commit target, a moved child) is
 *       rejected before any consumer runs with the protocol's first
 *       failing rule named; a consumer's fail-closed producer-defect
 *       rejection is likewise a failing verdict, never a crash.</li>
 *   <li>Every consumer produces a report: three real per-consumer
 *       results with at least one event each (no stubbed/partial
 *       run).</li>
 *   <li>Every event validates against its exact validated IR operation:
 *       module, op id, structural parent, kind, and the recomputed
 *       operation-contract digest — a moved child, a wrong selector, a
 *       missing boundary, or a fabricated event fails even with
 *       coincidental output.</li>
 *   <li>Each op has exactly one START and one terminal event, and the
 *       three traces match event-for-event (canonical text).</li>
 *   <li>Ordered effects match event-for-event across consumers and equal
 *       the seed's pinned expectation (the wiki projection).</li>
 *   <li>Terminals match across consumers and equal the seed's pinned
 *       expectation (post-state/result and error origin).</li>
 * </ol>
 */
public final class SemanticDifferentialHarness {

    private SemanticDifferentialHarness() {
    }

    /** The pinned expectation of one matrix seed (the wiki projection). */
    public sealed interface TerminalExpectation {

        /** The run succeeds with exactly this result atom. */
        record SuccessWith(String resultAtom) implements TerminalExpectation {
            public SuccessWith {
                Objects.requireNonNull(resultAtom, "resultAtom must not be null");
            }
        }

        /** The run fails with exactly this code at exactly this origin. */
        record FailureWith(String code, String originText) implements TerminalExpectation {
            public FailureWith {
                Objects.requireNonNull(code, "code must not be null");
            }
        }
    }

    /** The seed expectation: ordered effects plus the terminal projection. */
    public record Expectation(List<String> effects, TerminalExpectation terminal,
                              String what) {

        public Expectation {
            effects = List.copyOf(effects);
            Objects.requireNonNull(terminal, "terminal must not be null");
            Objects.requireNonNull(what, "what must not be null");
        }

        public static Expectation success(String what, List<String> effects,
                                          String resultAtom) {
            return new Expectation(effects,
                new TerminalExpectation.SuccessWith(resultAtom), what);
        }

        public static Expectation failure(String what, List<String> effects, String code,
                                          String originText) {
            return new Expectation(effects,
                new TerminalExpectation.FailureWith(code, originText), what);
        }
    }

    /** The harness verdict: a real execution comparison report. */
    public record Verdict(
        boolean pass,
        String report,
        List<SemanticRuntimeModel.ConsumerRun> runs,
        List<String> failures
    ) {

        public Verdict {
            runs = List.copyOf(runs);
            failures = List.copyOf(failures);
        }
    }

    /**
     * Runs the three-consumer matrix over the validated unit/table and
     * returns the differential verdict.
     *
     * @param unit        the validated lowered module unit; non-null
     * @param table       the unit's produced block-membership table; non-null
     * @param expectation the seed's pinned expectation; non-null
     * @param workspace   an isolated workspace directory for the emitted
     *                    artifacts (created if absent); non-null
     * @return the verdict with the per-consumer comparison report
     */
    public static Verdict run(LoweredModuleUnit unit, StructuredBodyTable table,
                              Expectation expectation, Path workspace) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(expectation, "expectation must not be null");
        Objects.requireNonNull(workspace, "workspace must not be null");
        List<String> failures = new ArrayList<>();
        List<SemanticRuntimeModel.ConsumerRun> runs = new ArrayList<>();
        StringBuilder report = new StringBuilder();
        report.append("== Differential matrix run: ").append(expectation.what())
            .append(" ==\n");

        // Gate 0: the address-chain protocol over the unit the harness
        // consumes (A-D1/A-D9: the single-evaluation rule and the closed
        // chain shapes — exactly one commit child, always last). A
        // corrupted chain (a duplicated commit, a re-wired commit
        // target, a moved child) is a failing verdict naming the first
        // rule, never a coincidental pass: the consumers execute a chain
        // uniformly, so only the protocol can distinguish the corrupted
        // shape from its output.
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> chainFailure =
            deal.semantic.ir.AddressChainProtocol.validate(unit);
        if (chainFailure.isPresent()) {
            return rejectedVerdict("the address-chain protocol rejects the unit",
                chainFailure.get().code() + " " + chainFailure.get().message(), report);
        }

        // 1. The semantic oracle (in-process). A producer defect the
        // oracle rejects fail closed is a failing verdict naming the
        // rejection, never a harness crash.
        SemanticRuntimeModel.ConsumerRun oracle;
        try {
            oracle = SemanticOracle.execute(unit, table);
        } catch (RuntimeException rejected) {
            return rejectedVerdict("the semantic oracle rejects the unit",
                rejected.getClass().getSimpleName() + ": " + rejected.getMessage(),
                report);
        }
        runs.add(oracle);
        report.append(oracle.comparisonReport()).append('\n');

        // 2. The shared LuaJIT emitter artifact.
        SemanticRuntimeModel.ConsumerRun lua = runLua(unit, table, workspace, failures);
        if (lua != null) {
            runs.add(lua);
            report.append(lua.comparisonReport()).append('\n');
        }

        // 3. The shared JVM emitter artifact.
        SemanticRuntimeModel.ConsumerRun jvm = runJvm(unit, table, workspace, failures);
        if (jvm != null) {
            runs.add(jvm);
            report.append(jvm.comparisonReport()).append('\n');
        }

        // Gate 1: three real per-consumer runs.
        if (runs.size() != 3) {
            failures.add("three-consumer gate: only " + runs.size()
                + " of 3 consumers produced a run — the matrix is not a "
                + "stubbed/partial run");
        }
        return verdictFrom(unit, expectation, runs, failures, report);
    }

    // =========================================================================
    // The project-level matrix (cross-module CLASSES surfaces)
    // =========================================================================

    /**
     * Runs the three-consumer project matrix over the validated
     * executable closure (the cross-module factory surface): the
     * semantic oracle executes the closure in-process; the shared
     * LuaJIT combined artifact and the shared JVM combined artifact are
     * emitted, compiled, and executed by the real toolchains. A
     * {@code CLASS_FACTORY} event's expected parent is the triggering
     * caller's {@code CLASS_NEW} op (the cross-unit K-D12 parent),
     * derived deterministically from the caller payloads and the owner
     * registries.
     *
     * @param project    the validated executable closure; non-null
     * @param tables     each module's block-membership table; non-null
     * @param registries each module's class-factory registry; non-null
     * @param expectation the seed's pinned expectation; non-null
     * @param workspace  an isolated workspace directory; non-null
     * @return the verdict with the per-consumer comparison report
     */
    public static Verdict runProject(ExecutableLoweredProject project,
                                     Map<ModuleId, StructuredBodyTable> tables,
                                     Map<ModuleId, ClassFactoryRegistry> registries,
                                     Expectation expectation, Path workspace) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        Objects.requireNonNull(expectation, "expectation must not be null");
        Objects.requireNonNull(workspace, "workspace must not be null");
        List<String> failures = new ArrayList<>();
        List<SemanticRuntimeModel.ConsumerRun> runs = new ArrayList<>();
        StringBuilder report = new StringBuilder();
        report.append("== Differential project matrix run: ").append(expectation.what())
            .append(" ==\n");

        // Gate 0: the address-chain protocol over every closure unit (the
        // project-level twin of the module gate above).
        for (LoweredModuleUnit moduleUnit : project.modules().values()) {
            java.util.Optional<deal.diagnostics.CompilerDiagnostic> chainFailure =
                deal.semantic.ir.AddressChainProtocol.validate(moduleUnit);
            if (chainFailure.isPresent()) {
                return rejectedVerdict("the address-chain protocol rejects module "
                    + moduleUnit.moduleId().path(), chainFailure.get().code() + " "
                    + chainFailure.get().message(), report);
            }
        }

        // 1. The semantic oracle (in-process, complete closure).
        SemanticRuntimeModel.ConsumerRun oracle;
        try {
            oracle = SemanticOracle.executeProjectInits(project, tables, registries, null);
        } catch (RuntimeException rejected) {
            return rejectedVerdict("the semantic oracle rejects the closure",
                rejected.getClass().getSimpleName() + ": " + rejected.getMessage(),
                report);
        }
        runs.add(oracle);
        report.append(oracle.comparisonReport()).append('\n');

        // 2. The shared LuaJIT combined artifact.
        SemanticRuntimeModel.ConsumerRun lua = runProjectLua(project, tables, registries,
            workspace, failures);
        if (lua != null) {
            runs.add(lua);
            report.append(lua.comparisonReport()).append('\n');
        }

        // 3. The shared JVM combined artifact.
        SemanticRuntimeModel.ConsumerRun jvm = runProjectJvm(project, tables, registries,
            workspace, failures);
        if (jvm != null) {
            runs.add(jvm);
            report.append(jvm.comparisonReport()).append('\n');
        }

        if (runs.size() != 3) {
            failures.add("three-consumer gate: only " + runs.size()
                + " of 3 consumers produced a run — the matrix is not a "
                + "stubbed/partial run");
        }
        return verdictFromProject(project, registries, expectation, runs, failures,
            report);
    }

    /**
     * A failing verdict for a unit (or closure) the harness rejects before
     * any consumer runs: the address-chain protocol's first failing rule
     * or a consumer's fail-closed producer-defect rejection. No consumer
     * runs, so the verdict carries no runs — never a silent pass.
     */
    private static Verdict rejectedVerdict(String what, String detail,
                                           StringBuilder report) {
        List<String> failures = new ArrayList<>();
        failures.add(what + ": " + detail);
        report.append("== Verdict: FAIL ==\n");
        for (String failure : failures) {
            report.append("FAIL: ").append(failure).append('\n');
        }
        return new Verdict(false, report.toString(), List.of(), failures);
    }

    /** The shared LuaJIT combined-artifact runner. */
    private static SemanticRuntimeModel.ConsumerRun runProjectLua(
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, Path workspace,
            List<String> failures) {
        try {
            Files.createDirectories(workspace);
            String lua = LuaSemanticEmitter.emitProject(project, tables, registries);
            LoweredModuleUnit entry = project.modules().get(project.entryModule());
            Path script = workspace.resolve("project.lua");
            Files.writeString(script, lua, StandardCharsets.UTF_8);
            Path stdout = workspace.resolve("lua-proj-out.txt");
            Path stderr = workspace.resolve("lua-proj-err.txt");
            ProcessBuilder builder = new ProcessBuilder("luajit",
                script.toAbsolutePath().toString());
            builder.redirectOutput(stdout.toFile());
            builder.redirectError(stderr.toFile());
            Process process = builder.start();
            int exit = process.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared LuaJIT project artifact exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun run =
                decodeRun("shared-luajit", entry, protocolLines, failures);
            crossCheckStdout(run, stdoutLines, "shared-luajit", failures);
            return run;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared LuaJIT project infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    /** The shared JVM combined-artifact runner. */
    private static SemanticRuntimeModel.ConsumerRun runProjectJvm(
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, Path workspace,
            List<String> failures) {
        try {
            Files.createDirectories(workspace);
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProject(project, tables, registries);
            LoweredModuleUnit entry = project.modules().get(project.entryModule());
            Path source = workspace.resolve(emission.className() + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("jvm-proj-classes");
            Files.createDirectories(classes);
            String classpath = System.getProperty("java.class.path", "");
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            if (compileExit != 0) {
                failures.add("shared JVM project artifact compilation failed ("
                    + compileExit + "): " + compileOut);
                return null;
            }
            Path stdout = workspace.resolve("jvm-proj-out.txt");
            Path stderr = workspace.resolve("jvm-proj-err.txt");
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + java.io.File.pathSeparator + classes,
                emission.className());
            javaRun.redirectOutput(stdout.toFile());
            javaRun.redirectError(stderr.toFile());
            Process run = javaRun.start();
            int exit = run.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared JVM project artifact exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun consumerRun =
                decodeRun("shared-jvm", entry, protocolLines, failures);
            crossCheckStdout(consumerRun, stdoutLines, "shared-jvm", failures);
            return consumerRun;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared JVM project infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    /**
     * Applies the verdict gates shared by the module and callback
     * matrices over the project closure: every event validates against
     * its exact IR op across all units, with the cross-unit factory
     * parent override (a CLASS_FACTORY event parents to the triggering
     * caller CLASS_NEW).
     */
    private static Verdict verdictFromProject(ExecutableLoweredProject project,
                                              Map<ModuleId, ClassFactoryRegistry> registries,
                                              Expectation expectation,
                                              List<SemanticRuntimeModel.ConsumerRun> runs,
                                              List<String> failures,
                                              StringBuilder report) {
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            if (run.trace().isEmpty()) {
                failures.add(run.consumer() + " produced no events (a hollow run)");
            }
        }

        // Gate 2: every event validates against the exact validated IR
        // op of its owning unit.
        Map<OpId, SemanticOp> opsById = new HashMap<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                opsById.put(op.opId(), op);
            }
        }
        Map<OpId, ArrayDeque<OpId>> factoryParents = factoryParentOverrides(project, registries);
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            // One fresh queue set per consumer: each run validates
            // against the same trigger order independently.
            Map<OpId, ArrayDeque<OpId>> consumerQueues = new HashMap<>();
            for (Map.Entry<OpId, ArrayDeque<OpId>> entry : factoryParents.entrySet()) {
                consumerQueues.put(entry.getKey(), new ArrayDeque<>(entry.getValue()));
            }
            Map<OpId, OpId> lastFactoryParents = new HashMap<>();
            validateEvents(run, opsById, consumerQueues, lastFactoryParents, failures);
        }

        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            checkPairing(run, failures);
        }
        compareTraces(runs, failures);
        compareEffects(runs, expectation, failures);
        compareTerminals(runs, expectation, failures);

        boolean pass = failures.isEmpty();
        report.append("== Verdict: ").append(pass ? "PASS" : "FAIL").append(" ==\n");
        for (String failure : failures) {
            report.append("FAIL: ").append(failure).append('\n');
        }
        return new Verdict(pass, report.toString(), runs, failures);
    }

    /**
     * The deterministic cross-unit factory-parent overrides: every
     * caller {@code CLASS_NEW(SHARED_FACTORY)} resolves its owner
     * factory through the owner's registry — that factory op's executed
     * events parent to the caller op (K-D12). One factory may be
     * triggered by several callers, so the expected parents queue in
     * trigger order (unit order, then op order — the straight-line walk
     * order of the corpus).
     */
    private static Map<OpId, ArrayDeque<OpId>> factoryParentOverrides(
            ExecutableLoweredProject project, Map<ModuleId, ClassFactoryRegistry> registries) {
        Map<OpId, ArrayDeque<OpId>> overrides = new HashMap<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_NEW) {
                    continue;
                }
                KindPayload.ClassNewPayload payload =
                    (KindPayload.ClassNewPayload) op.payload();
                if (payload.defaultOwner() != deal.semantic.ir.DefaultOwner.SHARED_FACTORY) {
                    continue;
                }
                OpId factoryOpId = ClassFactoryRegistry.ownerFactoryOp(registries,
                    payload.classFactoryRef());
                if (factoryOpId != null) {
                    overrides.computeIfAbsent(factoryOpId, k -> new ArrayDeque<>())
                        .add(op.opId());
                }
            }
        }
        return overrides;
    }

    // =========================================================================
    // The host-driven callback surface (CALLBACK_INVOKE dispatch entries)
    // =========================================================================

    /** One scripted host argument of a callback invocation. */
    public sealed interface CallbackArg
        permits CallbackArg.Int, CallbackArg.Number, CallbackArg.Str, CallbackArg.Null {

        /** An int32 argument (the closed int carrier). */
        record Int(long value) implements CallbackArg {
        }

        /** A number argument. */
        record Number(double value) implements CallbackArg {
        }

        /** A string argument. */
        record Str(String value) implements CallbackArg {
        }

        /** A language-null argument. */
        record Null() implements CallbackArg {
        }
    }

    /**
     * Runs the three-consumer callback matrix: the semantic oracle's
     * {@code invokeCallback} surface, the shared LuaJIT artifact's
     * dispatch entry driven by a real top-level host script (the module
     * init walk suppressed under the callback-only drive flag), and the
     * shared JVM artifact's static dispatch entry driven by a real host
     * main — scripted arguments never synthesized traces.
     *
     * @param unit          the validated lowered module unit; non-null
     * @param table         the unit's produced block-membership table; non-null
     * @param functionValue the bound function value identity; non-null
     * @param args          the scripted host arguments; non-null
     * @param expectation   the seed's pinned expectation; non-null
     * @param workspace     an isolated workspace directory; non-null
     * @return the verdict with the per-consumer comparison report
     */
    public static Verdict runCallback(LoweredModuleUnit unit, StructuredBodyTable table,
                                      ValueId functionValue, List<CallbackArg> args,
                                      Expectation expectation, Path workspace) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(functionValue, "functionValue must not be null");
        Objects.requireNonNull(args, "args must not be null");
        Objects.requireNonNull(expectation, "expectation must not be null");
        Objects.requireNonNull(workspace, "workspace must not be null");
        List<String> failures = new ArrayList<>();
        List<SemanticRuntimeModel.ConsumerRun> runs = new ArrayList<>();
        StringBuilder report = new StringBuilder();
        report.append("== Differential callback matrix run: ")
            .append(expectation.what()).append(" ==\n");

        // 1. The semantic oracle (in-process, top-level invocation).
        List<SemanticOracle.Value> oracleArgs = new ArrayList<>();
        for (CallbackArg arg : args) {
            oracleArgs.add(oracleValueOf(arg));
        }
        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.invokeCallback(unit,
            table, functionValue, oracleArgs);
        runs.add(oracle);
        report.append(oracle.comparisonReport()).append('\n');

        // 2. The shared LuaJIT artifact's dispatch entry.
        SemanticRuntimeModel.ConsumerRun lua = runLuaCallback(unit, table, functionValue,
            args, workspace, failures);
        if (lua != null) {
            runs.add(lua);
            report.append(lua.comparisonReport()).append('\n');
        }

        // 3. The shared JVM artifact's dispatch entry.
        SemanticRuntimeModel.ConsumerRun jvm = runJvmCallback(unit, table, functionValue,
            args, workspace, failures);
        if (jvm != null) {
            runs.add(jvm);
            report.append(jvm.comparisonReport()).append('\n');
        }

        if (runs.size() != 3) {
            failures.add("three-consumer gate: only " + runs.size()
                + " of 3 consumers produced a run — the callback matrix is not a "
                + "stubbed/partial run");
        }
        return verdictFrom(unit, expectation, runs, failures, report);
    }

    /** One scripted host argument as the semantic oracle's value. */
    private static SemanticOracle.Value oracleValueOf(CallbackArg arg) {
        return switch (arg) {
            case CallbackArg.Int value -> new SemanticOracle.Value.IntValue(value.value());
            case CallbackArg.Number value -> new SemanticOracle.Value.NumValue(value.value());
            case CallbackArg.Str value -> new SemanticOracle.Value.StrValue(value.value());
            case CallbackArg.Null ignored -> SemanticOracle.Value.NullValue.INSTANCE;
        };
    }

    /** The dispatch entry name of one CALLBACK_INVOKE op (per-unit record). */
    private static String callbackEntryName(OpId opId) {
        return "cb" + opId.id();
    }

    /** The unit's CALLBACK_INVOKE op bound to the given function value. */
    private static SemanticOp callbackOpOf(LoweredModuleUnit unit, ValueId functionValue) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CALLBACK_INVOKE
                    && ((KindPayload.CallbackInvokePayload) op.payload()).function()
                        .equals(functionValue)) {
                return op;
            }
        }
        return null;
    }

    /**
     * The Lua literal of one scripted host argument (the closed carriers):
     * a DEAL number value is the runtime's number-variant carrier, an int
     * value a plain Lua number — exactly the artifact value model's
     * int/number representation.
     */
    private static String luaLiteralOf(CallbackArg arg) {
        return switch (arg) {
            case CallbackArg.Int value -> String.valueOf(value.value());
            case CallbackArg.Number value -> "{__jn = true, k = \"number\", d = "
                + Double.toString(value.value()) + "}";
            case CallbackArg.Str value -> quoteLua(value.value());
            case CallbackArg.Null ignored -> "nil";
        };
    }

    /** The JVM literal of one scripted host argument (the closed carriers). */
    private static String jvmLiteralOf(CallbackArg arg) {
        return switch (arg) {
            case CallbackArg.Int value -> value.value() + "L";
            case CallbackArg.Number value -> Double.toString(value.value()) + "d";
            case CallbackArg.Str value -> "\"" + value.value()
                .replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
            case CallbackArg.Null ignored -> "null";
        };
    }

    /** One Lua string literal. */
    private static String quoteLua(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                default -> sb.append(c);
            }
        }
        sb.append('"');
        return sb.toString();
    }

    /** The shared LuaJIT artifact's callback dispatch entry, host-driven. */
    private static SemanticRuntimeModel.ConsumerRun runLuaCallback(
            LoweredModuleUnit unit, StructuredBodyTable table, ValueId functionValue,
            List<CallbackArg> args, Path workspace, List<String> failures) {
        SemanticOp callback = callbackOpOf(unit, functionValue);
        if (callback == null) {
            failures.add("shared LuaJIT callback drive: the unit records no "
                + "CALLBACK_INVOKE for " + functionValue);
            return null;
        }
        try {
            Files.createDirectories(workspace);
            String lua = LuaSemanticEmitter.emitModule(unit, table);
            Path artifact = workspace.resolve(unit.moduleId().path().replace('/', '_')
                + "-cb.lua");
            Files.writeString(artifact, lua, StandardCharsets.UTF_8);
            StringBuilder argsText = new StringBuilder();
            for (CallbackArg arg : args) {
                if (argsText.length() > 0) {
                    argsText.append(", ");
                }
                argsText.append(luaLiteralOf(arg));
            }
            Path driver = workspace.resolve("lua-cb-driver.lua");
            Files.writeString(driver,
                "dofile(" + quoteLua(artifact.toAbsolutePath().toString()) + ")\n"
                    + "local __ok, __res = pcall(__callbacks["
                    + quoteLua(callbackEntryName(callback.opId())) + "], "
                    + argsText + ")\n"
                    + "if __ok then\n"
                    + "  io.stderr:write(\"R|success|\"..__callbacks.__hostAtom(__res)"
                    + "..\"\\n\")\n"
                    + "else\n"
                    + "  io.stderr:write(\"R|failure|\"..__callbacks.__errtext(__res)"
                    + "..\"\\n\")\n"
                    + "end\n"
                    + "io.stderr:flush()\n",
                StandardCharsets.UTF_8);
            Path stdout = workspace.resolve("lua-cb-out.txt");
            Path stderr = workspace.resolve("lua-cb-err.txt");
            ProcessBuilder builder = new ProcessBuilder("luajit",
                driver.toAbsolutePath().toString());
            builder.environment().put("DEAL_CALLBACK_ONLY", "1");
            builder.redirectOutput(stdout.toFile());
            builder.redirectError(stderr.toFile());
            Process process = builder.start();
            int exit = process.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared LuaJIT callback drive exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun run =
                decodeRun("shared-luajit", unit, protocolLines, failures);
            crossCheckStdout(run, stdoutLines, "shared-luajit", failures);
            return run;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared LuaJIT callback infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    /** The shared JVM artifact's callback dispatch entry, host-driven. */
    private static SemanticRuntimeModel.ConsumerRun runJvmCallback(
            LoweredModuleUnit unit, StructuredBodyTable table, ValueId functionValue,
            List<CallbackArg> args, Path workspace, List<String> failures) {
        SemanticOp callback = callbackOpOf(unit, functionValue);
        if (callback == null) {
            failures.add("shared JVM callback drive: the unit records no "
                + "CALLBACK_INVOKE for " + functionValue);
            return null;
        }
        try {
            Files.createDirectories(workspace);
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitModule(unit, table);
            Path source = workspace.resolve(emission.className() + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("jvm-cb-classes");
            Files.createDirectories(classes);
            String classpath = System.getProperty("java.class.path", "");
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            if (compileExit != 0) {
                failures.add("shared JVM callback artifact compilation failed ("
                    + compileExit + "): " + compileOut);
                return null;
            }
            KindPayload.CallbackInvokePayload payload =
                (KindPayload.CallbackInvokePayload) callback.payload();
            String returnKind = staticKindOf(payload.descriptor().returnType());
            StringBuilder argsText = new StringBuilder();
            for (CallbackArg arg : args) {
                if (argsText.length() > 0) {
                    argsText.append(", ");
                }
                argsText.append(jvmLiteralOf(arg));
            }
            String driverClass = emission.className() + "CallbackDriver";
            Path driver = workspace.resolve(driverClass + ".java");
            Files.writeString(driver,
                "public class " + driverClass + " {\n"
                    + "  public static void main(String[] args) {\n"
                    + "    try {\n"
                    + "      Object r = " + emission.className() + "."
                    + callbackEntryName(callback.opId()) + "(new Object[]{"
                    + argsText + "});\n"
                    + "      System.err.println(\"R|success|\" + "
                    + "deal.codegen.jvm.JvmRuntime.atom(r, \"" + returnKind
                    + "\"));\n"
                    + "    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n"
                    + "      System.err.println(\"R|failure|\" + "
                    + "deal.codegen.jvm.JvmRuntime.errtext(e));\n"
                    + "    }\n"
                    + "    System.err.flush();\n"
                    + "  }\n"
                    + "}\n",
                StandardCharsets.UTF_8);
            ProcessBuilder driverJavac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath + java.io.File.pathSeparator + classes,
                "-d", classes.toString(), driver.toAbsolutePath().toString());
            driverJavac.redirectErrorStream(true);
            Process driverCompile = driverJavac.start();
            String driverOut = new String(driverCompile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int driverExit = driverCompile.waitFor();
            if (driverExit != 0) {
                failures.add("shared JVM callback driver compilation failed ("
                    + driverExit + "): " + driverOut);
                return null;
            }
            Path stdout = workspace.resolve("jvm-cb-out.txt");
            Path stderr = workspace.resolve("jvm-cb-err.txt");
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, driverClass);
            javaRun.redirectOutput(stdout.toFile());
            javaRun.redirectError(stderr.toFile());
            Process run = javaRun.start();
            int exit = run.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared JVM callback drive exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun consumerRun =
                decodeRun("shared-jvm", unit, protocolLines, failures);
            crossCheckStdout(consumerRun, stdoutLines, "shared-jvm", failures);
            return consumerRun;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared JVM callback infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    // =========================================================================
    // The host-driven async-entry surface (async EXTERNAL_ENTRY dispatch)
    // =========================================================================

    /** One scripted async host completion terminal of the deterministic host seam. */
    public sealed interface AsyncHostCompletion
        permits AsyncHostCompletion.Returned, AsyncHostCompletion.Thrown {

        /** The host completed by value. */
        record Returned(CallbackArg value) implements AsyncHostCompletion {
        }

        /** The host completed by throwing (code/message preserved). */
        record Thrown(String code, String message) implements AsyncHostCompletion {
        }
    }

    /**
     * The scripted async host behavior of one seed: the bound operation
     * label (null scripts the bad-handle terminal), the expected host
     * export cell (null: the seam keys on the operation label alone),
     * and the completion. A non-null {@code expectedExport} makes the
     * seam key on the export identity cell exactly like a scenario host
     * adapter that keys its scripted async terminals on the documented
     * export cell ({@code HostResponder.startAsync} {@code @param
     * export}; {@code JvmRuntime.HostAsync.startAsync} {@code @param
     * export}): a start whose export cell does not match scripts the
     * bad-handle terminal, so the three-consumer parity of the
     * {@code ASYNC_START(HOST)} export cell is gate-pinned.
     */
    public record AsyncHostScript(String boundLabel, String expectedExport,
                                  AsyncHostCompletion completion) {

        /** Scripts the seam keyed on the operation label alone (the export cell unchecked). */
        public AsyncHostScript(String boundLabel, AsyncHostCompletion completion) {
            this(boundLabel, null, completion);
        }

        public AsyncHostScript {
            Objects.requireNonNull(completion, "completion must not be null");
        }
    }

    /**
     * Runs the three-consumer async-entry matrix: the semantic oracle's
     * {@code invokeAsyncEntry} surface, the shared LuaJIT artifacts'
     * async-entry dispatch entry driven by a real top-level host script
     * (module initialization first, then the entry — the deferred-main
     * drive), and the shared JVM artifacts' static dispatch entry driven
     * by a real host driver main — scripted arguments and scripted host
     * terminals, never synthesized traces. The project may carry several
     * modules (cross-module async: the caller's
     * {@code ASYNC_START(EXTERNAL)} executes the callee artifact's entry).
     *
     * @param project    the validated executable project closure; non-null
     * @param tables     the produced block-membership tables per module; non-null
     * @param exportName the invoked async export name; non-null
     * @param args       the scripted host arguments; non-null
     * @param expectation the seed's pinned expectation; non-null
     * @param workspace  an isolated workspace directory; non-null
     * @param host       the scripted async host seam (null: no host operations)
     * @return the verdict with the per-consumer comparison report
     */
    public static Verdict runAsyncEntry(deal.semantic.ir.ExecutableLoweredProject project,
            Map<deal.semantic.ir.ModuleId, StructuredBodyTable> tables,
            String exportName, List<CallbackArg> args, Expectation expectation,
            Path workspace, AsyncHostScript host) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(exportName, "exportName must not be null");
        Objects.requireNonNull(args, "args must not be null");
        Objects.requireNonNull(expectation, "expectation must not be null");
        Objects.requireNonNull(workspace, "workspace must not be null");
        List<String> failures = new ArrayList<>();
        List<SemanticRuntimeModel.ConsumerRun> runs = new ArrayList<>();
        StringBuilder report = new StringBuilder();
        report.append("== Differential async-entry matrix run: ")
            .append(expectation.what()).append(" ==\n");

        // 1. The semantic oracle (in-process, top-level invocation).
        List<SemanticOracle.Value> oracleArgs = new ArrayList<>();
        for (CallbackArg arg : args) {
            oracleArgs.add(oracleValueOf(arg));
        }
        SemanticOracle.HostResponder responder = host == null ? null
            : new SemanticOracle.HostResponder() {
                @Override
                public String startAsync(deal.semantic.ir.ModuleId module, String export,
                        RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args,
                        String operationLabel) {
                    if (host.expectedExport() != null
                            && !host.expectedExport().equals(export)) {
                        return null; // a mismatched export cell is a bad handle
                    }
                    return host.boundLabel();
                }

                @Override
                public SyncOutcome completeAsync(String operationLabel) {
                    return switch (host.completion()) {
                        case AsyncHostCompletion.Returned returned ->
                            new SyncOutcome.Returned(oracleValueOf(returned.value()));
                        case AsyncHostCompletion.Thrown thrown ->
                            new SyncOutcome.Thrown(thrown.code(), thrown.message());
                    };
                }
            };
        SemanticRuntimeModel.ConsumerRun oracle =
            SemanticOracle.invokeAsyncEntry(project, tables, responder,
                project.entryModule(), exportName, oracleArgs);
        runs.add(oracle);
        report.append(oracle.comparisonReport()).append('\n');

        // 2. The shared LuaJIT artifacts' dispatch entries.
        SemanticRuntimeModel.ConsumerRun lua = runLuaAsyncEntry(project, tables,
            exportName, args, workspace, host, failures);
        if (lua != null) {
            runs.add(lua);
            report.append(lua.comparisonReport()).append('\n');
        }

        // 3. The shared JVM artifacts' dispatch entries.
        SemanticRuntimeModel.ConsumerRun jvm = runJvmAsyncEntry(project, tables,
            exportName, args, workspace, host, failures);
        if (jvm != null) {
            runs.add(jvm);
            report.append(jvm.comparisonReport()).append('\n');
        }

        if (runs.size() != 3) {
            failures.add("three-consumer gate: only " + runs.size()
                + " of 3 consumers produced a run — the async-entry matrix is not a "
                + "stubbed/partial run");
        }
        return verdictFrom(project.modules(), expectation, runs, failures, report);
    }

    /** The async EXTERNAL_ENTRY op of the entry module's export, or null. */
    private static SemanticOp asyncEntryOf(deal.semantic.ir.ExecutableLoweredProject project,
                                           String exportName) {
        LoweredModuleUnit unit = project.modules().get(project.entryModule());
        if (unit == null) {
            return null;
        }
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY) {
                KindPayload.ExternalEntryPayload payload =
                    (KindPayload.ExternalEntryPayload) op.payload();
                if (payload.async() && payload.exportName().equals(exportName)) {
                    return op;
                }
            }
        }
        return null;
    }

    /** The shared LuaJIT async-entry dispatch drive (deferred main + entry). */
    private static SemanticRuntimeModel.ConsumerRun runLuaAsyncEntry(
            deal.semantic.ir.ExecutableLoweredProject project,
            Map<deal.semantic.ir.ModuleId, StructuredBodyTable> tables,
            String exportName, List<CallbackArg> args, Path workspace,
            AsyncHostScript host, List<String> failures) {
        SemanticOp entry = asyncEntryOf(project, exportName);
        if (entry == null) {
            failures.add("shared LuaJIT async-entry drive: the entry module records no "
                + "async EXTERNAL_ENTRY for '" + exportName + "'");
            return null;
        }
        try {
            Files.createDirectories(workspace);
            List<String> dofiles = new ArrayList<>();
            for (LoweredModuleUnit unit : project.modules().values()) {
                if (unit.moduleId().equals(project.entryModule())) {
                    continue;
                }
                String lua = LuaSemanticEmitter.emitModule(unit, tables.get(unit.moduleId()));
                Path artifact = workspace.resolve(unit.moduleId().path().replace('/', '_')
                    + "-dep.lua");
                Files.writeString(artifact, lua, StandardCharsets.UTF_8);
                dofiles.add("dofile(" + quoteLua(artifact.toAbsolutePath().toString())
                    + ")\n");
            }
            LoweredModuleUnit entryUnit = project.modules().get(project.entryModule());
            String lua = LuaSemanticEmitter.emitModule(entryUnit,
                tables.get(project.entryModule()));
            Path entryArtifact = workspace.resolve("entry.lua");
            Files.writeString(entryArtifact, lua, StandardCharsets.UTF_8);
            StringBuilder drive = new StringBuilder();
            for (String dofile : dofiles) {
                drive.append(dofile);
            }
            drive.append("dofile(").append(quoteLua(entryArtifact.toAbsolutePath().toString()))
                .append(")\n");
            if (host != null) {
                drive.append("__callbacks.__hostStartAsync = function(label, module, "
                    + "export, ...)\n");
                if (host.boundLabel() == null) {
                    drive.append("  return nil\n");
                } else {
                    if (host.expectedExport() != null) {
                        drive.append("  if export ~= ")
                            .append(quoteLua(host.expectedExport()))
                            .append(" then return nil end\n");
                    }
                    drive.append("  return ").append(quoteLua(host.boundLabel())).append("\n");
                }
                drive.append("end\n");
                drive.append("__callbacks.__hostCompleteAsync = function(label)\n");
                switch (host.completion()) {
                    case AsyncHostCompletion.Returned returned -> {
                        drive.append("  return {ok = true, v = ")
                            .append(luaLiteralOf(returned.value())).append("}\n");
                    }
                    case AsyncHostCompletion.Thrown thrown -> {
                        drive.append("  return {ok = false, code = ")
                            .append(quoteLua(thrown.code())).append(", m = ")
                            .append(quoteLua(thrown.message())).append("}\n");
                    }
                }
                drive.append("end\n");
            }
            drive.append("local __okM, __errM = __dealMain()\n");
            drive.append("if not __okM then\n");
            drive.append("  io.stderr:write(\"R|failure|\"..__callbacks.__errtext(__errM)"
                + "..\"\\n\")\n");
            drive.append("else\n");
            drive.append("  local __okE, __resE = pcall(__asyncEntries[")
                .append(quoteLua(project.entryModule().path() + "#" + exportName))
                .append("], \"-\", true");
            for (CallbackArg arg : args) {
                drive.append(", ").append(luaLiteralOf(arg));
            }
            drive.append(")\n");
            drive.append("  if __okE then\n");
            drive.append("    io.stderr:write(\"R|success|\"..__callbacks.__hostAtom(__resE)"
                + "..\"\\n\")\n");
            drive.append("  else\n");
            drive.append("    io.stderr:write(\"R|failure|\"..__callbacks.__errtext(__resE)"
                + "..\"\\n\")\n");
            drive.append("  end\n");
            drive.append("end\n");
            drive.append("io.stderr:flush()\n");
            Path driver = workspace.resolve("lua-async-entry-driver.lua");
            Files.writeString(driver, drive.toString(), StandardCharsets.UTF_8);
            Path stdout = workspace.resolve("lua-ae-out.txt");
            Path stderr = workspace.resolve("lua-ae-err.txt");
            ProcessBuilder builder = new ProcessBuilder("luajit",
                driver.toAbsolutePath().toString());
            builder.environment().put("DEAL_DEFER_MAIN", "1");
            builder.redirectOutput(stdout.toFile());
            builder.redirectError(stderr.toFile());
            Process process = builder.start();
            int exit = process.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared LuaJIT async-entry drive exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun run =
                decodeRun("shared-luajit", entryUnit, protocolLines, failures);
            crossCheckStdout(run, stdoutLines, "shared-luajit", failures);
            return run;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared LuaJIT async-entry infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    /** The shared JVM async-entry dispatch drive (dealMain + entry from a host main). */
    private static SemanticRuntimeModel.ConsumerRun runJvmAsyncEntry(
            deal.semantic.ir.ExecutableLoweredProject project,
            Map<deal.semantic.ir.ModuleId, StructuredBodyTable> tables,
            String exportName, List<CallbackArg> args, Path workspace,
            AsyncHostScript host, List<String> failures) {
        SemanticOp entry = asyncEntryOf(project, exportName);
        if (entry == null) {
            failures.add("shared JVM async-entry drive: the entry module records no "
                + "async EXTERNAL_ENTRY for '" + exportName + "'");
            return null;
        }
        try {
            Files.createDirectories(workspace);
            Path classes = workspace.resolve("jvm-ae-classes");
            Files.createDirectories(classes);
            String classpath = System.getProperty("java.class.path", "");
            JvmSemanticEmitter.EmissionResult entryEmission = null;
            List<String> sourceFiles = new ArrayList<>();
            for (LoweredModuleUnit unit : project.modules().values()) {
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitModule(unit, tables.get(unit.moduleId()));
                Path source = workspace.resolve(emission.className() + ".java");
                Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
                sourceFiles.add(source.toAbsolutePath().toString());
                if (unit.moduleId().equals(project.entryModule())) {
                    entryEmission = emission;
                }
            }
            List<String> javacArgs = new ArrayList<>(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString()));
            javacArgs.addAll(sourceFiles);
            ProcessBuilder javac = new ProcessBuilder(javacArgs);
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            if (compileExit != 0) {
                failures.add("shared JVM async-entry artifact compilation failed ("
                    + compileExit + "): " + compileOut);
                return null;
            }
            KindPayload.ExternalEntryPayload payload =
                (KindPayload.ExternalEntryPayload) entry.payload();
            String returnKind = staticKindOf(payload.completionDescriptor());
            StringBuilder argsText = new StringBuilder();
            for (CallbackArg arg : args) {
                if (argsText.length() > 0) {
                    argsText.append(", ");
                }
                argsText.append(jvmLiteralOf(arg));
            }
            String driverClass = entryEmission.className() + "AsyncEntryDriver";
            Path driver = workspace.resolve(driverClass + ".java");
            StringBuilder driverSource = new StringBuilder();
            driverSource.append("public class ").append(driverClass).append(" {\n")
                .append("  public static void main(String[] args) {\n");
            if (host != null) {
                driverSource.append("    deal.codegen.jvm.JvmRuntime.HOST_ASYNC = "
                    + "new deal.codegen.jvm.JvmRuntime.HostAsync() {\n");
                driverSource.append("      public String startAsync(String module, "
                    + "String export, String label, Object[] args) {\n");
                if (host.boundLabel() == null) {
                    driverSource.append("        return null;\n");
                } else {
                    if (host.expectedExport() != null) {
                        driverSource.append("        if (!")
                            .append(javaStringLiteral(host.expectedExport()))
                            .append(".equals(export)) return null;\n");
                    }
                    driverSource.append("        return ")
                        .append(javaStringLiteral(host.boundLabel())).append(";\n");
                }
                driverSource.append("      }\n");
                driverSource.append("      public deal.codegen.jvm.JvmRuntime.HostAsync."
                    + "HostCompletion completeAsync(String label) {\n");
                switch (host.completion()) {
                    case AsyncHostCompletion.Returned returned ->
                        driverSource.append("        return new deal.codegen.jvm.JvmRuntime."
                            + "HostAsync.HostCompletion(")
                            .append(jvmLiteralOf(returned.value()))
                            .append(", null, null);\n");
                    case AsyncHostCompletion.Thrown thrown ->
                        driverSource.append("        return new deal.codegen.jvm.JvmRuntime."
                            + "HostAsync.HostCompletion(null, ")
                            .append(javaStringLiteral(thrown.code())).append(", ")
                            .append(javaStringLiteral(thrown.message())).append(");\n");
                }
                driverSource.append("      }\n")
                    .append("    };\n");
            }
            driverSource.append("    try {\n")
                .append("      ").append(entryEmission.className()).append(".dealMain();\n")
                .append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n")
                .append("      System.err.println(\"R|failure|\" + "
                    + "deal.codegen.jvm.JvmRuntime.errtext(e));\n")
                .append("      System.err.flush();\n")
                .append("      return;\n")
                .append("    }\n")
                .append("    try {\n")
                .append("      Object r = ").append(entryEmission.className())
                .append(".ae").append(entry.opId().id())
                .append("(\"-\", true, new Object[]{").append(argsText).append("});\n")
                .append("      System.err.println(\"R|success|\" + "
                    + "deal.codegen.jvm.JvmRuntime.atom(r, \"")
                .append(returnKind).append("\"));\n")
                .append("    } catch (deal.codegen.jvm.JvmRuntime.DealError e) {\n")
                .append("      System.err.println(\"R|failure|\" + "
                    + "deal.codegen.jvm.JvmRuntime.errtext(e));\n")
                .append("    }\n")
                .append("    System.err.flush();\n")
                .append("  }\n")
                .append("}\n");
            Files.writeString(driver, driverSource.toString(), StandardCharsets.UTF_8);
            ProcessBuilder driverJavac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath + java.io.File.pathSeparator + classes,
                "-d", classes.toString(), driver.toAbsolutePath().toString());
            driverJavac.redirectErrorStream(true);
            Process driverCompile = driverJavac.start();
            String driverOut = new String(driverCompile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int driverExit = driverCompile.waitFor();
            if (driverExit != 0) {
                failures.add("shared JVM async-entry driver compilation failed ("
                    + driverExit + "): " + driverOut);
                return null;
            }
            Path stdout = workspace.resolve("jvm-ae-out.txt");
            Path stderr = workspace.resolve("jvm-ae-err.txt");
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, driverClass);
            javaRun.redirectOutput(stdout.toFile());
            javaRun.redirectError(stderr.toFile());
            Process run = javaRun.start();
            int exit = run.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared JVM async-entry drive exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun consumerRun =
                decodeRun("shared-jvm", project.modules().get(project.entryModule()),
                    protocolLines, failures);
            crossCheckStdout(consumerRun, stdoutLines, "shared-jvm", failures);
            return consumerRun;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared JVM async-entry infrastructure failure: "
                + exception.getMessage());
            return null;
        }
    }

    /** One Java string literal. */
    private static String javaStringLiteral(String text) {
        return "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    /** The closed static runtime kind of a descriptor (the emitter's map). */
    private static String staticKindOf(RuntimeDescriptor descriptor) {
        if (descriptor instanceof RuntimeDescriptor.Null) {
            return "null";
        }
        if (descriptor instanceof RuntimeDescriptor.Boolean) {
            return "bool";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Number) {
            return "number";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable:" + staticKindOf(nullable.inner());
        }
        return "ref";
    }

    /** Applies the verdict gates shared by the module and callback matrices. */
    private static Verdict verdictFrom(LoweredModuleUnit unit, Expectation expectation,
                                       List<SemanticRuntimeModel.ConsumerRun> runs,
                                       List<String> failures, StringBuilder report) {
        Map<OpId, SemanticOp> opsById = new HashMap<>();
        for (SemanticOp op : unit.ops()) {
            opsById.put(op.opId(), op);
        }
        return verdictFromOps(opsById, expectation, runs, failures, report);
    }

    /** Applies the verdict gates over a multi-module implementation closure. */
    private static Verdict verdictFrom(Map<deal.semantic.ir.ModuleId, LoweredModuleUnit> units,
                                       Expectation expectation,
                                       List<SemanticRuntimeModel.ConsumerRun> runs,
                                       List<String> failures, StringBuilder report) {
        Map<OpId, SemanticOp> opsById = new HashMap<>();
        for (LoweredModuleUnit unit : units.values()) {
            for (SemanticOp op : unit.ops()) {
                opsById.put(op.opId(), op);
            }
        }
        return verdictFromOps(opsById, expectation, runs, failures, report);
    }

    /** Applies the verdict gates shared by the module and callback matrices. */
    private static Verdict verdictFromOps(Map<OpId, SemanticOp> opsById,
                                          Expectation expectation,
                                          List<SemanticRuntimeModel.ConsumerRun> runs,
                                          List<String> failures, StringBuilder report) {
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            if (run.trace().isEmpty()) {
                failures.add(run.consumer() + " produced no events (a hollow run)");
            }
        }

        // Gate 2: every event validates against the exact validated IR op.
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            validateEvents(run, opsById, Map.of(), Map.of(), failures);
        }

        // Gate 3: START/terminal pairing per op and three-way trace equality.
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            checkPairing(run, failures);
        }
        compareTraces(runs, failures);

        // Gate 4: effect equality across consumers and against the projection.
        compareEffects(runs, expectation, failures);

        // Gate 5: terminal equality across consumers and against the projection.
        compareTerminals(runs, expectation, failures);

        boolean pass = failures.isEmpty();
        report.append("== Verdict: ").append(pass ? "PASS" : "FAIL").append(" ==\n");
        for (String failure : failures) {
            report.append("FAIL: ").append(failure).append('\n');
        }
        return new Verdict(pass, report.toString(), runs, failures);
    }

    // =========================================================================
    // Consumer runners
    // =========================================================================

    private static SemanticRuntimeModel.ConsumerRun runLua(LoweredModuleUnit unit,
                                                           StructuredBodyTable table,
                                                           Path workspace,
                                                           List<String> failures) {
        try {
            Files.createDirectories(workspace);
            String lua = LuaSemanticEmitter.emitModule(unit, table);
            Path script = workspace.resolve(unit.moduleId().path().replace('/', '_')
                + ".lua");
            Files.writeString(script, lua, StandardCharsets.UTF_8);
            Path stdout = workspace.resolve("lua-out.txt");
            Path stderr = workspace.resolve("lua-err.txt");
            ProcessBuilder builder = new ProcessBuilder("luajit",
                script.toAbsolutePath().toString());
            builder.redirectOutput(stdout.toFile());
            builder.redirectError(stderr.toFile());
            Process process = builder.start();
            int exit = process.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared LuaJIT artifact exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun run =
                decodeRun("shared-luajit", unit, protocolLines, failures);
            crossCheckStdout(run, stdoutLines, "shared-luajit", failures);
            return run;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared LuaJIT infrastructure failure: " + exception.getMessage());
            return null;
        }
    }

    private static SemanticRuntimeModel.ConsumerRun runJvm(LoweredModuleUnit unit,
                                                           StructuredBodyTable table,
                                                           Path workspace,
                                                           List<String> failures) {
        try {
            Files.createDirectories(workspace);
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitModule(unit, table);
            Path source = workspace.resolve(emission.className() + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("jvm-classes");
            Files.createDirectories(classes);
            String classpath = System.getProperty("java.class.path", "");
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            if (compileExit != 0) {
                failures.add("shared JVM artifact compilation failed ("
                    + compileExit + "): " + compileOut);
                return null;
            }
            Path stdout = workspace.resolve("jvm-out.txt");
            Path stderr = workspace.resolve("jvm-err.txt");
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + java.io.File.pathSeparator + classes,
                emission.className());
            javaRun.redirectOutput(stdout.toFile());
            javaRun.redirectError(stderr.toFile());
            Process run = javaRun.start();
            int exit = run.waitFor();
            List<String> stdoutLines = Files.readAllLines(stdout, StandardCharsets.UTF_8);
            List<String> protocolLines = Files.readAllLines(stderr, StandardCharsets.UTF_8);
            if (exit != 0) {
                failures.add("shared JVM artifact exited " + exit + ": "
                    + String.join(" / ", protocolLines));
                return null;
            }
            SemanticRuntimeModel.ConsumerRun consumerRun =
                decodeRun("shared-jvm", unit, protocolLines, failures);
            crossCheckStdout(consumerRun, stdoutLines, "shared-jvm", failures);
            return consumerRun;
        } catch (IOException | InterruptedException exception) {
            failures.add("shared JVM infrastructure failure: " + exception.getMessage());
            return null;
        }
    }

    /** Decodes the artifact's protocol stream into a consumer run. */
    private static SemanticRuntimeModel.ConsumerRun decodeRun(
            String consumer, LoweredModuleUnit unit, List<String> lines,
            List<String> failures) {
        List<SemanticRuntimeModel.TraceEvent> trace = new ArrayList<>();
        List<SemanticRuntimeModel.EffectEvent> effects = new ArrayList<>();
        SemanticRuntimeModel.Terminal terminal = null;
        for (String line : lines) {
            if (line.isEmpty()) {
                continue;
            }
            try {
                Object decoded = SemanticTraceProtocol.decode(line);
                if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                    trace.add(event);
                } else if (decoded instanceof SemanticRuntimeModel.EffectEvent effect) {
                    effects.add(effect);
                } else if (decoded instanceof SemanticRuntimeModel.Terminal term) {
                    if (terminal != null) {
                        failures.add(consumer + " published two terminals: " + line);
                    }
                    terminal = term;
                }
            } catch (RuntimeException exception) {
                failures.add(consumer + " protocol decode failure on line \"" + line
                    + "\": " + exception.getMessage());
            }
        }
        if (terminal == null) {
            failures.add(consumer + " published no terminal record");
            terminal = new SemanticRuntimeModel.Terminal.Success("null");
        }
        return new SemanticRuntimeModel.ConsumerRun(consumer, unit.moduleId().path(),
            unit.interfaceHash(), unit.loweringContextHash(), trace, effects, terminal,
            consumer + ": decoded " + trace.size() + " events, " + effects.size()
                + " effects");
    }

    /**
     * Cross-checks the real program-output bytes against the recorded
     * console effects: the STDOUT-channel effect texts are exactly the
     * artifact's stdout lines. The STDERR channel shares the trace stream,
     * so trace mode publishes only the protocol record (whose channel
     * field is compared with the other consumers' records); the real
     * STDERR effect bytes are pinned by the production-mode checks.
     */
    private static void crossCheckStdout(SemanticRuntimeModel.ConsumerRun run,
                                         List<String> stdoutLines, String consumer,
                                         List<String> failures) {
        List<String> recorded = new ArrayList<>();
        for (SemanticRuntimeModel.EffectEvent effect : run.effects()) {
            if (effect.kind() == SemanticRuntimeModel.EffectEvent.Kind.CONSOLE_WRITE
                    && effect.channel() == SharedStdlibSemantics.Channel.STDOUT) {
                recorded.add(effect.text());
            }
        }
        if (!recorded.equals(stdoutLines)) {
            failures.add(consumer + " stdout effect bytes " + stdoutLines
                + " do not equal its recorded STDOUT console effects " + recorded);
        }
    }

    // =========================================================================
    // Gates
    // =========================================================================

    /** Gate 2: event validation against the exact validated IR op. */
    private static void validateEvents(SemanticRuntimeModel.ConsumerRun run,
                                       Map<OpId, SemanticOp> opsById,
                                       Map<OpId, ArrayDeque<OpId>> parentOverrides,
                                       Map<OpId, OpId> lastFactoryParents,
                                       List<String> failures) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            SemanticOp op = opsById.get(event.op());
            if (op == null) {
                failures.add(run.consumer() + " event " + event.sequence()
                    + " names op " + event.op() + " absent from the validated unit");
                continue;
            }
            if (event.kind() != op.kind()) {
                failures.add(run.consumer() + " event " + event.sequence() + " kind "
                    + event.kind() + " != the validated op kind " + op.kind());
            }
            if (!event.contractDigest().equals(op.contract().canonicalDigest())) {
                failures.add(run.consumer() + " event " + event.sequence()
                    + " contract digest " + event.contractDigest()
                    + " != the validated operation digest "
                    + op.contract().canonicalDigest());
            }
            OpId expectedParent = op.origin().parentOpId();
            if (op.kind() == SemanticOpKind.CLASS_FACTORY) {
                ArrayDeque<OpId> queue = parentOverrides.get(op.opId());
                if (event.phase() == SemanticRuntimeModel.Phase.START) {
                    // One recorded triggering caller per factory
                    // execution: the START pops it; the terminal
                    // reuses the same parent (the straight-line trigger
                    // order of the corpus).
                    if (queue == null || queue.isEmpty()) {
                        failures.add(run.consumer() + " event " + event.sequence()
                            + " executes CLASS_FACTORY " + op.opId()
                            + " without a recorded triggering caller "
                            + "(the cross-unit parent override queue is empty)");
                        continue;
                    }
                    expectedParent = queue.poll();
                    lastFactoryParents.put(op.opId(), expectedParent);
                } else {
                    expectedParent = lastFactoryParents.get(op.opId());
                    if (expectedParent == null) {
                        failures.add(run.consumer() + " event " + event.sequence()
                            + " terminates CLASS_FACTORY " + op.opId()
                            + " without a recorded triggering START "
                            + "(the cross-unit parent override is unbound)");
                        continue;
                    }
                }
            }
            boolean parentOk;
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY && expectedParent == null) {
                // The cross-unit entry parent (semantic-lowering-
                // differential-conformance D4): an unattached
                // EXTERNAL_ENTRY record executes under its triggering
                // caller op (CALL/ASYNC_START) or top-level under a
                // host-driven drive — the runtime parent is the caller,
                // never the recorded null.
                parentOk = event.parentOp() == null
                    || opsById.containsKey(event.parentOp());
            } else {
                parentOk = Objects.equals(event.parentOp(), expectedParent);
            }
            if (!parentOk) {
                failures.add(run.consumer() + " event " + event.sequence()
                    + " parent " + event.parentOp() + " != the validated op's parent "
                    + expectedParent);
            }
            if (!event.module().equals(unitPathOf(op.opId()))) {
                failures.add(run.consumer() + " event " + event.sequence()
                    + " module " + event.module() + " != the op's module "
                    + unitPathOf(op.opId()));
            }
        }
    }

    private static String unitPathOf(OpId opId) {
        return opId.module().path();
    }

    /** Gate 3a: per op, START/terminal events alternate (shared bodies re-execute). */
    private static void checkPairing(SemanticRuntimeModel.ConsumerRun run,
                                     List<String> failures) {
        Map<OpId, Integer> starts = new HashMap<>();
        Map<OpId, Integer> terminals = new HashMap<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.phase() == SemanticRuntimeModel.Phase.START) {
                starts.merge(event.op(), 1, Integer::sum);
            } else {
                terminals.merge(event.op(), 1, Integer::sum);
            }
        }
        for (Map.Entry<OpId, Integer> entry : starts.entrySet()) {
            Integer terminalCount = terminals.get(entry.getKey());
            if (terminalCount == null || !terminalCount.equals(entry.getValue())) {
                failures.add(run.consumer() + " op " + entry.getKey() + " has "
                    + entry.getValue() + " START events but " + terminalCount
                    + " terminal events (each START needs exactly one terminal)");
            }
        }
        // Each START is followed by exactly one terminal before the next
        // START of the same op (a started operation ends exactly once).
        Map<OpId, Boolean> open = new HashMap<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.phase() == SemanticRuntimeModel.Phase.START) {
                Boolean wasOpen = open.put(event.op(), Boolean.TRUE);
                if (Boolean.TRUE.equals(wasOpen)) {
                    failures.add(run.consumer() + " op " + event.op()
                        + " starts again before its previous terminal");
                }
            } else {
                Boolean wasOpen = open.put(event.op(), Boolean.FALSE);
                if (!Boolean.TRUE.equals(wasOpen)) {
                    failures.add(run.consumer() + " op " + event.op()
                        + " terminates without an open START");
                }
            }
        }
    }

    /** Gate 3b: the three traces match event-for-event. */
    private static void compareTraces(List<SemanticRuntimeModel.ConsumerRun> runs,
                                      List<String> failures) {
        if (runs.size() < 2) {
            return;
        }
        SemanticRuntimeModel.ConsumerRun base = runs.get(0);
        for (int i = 1; i < runs.size(); i++) {
            SemanticRuntimeModel.ConsumerRun other = runs.get(i);
            if (base.trace().size() != other.trace().size()) {
                failures.add("trace length mismatch: " + base.consumer() + " has "
                    + base.trace().size() + " events, " + other.consumer() + " has "
                    + other.trace().size());
                continue;
            }
            for (int j = 0; j < base.trace().size(); j++) {
                String baseText = base.trace().get(j).text();
                String otherText = other.trace().get(j).text();
                if (!baseText.equals(otherText)) {
                    failures.add("trace event " + j + " mismatch: "
                        + base.consumer() + " [" + baseText + "] vs " + other.consumer()
                        + " [" + otherText + "]");
                }
            }
        }
    }

    /** Gate 4: effects across consumers and against the projection. */
    private static void compareEffects(List<SemanticRuntimeModel.ConsumerRun> runs,
                                       Expectation expectation, List<String> failures) {
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            List<String> effects = new ArrayList<>();
            for (SemanticRuntimeModel.EffectEvent effect : run.effects()) {
                effects.add(effect.text());
            }
            if (!effects.equals(expectation.effects())) {
                failures.add(run.consumer() + " effects " + effects
                    + " != the pinned projection " + expectation.effects());
            }
        }
        if (runs.size() >= 2) {
            for (int i = 1; i < runs.size(); i++) {
                if (!runs.get(0).effects().equals(runs.get(i).effects())) {
                    failures.add("effect mismatch: " + runs.get(0).consumer() + " "
                        + runs.get(0).effects() + " vs " + runs.get(i).consumer() + " "
                        + runs.get(i).effects());
                }
            }
        }
    }

    /** Gate 5: terminals across consumers and against the projection. */
    private static void compareTerminals(List<SemanticRuntimeModel.ConsumerRun> runs,
                                         Expectation expectation, List<String> failures) {
        for (SemanticRuntimeModel.ConsumerRun run : runs) {
            switch (expectation.terminal()) {
                case TerminalExpectation.SuccessWith success -> {
                    if (run.terminal() instanceof
                            SemanticRuntimeModel.Terminal.Success terminal
                            && success.resultAtom().equals(terminal.resultAtom())) {
                        // matches
                    } else {
                        failures.add(run.consumer() + " terminal " + terminalText(
                            run.terminal()) + " != the pinned success projection "
                            + success.resultAtom());
                    }
                }
                case TerminalExpectation.FailureWith failure -> {
                    if (run.terminal() instanceof
                            SemanticRuntimeModel.Terminal.DealFailure terminal
                            && failure.code().equals(terminal.error().code())
                            && (failure.originText() == null
                                || failure.originText().equals(terminal.error().origin()))) {
                        // matches
                    } else {
                        failures.add(run.consumer() + " terminal " + terminalText(
                            run.terminal()) + " != the pinned failure projection "
                            + failure.code() + " at " + failure.originText());
                    }
                }
            }
        }
        if (runs.size() >= 2) {
            String base = terminalText(runs.get(0).terminal());
            for (int i = 1; i < runs.size(); i++) {
                if (!base.equals(terminalText(runs.get(i).terminal()))) {
                    failures.add("terminal mismatch: " + runs.get(0).consumer() + " ["
                        + base + "] vs " + runs.get(i).consumer() + " ["
                        + terminalText(runs.get(i).terminal()) + "]");
                }
            }
        }
    }

    private static String terminalText(SemanticRuntimeModel.Terminal terminal) {
        return switch (terminal) {
            case SemanticRuntimeModel.Terminal.Success success ->
                "success(" + success.resultAtom() + ")";
            case SemanticRuntimeModel.Terminal.DealFailure failure ->
                "failure(" + failure.error().code() + "@" + failure.error().origin() + ")";
        };
    }
}
