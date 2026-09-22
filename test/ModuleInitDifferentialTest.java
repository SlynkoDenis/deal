package deal.test;

import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.lexer.Lexer;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.CapabilityRequirementCatalog;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.StructuredBodyTable;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The module-init differential corpus, the shared-emitter totality gate, and
 * the module-init negative controls (sequencing step 9, E1/E3/E8; ISSUE-0590).
 *
 * <p><b>Module-init seeds.</b> The lowerer-produced {@code MODULE_INIT}
 * envelope executes three-way over the production lowering pipelines: a
 * successful init publishes the op's SUCCESS with the walk's events nested
 * under it; a failing init publishes the op's single FAILURE before the run's
 * terminal and publishes zero {@code EXPORT_PUBLISH} events although its
 * block carries the publication ops (the full-program carrier's exported
 * function), so the failure-path evidence is never a hollow empty-set
 * assertion; the full-program carrier carries the
 * resolved import/export ops ({@code MODULE_IMPORT}/{@code EXPORT_READ}/
 * {@code EXPORT_PUBLISH}/{@code ENTRY_INVOKE}) nested under the envelope, so
 * every MODULES R-CAPABILITY required operation is produced and a
 * MODULES-claiming unit validates (the claim was unsatisfiable before this
 * task); a hand-built unit without the op (the synthetic-unit surface) keeps
 * the bare init-block behavior.</p>
 *
 * <p><b>Totality gate.</b> Both emitters' {@code emitOp} switches carry
 * exactly one arm per closed {@code SemanticOpKind} value and retain the
 * default throw (the plain-javac toolchain does not compile-check
 * statement-switch exhaustiveness, so the assertion is a real source-level
 * gate over the closed enum), and a lowered feature corpus is emitted and
 * executed on both real targets ({@code luajit};
 * {@code javac --release 25 -proc:none} + {@code java}) with the three
 * consumers compared event-for-event. No single unit carries all 55 kinds —
 * the lowerer decomposes by family (each family's suite landed its own
 * three-way corpus) and the class-channel carrier and the full-program
 * carrier split the surface — so the per-kind coverage is the arm gate over
 * the closed enum plus the family corpora this suite and the step 1–8 suites
 * execute on the real toolchains.</p>
 *
 * <p><b>Negative controls.</b> A unit whose {@code MODULE_INIT} op records a
 * structural parent (the envelope is parentless) is rejected by the
 * consumers; two defect-injected artifacts fail the failure-path rule the
 * failing seed pins — one publishes the envelope's INITIALIZED state on the
 * FAILURE path, the other publishes an export (with its own
 * {@code EXPORT_PUBLISH} trace event) on the FAILURE path while keeping the
 * state-event shape (one START, one FAILURE, no SUCCESS), so the rule's
 * publication census, not a coincidental state event, is what rejects it.</p>
 */
public class ModuleInitDifferentialTest {

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

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "main.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final Path WORKSPACE = Path.of("build/module-init-diff");

    /**
     * The failing-init seed (the E8 failure path): the full-program carrier
     * gives the unit a resolved import ({@code MODULE_IMPORT}) and an
     * exported function ({@code EXPORT_PUBLISH}/{@code ENTRY_INVOKE} in the
     * module-init block's trailing E7 terminals), so the failing walk's
     * "no export publication" evidence covers a unit whose block really
     * carries publication ops — never a hollow empty-set assertion. The
     * module-level statement at line 6 fails before the block reaches the
     * terminals.
     */
    private static final String FAILING_INIT_SOURCE = """
        import * as console from "std/console"
        export function main(): null {
          console.log("m")
          return null
        }
        let broken: int = 1 / 0
        """;

    // =========================================================================
    // The single-module class pipeline (the ISSUE-0516/ISSUE-0586 pattern)
    // =========================================================================

    private record CheckedSlice(deal.ast.ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private static CheckedSlice checkSlice(String source) {
        Lexer lexer = new Lexer(source, SOURCE_ID);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents());
        deal.parser.ParseResult parse = parser.parse();
        check(parse.diagnostics().isEmpty(),
            "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver names = new NameResolver(MODULE.path(), new StubModuleResolver());
        SymbolTable symbols = names.resolve(parse.program());
        check(names.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + names.diagnostics());
        if (!names.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(MODULE.path(), symbols, names,
            parse.program());
        check(checks.diagnostics().isEmpty(),
            "the slice checks cleanly: " + checks.diagnostics());
        if (!checks.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

    /** The exported class types (and @jsonable synthetics) of the slice. */
    private static Map<String, deal.types.Type> sliceExports(CheckedSlice slice,
                                                             SymbolTable symbols) {
        Map<String, deal.types.Type> exports = new LinkedHashMap<>();
        for (deal.ast.StatementNode stmt : slice.program().statements()) {
            if (stmt instanceof deal.ast.ExportDeclaration exp
                    && exp.declaration() instanceof deal.ast.ClassDeclaration cd) {
                deal.checker.Symbol sym = symbols.resolve(cd.name());
                if (sym instanceof deal.checker.Symbol.ClassSymbol cs) {
                    exports.put(cd.name(),
                        deal.types.Types.classType(cs.name(), cs.identity()));
                    if (cd.isJsonable()) {
                        deal.checker.Symbol fromSym = symbols.resolve(cd.name() + "$fromJson");
                        deal.checker.Symbol toSym = symbols.resolve(cd.name() + "$toJson");
                        if (fromSym instanceof deal.checker.Symbol.FunctionSymbol from) {
                            exports.put(cd.name() + "$fromJson", from.funcType());
                        }
                        if (toSym instanceof deal.checker.Symbol.FunctionSymbol to) {
                            exports.put(cd.name() + "$toJson", to.funcType());
                        }
                    }
                }
            }
        }
        return exports;
    }

    private record Lowered(LoweredModuleUnit unit, StructuredBodyTable table) {
    }

    /**
     * The full-program lowering of one slice (the MODULES arm's carrier: a
     * module with resolved imports and exports produces {@code MODULE_IMPORT}/
     * {@code EXPORT_*}/{@code ENTRY_INVOKE} ops nested under the
     * {@code MODULE_INIT} envelope).
     */
    private static Lowered lowerProgram(String source, String what) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput input = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of(SOURCE_ID), slice.program(), slice.checks(),
            importsOf(slice.program()), exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        ModuleFact fact = new ModuleFact(SOURCE_ID, MODULE, false, false, slice.program(),
            sliceExports(slice, slice.symbols()), slice.symbols(), slice.checks(), List.of());
        deal.semantic.CheckedProjectBuildResult built = CheckedProjectBuilder.build(
            invocation, MODULE, List.of(fact));
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            what + ": the checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests().size() == 1,
            what + ": the foundation detector produces exactly one manifest: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests().size() != 1) {
            return null;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            manifests.manifests().get(0).constructCoverage();
        SemanticLowerer.FullProgramE7Result carrier =
            SemanticLowerer.lowerModuleFullProgramE7(
                input, SemanticProfile.DEAL_V1_2_INT32, coverage,
                built.index().interfaceIndexDigest(), REGISTRY_HASH,
                SemanticIdAllocator.over(List.of(MODULE)), Map.of(), Map.of(), Set.of());
        SemanticLowerer.LoweringResult lowering =
            carrier == null ? null : carrier.lowering();
        check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
            what + " lowers to a validated unit through the full-program carrier: "
                + (lowering == null ? "null" : lowering.diagnostics()));
        if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
            return null;
        }
        return new Lowered(lowering.unit(), lowering.table());
    }

    /** The resolved import facts of the slice (the production resolved ids). */
    private static List<deal.semantic.ir.ResolvedImport> importsOf(
            deal.ast.ProgramNode program) {
        List<deal.semantic.ir.ResolvedImport> imports = new ArrayList<>();
        for (deal.ast.StatementNode statement : program.statements()) {
            if (statement instanceof deal.ast.ImportDeclaration imported) {
                String resolved = switch (imported.modulePath()) {
                    case "std/console" -> "std.console";
                    case "std/string" -> "std.string";
                    case "std/table" -> "std.table";
                    case "std/json" -> "std.json";
                    case "std/math" -> "std.math";
                    case "std/time" -> "std.time";
                    default -> imported.modulePath();
                };
                imports.add(new deal.semantic.ir.ResolvedImport(imported.alias(),
                    imported.modulePath(), new ModuleId(resolved),
                    deal.semantic.ir.ExternalModuleKind.STDLIB));
            }
        }
        return imports;
    }

    /** The checked export facts of the slice (the E7 terminal carrier's input). */
    private static List<deal.semantic.ir.ExportInterface> exportsOf(
            deal.ast.ProgramNode program) {
        List<deal.semantic.ir.ExportInterface> exports = new ArrayList<>();
        for (deal.ast.StatementNode statement : program.statements()) {
            if (statement instanceof deal.ast.ExportDeclaration exported
                    && exported.declaration()
                        instanceof deal.ast.FunctionDeclaration function) {
                exports.add(new deal.semantic.ir.ExportInterface(function.name(),
                    "function"));
            }
        }
        return exports;
    }

    private static Lowered lower(String source, String what) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput input = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of(SOURCE_ID), slice.program(), slice.checks(), List.of(), List.of(),
            CheckedModuleKind.IMPLEMENTATION);
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        ModuleFact fact = new ModuleFact(SOURCE_ID, MODULE, false, false, slice.program(),
            sliceExports(slice, slice.symbols()), slice.symbols(), slice.checks(), List.of());
        deal.semantic.CheckedProjectBuildResult built = CheckedProjectBuilder.build(
            invocation, MODULE, List.of(fact));
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            what + ": the checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests().size() == 1,
            what + ": the foundation detector produces exactly one manifest: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests().size() != 1) {
            return null;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            new LinkedHashMap<>(manifests.manifests().get(0).constructCoverage());
        coverage.remove(ConstructKind.IMPORT_EXPORT_ENTRY);
        ExternalModuleInterface ownInterface = built.index().modules().get(MODULE);
        SemanticLowerer.ClassDeclarationCoreResult result =
            SemanticLowerer.lowerModuleClassCore(input, SemanticProfile.DEAL_V1_2_INT32,
                coverage, built.index().interfaceIndexDigest(), REGISTRY_HASH,
                ownInterface, Map.of(), SemanticIdAllocator.over(List.of(MODULE)));
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return new Lowered(result.lowering().unit(), result.lowering().table());
    }

    private static SemanticDifferentialHarness.Verdict run(Lowered lowered,
            SemanticDifferentialHarness.TerminalExpectation terminal, String what) {
        if (lowered == null) {
            return null;
        }
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            lowered.unit(), lowered.table(),
            new SemanticDifferentialHarness.Expectation(List.of(), terminal, what),
            WORKSPACE);
        check(verdict.pass(), what + ": the three-consumer matrix verdict passes:\n"
            + verdict.report());
        return verdict;
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    // =========================================================================
    // 1. The module-init envelope (successful init)
    // =========================================================================

    static void testSuccessfulInit() {
        System.out.println("-- Module init: the MODULE_INIT envelope runs the init "
            + "block and publishes its SUCCESS --");
        Lowered lowered = lower("""
            export class Person {
              name: string = "anon";
              age: int = 0;
            }
            let p: Person = {name: "bob"}
            """, "successful init");
        if (lowered == null) {
            return;
        }
        List<SemanticOp> initOps = ofKind(lowered.unit(), SemanticOpKind.MODULE_INIT);
        check(initOps.size() == 1,
            "the lowerer produces exactly one MODULE_INIT op per unit; got "
                + initOps.size());
        if (initOps.size() == 1) {
            SemanticOp initOp = initOps.get(0);
            check(initOp.payload()
                    instanceof deal.semantic.ir.KindPayload.ModuleInitPayload payload
                    && payload.module().equals(MODULE)
                    && payload.initBlock().equals(lowered.unit().moduleInit().initBlock()),
                "the MODULE_INIT payload names the module and the module-init block "
                    + "(the ModuleInitPlan carrier)");
            check(initOp.origin().parentOpId() == null && initOp.result() == null
                    && initOp.resultType() == null,
                "the MODULE_INIT op is detached, result-less, and parentless");
            check(!lowered.table().opBlocks().containsKey(initOp.opId()),
                "the MODULE_INIT op is a module-level op outside the "
                    + "block-membership table (the C-D1 exemption)");
        }
        SemanticDifferentialHarness.Verdict verdict = run(lowered,
            new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null"),
            "successful init");
        if (verdict == null) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun consumerRun : verdict.runs()) {
            boolean sawStart = false;
            boolean sawSuccess = false;
            String output = null;
            int starts = 0;
            for (SemanticRuntimeModel.TraceEvent event : consumerRun.trace()) {
                if (event.kind() != SemanticOpKind.MODULE_INIT) {
                    continue;
                }
                if (event.phase() == SemanticRuntimeModel.Phase.START) {
                    sawStart = true;
                    starts++;
                } else {
                    sawSuccess = event.phase() == SemanticRuntimeModel.Phase.SUCCESS;
                    output = event.output();
                }
            }
            check(sawStart && sawSuccess && starts == 1
                    && "state:INITIALIZED".equals(output),
                consumerRun.consumer() + " publishes exactly one MODULE_INIT "
                    + "START/SUCCESS pair with the INITIALIZED state; got starts="
                    + starts + " success=" + sawSuccess + " output=" + output);
        }
    }

    // =========================================================================
    // 2. A failing init publishes the envelope's FAILURE
    // =========================================================================

    static void testFailingInit() {
        System.out.println("-- Module init: a failing walk publishes the envelope's "
            + "FAILURE and no export publication --");
        Lowered lowered = lowerProgram(FAILING_INIT_SOURCE, "failing init");
        if (lowered == null) {
            return;
        }
        int publishOps = ofKind(lowered.unit(), SemanticOpKind.EXPORT_PUBLISH).size();
        int importOps = ofKind(lowered.unit(), SemanticOpKind.MODULE_IMPORT).size();
        check(publishOps >= 1 && importOps >= 1,
            "the failing-init seed carries the nested MODULE_IMPORT/EXPORT_PUBLISH ops "
                + "(the failing walk's zero-publication assertion is not hollow); got "
                + importOps + " import(s), " + publishOps + " publication(s)");
        for (SemanticOp op : lowered.unit().ops()) {
            if (op.kind() == SemanticOpKind.MODULE_IMPORT
                    || op.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                check(lowered.unit().moduleInit().initBlock()
                        .equals(lowered.table().opBlocks().get(op.opId())),
                    "the failing seed's " + op.kind() + " op is a member of the "
                        + "module-init block (nested under the MODULE_INIT envelope)");
            }
        }
        SemanticDifferentialHarness.Verdict verdict = run(lowered,
            new SemanticDifferentialHarness.TerminalExpectation.FailureWith("E8005",
                "main.deal:6:19"),
            "failing init");
        if (verdict == null) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun consumerRun : verdict.runs()) {
            int starts = 0;
            int failures = 0;
            int successes = 0;
            int publications = 0;
            for (SemanticRuntimeModel.TraceEvent event : consumerRun.trace()) {
                if (event.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                    publications++;
                }
                if (event.kind() != SemanticOpKind.MODULE_INIT) {
                    continue;
                }
                switch (event.phase()) {
                    case START -> starts++;
                    case FAILURE -> failures++;
                    case SUCCESS -> successes++;
                }
            }
            check(starts == 1 && failures == 1 && successes == 0,
                consumerRun.consumer() + " publishes one MODULE_INIT START and exactly "
                    + "one FAILURE (no SUCCESS) for the failing walk; got starts="
                    + starts + " failures=" + failures + " successes=" + successes);
            check(publications == 0,
                consumerRun.consumer() + " publishes zero EXPORT_PUBLISH events for the "
                    + "failing walk (the failing init publishes no export at all, never "
                    + "merely none after the FAILURE); got " + publications);
        }
    }

    // =========================================================================
    // 3. A hand-built unit without the op keeps the bare init block
    // =========================================================================

    static void testHandBuiltUnitWithoutOp() {
        System.out.println("-- Module init: a hand-built unit without the op keeps the "
            + "bare init block (the synthetic-unit surface) --");
        Lowered lowered = lower("let x: int = 1", "hand-built baseline");
        if (lowered == null) {
            return;
        }
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : lowered.unit().ops()) {
            if (op.kind() != SemanticOpKind.MODULE_INIT) {
                ops.add(op);
            }
        }
        LoweredModuleUnit stripped = new LoweredModuleUnit(
            lowered.unit().formatVersion(), lowered.unit().semanticProfile(),
            lowered.unit().moduleId(), lowered.unit().interfaceHash(),
            lowered.unit().loweringContextHash(), lowered.unit().requiredCapabilities(),
            lowered.unit().constructCoverage(), lowered.unit().classLayouts(),
            lowered.unit().functions(), lowered.unit().moduleInit(),
            lowered.unit().exportPlan(), lowered.unit().functionBindings(), ops);
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            stripped, lowered.table(),
            new SemanticDifferentialHarness.Expectation(List.of(),
                new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null"),
                "hand-built baseline"),
            WORKSPACE);
        check(verdict.pass(), "the stripped unit runs three-way without the envelope:\n"
            + verdict.report());
        for (SemanticRuntimeModel.ConsumerRun consumerRun : verdict.runs()) {
            boolean sawInit = false;
            for (SemanticRuntimeModel.TraceEvent event : consumerRun.trace()) {
                if (event.kind() == SemanticOpKind.MODULE_INIT) {
                    sawInit = true;
                }
            }
            check(!sawInit, consumerRun.consumer() + " emits no MODULE_INIT event for "
                + "the stripped unit");
        }
    }

    // =========================================================================
    // 4. The totality gate (one arm per closed kind, default throw retained)
    // =========================================================================

    static void testTotalityGate() {
        System.out.println("-- Totality gate: one emitOp arm per closed kind in both "
            + "emitters; the default throw remains --");
        checkArmCoverage("deal/codegen/lua/LuaSemanticEmitter.java", "shared LuaJIT");
        checkArmCoverage("deal/codegen/jvm/JvmSemanticEmitter.java", "shared JVM");
    }

    private static void checkArmCoverage(String path, String what) {
        String source;
        try {
            source = java.nio.file.Files.readString(Path.of(path));
        } catch (java.io.IOException exception) {
            check(false, what + " emitter source is unreadable: "
                + exception.getMessage());
            return;
        }
        int switchStart = source.indexOf("private void emitOp(SemanticOp op");
        check(switchStart >= 0, what + " emitter carries the emitOp switch");
        if (switchStart < 0) {
            return;
        }
        int defaultAt = source.indexOf("default -> throw new IllegalStateException",
            switchStart);
        check(defaultAt >= 0, what + " emitOp keeps the default throw (the fail-closed "
            + "E6005 backstop)");
        if (defaultAt < 0) {
            return;
        }
        String switchText = source.substring(switchStart, defaultAt);
        for (SemanticOpKind kind : EnumSet.allOf(SemanticOpKind.class)) {
            int count = 0;
            int index = 0;
            while ((index = switchText.indexOf("case " + kind.name() + " ", index)) >= 0) {
                count++;
                index += 1;
            }
            check(count == 1, what + " emitOp realizes " + kind.name()
                + " with exactly one arm; got " + count);
        }
    }

    // =========================================================================
    // 5. The behavioral feature corpus (real toolchains)
    // =========================================================================

    static void testFeatureCorpus() {
        System.out.println("-- Totality gate: the feature corpus emits and runs on "
            + "both real targets three-way --");
        Map<String, String> corpus = new LinkedHashMap<>();
        corpus.put("containers", """
            let xs: int[] = [1, 2, 3]
            let t: table = {a: 1}
            let n: int = xs.length
            let first: int | null = xs[0]
            xs[1] = 7
            delete t.a
            """);
        corpus.put("control", """
            let total: int = 0
            let other: int = total - 1
            let text: string = "a" + "b"
            """);
        corpus.put("classes", """
            export class Person {
              name: string = "anon";
              age: int = 0;
              note?: string | null;
            }
            let p: Person = {name: "bob", age: 3}
            p.age = 4
            let present: boolean = has(p.note)
            delete p.note
            """);
        corpus.put("json", """
            // @jsonable
            export class Card {
              rank: int = 0;
              label: string = "x";
            }
            let c: Card = {rank: 1}
            """);
        int units = 0;
        int executed = 0;
        Set<SemanticOpKind> union = EnumSet.noneOf(SemanticOpKind.class);
        for (Map.Entry<String, String> entry : corpus.entrySet()) {
            Lowered lowered = lower(entry.getValue(), entry.getKey());
            if (lowered == null) {
                continue;
            }
            units++;
            for (SemanticOp op : lowered.unit().ops()) {
                union.add(op.kind());
            }
            SemanticDifferentialHarness.Verdict verdict = run(lowered,
                new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null"),
                entry.getKey() + " feature corpus");
            if (verdict != null && verdict.pass()) {
                executed++;
            }
        }
        check(units == corpus.size(), "the feature corpus lowers every unit; got "
            + units + " of " + corpus.size());
        check(executed == units, "every corpus unit runs green three-way; got "
            + executed + " of " + units);
        check(union.contains(SemanticOpKind.MODULE_INIT)
                && union.contains(SemanticOpKind.CLASS_NEW)
                && union.contains(SemanticOpKind.CLASS_DEFAULT)
                && union.contains(SemanticOpKind.CLASS_FACTORY)
                && union.contains(SemanticOpKind.JSON_FROM_CLASS)
                && union.contains(SemanticOpKind.JSON_TO_CLASS)
                && union.contains(SemanticOpKind.FIELD_WRITE)
                && union.contains(SemanticOpKind.HAS_FIELD)
                && union.contains(SemanticOpKind.INDEX_READ)
                && union.contains(SemanticOpKind.DELETE),
            "the corpus exercises the module/class/JSON/container/control families; got "
                + union);
    }

    // =========================================================================
    // 5b. The MODULES carrier seed (resolved imports/exports under the envelope)
    // =========================================================================

    /**
     * The MODULES carrier seed: the full-program unit carries resolved
     * imports and exports ({@code MODULE_IMPORT}/{@code EXPORT_READ}/
     * {@code EXPORT_PUBLISH}/{@code ENTRY_INVOKE}) nested under the
     * {@code MODULE_INIT} envelope, every MODULES required operation is
     * produced (the R-CAPABILITY claim is satisfiable — never a dead schema
     * row), and the corpus runs green three-way with real artifacts.
     */
    static void testModuleImportEnvelopeSeed() {
        System.out.println("-- Modules: resolved imports/exports nest under the MODULE_INIT "
            + "envelope and the MODULES claim is satisfiable --");
        Lowered lowered = lowerProgram("""
            import * as console from "std/console"
            export function main(): null {
              console.log("m")
              return null
            }
            """, "modules carrier seed");
        if (lowered == null) {
            return;
        }
        Set<SemanticOpKind> produced = EnumSet.noneOf(SemanticOpKind.class);
        for (SemanticOp op : lowered.unit().ops()) {
            produced.add(op.kind());
        }
        for (CapabilityRequirementCatalog.RequiredOperation row
                : CapabilityRequirementCatalog.requiredOperations(
                    SemanticCapability.MODULES)) {
            boolean satisfied = false;
            for (SemanticOpKind kind : row.kinds()) {
                if (produced.contains(kind)) {
                    satisfied = true;
                    break;
                }
            }
            check(satisfied, "the MODULES required operation " + row.verbatim()
                + " is produced by the unit (the claim is satisfiable; no dead schema row)");
        }
        LoweredModuleUnit claimed = withCapabilities(lowered.unit(),
            SemanticCapability.MODULES);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> validation =
            SemanticIrValidator.validate(claimed, new SemanticIrValidator.ComparisonFacts(
                lowered.unit().interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                REGISTRY_HASH));
        check(validation.isEmpty(), "the same unit claiming MODULES passes the closed "
            + "validator (R-CAPABILITY satisfied by the produced MODULE_INIT family; "
            + "before ISSUE-0590 the claim was unsatisfiable): " + validation);
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            lowered.unit(), lowered.table(),
            new SemanticDifferentialHarness.Expectation(List.of("m"),
                new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null"),
                "modules carrier seed"),
            WORKSPACE);
        check(verdict.pass(), "the MODULES carrier seed runs green three-way "
            + "(semantic oracle + shared LuaJIT + shared JVM, real artifacts):\n"
            + verdict.report());
        if (!verdict.pass()) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun consumerRun : verdict.runs()) {
            int initStart = -1;
            int initTerminal = -1;
            int importStart = -1;
            int publishTerminal = -1;
            for (int index = 0; index < consumerRun.trace().size(); index++) {
                SemanticRuntimeModel.TraceEvent event = consumerRun.trace().get(index);
                if (event.kind() == SemanticOpKind.MODULE_INIT) {
                    if (event.phase() == SemanticRuntimeModel.Phase.START) {
                        initStart = index;
                    } else {
                        initTerminal = index;
                    }
                } else if (event.kind() == SemanticOpKind.MODULE_IMPORT
                        && event.phase() == SemanticRuntimeModel.Phase.START) {
                    importStart = index;
                } else if (event.kind() == SemanticOpKind.EXPORT_PUBLISH
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                    publishTerminal = index;
                }
            }
            check(initStart >= 0 && initTerminal > initStart && importStart > initStart
                    && publishTerminal > importStart && initTerminal > publishTerminal,
                consumerRun.consumer() + " nests the MODULE_IMPORT/EXPORT_PUBLISH ops "
                    + "under the MODULE_INIT envelope (START before the nested ops, the "
                    + "single terminal after them); got initStart=" + initStart
                    + " importStart=" + importStart + " publishTerminal=" + publishTerminal
                    + " initTerminal=" + initTerminal);
        }
    }

    /** One copy of the unit with the given capability added to its claims. */
    private static LoweredModuleUnit withCapabilities(LoweredModuleUnit unit,
                                                      SemanticCapability capability) {
        Set<SemanticCapability> claims = unit.requiredCapabilities().isEmpty()
            ? EnumSet.noneOf(SemanticCapability.class)
            : EnumSet.copyOf(unit.requiredCapabilities());
        claims.add(capability);
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(), claims,
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), unit.functionBindings(), unit.ops());
    }

    // =========================================================================
    // 6. Negative controls (never a coincidental pass)
    // =========================================================================

    /**
     * The wrong-parent negative: the module-level envelope op is parentless,
     * so a unit whose MODULE_INIT op records a structural parent is rejected
     * by the consumers (the oracle fails closed, the harness verdict fails) —
     * never a coincidental pass on the identical output.
     */
    static void testWrongParentNegative() {
        System.out.println("-- Negative: a parented MODULE_INIT envelope fails (never a "
            + "coincidental pass) --");
        Lowered lowered = lower("let x: int = 1", "wrong parent negative");
        if (lowered == null) {
            return;
        }
        List<SemanticOp> initOps = ofKind(lowered.unit(), SemanticOpKind.MODULE_INIT);
        check(initOps.size() == 1, "the negative seed carries exactly one MODULE_INIT op");
        if (initOps.size() != 1) {
            return;
        }
        SemanticOp bodyOp = null;
        for (SemanticOp op : lowered.unit().ops()) {
            if (op.kind() != SemanticOpKind.MODULE_INIT) {
                bodyOp = op;
                break;
            }
        }
        check(bodyOp != null, "the negative seed carries a body op to name as the wrong "
            + "parent");
        if (bodyOp == null) {
            return;
        }
        SemanticOp initOp = initOps.get(0);
        SemanticOp parented = new SemanticOp(initOp.opId(), initOp.kind(),
            new SourceOrigin(initOp.origin().sourceId(), initOp.origin().span(),
                initOp.origin().kind(), initOp.origin().anchorId(), bodyOp.opId()),
            initOp.result(), initOp.resultType(), initOp.operands(), initOp.operandTypes(),
            initOp.payload(), initOp.failurePolicy(), initOp.contract());
        LoweredModuleUnit mutated = withOps(lowered.unit(), initOp.opId(), parented);
        boolean failing;
        try {
            SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
                mutated, lowered.table(),
                new SemanticDifferentialHarness.Expectation(List.of(),
                    new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null"),
                    "wrong parent negative"),
                WORKSPACE);
            failing = !verdict.pass();
            check(!verdict.pass(), "a parented MODULE_INIT fails the differential verdict "
                + "(never a coincidental pass):\n" + verdict.report());
        } catch (RuntimeException exception) {
            failing = true;
            check(true, "a parented MODULE_INIT fails the consumers closed ("
                + exception.getClass().getSimpleName() + ": " + exception.getMessage()
                + ")");
        }
        check(failing, "the wrong-parent negative control produced a failing outcome");
    }

    /**
     * The failure-path publication negative: an artifact that publishes on
     * the MODULE_INIT FAILURE path is a defect; the failure-path rule the
     * failing-init seed pins — exactly one START, one FAILURE terminal, no
     * SUCCESS, and zero {@code EXPORT_PUBLISH} events — must reject it. Two
     * defects are injected into the emitted artifact text: the state
     * publication (INITIALIZED with its state SUCCESS event), and the export
     * publication without any state event (an export entry plus its own
     * {@code EXPORT_PUBLISH} trace event) — the second is invisible to the
     * state-event census alone, so the rule's publication count is what
     * rejects it. Both controls prove the rule is discriminating and never
     * satisfied by coincidence.
     */
    static void testFailurePathPublicationNegative() {
        System.out.println("-- Negative: an artifact publishing on the MODULE_INIT FAILURE "
            + "path fails the failure-path rule --");
        Lowered lowered = lowerProgram(FAILING_INIT_SOURCE, "failure path negative");
        if (lowered == null) {
            return;
        }
        int publishOps = ofKind(lowered.unit(), SemanticOpKind.EXPORT_PUBLISH).size();
        check(publishOps >= 1,
            "the failure-path negative seed carries EXPORT_PUBLISH ops (the rule is "
                + "not hollow); got " + publishOps);
        String artifact = LuaSemanticEmitter.emitModule(lowered.unit(), lowered.table());
        int failureAt = artifact.indexOf("\"FAILURE\", \"MODULE_INIT\"");
        int successAt = artifact.indexOf("\"SUCCESS\", \"MODULE_INIT\"", failureAt);
        int errorAt = artifact.indexOf("error(__initErr, 0)", failureAt);
        check(failureAt >= 0 && successAt > failureAt && errorAt > failureAt,
            "the emitted envelope carries the failure branch (FAILURE event, the "
                + "success-path state publication, and the error rethrow)");
        if (failureAt < 0 || successAt <= failureAt || errorAt <= failureAt) {
            return;
        }
        int publicationAt = artifact.indexOf("\"SUCCESS\", \"EXPORT_PUBLISH\"");
        check(publicationAt >= 0,
            "the emitted artifact carries the EXPORT_PUBLISH publication the envelope "
                + "would run on the success path");
        if (publicationAt < 0) {
            return;
        }
        int successLineStart = artifact.lastIndexOf('\n', successAt) + 1;
        int successLineEnd = artifact.indexOf('\n', successLineStart);
        String successLine = artifact.substring(successLineStart, successLineEnd);
        int publicationLineStart = artifact.lastIndexOf('\n', publicationAt) + 1;
        int publicationLineEnd = artifact.indexOf('\n', publicationLineStart);
        String publicationLine = artifact.substring(publicationLineStart,
            publicationLineEnd);
        // The injection targets the registry surface the artifact really
        // publishes through (the per-module export surface keyed by the
        // emitting module's identity), so the injected export is really
        // published and not a stray global.
        String surface = "__exportSurfaces[\"" + lowered.unit().moduleId().path()
            + "\"]";
        // The state-publication defect: the FAILURE path publishes the
        // INITIALIZED state (and an export entry) with a state SUCCESS event.
        String stateInjected = artifact.substring(0, errorAt)
            + successLine + "\n"
            + surface + "[\"__defect__\"] = true\n"
            + artifact.substring(errorAt);
        // The export-publication defect without any state event: the FAILURE
        // path publishes an export with its own EXPORT_PUBLISH trace event —
        // the state-event census alone cannot reject it, so the rule must
        // count the publication events in the artifact's trace.
        String exportInjected = artifact.substring(0, errorAt)
            + surface + "[\"__defect__\"] = {__kind = \"function\", "
            + "sig = \"():null\", f = function() return nil end}\n"
            + publicationLine + "\n"
            + artifact.substring(errorAt);
        List<String> real = runLuaArtifact(artifact, "module-init-failure-real.lua");
        List<String> stateInjectionRun = runLuaArtifact(stateInjected,
            "module-init-failure-state-injected.lua");
        List<String> exportInjectionRun = runLuaArtifact(exportInjected,
            "module-init-failure-export-injected.lua");
        FailurePathCensus realCensus = failurePathCensus(real);
        check(realCensus.ruleHolds(),
            "the real artifact passes the failure-path rule (one MODULE_INIT START, one "
                + "FAILURE, no SUCCESS, zero EXPORT_PUBLISH events — the failing init "
                + "publishes no export at all): " + realCensus);
        FailurePathCensus stateCensus = failurePathCensus(stateInjectionRun);
        check(!stateCensus.ruleHolds(),
            "the state-injected artifact fails the failure-path rule (never a "
                + "coincidental pass): the FAILURE path published the INITIALIZED state: "
                + stateCensus);
        FailurePathCensus exportCensus = failurePathCensus(exportInjectionRun);
        check(exportCensus.publications() >= 1,
            "the export-injected artifact publishes an EXPORT_PUBLISH event on the "
                + "FAILURE path (the injection is effective): " + exportCensus);
        check(exportCensus.starts() == 1 && exportCensus.failures() == 1
                && exportCensus.successes() == 0,
            "the export-injected artifact keeps the state-event shape (one START, one "
                + "FAILURE, no SUCCESS), so the rejection is caused by the published "
                + "export, never by a coincidental state event: " + exportCensus);
        check(!exportCensus.ruleHolds(),
            "the export-injected artifact fails the failure-path rule: an export "
                + "published on the FAILURE path is rejected even without a state "
                + "event: " + exportCensus);
    }

    /** The failure-path rule census over one artifact's protocol lines. */
    private record FailurePathCensus(int starts, int failures, int successes,
                                     int publications) {

        /** One START, one FAILURE, no SUCCESS, and zero export publications. */
        boolean ruleHolds() {
            return starts == 1 && failures == 1 && successes == 0 && publications == 0;
        }
    }

    /**
     * The module-init failure-path rule: one START, one FAILURE, no SUCCESS,
     * and zero EXPORT_PUBLISH events. The publication count rejects an
     * artifact that publishes an export on the FAILURE path without any
     * state event — the state-event census alone would pass such a defect.
     */
    private static FailurePathCensus failurePathCensus(List<String> protocolLines) {
        if (protocolLines == null) {
            return new FailurePathCensus(-1, -1, -1, -1);
        }
        int starts = 0;
        int failures = 0;
        int successes = 0;
        int publications = 0;
        for (String line : protocolLines) {
            if (line.isEmpty()) {
                continue;
            }
            Object decoded;
            try {
                decoded = deal.semantic.SemanticTraceProtocol.decode(line);
            } catch (RuntimeException exception) {
                continue;
            }
            if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                if (event.kind() == SemanticOpKind.EXPORT_PUBLISH) {
                    publications++;
                }
                if (event.kind() == SemanticOpKind.MODULE_INIT) {
                    switch (event.phase()) {
                        case START -> starts++;
                        case FAILURE -> failures++;
                        case SUCCESS -> successes++;
                    }
                }
            }
        }
        return new FailurePathCensus(starts, failures, successes, publications);
    }

    /** Writes one emitted Lua artifact and runs it under real luajit. */
    private static List<String> runLuaArtifact(String text, String name) {
        Path directory = WORKSPACE.resolve("negative");
        try {
            java.nio.file.Files.createDirectories(directory);
            Path script = directory.resolve(name);
            java.nio.file.Files.writeString(script, text,
                java.nio.charset.StandardCharsets.UTF_8);
            Path stdout = directory.resolve(name + ".out");
            Path stderr = directory.resolve(name + ".err");
            ProcessBuilder builder = new ProcessBuilder("luajit",
                script.toAbsolutePath().toString());
            builder.redirectOutput(stdout.toFile());
            builder.redirectError(stderr.toFile());
            Process process = builder.start();
            int exit = process.waitFor();
            List<String> lines = java.nio.file.Files.readAllLines(stderr,
                java.nio.charset.StandardCharsets.UTF_8);
            check(exit == 0, "the " + name + " artifact exits 0 (the trace-mode wrapper "
                + "publishes the failure terminal without changing the exit code); got "
                + exit + ": " + lines);
            return exit == 0 ? lines : null;
        } catch (java.io.IOException | InterruptedException exception) {
            check(false, "the " + name + " artifact run failed: " + exception.getMessage());
            return null;
        }
    }

    /** One copy of the unit with the given op replaced (the negative surfaces). */
    private static LoweredModuleUnit withOps(LoweredModuleUnit unit, OpId replaced,
                                             SemanticOp replacement) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op.opId().equals(replaced) ? replacement : op);
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Module Init Differential Test + Shared-Emitter Totality "
            + "Gate (ISSUE-0590) ===");
        System.out.println();
        testSuccessfulInit();
        testFailingInit();
        testHandBuiltUnitWithoutOp();
        testTotalityGate();
        testFeatureCorpus();
        testModuleImportEnvelopeSeed();
        testWrongParentNegative();
        testFailurePathPublicationNegative();
        System.out.println();
        System.out.println("ModuleInitDifferentialTest passed=" + passed + " failed="
            + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
