package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
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
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The runtime integration matrix of the {@code EVALUATION_ORDER}
 * decomposition tail (ISSUE-0410): every matrix seed is lowered through
 * the real production chain (lexer → parser → checker → checked project →
 * requirement manifest → the carrier's full-program lowerer → the closed
 * validator → the address-chain protocol → the control-flow validator)
 * and then executed on the semantic oracle and BOTH shared emitters'
 * real artifacts (the shared LuaJIT script run by the real {@code luajit}
 * binary; the shared JVM class compiled with the real
 * {@code javac --release 25 -proc:none} and executed by the real
 * {@code java}) via {@link SemanticDifferentialHarness} — the identical
 * validated {@link LoweredModuleUnit} plus its
 * {@link StructuredBodyTable} through all three consumers.
 *
 * <p>The verdict is a real execution comparison report: every event
 * validates against its exact IR operation (snapshot, digest,
 * {@code parentOpId} nesting), the three traces match event-for-event,
 * ordered effects match the wiki projections, and terminals (post-state
 * result and error origin) match — a duplicated evaluation, a wrong
 * selector, or a missing boundary fails the tail even when printed
 * output coincides.</p>
 */
public class RuntimeIntegrationMatrixTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Fixed invocation facts
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new deal.semantic.ir.ProjectInterfaceIndex(
        deal.semantic.ir.ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new deal.semantic.ir.ExternalModuleInterface(MODULE,
                deal.semantic.ir.ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(),
                List.of(), deal.semantic.ir.InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();
    private static final Path WORKSPACE = Path.of("build/runtime-matrix-work");

    // =========================================================================
    // Seed preludes (each seed declares exactly the helpers it calls)
    // =========================================================================

    private static final String CONSOLE = "import * as console from \"std/console\"\n";
    private static final String FN_MARK =
        "function mark(s: string, v: int): int { console.log(s); return v; }\n";
    private static final String FN_GETARR =
        "function getArr(s: string, xs: int[]): int[] { console.log(s); return xs; }\n";
    private static final String FN_BOOMINT =
        "function boomInt(s: string, z: int | null): int { console.log(s); "
            + "let x: int = int(z); return x; }\n";
    private static final String FN_BOOMARR =
        "function boomArr(s: string, z: int | null): int[] { console.log(s); "
            + "let x: int = int(z); return [x]; }\n";

    private static final String P_MARK = CONSOLE + FN_MARK;
    private static final String P_MARK_GET = CONSOLE + FN_MARK + FN_GETARR;
    private static final String P_MARK_GET_BOOMINT =
        CONSOLE + FN_MARK + FN_GETARR + FN_BOOMINT;
    private static final String P_BOOMARR = CONSOLE + FN_BOOMARR;

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        ModuleResolver resolver = new ModuleResolver() {
            @Override
            public Map<String, deal.types.Type> resolveModule(String modulePath,
                    String importingModule, java.util.Set<String> modulesInProgress)
                    throws ModuleNotFoundException {
                var exports = deal.module.StdlibModuleResolver.stdlibExports(
                    Path.of("std").toAbsolutePath().toString());
                if (!exports.containsKey(modulePath)) {
                    throw new ModuleNotFoundException("Module not found: " + modulePath);
                }
                return exports.get(modulePath);
            }

            @Override
            public deal.checker.Symbol.ClassSymbol resolveClassSymbol(String className,
                    String modulePath, String importingModule)
                    throws ModuleNotFoundException {
                return null;
            }
        };
        NameResolver nr = new NameResolver(SOURCE_ID, resolver);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": checks cleanly: " + result.diagnostics());
        if (!result.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    private static List<ResolvedImport> importsOf(ProgramNode program) {
        List<ResolvedImport> imports = new ArrayList<>();
        for (deal.ast.StatementNode stmt : program.statements()) {
            if (stmt instanceof deal.ast.ImportDeclaration imp) {
                // Production-faithful resolved ids (the checked-project
                // builder records the resolved target's dotted module id,
                // e.g. std/console → std.console, never the raw import
                // specifier): the closed StdlibFunctionCatalog keys on
                // the resolved dotted form.
                String resolved = switch (imp.modulePath()) {
                    case "std/console" -> "std.console";
                    case "std/string" -> "std.string";
                    case "std/table" -> "std.table";
                    case "std/json" -> "std.json";
                    case "std/math" -> "std.math";
                    case "std/time" -> "std.time";
                    default -> imp.modulePath();
                };
                imports.add(new ResolvedImport(imp.alias(), imp.modulePath(),
                    new ModuleId(resolved),
                    deal.semantic.ir.ExternalModuleKind.STDLIB));
            }
        }
        return imports;
    }

    private record LoweredSlice(LoweredModuleUnit unit, StructuredBodyTable table) {
    }

    /** The full production chain: checked project → manifests → carrier lowering. */
    private static LoweredSlice lowerFull(CheckedSlice slice, String what) {
        if (slice == null) {
            return null;
        }
        CheckedModuleInput input = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of("test.deal"), slice.program(), slice.checks(),
            importsOf(slice.program()), List.of(), CheckedModuleKind.IMPLEMENTATION);
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        ModuleFact fact = new ModuleFact(SOURCE_ID, MODULE, false, false, slice.program(),
            Map.of(), slice.symbols(), slice.checks(), List.of());
        deal.semantic.CheckedProjectBuildResult built = CheckedProjectBuilder.build(
            invocation, MODULE, List.of(fact));
        check(built != null && !built.hasErrors() && built.input() != null,
            what + ": the checked project builds cleanly");
        if (built == null || built.hasErrors() || built.input() == null) {
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty(),
            what + ": the manifest computation is clean");
        if (manifests == null || !manifests.diagnostics().isEmpty()) {
            return null;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            manifests.manifests().get(0).constructCoverage();
        SemanticLowerer.LoweringResult lowering = SemanticLowerer.lowerModuleFullProgram(
            input, SemanticProfile.DEAL_V1_2_INT32, coverage, INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
            what + ": the carrier lowers through the validator/chain protocol/"
                + "control-flow validator: " + (lowering == null ? "null"
                    : lowering.diagnostics()));
        if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
            return null;
        }
        return new LoweredSlice(lowering.unit(), lowering.table());
    }

    /**
     * Runs the three-consumer differential matrix for one seed and
     * asserts the pinned projection.
     */
    private static SemanticDifferentialHarness.Verdict runMatrix(String source, String what,
            List<String> expectedEffects,
            SemanticDifferentialHarness.TerminalExpectation terminal) {
        CheckedSlice slice = checkSlice(source, what);
        LoweredSlice lowered = lowerFull(slice, what);
        if (lowered == null) {
            return null;
        }
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            lowered.unit(), lowered.table(),
            new SemanticDifferentialHarness.Expectation(expectedEffects, terminal, what),
            WORKSPACE);
        check(verdict.pass(), what + ": the three-consumer matrix verdict passes:\n"
            + verdict.report());
        if (!verdict.pass()) {
            return verdict;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            check(!run.trace().isEmpty(), what + ": " + run.consumer()
                + " produced real events");
        }
        return verdict;
    }

    /**
     * Asserts every consumer's terminal failure message exactly (the
     * cross-consumer verdict compares the traces event-for-event; this pin
     * additionally fixes the closed projection text).
     */
    private static void checkTerminalMessage(SemanticDifferentialHarness.Verdict verdict,
            String message, String what) {
        if (verdict == null) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            String actual = run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                ? failure.error().message() : run.terminal().toString();
            check(message.equals(actual), what + ": " + run.consumer()
                + " publishes the exact failure message (got " + actual + ")");
        }
    }

    /**
     * Asserts every consumer's terminal failure expected/actual pair
     * exactly (the cross-consumer verdict compares the traces
     * event-for-event; this pin additionally fixes the closed projection
     * facts).
     */
    private static void checkTerminalExpectedActual(SemanticDifferentialHarness.Verdict verdict,
            String expected, String actual, String what) {
        if (verdict == null) {
            return;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            if (!(run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure failure)) {
                continue;
            }
            SemanticRuntimeModel.ErrorSnapshot error = failure.error();
            check(java.util.Objects.equals(error.expected(), expected)
                    && java.util.Objects.equals(error.actual(), actual),
                what + ": " + run.consumer()
                    + " publishes the exact expected/actual pair (got expected="
                    + error.expected() + " actual=" + error.actual() + ")");
        }
    }

    private static final SemanticDifferentialHarness.TerminalExpectation SUCCESS =
        new SemanticDifferentialHarness.TerminalExpectation.SuccessWith("null");
    private static final SemanticDifferentialHarness.TerminalExpectation E8001 =
        new SemanticDifferentialHarness.TerminalExpectation.FailureWith("E8001", null);
    private static final SemanticDifferentialHarness.TerminalExpectation E8002 =
        new SemanticDifferentialHarness.TerminalExpectation.FailureWith("E8002", null);

    // =========================================================================
    // 1. The chain matrix
    // =========================================================================

    static void testChainOrderMatrix() {
        System.out.println("-- Chain matrix: receiver/key/RHS order, normalize-time "
            + "length, VARIABLE boundary placement, append, publish --");

        // (a) receiver → key → RHS with console-marked functions.
        {
            String source = P_MARK_GET
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2, 3];\n"
                + "  getArr(\"arr\", xs)[mark(\"idx\", 0)] = mark(\"rhs\", 42);\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            SemanticDifferentialHarness.Verdict verdict = runMatrix(source,
                "chain order seed (arr/idx/rhs)",
                List.of("arr", "idx", "rhs", "done"), SUCCESS);
            // The retained double-evaluation detector: each CALL starts
            // exactly once in every consumer's trace.
            if (verdict != null) {
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    Map<String, Integer> starts = new java.util.HashMap<>();
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.kind() == SemanticOpKind.CALL
                                && event.phase() == SemanticRuntimeModel.Phase.START) {
                            starts.merge(event.op().toString(), 1, Integer::sum);
                        }
                    }
                    check(starts.values().stream().allMatch(count -> count == 1),
                        "chain order seed: every CALL starts exactly once in "
                            + run.consumer() + " (single evaluation): " + starts);
                }
            }
        }

        // (a2)/(a3) Hoisted-operand parity seeds reproducing the pinned
        // jvm-arr-eval-order-hoisted (index-side, index, value-side, value)
        // and jvm-arr-eval-order-write-hoisted-parity (a, b, i, c, v,
        // write-ok) outputs: an operand's nested side-effecting argument
        // completes before the operand call's own effect, with hoisted
        // operands — on the oracle AND both shared emitters.
        {
            String source = CONSOLE
                + "function pick(s: string, z: null): int { console.log(s); return 0; }\n"
                + "function main(): null {\n"
                + "  let xs: int[] = [5, 6];\n"
                + "  xs[pick(\"index\", console.log(\"index-side\"))] = "
                + "pick(\"value\", console.log(\"value-side\"));\n"
                + "  if (xs[0] === 0) { console.log(\"written\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "hoisted-operand parity "
                + "jvm-arr-eval-order-hoisted (index-side, index, value-side, value)",
                List.of("index-side", "index", "value-side", "value", "written"),
                SUCCESS);
        }
        {
            String source = CONSOLE
                + "function pick(s: string, z: null): int { console.log(s); return 0; }\n"
                + "function getArr(s: string, xs: int[]): int[] "
                + "{ console.log(s); return xs; }\n"
                + "function main(): null {\n"
                + "  let xs: int[] = [5, 6];\n"
                + "  getArr(\"a\", xs)[pick(\"i\", console.log(\"b\"))] = "
                + "pick(\"v\", console.log(\"c\"));\n"
                + "  if (xs[0] === 0) { console.log(\"write-ok\"); }\n"
                + "}\n";
            runMatrix(source, "hoisted-operand parity "
                + "jvm-arr-eval-order-write-hoisted-parity (a, b, i, c, v, write-ok)",
                List.of("a", "b", "i", "c", "v", "write-ok"), SUCCESS);
        }

        // (b) TABLE_SLOT member and index targets.
        {
            String source = P_MARK
                + "function main(): null {\n"
                + "  let t = {a: 1};\n"
                + "  t.a = mark(\"rhs\", 7);\n"
                + "  t[\"k\"] = mark(\"rhs2\", 8);\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "TABLE_SLOT member/index chains",
                List.of("rhs", "rhs2", "done"), SUCCESS);
        }

        // (c) The normalize-time length read.
        {
            String source = CONSOLE
                + "function grow(s: string, xs: int[]): int { console.log(s); "
                + "xs[xs.length] = 9; return 0; }\n"
                + "function rhs(s: string, v: int): int { console.log(s); return v; }\n"
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  xs[grow(\"idx\", xs)] = rhs(\"rhs\", 42);\n"
                + "  if (xs.length === 3 && xs[0] === 42 && xs[2] === 9) "
                + "{ console.log(\"normalize-time\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "normalize-time length read (length-mutating key)",
                List.of("idx", "rhs", "normalize-time"), SUCCESS);
        }

        // (d) VARIABLE boundary placement.
        {
            String source = CONSOLE
                + "function pick(s: string, v: int): int { console.log(s); return v; }\n"
                + "function main(): null {\n"
                + "  let x: int = 0;\n"
                + "  x = pick(\"val\", 42);\n"
                + "  if (x === 42) { console.log(\"stored\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "VARIABLE chain boundary placement",
                List.of("val", "stored"), SUCCESS);
        }

        // (e) The append idiom.
        {
            String source = P_MARK
                + "function main(): null {\n"
                + "  let xs: int[] = [1];\n"
                + "  xs[xs.length] = mark(\"rhs\", 42);\n"
                + "  if (xs.length === 2 && xs[1] === 42) { console.log(\"append\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "append idiom xs[xs.length] = v",
                List.of("rhs", "append"), SUCCESS);
        }

        // (f) ASSIGN publishes the committed value; DELETE publishes none.
        {
            String source = P_MARK
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2, 3];\n"
                + "  let y: int = (xs[0] = mark(\"rhs\", 42));\n"
                + "  if (y === 42) { console.log(\"published\") } else { console.log(\"bad\") }\n"
                + "  delete xs[2];\n"
                + "  console.log(\"deleted\");\n"
                + "}\n";
            runMatrix(source, "ASSIGN publishes the committed value; DELETE publishes none",
                List.of("rhs", "published", "deleted"), SUCCESS);
        }
    }

    // =========================================================================
    // 2. Chain failure matrix
    // =========================================================================

    static void testChainFailureMatrix() {
        System.out.println("-- Chain failure matrix: failure at every position, "
            + "no commit, earlier effects remain --");

        {
            String source = P_BOOMARR
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  boomArr(\"arr\", null)[0] = 42;\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "receiver failure (no commit; [arr] remains)",
                List.of("arr"), E8001);
        }
        {
            String source = P_MARK_GET_BOOMINT
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  getArr(\"arr\", xs)[boomInt(\"idx\", null)] = mark(\"rhs\", 42);\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "key failure (RHS never evaluates; no commit)",
                List.of("arr", "idx"), E8001);
        }
        {
            String source = P_MARK_GET_BOOMINT
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  getArr(\"arr\", xs)[mark(\"idx\", 0)] = boomInt(\"rhs\", null);\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "RHS failure (no commit; [arr, idx, rhs] remain)",
                List.of("arr", "idx", "rhs"), E8001);
        }
        {
            String source = P_MARK_GET
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  getArr(\"arr\", xs)[mark(\"idx\", -1)] = mark(\"rhs\", 42);\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "write bounds failure (E8002 at the write-target origin)",
                List.of("arr", "idx", "rhs"), E8002);
        }
        {
            String source = P_MARK_GET
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  let x: int = getArr(\"arr\", xs)[mark(\"idx\", -1)];\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "negative index read (E8002 negative array index)",
                List.of("arr", "idx"), E8002);
        }
        {
            String source = P_MARK_GET
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  delete getArr(\"arr\", xs)[mark(\"idx\", -1)];\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "array delete bounds failure (E8002 delete-target origin)",
                List.of("arr", "idx"), E8002);
        }
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  delete xs[2];\n"
                + "  if (xs.length === 2) { console.log(\"no-op-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "array delete at index == length (permitted no-op)",
                List.of("no-op-ok"), SUCCESS);
        }
    }

    // =========================================================================
    // 3. The comparison matrix
    // =========================================================================

    static void testComparisonMatrix() {
        System.out.println("-- Comparison matrix: the closed B-D2 rows through all "
            + "three consumers --");

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let n: number = 0.0 / 0.0;\n"
                + "  if (n === n) { console.log(\"nan-eq\") } else { console.log(\"nan-ne\") }\n"
                + "  let z: number = -0.0;\n"
                + "  let p: number = 0.0;\n"
                + "  if (z === p) { console.log(\"nz-eq\") } else { console.log(\"bad1\") }\n"
                + "  if (z < p) { console.log(\"bad2\") } else { console.log(\"nz-nolt\") }\n"
                + "  if (z <= p) { console.log(\"nz-le\") } else { console.log(\"bad3\") }\n"
                + "  if (n < 1.0) { console.log(\"bad4\") } else { console.log(\"nan-nolt\") }\n"
                + "  if (n >= 1.0) { console.log(\"bad5\") } else { console.log(\"nan-noge\") }\n"
                + "  if (1.5 < 2.5) { console.log(\"lt\") } else { console.log(\"bad6\") }\n"
                + "  if (2.5 > 1.5 && 1.5 <= 1.5 && 1.5 >= 1.5 && 1.5 !== 2.5) "
                + "{ console.log(\"num-ok\") } else { console.log(\"bad7\") }\n"
                + "}\n";
            runMatrix(source, "NUMBER_* IEEE rows (NaN, -0.0, orderings)",
                List.of("nan-ne", "nz-eq", "nz-nolt", "nz-le", "nan-nolt", "nan-noge",
                    "lt", "num-ok"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let s1: string = \"\uFFFF\";\n"
                + "  let s2: string = \"\uD800\uDC00\";\n"
                + "  if (s1 < s2) { console.log(\"codepoint-order\") } "
                + "else { console.log(\"bad\") }\n"
                + "  if (\"a\" === \"a\" && \"a\" !== \"b\") { console.log(\"str-eq\") } "
                + "else { console.log(\"bad2\") }\n"
                + "}\n";
            // U+FFFF vs U+10000 discriminates: code point order says
            // FFFF < 10000 (true -> codepoint-order), while the UTF-16
            // code-unit order used by String.compareTo says FFFF > D800
            // (false) — a shared-JVM realization using String.compareTo
            // fails this seed.
            runMatrix(source, "STRING_* scalar-lexicographic order (code point, "
                + "not UTF-16; the supplementary pair discriminates "
                + "String.compareTo)", List.of("codepoint-order", "str-eq"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  if (1 === 1 && 1 !== 2 && 1 < 2 && 2 > 1 && 1 <= 1 && 2 >= 1) "
                + "{ console.log(\"int-ok\") } else { console.log(\"bad\") }\n"
                + "  if (true === true && false !== true) { console.log(\"bool-ok\") } "
                + "else { console.log(\"bad2\") }\n"
                + "  let m: null = null;\n"
                + "  if (m === m && !(m !== m)) { console.log(\"null-ok\") } "
                + "else { console.log(\"bad3\") }\n"
                + "}\n";
            runMatrix(source, "INT32_*/BOOLEAN_*/NULL_* rows",
                List.of("int-ok", "bool-ok", "null-ok"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let a: int | null = null;\n"
                + "  let b: int | null = null;\n"
                + "  let c: int | null = 3;\n"
                + "  let d: int | null = 3;\n"
                + "  if (a === b) { console.log(\"null-null\") } else { console.log(\"bad\") }\n"
                + "  if (a !== c) { console.log(\"null-val-ne\") } else { console.log(\"bad2\") }\n"
                + "  if (c === d) { console.log(\"val-val\") } else { console.log(\"bad3\") }\n"
                + "  if (a === null) { console.log(\"n-null-eq\") } else { console.log(\"bad4\") }\n"
                + "  if (null === a) { console.log(\"null-n-eq\") } else { console.log(\"bad5\") }\n"
                + "  if (c !== null) { console.log(\"v-null-ne\") } else { console.log(\"bad6\") }\n"
                + "  if (null !== c) { console.log(\"null-v-ne\") } else { console.log(\"bad7\") }\n"
                + "}\n";
            runMatrix(source, "NULLABLE_* sides and NULLABLE_NULL_* directions",
                List.of("null-null", "null-val-ne", "val-val", "n-null-eq", "null-n-eq",
                    "v-null-ne", "null-v-ne"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  let ys: int[] = [1, 2];\n"
                + "  let t = {a: 1};\n"
                + "  let u = {a: 1};\n"
                + "  if (xs === xs) { console.log(\"same-arr\") } else { console.log(\"bad\") }\n"
                + "  if (xs !== ys) { console.log(\"distinct-arr\") } else { console.log(\"bad2\") }\n"
                + "  if (t === t) { console.log(\"same-table\") } else { console.log(\"bad3\") }\n"
                + "  if (t !== u) { console.log(\"distinct-table\") } else { console.log(\"bad4\") }\n"
                + "}\n";
            runMatrix(source, "REFERENCE_* identity (array/table)",
                List.of("same-arr", "distinct-arr", "same-table", "distinct-table"),
                SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let xs: int[] = [1];\n"
                + "  if (xs[99] === 5) { console.log(\"bad\") } else { console.log(\"ne\") }\n"
                + "  if (xs[99] !== 5) { console.log(\"neq\") } else { console.log(\"bad2\") }\n"
                + "  if (xs[99] === xs[99]) { console.log(\"nil-eq-nil\") } "
                + "else { console.log(\"bad3\") }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "missing≡null past-end comparison operands (no E8001)",
                List.of("ne", "neq", "nil-eq-nil", "done"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function left(): int { console.log(\"l\"); return 1; }\n"
                + "function right(): int { console.log(\"r\"); return 2; }\n"
                + "function main(): null {\n"
                + "  if (left() === right()) { console.log(\"bad\") } "
                + "else { console.log(\"ordered\") }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "comparison operands left-to-right exactly once",
                List.of("l", "r", "ordered", "done"), SUCCESS);
        }
    }

    // =========================================================================
    // 4. The control matrix
    // =========================================================================

    static void testControlMatrix() {
        System.out.println("-- Control matrix: short circuit, loops, FOR_EACH, "
            + "TRY_CATCH/THROW, BREAK/CONTINUE, DISCARD --");

        {
            String source = CONSOLE
                + "function side(): boolean { console.log(\"side\"); return true; }\n"
                + "function yes(): boolean { console.log(\"yes\"); return true; }\n"
                + "function no(): boolean { console.log(\"no\"); return false; }\n"
                + "function main(): null {\n"
                + "  if (no() && side()) { console.log(\"bad\") } "
                + "else { console.log(\"and-skip\") }\n"
                + "  if (yes() || side()) { console.log(\"or-skip\") } "
                + "else { console.log(\"bad2\") }\n"
                + "  if (yes() && yes()) { console.log(\"and-run\") } "
                + "else { console.log(\"bad3\") }\n"
                + "  if (no() || yes()) { console.log(\"or-run\") } "
                + "else { console.log(\"bad4\") }\n"
                + "}\n";
            runMatrix(source, "short circuit (skipped blocks leave no effects)",
                List.of("no", "and-skip", "yes", "or-skip", "yes", "yes", "and-run",
                    "no", "yes", "or-run"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function count(): boolean { console.log(\"c\"); return true; }\n"
                + "function dec(x: int): int { console.log(\"d\"); return x - 1; }\n"
                + "function main(): null {\n"
                + "  let i: int = 2;\n"
                + "  while (count() && i > 0) { i = dec(i); }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "while per-iteration condition re-evaluation",
                List.of("c", "d", "c", "d", "c", "done"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  for (let i: int = 0; i < 5; i = i + 1) {\n"
                + "    if (i === 1) { continue }\n"
                + "    if (i === 3) { break }\n"
                + "    console.log(\"b\");\n"
                + "  }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "FOR init/test/body/update with continue-to-update "
                + "and break", List.of("b", "b", "done"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let n: int = 0;\n"
                + "  for (;;) {\n"
                + "    n = n + 1;\n"
                + "    if (n === 3) { break }\n"
                + "  }\n"
                + "  if (n === 3) { console.log(\"testless-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source, "test-less for");
            LoweredSlice lowered = lowerFull(slice, "test-less for");
            if (lowered != null) {
                boolean shape = ofKind(lowered.unit(), SemanticOpKind.LOOP).stream()
                    .anyMatch(op -> {
                        KindPayload.LoopPayload payload =
                            (KindPayload.LoopPayload) op.payload();
                        SemanticOp producer = producerOf(lowered.unit(),
                            payload.condition());
                        return producer != null && producer.kind() == SemanticOpKind.CONST
                            && producer.origin().kind()
                                == deal.semantic.ir.SourceOriginKind.SYNTHETIC
                            && lowered.table().blockOps()
                                .getOrDefault(payload.initBlock(), List.of())
                                .contains(producer.opId());
                    });
                check(shape, "test-less for: the CONST true condition production "
                    + "lives once in initBlock");
            }
            runMatrix(source, "test-less for (;;) shape",
                List.of("testless-ok"), SUCCESS);
        }

        {
            String source = CONSOLE
                + "function mk(s: string): int[] { console.log(s); return [10, 20]; }\n"
                + "function main(): null {\n"
                + "  for (let e: int of mk(\"iter\")) {\n"
                + "    if (e === 10) { console.log(\"first\") } else { console.log(\"other\") }\n"
                + "  }\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  for (let e: int of xs) {\n"
                + "    if (e === 1) { xs[xs.length] = 99; }\n"
                + "    console.log(\"v\");\n"
                + "  }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            runMatrix(source, "FOR_EACH iterable-once, 0-based first visit, "
                + "snapshot range", List.of("iter", "first", "other", "v", "v", "done"),
                SUCCESS);
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let xs: (int|null)[] = [];\n"
                + "  xs[0] = null;\n"
                + "  xs[1] = 1;\n"
                + "  for (let e: int|null of xs) {\n"
                + "    if (e === null) { console.log(\"nil\") } "
                + "else { console.log(\"int\") }\n"
                + "  }\n"
                + "  console.log(\"done\");\n"
                + "}\n";
            // A present null element passes the nullable element descriptor
            // (effects nil, int, done); conflating it with missing raises
            // E8001 "expected nullable(int), got missing" — the parity
            // break the emitters must never reproduce.
            runMatrix(source, "FOR_EACH(ARRAY_VALUES) preserves a present null "
                + "element (null never conflated with missing)",
                List.of("nil", "int", "done"), SUCCESS);
        }
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2];\n"
                + "  for (let e: int of xs) {\n"
                + "    if (e === 1) { delete xs[1]; }\n"
                + "    console.log(\"v\");\n"
                + "  }\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "FOR_EACH shrink (missing element E8001 at the "
                + "FOR_EACH origin)", List.of("v"), E8001);
        }

        {
            String source = CONSOLE
                + "function boom(z: int | null): int { return int(z); }\n"
                + "function main(): null {\n"
                + "  try { let x: int = boom(null); console.log(\"bad\"); } "
                + "catch (e) { console.log(\"caught\"); }\n"
                + "  try { console.log(\"ok\"); } catch (e) { console.log(\"bad2\"); }\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "TRY_CATCH catch-on-failure / skip-on-success",
                List.of("caught", "ok", "after"), SUCCESS);
        }
        {
            String source = CONSOLE
                + "function rethrow(): null { try { let z: int | null = null; "
                + "let x: int = int(z); } catch (e) { throw e; } }\n"
                + "function main(): null { rethrow(); console.log(\"after\"); }\n";
            SemanticDifferentialHarness.Verdict verdict = runMatrix(source,
                "catch re-throw (own THROW origin with cause = the original)",
                List.of(), E8001);
            if (verdict != null) {
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal() instanceof
                        SemanticRuntimeModel.Terminal.DealFailure failure
                        && failure.error().cause() != null
                        && "E8001".equals(failure.error().cause().code()),
                        "catch re-throw: " + run.consumer()
                            + " carries cause = the original E8001 snapshot");
                }
            }
        }

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  while (true) {\n"
                + "    try { console.log(\"t\"); break; } catch (e) { console.log(\"bad\"); }\n"
                + "  }\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "break across a try boundary",
                List.of("t", "after"), SUCCESS);
        }

        {
            String source = P_MARK
                + "function main(): null {\n"
                + "  mark(\"d\", 1);\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source, "discard");
            LoweredSlice lowered = lowerFull(slice, "discard");
            if (lowered != null) {
                check(ofKind(lowered.unit(), SemanticOpKind.DISCARD).stream()
                    .anyMatch(op -> op.origin().kind()
                        == deal.semantic.ir.SourceOriginKind.SYNTHETIC),
                    "discard: the expression statement lowers to an audited DISCARD");
            }
            runMatrix(source, "DISCARD audit", List.of("d", "after"), SUCCESS);
        }
    }

    // =========================================================================
    // 5. The CONTAINERS_AND_STRINGS extras matrix (the step-1 cutover):
    //    OPTIONAL_READ pre-map seeds and HAS_FIELD presence units
    // =========================================================================

    static void testContainerExtrasMatrix() {
        System.out.println("-- Container extras matrix: OPTIONAL_READ present/missing/"
            + "present-null/wrong-kind, HAS_FIELD presence --");

        // (a) Present: the missing-capable read of a present key lowers
        // to MEMBER_READ(INTERNAL_MISSING) + OPTIONAL_READ + the
        // CONTEXTUAL_TABLE_READ boundary child, and the present value
        // passes the optional-read validation unchanged.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: table = { a: 1 };\n"
                + "  let x: int | null = t.a;\n"
                + "  if (x === null) { console.log(\"bad\") } "
                + "else { console.log(\"present\") }\n"
                + "}\n";
            runMatrix(source, "OPTIONAL_READ present key (value passes)",
                List.of("present"), SUCCESS);
        }

        // (b) Missing: an absent key pre-maps to language null before
        // the boundary validates — never the E8001 missing projection.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: table = { a: 1 };\n"
                + "  let y: int | null = t.b;\n"
                + "  if (y === null) { console.log(\"nil\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "OPTIONAL_READ missing key (missing → null before "
                + "validation)", List.of("nil"), SUCCESS);
        }

        // (c) Present null stays present null: a stored null passes the
        // nullable descriptor and never conflates with the internal
        // missing against the inner descriptor.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: table = { n: null };\n"
                + "  let w: int | null = t.n;\n"
                + "  if (w === null) { console.log(\"nil\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "OPTIONAL_READ present null (null never conflated "
                + "with missing)", List.of("nil"), SUCCESS);
        }

        // (d) A present wrong-kind value fails the optional-read present
        // branch: the CONTEXTUAL_TABLE_READ child projects the pinned
        // E8001 at the boundary origin (the differential verdict pins
        // the event-for-event failure shape on all three consumers).
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: table = { a: \"s\" };\n"
                + "  let x: int | null = t.a;\n"
                + "  console.log(\"after\");\n"
                + "}\n";
            runMatrix(source, "OPTIONAL_READ present wrong kind (E8001 at the "
                + "boundary origin)", List.of(), E8001);
        }
    }

    static void testHasFieldPresenceMatrix() {
        System.out.println("-- HAS_FIELD presence matrix: present int / present null / "
            + "absent keys through the three consumers --");

        ValueId one = nextValue();
        ValueId nul = nextValue();
        ValueId table = nextValue();
        ValueId hasA = nextValue();
        ValueId hasN = nextValue();
        ValueId hasM = nextValue();
        List<SemanticOp> ops = List.of(
            syntheticOp(SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                one, RuntimeDescriptor.Int.INSTANCE),
            syntheticOp(SemanticOpKind.CONST,
                new KindPayload.ConstPayload(ScalarValue.Null.INSTANCE),
                nul, RuntimeDescriptor.Null.INSTANCE),
            syntheticOp(SemanticOpKind.TABLE_NEW,
                new KindPayload.TableNewPayload(List.of(
                    new KindPayload.TableEntry("a", one),
                    new KindPayload.TableEntry("n", nul))),
                table, RuntimeDescriptor.Table.INSTANCE),
            syntheticOp(SemanticOpKind.HAS_FIELD,
                new KindPayload.HasFieldPayload(table, "a"),
                hasA, RuntimeDescriptor.Boolean.INSTANCE),
            syntheticOp(SemanticOpKind.HAS_FIELD,
                new KindPayload.HasFieldPayload(table, "n"),
                hasN, RuntimeDescriptor.Boolean.INSTANCE),
            syntheticOp(SemanticOpKind.HAS_FIELD,
                new KindPayload.HasFieldPayload(table, "m"),
                hasM, RuntimeDescriptor.Boolean.INSTANCE));
        LoweredModuleUnit unit = syntheticUnit(ops);
        StructuredBodyTable bodyTable = syntheticTable(ops);
        var validation = SemanticIrValidator.validate(unit,
            new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
        check(validation.isEmpty(),
            "the HAS_FIELD presence unit is valid IR: " + validation);
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            unit, bodyTable, new SemanticDifferentialHarness.Expectation(List.of(),
                SUCCESS, "HAS_FIELD presence (present int, present null, absent)"),
            WORKSPACE);
        check(verdict.pass(),
            "the HAS_FIELD presence unit passes the three-consumer matrix:\n"
                + verdict.report());

        // The present=false OPTIONAL_READ payload shape (a statically
        // absent slot): language null, no boundary child — the second
        // closed payload arm.
        ValueId absent = nextValue();
        LoweredModuleUnit absentUnit = syntheticUnit(List.of(
            syntheticOp(SemanticOpKind.OPTIONAL_READ,
                new KindPayload.OptionalReadPayload(null, false,
                    RuntimeDescriptor.Int.INSTANCE),
                absent, nullableInt())));
        StructuredBodyTable absentTable = syntheticTable(absentUnit.ops());
        var absentValidation = SemanticIrValidator.validate(absentUnit,
            new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
        check(absentValidation.isEmpty(),
            "the present=false OPTIONAL_READ unit is valid IR: " + absentValidation);
        SemanticDifferentialHarness.Verdict absentVerdict = SemanticDifferentialHarness.run(
            absentUnit, absentTable, new SemanticDifferentialHarness.Expectation(List.of(),
                SUCCESS, "OPTIONAL_READ present=false (statically absent slot → null)"),
            WORKSPACE);
        check(absentVerdict.pass(),
            "the present=false OPTIONAL_READ unit passes the three-consumer "
                + "matrix:\n" + absentVerdict.report());
    }

    // =========================================================================
    // 5b. The BINDINGS family matrix (the step-5 emission):
    //     RECURSIVE_GROUP_INIT through the group-core lowering path
    //     (RecursiveGroupLoweringTest's real reachable IR) on all three
    //     consumers — atomic publication, fresh identities, one factory
    //     invocation per member per execution, and the nested-scope
    //     emission shape
    // =========================================================================

    /**
     * The group-core lowering path (ISSUE-0446's production surface):
     * the identical validated unit the
     * {@code RecursiveGroupLoweringTest} path produces — the
     * {@code RECURSIVE_GROUP_INIT} op appears in the validated unit,
     * never invented by the seeds (anti-hollow: the harness compares
     * the three consumers' traces over this real IR, not source
     * presence).
     */
    private static SemanticLowerer.GroupCoreResult lowerGroupCore(CheckedSlice slice,
                                                                  String what) {
        if (slice == null) {
            return null;
        }
        CheckedModuleInput input = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of("test.deal"), slice.program(), slice.checks(),
            importsOf(slice.program()), List.of(), CheckedModuleKind.IMPLEMENTATION);
        SemanticLowerer.GroupCoreResult result = SemanticLowerer.lowerModuleGroupCore(
            input, SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + ": the group-core path lowers a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    /** Runs the group-core seed through the three-consumer matrix. */
    private static SemanticDifferentialHarness.Verdict runGroupMatrix(
            String source, String what) {
        CheckedSlice slice = checkSlice(source, what);
        SemanticLowerer.GroupCoreResult result = lowerGroupCore(slice, what);
        if (result == null) {
            return null;
        }
        SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
            result.lowering().unit(), result.lowering().table(),
            new SemanticDifferentialHarness.Expectation(List.of(), SUCCESS, what),
            WORKSPACE);
        check(verdict.pass(), what + ": the three-consumer matrix verdict passes:\n"
            + verdict.report());
        if (!verdict.pass()) {
            return verdict;
        }
        for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
            check(!run.trace().isEmpty(), what + ": " + run.consumer()
                + " produced real events");
        }
        return verdict;
    }

    /**
     * The atomic-publication pin: for every group op, each consumer's
     * SUCCESS event directly follows the op's START (the publication
     * sequence emits zero interleaved events), and every executed
     * member-load event follows the group op's SUCCESS — a partial
     * publisher interleaving a member observation mid-publication (the
     * partial-publication defect) breaks this adjacency, and the
     * three-way trace comparison then names the first mismatch class.
     */
    private static void pinAtomicPublication(LoweredModuleUnit unit,
            SemanticDifferentialHarness.Verdict verdict, String what) {
        List<SemanticOp> groups = ofKind(unit, SemanticOpKind.RECURSIVE_GROUP_INIT);
        check(!groups.isEmpty(), what + ": the unit carries at least one "
            + "RECURSIVE_GROUP_INIT op (real reachable IR)");
        for (SemanticOp group : groups) {
            for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                List<SemanticRuntimeModel.TraceEvent> events = run.trace();
                int start = -1;
                int success = -1;
                for (int i = 0; i < events.size(); i++) {
                    SemanticRuntimeModel.TraceEvent event = events.get(i);
                    if (!event.op().equals(group.opId())) {
                        continue;
                    }
                    if (event.phase() == SemanticRuntimeModel.Phase.START) {
                        start = i;
                    } else if (event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                        success = i;
                    }
                }
                check(start >= 0, what + ": " + run.consumer() + " starts the group "
                    + group.opId());
                check(success == start + 1, what + ": " + run.consumer()
                    + " publishes the group " + group.opId() + " atomically "
                    + "(SUCCESS directly follows START at index " + start
                    + "/" + success + " — no interleaved member observation)");
                for (int i = 0; i < events.size(); i++) {
                    SemanticRuntimeModel.TraceEvent event = events.get(i);
                    if (event.kind() == SemanticOpKind.BINDING_LOAD
                            && isMemberLoadOf(unit, group, event.op())
                            && i < success) {
                        fail(what + ": " + run.consumer() + " executes member load "
                            + event.op() + " before the group " + group.opId()
                            + " completes (partial publication)");
                    }
                }
            }
        }
    }

    /** True iff the event's op is a generation-0 load of one group member binding. */
    private static boolean isMemberLoadOf(LoweredModuleUnit unit, SemanticOp group,
                                          OpId eventOp) {
        SemanticOp op = opById(unit, eventOp);
        if (op == null || op.kind() != SemanticOpKind.BINDING_LOAD) {
            return false;
        }
        KindPayload.RecursiveGroupInitPayload payload =
            (KindPayload.RecursiveGroupInitPayload) group.payload();
        KindPayload.BindingLoadPayload load = (KindPayload.BindingLoadPayload) op.payload();
        return load.generation() == 0 && payload.bindings().contains(load.binding());
    }

    static void testRecursiveGroupMatrix() {
        System.out.println("-- Recursive group matrix: atomic publication, fresh "
            + "identities, one factory invocation per member per execution, "
            + "nested-scope emission --");

        // (a) The canonical mutual pair: sibling loads inside the member
        // bodies, module-level loads after the group op — the
        // publication-completeness seed (a member reading a group
        // binding must observe the published sibling, never a partial
        // group; the atomic-publication pin asserts the group's events
        // carry zero interleaved observations).
        {
            String source = """
                function f(): null {
                  let gRef: () => null = g;
                  let selfRef: () => null = f;
                }
                function g(): null {
                  let fRef: () => null = f;
                }
                let fTop: () => null = f;
                let gTop: () => null = g;
                """;
            CheckedSlice slice = checkSlice(source, "group (a) mutual pair");
            SemanticLowerer.GroupCoreResult result =
                lowerGroupCore(slice, "group (a) mutual pair");
            if (result == null) {
                return;
            }
            SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
                result.lowering().unit(), result.lowering().table(),
                new SemanticDifferentialHarness.Expectation(List.of(), SUCCESS,
                    "group (a) mutual pair — atomic publication and member "
                        + "loads after publication"),
                WORKSPACE);
            check(verdict.pass(),
                "group (a): the three-consumer matrix verdict passes:\n"
                    + verdict.report());
            if (verdict.pass()) {
                pinAtomicPublication(result.lowering().unit(), verdict,
                    "group (a)");
            }
        }

        // (b) The fresh-identity and single-factory pins: two groups plus
        // two loads of the same member — the two loads publish the
        // identical ref atom (exactly one factory invocation per member
        // per execution; a re-evaluating factory would publish a second
        // distinct identity and the three-way trace comparison would
        // name the first mismatch class), while a different group's
        // member publishes a distinct ref (fresh identities per group).
        {
            String source = """
                function f(): null {
                  let gRef: () => null = g;
                }
                function g(): null {
                  let fRef: () => null = f;
                }
                function h(): null {
                  let iRef: () => null = i;
                }
                function i(): null {
                  let hRef: () => null = h;
                }
                let a: () => null = f;
                let b: () => null = f;
                let c: () => null = h;
                """;
            CheckedSlice slice = checkSlice(source,
                "group (b) fresh identities / single factory");
            SemanticLowerer.GroupCoreResult result =
                lowerGroupCore(slice, "group (b) fresh identities / single factory");
            if (result == null) {
                return;
            }
            SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
                result.lowering().unit(), result.lowering().table(),
                new SemanticDifferentialHarness.Expectation(List.of(), SUCCESS,
                    "group (b) fresh identities / single factory per member"),
                WORKSPACE);
            check(verdict.pass(),
                "group (b): the three-consumer matrix verdict passes:\n"
                    + verdict.report());
            if (verdict.pass()) {
                pinAtomicPublication(result.lowering().unit(), verdict,
                    "group (b)");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    List<String> functionLoadAtoms = new ArrayList<>();
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.kind() == SemanticOpKind.BINDING_LOAD
                                && event.phase() == SemanticRuntimeModel.Phase.SUCCESS
                                && event.output() != null
                                && event.output().startsWith("ref:")) {
                            functionLoadAtoms.add(event.output());
                        }
                    }
                    check(functionLoadAtoms.size() == 3
                            && functionLoadAtoms.get(0).equals(functionLoadAtoms.get(1))
                            && !functionLoadAtoms.get(1).equals(functionLoadAtoms.get(2)),
                        "group (b): " + run.consumer() + " publishes one identity "
                            + "per member per execution (the two f-loads agree at "
                            + functionLoadAtoms.get(0) + "; the h-load is a fresh "
                            + "distinct identity) — a re-evaluated factory breaks "
                            + "the load-atom equality: " + functionLoadAtoms);
                }
            }
        }

        // (c) A non-member capture: the member factory receives the
        // capturing cell among its arguments (the enclosing body's
        // parameter cell and the sibling SHARED_CELLs) — the emission
        // shape compiles and runs on both real toolchains. (A
        // module-level let read inside a member body is a module-member
        // construct of the E9/E10 window, outside the group-core walk;
        // the parameter capture pins the non-member capture-cell arm
        // instead.)
        {
            String source = """
                function outer(x: int): null {
                  function f(): null {
                    let xRef: int = x;
                    let gRef: () => null = g;
                  }
                  function g(): null {
                    let fRef: () => null = f;
                  }
                  let gTop: () => null = g;
                }
                """;
            runGroupMatrix(source, "group (c) non-member capture cells "
                + "(enclosing parameter cell)");
        }

        // (d) A closure group side by side: a self-recursive closure
        // (size-1 SCC → CLOSURE_NEW) next to the mutual group — both
        // producing allocations execute in one unit.
        {
            String source = """
                function f(): null {
                  let gRef: () => null = g;
                  let selfRef: () => null = f;
                }
                function g(): null {
                  let fRef: () => null = f;
                }
                function self(): null {
                  let me: () => null = self;
                }
                let fTop: () => null = f;
                let selfTop: () => null = self;
                """;
            runGroupMatrix(source, "group (d) closure + group producing "
                + "allocations in one unit");
        }

        // (e) The nested-scope group: the op sits at the first member's
        // declaration position inside the enclosing function's body —
        // the emitters realize the arm inside the factory body, and the
        // artifacts still compile and run under the real toolchains
        // (the group never executes because the enclosing body never
        // runs in the group-core window — an emission-shape seed).
        {
            String source = """
                function outer(): null {
                  let before: int = 1;
                  function f(): null {
                    let gRef: () => null = g;
                  }
                  function g(): null {
                    let fRef: () => null = f;
                  }
                  let after: int = 2;
                }
                """;
            CheckedSlice slice = checkSlice(source, "group (e) nested-scope group");
            SemanticLowerer.GroupCoreResult result =
                lowerGroupCore(slice, "group (e) nested-scope group");
            if (result == null) {
                return;
            }
            SemanticDifferentialHarness.Verdict verdict = SemanticDifferentialHarness.run(
                result.lowering().unit(), result.lowering().table(),
                new SemanticDifferentialHarness.Expectation(List.of(), SUCCESS,
                    "group (e) nested-scope group emission inside the factory body"),
                WORKSPACE);
            check(verdict.pass(),
                "group (e): the three-consumer matrix verdict passes (the "
                    + "nested-group arm compiles and runs in both real artifacts):\n"
                    + verdict.report());
        }
    }

    static void testRecursiveGroupProductionEmission() {
        System.out.println("-- RECURSIVE_GROUP_INIT production emission --");

        // Production-mode realization (no trace-only arm): the same
        // group unit emitted through the production surfaces runs under
        // the real toolchains with the retained production terminal
        // (silent success, exit 0 — the publication code is emitted
        // identically in both modes).
        {
            String source = """
                function f(): null {
                  let gRef: () => null = g;
                  let selfRef: () => null = f;
                }
                function g(): null {
                  let fRef: () => null = f;
                }
                let fTop: () => null = f;
                let gTop: () => null = g;
                """;
            CheckedSlice slice = checkSlice(source,
                "production-mode group emission");
            SemanticLowerer.GroupCoreResult result =
                lowerGroupCore(slice, "production-mode group emission");
            if (result == null) {
                return;
            }
            try {
                String lua = deal.codegen.lua.LuaSemanticEmitter
                    .emitProductionModule(result.lowering().unit(),
                        result.lowering().table(), true);
                Path script = WORKSPACE.resolve("group-prod.lua");
                Files.writeString(script, lua);
                Process luaRun = new ProcessBuilder("luajit",
                    script.toAbsolutePath().toString())
                    .redirectErrorStream(true).start();
                String luaOutput = new String(luaRun.getInputStream().readAllBytes());
                int luaExit = luaRun.waitFor();
                check(luaExit == 0 && luaOutput.isEmpty(),
                    "the production shared-LuaJIT group artifact runs with the "
                        + "retained silent production terminal (exit " + luaExit
                        + ", output " + luaOutput.trim() + ")");

                deal.codegen.jvm.JvmSemanticEmitter.EmissionResult emission =
                    deal.codegen.jvm.JvmSemanticEmitter.emitProductionModule(
                        result.lowering().unit(), result.lowering().table(), true,
                        "GroupProdMain");
                Path sourceFile = WORKSPACE.resolve("GroupProdMain.java");
                Files.writeString(sourceFile, emission.source());
                Path classes = WORKSPACE.resolve("group-prod-classes");
                Files.createDirectories(classes);
                String classpath = System.getProperty("java.class.path", "");
                Process compile = new ProcessBuilder("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    sourceFile.toAbsolutePath().toString())
                    .redirectErrorStream(true).start();
                String compileOutput = new String(
                    compile.getInputStream().readAllBytes());
                int compileExit = compile.waitFor();
                check(compileExit == 0, "the production shared-JVM group artifact "
                    + "compiles (exit " + compileExit + ": " + compileOutput.trim()
                    + ")");
                if (compileExit == 0) {
                    Process javaRun = new ProcessBuilder("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes,
                        "GroupProdMain").redirectErrorStream(true).start();
                    String javaOutput = new String(
                        javaRun.getInputStream().readAllBytes());
                    int javaExit = javaRun.waitFor();
                    check(javaExit == 0 && javaOutput.isEmpty(),
                        "the production shared-JVM group artifact runs with the "
                            + "retained silent production terminal (exit " + javaExit
                            + ", output " + javaOutput.trim() + ")");
                }
            } catch (java.io.IOException | InterruptedException exception) {
                fail("production-mode group emission: infrastructure failure: "
                    + exception.getMessage());
            }
        }
    }

    // =========================================================================
    // 6. Pinned IR facts
    // =========================================================================

    static void testPinnedIrFacts() {
        System.out.println("-- Pinned IR facts: wrong selector / missing boundary / "
            + "moved child negatives --");

        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let n: number = 0.0 / 0.0;\n"
                + "  if (n === n) { console.log(\"bad\") } else { console.log(\"ne\") }\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source, "selector pinning");
            LoweredSlice lowered = lowerFull(slice, "selector pinning");
            if (lowered != null) {
                boolean pinned = ofKind(lowered.unit(), SemanticOpKind.BINARY).stream()
                    .anyMatch(op -> ((KindPayload.BinaryPayload) op.payload()).selector()
                        == BinarySelector.NUMBER_EQ);
                check(pinned, "the NaN equality lowers to the pinned NUMBER_EQ "
                    + "selector");
            }
        }

    }

    // =========================================================================
    // 7. The stdlib matrix (ISSUE-0585): the closed STDLIB_CALL
    //    realization — cataloged calls and failure projections through
    //    the semantic oracle and both shared emitters' real artifacts
    // =========================================================================

    private static final String STR = "import * as str from \"std/string\"\n";
    private static final String TBL = "import * as tbl from \"std/table\"\n";
    private static final String JSON = "import * as json from \"std/json\"\n";
    private static final String MATH = "import * as math from \"std/math\"\n";

    static void testStdlibMatrix() {
        System.out.println("-- Stdlib matrix: the closed STDLIB_CALL realization — "
            + "string/table/json/math families, failure projections --");

        // (a) STRING_LENGTH: the Unicode scalar count (a surrogate pair
        // is one scalar) — 5 and 3 scalars, never the UTF-8 byte counts.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let n: int = str.length(\"aé中😀b\")\n"
                + "  let m: int = str.length(\"a😀b\")\n"
                + "  let z: int = str.length(\"\")\n"
                + "  if (n === 5 && m === 3 && z === 0) { console.log(\"len-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_LENGTH scalar counts (astral + empty)",
                List.of("len-ok"), SUCCESS);
        }

        // (b) STRING_SUBSTRING: scalar indices with the closed clamping.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let a: string = str.substring(\"abcdef\", 1, 4)\n"
                + "  let b: string = str.substring(\"abc\", -5, 99)\n"
                + "  let c: string = str.substring(\"abc\", 2, 2)\n"
                + "  let d: string = str.substring(\"a😀b\", 1, 2)\n"
                + "  if (a === \"bcd\" && b === \"abc\" && c === \"\" "
                + "&& d === \"😀\") { console.log(\"sub-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_SUBSTRING scalar slice + clamping",
                List.of("sub-ok"), SUCCESS);
        }

        // (c) The search family: contains/startsWith/endsWith — literal
        // scalar subsequences, an empty part contained/prefix/suffix.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let c1: boolean = str.contains(\"hello\", \"ell\")\n"
                + "  let c2: boolean = str.contains(\"hello\", \"\")\n"
                + "  let c3: boolean = str.contains(\"hello\", \"x\")\n"
                + "  let s1: boolean = str.startsWith(\"hello\", \"he\")\n"
                + "  let s2: boolean = str.startsWith(\"hello\", \"\")\n"
                + "  let e1: boolean = str.endsWith(\"hello\", \"lo\")\n"
                + "  let e2: boolean = str.endsWith(\"hello\", \"\")\n"
                + "  if (c1 && c2 && !c3 && s1 && s2 && e1 && e2) { console.log(\"find-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_CONTAINS/STARTS_WITH/ENDS_WITH scalar search",
                List.of("find-ok"), SUCCESS);
        }

        // (d) STRING_REPLACE: non-overlapping left-to-right replacement;
        // an empty search text returns the input unchanged.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let r1: string = str.replace(\"a-b-c\", \"-\", \"+\")\n"
                + "  let r2: string = str.replace(\"aaa\", \"aa\", \"b\")\n"
                + "  let r3: string = str.replace(\"abc\", \"\", \"x\")\n"
                + "  if (r1 === \"a+b+c\" && r2 === \"ba\" && r3 === \"abc\") "
                + "{ console.log(\"repl-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_REPLACE non-overlapping + empty-from",
                List.of("repl-ok"), SUCCESS);
        }

        // (e) STRING_SPLIT: empty input → [], empty separator → per-scalar
        // singles, and leading/internal/trailing empty parts preserved.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let parts: string[] = str.split(\"a,b\", \",\")\n"
                + "  let empty: string[] = str.split(\"\", \",\")\n"
                + "  let singles: string[] = str.split(\"ab\", \"\")\n"
                + "  let holes: string[] = str.split(\"a,,b\", \",\")\n"
                + "  if (parts.length === 2 && parts[0] === \"a\" && parts[1] === \"b\" "
                + "&& empty.length === 0 && singles.length === 2 "
                + "&& singles[0] === \"a\" && singles[1] === \"b\" "
                + "&& holes.length === 3 && holes[0] === \"a\" && holes[1] === \"\" "
                + "&& holes[2] === \"b\") { console.log(\"split-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_SPLIT parts + empty separators",
                List.of("split-ok"), SUCCESS);
        }

        // (f) STRING_TRIM: the closed trim set (U+0009-U+000D and
        // U+0020); U+00A0 is never trimmed.
        {
            String source = CONSOLE + STR
                + "function main(): null {\n"
                + "  let t1: string = str.trim(\"  x  \")\n"
                + "  let t2: string = str.trim(\"x \")\n"
                + "  let t3: string = str.trim(\"x\u00A0\")\n"
                + "  if (t1 === \"x\" && t2 === \"x\" && t3 === \"x\u00A0\") "
                + "{ console.log(\"trim-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "STRING_TRIM closed set + non-breaking space",
                List.of("trim-ok"), SUCCESS);
        }

        // (g) TABLE_KEYS: first-insertion order; delete removes the
        // order slot and reinsertion appends it.
        {
            String source = CONSOLE + TBL
                + "function main(): null {\n"
                + "  let t: table = { zero: 0, one: 1, two: 2, filler: 3 }\n"
                + "  delete t.filler\n"
                + "  let ks: string[] = tbl.keys(t)\n"
                + "  let u: table = { a: 1, b: 2 }\n"
                + "  delete u.a\n"
                + "  u.a = 3\n"
                + "  let us: string[] = tbl.keys(u)\n"
                + "  if (ks.length === 3 && ks[0] === \"zero\" && ks[1] === \"one\" "
                + "&& ks[2] === \"two\" && us.length === 2 && us[0] === \"b\" "
                + "&& us[1] === \"a\") { console.log(\"keys-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "TABLE_KEYS first-insertion order + delete/reinsert",
                List.of("keys-ok"), SUCCESS);
        }

        // (h) JSON_PARSE: nested data with typed reads (int/string/
        // null/number), missing keys pre-map to null, duplicate keys keep
        // the last value, and the int/number lexical split round-trips
        // (parsed arrays flow through the stringify walker).
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"a\\\": 1, \\\"b\\\": \\\"x\\\", "
                + "\\\"c\\\": [true, null], \\\"x\\\": {\\\"e\\\": 1.5}, \\\"n\\\": null}\")\n"
                + "  let a: int = d.a\n"
                + "  let b: string = d.b\n"
                + "  let x: table = d.x\n"
                + "  let e: number = x.e\n"
                + "  let n: int | null = d.n\n"
                + "  let m: int | null = d.missing\n"
                + "  let dup: table = json.parse(\"{\\\"a\\\": 1, \\\"a\\\": 2}\")\n"
                + "  let da: int = dup.a\n"
                + "  let rt: string = json.stringify(json.parse(\"{\\\"a\\\":1,\\\"n\\\":100.0,\\\"xs\\\":[1,2]}\"))\n"
                + "  if (a === 1 && b === \"x\" && e === 1.5 && n === null "
                + "&& m === null && da === 2 "
                + "&& rt === \"{\\\"a\\\":1,\\\"n\\\":100.0,\\\"xs\\\":[1,2]}\") "
                + "{ console.log(\"parse-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE nested read + duplicate keys + round-trip",
                List.of("parse-ok"), SUCCESS);
        }

        // (i) JSON_STRINGIFY: deterministic first-insertion-order text,
        // RFC-8259 escaping, nested arrays/objects, and the exact
        // int/number spellings.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let doc: table = { count: 42, ratio: 2.5, flag: true, "
                + "nothing: null, name: \"Ada\" }\n"
                + "  let encoded: string = json.stringify(doc)\n"
                + "  let esc: table = { s: \"a\\\"b\" }\n"
                + "  let nested: table = { xs: [1, 2], g: { h: 2 } }\n"
                + "  let ne: string = json.stringify(nested)\n"
                + "  if (encoded === \"{\\\"count\\\":42,\\\"ratio\\\":2.5,\\\"flag\\\":true,"
                + "\\\"nothing\\\":null,\\\"name\\\":\\\"Ada\\\"}\" "
                + "&& json.stringify(esc) === \"{\\\"s\\\":\\\"a\\\\\\\"b\\\"}\" "
                + "&& ne === \"{\\\"xs\\\":[1,2],\\\"g\\\":{\\\"h\\\":2}}\") "
                + "{ console.log(\"stringify-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY order + escaping + nesting",
                List.of("stringify-ok"), SUCCESS);
        }

        // (i2) JSON_STRINGIFY number spellings: the integral-number class
        // — a number-typed value is never confused with an int carrier
        // (Double.toString parity: 1.0, 100.0, -0.0, 1E20, the 4.0/2.0
        // division result, a MATH_SQRT result), int positions keep the
        // integer spelling, and the distinction survives nested objects,
        // array literals, member writes, and index writes. A shared
        // realization that spells an integral number-typed value with
        // the Lua tostring integer form fails this seed.
        {
            String source = CONSOLE + JSON + MATH
                + "function main(): null {\n"
                + "  let half: number = 4.0 / 2.0\n"
                + "  let root: number = math.sqrt(16.0)\n"
                + "  let t: table = { a: 1.0, b: 100.0, c: -0.0, d: 1.0e20, "
                + "e: 0.5, i: 42, j: -1 }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  let u: table = { n: half, r: root, xs: [1.0, 2.5], "
                + "g: { h: 100.0 } }\n"
                + "  let us: string = json.stringify(u)\n"
                + "  let xs: number[] = [1.0, 2.0]\n"
                + "  xs[1] = 5.0\n"
                + "  let v: table = { xs: xs }\n"
                + "  let vs: string = json.stringify(v)\n"
                + "  let w: table = { z: 1 }\n"
                + "  w.k = 3.0\n"
                + "  let ws: string = json.stringify(w)\n"
                + "  w.k = 4\n"
                + "  let ws2: string = json.stringify(w)\n"
                + "  if (s === \"{\\\"a\\\":1.0,\\\"b\\\":100.0,\\\"c\\\":-0.0,"
                + "\\\"d\\\":1.0E20,\\\"e\\\":0.5,\\\"i\\\":42,\\\"j\\\":-1}\" "
                + "&& us === \"{\\\"n\\\":2.0,\\\"r\\\":4.0,\\\"xs\\\":[1.0,2.5],"
                + "\\\"g\\\":{\\\"h\\\":100.0}}\" "
                + "&& vs === \"{\\\"xs\\\":[1.0,5.0]}\" "
                + "&& ws === \"{\\\"z\\\":1,\\\"k\\\":3.0}\" "
                + "&& ws2 === \"{\\\"z\\\":1,\\\"k\\\":4}\") "
                + "{ console.log(\"strnum-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY number spellings (integral number "
                + "class: 1.0/100.0/-0.0/1E20 + computed/array/member-write slots)",
                List.of("strnum-ok"), SUCCESS);
        }

        // (i3) JSON_PARSE value carriers through the typed reads: an
        // array element read, a for-of element used in arithmetic, the
        // conversion intrinsics over raw parsed reads, and the numeric
        // MATH parameters — the runtime-carried int/number values flow
        // through every numeric consumer (the shared JVM runtime's
        // Long/Double tolerance), and the parsed graph round-trips
        // through the stringify walker with the parsed spellings.
        {
            String source = CONSOLE + JSON + MATH
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"xs\\\": [1.0, 2.0], "
                + "\\\"i\\\": 2, \\\"n\\\": 1.0}\")\n"
                + "  let xs: number[] = d.xs\n"
                + "  let first: number = xs[0]\n"
                + "  let sum: number = 0.0\n"
                + "  for (let x: number of xs) { sum = sum + x }\n"
                + "  let a: number = number(d.i)\n"
                + "  let b: int = int(d.n)\n"
                + "  let f: number = math.floor(d.n)\n"
                + "  let mn: int = math.minInt(d.i, 5)\n"
                + "  let rt: string = json.stringify(d)\n"
                + "  if (first === 1.0 && sum === 3.0 && a === 2.0 && b === 1 "
                + "&& f === 1.0 && mn === 2 "
                + "&& rt === \"{\\\"xs\\\":[1.0,2.0],\\\"i\\\":2,\\\"n\\\":1.0}\") "
                + "{ console.log(\"parse-read-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE typed reads (array element, for-of "
                + "arithmetic, conversions, MATH args, round-trip)",
                List.of("parse-read-ok"), SUCCESS);
        }

        // (i4) The admitted-variant class: the closed value model keeps
        // the int/number variant through every typed boundary, so an int
        // value read from a parsed container and admitted at a
        // number-typed position keeps the integer spelling, and a number
        // value admitted at an int-typed position keeps the decimal
        // spelling — the parsed carriers and the plain dynamic reads
        // alike. A shared Lua realization that follows the static kind
        // instead of the admitted variant fails these seeds.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"i\\\": 2, \\\"n\\\": 2.0}\")\n"
                + "  let a: number = d.i\n"
                + "  let b: int = d.n\n"
                + "  let t: table = { a: a, b: b }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  if (s === \"{\\\"a\\\":2,\\\"b\\\":2.0}\") "
                + "{ console.log(\"parsed-var-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY admitted variants (parsed int under "
                + "number, parsed number under int)", List.of("parsed-var-ok"), SUCCESS);
        }
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = { i: 2, n: 2.0 }\n"
                + "  let a: number = d.i\n"
                + "  let b: int = d.n\n"
                + "  let t: table = { a: a, b: b }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  if (s === \"{\\\"a\\\":2,\\\"b\\\":2.0}\") "
                + "{ console.log(\"dyn-var-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY admitted variants (dynamic int read "
                + "under number, dynamic number read under int)",
                List.of("dyn-var-ok"), SUCCESS);
        }
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"xs\\\": [1, 2]}\")\n"
                + "  let xs: number[] = d.xs\n"
                + "  let first: number = xs[0]\n"
                + "  let a: string = json.stringify({ a: first })\n"
                + "  let ns: number[] = [5.0, 6.0]\n"
                + "  let f: number = ns[0]\n"
                + "  let b: string = json.stringify({ b: f })\n"
                + "  if (a === \"{\\\"a\\\":1}\" && b === \"{\\\"b\\\":5.0}\") "
                + "{ console.log(\"arr-var-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY admitted variants (parsed int array "
                + "element, number array element)", List.of("arr-var-ok"), SUCCESS);
        }

        // (i5) The for-of element read is a typed position: the admitted
        // int/number variant must survive it exactly as it survives the
        // member read — an int element admitted at a number-typed element
        // position keeps the integer spelling, a number element admitted
        // at an int-typed element position keeps the decimal spelling. A
        // shared Lua realization whose for-of cell holds the raw plain
        // number (no variant materialization at the element read) spells
        // the int element through the number-typed binding kind.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = { xs: [1, 2] }\n"
                + "  let xs: number[] = d.xs\n"
                + "  for (let x: number of xs) "
                + "{ console.log(json.stringify({ v: x })) }\n"
                + "  let e: table = { ys: [7.0, 8.5] }\n"
                + "  let ys: number[] = e.ys\n"
                + "  for (let y: number of ys) "
                + "{ console.log(json.stringify({ v: y })) }\n"
                + "  let f: table = { zs: [2.0] }\n"
                + "  let zs: int[] = f.zs\n"
                + "  for (let z: int of zs) "
                + "{ console.log(json.stringify({ v: z })) }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY for-of element variants (int under "
                + "number, number under number, number under int)",
                List.of("{\"v\":1}", "{\"v\":2}", "{\"v\":7.0}", "{\"v\":8.5}",
                    "{\"v\":2.0}"), SUCCESS);
        }

        // (i6) The OPTIONAL_READ present branch is a typed position: the
        // present value keeps its admitted variant through the pre-map
        // and the contextual validation — an int value read at a
        // number-typed nullable position stays int, a number value read
        // at an int-typed nullable position stays a number. A shared Lua
        // realization whose optional present branch copies the raw plain
        // number spells the int value through the nullable binding kind.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"i\\\": 2, \\\"n\\\": 2.0}\")\n"
                + "  let a: number | null = d.i\n"
                + "  let b: int | null = d.n\n"
                + "  let t: table = { a: a, b: b }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  let e: table = { i: 2, n: 2.0 }\n"
                + "  let c: number | null = e.i\n"
                + "  let f: int | null = e.n\n"
                + "  let u: table = { a: c, b: f }\n"
                + "  let us: string = json.stringify(u)\n"
                + "  if (s === \"{\\\"a\\\":2,\\\"b\\\":2.0}\" "
                + "&& us === \"{\\\"a\\\":2,\\\"b\\\":2.0}\") "
                + "{ console.log(\"nullable-var-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY nullable-read admitted variants "
                + "(parsed and dynamic, int under number, number under int)",
                List.of("nullable-var-ok"), SUCCESS);
        }

        // (r) CONSOLE_ERROR: the STDERR channel of the closed effect
        // contract. Trace mode publishes the protocol record (the exact
        // scalar text plus its channel) while the trace stream stays
        // decode-clean — the harness decodes every stderr line, so a raw
        // effect byte would fail the run; the production-mode pins check
        // the real STDERR program bytes.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  console.log(\"out\")\n"
                + "  console.error(\"oops\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "CONSOLE_ERROR STDERR channel + ordered console effects",
                List.of("out", "oops", "after"), SUCCESS);
        }

        // (j) The math family: IEEE floor/ceil/sqrt, signed32 abs, and
        // the min/max selectors.
        {
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let f: number = math.floor(1.7)\n"
                + "  let c: number = math.ceil(1.2)\n"
                + "  let s: number = math.sqrt(16.0)\n"
                + "  let a: int = math.absInt(-5)\n"
                + "  let n: number = math.absNumber(-2.5)\n"
                + "  let mn: int = math.minInt(3, 5)\n"
                + "  let mx: int = math.maxInt(3, 5)\n"
                + "  if (f === 1.0 && c === 2.0 && s === 4.0 && a === 5 "
                + "&& n === 2.5 && mn === 3 && mx === 5) { console.log(\"math-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "MATH_FLOOR/CEIL/SQRT/ABS/MIN/MAX results",
                List.of("math-ok"), SUCCESS);
        }

        // (k) STDLIB_PARAMETER failure projection: a dynamic non-string
        // argument fails the string boundary (E8001 at the boundary
        // origin) before any algorithm runs.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: table = { value: 1 }\n"
                + "  console.log(t.value)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "CONSOLE_LOG dynamic non-string (E8001 boundary)",
                List.of(), E8001);
        }

        // (l) INT32_RESULT projection: absInt(-2147483648) fails E8004
        // at the call origin (the exact long intermediate; the argument
        // is composed through INT32_SUB so no int literal sits outside
        // the signed32 gate).
        {
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let x: int = math.absInt(-2147483647 - 1)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "MATH_ABS_INT int32 minimum (E8004)", List.of(),
                new SemanticDifferentialHarness.TerminalExpectation.FailureWith(
                    "E8004", null));
        }

        // (m) SQRT_NEGATIVE projection: sqrt(-1.0) fails E8001 with the
        // canonical hex-float actual.
        {
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let x: number = math.sqrt(-1.0)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "MATH_SQRT negative (E8001 hex-float actual)",
                List.of(), E8001);
        }

        // (m5) The non-finite number spelling: an infinity carries the
        // Java canonical hex-float spelling ("Infinity"/"-Infinity"),
        // never LuaJIT's "inf"/"-inf" — the infinity crosses the
        // division result, the parameter boundary and the result
        // boundary, and every trace atom must equal the oracle's and the
        // shared JVM runtime's numberAtom (Double.toHexString).
        {
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let t: number = 1.0 / 0.0\n"
                + "  let f: number = math.floor(t)\n"
                + "  if (f === t) { console.log(\"inf-ok\") } else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "MATH_FLOOR infinite argument (num:Infinity atoms)",
                List.of("inf-ok"), SUCCESS);
        }

        // (m6) The SQRT_NEGATIVE actual of a negative infinity argument:
        // the failure projection's actual is the canonical hex-float
        // spelling of -Infinity (the single __numHex renderer), identical
        // across the oracle and both shared artifacts.
        {
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let x: number = math.sqrt(-1.0 / 0.0)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "MATH_SQRT negative infinity (E8001 -Infinity actual)",
                List.of(), E8001);
        }

        // (m7) The subnormal hex-float spelling: a value below 2^-1022
        // carries Java's fixed-exponent denormal atom
        // ("num:0x0.00000000007e8p-1022"), never LuaJIT's normalized
        // "num:0x1.fap-1064" — the subnormal flows through the literal,
        // an arithmetic result, the load and every boundary atom.
        {
            String source = CONSOLE
                + "function main(): null {\n"
                + "  let t: number = 1.0e-320\n"
                + "  let u: number = t + 0.0\n"
                + "  if (u === t) { console.log(\"subnormal-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "subnormal number atom (denormal hex spelling)",
                List.of("subnormal-ok"), SUCCESS);
        }

        // (m8) The JSON_STRINGIFY text of the values the C %g path spells
        // differently from Double.toString: a subnormal (1.0E-320, not
        // the 1.0E-321 exponent), a shortest-decimal tie
        // (2.9802322387695312E-8), a closest-decimal-outside-the-
        // interval case (5.858190679279809E-244), a 17-digit tie
        // (1.2599473634643432E15) and a value whose shortest decimal
        // rounds up across the power of ten (1.0E23).
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let t: table = { a: 1.0e-320, b: 2.9802322387695312e-8, "
                + "c: 1.2599473634643432e15, d: 5.858190679279809e-244, e: 1.0e23 }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  if (s === \"{\\\"a\\\":1.0E-320,\\\"b\\\":2.9802322387695312E-8,"
                + "\\\"c\\\":1.2599473634643432E15,\\\"d\\\":5.858190679279809E-244,"
                + "\\\"e\\\":1.0E23}\") { console.log(\"numtext-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source,
                "JSON_STRINGIFY Double.toString spellings (subnormal, ties, round-up)",
                List.of("numtext-ok"), SUCCESS);
        }

        // (n) JSON_PARSE_SYNTAX projections: the defect-classification
        // texts and the 1-based UTF-8 byte offsets (a multi-byte scalar
        // counts its full UTF-8 length).
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{bad\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE missing key (E8001 parse position)",
                List.of(), E8001);
        }
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE empty input (E8001 unexpected end)",
                List.of(), E8001);
        }
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"é\\\": }\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE byte offset after a multi-byte scalar",
                List.of(), E8001);
        }

        // (o) STDLIB_RETURN boundary: a successful parse whose top-level
        // value is not a table fails the declared return boundary
        // (E8001 at the boundary origin — the call machine's, never the
        // primitive's).
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"\\\"x\\\"\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "JSON_PARSE non-table top level (E8001 return boundary)",
                List.of(), E8001);
        }

        // (o2) STDLIB_RETURN boundary over a top-level parsed array: the
        // runtime value is an array, so the actual kind is "array" —
        // never the declared static "table".
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"[1,2]\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            SemanticDifferentialHarness.Verdict verdict = runMatrix(source,
                "JSON_PARSE top-level array (E8001 array actual)", List.of(), E8001);
            checkTerminalMessage(verdict, "expected table, got array",
                "JSON_PARSE top-level array return boundary");
        }

        // (p) JSON_TO_ERROR projection: the first declaration-order
        // unsupported value wins with its field path and actual token —
        // a nonfinite number at field n.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let t: table = { n: 0.0 / 0.0 }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY nonfinite number (E8001 field path)",
                List.of(), E8001);
        }

        // (p2) JSON_TO_ERROR over a deleted array element: the deleted
        // slot is the internal missing, not language null — the walker
        // fails with the "missing" projection instead of emitting null.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let xs: int[] = [1, 2, 3]\n"
                + "  delete xs[1]\n"
                + "  let t: table = { xs: xs }\n"
                + "  let s: string = json.stringify(t)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            SemanticDifferentialHarness.Verdict verdict = runMatrix(source,
                "JSON_STRINGIFY deleted array element (E8001 missing)", List.of(), E8001);
            checkTerminalMessage(verdict,
                "unsupported type for JSON encoding: missing",
                "JSON_STRINGIFY deleted array element");
            checkTerminalExpectedActual(verdict,
                SharedStdlibSemantics.JSON_STRINGIFY_EXPECTED, "missing",
                "JSON_STRINGIFY deleted array element");
        }

        // (p3) The present-null element of a parsed array stays language
        // null (the __NULL marker), never the deleted-slot missing — the
        // round trip pins the distinction the missing arm must respect.
        {
            String source = CONSOLE + JSON
                + "function main(): null {\n"
                + "  let d: table = json.parse(\"{\\\"xs\\\": [1, null, 2]}\")\n"
                + "  let s: string = json.stringify(d)\n"
                + "  if (s === \"{\\\"xs\\\":[1,null,2]}\") { console.log(\"hole-ok\") } "
                + "else { console.log(\"bad\") }\n"
                + "}\n";
            runMatrix(source, "JSON_STRINGIFY parsed present-null element (not missing)",
                List.of("hole-ok"), SUCCESS);
        }

        // (q) Production-mode realization (no trace-only arm): the same
        // stdlib unit emitted through the production surfaces runs under
        // the real toolchains — the cataloged results land on stdout, and
        // a projection failure publishes the retained DEAL_ERROR_CODE
        // terminal on stdout with exit 1.
        {
            String source = CONSOLE + STR + MATH + JSON
                + "function main(): null {\n"
                + "  let n: int = str.length(\"a😀b\")\n"
                + "  let a: int = math.absInt(-5)\n"
                + "  let d: table = json.parse(\"{\\\"xs\\\": [1.0, 2.0]}\")\n"
                + "  let xs: number[] = d.xs\n"
                + "  let first: number = xs[0]\n"
                + "  let text: string = json.stringify({ v: first })\n"
                + "  if (n === 3 && a === 5 && first === 1.0 "
                + "&& text === \"{\\\"v\\\":1.0}\") "
                + "{ console.log(\"stdlib-prod-ok\") } "
                + "else { console.log(\"stdlib-prod-bad\") }\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source,
                "production-mode stdlib emission");
            LoweredSlice lowered = lowerFull(slice,
                "production-mode stdlib emission");
            if (lowered != null) {
                try {
                    String lua = deal.codegen.lua.LuaSemanticEmitter
                        .emitProductionModule(lowered.unit(), lowered.table(), true);
                    Path script = WORKSPACE.resolve("stdlib-prod.lua");
                    Files.writeString(script, lua);
                    Process luaRun = new ProcessBuilder("luajit",
                        script.toAbsolutePath().toString())
                        .redirectErrorStream(true).start();
                    String luaOutput = new String(
                        luaRun.getInputStream().readAllBytes());
                    int luaExit = luaRun.waitFor();
                    check(luaExit == 0 && luaOutput.contains("stdlib-prod-ok"),
                        "the production shared-LuaJIT stdlib artifact runs the "
                            + "cataloged calls (exit " + luaExit + ", output "
                            + luaOutput.trim() + ")");

                    deal.codegen.jvm.JvmSemanticEmitter.EmissionResult emission =
                        deal.codegen.jvm.JvmSemanticEmitter.emitProductionModule(
                            lowered.unit(), lowered.table(), true, "StdlibProdMain");
                    Path sourceFile = WORKSPACE.resolve("StdlibProdMain.java");
                    Files.writeString(sourceFile, emission.source());
                    Path classes = WORKSPACE.resolve("stdlib-prod-classes");
                    Files.createDirectories(classes);
                    String classpath = System.getProperty("java.class.path", "");
                    Process compile = new ProcessBuilder("javac", "--release", "25",
                        "-proc:none", "-cp", classpath, "-d", classes.toString(),
                        sourceFile.toAbsolutePath().toString())
                        .redirectErrorStream(true).start();
                    String compileOutput = new String(
                        compile.getInputStream().readAllBytes());
                    int compileExit = compile.waitFor();
                    check(compileExit == 0, "the production shared-JVM stdlib "
                        + "artifact compiles (exit " + compileExit + ": "
                        + compileOutput.trim() + ")");
                    if (compileExit == 0) {
                        Process javaRun = new ProcessBuilder("java", "-cp",
                            classpath + java.io.File.pathSeparator + classes,
                            "StdlibProdMain").redirectErrorStream(true).start();
                        String javaOutput = new String(
                            javaRun.getInputStream().readAllBytes());
                        int javaExit = javaRun.waitFor();
                        check(javaExit == 0 && javaOutput.contains("stdlib-prod-ok"),
                            "the production shared-JVM stdlib artifact runs the "
                                + "cataloged calls (exit " + javaExit + ", output "
                                + javaOutput.trim() + ")");
                    }
                } catch (java.io.IOException | InterruptedException exception) {
                    fail("production-mode stdlib emission: infrastructure failure: "
                        + exception.getMessage());
                }
            }
        }
        {
            // The production failure projection: the shared artifact exits 1
            // with the retained DEAL_ERROR_CODE terminal on stdout (never a
            // trace suppression that swallows the projection).
            String source = CONSOLE + MATH
                + "function main(): null {\n"
                + "  let x: number = math.sqrt(-1.0)\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source,
                "production-mode stdlib failure projection");
            LoweredSlice lowered = lowerFull(slice,
                "production-mode stdlib failure projection");
            if (lowered != null) {
                try {
                    String lua = deal.codegen.lua.LuaSemanticEmitter
                        .emitProductionModule(lowered.unit(), lowered.table(), true);
                    Path script = WORKSPACE.resolve("stdlib-prod-fail.lua");
                    Files.writeString(script, lua);
                    Process luaRun = new ProcessBuilder("luajit",
                        script.toAbsolutePath().toString())
                        .redirectErrorStream(true).start();
                    String luaOutput = new String(
                        luaRun.getInputStream().readAllBytes());
                    int luaExit = luaRun.waitFor();
                    check(luaExit == 1
                            && luaOutput.contains("DEAL_ERROR_CODE: E8001")
                            && !luaOutput.contains("after"),
                        "the production shared-LuaJIT stdlib artifact publishes the "
                            + "retained DEAL_ERROR_CODE terminal (exit " + luaExit
                            + ", output " + luaOutput.trim() + ")");

                    deal.codegen.jvm.JvmSemanticEmitter.EmissionResult emission =
                        deal.codegen.jvm.JvmSemanticEmitter.emitProductionModule(
                            lowered.unit(), lowered.table(), true,
                            "StdlibProdFailMain");
                    Path sourceFile = WORKSPACE.resolve("StdlibProdFailMain.java");
                    Files.writeString(sourceFile, emission.source());
                    Path classes = WORKSPACE.resolve("stdlib-prod-fail-classes");
                    Files.createDirectories(classes);
                    String classpath = System.getProperty("java.class.path", "");
                    Process compile = new ProcessBuilder("javac", "--release", "25",
                        "-proc:none", "-cp", classpath, "-d", classes.toString(),
                        sourceFile.toAbsolutePath().toString())
                        .redirectErrorStream(true).start();
                    String compileOutput = new String(
                        compile.getInputStream().readAllBytes());
                    int compileExit = compile.waitFor();
                    check(compileExit == 0, "the production shared-JVM stdlib "
                        + "failure artifact compiles (exit " + compileExit + ": "
                        + compileOutput.trim() + ")");
                    if (compileExit == 0) {
                        Process javaRun = new ProcessBuilder("java", "-cp",
                            classpath + java.io.File.pathSeparator + classes,
                            "StdlibProdFailMain").redirectErrorStream(true).start();
                        String javaOutput = new String(
                            javaRun.getInputStream().readAllBytes());
                        int javaExit = javaRun.waitFor();
                        check(javaExit == 1
                                && javaOutput.contains("DEAL_ERROR_CODE: E8001")
                                && !javaOutput.contains("after"),
                            "the production shared-JVM stdlib artifact publishes the "
                                + "retained DEAL_ERROR_CODE terminal (exit " + javaExit
                                + ", output " + javaOutput.trim() + ")");
                    }
                } catch (java.io.IOException | InterruptedException exception) {
                    fail("production-mode stdlib failure projection: "
                        + "infrastructure failure: " + exception.getMessage());
                }
            }
        }
        {
            // The CONSOLE_ERROR production channel: the same program as
            // the trace-mode CONSOLE_ERROR seed, so the real program bytes
            // cross-check the recorded effects — the CONSOLE_LOG effects
            // ("out", "after") are exactly the stdout lines in order and
            // the CONSOLE_ERROR effect ("oops") is exactly the stderr line
            // with the closed scalar bytes plus one '\n'.
            String source = CONSOLE
                + "function main(): null {\n"
                + "  console.log(\"out\")\n"
                + "  console.error(\"oops\")\n"
                + "  console.log(\"after\")\n"
                + "}\n";
            CheckedSlice slice = checkSlice(source, "production-mode console channels");
            LoweredSlice lowered = lowerFull(slice, "production-mode console channels");
            if (lowered != null) {
                try {
                    String lua = deal.codegen.lua.LuaSemanticEmitter
                        .emitProductionModule(lowered.unit(), lowered.table(), true);
                    Path script = WORKSPACE.resolve("console-prod.lua");
                    Files.writeString(script, lua);
                    Path luaOut = WORKSPACE.resolve("console-prod-lua-out.txt");
                    Path luaErr = WORKSPACE.resolve("console-prod-lua-err.txt");
                    Process luaRun = new ProcessBuilder("luajit",
                        script.toAbsolutePath().toString())
                        .redirectOutput(luaOut.toFile()).redirectError(luaErr.toFile())
                        .start();
                    int luaExit = luaRun.waitFor();
                    String luaOutText = Files.readString(luaOut);
                    String luaErrText = Files.readString(luaErr);
                    check(luaExit == 0 && luaOutText.equals("out\nafter\n")
                            && luaErrText.equals("oops\n"),
                        "the production shared-LuaJIT console artifact writes the "
                            + "CONSOLE_LOG effect bytes to stdout and the CONSOLE_ERROR "
                            + "effect bytes to stderr (exit " + luaExit + ", stdout "
                            + luaOutText.trim() + ", stderr " + luaErrText.trim() + ")");

                    deal.codegen.jvm.JvmSemanticEmitter.EmissionResult emission =
                        deal.codegen.jvm.JvmSemanticEmitter.emitProductionModule(
                            lowered.unit(), lowered.table(), true, "ConsoleProdMain");
                    Path sourceFile = WORKSPACE.resolve("ConsoleProdMain.java");
                    Files.writeString(sourceFile, emission.source());
                    Path classes = WORKSPACE.resolve("console-prod-classes");
                    Files.createDirectories(classes);
                    String classpath = System.getProperty("java.class.path", "");
                    Process compile = new ProcessBuilder("javac", "--release", "25",
                        "-proc:none", "-cp", classpath, "-d", classes.toString(),
                        sourceFile.toAbsolutePath().toString())
                        .redirectErrorStream(true).start();
                    String compileOutput = new String(
                        compile.getInputStream().readAllBytes());
                    int compileExit = compile.waitFor();
                    check(compileExit == 0, "the production shared-JVM console "
                        + "artifact compiles (exit " + compileExit + ": "
                        + compileOutput.trim() + ")");
                    if (compileExit == 0) {
                        Path jvmOut = WORKSPACE.resolve("console-prod-jvm-out.txt");
                        Path jvmErr = WORKSPACE.resolve("console-prod-jvm-err.txt");
                        Process javaRun = new ProcessBuilder("java", "-cp",
                            classpath + java.io.File.pathSeparator + classes,
                            "ConsoleProdMain")
                            .redirectOutput(jvmOut.toFile())
                            .redirectError(jvmErr.toFile()).start();
                        int javaExit = javaRun.waitFor();
                        String jvmOutText = Files.readString(jvmOut);
                        String jvmErrText = Files.readString(jvmErr);
                        check(javaExit == 0 && jvmOutText.equals("out\nafter\n")
                                && jvmErrText.equals("oops\n"),
                            "the production shared-JVM console artifact writes the "
                                + "CONSOLE_LOG effect bytes to stdout and the "
                                + "CONSOLE_ERROR effect bytes to stderr (exit " + javaExit
                                + ", stdout " + jvmOutText.trim() + ", stderr "
                                + jvmErrText.trim() + ")");
                    }
                } catch (java.io.IOException | InterruptedException exception) {
                    fail("production-mode console channels: infrastructure failure: "
                        + exception.getMessage());
                }
            }
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    private static SemanticOp opById(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp producerOf(LoweredModuleUnit unit,
                                         deal.semantic.ir.ValueId value) {
        for (SemanticOp op : unit.ops()) {
            if (value.equals(op.result())) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // Synthetic unit helpers (the hand-built extras corpus units)
    // =========================================================================

    private static int nextSyntheticValue = 1;

    private static ValueId nextValue() {
        return new ValueId(nextSyntheticValue++);
    }

    private static RuntimeDescriptor nullableInt() {
        return new RuntimeDescriptor.Nullable(RuntimeDescriptor.Int.INSTANCE);
    }

    /** One synthetic validated-shape op with a wired contract digest. */
    private static SemanticOp syntheticOp(SemanticOpKind kind, KindPayload payload,
                                          SemanticValue result, OpResultType resultType) {
        AnchorId anchor = new AnchorId(0);
        SourceOrigin origin = new SourceOrigin("test.deal",
            SourceSpan.synthetic("test.deal"), SourceOriginKind.SYNTHETIC, anchor, null);
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, List.of(), selector,
            payload, FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, List.of(), selector,
            payload, FailurePolicyId.NO_DEAL_FAILURE, List.of(), digest);
        return new SemanticOp(new OpId(MODULE, nextSyntheticValue++), kind, origin, result,
            resultType, List.of(), List.of(), payload, FailurePolicyId.NO_DEAL_FAILURE,
            contract);
    }

    /** One synthetic unit over the extras corpus ops. */
    private static LoweredModuleUnit syntheticUnit(List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MODULE, INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH),
            java.util.Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            ops);
    }

    /** The single-block membership table of one synthetic unit. */
    private static StructuredBodyTable syntheticTable(List<SemanticOp> ops) {
        List<OpId> opIds = new ArrayList<>();
        Map<OpId, BlockId> opBlocks = new java.util.LinkedHashMap<>();
        for (SemanticOp op : ops) {
            opIds.add(op.opId());
            opBlocks.put(op.opId(), new BlockId(0));
        }
        return new StructuredBodyTable(Map.of(new BlockId(0), opIds), opBlocks);
    }

    // =========================================================================
    // Entry
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Runtime Integration Matrix Test (ISSUE-0410 "
            + "decomposition tail: semantic oracle + shared LuaJIT + shared JVM) ===\n");

        testChainOrderMatrix();
        testChainFailureMatrix();
        testComparisonMatrix();
        testControlMatrix();
        testContainerExtrasMatrix();
        testHasFieldPresenceMatrix();
        testRecursiveGroupMatrix();
        testRecursiveGroupProductionEmission();
        testStdlibMatrix();
        testPinnedIrFacts();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
