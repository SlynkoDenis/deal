package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticFormatter;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.RangeOrigin;
import deal.types.Type;
import deal.types.Types;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.identity.CanonicalModuleIdentity;
import deal.identity.ProjectModuleIdentity;
import deal.module.ModuleIdentityResolver;
import deal.module.ModuleShapeValidator;
import deal.module.CompilationOrchestrator;
import deal.project.ProjectContext;
import deal.project.ProjectLocator;
import deal.project.StrictManifestParser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ir.ReleaseState;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ModuleRoute;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RoutePlanResult;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticProfile;
import deal.source.ScalarSourceCursor;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Unit tests for the JVM backend skeleton (ISSUE-0091), the first
 * semantic slice (ISSUE-0092 — while loops and template literals), the
 * functions/direct-calls slice (ISSUE-0093 — parameter shadowing
 * against module fields and other visible bindings), and the
 * primitive-array slice (ISSUE-0094 — {@code int[]}/{@code number[]}/
 * {@code string[]}/{@code boolean[]} literals, index reads, element
 * writes, and {@code .length} reads with the spec's runtime checks), the
 * modules/imports/exports slice (ISSUE-0096 — multi-module
 * compilation, namespace imports, and imported direct calls), and the
 * stdlib-boundary slice (ISSUE-0097 — the stdlib modules whose declared
 * functions use only the supported value types: {@code std/console},
 * {@code std/string}, {@code std/math}, {@code std/time}):
 * <ul>
 *   <li>parameter shadowing (ISSUE-0093): a parameter shadowing a
 *       module field emits ONE disambiguated Java name in both the
 *       method signature and the body, a {@code let} shadowing a
 *       disambiguated parameter never reuses the parameter's emitted
 *       name (its initializer's enclosing read binds to the parameter),
 *       double-nested local shadowing reads the nearest enclosing
 *       binding, and the triple-deep shadow chain (field → parameter →
 *       body-top let → inner-block let, with and without the module
 *       field) emits one distinct Java name per binding — never
 *       re-using a shadowed parameter's still-in-Java-scope name, which
 *       javac would reject after the CLI reported success — all compiled
 *       and executed with {@code javac} + {@code java},</li>
 *   <li>while loops: counting/nested/shadowed loops, {@code while (false)}
 *       bodies that never run, per-iteration re-evaluation of conditions
 *       with hoisted null-typed side effects, function-body module-field
 *       dominance guards through loop bodies (a write inside a loop body
 *       dominates nothing after the loop), module-level returns inside
 *       while bodies, use-before-declaration in while conditions, and the
 *       emitted {@code loopCond} identity helper (constant-expression
 *       conditions are never visible to javac; a DEAL function colliding
 *       with the helper signature is E6000),</li>
 *   <li>template literals lowered to string concatenation (interpolated
 *       and plain parts, empty parts elided, single-part templates),</li>
 *   <li>identifier translation and collision-safe class-name derivation,</li>
 *   <li>Java emission for the supported skeleton surface
 *       (literals, arithmetic, locals, if/else, console output, intrinsics),</li>
 *   <li>local classes and nominal checks (ISSUE-0095): module-level
 *       {@code class} declarations emit a generated nested static class
 *       ({@code $C_<name>} extending the {@code $Base} identity holder),
 *       object-literal construction applies defaults per construction with
 *       provided fields evaluated left-to-right, primitive field
 *       reads/writes emit direct accesses, tables emit a minimal ordered
 *       string-key map (the shared {@code $DealRt.Table} class),
 *       and a class-typed table read — the
 *       slice's one untyped boundary — runs the emitted {@code $check<C>}
 *       nominal check (E8001 for wrong-class and non-class values),</li>
 *   <li>imported classes and cross-module nominal identity (ISSUE-0109):
 *       {@code export class} emits the same generated nested class as a
 *       local one (the export only adds the class to the module type),
 *       imported-class values map to the DECLARING module's generated
 *       class ({@code Lib.$C_C}), imported construction
 *       ({@code new Lib.$C_Point(...)} with literal defaults applied
 *       inline and provided fields reordered to declaration order),
 *       class-typed table reads run the declaring module's nominal check
 *       helper (success for a genuine instance; E8001 naming both
 *       module-qualified identities for a same-name sibling from another
 *       module), and a same-named local class never satisfies the
 *       imported-class guard (locality is decided from the Type.Class
 *       module path),</li>
 *   <li>the nullable slice (ISSUE-0108): {@code T | null} for the four
 *       primitives and local classes across locals, module fields, class
 *       fields, parameters, and returns (boxed reference representation,
 *       narrowed reads unbox through the null-check branches),
 *       {@code T[] | null} and {@code (T | null)[]} for the primitive
 *       and local-class element types, class arrays {@code C[]}, the
 *       table-read nullable boundary checks with runtime E8001 failures,
 *       and the {@code int()}/{@code number()} nullable conversion
 *       overloads — all compiled and executed with {@code javac} +
 *       {@code java},</li>
 *   <li>the @jsonable slice (JSON serialization): the generated
 *       {@code C$fromJson}/{@code C$toJson} module exports (translated
 *       with {@code javaName} — {@code User$dfromJson} — exactly what
 *       the same-module and imported call sites emit), the per-class
 *       {@code $jsonFields} descriptor table, fromJson validation
 *       (extra keys, malformed JSON, type mismatches → the DEAL null,
 *       never a throw — including hostile deep-nesting input, where
 *       the emitted parser converts its StackOverflowError to the DEAL
 *       null and the table-value conversion carries a bounded depth
 *       guard), toJson serialization with std/json.lua's
 *       E8001 NaN/Infinity rejection, defaults applied inline,
 *       required no-default fields (the reference defaults table:
 *       the primitive zeroes, a fresh empty table/array per call —
 *       never Java null — and a required class-typed field's absent
 *       key as a fromJson validation failure), nullable/array/
 *       nested-class/optional/table-typed fields
 *       (the three optional-nullable states through the Missing
 *       sentinel with {@code has()} presence, JSON-shaped table data
 *       including array-mode tables), and the slice boundaries
 *       (optional/table-typed fields on NON-jsonable classes,
 *       optional table fields of @jsonable classes — their reads
 *       yield {@code table | null} — and module-level helper calls —
 *       E6000/E1049), runtime cases
 *       compiled and executed with {@code javac} + {@code java},</li>
 *   <li>E6000 rejection of out-of-scope constructs (optional/
 *       array/class/table-typed (non-nullable) class fields, nested class
 *       declarations, table reads with primitive (non-nullable) targets,
 *       table field writes, nested/function arrays, {@code table | null}
 *       values, {@code (table | null)[]} elements, for/for-of
 *       loops, async, non-project imports — at the import statement
 *       itself, even when unused —, module-level returns,
 *       use-before-declaration, runtime-helper name collisions),</li>
 *   <li>the stdlib boundary (ISSUE-0097): {@code std/string}/
 *       {@code std/math}/{@code std/time} imports compile and execute
 *       their declared functions through the emitted {@code __str*}/
 *       {@code __mathSqrt} helpers and fully-qualified
 *       {@code java.lang.Math}/{@code java.lang.String} expressions —
 *       Unicode scalar-value {@code length}/{@code substring}/
 *       {@code split} (including the {@code "héllo"} scalar-count and
 *       scalar-position pins — spec-v1.2 measures string lengths and
 *       positions in Unicode scalar values), plain-text search/replace
 *       with the empty-{@code old} guard, the Lua-whitespace
 *       {@code trim}, the negative-input {@code sqrt} E8001, the
 *       extreme-negative {@code absInt}, and the second-truncated
 *       {@code nowMillis()} — while {@code std/table}
 *       and {@code std/json} (ISSUE-0302) also execute: {@code keys}
 *       over the shared table carrier and {@code json.parse}/
 *       {@code json.stringify} over the emitted shared JSON runtime,
 *       all compiled and executed with {@code javac} +
 *       {@code java} subprocesses,</li>
 *   <li>observable-behavior preservation for null-typed side effects
 *       (null-typed returns/initializers/assignments/arguments — including
 *       captures of locals and parameters reassigned later in their scope,
 *       which a lambda lowering would make javac reject), module-level
 *       load-time statements, standalone expression statements, null
 *       equality, floored {@code %} on negative operands, string
 *       equality/ordering, and {@code console.error} → stderr — verified by
 *       executing the emitted artifact with {@code javac} + {@code java}
 *       subprocesses,</li>
 *   <li>left-to-right evaluation-order preservation for hoisted null-typed
 *       side effects: an earlier inline side-effecting (or raising)
 *       operand of the same statement is materialized into a temporary
 *       before the hoisted pre-statement, in every combination position —
 *       never an inverted output order and never a lambda,</li>
 *   <li>dead-code skipping after non-completing statements (a complete
 *       all-returning if/else, return-after-return, block-level dead
 *       lets/expression statements, dead else-if chains with hoisted
 *       null-typed conditions — never an artifact javac rejects as
 *       unreachable), function-body reads of later-declared module fields
 *       governed by a write-dominance analysis (write-then-read allowed;
 *       the no-prior-write shape — LuaJIT fails at call time reading the
 *       global nil — rejected with E6000; the load-time guard stays), and
 *       fixture-schema validation ({@code expectedCompileError} combined
 *       with runtime/IR assertions fails per conformance-test-architecture
 *       D6),</li>
 *   <li>DEAL runtime error codes (E8004/E8005/E8006/E8001 incl. the
 *       negative-exponent and extreme-power paths) surfaced by executing the
 *       emitted artifact,</li>
 *   <li>the DEAL int safe range ±(2^53-1) = ±9007199254740991: boundary
 *       success and E8004 pins for every int-producing operation
 *       (add/sub/mul/neg/{@code **}/int() and out-of-range literals as
 *       operands or at the return), with emission assertions that the
 *       helpers route through the emitted {@code checkInt} bound — never
 *       Java's long bound,</li>
 *   <li>fully-qualified {@code java.lang} references: locals, parameters,
 *       and module fields named {@code System}/{@code Math}/{@code Double}/
 *       {@code String}/{@code Void}/{@code Integer}/{@code Character}/
 *       {@code RuntimeException}/{@code ArithmeticException} coexist with
 *       console output, int arithmetic, number {@code **}, non-finite
 *       literals, string ordering, and runtime errors — all compiled and
 *       executed, with qualified-name emission assertions,</li>
 *   <li>use-before-declaration walking of every {@code if}/{@code else if}
 *       chain condition: module-level, function-body, and deep-chain
 *       forward references are E6000 (never an artifact javac rejects after
 *       the CLI reported success), while chains over already-declared
 *       variables stay clean,</li>
 *   <li>primitive arrays (ISSUE-0094): the emitted {@code __IntArray}/
 *       {@code __NumberArray}/{@code __StringArray}/{@code __BooleanArray}
 *       wrapper classes and read/write helpers (bounds checks: negative
 *       read/write and gap write → E8002, read past the end → E8001
 *       "expected &lt;T&gt;, got null"; element value checks: int elements
 *       route through {@code checkInt} → E8004; the write check runs after
 *       the receiver/index/RHS expressions evaluate, per spec-v1.2
 *       §Operational semantics rule 3), appends at {@code i == length} with
 *       the wrapper identity stable across growth (alias parity),
 *       evaluation order with hoisted null-typed side effects materialized
 *       into temporaries, arrays through function parameters/returns and
 *       module fields, E6000 rejection of nested arrays and
 *       function arrays, and
 *       use-before-declaration guards walking index/array-literal/length
 *       positions — all compiled and executed with {@code javac} +
 *       {@code java},</li>
 *   <li>the backend-selection seam: {@code CompilationOrchestrator} with
 *       {@code Backend.JVM} emits and compiles a real {@code .java} artifact,
 *       rejects out-of-scope projects with E6000, detects class-name
 *       collisions, the default stays LuaJIT, {@code DealConfig} and the CLI
 *       accept {@code jvm},</li>
 *   <li>the modules slice (ISSUE-0096): multi-module orchestrator compiles
 *       emit one artifact class per module with the import resolution map
 *       ({@code testModuleImports}), same-basename modules in different
 *       directories derive isolated class names ({@code
 *       testModuleClassIsolation}), sibling imports initialize
 *       depth-first in import order ({@code testModuleUnusedImportLoadTime}),
 *       backend-level emission pins the load-time {@code __init$} trigger
 *       and the static cross-class call ({@code
 *       testModuleImportBackendEmission}), an unused project-module import
 *       still runs the imported module's load-time code ({@code
 *       testOrchestratorJvmImportSupported}), and a declaration/host-module
 *       import stays E6000 with no artifact ({@code
 *       testOrchestratorJvmDeclarationImportRejected}).</li>
 *   <li>function values and wrappers (ISSUE-0098): per-signature wrapper
 *       classes with spec-convention descriptor strings, per-declaration
 *       wrapper instance fields, indirect-call dispatch through
 *       {@code invoke}, intrinsic function-value wrappers, arity-extension
 *       adapters at variable/assignment positions (static-method
 *       delegation for module functions and effectively-final snapshot
 *       temporaries for locals/parameters the enclosing body never
 *       reassigns; reassigned locals/parameters and non-identifier
 *       adapter values are E6000 until ISSUE-0110 — never a lambda,
 *       never a silent divergence), E8010 runtime signature checks at
 *       callback/return boundaries with LuaJIT's exact message and the
 *       checked value expression evaluated FIRST
 *       (evaluate-then-check — side effects never dropped; a check
 *       operand's VALUE lowers to an actual-shape temporary while the
 *       raising construction stays INLINE at the argument position, so
 *       two arity-mismatched function-valued arguments in one call
 *       compile to valid Java and raise the FIRST parameter's E8010 in
 *       parameter order, pinned in {@code testFunctionValues} and the
 *       {@code jvm-fv-cross-e8010-two-mismatched-args} conformance
 *       fixture), wrapper
 *       reference equality, call-result-callee evaluation order (the
 *       callee materialized into a single-assignment temporary at its
 *       evaluation position, before any argument's hoisted
 *       pre-statements), the shared-carrier shape encoding and $check behaviors
 *       ({@code testSharedCarrierShapeEncoding},
 *       {@code testSharedCarrierCheckBehaviors}), function
 *       equality/inequality over array-/class-/nullable-parameter
 *       signatures now emitting on the shared wrappers, and
 *       cross-module
 *       function values (a Func-typed argument to an imported module
 *       call — including the arity-extension/E8010-boundary shape —
 *       an imported call result with Func static type, and an imported
 *       call-result callee) compiling and executing on the shared
 *       $DealRt carriers with reference identity across the module
 *       boundary
 *       ({@code testCrossModuleFunctionValues},
 *       {@code testSharedCarrierCrossModuleIdentity} — the pre-fix
 *       per-module wrapper classes could not cross a module boundary,
 *       so the pre-fix emissions were artifacts javac rejected after
 *       the CLI reported success). Every v1.1 module-field/load-time
 *       shape — the LIVE
 *       static-field-delegation adapter, the load-time indirect-call
 *       guards, the module-level call-result callee hazards, and the
 *       rest function-type arm — is a v1.2 frontend grammar gate
 *       (E1049/E1047) pinned in {@code testFunctionValues}: the v1.2
 *       module top level holds only declarations, so those shapes no
 *       longer reach a backend.</li>
 * </ul>
 *
 * <p>This class covers JVM backend seams, edge behavior, and generated
 * artifact execution directly.
 */
public class JvmBackendTest {

    private static final int DEFAULT_JOBS = 1;

    /**
     * The harness invocation of the retained-subject compiles (ISSUE-0643
     * P10 item 3): COMMON_SHADOW / DEAL_V1_2_INT32, never the release-owned
     * production record, so the retained per-module JVM artifact assertions
     * stay green; the production-invocation pins keep the release-owned
     * record and assert the project-artifact outcome.
     */
    private static CompilerInvocation harnessInvocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
    }

    private static final AtomicInteger passed = new AtomicInteger();
    private static final AtomicInteger failed = new AtomicInteger();

    /**
     * Per-worker-thread temp project dir (ISSUE-0274 parallel workers):
     * every test method writes its scratch files into its own directory,
     * so parallel execution never shares temp state. All created dirs
     * are registered for the end-of-run cleanup.
     */
    private static final ConcurrentLinkedQueue<Path> tmpDirs =
        new ConcurrentLinkedQueue<>();
    private static final ThreadLocal<Path> tmpDir =
        ThreadLocal.withInitial(() -> {
            try {
                Path dir = Files.createTempDirectory("jvm_backend_test_");
                tmpDirs.add(dir);
                return dir;
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        });

    /** The per-thread output buffer the dispatch streams route writes to. */
    private static final ThreadLocal<StringBuilder> OUTPUT_BUFFER =
        new ThreadLocal<>();
    /**
     * Per-thread stderr capture override for the CLI-warning tests: while
     * set, the dispatch stderr stream routes this thread's stderr writes
     * into the override instead of the output buffer — the same
     * observable capture the tests previously performed with a global
     * {@code System.setErr} swap, without the global race.
     */
    private static final ThreadLocal<OutputStream> ERR_CAPTURE =
        new ThreadLocal<>();
    private static final Object CONSOLE_LOCK = new Object();

    public static void main(String[] args) {
        // ISSUE-0274 gate-time work: the 89 test methods spawn over two
        // hundred java subprocesses and an in-process javac compile each;
        // running them sequentially kept the suite over the gate's
        // wall-clock budget. The methods are independent — each writes
        // into its own per-thread temp dir and its own per-test output
        // buffer — so they run on a worker pool with the same
        // deterministic-outcome machinery legacy JSON conformance harness uses
        // (atomic counters, per-test buffered output flushed as one
        // contiguous block, completion-order blocks). The CLI-warning
        // captures route through the per-thread ERR_CAPTURE override
        // instead of a global System.setErr swap, so no test needs a
        // serialized main-thread tail. The pool is sized at 2x the core
        // count for the same reason legacy JSON conformance harness oversubscribes:
        // per-test work is dominated by javac/java subprocess latency, so
        // the extra workers overlap spawns under concurrent host load.
        PrintStream realOut = System.out;
        PrintStream realErr = System.err;
        System.setOut(new PrintStream(new DispatchStream(realOut, false),
            true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(new DispatchStream(realErr, true),
            true, StandardCharsets.UTF_8));

        List<TestCase> parallelTests = List.of(
            new TestCase("testBackendNames", () -> testBackendNames()),
            new TestCase("testIdentifierTranslation", () -> testIdentifierTranslation()),
            new TestCase("testClassNameDerivation", () -> testClassNameDerivation()),
            new TestCase("testEmissionSmoke", () -> testEmissionSmoke()),
            new TestCase("testUnsupportedConstructsRejected", () -> testUnsupportedConstructsRejected()),
            new TestCase("testWhileLoops", () -> testWhileLoops()),
            new TestCase("testWhileFalseBodySkipped", () -> testWhileFalseBodySkipped()),
            new TestCase("testWhileHoistedConditionPerIteration", () -> testWhileHoistedConditionPerIteration()),
            new TestCase("testWhileContinueTargetsWhileInsideTransformedFor", () -> testWhileContinueTargetsWhileInsideTransformedFor()),
            new TestCase("testWhileLoopModuleFieldDominanceGuards", () -> testWhileLoopModuleFieldDominanceGuards()),
            new TestCase("testWhileModuleLevelReturnRejected", () -> testWhileModuleLevelReturnRejected()),
            new TestCase("testWhileUseBeforeDeclarationRejected", () -> testWhileUseBeforeDeclarationRejected()),
            new TestCase("testLoopCondHelperCollision", () -> testLoopCondHelperCollision()),
            new TestCase("testTemplateLiterals", () -> testTemplateLiterals()),
            new TestCase("testPrimitiveArrays", () -> testPrimitiveArrays()),
            new TestCase("testArrayRuntimeErrorCodes", () -> testArrayRuntimeErrorCodes()),
            new TestCase("testArrayEvaluationOrderHoisted", () -> testArrayEvaluationOrderHoisted()),
            new TestCase("testArrayReadComparisonNilSemantics", () -> testArrayReadComparisonNilSemantics()),
            new TestCase("testArrayEvalOrderSideEffectingReceiver", () -> testArrayEvalOrderSideEffectingReceiver()),
            new TestCase("testArrayReadComparisonBothReadsOrder", () -> testArrayReadComparisonBothReadsOrder()),
            new TestCase("testArrayReadComparisonPlainLeftOperandOrder", () -> testArrayReadComparisonPlainLeftOperandOrder()),
            new TestCase("testArrayBoundaryLessReadPositions", () -> testArrayBoundaryLessReadPositions()),
            new TestCase("testArrayDeleteRejected", () -> testArrayDeleteRejected()),
            new TestCase("testBytesArrayPastEndReadsYieldTheDealNull", () -> testBytesArrayPastEndReadsYieldTheDealNull()),
            new TestCase("testArrayUnsupportedElementTypesRejected", () -> testArrayUnsupportedElementTypesRejected()),
            new TestCase("testArrayUseBeforeDeclarationGuards", () -> testArrayUseBeforeDeclarationGuards()),
            new TestCase("testNullReturnSideEffects", () -> testNullReturnSideEffects()),
            new TestCase("testNullTypedInitializers", () -> testNullTypedInitializers()),
            new TestCase("testNullTypedCapturesWithReassignment", () -> testNullTypedCapturesWithReassignment()),
            new TestCase("testNullEquality", () -> testNullEquality()),
            new TestCase("testStandaloneExpressionStatements", () -> testStandaloneExpressionStatements()),
            new TestCase("testNumberModStringAndStderrRuntime", () -> testNumberModStringAndStderrRuntime()),
            new TestCase("testModuleLevelStatements", () -> testModuleLevelStatements()),
            new TestCase("testShadowedInitializer", () -> testShadowedInitializer()),
            new TestCase("testParameterShadowing", () -> testParameterShadowing()),
            new TestCase("testClassSlice", () -> testClassSlice()),
            new TestCase("testLegacyGenerateOverloadChain", () -> testLegacyGenerateOverloadChain()),
            new TestCase("testTypeDescriptorEmitter", () -> testTypeDescriptorEmitter()),
            new TestCase("testSharedCheckSeam", () -> testSharedCheckSeam()),
            new TestCase("testSharedCheckSeamCanonicalParsing", () -> testSharedCheckSeamCanonicalParsing()),
            new TestCase("testNullableSlice", () -> testNullableSlice()),
            new TestCase("testAsyncSlice", () -> testAsyncSlice()),
            new TestCase("testJsonableSlice", () -> testJsonableSlice()),
            new TestCase("testJsonOriginLiterals", () -> testJsonOriginLiterals()),
            new TestCase("testJsonStdlibBoundary", () -> testJsonStdlibBoundary()),
            new TestCase("testImportedClassValues", () -> testImportedClassValues()),
            new TestCase("testFunctionValues", () -> testFunctionValues()),
            new TestCase("testSharedCarrierShapeEncoding", () -> testSharedCarrierShapeEncoding()),
            new TestCase("testSharedShapeCollectionOrder", () -> testSharedShapeCollectionOrder()),
            new TestCase("testSharedCarrierCheckBehaviors", () -> testSharedCarrierCheckBehaviors()),
            new TestCase("testSharedCarrierCrossModuleIdentity", () -> testSharedCarrierCrossModuleIdentity()),
            new TestCase("testSharedCarrierHostClassShapes", () -> testSharedCarrierHostClassShapes()),
            new TestCase("testHostClassArraySeamRuntime", () -> testHostClassArraySeamRuntime()),
            new TestCase("testSharedCarrierIndirectClassShape", () -> testSharedCarrierIndirectClassShape()),
            new TestCase("testCrossModuleFunctionValues", () -> testCrossModuleFunctionValues()),
            new TestCase("testUseBeforeDeclarationRejected", () -> testUseBeforeDeclarationRejected()),
            new TestCase("testFunctionBodyModuleFieldAccessGuards", () -> testFunctionBodyModuleFieldAccessGuards()),
            new TestCase("testAssignmentBeforeDeclarationRejected", () -> testAssignmentBeforeDeclarationRejected()),
            new TestCase("testDeadCodeAfterNonCompletingStatements", () -> testDeadCodeAfterNonCompletingStatements()),
            new TestCase("testRuntimeErrorCodes", () -> testRuntimeErrorCodes()),
            new TestCase("testIntSafeRange", () -> testIntSafeRange()),
            new TestCase("testJavaLangNameCollisions", () -> testJavaLangNameCollisions()),
            new TestCase("testElseIfChainUseBeforeDeclaration", () -> testElseIfChainUseBeforeDeclaration()),
            new TestCase("testNonFiniteNumberLiterals", () -> testNonFiniteNumberLiterals()),
            new TestCase("testShortCircuitPreservation", () -> testShortCircuitPreservation()),
            new TestCase("testEvaluationOrderPreservation", () -> testEvaluationOrderPreservation()),
            new TestCase("testStringScalarOrdering", () -> testStringScalarOrdering()),
            new TestCase("testModuleLevelCallReadingLaterField", () -> testModuleLevelCallReadingLaterField()),
            new TestCase("testModuleLevelCallBeforeFunctionDeclarationRejected", () -> testModuleLevelCallBeforeFunctionDeclarationRejected()),
            new TestCase("testRunnerModuleErrorCodeWithExport", () -> testRunnerModuleErrorCodeWithExport()),
            new TestCase("testProfilePlumbIntMode", () -> testProfilePlumbIntMode()),
            new TestCase("testInt32TimeBoundary", () -> testInt32TimeBoundary()),
            new TestCase("testEmissionSeamFieldSurfaceAndMessageSplit",
                () -> testEmissionSeamFieldSurfaceAndMessageSplit()),
            new TestCase("testArithmeticRaiseSiteOrigins",
                () -> testArithmeticRaiseSiteOrigins()),
            new TestCase("testInt32BoundarySeamSites", () -> testInt32BoundarySeamSites()),
            new TestCase("testInt32DeclaredBoundaryMatrix", () -> testInt32DeclaredBoundaryMatrix()),
            new TestCase("testInt32EdgeMatrix", () -> testInt32EdgeMatrix()),
            new TestCase("testInt32NumberPowBand", () -> testInt32NumberPowBand()),
            new TestCase("testInt32NumPowHelperCollision", () -> testInt32NumPowHelperCollision()),
            new TestCase("testInt32ArrayAndFieldBoundaries", () -> testInt32ArrayAndFieldBoundaries()),
            new TestCase("testBytesRuntimeLane", () -> testBytesRuntimeLane()),
            new TestCase("testOriginThreadingSurface", () -> testOriginThreadingSurface()),
            new TestCase("testErrorSnapshotOriginLiterals",
                () -> testErrorSnapshotOriginLiterals()),
            new TestCase("testOriginThreadingHelperCollisions",
                () -> testOriginThreadingHelperCollisions()),
            new TestCase("testDeclaredBoundaryOrigins", () -> testDeclaredBoundaryOrigins()),
            new TestCase("testUserThrowOrigins", () -> testUserThrowOrigins()),
            new TestCase("testRecursiveBytesClosureLane", () -> testRecursiveBytesClosureLane()),
            new TestCase("testCommonShadowInvocationPipeline", () -> testCommonShadowInvocationPipeline()),
            new TestCase("testLegacyByteCompat", () -> testLegacyByteCompat()),
            new TestCase("testOrchestratorJvmBackend", () -> testOrchestratorJvmBackend()),
            new TestCase("testOrchestratorDefaultStaysLua", () -> testOrchestratorDefaultStaysLua()),
            new TestCase("testOrchestratorJvmRejectsUnsupported", () -> testOrchestratorJvmRejectsUnsupported()),
            new TestCase("testOrchestratorJvmImportSupported", () -> testOrchestratorJvmImportSupported()),
            new TestCase("testStdlibCallEmission", () -> testStdlibCallEmission()),
            new TestCase("testStdlibTableBoundaryAccepted", () -> testStdlibTableBoundaryAccepted()),
            new TestCase("testStdlibExecution", () -> testStdlibExecution()),
            new TestCase("testStdlibSqrtNegativeRuntimeError", () -> testStdlibSqrtNegativeRuntimeError()),
            new TestCase("testStdlibScalarSemantics", () -> testStdlibScalarSemantics()),
            new TestCase("testEntryModuleEmitsJvmEntryPoint", () -> testEntryModuleEmitsJvmEntryPoint()),
            new TestCase("testEntryGateBackendE6004", () -> testEntryGateBackendE6004()),
            new TestCase("testEntryE6004ProgramSpanAnchors", () -> testEntryE6004ProgramSpanAnchors()),
            new TestCase("testJsonableSyntheticE6000Anchor", () -> testJsonableSyntheticE6000Anchor()),
            new TestCase("testStringForOfScalarIteration", () -> testStringForOfScalarIteration()),
            new TestCase("testArrayForOfRefElementShapes", () -> testArrayForOfRefElementShapes()),
            new TestCase("testCatchVarCapturedByNestedFunction", () -> testCatchVarCapturedByNestedFunction()),
            new TestCase("testBoundaryStringValidation", () -> testBoundaryStringValidation()),
            new TestCase("testStdlibTimeNowMillis", () -> testStdlibTimeNowMillis()),
            new TestCase("testStdlibHelperNameCollisions", () -> testStdlibHelperNameCollisions()),
            new TestCase("testOrchestratorJvmStdlibImport", () -> testOrchestratorJvmStdlibImport()),
            new TestCase("testOrchestratorJvmDeclarationImportRejected", () -> testOrchestratorJvmDeclarationImportRejected()),
            new TestCase("testHostAbiSlice", () -> testHostAbiSlice()),
            new TestCase("testOrchestratorJvmClassCollision", () -> testOrchestratorJvmClassCollision()),
            new TestCase("testModuleImports", () -> testModuleImports()),
            new TestCase("testModuleClassIsolation", () -> testModuleClassIsolation()),
            new TestCase("testModuleUnusedImportLoadTime", () -> testModuleUnusedImportLoadTime()),
            new TestCase("testModuleImportBackendEmission", () -> testModuleImportBackendEmission()),
            new TestCase("testModuleImportUseBeforeImportRejected", () -> testModuleImportUseBeforeImportRejected()),
            new TestCase("testOrchestratorJvmSourceMapWarning", () -> testOrchestratorJvmSourceMapWarning()),
            new TestCase("testStrictBackendField", () -> testStrictBackendField()),
            new TestCase("testCliBackendFlag", () -> testCliBackendFlag()),
            new TestCase("testIrDumpExactMigration", () -> testIrDumpExactMigration()));

        int workers = Math.max(1, Math.min(
            Integer.getInteger("deal.test.jobs", DEFAULT_JOBS),
            parallelTests.size()));
        ExecutorService pool = Executors.newFixedThreadPool(workers);
        try {
            List<Future<?>> futures = new ArrayList<>();
            for (TestCase test : parallelTests) {
                futures.add(pool.submit(() -> runTestCaseWorker(test)));
            }
            for (Future<?> future : futures) {
                future.get();
            }
        } catch (Exception e) {
            failed.incrementAndGet();
            System.err.println("FAIL: harness exception: " + e);
            e.printStackTrace(System.err);
        } finally {
            pool.shutdownNow();
        }
        cleanup();

        System.out.println();
        System.out.println("=== JVM Backend Test Summary ===");
        System.out.println("Passed: " + passed.get() + ", Failed: "
            + failed.get());
        if (failed.get() > 0) {
            System.exit(1);
        }
    }

    private static void check(boolean condition, String message) {
        if (condition) {
            passed.incrementAndGet();
        } else {
            failed.incrementAndGet();
            System.err.println("FAIL: " + message);
        }
    }

    private static void fail(String message) {
        failed.incrementAndGet();
        System.err.println("FAIL: " + message);
    }

    /** One named test method for the worker pool (ISSUE-0274). */
    private record TestCase(String name, TestBody body) { }

    /** A test method body: per-test isolated, run once per test. */
    @FunctionalInterface
    private interface TestBody {
        void run() throws Exception;
    }

    /**
     * Runs one test method on a worker thread with its own output
     * buffer, flushed as one contiguous block under the console lock
     * when the method finishes — the legacy JSON conformance harness worker
     * pattern at per-test granularity (ISSUE-0274).
     */
    private static void runTestCaseWorker(TestCase test) {
        StringBuilder buffer = new StringBuilder();
        OUTPUT_BUFFER.set(buffer);
        try {
            test.body().run();
        } catch (Throwable t) {
            System.err.println("FAIL: test method '" + test.name()
                + "' threw: " + t);
            t.printStackTrace(System.err);
            failed.incrementAndGet();
        } finally {
            OUTPUT_BUFFER.remove();
            synchronized (CONSOLE_LOCK) {
                System.out.print(buffer);
            }
        }
    }

    /**
     * Routes every write to the current thread's output buffer; threads
     * without a buffer (the main thread before/after the worker pool)
     * write straight through to the real stream under the console lock.
     */
    private static final class DispatchStream extends OutputStream {
        private final OutputStream sink;
        private final boolean stderrSide;

        DispatchStream(OutputStream sink, boolean stderrSide) {
            this.sink = sink;
            this.stderrSide = stderrSide;
        }

        @Override
        public void write(int b) {
            OutputStream capture = stderrSide ? ERR_CAPTURE.get() : null;
            if (capture != null) {
                try {
                    capture.write(b);
                } catch (IOException ignored) {
                }
                return;
            }
            StringBuilder buffer = OUTPUT_BUFFER.get();
            if (buffer != null) {
                buffer.append((char) b);
                return;
            }
            synchronized (CONSOLE_LOCK) {
                try {
                    sink.write(b);
                } catch (IOException ignored) {
                }
            }
        }

        @Override
        public void write(byte[] b, int off, int len) {
            OutputStream capture = stderrSide ? ERR_CAPTURE.get() : null;
            if (capture != null) {
                try {
                    capture.write(b, off, len);
                } catch (IOException ignored) {
                }
                return;
            }
            StringBuilder buffer = OUTPUT_BUFFER.get();
            if (buffer != null) {
                buffer.append(new String(b, off, len, StandardCharsets.UTF_8));
                return;
            }
            synchronized (CONSOLE_LOCK) {
                try {
                    sink.write(b, off, len);
                } catch (IOException ignored) {
                }
            }
        }

        @Override
        public void flush() {
            OutputStream capture = stderrSide ? ERR_CAPTURE.get() : null;
            if (capture != null) {
                try {
                    capture.flush();
                } catch (IOException ignored) {
                }
                return;
            }
            if (OUTPUT_BUFFER.get() == null) {
                synchronized (CONSOLE_LOCK) {
                    try {
                        sink.flush();
                    } catch (IOException ignored) {
                    }
                }
            }
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static Path writeFile(String relativePath, String content) throws IOException {
        Path file = tmpDir.get().resolve(relativePath);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file;
    }

    private static void cleanup() {
        for (Path dir : tmpDirs) {
            try {
                Files.walk(dir).sorted(Comparator.reverseOrder())
                    .forEach(f -> { try { Files.deleteIfExists(f); } catch (IOException ignored) {} });
            } catch (IOException ignored) {}
        }
    }

    /** Result of the real frontend pipeline (lexer → parser → resolver → checker). */
    private record Frontend(ProgramNode program, CheckResult checkResult,
                            List<CompilerDiagnostic> errors) {}

    // E9999 is the project's test-only pseudo code for a NameResolver
    // exception (the ConformanceTest precedent); it uses the deprecated
    // synthetic factory with an anchor note naming the fixture source
    // (D5/verification 6), and this suppression keeps the build
    // warning-free.
    @SuppressWarnings("deprecation")
    private static Frontend compileFrontend(String source, String filename) {
        return compileFrontend(source, filename,
            StubModuleResolver.acceptingUnknownModules());
    }

    /** Frontend compile with an explicit module resolver (ISSUE-0096 module
     * probes: a fixed export map accepts namespace imports without an
     * orchestrator). */
    @SuppressWarnings("deprecation")
    private static Frontend compileFrontend(String source, String filename,
                                            ModuleResolver moduleResolver) {
        List<CompilerDiagnostic> errors = new ArrayList<>();

        LexResult lex = new Lexer(source, filename).tokenize();
        for (CompilerDiagnostic d : lex.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (lex.hasErrors()) {
            return new Frontend(null, null, errors);
        }

        Parser parser = new Parser(lex.tokens(), filename, lex.directiveEvents());
        ParseResult parse = parser.parse();
        for (CompilerDiagnostic d : parse.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (parse.hasErrors()) {
            return new Frontend(null, null, errors);
        }

        // Post-parse module shape validation (v1.2 module top level:
        // E1048/E1049/E1050/E1051), mirroring the orchestrator pipeline —
        // the parser alone no longer rejects v1.1 module shapes.
        for (CompilerDiagnostic d : ModuleShapeValidator.validate(parse.program(),
                filename, filename.endsWith(".d.deal"))) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }
        if (!errors.isEmpty()) {
            return new Frontend(null, null, errors);
        }

        NameResolver nr = new NameResolver(filename, moduleResolver);
        SymbolTable symTable;
        try {
            symTable = nr.resolve(parse.program());
        } catch (Exception e) {
            errors.add(CompilerDiagnostic.synthetic("E9999", "error",
                e.getMessage(), filename,
                "missing anchor: fixture source '" + filename + "'"));
            return new Frontend(null, null, errors);
        }
        for (CompilerDiagnostic d : nr.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }

        CheckResult result = TypeChecker.check(filename, symTable, nr, parse.program());
        for (CompilerDiagnostic d : result.diagnostics()) {
            if ("error".equals(d.severity())) {
                errors.add(d);
            }
        }

        return new Frontend(parse.program(), result, errors);
    }

    private record ExecResult(String output, int exitCode) {}

    /**
     * Compiles the generated artifact with the javac frontend in-process
     * ({@code StubModuleResolver.compileWithJavac} — the identical
     * javac passes the binary runs; ISSUE-0109 gate-time work, the
     * several hundred spawn sites here each paid a full JVM boot) and
     * executes it with {@code java} in a subprocess — artifact execution
     * stays the same contract the conformance adapter enforces.
     */
    private static ExecResult compileAndRunJvm(String source, String name)
            throws Exception {
        Frontend f = compileFrontend(source, "jvmtest-" + name + ".deal");
        if (!f.errors().isEmpty()) {
            throw new RuntimeException("frontend errors: " + f.errors());
        }
        // The sourcePath must equal the checker's module path: the
        // checker types with the source FILENAME ("jvmtest-<name>.deal"),
        // and the backend's locality predicate (ISSUE-0095) recognizes a
        // local Type.Class by its module path matching the backend-held
        // module path or source path — the same alignment the
        // legacy JSON conformance harness adapter uses.
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-" + name + ".deal", "Main");
        if (res.hasErrors()) {
            throw new RuntimeException("codegen errors: " + res.diagnostics());
        }

        Path dir = Files.createTempDirectory("jvmtest_run_");
        Files.writeString(dir.resolve("Main.java"), res.source());
        Files.writeString(dir.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(f.program(), "Main"));

        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(dir,
            List.of("Main.java", "JvmConformanceRunner.java"), javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed: " + javacErr);
        }

        ProcessBuilder java = new ProcessBuilder("java", "-cp",
            dir.toString(), "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();

        try {
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(p -> { try { Files.deleteIfExists(p); } catch (IOException ignored) {} });
        } catch (IOException ignored) {}

        return new ExecResult(out, exit);
    }

    /**
     * Compiles every {@code .java} artifact in {@code dir} together with a
     * generated runner (auto-invoking the entry program's zero-arity
     * exports) with the javac frontend in-process
     * ({@code StubModuleResolver.compileWithJavac}; ISSUE-0109
     * gate-time work) and executes with {@code java} in a subprocess —
     * artifact execution stays the same contract the conformance adapter
     * enforces for multi-module fixtures.
     */
    private static ExecResult runJvmArtifacts(Path dir, ProgramNode entryProgram,
                                              String entryClass) throws Exception {
        Files.writeString(dir.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(entryProgram, entryClass));

        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(dir)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                  .sorted()
                  .forEach(p -> javaFiles.add(p.getFileName().toString()));
        }
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(dir,
            javaFiles, javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed: " + javacErr);
        }

        ProcessBuilder java = new ProcessBuilder("java", "-cp", dir.toString(),
            "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        return new ExecResult(out, exit);
    }

    /**
     * A fixed-export module resolver for backend-level module probes
     * (ISSUE-0096): the real NameResolver/TypeChecker accept namespace
     * imports without an orchestrator.
     */
    private static final class FixedModuleResolver implements ModuleResolver {
        private final Map<String, Map<String, Type>> modules;

        FixedModuleResolver(Map<String, Map<String, Type>> modules) {
            this.modules = modules;
        }

        @Override
        public Map<String, Type> resolveModule(String modulePath,
                                               String importingModule,
                                               Set<String> modulesInProgress)
                throws ModuleNotFoundException {
            Map<String, Type> exports = modules.get(modulePath);
            if (exports == null) {
                throw new ModuleNotFoundException("Module not found: " + modulePath);
            }
            return exports;
        }

        @Override
        public Symbol.ClassSymbol resolveClassSymbol(String className,
                                                      String modulePath,
                                                      String importingModule)
                throws ModuleNotFoundException {
            return null;
        }
    }

    // =========================================================================
    // Tests
    // =========================================================================

    private static void testBackendNames() {
        System.out.println("-- Backend names --");

        check(Backend.fromCliName("lua").orElse(null) == Backend.LUAJIT,
            "'lua' selects LuaJIT");
        check(Backend.fromCliName("luajit").orElse(null) == Backend.LUAJIT,
            "'luajit' selects LuaJIT");
        check(Backend.fromCliName("jvm").orElse(null) == Backend.JVM,
            "'jvm' selects JVM");
        check(Backend.fromCliName("JVM").orElse(null) == Backend.JVM,
            "backend names are case-insensitive");
        check(Backend.fromCliName("wasm").isEmpty(), "unknown backend is empty");
        check(Backend.fromCliName(null).isEmpty(), "null backend name is empty");
        check(Backend.LUAJIT.cliName().equals("luajit"), "LuaJIT cli name");
        check(Backend.JVM.cliName().equals("jvm"), "JVM cli name");
    }

    private static void testIdentifierTranslation() {
        System.out.println("-- Identifier translation --");

        check(JvmBackend.javaName("x").equals("x"), "plain identifier unchanged");
        check(JvmBackend.javaName("int").equals("_int"),
            "Java keyword gets reserved-word prefix");
        check(JvmBackend.javaName("class").equals("_class"),
            "Java keyword 'class' translated");
        check(JvmBackend.javaName("_").equals("$u"), "'_' escaped");
        check(JvmBackend.javaName("_foo").equals("$ufoo"),
            "leading underscore escaped");
        check(JvmBackend.javaName("$bar").equals("$dbar"),
            "dollar escaped");

        // Injectivity: translations are pairwise distinct and reserved-word
        // prefixes can never collide with escaped identifiers.
        List<String> sample = List.of("int", "_int", "class", "_class", "x",
            "_x", "$x", "$dx", "_", "__", "$", "$$", "foo", "_foo", "$foo",
            "new", "_new", "switch", "_switch", "long", "_long");
        for (int i = 0; i < sample.size(); i++) {
            for (int j = i + 1; j < sample.size(); j++) {
                check(!JvmBackend.javaName(sample.get(i))
                        .equals(JvmBackend.javaName(sample.get(j))),
                    "translation is injective for '" + sample.get(i)
                        + "' vs '" + sample.get(j) + "'");
            }
        }
    }

    private static void testClassNameDerivation() {
        System.out.println("-- Class name derivation --");

        check(JvmBackend.classNameFor("main").equals("Main"),
            "simple module → Main");
        // ISSUE-0091 rework: names derive from the FULL module path so
        // app/main and sub/main can never silently overwrite each other.
        check(JvmBackend.classNameFor("app.main").equals("AppMain"),
            "dotted path → every segment contributes");
        check(JvmBackend.classNameFor("app/sub/main").equals("AppSubMain"),
            "slashed path → every segment contributes");
        check(!JvmBackend.classNameFor("app/main").equals(
                JvmBackend.classNameFor("sub/main")),
            "app/main and sub/main derive distinct class names");
        check(JvmBackend.classNameFor("jvm_main").equals("Jvm_main"),
            "underscore segment kept");
        check(JvmBackend.classNameFor("jvm-fixture").equals("Jvm_fixture"),
            "invalid chars sanitized");
        check(JvmBackend.classNameFor("").equals("Main"),
            "empty path → Main");
    }

    private static void testEmissionSmoke() {
        System.out.println("-- JVM emission smoke --");

        String source = """
            import * as console from "std/console"

            function add(a: int, b: int): int { return a + b; }

            function classify(n: int): int {
              if (n < 0) {
                return 0;
              } else if (n === 0) {
                return 1;
              } else {
                return 2;
              }
            }

            export function test(): int {
              let x: int = add(1, 2);
              let s: string = "lit" + "eral";
              let b: boolean = !false;
              let n: number = number(7);
              let i2: int = int(3.0);
              let z: null = null;
              console.log(s);
              return classify(x - 3) * 10 + int(n) + i2;
            }
            """;

        Frontend f = compileFrontend(source, "jvmtest-smoke.deal");
        check(f.errors().isEmpty(), "smoke frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;

        JvmBackend.JvmCodegenResult res =
            JvmBackend.generate(f.program(), f.checkResult(), "jvmtest-smoke.deal", "main");
        check(!res.hasErrors(), "smoke codegen clean: " + res.diagnostics());
        check(res.className().equals("Main"), "class name from module path");
        if (res.hasErrors()) return;

        String java = res.source();
        check(java.contains("public final class Main"), "class declaration");
        // v1.2 module top level has no lets, so no module-field emission
        // surface exists in the smoke shape.
        check(java.contains("static long add(long a, long b)"),
            "function → static method with mapped types");
        check(hasOriginCall(java, "return intAdd(a, b,"),
            "checked int add carries the compile-time origin literals");
        check(java.contains("else if ("), "else-if chain");
        check(java.contains("java.lang.System.out.println("), "console.log → java.lang.System.out");
        check(hasOriginCall(java, "intFromNumber(3.0,"),
            "int() intrinsic carries the compile-time origin literals");
        check(java.contains("numberFromInt(7L)"), "number() intrinsic");
        check(java.contains("long x = add(1L, 2L);"), "local with int literals");
        check(java.contains("(\"lit\" + \"eral\")"), "string concatenation");
        check(java.contains("(!"), "boolean not");
        check(java.contains("Void z = null;"), "null-typed local from null literal");
        check(java.contains("public static long test()"), "exported function public");
        check(java.contains("static final class DealError"), "runtime error class");
        check(java.contains("static long intPow("), "pow helper emitted");
        check(!java.contains("nullAnd"),
            "null-typed calls are hoisted as pre-statements, not nullAnd-wrapped");
        check(!java.contains(" -> "),
            "emitted code contains no lambdas (capture-safety guarantee; "
                + "wrapper descriptor strings may contain the arrow glyph "
                + "without spaces, e.g. (int,int)->int)");
        check(!java.contains("__rt"), "no Lua runtime references");
    }

    private static void testUnsupportedConstructsRejected() {
        System.out.println("-- Unsupported constructs → E6000 --");

        record Case(String what, String source) {}
        List<Case> cases = List.of(
            new Case("array of nullable table elements", """
                export function test(): null {
                  let xs: (table | null)[] = [];
                }
                """),
            new Case("nullable table type", """
                export function test(): null {
                  let t: table | null = null;
                }
                """),
            new Case("nested class declaration", """
                export function test(): int {
                  class Inner { v: int = 0; }
                  return 1;
                }
                """),
            new Case("unused non-console module import", """
                import * as m from "./other"
                export function test(): int { return 1; }
                """),
            new Case("function-typed class field", """
                class Holder { cb: (x: int) => int; }
                export function test(): int { return 1; }
                """),
            new Case("self-referential initializer", """
                export function test(): int {
                  let x: int = x + 1;
                  return x;
                }
                """),
            new Case("use of local before its declaration", """
                import * as console from "std/console"
                export function test(): null {
                  console.log(x);
                  let x: string = "later";
                }
                """),
            new Case("function colliding with runtime helper", """
                function intAdd(a: int, b: int): int { return a + b; }
                export function test(): int { return intAdd(1, 2); }
                """)
        );

        for (Case c : cases) {
            Frontend f = compileFrontend(c.source, "jvmtest-unsupported.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept unsupported case '" + c.what()
                    + "' (the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f.program(), f.checkResult(),
                    "jvmtest-unsupported.deal", "main");
            check(res.hasErrors(), "backend rejects " + c.what());
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 diagnostic for " + c.what() + ": " + res.diagnostics());
        }

        // ISSUE-0102: the shapes this slice promoted out of the E6000
        // rejection list now compile (each generates an artifact the
        // runtime fixtures above also execute through javac + java).
        List<Case> promoted = List.of(
            new Case("async function expression (ISSUE-0304)", """
                export function test(): null {
                  let f: async () => int = async function(): int { return 5; };
                  return null;
                }
                """),
            new Case("optional class field", """
                class Point { x?: int; }
                export function test(): int { return 1; }
                """),
            new Case("nested array type", """
                export function test(): int {
                  let rows: int[][] = [[1, 2], [3, 4]];
                  return rows[0][1];
                }
                """),
            new Case("unused std/json import (ISSUE-0302)", """
                import * as j from "std/json"
                export function test(): int { return 1; }
                """),
            new Case("array of function elements", """
                function add1(x: int): int { return x + 1; }
                export function test(): int {
                  let fs: ((x: int) => int)[] = [add1];
                  return fs[0](3);
                }
                """),
            new Case("table field read with a primitive target type", """
                export function test(): int {
                  let t: table = { item: 5 };
                  let n: int = t.item;
                  return n;
                }
                """),
            new Case("table field assignment", """
                export function test(): int {
                  let t: table = { item: 5 };
                  t.item = 6;
                  return 1;
                }
                """),
            new Case("class-typed class field", """
                class Inner { v: int = 0; }
                class Outer { inner: Inner = {}; }
                export function test(): int { return 1; }
                """),
            new Case("stdlib module import whose functions take table values", """
                import * as t from "std/table"
                export function test(): int { return 1; }
                """),
            new Case("throw", """
                export function test(): null {
                  throw { code: "E_TEST", message: "x" };
                  return;
                }
                """)
        );
        for (Case c : promoted) {
            Frontend f = compileFrontend(c.source, "jvmtest-unsupported.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept promoted case '" + c.what()
                    + "': " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f.program(), f.checkResult(),
                    "jvmtest-unsupported.deal", "main");
            check(!res.hasErrors(),
                "backend now accepts " + c.what() + ": " + res.diagnostics());
        }

        // Cross-module function-value flow on the shared $DealRt
        // carriers (jvm-function-values-slice: the four former
        // E6000 rejection pins are runtime pins now — ISSUE-0301). The
        // emission-shape pins here assert the promoted forms: the
        // callback argument crosses as the shared wrapper field, the
        // arity-extension argument carries the imported parameter
        // boundary's E8010 raising construction, and the returned
        // function value / call-result callee hold the SAME shared
        // wrapper class the caller types.
        Map<String, Map<String, Type>> xmodLib = Map.of(
            "./lib", Map.of(
                "apply", Types.func(List.of(
                    Types.func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE),
                    Type.Int.INSTANCE), Type.Int.INSTANCE),
                "apply2", Types.func(List.of(
                    Types.func(List.of(Type.Int.INSTANCE, Type.String.INSTANCE),
                        Type.Int.INSTANCE),
                    Type.Int.INSTANCE), Type.Int.INSTANCE),
                "picker", Types.func(List.of(),
                    Types.func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE))));
        record XmodPin(String what, String source, String emission) {}
        List<XmodPin> xmodPins = List.of(
            new XmodPin("callback passed into an imported module call", """
                import * as lib from "./lib"
                function inc(x: int): int { return x + 1; }
                export function test(): int { return lib.apply(inc, 41); }
                """, "Lib.apply(inc$fn, 41L)"),
            new XmodPin("arity-extension adapter argument to an imported module call", """
                import * as lib from "./lib"
                function inc(x: int): int { return x + 1; }
                export function test(): int { return lib.apply2(inc, 41); }
                """, "Lib.apply2(new $DealRt.Fn2_I_S_R_I() { { if (!checkSig(\"(int,string)->int\", \"(int)->int\"))"),
            new XmodPin("function value returned from an imported module call", """
                import * as lib from "./lib"
                export function test(): int {
                  let f: (x: int) => int = lib.picker();
                  return f(41);
                }
                """, "$DealRt.Fn1_I_R_I f = Lib.picker();"),
            new XmodPin("imported call result used as a call-result callee", """
                import * as lib from "./lib"
                export function test(): int { return lib.picker()(41); }
                """, "__fn0.invokeAt("));
        for (XmodPin pin : xmodPins) {
            Frontend f = compileFrontend(pin.source(),
                "jvmtest-xmod-carrier.deal", new FixedModuleResolver(xmodLib));
            if (!f.errors().isEmpty()) {
                fail("frontend must accept the shared-carrier shape '"
                    + pin.what() + "': " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-xmod-carrier.deal",
                "main", Map.of("./lib", "lib"));
            check(!res.hasErrors(), "backend accepts " + pin.what() + ": "
                + res.diagnostics());
            check(res.source().contains(pin.emission()),
                "emission shape for " + pin.what() + " (" + pin.emission()
                    + ")");
        }

        // @jsonable optional table field (jvm-jsonable-slice:
        // jvm-jsonable-optional-table-rejected).
        Frontend jsonableF = compileFrontend("""
            // @jsonable
            export class Wrap {
              data?: table;
            }
            export function test(): int { return 1; }
            """, "jvmtest-jsonable-optional-table.deal");
        if (!jsonableF.errors().isEmpty()) {
            fail("frontend must accept the @jsonable optional-table shape "
                + "(the backend rejects it): " + jsonableF.errors());
        } else {
            JvmBackend.JvmCodegenResult jsonableRes = JvmBackend.generate(
                jsonableF.program(), jsonableF.checkResult(),
                "jvmtest-jsonable-optional-table.deal", "main");
            check(jsonableRes.hasErrors(),
                "backend rejects the @jsonable optional table field");
            check(jsonableRes.diagnostics().stream().anyMatch(d ->
                    "E6000".equals(d.code())
                        && ("JVM backend (skeleton) does not support "
                            + "optional table fields of @jsonable class "
                            + "'Wrap' (the read of 'data' yields "
                            + "`table | null`, which stays out of the "
                            + "slice's typed positions) yet").equals(d.message())),
                "E6000 detail text exact for the @jsonable optional table "
                    + "field: " + jsonableRes.diagnostics());
        }
    }


    // =========================================================================
    // ISSUE-0092 semantic slice: while loops and template literals
    // =========================================================================

    private static int occurrences(String haystack, String needle) {
        int n = 0;
        for (int i = 0; (i = haystack.indexOf(needle, i)) >= 0; i += needle.length()) {
            n++;
        }
        return n;
    }

    /** While loops compute through local mutation (the ISSA-0092 slice
     * surface: condition, body block scope, reassignment, return). */
    private static void testWhileLoops() throws Exception {
        System.out.println("-- While loops (javac + java) --");

        ExecResult count = compileAndRunJvm("""
            export function test(): int {
              let i: int = 0;
              let sum: int = 0;
              while (i < 5) {
                i = i + 1;
                sum = sum + i;
              }
              return sum;
            }
            """, "whilecount");
        check(count.exitCode() == 0, "counting while exits 0");
        check(count.output().contains("15"),
            "counting while sums 1..5 → 15: " + count.output());

        ExecResult nested = compileAndRunJvm("""
            export function test(): int {
              let total: int = 0;
              let i: int = 1;
              while (i <= 3) {
                let j: int = 1;
                let inner: int = 0;
                while (j <= i) {
                  inner = inner + j;
                  j = j + 1;
                }
                total = total + inner;
                i = i + 1;
              }
              return total;
            }
            """, "whilenested");
        check(nested.exitCode() == 0, "nested while exits 0");
        check(nested.output().contains("10"),
            "nested while sums triangular numbers → 10: " + nested.output());

        // A while-true loop that returns from inside the body: the emitted
        // condition is routed through loopCond so javac never sees a
        // constant-true condition and the trailing return stays reachable.
        ExecResult until = compileAndRunJvm("""
            export function test(): int {
              let i: int = 0;
              while (true) {
                if (i > 2) {
                  return i;
                }
                i = i + 1;
              }
              return -1;
            }
            """, "whileuntil");
        check(until.exitCode() == 0, "while-true loop exits 0");
        check(until.output().contains("3"),
            "while-true loop returns from inside the body → 3: " + until.output());

        // v1.2 module top level has no statements; the condition
        // re-evaluation shape runs inside a function instead (a
        // module-level while would be a parse error, pinned below).
        ExecResult moduleWhile = compileAndRunJvm("""
            import * as console from "std/console"
            function tick(): null { console.log("tick"); }
            export function test(): int {
              let i: int = 0;
              while (i < 2 && tick() === null) {
                i = i + 1;
              }
              return i;
            }
            """, "whilemodule");
        check(moduleWhile.exitCode() == 0, "while-loop exits 0");
        check(occurrences(moduleWhile.output(), "tick") == 2,
            "while condition re-evaluates per iteration → tick ×2: "
                + moduleWhile.output());
        check(moduleWhile.output().contains("2"),
            "while leaves the local at 2: " + moduleWhile.output());

        // v1.2 grammar gate: the module-level while shape is a frontend
        // parse error (E1049).
        Frontend moduleWhileShape = compileFrontend("""
            import * as console from "std/console"
            while (true) {
              console.log("never");
            }
            export function test(): null { return null; }
            """, "jvmtest-whilemodule-shape.deal");
        check(moduleWhileShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level while rejected with E1049: " + moduleWhileShape.errors());

        // Emission shape: the plain form routes the condition through the
        // loopCond identity helper (never a constant expression) and keeps
        // the body as a Java block.
        Frontend f = compileFrontend("""
            export function test(): int {
              let i: int = 0;
              while (i < 3) {
                i = i + 1;
              }
              return i;
            }
            """, "jvmtest-while-emission.deal");
        check(f.errors().isEmpty(), "while emission probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-while-emission.deal", "main");
            check(!res.hasErrors(), "while emission probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("while (loopCond((i < 3L)))"),
                    "condition routed through loopCond: " + res.source().substring(
                        res.source().indexOf("while"), res.source().indexOf("while") + 60));
                check(res.source().contains("static boolean loopCond(boolean v) { return v; }"),
                    "loopCond identity helper emitted");
                check(!res.source().contains(" -> "),
                    "while emission contains no lambda");
            }
        }
    }

    /** {@code while (false)} never runs its body — emitted as a loop whose
     * non-constant condition keeps the body reachable to javac (JLS
     * §14.21) and never taken at runtime, matching LuaJIT. */
    private static void testWhileFalseBodySkipped() throws Exception {
        System.out.println("-- while (false) body never runs (javac + java) --");

        ExecResult skipped = compileAndRunJvm("""
            export function test(): int {
              let x: int = 1;
              while (false) {
                x = x + 1;
              }
              return x;
            }
            """, "whilefalse");
        check(skipped.exitCode() == 0, "while-false exits 0");
        check(skipped.output().contains("1"),
            "while-false body skipped → 1: " + skipped.output());

        // Emission: the condition is wrapped in loopCond so javac does not
        // see a constant-false condition (whose body would be unreachable).
        Frontend f = compileFrontend("""
            export function test(): int {
              let x: int = 1;
              while (false) {
                x = x + 1;
              }
              return x;
            }
            """, "jvmtest-whilefalse-emission.deal");
        check(f.errors().isEmpty(), "while-false probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-whilefalse-emission.deal", "main");
            check(!res.hasErrors(), "while-false probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("while (loopCond(false))"),
                    "constant-false condition wrapped in loopCond");
            }
        }
    }

    /** A condition whose evaluation hoists a side-effecting null-typed call
     * must re-run that call on EVERY iteration (LuaJIT re-evaluates the
     * condition each time), not once before the loop. */
    private static void testWhileHoistedConditionPerIteration() throws Exception {
        System.out.println("-- While condition hoisted side effects per iteration (javac + java) --");

        ExecResult perIter = compileAndRunJvm("""
            import * as console from "std/console"
            function tick(): null { console.log("tick"); }
            export function test(): int {
              let i: int = 0;
              while (i < 3 && tick() === null) {
                i = i + 1;
              }
              return i;
            }
            """, "whilehoisted");
        check(perIter.exitCode() == 0, "hoisted-condition while exits 0");
        check(occurrences(perIter.output(), "tick") == 3,
            "condition re-evaluates per iteration → tick ×3: " + perIter.output());
        check(perIter.output().contains("3"),
            "loop counts to 3: " + perIter.output());
    }

    /** A DEAL continue inside a while nested in a TRANSFORMED (hoisted)
     * C-style for must target the while — the nearest enclosing loop —
     * never the enclosing for's re-placed-update label. The transformed
     * for pushes its cont$N label onto {@code loopContinueLabels}; the
     * while pushes a null frame over it, so emitContinue emits plain
     * {@code continue;} and Java resolves it to the nearest Java loop
     * (the while). Without the frame the while-level continue emitted
     * {@code break cont$N;} — exiting the for body, running the for
     * update, and silently skipping the while's remaining iterations
     * (LuaJIT prints 10 / 4, the broken JVM shape printed 5 / 2). */
    private static void testWhileContinueTargetsWhileInsideTransformedFor()
            throws Exception {
        System.out.println("-- While continue inside a transformed for (javac + java) --");

        // Runtime: the reviewer's probe shape — a while with a continue
        // nested in a for whose boolean[]-read condition hoists the
        // side-effecting reads into the transformed form.
        ExecResult plain = compileAndRunJvm("""
            export function test(): int {
              let flags: boolean[] = [true, true, true, true, true];
              let n: int = 0;
              for (let i: int = 0; i < 5 && flags[i]; i = i + 1) {
                let j: int = 0;
                while (j < 2) {
                  j = j + 1;
                  n = n + 1;
                  if (j === 1) { continue; }
                }
              }
              return n;
            }
            """, "whilecontintransfor");
        check(plain.exitCode() == 0,
            "while-continue-in-transformed-for exits 0: " + plain.output());
        check(plain.output().contains("10"),
            "the while-level continue stays inside the while → 2 per for "
                + "iteration, 5 iterations → 10 (LuaJIT parity; the broken "
                + "shape printed 5): " + plain.output());

        // Runtime: the hoisted-condition while variant — the continue
        // must re-run the hoisted per-iteration condition side effects
        // (tick) exactly like LuaJIT, not exit the while.
        ExecResult hoisted = compileAndRunJvm("""
            import * as console from "std/console"
            function tick(): null { console.log("tick"); }
            export function test(): int {
              let flags: boolean[] = [true, true];
              let n: int = 0;
              for (let i: int = 0; i < 2 && flags[i]; i = i + 1) {
                let j: int = 0;
                while (j < 2 && tick() === null) {
                  j = j + 1;
                  n = n + 1;
                  if (j === 1) { continue; }
                }
              }
              return n;
            }
            """, "whilehoistedcontintransfor");
        check(hoisted.exitCode() == 0,
            "hoisted-while-continue-in-transformed-for exits 0: "
                + hoisted.output());
        check(occurrences(hoisted.output(), "tick") == 4,
            "the continue re-enters the while head and re-runs the hoisted "
                + "condition side effects → tick ×4: " + hoisted.output());
        check(hoisted.output().contains("4"),
            "the hoisted while counts fully → 4 (the broken shape printed "
                + "2): " + hoisted.output());

        // Emission shape: the for-level continue still routes to the
        // re-placed-update label, the while-level continue stays a plain
        // Java continue targeting the while, and the while body keeps the
        // loopCond-wrapped condition.
        Frontend f = compileFrontend("""
            export function test(): int {
              let flags: boolean[] = [true, true, true, true, true];
              let n: int = 0;
              for (let i: int = 0; i < 5 && flags[i]; i = i + 1) {
                if (i === 2) { continue; }
                let j: int = 0;
                while (j < 2) {
                  j = j + 1;
                  n = n + 1;
                  if (j === 1) { continue; }
                }
              }
              return n;
            }
            """, "jvmtest-whilecont-transfor.deal");
        check(f.errors().isEmpty(),
            "while-continue-transformed-for probe frontend clean: "
                + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-whilecont-transfor.deal", "main");
            check(!res.hasErrors(),
                "while-continue-transformed-for probe codegen clean: "
                    + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("break cont$0;"),
                    "the for-level continue still routes through the "
                        + "re-placed-update label");
                check(occurrences(res.source(), "break cont$0;") == 1,
                    "exactly one label-routed continue (the for-level "
                        + "one) — the while-level continue is not one");
                check(occurrences(res.source(), "continue;") == 1,
                    "exactly one plain `continue;` — the while-level one: "
                        + occurrences(res.source(), "continue;"));
                int whileIdx =
                    res.source().indexOf("while (loopCond((j < 2L))) {");
                int contIdx = res.source().indexOf("continue;");
                check(whileIdx >= 0 && contIdx > whileIdx,
                    "the plain `continue;` sits inside the while body "
                        + "(index " + contIdx + " after " + whileIdx + ")");
                check(res.source().contains("while (loopCond((j < 2L))) {"),
                    "the while body keeps the loopCond-wrapped condition");
            }
        }
    }

    /** Function-body module-field dominance guards walk through while
     * bodies: writes inside a loop body dominate nothing after the loop
     * (the body may run zero times), reads/writes of later-declared
     * fields in a condition or body stay E6000, and the field-declared-
     * first shape stays full parity. */
    private static void testWhileLoopModuleFieldDominanceGuards() throws Exception {
        // v1.2 grammar gate: module-level lets were removed, so the v1.1
        // module-field dominance-guard shapes (function-body reads/writes
        // of later-declared module fields) are frontend parse errors
        // (E1049) before any backend analysis. The in-function loop
        // behavior they guarded is pinned by testWhileLoops above.
        Frontend writeInBody = compileFrontend("""
            function f(): int {
              let i: int = 0;
              while (i < 2) {
                x = x + 1;
                i = i + 1;
              }
              return x;
            }
            let x: int = 1;
            export function test(): int { return f(); }
            """, "jvmtest-while-dominance-write.deal");
        check(writeInBody.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "while-body write shape rejected with E1049: " + writeInBody.errors());

        Frontend readInCond = compileFrontend("""
            function g(): int {
              let i: int = 0;
              while (i < x) {
                i = i + 1;
              }
              return i;
            }
            let x: int = 5;
            export function test(): int { return g(); }
            """, "jvmtest-while-dominance-read.deal");
        check(readInCond.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "while-condition read shape rejected with E1049: " + readInCond.errors());

        Frontend parity = compileFrontend("""
            let x: int = 2;
            function h(): int {
              let i: int = 0;
              while (i < x) {
                i = i + 1;
              }
              return i;
            }
            export function test(): int { return h(); }
            """, "jvmtest-whiledomparity.deal");
        check(parity.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "declared-first module field shape rejected with E1049: " + parity.errors());
    
    }

    /** Module-level while bodies cannot contain return (Java initializers
     * cannot return) — E6000, never an artifact javac rejects. */
    private static void testWhileModuleLevelReturnRejected() {
        // v1.2 grammar gate: a module-level while is a frontend parse
        // error (E1049) — the v1.1 module-level-return E6000 surface is
        // removed with the module-level statement grammar.
        Frontend f = compileFrontend("""
            export function test(): int { return 1; }
            while (true) {
              if (false) {
                return;
              }
            }
            """, "jvmtest-while-module-return.deal");
        check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "module-level while rejected with E1049: " + f.errors());
    
    }

    /** Use-before-declaration detection walks while conditions: a
     * later-declared variable there is E6000, never an artifact javac
     * rejects after the CLI reported success. */
    private static void testWhileUseBeforeDeclarationRejected() {
        System.out.println("-- Use-before-declaration in a while condition → E6000 --");

        Frontend f = compileFrontend("""
            import * as console from "std/console"
            export function test(): null {
              while (x === 0) {
                console.log("looped");
              }
              let x: int = 0;
            }
            """, "jvmtest-while-undeclared.deal");
        check(f.errors().isEmpty(), "while-undeclared frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-while-undeclared.deal", "main");
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())),
                "while condition use-before-declaration is E6000: " + res.diagnostics());
        }
    }

    /** A DEAL function whose mapped signature duplicates the emitted
     * loopCond helper would emit a duplicate Java method — E6000. */
    private static void testLoopCondHelperCollision() {
        System.out.println("-- loopCond helper signature collision → E6000 --");

        Frontend f = compileFrontend("""
            function loopCond(v: boolean): boolean { return v; }
            export function test(): boolean { return loopCond(true); }
            """, "jvmtest-loopcond-collision.deal");
        check(f.errors().isEmpty(), "loopCond collision frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-loopcond-collision.deal", "main");
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())),
                "loopCond helper collision is E6000: " + res.diagnostics());
        }
    }

    /** Template literals lower to string concatenation: interpolated and
     * plain parts, empty parts elided, single-part templates emitted as the
     * literal itself — all string-typed by the checker (E3016 otherwise). */
    private static void testTemplateLiterals() throws Exception {
        System.out.println("-- Template literals (javac + java) --");

        ExecResult run = compileAndRunJvm("""
            export function test(): string {
              let a: string = "alpha";
              let b: string = "beta";
              let t1: string = `x${a}y${b}z`;
              let t2: string = `plain`;
              let t3: string = `${a}b`;
              let t4: string = `x${""}y`;
              return t1 + t2 + t3 + t4;
            }
            """, "templates");
        check(run.exitCode() == 0, "template run exits 0");
        check(run.output().contains("xalphaybetazplainalphabxy"),
            "template interpolations concatenate: " + run.output());

        Frontend f = compileFrontend("""
            export function test(): string {
              let a: string = "alpha";
              let b: string = "beta";
              let t1: string = `x${a}y${b}z`;
              let t2: string = `plain`;
              let t3: string = `${a}b`;
              let t4: string = `x${""}y`;
              return t1 + t2 + t3 + t4;
            }
            """, "jvmtest-template-emission.deal");
        check(f.errors().isEmpty(), "template probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-template-emission.deal", "main");
            check(!res.hasErrors(), "template probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains(
                        "java.lang.String t1 = (\"x\" + a + \"y\" + b + \"z\");"),
                    "interpolated template lowers to concatenation: "
                        + (res.source().contains("t1 =") ? res.source().substring(
                            res.source().indexOf("t1 ="), res.source().indexOf("t1 =") + 50)
                            : "<missing>"));
                check(res.source().contains("java.lang.String t2 = \"plain\";"),
                    "single-part template emits its literal");
                check(res.source().contains("java.lang.String t3 = (a + \"b\");"),
                    "empty leading literal part elided");
                check(res.source().contains("java.lang.String t4 = (\"x\" + \"\" + \"y\");"),
                    "empty INTERPOLATION part kept (it is an expression, like LuaJIT)");
                check(!res.source().contains("unsupported(\"template literals\""),
                    "no template-literal E6000 fallback in the artifact");
            }
        }
    }

    // =========================================================================
    // ISSUE-0094 semantic slice: primitive arrays (literals, indexing,
    // element assignment, .length) with the spec's runtime checks
    // =========================================================================

    /** Primitive arrays compile and run end-to-end (javac + java): int[]/
     * number[]/string[]/boolean[] literals, index reads, element writes,
     * the i == length append (the xs[xs.length] idiom and a plain
     * index-equals-length write), .length reads, aliases sharing one
     * mutable wrapper (stable across append growth), arrays through
     * function parameters/returns, and module-level array fields — with
     * emission assertions for the wrapper/helper lowering. */
    private static void testPrimitiveArrays() throws Exception {
        System.out.println("-- Primitive arrays (javac + java) --");

        ExecResult run = compileAndRunJvm("""
            export function test(): int {
              let xs: int[] = [10, 20, 30];
              xs[1] = 99;
              xs[xs.length] = 40;
              let b: int[] = xs;
              b[0] = 7;
              let ns: number[] = [1.5, 2.5];
              ns[1] = ns[0] + 1.0;
              let ss: string[] = ["a", "b"];
              ss[0] = ss[1] + "x";
              let bs: boolean[] = [true, false];
              bs[1] = bs[0];
              let total: int = xs[0] + xs[1] + xs[2] + xs[3] + xs.length + b.length;
              if (ns[0] === 1.5 && ns[1] === 2.5 && ss[0] === "bx" && bs[0] && bs[1]) {
                return total;
              }
              return 0;
            }
            """, "arrays");
        check(run.exitCode() == 0, "array run exits 0: " + run.output());
        check(run.output().contains("184"),
            "literal/read/write/append/length compute 184 (7+99+30+40 = 176, "
            + "+ xs.length(4) + b.length(4)): " + run.output());

        // Append + alias + param/return shapes.
        ExecResult append = compileAndRunJvm("""
            function fill(xs: int[], v: int): int[] {
              xs[0] = v;
              return xs;
            }
            export function test(): int {
              let xs: int[] = [];
              xs[xs.length] = 1;
              xs[xs.length] = 2;
              xs[2] = 4;
              let ys: int[] = fill(xs, 9);
              return ys[0] + ys[1] + ys[2] + ys.length;
            }
            """, "append");
        check(append.exitCode() == 0, "append run exits 0: " + append.output());
        check(append.output().contains("18"),
            "append + param write computes 18 (9+2+4+3): " + append.output());

        // v1.2 grammar gate: module-level array fields were removed — the
        // v1.1 load-time mutation shape is a frontend parse error (E1049).
        Frontend moduleShape = compileFrontend("""
            let g: int[] = [1, 2];
            g[0] = 5;
            export function test(): int { return g[0] + g[1] + g.length; }
            """, "jvmtest-modarr.deal");
        check(moduleShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level array field rejected with E1049: " + moduleShape.errors());

        // Emission shape: wrapper classes, read/write helper calls, length
        // lowering, and checkInt on int element stores.
        Frontend f = compileFrontend("""
            export function test(): int {
              let xs: int[] = [10, 20];
              xs[1] = 99;
              return xs[0] + xs.length;
            }
            """, "jvmtest-arrays-emission.deal");
        check(f.errors().isEmpty(), "array emission frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrays-emission.deal", "main");
            check(!res.hasErrors(), "array emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("static final class __IntArray"),
                    "shared $DealRt __IntArray wrapper class emitted");
                check(java.contains("new $DealRt.__IntArray(new long[]{10L, 20L})"),
                    "int[] literal lowers to new $DealRt.__IntArray(new long[]{…})");
                String boundaryFile = "Main.java";
                check(java.contains("__intArrayWrite(xs, 1L, 99L, "
                        + "\"jvmtest-arrays-emission.deal\", 3, 3);"),
                    "element write lowers to the __intArrayWrite helper call "
                        + "carrying the index expression origin (3:3)");
                check(java.contains("__intArrayRead(xs, 0L, "
                        + "\"jvmtest-arrays-emission.deal\", 4, 10, "
                        + "\"" + boundaryFile + "\", 4, 10)"),
                    "element read lowers to the __intArrayRead helper call "
                        + "carrying the index expression origin (4:10) and "
                        + "the return-boundary origin");
                check(java.contains("((long) xs.data.length)"),
                    ".length lowers to a wrapped storage-length read");
                check(java.contains("v = checkInt(v, oFile, oLine, oCol);"),
                    "int element stores route through checkInt (E8004) "
                        + "with the origin-threading parameters");
                check(java.contains("i == (long) a.data.length"),
                    "append growth at i == length is present");
                check(java.contains("static boolean __booleanArrayWrite"),
                    "boolean write helper emitted");
                check(java.contains("static java.lang.String __stringArrayRead"),
                    "string read helper emitted");
                check(java.contains("static double __numberArrayRead"),
                    "number read helper emitted");
                check(!res.source().contains("unsupported(\"array"),
                    "no array E6000 fallback in the artifact");
            }
        }
    }

    /** Array runtime checks surface with DEAL error codes: negative read
     * E8002, read past the end E8001 "expected int, got null", negative
     * write E8002, gap write E8002, out-of-safe-range int element write
     * E8004 (the element value check). */
    private static void testArrayRuntimeErrorCodes() throws Exception {
        System.out.println("-- Array runtime error codes (javac + java) --");

        String[][] errorCases = {
            {"int", "let xs: int[] = [1, 2, 3]; return xs[-1];", "E8002", "negative read"},
            {"int", "let xs: int[] = [1, 2, 3]; return xs[99];", "E8001", "oob read"},
            {"int", "let xs: int[] = [1, 2, 3]; xs[-1] = 9; return xs[0];", "E8002", "negative write"},
            {"int", "let xs: int[] = [1, 2, 3]; xs[4] = 9; return xs[0];", "E8002", "gap write"},
            {"int", "let xs: int[] = [1]; xs[0] = 9223372036854775807; return xs[0];", "E8004", "int element check"},
            {"int", "let xs: int[] = []; xs[xs.length] = 9007199254740991; return 0;", null, "append boundary ok"},
            {"int", "let xs: number[] = [1.5]; xs[99] = 2.5; return 0;", "E8002", "number gap write"},
            {"string", "let ss: string[] = [\"a\"]; return ss[-2];", "E8002", "string negative read"},
            {"boolean", "let bs: boolean[] = [true]; return bs[1];", "E8001", "boolean oob read"},
        };
        for (String[] c : errorCases) {
            ExecResult r = compileAndRunJvm(
                "export function test(): " + c[0] + " { " + c[1] + " }", "arrerr");
            if (c[2] == null) {
                check(r.exitCode() == 0, c[3] + " exits 0: " + r.output());
            } else {
                check(r.exitCode() == 1, c[3] + " exits 1: " + r.output());
                check(r.output().contains("DEAL_ERROR_CODE: " + c[2]),
                    c[3] + " reports " + c[2] + ": " + r.output());
            }
        }

        // The boolean element spelling ("expected boolean, got null") is
        // pinned explicitly: the past-end boolean[] read raises the
        // boundary failure with the element-type message, not a generic
        // one.
        ExecResult boolSpelling = compileAndRunJvm(
            "export function test(): boolean { "
            + "let bs: boolean[] = [true]; return bs[1]; }", "arrerrbool");
        check(boolSpelling.exitCode() == 1
                && boolSpelling.output().contains("DEAL_ERROR_CODE: E8001")
                && boolSpelling.output().contains("expected boolean, got null"),
            "the boolean oob read spells 'expected boolean, got null': "
                + boolSpelling.output());

        // The write check runs AFTER the receiver/index/RHS expressions
        // evaluate (spec §Operational semantics rule 3): the RHS's E8004
        // fires before the E8002 bounds check for a gap write with an
        // out-of-range RHS — the JVM evaluates the helper-call arguments
        // left to right, then the helper performs its checks.
        ExecResult order = compileAndRunJvm("""
            export function test(): int {
              let xs: int[] = [1];
              xs[4] = 9223372036854775807;
              return 0;
            }
            """, "arrordercheck");
        check(order.exitCode() == 1, "gap write with out-of-range RHS exits 1: "
            + order.output());
        check(order.output().contains("DEAL_ERROR_CODE: E8004"),
            "the RHS value check (E8004) runs before the bounds check per "
            + "spec rule 3: " + order.output());
    }

    private static void testArrayDeleteRejected() {
        System.out.println("-- Array delete rejected with E6000 --");
        Frontend frontend = compileFrontend("""
            export function main(): null {
              let xs: int[] = [1, 2, 3];
              delete xs[1];
            }
            """, "jvmtest-array-delete.deal");
        check(frontend.errors().isEmpty(),
            "array-delete frontend clean: " + frontend.errors());
        if (frontend.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult result = JvmBackend.generate(
                frontend.program(), frontend.checkResult(),
                "jvmtest-array-delete.deal", "main");
            check(result.hasErrors() && result.diagnostics().stream()
                    .anyMatch(diagnostic -> "E6000".equals(diagnostic.code())),
                "the JVM backend rejects array-index delete with E6000: "
                    + result.diagnostics());
        }
    }

    /** Array evaluation order with hoisted null-typed side effects: the
     * index operand's hoisted print runs before its inline call, which is
     * materialized into a temporary ahead of the RHS's hoisted print —
     * output index-side, index, value-side, value, then the written
     * element. Never a lambda, never an inverted print order. */
    private static void testArrayEvaluationOrderHoisted() throws Exception {
        System.out.println("-- Array evaluation order with hoisted side effects --");

        ExecResult run = compileAndRunJvm("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): int {
              let xs: int[] = [5, 6];
              xs[pick("index", console.log("index-side"))] = pick("value", console.log("value-side"));
              return xs[0];
            }
            """, "arrord");
        check(run.exitCode() == 0, "hoisted array order exits 0: " + run.output());
        check(run.output().contains("index-side\nindex\nvalue-side\nvalue\n0"),
            "hoisted side effects keep left-to-right order: " + run.output());

        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): int {
              let xs: int[] = [5, 6];
              xs[pick("index", console.log("index-side"))] = pick("value", console.log("value-side"));
              return xs[0];
            }
            """, "jvmtest-arrord-emission.deal");
        check(f.errors().isEmpty(), "hoisted array order frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrord-emission.deal", "main");
            check(!res.hasErrors(), "hoisted array order codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(!java.contains(" -> "),
                    "no lambda emitted for array order (spaced arrow; "
                    + "wrapper descriptor strings may carry the unspaced "
                    + "arrow glyph): " + java);
                int sideIdx = java.indexOf("\"index-side\"");
                int tempIdx = java.indexOf("__t0 = pick(");
                int valueIdx = java.indexOf("\"value-side\"");
                check(sideIdx >= 0 && tempIdx >= 0 && valueIdx >= 0
                        && sideIdx < tempIdx && tempIdx < valueIdx,
                    "the inline index call is materialized into __t0 between "
                    + "the index-side and value-side hoisted prints");
                check(java.contains("__intArrayWrite(xs, __t0, "
                        + "pick(\"value\", null), "
                        + "\"jvmtest-arrord-emission.deal\", 5, 3);"),
                    "the write helper call carries the materialized index "
                        + "and the index expression origin (5:3)");
            }
        }
    }

    /** === / !== operand positions with array reads past the end
     * (ISSUE-0094 rework): the spec read-site contract applies no typed
     * boundary at a comparison operand, so LuaJIT reads nil and computes
     * the comparison — the JVM boxed comparison reads must yield the same
     * nil semantics (nil === v false, nil !== v true, nil === nil true)
     * for all four element types instead of raising E8001. Also pins the
     * strict evaluation of the non-read operand (never skipped by a Java
     * short-circuit), the negative-index E8002 that LuaJIT raises
     * unconditionally in the same position, and the boxed-helper emission
     * shape. */
    private static void testArrayReadComparisonNilSemantics() throws Exception {
        System.out.println("-- Array reads in === / !== positions (javac + java) --");

        ExecResult run = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              let ns: number[] = [1.5];
              let ss: string[] = ["a"];
              let bs: boolean[] = [true];
              if (xs[99] === 5) { console.log("bad1"); }
              if (xs[99] !== 5) { console.log("int-neq"); }
              if (xs[99] === xs[99]) { console.log("nil-eq-nil"); }
              if (ns[99] !== 2.5) { console.log("number-neq"); }
              if (ss[99] === "x") { console.log("bad2"); }
              if (ss[99] !== "x") { console.log("string-neq"); }
              if (bs[99] === true) { console.log("bad3"); }
              if (bs[99] !== true) { console.log("boolean-neq"); }
              if (xs[0] === 1 && xs[99] !== 1) { console.log("mixed"); }
            }
            """, "arrcmp");
        check(run.exitCode() == 0, "comparison nil semantics exits 0: " + run.output());
        check(run.output().contains("int-neq")
                && run.output().contains("nil-eq-nil")
                && run.output().contains("number-neq")
                && run.output().contains("string-neq")
                && run.output().contains("boolean-neq")
                && run.output().contains("mixed")
                && !run.output().contains("bad"),
            "nil === v / nil !== v / nil === nil semantics for all four "
            + "element types: " + run.output());

        // The non-read comparison operand always evaluates — the Java
        // null-guard short-circuit must never skip a DEAL-visible effect
        // (LuaJIT evaluates both operands strictly). Both directions.
        ExecResult rhs = compileAndRunJvm("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            export function test(): null {
              let xs: int[] = [1];
              if (xs[99] === mark("rhs", 5)) { console.log("bad-eq"); }
              if (xs[99] !== mark("rhs2", 5)) { console.log("neq-ok"); }
            }
            """, "arrcmprhs");
        check(rhs.exitCode() == 0, "RHS-evaluation shape exits 0: " + rhs.output());
        check(rhs.output().contains("rhs") && rhs.output().contains("rhs2")
                && rhs.output().contains("neq-ok")
                && !rhs.output().contains("bad-eq"),
            "the value operand always evaluates in both directions: "
                + rhs.output());

        ExecResult lhs = compileAndRunJvm("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            export function test(): null {
              let xs: int[] = [1];
              if (mark("lhs", 5) === xs[99]) { console.log("bad-eq"); }
              if (mark("lhs2", 5) !== xs[99]) { console.log("neq-ok"); }
            }
            """, "arrcmplhs");
        check(lhs.exitCode() == 0, "LHS-evaluation shape exits 0: " + lhs.output());
        check(lhs.output().contains("lhs") && lhs.output().contains("lhs2")
                && lhs.output().contains("neq-ok")
                && !lhs.output().contains("bad-eq"),
            "the value operand always evaluates on the left too: "
                + lhs.output());

        // Read-vs-read with only one side past the end: nil === 5 is
        // false, 5 === nil is false, nil !== 5 is true — and the
        // in-bounds elements still compare normally.
        ExecResult rr = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              let ys: int[] = [5];
              if (xs[99] === ys[0]) { console.log("bad-a"); }
              if (ys[0] === xs[99]) { console.log("bad-b"); }
              if (xs[99] !== ys[0]) { console.log("rr-neq"); }
              if (xs[0] === ys[0]) { console.log("bad-c"); }
              if (xs[0] !== ys[0]) { console.log("rr-in-bounds-neq"); }
              if (xs[0] === xs[0]) { console.log("rr-in-bounds-eq"); }
            }
            """, "arrcmprr");
        check(rr.exitCode() == 0, "read-vs-read shape exits 0: " + rr.output());
        check(rr.output().contains("rr-neq")
                && rr.output().contains("rr-in-bounds-neq")
                && rr.output().contains("rr-in-bounds-eq")
                && !rr.output().contains("bad"),
            "read-vs-read nil semantics and in-bounds element comparisons: "
                + rr.output());

        // A negative index in a comparison operand still raises E8002
        // (LuaJIT emits the negative-index check unconditionally at the
        // read, whatever the surrounding position).
        ExecResult neg = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              if (xs[-1] === 5) { console.log("bad"); }
            }
            """, "arrcmpneg");
        check(neg.exitCode() == 1, "negative comparison index exits 1: "
            + neg.output());
        check(neg.output().contains("DEAL_ERROR_CODE: E8002"),
            "negative index in === raises E8002: " + neg.output());

        // A comparison read inside a while condition re-evaluates per
        // iteration: the boxed read pre-statement is flushed inside the
        // loop before the condition test (LuaJIT re-evaluates the
        // condition every iteration), never once before the loop.
        ExecResult w = compileAndRunJvm("""
            export function test(): int {
              let xs: int[] = [1, 2, 3];
              let i: int = 0;
              while (xs[i] !== 3) {
                i = i + 1;
              }
              return i;
            }
            """, "arrcmpwhile");
        check(w.exitCode() == 0, "while comparison read exits 0: " + w.output());
        check(w.output().contains("2"),
            "the boxed comparison read re-evaluates per iteration "
            + "(i reaches 2): " + w.output());

        // Emission shape: boxed helpers, nullable temporaries, no lambda.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              if (xs[99] === 5) { console.log("eq"); }
              if (xs[99] !== 5) { console.log("neq"); }
            }
            """, "jvmtest-arrcmp-emission.deal");
        check(f.errors().isEmpty(), "comparison emission frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrcmp-emission.deal", "main");
            check(!res.hasErrors(), "comparison emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("static java.lang.Long __intArrayReadBoxed"),
                    "__intArrayReadBoxed helper emitted");
                check(java.contains("__intArrayReadBoxed(xs, 99L, "
                        + "\"jvmtest-arrcmp-emission.deal\", 4, 7)")
                        && java.contains("__intArrayReadBoxed(xs, 99L, "
                        + "\"jvmtest-arrcmp-emission.deal\", 5, 7)"),
                    "both past-end comparison reads route through the "
                        + "boxed helper carrying their index-expression "
                        + "origins (4:7, 5:7): " + java);
                check(java.contains("static java.lang.String __stringArrayReadBoxed")
                        && java.contains("static java.lang.Double __numberArrayReadBoxed")
                        && java.contains("static java.lang.Boolean __booleanArrayReadBoxed"),
                    "boxed helpers emitted for all four element types");
                check(!java.contains(" -> "),
                    "no lambda emitted for comparison positions (spaced "
                    + "arrow; wrapper descriptor strings may carry the "
                    + "unspaced arrow glyph): " + java);
            }
        }
    }

    /** Array evaluation order with a side-effecting receiver and hoisting
     * index and RHS operands (the reviewer's critical repro): the
     * receiver's inline call must run BEFORE the index operand's hoisted
     * print — the materialization is anchored at the earliest hoist start
     * after the receiver, not at the last hoisting operand's start, which
     * printed b, a, i, c, v. Same anchoring for array literals with a
     * side-effecting first element and hoisting later elements. */
    private static void testArrayEvalOrderSideEffectingReceiver() throws Exception {
        System.out.println("-- Array evaluation order with a side-effecting receiver --");

        ExecResult run = compileAndRunJvm("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            function getArr(label: string, xs: int[]): int[] { console.log(label); return xs; }
            export function test(): null {
              let xs: int[] = [5, 6];
              getArr("a", xs)[pick("i", console.log("b"))] = pick("v", console.log("c"));
              if (xs[0] === 0) { console.log("write-ok"); }
            }
            """, "arrrecvwrite");
        check(run.exitCode() == 0, "side-effecting receiver write exits 0: "
            + run.output());
        check(run.output().contains("a\nb\ni\nc\nv\nwrite-ok"),
            "receiver 'a' runs before the index operand's hoisted 'b' "
            + "(a, b, i, c, v): " + run.output());

        ExecResult lit = compileAndRunJvm("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            function getA(label: string): int { console.log(label); return 1; }
            export function test(): null {
              let xs: int[] = [getA("a"), pick("i", console.log("b")), pick("v", console.log("c"))];
              if (xs[0] === 1 && xs[1] === 0 && xs[2] === 0) { console.log("lit-ok"); }
            }
            """, "arrrecvlit");
        check(lit.exitCode() == 0, "side-effecting first literal element exits 0: "
            + lit.output());
        check(lit.output().contains("a\nb\ni\nc\nv\nlit-ok"),
            "literal first element 'a' runs before the hoisted 'b' of the "
            + "second element (a, b, i, c, v): " + lit.output());

        // Emission shape: the receiver's inline call is materialized at
        // the index operand's hoist start — BEFORE the hoisted println —
        // and never inside a lambda.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            function getArr(label: string, xs: int[]): int[] { console.log(label); return xs; }
            export function test(): null {
              let xs: int[] = [5, 6];
              getArr("a", xs)[pick("i", console.log("b"))] = pick("v", console.log("c"));
            }
            """, "jvmtest-arrrecv-emission.deal");
        check(f.errors().isEmpty(), "receiver-order emission frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrrecv-emission.deal", "main");
            check(!res.hasErrors(), "receiver-order emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                int recvIdx = java.indexOf("__t1 = getArr(\"a\", xs);");
                int hoistIdx = java.indexOf("java.lang.System.out.println(\"b\");");
                int inlineIdx = java.indexOf("__t0 = pick(\"i\", null);");
                check(recvIdx >= 0 && hoistIdx >= 0 && inlineIdx >= 0
                        && recvIdx < hoistIdx && hoistIdx < inlineIdx,
                    "the receiver materialization lands before the index "
                    + "operand's hoisted println and the index's "
                    + "materialized inline call: " + java);
                check(!java.contains(" -> "),
                    "no lambda emitted for the receiver shape (spaced "
                    + "arrow; wrapper descriptor strings may carry the "
                    + "unspaced arrow glyph): " + java);
            }
        }
    }

    /** Both === / !== operands are array reads: the LEFT read evaluates
     * completely — receiver, index, and the boxed helper call — before
     * the right operand's first evaluation. When the left read raises
     * E8002 (negative index) and the right read's receiver/index hoists
     * a null-typed side effect, the JVM must raise before that hoisted
     * print runs (LuaJIT evaluates the left read and raises before the
     * right operand is evaluated): the reviewer's repro
     * {@code ys[-1] === makeArr("made", console.log("h"))[0]} printed
     * "h" before the E8002 when the boxed read pre-statements were
     * appended after the right operand's hoisted println — anchoring
     * the left read's helper call at the left operand's evaluation
     * position (immediately after the left receiver/index hoisted
     * statements, before the right operand is even emitted) fixes it. */
    private static void testArrayReadComparisonBothReadsOrder() throws Exception {
        System.out.println("-- Both-reads === / !== left-read evaluation position --");

        // Shape 1: left read raises E8002; the right read's RECEIVER
        // hoists a null-typed side effect. Only the E8002 may print.
        ExecResult recv = compileAndRunJvm("""
            import * as console from "std/console"
            function makeArr(label: string, z: null): int[] { console.log(label); return [1]; }
            export function test(): null {
              let ys: int[] = [1];
              if (ys[-1] === makeArr("made", console.log("h"))[0]) { console.log("bad"); }
            }
            """, "arrbothnegrecv");
        check(recv.exitCode() == 1, "left-negative/right-hoisting-receiver "
            + "shape exits 1: " + recv.output());
        check(recv.output().contains("DEAL_ERROR_CODE: E8002")
                && !recv.output().contains("h")
                && !recv.output().contains("made")
                && !recv.output().contains("bad"),
            "the left read's E8002 raises before the right receiver's "
            + "hoisted println (no 'h'/'made' before it): " + recv.output());

        // Shape 2: left read raises E8002; the right read's INDEX
        // operand hoists a null-typed side effect. Same contract.
        ExecResult idx = compileAndRunJvm("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): null {
              let ys: int[] = [1];
              let zs: int[] = [1];
              if (ys[-1] === zs[pick("i", console.log("h"))]) { console.log("bad"); }
            }
            """, "arrbothnegidx");
        check(idx.exitCode() == 1, "left-negative/right-hoisting-index "
            + "shape exits 1: " + idx.output());
        check(idx.output().contains("DEAL_ERROR_CODE: E8002")
                && !idx.output().contains("h")
                && !idx.output().contains("bad"),
            "the left read's E8002 raises before the right index's "
            + "hoisted println (no 'h' before it; 'h' always precedes "
            + "pick's 'i' label, and the bare 'i' cannot be pinned "
            + "because the E8002 message 'negative array index' "
            + "contains the letter i): " + idx.output());

        // Positive control: both reads in bounds — the left read still
        // evaluates completely before the right operand's hoisted print
        // and receiver call (h, made, h2, made2, eq-ok).
        ExecResult ok = compileAndRunJvm("""
            import * as console from "std/console"
            function makeArr(label: string, z: null): int[] { console.log(label); return [1]; }
            export function test(): null {
              let ys: int[] = [1];
              if (ys[0] !== makeArr("made", console.log("h"))[0]) { console.log("bad-neq"); }
              if (ys[0] === makeArr("made2", console.log("h2"))[0]) { console.log("eq-ok"); }
            }
            """, "arrbothinbounds");
        check(ok.exitCode() == 0, "in-bounds both-reads shape exits 0: "
            + ok.output());
        check(ok.output().contains("h\nmade\nh2\nmade2\neq-ok")
                && !ok.output().contains("bad"),
            "in-bounds both-reads order is h, made, h2, made2, eq-ok: "
                + ok.output());

        // Emission shape: the left read's boxed helper pre-statement is
        // anchored BEFORE the right operand's hoisted println, and the
        // right read's helper call follows its own operand's hoisted
        // statements.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function makeArr(label: string, z: null): int[] { console.log(label); return [1]; }
            export function test(): null {
              let ys: int[] = [1];
              if (ys[-1] === makeArr("made", console.log("h"))[0]) { console.log("bad"); }
            }
            """, "jvmtest-arrboth-order-emission.deal");
        check(f.errors().isEmpty(), "both-reads order emission frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrboth-order-emission.deal", "main");
            check(!res.hasErrors(), "both-reads order emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                int leftReadIdx = java.indexOf(
                    "__intArrayReadBoxed(ys, intNeg(1L,");
                int hoistIdx = java.indexOf(
                    "java.lang.System.out.println(\"h\");");
                int rightReadIdx = java.indexOf(
                    "__intArrayReadBoxed(makeArr(\"made\", null), 0L, "
                        + "\"jvmtest-arrboth-order-emission.deal\", "
                        + "5, 18);");
                check(leftReadIdx >= 0 && hoistIdx >= 0 && rightReadIdx >= 0
                        && leftReadIdx < hoistIdx && hoistIdx < rightReadIdx,
                    "the left read's boxed helper call lands before the "
                    + "right operand's hoisted println, which lands before "
                    + "the right read's helper call: " + java);
                check(!java.contains(" -> "),
                    "no lambda emitted for the both-reads shape (spaced "
                    + "arrow; wrapper descriptor strings may carry the "
                    + "unspaced arrow glyph): " + java);
            }
        }
    }

    /** Boundary-less array-read positions (ISSUE-0094 rework): the spec
     * read-site contract (§Bounds and nil behavior) applies no typed
     * boundary to a discarded read, a {@code !} operand, or a
     * {@code &&}/{@code ||} operand, so LuaJIT computes on the nil a
     * past-end read yields instead of raising E8001 — a discarded read
     * drops it (no error), {@code not nil} is {@code true}, and
     * {@code nil or true} is {@code true} (nil is falsy). The JVM routes
     * those positions through the boxed read helpers (null past the end,
     * still E8002 for a negative index) and Lua's nil semantics: the
     * discard drops the boxed value, {@code !} coerces with
     * {@code (x == null || !x.booleanValue())}, and {@code &&}/{@code ||}
     * lower to boxed {@code java.lang.Boolean} temporaries with
     * truthiness guards — while the result nil (e.g. {@code bs[99] && true})
     * still fails at a typed boolean boundary exactly where LuaJIT's
     * check_boolean(nil) fails (E8001 "expected boolean, got null"). */
    private static void testArrayBoundaryLessReadPositions() throws Exception {
        System.out.println("-- Boundary-less read positions (javac + java) --");

        // The three reviewer shapes in one artifact: discard, !read, and
        // || / && operands — matching the LuaJIT reference exactly.
        ExecResult run = compileAndRunJvm("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): null {
              let xs: int[] = [1];
              let ns: number[] = [1.5];
              let ss: string[] = ["a"];
              let bs: boolean[] = [true];
              xs[99];
              ns[99];
              ss[99];
              bs[99];
              console.log("discard-ok");
              let b: boolean = !bs[99];
              if (b) { console.log("not-coerced-true"); }
              if (!bs[99]) { console.log("not-taken"); }
              let d: boolean = !(bs[99] && true);
              if (d) { console.log("not-niland"); }
              let c: boolean = bs[99] || true;
              if (c) { console.log("or-coerced"); }
              let g: boolean = true || bs[pick("xx", console.log("h"))];
              if (g) { console.log("true-or-skip"); }
              let f: boolean = false && bs[pick("yy", console.log("h2"))];
              if (!f) { console.log("false-and-skip"); }
            }
            """, "arrboundaryless");
        check(run.exitCode() == 0, "boundary-less shapes exit 0: "
            + run.output());
        check(run.output().contains("discard-ok\nnot-coerced-true\nnot-taken\nnot-niland\nor-coerced\ntrue-or-skip\nfalse-and-skip"),
            "discard / ! / && || shapes match the LuaJIT reference "
            + "(discard-ok, not-coerced-true, not-taken, not-niland, "
            + "or-coerced, true-or-skip, false-and-skip): " + run.output());
        check(!run.output().contains("h\n") && !run.output().contains("xx")
                && !run.output().contains("yy"),
            "the skipped && / || right operands never evaluate (no "
            + "hoisted h print, no pick labels): " + run.output());

        // The result nil of `bs[99] && true` fails at the declaration's
        // typed boolean boundary (LuaJIT: check_boolean(nil) → E8001
        // "expected boolean"); the JVM converts with booleanNotNull and
        // must spell the message with the established null convention.
        ExecResult boundary = compileAndRunJvm("""
            export function test(): boolean {
              let bs: boolean[] = [true];
              let b: boolean = bs[99] && true;
              return b;
            }
            """, "arrandboundary");
        check(boundary.exitCode() == 1, "nil && result at a boolean "
            + "boundary exits 1: " + boundary.output());
        check(boundary.output().contains("DEAL_ERROR_CODE: E8001")
                && boundary.output().contains("expected boolean, got null"),
            "the && nil result fails the boolean boundary with E8001 "
            + "'expected boolean, got null': " + boundary.output());

        // The if-condition boundary raises the same way.
        ExecResult cond = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let bs: boolean[] = [true];
              if (bs[99] && true) { console.log("bad"); }
              console.log("unreachable");
            }
            """, "arrandcondboundary");
        check(cond.exitCode() == 1 && cond.output().contains(
                "DEAL_ERROR_CODE: E8001")
                && !cond.output().contains("bad")
                && !cond.output().contains("unreachable"),
            "the && nil result fails the if-condition boundary with E8001 "
            + "(no 'bad'/'unreachable'): " + cond.output());

        // A negative index in a discarded read still raises E8002
        // (LuaJIT raises that unconditionally at the read).
        ExecResult neg = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              xs[-1];
              console.log("unreachable");
            }
            """, "arrdiscardneg");
        check(neg.exitCode() == 1
                && neg.output().contains("DEAL_ERROR_CODE: E8002")
                && !neg.output().contains("unreachable"),
            "a discarded negative-index read still raises E8002: "
                + neg.output());

        // Emission shapes: boxed discard, the ! coercion, the boxed
        // short-circuit temp with truthiness guards, the booleanNotNull
        // boundary conversion — and never a lambda.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): null {
              let xs: int[] = [1];
              let bs: boolean[] = [true];
              xs[99];
              let b: boolean = !bs[99];
              let c: boolean = bs[99] || true;
              let d: boolean = bs[99] && true;
              if (!(bs[99] && true)) { console.log("x"); }
            }
            """, "jvmtest-arrboundaryless-emission.deal");
        check(f.errors().isEmpty(), "boundary-less emission frontend clean: "
            + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrboundaryless-emission.deal", "main");
            check(!res.hasErrors(), "boundary-less emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("__intArrayReadBoxed(xs, 99L, "
                            + "\"jvmtest-arrboundaryless-emission.deal\", "
                            + "6, 3)")
                        && java.contains("java.lang.Long __ignored"),
                    "the discarded read emits the boxed helper call and a "
                    + "boxed dummy-local discard: " + java);
                check(java.contains(" == null || !")
                        && java.contains(".booleanValue())"),
                    "the ! operand emits Lua's not coercion "
                    + "(x == null || !x.booleanValue()): " + java);
                check(java.contains("java.lang.Boolean __sc")
                        && java.contains(" != null && ")
                        && java.contains("booleanNotNull("),
                    "&& / || operands lower to boxed short-circuit "
                    + "temporaries with truthiness guards and the typed "
                    + "boundary converts with booleanNotNull: " + java);
                check(!java.contains(" -> "),
                    "no lambda emitted for the boundary-less shapes (spaced "
                    + "arrow; wrapper descriptor strings may carry the "
                    + "unspaced arrow glyph): " + java);
            }
        }
    }

    /** The bytes-array past-end nil shapes (the recursive bytes
     * closure, ISSUE-0160 E8 D1; the cycle-3 parity finding): a
     * {@code (bytes | null)[]} read past the end and a {@code bytes[]}
     * read past the end consumed at a {@code bytes | null} target both
     * yield the DEAL null — the nullable element/target accepts the
     * LuaJIT nil with no boundary failure — exactly like the settled
     * {@code __intOrNullArrayRead} convention, and standalone discarded
     * past-end reads of both shapes drop the nil silently. The emitted
     * {@code __bytesOrNullArrayRead} past-end branch returns null, the
     * element-typed {@code __bytesArrayRead} keeps its E8001 raise for
     * the non-nullable target, the nil-accepting positions route
     * through the boxed {@code __bytesArrayReadBoxed} helper, and a
     * negative index still raises E8002 on every helper (LuaJIT raises
     * that unconditionally at the read). The LuaJIT lane pins the same
     * shapes cross-backend in
     * {@code retired JSON slice jvm-arrays-slice}
     * ({@code jvm-bytes-arr-past-end-null-parity},
     * {@code jvm-bytes-arr-negative-read-e8002}). */
    private static void testBytesArrayPastEndReadsYieldTheDealNull()
            throws Exception {
        System.out.println("-- Bytes-array past-end nil reads (javac + java) --");

        // Shape 1 — (bytes | null)[] past-end read into a bytes | null
        // parameter: the nullable element accepts the LuaJIT nil, so the
        // read yields the DEAL null and probe returns 7 (the pre-fix
        // helper raised E8001 "expected bytes, got null" here).
        ExecResult orNullShape = compileAndRunJvm("""
            import * as console from "std/console"
            function probe(b: bytes | null): int { return 7; }
            export function test(): null {
              let ys: (bytes | null)[] = [];
              ys[0] = bytes(3);
              let inb: int = probe(ys[0]);
              console.log("value-ok");
              let past: int = probe(ys[1]);
              console.log("past-end-ok");
              if (inb !== 7 || past !== 7) {
                throw { code: "TEST_FAIL", message: "probe" };
              }
              ys[1];
              console.log("discard-ok");
            }
            """, "bytesarrornullpastend");
        check(orNullShape.exitCode() == 0,
            "(bytes | null)[] past-end read yields the DEAL null (exit "
                + "0): " + orNullShape.output());
        check(orNullShape.output().contains(
                "value-ok\npast-end-ok\ndiscard-ok"),
            "the in-bounds and past-end reads both cross the bytes | null "
                + "boundary (value-ok, past-end-ok) and the discarded "
                + "past-end read drops the nil (discard-ok): "
                + orNullShape.output());

        // Shape 2 — bytes[] past-end read into a bytes | null parameter:
        // the read site's contextual target accepts the nil, so the read
        // routes through the boxed helper (the pre-fix code fell through
        // to the element-typed __bytesArrayRead and raised E8001).
        ExecResult boxedShape = compileAndRunJvm("""
            import * as console from "std/console"
            function probe(b: bytes | null): int { return 7; }
            export function test(): null {
              let xs: bytes[] = [];
              xs[0] = bytes(2);
              let inb: int = probe(xs[0]);
              console.log("value-ok");
              let past: int = probe(xs[1]);
              console.log("past-end-ok");
              if (inb !== 7 || past !== 7) {
                throw { code: "TEST_FAIL", message: "probe" };
              }
              xs[1];
              console.log("discard-ok");
            }
            """, "bytesarrboxedpastend");
        check(boxedShape.exitCode() == 0,
            "bytes[] past-end read at a bytes | null target yields the "
                + "DEAL null (exit 0): " + boxedShape.output());
        check(boxedShape.output().contains(
                "value-ok\npast-end-ok\ndiscard-ok"),
            "the boxed bytes[] past-end read crosses the bytes | null "
                + "boundary (past-end-ok) and the discard drops the nil "
                + "(value-ok, past-end-ok, discard-ok): "
                + boxedShape.output());

        // The element-typed read keeps the non-nullable boundary: a
        // bytes[] past-end read at a bytes target still raises E8001
        // (LuaJIT's check_bytes at the read site).
        ExecResult nonNullTarget = compileAndRunJvm("""
            export function test(): int {
              let xs: bytes[] = [];
              let b: bytes = xs[0];
              return b.length;
            }
            """, "bytesarrnonnulltarget");
        check(nonNullTarget.exitCode() == 1
                && nonNullTarget.output().contains("DEAL_ERROR_CODE: E8001")
                && nonNullTarget.output().contains("expected bytes, got null"),
            "bytes[] past-end read at a bytes target still raises E8001 "
                + "'expected bytes, got null': " + nonNullTarget.output());

        // A negative index still raises E8002 on every helper route
        // (LuaJIT raises that unconditionally at the read).
        ExecResult negBoxed = compileAndRunJvm("""
            import * as console from "std/console"
            function probe(b: bytes | null): int { return 7; }
            export function test(): null {
              let xs: bytes[] = [];
              let r: int = probe(xs[-1]);
              console.log("unreachable");
            }
            """, "bytesarrnegboxed");
        check(negBoxed.exitCode() == 1
                && negBoxed.output().contains("DEAL_ERROR_CODE: E8002")
                && !negBoxed.output().contains("unreachable"),
            "the boxed bytes[] read's negative index still raises E8002: "
                + negBoxed.output());
        ExecResult negOrNull = compileAndRunJvm("""
            import * as console from "std/console"
            function probe(b: bytes | null): int { return 7; }
            export function test(): null {
              let ys: (bytes | null)[] = [];
              let r: int = probe(ys[-1]);
              console.log("unreachable");
            }
            """, "bytesarrnegororsnull");
        check(negOrNull.exitCode() == 1
                && negOrNull.output().contains("DEAL_ERROR_CODE: E8002")
                && !negOrNull.output().contains("unreachable"),
            "the (bytes | null)[] read's negative index still raises "
                + "E8002: " + negOrNull.output());

        // Emission shapes: the or-null helper returns null past the end
        // (no raise), the element-typed helper keeps the E8001 raise,
        // the boxed helper exists with its own null past-end branch, and
        // the nil-accepting sites emit the boxed helper call.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function probe(b: bytes | null): int { return 7; }
            export function test(): null {
              let xs: bytes[] = [];
              xs[0] = bytes(2);
              let ys: (bytes | null)[] = [];
              ys[0] = bytes(3);
              let b: int = probe(xs[0]);
              let c: int = probe(xs[1]);
              let d: int = probe(ys[0]);
              let e: int = probe(ys[1]);
              if (b + c + d + e === 28) { console.log("x"); }
              xs[1];
              ys[1];
              let g: bytes = xs[1];
              g.length;
            }
            """, "jvmtest-bytesarrpastend-emission.deal");
        check(f.errors().isEmpty(), "bytes-array past-end emission "
            + "frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-bytesarrpastend-emission.deal", "main");
            check(!res.hasErrors(), "bytes-array past-end emission codegen "
                + "clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "static $DealRt.Bytes __bytesOrNullArrayRead(")
                        && java.contains(
                        "if (i >= (long) a.data.length) return null;"),
                    "the (bytes | null)[] read helper yields the DEAL "
                        + "null past the end (return null branch): "
                        + java);
                check(java.contains(
                        "static $DealRt.Bytes __bytesArrayRead(")
                        && java.contains(
                        "if (i >= (long) a.data.length) throw new DealError(\"E8001\", \"expected bytes, got null\", bFile, bLine, bCol);"),
                    "the element-typed bytes[] helper keeps the E8001 "
                        + "past-end raise at the consumer boundary origin: "
                        + java);
                check(java.contains(
                        "static $DealRt.Bytes __bytesArrayReadBoxed(")
                        && java.contains(
                            "__bytesArrayReadBoxed(xs, 1L, "
                            + "\"jvmtest-bytesarrpastend-emission.deal\", "
                            + "9, 22)"),
                    "the boxed bytes[] read helper exists and the "
                        + "bytes | null target site routes through it "
                        + "with the index-expression origin: " + java);
                check(java.contains(
                        "__bytesArrayReadBoxed(xs, 1L, "
                            + "\"jvmtest-bytesarrpastend-emission.deal\", "
                            + "9, 22)")
                        && java.contains(
                            "__bytesOrNullArrayRead(ys, 1L, "
                            + "\"jvmtest-bytesarrpastend-emission.deal\", "
                            + "14, 3)"),
                    "both discarded past-end reads use the nil-yielding "
                        + "helpers (no element-typed E8001 at a discard): "
                        + java);
                check(java.contains(
                        "__bytesArrayRead(xs, 1L, "
                            + "\"jvmtest-bytesarrpastend-emission.deal\", "
                            + "15, 18, "
                            + "\"Main.java\", 15, 10)"),
                    "the non-nullable bytes target keeps the "
                        + "element-typed read helper carrying the index "
                        + "expression (15:18) and the declared bytes "
                        + "annotation (15:10) as the boundary origin: "
                        + java);
            }
        }
    }

    /** Plain-value-left {@code ===}/{@code !==} operand evaluation
     * order (ISSUE-0094 rework): when the LEFT operand is a plain
     * non-nil-capable value and the RIGHT operand carries the LuaJIT
     * nil semantics (a primitive array read or a nil-aware {@code &&}/
     * {@code ||} result), the left operand's inline evaluation is
     * materialized into a pre-statement IMMEDIATELY — before the right
     * operand is even emitted, so the right operand's boxed read helper
     * call (and its operands' hoisted side effects) can never run
     * first. A late materialization inverted the spec's strict
     * left-to-right order (§Operational semantics):
     * {@code mark("lhs", 5) === xs[-1]} raised the right read's E8002
     * before printing "lhs" (LuaJIT prints "lhs" first) and
     * {@code (9007199254740991 + 1) === xs[-1]} raised the read's E8002
     * where LuaJIT raises the left arithmetic's E8004 first. */
    private static void testArrayReadComparisonPlainLeftOperandOrder()
            throws Exception {
        System.out.println("-- Plain-left === / !== operand order (javac + java) --");

        // The reviewer's int shape: the left effect must print before
        // the right read's E8002. The number/string/boolean and
        // nil-aware-right shapes follow in their own artifacts below.
        ExecResult run = compileAndRunJvm("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            export function test(): null {
              let xs: int[] = [1];
              if (mark("lhs", 5) === xs[-1]) { console.log("bad"); }
            }
            """, "arrplainlhserr");
        check(run.exitCode() == 1
                && run.output().contains("lhs")
                && run.output().contains("DEAL_ERROR_CODE: E8002")
                && !run.output().contains("bad"),
            "int shape: 'lhs' prints before the right read's E8002, no "
            + "'bad': " + run.output());

        ExecResult runN = compileAndRunJvm("""
            import * as console from "std/console"
            function markN(label: string, v: number): number { console.log(label); return v; }
            export function test(): null {
              let ns: number[] = [1.5];
              if (markN("lhsN", 2.5) === ns[-1]) { console.log("badN"); }
            }
            """, "arrplainlhserrnum");
        check(runN.exitCode() == 1
                && runN.output().contains("lhsN")
                && runN.output().contains("DEAL_ERROR_CODE: E8002")
                && !runN.output().contains("badN"),
            "number shape: 'lhsN' prints before the right read's E8002: "
                + runN.output());

        ExecResult runS = compileAndRunJvm("""
            import * as console from "std/console"
            function markS(label: string, v: string): string { console.log(label); return v; }
            export function test(): null {
              let ss: string[] = ["a"];
              if (markS("lhsS", "x") === ss[-1]) { console.log("badS"); }
            }
            """, "arrplainlhserrstr");
        check(runS.exitCode() == 1
                && runS.output().contains("lhsS")
                && runS.output().contains("DEAL_ERROR_CODE: E8002")
                && !runS.output().contains("badS"),
            "string shape: 'lhsS' prints before the right read's E8002: "
                + runS.output());

        ExecResult runB = compileAndRunJvm("""
            import * as console from "std/console"
            function markB(label: string, v: boolean): boolean { console.log(label); return v; }
            export function test(): null {
              let bs: boolean[] = [true];
              if (markB("lhs", true) === bs[-1]) { console.log("bad"); }
            }
            """, "arrplainlhserrbool");
        check(runB.exitCode() == 1
                && runB.output().contains("lhs")
                && runB.output().contains("DEAL_ERROR_CODE: E8002")
                && !runB.output().contains("bad"),
            "boolean shape: 'lhs' prints before the right read's E8002: "
                + runB.output());

        ExecResult runNA = compileAndRunJvm("""
            import * as console from "std/console"
            function markB(label: string, v: boolean): boolean { console.log(label); return v; }
            export function test(): null {
              let bs: boolean[] = [true];
              if (markB("lhs", true) === (bs[-1] && true)) { console.log("bad"); }
            }
            """, "arrplainlhserrnilaware");
        check(runNA.exitCode() == 1
                && runNA.output().contains("lhs")
                && runNA.output().contains("DEAL_ERROR_CODE: E8002")
                && !runNA.output().contains("bad"),
            "nil-aware && right operand: 'lhs' prints before the right "
            + "operand's read E8002: " + runNA.output());

        // Both-raise precedence: the left operand's checked arithmetic
        // must raise E8004 before the right read's E8002.
        ExecResult both = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1];
              if ((9007199254740991 + 1) === xs[-1]) { console.log("bad"); }
            }
            """, "arrplainlhsbothraise");
        check(both.exitCode() == 1
                && both.output().contains("DEAL_ERROR_CODE: E8004")
                && !both.output().contains("E8002")
                && !both.output().contains("bad"),
            "both-raise precedence: the left arithmetic's E8004 raises "
            + "first, never the read's E8002: " + both.output());

        // Positive control: an in-bounds right read with a hoisting
        // index — lhs, h, i, eq-ok (the left call still evaluates
        // completely first).
        ExecResult ok = compileAndRunJvm("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            function pick(label: string, z: null): int { console.log(label); return 0; }
            export function test(): null {
              let xs: int[] = [1];
              let zs: int[] = [5];
              if (mark("lhs", 5) === zs[pick("i", console.log("h"))]) { console.log("eq-ok"); }
            }
            """, "arrplainlhsinbounds");
        check(ok.exitCode() == 0
                && ok.output().contains("lhs\nh\ni\neq-ok")
                && !ok.output().contains("bad"),
            "in-bounds positive control prints lhs, h, i, eq-ok: "
                + ok.output());

        // The JVM's spec order for an effectful right receiver and index
        // (receiver before index, §Operational semantics rule 1):
        // lhs, made, idx — LuaJIT emits the index first (documented
        // divergence), so this shape is pinned JVM-only.
        ExecResult recv = compileAndRunJvm("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            function getArr(label: string, xs: int[]): int[] { console.log(label); return xs; }
            export function test(): null {
              let xs: int[] = [1];
              if (mark("lhs", 5) === getArr("made", xs)[mark("idx", 99)]) { console.log("bad"); }
            }
            """, "arrplainlhsrecv");
        check(recv.exitCode() == 0
                && recv.output().contains("lhs\nmade\nidx")
                && !recv.output().contains("bad"),
            "effectful right receiver/index order is lhs, made, idx "
            + "(past-end read yields nil; 5 === nil is false): "
                + recv.output());

        // Emission shapes: the effectful left operand's materialization
        // pre-statement is anchored BEFORE the right read's boxed helper
        // call (int and checked-arithmetic shapes), a pure left operand
        // is NOT materialized (the comparison references the literal
        // directly), and no lambda is ever emitted.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function mark(label: string, v: int): int { console.log(label); return v; }
            export function test(): null {
              let xs: int[] = [1];
              if (mark("lhs", 5) === xs[-1]) { console.log("bad"); }
              if ((9007199254740991 + 1) === xs[-1]) { console.log("bad2"); }
              if (5 === xs[99]) { console.log("bad3"); }
            }
            """, "jvmtest-arrplainlhs-order-emission.deal");
        check(f.errors().isEmpty(), "plain-left order emission frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arrplainlhs-order-emission.deal", "main");
            check(!res.hasErrors(), "plain-left order emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                int markIdx = java.indexOf("long __t0 = mark(\"lhs\", 5L);");
                int read1Idx = java.indexOf(
                    "__intArrayReadBoxed(xs, intNeg(1L,");
                int addIdx = java.indexOf(
                    "intAdd(9007199254740991L, 1L,");
                int read2Idx = read1Idx >= 0
                    ? java.indexOf("__intArrayReadBoxed(xs, intNeg(1L,",
                        read1Idx + 1)
                    : -1;
                check(markIdx >= 0 && read1Idx >= 0 && addIdx >= 0
                        && markIdx < read1Idx && addIdx < read2Idx,
                    "each effectful left operand's materialization lands "
                    + "before ITS right read's boxed helper call (mark "
                    + "before the first E8002 read, the checked add "
                    + "before the second E8002 read): " + java);
                check(java.matches(
                        "(?s).*5L == __t\\d+\\.longValue\\(\\).*")
                        && !java.matches("(?s).*long __t\\d+ = 5L;.*"),
                    "a pure literal left operand is not materialized — "
                    + "the comparison references the literal directly "
                    + "and no 'long __t = 5L' pre-statement exists: "
                        + java);
                check(!java.contains(" -> "),
                    "no lambda emitted for the plain-left shapes (spaced "
                    + "arrow; wrapper descriptor strings may carry the "
                    + "unspaced arrow glyph): " + java);
            }
        }
    }

    /** Out-of-slice array shapes are rejected with E6000, never silently
     * miscompiled: nested (multi-dimensional) arrays, arrays of nullable
     * table elements, function arrays, table indexing (read and write),
     * and array element types coming from inferred literals of
     * unsupported element types. (The ISSUE-0108 nullable slice brings
     * nullable arrays, arrays of nullable primitive/class elements, and
     * class arrays in scope.) */
    private static void testArrayUnsupportedElementTypesRejected() {
        System.out.println("-- Unsupported array shapes → E6000 --");

        record Case(String what, String source) {}
        List<Case> cases = List.of(
            new Case("array of nullable table elements", """
                export function test(): null {
                  let xs: (table | null)[] = [];
                }
                """)
        );

        for (Case c : cases) {
            Frontend f = compileFrontend(c.source, "jvmtest-unsupported-arr.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept unsupported array case '" + c.what()
                    + "' (the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-unsupported-arr.deal", "main");
            check(res.hasErrors(), "backend rejects " + c.what());
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 diagnostic for " + c.what() + ": " + res.diagnostics());
        }

        // ISSUE-0102: nested arrays, function arrays, and table
        // reads/writes promoted out of the E6000 rejection list.
        List<Case> promoted = List.of(
            new Case("nested array literal", """
                export function test(): int {
                  let rows: int[][] = [[1, 2], [3, 4]];
                  return rows[0][1];
                }
                """),
            new Case("array of function elements", """
                function add1(x: int): int { return x + 1; }
                export function test(): int {
                  let fs: ((x: int) => int)[] = [add1];
                  return fs[0](3);
                }
                """),
            new Case("table index read", """
                export function test(): int {
                  let t: table = {};
                  return t.x;
                }
                """),
            new Case("table index write", """
                export function test(): null {
                  let t: table = {};
                  t.x = 1;
                }
                """)
        );
        for (Case c : promoted) {
            Frontend f = compileFrontend(c.source, "jvmtest-unsupported-arr.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept promoted array case '" + c.what()
                    + "': " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-unsupported-arr.deal", "main");
            check(!res.hasErrors(),
                "backend now accepts " + c.what() + ": " + res.diagnostics());
        }
    }

    /** Use-before-declaration guards walk array value positions: a
     * module-level call whose (transitive) body reads a later-declared
     * field through an index, an array literal, or a .length read is
     * E6000 (LuaJIT reads the global nil at load; Java would read the
     * default wrapper); a function reading a field declared after the
     * function through an index is E6000 (write-dominance analysis); an
     * assignment whose index expression references a later-declared local
     * is E6000 (Java cannot-find-symbol); an index write whose array
     * identifier is a later-declared local is E6000. */
    private static void testArrayUseBeforeDeclarationGuards() {
        // v1.2 grammar gate: module-field shapes (a module-level let) are
        // frontend parse errors (E1049) before the backend's
        // use-before-declaration analysis — module fields were removed.
        // The in-function guard shapes keep their E6000 backend rejection.
        record Case(String what, String source) {}
        List<Case> cases = List.of(
            new Case("index expression referencing later local", """
                export function test(): int {
                  let xs: int[] = [1, 2];
                  xs[z] = 9;
                  let z: int = 0;
                  return xs[0];
                }
                """),
            new Case("array identifier referencing later local in write", """
                export function test(): int {
                  x[0] = 9;
                  let x: int[] = [1, 2];
                  return 0;
                }
                """)
        );

        for (Case c : cases) {
            Frontend f = compileFrontend(c.source, "jvmtest-arr-undeclared.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept unsupported array guard case '"
                    + c.what() + "' (the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-arr-undeclared.deal", "main");
            check(res.hasErrors(), "backend rejects " + c.what());
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 diagnostic for " + c.what() + ": " + res.diagnostics());
        }

        List<String> moduleShapes = List.of(
            """
            let xs: int[] = [1, 2];
            f();
            function f(): int { return xs[0]; }
            export function test(): int { return 1; }
            """,
            """
            f();
            let xs: int[] = [1, 2];
            function f(): int { return xs.length; }
            export function test(): int { return 1; }
            """,
            """
            f();
            let a: int = 1;
            function f(): int[] { return [a, 2]; }
            export function test(): int { return 1; }
            """,
            """
            function f(): int { return xs[0]; }
            let xs: int[] = [1, 2];
            export function test(): int { return f(); }
            """,
            """
            function f(): int { xs[0] = 9; return 0; }
            let xs: int[] = [1, 2];
            export function test(): int { return f(); }
            """,
            """
            function f(): int { xs[xs.length] = 9; return 0; }
            let xs: int[] = [1, 2];
            export function test(): int { return f(); }
            """,
            """
            let xs: int[] = [1, 2];
            function bump(): int { xs[0] = 9; return xs[0]; }
            export function test(): int { return bump() + xs.length; }
            """
        );
        for (String shape : moduleShapes) {
            Frontend f = compileFrontend(shape, "jvmtest-arr-module-shape.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "module-field array shape rejected with E1049: " + f.errors());
        }
    
    }

    /**
     * ISSUE-0106 v1.2 entry-module invocation: when a compilation selects
     * an entry module, the backend must invoke {@code main()} from that
     * module (spec-v1.2 §No user-defined globals). The emitted entry
     * class gets a real JVM entry point — {@code public static void
     * main(String[] args)} — that calls the DEAL {@code main} export, so
     * running {@code java <Class>} executes the module's main without any
     * test runner.
     */
    private static void testEntryModuleEmitsJvmEntryPoint() throws Exception {
        System.out.println("-- Entry module emits the JVM entry point --");

        Frontend f = compileFrontend("""
            import * as console from "std/console"
            export function main(): null {
              console.log("entry-main-ran");
              return null;
            }
            export function helper(x: int): int { return x + 1; }
            """, "jvmtest-entry.deal");
        check(f.errors().isEmpty(), "entry frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;

        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-entry.deal", "main",
            Map.of(), Map.of(), Map.of(), true);
        check(!res.hasErrors(), "entry codegen clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        check(res.source().contains("public static void main(java.lang.String[] args)"),
            "entry module emits the JVM entry point");
        check(res.source().contains("    main();"),
            "the entry point invokes the DEAL main export");

        // javac + run `java Main` directly: the backend-emitted entry point
        // (not the conformance runner) drives the invocation.
        Path dir = Files.createTempDirectory("jvmtest_entry_");
        Files.writeString(dir.resolve("Main.java"), res.source());
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(dir,
            List.of("Main.java"), javacErr);
        check(javacOk, "entry artifact compiles: " + javacErr);
        if (javacOk) {
            ProcessBuilder java = new ProcessBuilder("java", "-cp",
                dir.toString(), "Main");
            java.redirectErrorStream(true);
            Process p = java.start();
            String out = new String(p.getInputStream().readAllBytes()).trim();
            int exit = p.waitFor();
            check(exit == 0, "java Main exits 0 (the emitted entry point runs)");
            check(out.contains("entry-main-ran"),
                "main() side effect observed through the emitted entry point: " + out);
        }
        try {
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(p2 -> { try { Files.deleteIfExists(p2); } catch (IOException ignored) {} });
        } catch (IOException ignored) {}

        // Non-entry modules emit no JVM entry point.
        JvmBackend.JvmCodegenResult lib = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-entry.deal", "main");
        check(!lib.hasErrors() && !lib.source()
                .contains("public static void main(java.lang.String[] args)"),
            "non-entry module emits no JVM entry point");
    }

    /** The JVM backend's entry-point backstop (spec-v1.2 §No user-defined
     * globals): when a compilation selects this module as the entry module,
     * the emitted entry point invokes the DEAL main export; a missing main,
     * a non-exported main, an async main, or a non-null return type is an
     * E6004 diagnostic (the same backend gate the Lua backend raises)
     * instead of a silently broken artifact. The frontend E2010/E2011
     * gate (the orchestrator's selected-entry rule) is pinned by
     * ModuleSystemTest; this pins the JVM emission path. */
    private static void testEntryGateBackendE6004() {
        System.out.println("-- Entry gate E6004 (JVM backend) --");

        List<String> bad = List.of(
            "export function helper(): int { return 1; }",
            "function main(): null { return null; }",
            "export async function main(): null { return null; }",
            "export function main(): int { return 1; }");
        for (String source : bad) {
            Frontend f = compileFrontend(source, "jvmtest-entrygate.deal");
            check(f.errors().isEmpty(), "entry-gate probe frontend clean: "
                + f.errors());
            if (f.errors().isEmpty()) {
                JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                    f.program(), f.checkResult(), "jvmtest-entrygate.deal",
                    "main", Map.of(), Map.of(), Map.of(), true);
                check(res.hasErrors() && res.diagnostics().stream()
                        .anyMatch(d -> "E6004".equals(d.code())),
                    "entry gate E6004: " + res.diagnostics());
            }
        }

        Frontend ok = compileFrontend(
            "export function main(): null { return null; }",
            "jvmtest-entrygate-ok.deal");
        check(ok.errors().isEmpty(), "conforming main(): null passes the gate: "
            + ok.errors());
        if (ok.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult okRes = JvmBackend.generate(
                ok.program(), ok.checkResult(), "jvmtest-entrygate-ok.deal",
                "main", Map.of(), Map.of(), Map.of(), true);
            check(!okRes.hasErrors()
                    && okRes.source().contains("public static void main(java.lang.String[] args)"),
                "conforming entry module emits the JVM entry point");
        }
    }

    /**
     * T12 verification-2 remainder: the JVM E6004 anchors at the program
     * span (SOURCE-exact via the T2 program-span obligation). An entry
     * program whose first statement does not start at (1,1) pins the
     * exact non-zero program-start scalar offset; an empty entry file
     * pins the zero-length SOURCE range (file,1,1,1,1,0,0,0,SOURCE) —
     * never SYNTHETIC, no anchor note.
     */
    private static void testEntryE6004ProgramSpanAnchors() {
        System.out.println("-- Entry gate E6004 program-span anchors (JVM backend) --");

        // A leading comment plus a blank line: the first statement (the
        // export) starts at 3:1, and the program span starts there too.
        String leading =
            "// leading comment\n"
            + "\n"
            + "export function helper(): int { return 1; }";
        Frontend f = compileFrontend(leading, "jvmtest-e6004-span.deal");
        check(f.errors().isEmpty(), "e6004-span probe frontend clean: "
            + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-e6004-span.deal",
                "main", Map.of(), Map.of(), Map.of(), true);
            CompilerDiagnostic e6004 = res.diagnostics().stream()
                .filter(d -> "E6004".equals(d.code()))
                .findFirst().orElse(null);
            check(e6004 != null, "E6004 present for the non-(1,1) entry: "
                + res.diagnostics());
            if (e6004 != null) {
                DiagnosticRange range = e6004.range();
                check(range.origin() == RangeOrigin.SOURCE,
                    "E6004 program-span origin is SOURCE: " + range);
                check(range.startLine() == 3 && range.startColumn() == 1,
                    "E6004 starts at 3:1 (the program start, never 1:1): "
                        + range);
                int expectedStart = ScalarSourceCursor.scalarCount(leading, 0,
                    leading.indexOf("export"));
                check(range.startScalarOffset() == expectedStart,
                    "E6004 start scalar offset is exact (" + expectedStart
                        + "): " + range);
                check(range.endScalarOffset() > range.startScalarOffset()
                        && range.scalarLength()
                            == range.endScalarOffset() - range.startScalarOffset(),
                    "E6004 spans the whole program: " + range);
                check(e6004.notes().isEmpty(),
                    "the SOURCE-anchored E6004 carries no anchor note: "
                        + e6004.notes());
            }
        }

        // Empty entry file: the program span is the explicit zero-length
        // SOURCE range at file start — never SYNTHETIC, no anchor note.
        Frontend empty = compileFrontend("", "jvmtest-e6004-empty.deal");
        check(empty.errors().isEmpty(), "empty-entry probe frontend clean: "
            + empty.errors());
        if (empty.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                empty.program(), empty.checkResult(), "jvmtest-e6004-empty.deal",
                "main", Map.of(), Map.of(), Map.of(), true);
            CompilerDiagnostic e6004 = res.diagnostics().stream()
                .filter(d -> "E6004".equals(d.code()))
                .findFirst().orElse(null);
            check(e6004 != null, "E6004 present for the empty entry: "
                + res.diagnostics());
            if (e6004 != null) {
                DiagnosticRange range = e6004.range();
                check(range.origin() == RangeOrigin.SOURCE
                        && range.file().equals("jvmtest-e6004-empty.deal")
                        && range.startLine() == 1 && range.startColumn() == 1
                        && range.endLine() == 1 && range.endColumn() == 1
                        && range.startScalarOffset() == 0
                        && range.endScalarOffset() == 0
                        && range.scalarLength() == 0,
                    "empty-entry E6004 is (file,1,1,1,1,0,0,0,SOURCE): "
                        + range);
                check(e6004.notes().isEmpty(),
                    "the empty-entry SOURCE E6004 carries no anchor note: "
                        + e6004.notes());
            }
        }
    }

    /**
     * T12 verification-6 fixture: the jsonable conversion sites that hold
     * only a converted class (no source span) record E6000 through the
     * explicit synthetic factory — the canonical
     * (file,1,1,1,1,0,0,0,SYNTHETIC) range plus a note naming the class.
     * The defensive locality guard of the builtin Error class type
     * reaches jsonClassRefSynthetic (the fromJson side of a @jsonable
     * class field); the checker rejects Error-typed @jsonable fields with
     * E4007 (Error$fromJson is never exported), so the fixture drives the
     * backend directly over the parsed and checked AST — the same
     * defensive path any checker-gated unreachable program exercises.
     */
    private static void testJsonableSyntheticE6000Anchor() {
        System.out.println("-- @jsonable conversion sites: synthetic E6000 anchor notes --");

        String source = """
            // @jsonable
            export class Holder {
              e: Error;
            }
            export function main(): null { return null; }
            """;
        LexResult lex = new Lexer(source, "jvmtest-jsonable-synth.deal").tokenize();
        check(!lex.hasErrors(), "synthetic-E6000 probe lexes clean: "
            + lex.diagnostics());
        ParseResult parse = new Parser(lex.tokens(), "jvmtest-jsonable-synth.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "synthetic-E6000 probe parses clean: "
            + parse.diagnostics());
        NameResolver nr = new NameResolver("jvmtest-jsonable-synth.deal",
            new StubModuleResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        CheckResult result = TypeChecker.check("jvmtest-jsonable-synth.deal",
            symTable, nr, parse.program());
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            parse.program(), result, "jvmtest-jsonable-synth.deal", "main",
            Map.of(), Map.of(), Map.of(), false);
        CompilerDiagnostic e6000 = res.diagnostics().stream()
            .filter(d -> "E6000".equals(d.code())
                && d.range().origin() == RangeOrigin.SYNTHETIC)
            .findFirst().orElse(null);
        check(e6000 != null, "synthetic E6000 present: " + res.diagnostics());
        if (e6000 != null) {
            DiagnosticRange range = e6000.range();
            check(range.origin() == RangeOrigin.SYNTHETIC
                    && range.startLine() == 1 && range.startColumn() == 1
                    && range.endLine() == 1 && range.endColumn() == 1
                    && range.startScalarOffset() == 0
                    && range.endScalarOffset() == 0
                    && range.scalarLength() == 0,
                "synthetic E6000 carries the canonical synthetic range: "
                    + range);
            check(e6000.message().contains("values of class type 'Error'")
                    && e6000.notes().size() == 1
                    && e6000.notes().get(0).message().equals(
                        "missing anchor: class declaration span for class 'Error'"),
                "synthetic E6000 message and note name the class: "
                    + e6000.message() + " | " + e6000.notes());
        }
    }

    /**
     * ISSUE-0106 v1.2 Unicode scalar-value string for-of: each iteration
     * yields one string containing exactly one scalar value, in order —
     * a supplementary character (U+1F600) is ONE iteration, not two UTF-16
     * code units.
     */
    private static void testStringForOfScalarIteration() throws Exception {
        System.out.println("-- String for-of iterates Unicode scalar values --");

        ExecResult res = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let acc: string = "";
              let count: int = 0;
              for (let c: string of "a\ud83d\ude00b") {
                acc = acc + c;
                count = count + 1;
              }
              console.log(acc);
              if (count !== 3) { console.log("bad-count"); return; }
              if (acc !== "a\ud83d\ude00b") { console.log("bad-acc"); return; }
              console.log("for-of-scalar-ok");
            }
            """, "forof-scalar");
        check(res.exitCode() == 0, "string for-of run exits 0: " + res.output());
        check(res.output().contains("for-of-scalar-ok"),
            "string for-of iterates three scalar values: " + res.output());

        // A string for-of over an ASCII string concatenates the scalar
        // values in order.
        ExecResult ascii = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let acc: string = "";
              for (let c: string of "deal") {
                acc = acc + c;
              }
              console.log(acc);
            }
            """, "forof-ascii");
        check(ascii.exitCode() == 0 && ascii.output().contains("deal"),
            "ASCII for-of concatenates in order: " + ascii.output());

        // Array for-of stays rejected with E6000 (documented slice boundary).
        // ISSUE-0102: array for-of promoted out of the E6000 slice
        // boundary — it iterates the wrapper storage in index order with
        // a fresh per-iteration binding (spec-v1.2 §For-of).
        ExecResult arrRun = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let xs: int[] = [1, 2, 3];
              let total: int = 0;
              for (let x: int of xs) {
                total = total + x;
              }
              if (total !== 6) { console.log("bad-sum"); return; }
              console.log("array-forof-ok");
            }
            """, "jvmtest-forof-array");
        check(arrRun.exitCode() == 0,
            "array for-of runs through javac + java: " + arrRun.output());
        check(arrRun.output().contains("array-forof-ok"),
            "array for-of sums its elements: " + arrRun.output());
    }

    /**
     * ISSUE-0102 rework (BOT-0933 finding 1): array for-of over function
     * elements, nullable-function elements, and nested-array elements was
     * silently miscompiled — {@code arrayForOfReadHelper} returned null
     * for these shapes while {@code javaArrayElementType} accepted them
     * without recording an E6000, so {@code emitArrayForOf} emitted the
     * inert {@code null(__iter0, __i0)} placeholder and the CLI reported
     * success for an artifact javac rejects. The helper now mirrors the
     * {@code emitIndexRead} chain: {@code Type.Func} /
     * {@code Nullable(Type.Func)} / {@code Type.Array} elements route
     * through {@code refArrayReadHelper} (per-shape
     * {@code __fnRead$}/{@code __fnOrNullRead$}/{@code __nestedRead$}
     * helpers with E6000 diagnostics for unsupported signatures), so the
     * shapes either run correctly or the backend rejects the program —
     * never a broken artifact after the CLI reported success.
     */
    private static void testArrayForOfRefElementShapes() throws Exception {
        System.out.println("-- Array for-of: function / nested / nullable-function elements --");

        // Runtime: for-of over a function array invokes every element.
        ExecResult fn = compileAndRunJvm("""
            import * as console from "std/console"
            function add1(x: int): int { return x + 1; }
            export function test(): null {
              let fs: ((x: int) => int)[] = [add1, add1];
              let total: int = 0;
              for (let f: (x: int) => int of fs) {
                total = total + f(total);
              }
              if (total !== 3) { console.log("bad-total"); return; }
              console.log("fnarr-forof-ok");
            }
            """, "forof-fnarr");
        check(fn.exitCode() == 0,
            "function-array for-of runs through javac + java: " + fn.output());
        check(fn.output().contains("fnarr-forof-ok"),
            "function-array for-of invokes each element: " + fn.output());

        // Runtime: for-of over a nested primitive array reads each row.
        ExecResult nested = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let rows: int[][] = [[1, 2], [3, 4]];
              let total: int = 0;
              for (let row: int[] of rows) {
                total = total + row[0] + row[1];
              }
              if (total !== 10) { console.log("bad-total"); return; }
              console.log("nested-forof-ok");
            }
            """, "forof-nested");
        check(nested.exitCode() == 0,
            "nested-array for-of runs through javac + java: " + nested.output());
        check(nested.output().contains("nested-forof-ok"),
            "nested-array for-of sums the rows: " + nested.output());

        // Runtime: for-of over a nullable-function array skips the DEAL
        // null element (Java null from the per-signature read).
        ExecResult orNull = compileAndRunJvm("""
            import * as console from "std/console"
            function add1(x: int): int { return x + 1; }
            export function test(): null {
              let fs: (((x: int) => int) | null)[] = [];
              fs[fs.length] = add1;
              fs[fs.length] = null;
              let total: int = 0;
              for (let f: ((x: int) => int) | null of fs) {
                if (f !== null) { total = total + f(total); }
              }
              if (total !== 1) { console.log("bad-total"); return; }
              console.log("fnornull-forof-ok");
            }
            """, "forof-fnornull");
        check(orNull.exitCode() == 0,
            "nullable-function-array for-of runs through javac + java: "
                + orNull.output());
        check(orNull.output().contains("fnornull-forof-ok"),
            "nullable-function-array for-of skips the null element: "
                + orNull.output());

        // Emission shapes: each supported shape reads through its
        // per-shape helper, never the inert null(...) placeholder.
        Frontend shape = compileFrontend("""
            function add1(x: int): int { return x + 1; }
            export function test(): int {
              let fs: ((x: int) => int)[] = [add1];
              let rows: int[][] = [[1]];
              let nfs: (((x: int) => int) | null)[] = [];
              let total: int = 0;
              for (let f: (x: int) => int of fs) { total = total + 1; }
              for (let row: int[] of rows) { total = total + 1; }
              for (let f: ((x: int) => int) | null of nfs) { total = total + 1; }
              return total;
            }
            """, "jvmtest-forof-refshape.deal");
        check(shape.errors().isEmpty(),
            "ref-shape for-of probe frontend clean: " + shape.errors());
        if (shape.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult er = JvmBackend.generate(
                shape.program(), shape.checkResult(),
                "jvmtest-forof-refshape.deal", "main");
            check(!er.hasErrors(),
                "ref-shape for-of codegen clean: " + er.diagnostics());
            if (!er.hasErrors()) {
                check(er.source().contains("__fnRead$Fn1_I_R_I"),
                    "function-array for-of uses the per-signature read helper");
                check(er.source().contains("__nestedRead$__IntArray"),
                    "nested-array for-of uses the per-shape read helper");
                check(er.source().contains("__fnOrNullRead$Fn1_I_R_I"),
                    "nullable-function-array for-of uses the per-signature "
                        + "read helper");
                check(!er.source().contains("null(__iter"),
                    "no inert null(...) placeholder in the for-of reads");
            }
        }

        // ISSUE-0301 shared carrier: a function-type ANNOTATION whose
        // signature has an array parameter is representable now — the
        // annotation resolves to the same shared per-signature wrapper
        // the inferred shapes carry (no E6000 remains for shapes this
        // surface covers), so the array-of-function for-of compiles
        // clean.
        Frontend arraySig = compileFrontend("""
            function bad(xs: int[]): int { return 1; }
            export function test(): int {
              let fs: ((xs: int[]) => int)[] = [];
              for (let f: (xs: int[]) => int of fs) { }
              return 0;
            }
            """, "jvmtest-forof-arraysig.deal");
        check(arraySig.errors().isEmpty(),
            "array-param annotation for-of probe frontend clean: "
                + arraySig.errors());
        if (arraySig.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult er = JvmBackend.generate(
                arraySig.program(), arraySig.checkResult(),
                "jvmtest-forof-arraysig.deal", "main");
            check(!er.hasErrors(),
                "array-param annotation for-of codegen clean: "
                    + er.diagnostics());
        }
        Frontend badNested = compileFrontend("""
            function add1(x: int): int { return x + 1; }
            export function test(): int {
              let fss: (((x: int) => int)[][]) = [];
              for (let fs: ((x: int) => int)[] of fss) { }
              return 0;
            }
            """, "jvmtest-forof-badnested.deal");
        check(badNested.errors().isEmpty(),
            "nested-function-array for-of probe frontend clean: "
                + badNested.errors());
        if (badNested.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult er = JvmBackend.generate(
                badNested.program(), badNested.checkResult(),
                "jvmtest-forof-badnested.deal", "main");
            check(!er.hasErrors(),
                "nested-function-array for-of codegen clean: "
                    + er.diagnostics());
        }

        // The real orchestrator pipeline (frontend → codegen → artifacts):
        // the supported shapes compile with success=true and ZERO
        // diagnostics, and the emitted artifacts run through javac + java.
        writeFile("src/refof_main.deal", """
            export function main(): null { return null; }
            function add1(x: int): int { return x + 1; }
            export function run(): int {
              let fs: ((x: int) => int)[] = [add1];
              let rows: int[][] = [[1, 2], [3, 4]];
              let total: int = 0;
              for (let f: (x: int) => int of fs) {
                total = total + f(total);
              }
              for (let row: int[] of rows) {
                total = total + row[0];
              }
              return total;
            }
            """);
        Path entryFile = tmpDir.get().resolve("src/refof_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/refof");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success = orchestrator.compile();
        check(success, "for-of over function/nested arrays compiles through "
            + "the orchestrator: " + orchestrator.diagnostics());
        check(orchestrator.diagnostics().isEmpty(),
            "zero diagnostics for the supported ref-shape for-of: "
                + orchestrator.diagnostics());
        check(Files.exists(outputDir.resolve("Refof_main.java")),
            "the ref-shape for-of entry module writes its artifact");
        if (success && Files.exists(outputDir.resolve("Refof_main.java"))) {
            ExecResult exec = runJvmArtifacts(outputDir,
                parseProgram("export function run(): int { return 1; }"),
                "Refof_main");
            check(exec.exitCode() == 0 && exec.output().contains("5"),
                "the orchestrator artifacts run: f(0)=1 then +1+3 = 5: "
                    + exec.output());
        }

        // ISSUE-0160 (recursive bytes-bearing closure): the
        // bytes-signature function-array for-of now compiles through
        // the orchestrator — the bytes carriers map to the shared
        // $DealRt wrappers and the per-signature read helper — and the
        // emitted artifacts run through javac + java.
        writeFile("src2/refof_bytes.deal", """
            export function main(): null { return null; }
            function bad(xs: bytes): int { return 1; }
            export function run(): int {
              let fs: ((xs: bytes) => int)[] = [bad];
              let total: int = 0;
              for (let f: (xs: bytes) => int of fs) {
                total = total + f(bytes(2));
              }
              return total;
            }
            """);
        Path bytesEntry = tmpDir.get().resolve("src2/refof_bytes.deal").toAbsolutePath();
        Path bytesOut = tmpDir.get().resolve("build/refof_bytes");
        List<Path> roots2 = List.of(tmpDir.get().resolve("src2").toAbsolutePath());
        CompilationOrchestrator bytesOrchestrator = new CompilationOrchestrator(
            bytesEntry,
            bytesOut,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots2,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean bytesSuccess = bytesOrchestrator.compile();
        check(bytesSuccess,
            "the bytes-signature for-of compiles through the orchestrator: "
                + bytesOrchestrator.diagnostics());
        check(bytesOrchestrator.diagnostics().isEmpty(),
            "zero diagnostics for the bytes-signature for-of: "
                + bytesOrchestrator.diagnostics());
        check(Files.exists(bytesOut.resolve("Refof_bytes.java")),
            "the bytes-signature for-of entry module writes its artifact");
        if (bytesSuccess && Files.exists(bytesOut.resolve("Refof_bytes.java"))) {
            ExecResult bytesExec = runJvmArtifacts(bytesOut,
                parseProgram("export function run(): int { return 1; }"),
                "Refof_bytes");
            check(bytesExec.exitCode() == 0 && bytesExec.output().contains("1"),
                "the bytes-signature for-of artifacts run: f(bytes(2))=1: "
                    + bytesExec.output());
        }

        // The table-signature function-array for-of stays E6000 (table
        // carriers inside function signatures are the ISSUE-0110
        // descriptor-join family, never the bytes closure — the
        // recursive bytes-bearing wrapper closure is retired) and
        // writes no entry artifact (E6000, never a broken artifact).
        writeFile("src3/refof_table.deal", """
            export function main(): null { return null; }
            function bad(t: table): int { return 1; }
            export function run(): int {
              let fs: ((t: table) => int)[] = [];
              for (let f: (t: table) => int of fs) { }
              return 0;
            }
            """);
        Path tableEntry = tmpDir.get().resolve("src3/refof_table.deal").toAbsolutePath();
        Path tableOut = tmpDir.get().resolve("build/refof_table");
        List<Path> roots3 = List.of(tmpDir.get().resolve("src3").toAbsolutePath());
        CompilationOrchestrator tableOrchestrator = new CompilationOrchestrator(
            tableEntry,
            tableOut,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots3,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean tableSuccess = tableOrchestrator.compile();
        check(!tableSuccess,
            "the table-signature for-of fails the orchestrator: "
                + tableOrchestrator.diagnostics());
        check(tableOrchestrator.diagnostics().stream()
                .anyMatch(d -> "E6000".equals(d.code())),
            "orchestrator reports E6000 for the table-signature for-of: "
                + tableOrchestrator.diagnostics());
        check(!Files.exists(tableOut.resolve("Refof_table.java")),
            "no entry artifact when the table-signature for-of is rejected");

        // Backend-boundary pin (T12): the for-of E6000 arrives through
        // the backend's native List<CompilerDiagnostic> and renders at
        // its real source position — SOURCE origin with exact scalar
        // offsets, never synthetic (1,1). The table-signature rejection
        // (table carriers inside function signatures — the ISSUE-0110
        // descriptor-join family) anchors at the loop variable's table
        // annotation.
        String tableSrc = Files.readString(tableEntry);
        int forIdx = tableSrc.indexOf("table", tableSrc.indexOf("for (let f"));
        check(forIdx >= 0, "fixture contains the table annotation");
        int lineStart = tableSrc.lastIndexOf('\n', forIdx) + 1;
        int expectedLine = tableSrc.substring(0, forIdx).split("\n", -1).length;
        int expectedColumn = forIdx - lineStart + 1;
        int expectedOffset = ScalarSourceCursor.scalarCount(tableSrc, 0, forIdx);
        CompilerDiagnostic e6000 = tableOrchestrator.diagnostics().stream()
            .filter(d -> "E6000".equals(d.code())
                && d.message().contains("table carriers"))
            .filter(d -> d.range() != null
                && d.range().startLine() == expectedLine
                && d.range().startColumn() == expectedColumn)
            .findFirst().orElse(null);
        check(e6000 != null, "for-of E6000 present for the boundary pin");
        if (e6000 != null) {
            DiagnosticRange range = e6000.range();
            check(range.origin() == RangeOrigin.SOURCE,
                "backend-boundary E6000 range origin is SOURCE: " + range);
            check(range.startLine() == expectedLine
                    && range.startColumn() == expectedColumn,
                "backend-boundary E6000 starts at the table annotation: "
                    + range);
            check(range.startScalarOffset() == expectedOffset,
                "backend-boundary E6000 start scalar offset is exact ("
                    + expectedOffset + "): " + range);
            check(range.endScalarOffset() > range.startScalarOffset()
                    && range.scalarLength()
                        == range.endScalarOffset() - range.startScalarOffset(),
                "backend-boundary E6000 spans the for-of statement: "
                    + range);
            String formatted = DiagnosticFormatter.format(e6000);
            check(formatted.contains("[span "),
                "the new formatter renders the backend diagnostic span: "
                    + formatted);
        }
    }

    /** A catch variable captured by a nested function inside the catch
     * block must cell-ify exactly like a captured local or parameter
     * (BOT-0942 finding 2). collectLocalDeclarations declares the catch
     * variable, so the function-level capture analysis marks it captured
     * and declareLocal registers the mapped name; emitTry then declares
     * the final cell at the top of the catch block. Reads and writes
     * route through e$c[0], the closure references the effectively-final
     * cell array, and a DEAL-level reassignment of the catch variable
     * writes the cell — LuaJIT's shared-upvalue semantics without javac's
     * "local variables referenced from an inner class must be final or
     * effectively final" rejection after the CLI reported success. */
    private static void testCatchVarCapturedByNestedFunction() throws Exception {
        System.out.println("-- Catch variable captured by a nested function (javac + java) --");

        // Runtime: the reviewer's probe — a closure reading the catch
        // variable's .code created BEFORE the catch variable is
        // reassigned must observe the NEW value (shared upvalue).
        ExecResult captured = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let ok: string = "no";
              try {
                throw { code: "E1", message: "first" };
              } catch (e) {
                let f: () => string = function(): string { return e.code; };
                e = { code: "E2", message: "second" };
                ok = f();
              }
              if (ok !== "E2") { console.log("bad-code"); return; }
              console.log("catch-cell-ok");
            }
            """, "catchvarcapture");
        check(captured.exitCode() == 0,
            "captured catch variable exits 0 (javac accepted the artifact): "
                + captured.output());
        check(captured.output().contains("catch-cell-ok"),
            "the closure reads the REASSIGNED catch variable's code (E2): "
                + captured.output());

        // Runtime: the same shape where the closure WRITES the catch
        // variable and the later catch-block code reads the new value.
        ExecResult write = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let seen: string = "no";
              try {
                throw { code: "E1", message: "first" };
              } catch (e) {
                let set: () => null = function(): null {
                  e = { code: "E3", message: "third" };
                };
                set();
                seen = e.code;
              }
              if (seen !== "E3") { console.log("bad-seen"); return; }
              console.log("catch-cell-write-ok");
            }
            """, "catchvarwrite");
        check(write.exitCode() == 0,
            "closure-written catch variable exits 0: " + write.output());
        check(write.output().contains("catch-cell-write-ok"),
            "the closure's catch-variable write is visible to the catch "
                + "block: " + write.output());

        // Emission shape: the catch variable lowers to a final cell
        // declared at the top of the catch block; the closure references
        // the cell; the DEAL-level reassignment writes the cell.
        Frontend f = compileFrontend("""
            export function test(): null {
              try {
                throw { code: "E1", message: "first" };
              } catch (e) {
                let f: () => string = function(): string { return e.code; };
                e = { code: "E2", message: "second" };
              }
            }
            """, "jvmtest-catchvar-capture.deal");
        check(f.errors().isEmpty(),
            "catch-var capture probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-catchvar-capture.deal", "main");
            check(!res.hasErrors(),
                "catch-var capture probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains(
                        "final java.lang.RuntimeException[] e$c = { e };"),
                    "the captured catch variable declares its final cell at "
                        + "the top of the catch block");
                check(res.source().contains("return __errorCode(e$c[0]);"),
                    "the closure reads the catch variable through the cell");
                check(res.source().contains(
                        "e$c[0] = new DealError(\"E2\", \"second\", "
                            + "__SRC, 6, 9);"),
                    "the DEAL-level reassignment writes the cell (the "
                        + "reassigned Error literal carries its own "
                        + "source span)");
            }
        }

        // Control: a catch variable NO nested function references stays a
        // plain catch parameter — no cell is emitted.
        Frontend plainCatch = compileFrontend("""
            export function test(): string {
              let code: string = "";
              try {
                throw { code: "E1", message: "first" };
              } catch (e) {
                code = e.code;
              }
              return code;
            }
            """, "jvmtest-catchvar-plain.deal");
        check(plainCatch.errors().isEmpty(),
            "plain catch probe frontend clean: " + plainCatch.errors());
        if (plainCatch.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                plainCatch.program(), plainCatch.checkResult(),
                "jvmtest-catchvar-plain.deal", "main");
            check(!res.hasErrors(),
                "plain catch probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(!res.source().contains(
                        "final java.lang.RuntimeException[] e$c"),
                    "an uncaptured catch variable emits no cell");
            }
        }

        // The real orchestrator pipeline (frontend → codegen → artifacts):
        // the captured catch-variable shape compiles with success=true and
        // zero diagnostics, and the emitted artifacts run through javac +
        // java printing the reassigned code.
        writeFile("src/catchcap_main.deal", """
            import * as console from "std/console"
            export function main(): null { return null; }
            export function run(): null {
              let ok: string = "no";
              try {
                throw { code: "E1", message: "first" };
              } catch (e) {
                let f: () => string = function(): string { return e.code; };
                e = { code: "E2", message: "second" };
                ok = f();
              }
              if (ok !== "E2") { console.log("bad-code"); return; }
              console.log("catch-cell-ok");
            }
            """);
        Path catchEntry =
            tmpDir.get().resolve("src/catchcap_main.deal").toAbsolutePath();
        Path catchOut = tmpDir.get().resolve("build/catchcap");
        List<Path> catchRoots =
            List.of(tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator catchOrchestrator = new CompilationOrchestrator(
            catchEntry,
            catchOut,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            catchRoots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean catchSuccess = catchOrchestrator.compile();
        check(catchSuccess,
            "captured catch-variable program compiles through the "
                + "orchestrator: " + catchOrchestrator.diagnostics());
        check(catchOrchestrator.diagnostics().isEmpty(),
            "zero diagnostics for the captured catch-variable program: "
                + catchOrchestrator.diagnostics());
        check(Files.exists(catchOut.resolve("Catchcap_main.java")),
            "the captured catch-variable entry module writes its artifact");
        if (catchSuccess
                && Files.exists(catchOut.resolve("Catchcap_main.java"))) {
            ExecResult exec = runJvmArtifacts(catchOut,
                parseProgram("export function run(): null { return null; }"),
                "Catchcap_main");
            check(exec.exitCode() == 0
                    && exec.output().contains("catch-cell-ok"),
                "the orchestrator artifacts run and print the reassigned "
                    + "code: " + exec.output());
        }
    }

    /**
     * ISSUE-0106 v1.2 boundary string validation: a string crossing an
     * untyped boundary (a table read) must be a java.lang.String with no
     * unpaired UTF-16 surrogate code units — the JVM string representation
     * contract (spec-v1.2 §String escapes and Unicode / §JVM value
     * mapping). Valid scalar strings (including supplementary characters)
     * pass; the emitted check helper carries the surrogate scan.
     */
    private static void testBoundaryStringValidation() throws Exception {
        System.out.println("-- Boundary string validation (unpaired surrogates) --");

        ExecResult res = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let t: table = { s: "a\ud83d\ude00b" };
              let s: string = t.s;
              console.log(s);
              if (s !== "a\ud83d\ude00b") { console.log("bad-read"); return; }
              console.log("boundary-ok");
            }
            """, "boundary-string");
        check(res.exitCode() == 0, "boundary string run exits 0: " + res.output());
        check(res.output().contains("boundary-ok"),
            "a scalar-valid supplementary string passes the table boundary: "
                + res.output());

        // Emission shape: the boundary check scans for unpaired surrogates.
        Frontend f = compileFrontend("""
            export function test(): string {
              let t: table = { s: "x" };
              let s: string = t.s;
              return s;
            }
            """, "jvmtest-boundary-emission.deal");
        check(f.errors().isEmpty(), "boundary probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult er = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-boundary-emission.deal", "main");
            check(!er.hasErrors(), "boundary probe codegen clean: " + er.diagnostics());
            if (!er.hasErrors()) {
                check(er.source().contains("$check(\"string\","),
                    "non-nullable string table reads run the $check string branch");
                check(er.source().contains("__hasUnpairedSurrogate"),
                    "the seam's string branch scans for unpaired surrogate code units");
                check(er.source().contains(
                        "expected string, got string with unpaired surrogate code units"),
                    "the rejection message names the invalid encoding");
            }
        }
    }

    /** Null-typed return expressions keep their side effects (ISSUE-0091
     * rework: `return console.log("x")` must print "x", never be discarded). */
    private static void testNullReturnSideEffects() throws Exception {
        System.out.println("-- Null-typed return side effects (javac + java) --");

        ExecResult direct = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null { return console.log("x"); }
            """, "nullret");
        check(direct.exitCode() == 0, "return console.log(...) exits 0");
        check(direct.output().contains("x"),
            "return console.log(...) prints 'x': " + direct.output());

        ExecResult viaHelper = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): null { return helper(); }
            """, "nullret2");
        check(viaHelper.exitCode() == 0, "return helper() exits 0");
        check(viaHelper.output().contains("helper-ran"),
            "return helper() prints 'helper-ran': " + viaHelper.output());

        // A parenthesized assignment is not a valid Java expression
        // statement (JLS §14.8) — the emitted return must use the
        // unparenthesized assignment core.
        ExecResult assignReturn = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let z: null = null;
              return z = console.log("assign-return");
            }
            """, "nullret3");
        check(assignReturn.exitCode() == 0, "assignment-in-return exits 0");
        check(assignReturn.output().contains("assign-return"),
            "assignment-in-return prints: " + assignReturn.output());
    }

    /** Void-returning calls in null-typed initializers/assignments/arguments
     * are hoisted into pre-statements and lowered to stmt + null, never to
     * invalid Java and never through a lambda. */
    private static void testNullTypedInitializers() throws Exception {
        System.out.println("-- Null-typed initializers/assignments/arguments (javac + java) --");

        ExecResult inits = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): null {
              let z: null = console.log("assign-log");
              let w: null = helper();
              return;
            }
            """, "nullinits");
        check(inits.exitCode() == 0, "null-typed initializers exit 0");
        check(inits.output().contains("assign-log"),
            "console.log initializer prints: " + inits.output());
        check(inits.output().contains("helper-ran"),
            "helper() initializer prints: " + inits.output());

        ExecResult assign = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let z: null = null;
              z = console.log("assign-stmt");
              return;
            }
            """, "nullassign");
        check(assign.exitCode() == 0, "null-typed assignment exits 0");
        check(assign.output().contains("assign-stmt"),
            "null-typed assignment prints: " + assign.output());

        ExecResult arg = compileAndRunJvm("""
            import * as console from "std/console"
            function pass(x: null): null { return x; }
            export function test(): null {
              let y: null = pass(console.log("arg-log"));
              return;
            }
            """, "nullarg");
        check(arg.exitCode() == 0, "null-typed call argument exits 0");
        check(arg.output().contains("arg-log"),
            "null-typed call argument prints: " + arg.output());

        // v1.2 grammar gate: module-level null-typed field initializers were
        // removed with module-level lets (E1049).
        Frontend moduleFieldShape = compileFrontend("""
            import * as console from "std/console"
            let z: null = console.log("module-null-field");
            export function test(): int { return 1; }
            """, "jvmtest-nullmodulefield.deal");
        check(moduleFieldShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level null field rejected with E1049: " + moduleFieldShape.errors());

        // A non-null call used as a STATEMENT whose null-typed argument is
        // hoisted: the argument runs before the call.
        ExecResult stmtWithNullArg = compileAndRunJvm("""
            import * as console from "std/console"
            function consume(x: null): int { console.log("consume-ran"); return 1; }
            export function test(): int {
              consume(console.log("arg-first"));
              return 2;
            }
            """, "nullstmtarg");
        check(stmtWithNullArg.exitCode() == 0, "statement call with null arg exits 0");
        check(stmtWithNullArg.output().contains("arg-first"),
            "hoisted argument runs: " + stmtWithNullArg.output());
        check(stmtWithNullArg.output().contains("consume-ran"),
            "consuming call runs: " + stmtWithNullArg.output());
        check(stmtWithNullArg.output().indexOf("arg-first")
                < stmtWithNullArg.output().indexOf("consume-ran"),
            "argument precedes the call: " + stmtWithNullArg.output());
        check(stmtWithNullArg.output().contains("2"),
            "return value printed: " + stmtWithNullArg.output());
    }

    /**
     * Null-typed calls in value positions (initializers, assignments, call
     * arguments) that capture locals or parameters reassigned anywhere in
     * their enclosing scope. A lambda-based lowering (`nullAnd(() -> call)`)
     * would emit "local variables referenced from a lambda expression must
     * be final or effectively final" javac errors for every one of these —
     * the statement-hoisting lowering must keep them all compiling and
     * running with the correct output order.
     */
    private static void testNullTypedCapturesWithReassignment() throws Exception {
        System.out.println("-- Null-typed captures with reassignment (javac + java) --");

        // The reviewer's exact repro: initializer capture, reassignment after.
        ExecResult initAfter = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let a: string = "x";
              let z: null = console.log(a);
              a = "y";
              return;
            }
            """, "capInitAfter");
        check(initAfter.exitCode() == 0, "initializer capture + later reassignment exits 0");
        check(initAfter.output().contains("x"),
            "initializer capture + later reassignment prints: " + initAfter.output());

        // Reassignment BEFORE the capture also breaks effectively-final.
        ExecResult initBefore = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let a: string = "x";
              a = "y";
              let z: null = console.log(a);
              return;
            }
            """, "capInitBefore");
        check(initBefore.exitCode() == 0, "pre-reassigned local capture exits 0");
        check(initBefore.output().contains("y"),
            "pre-reassigned local capture prints the new value: " + initBefore.output());

        // Capture in a call-argument position, reassignment after.
        ExecResult argCapture = compileAndRunJvm("""
            import * as console from "std/console"
            function pass(x: null): null { return x; }
            export function test(): null {
              let a: string = "x";
              let y: null = pass(console.log(a));
              a = "y";
              return;
            }
            """, "capArg");
        check(argCapture.exitCode() == 0, "argument capture + reassignment exits 0");
        check(argCapture.output().contains("x"),
            "argument capture + reassignment prints: " + argCapture.output());

        // Capture in an assignment value position, reassignment after.
        ExecResult assignCapture = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null {
              let a: string = "x";
              let z: null = null;
              z = console.log(a);
              a = "y";
              return;
            }
            """, "capAssign");
        check(assignCapture.exitCode() == 0, "assignment capture + reassignment exits 0");
        check(assignCapture.output().contains("x"),
            "assignment capture + reassignment prints: " + assignCapture.output());

        // Capture of a parameter reassigned after the capture.
        ExecResult paramCapture = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(p: string): null {
              let z: null = console.log(p);
              p = "changed";
            }
            export function test(): null { helper("param-captured"); }
            """, "capParam");
        check(paramCapture.exitCode() == 0, "parameter capture + reassignment exits 0");
        check(paramCapture.output().contains("param-captured"),
            "parameter capture + reassignment prints: " + paramCapture.output());

        // A non-null return whose ARGUMENT captures a reassigned local:
        // the hoisted call must run before the return expression.
        ExecResult returnArg = compileAndRunJvm("""
            import * as console from "std/console"
            function consume(x: null): int { return 7; }
            export function test(): int {
              let a: string = "x";
              return consume(console.log(a));
            }
            """, "capReturnArg");
        check(returnArg.exitCode() == 0, "return with captured null arg exits 0");
        check(returnArg.output().contains("x"),
            "return with captured null arg prints: " + returnArg.output());
        check(returnArg.output().contains("7"),
            "return with captured null arg computes: " + returnArg.output());

        // The emitted artifact for these programs must contain no lambdas
        // (the capture-safety guarantee) and must preserve evaluation order:
        // the hoisted call runs before the reassignment that follows it.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            export function test(): null {
              let a: string = "x";
              let z: null = console.log(a);
              a = "y";
              return;
            }
            """, "jvmtest-cap-nolambda.deal");
        check(f.errors().isEmpty(), "no-lambda probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-cap-nolambda.deal", "main");
            check(!res.hasErrors(), "no-lambda probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(!res.source().contains(" -> "),
                    "no-lambda probe emits no lambda");
                check(!res.source().contains("nullAnd"),
                    "no-lambda probe emits no nullAnd helper");
                int printIdx = res.source().indexOf("java.lang.System.out.println(a);");
                int reassignIdx = res.source().indexOf("a = \"y\";");
                check(printIdx >= 0 && reassignIdx >= 0 && printIdx < reassignIdx,
                    "hoisted call runs before the later reassignment");
            }
        }
    }

    /** {@code null === null} / {@code z === null} / {@code !==} (spec
     * §Value equality: {@code null === null} is true) emit Java {@code ==}/
     * {@code !=} — no E6000 fallback. */
    private static void testNullEquality() throws Exception {
        System.out.println("-- Null equality (javac + java) --");

        ExecResult eq = compileAndRunJvm("""
            export function test(): int {
              let z: null = null;
              let same: boolean = z === null;
              let litSame: boolean = null === null;
              let neq: boolean = null !== null;
              if (same && litSame && !neq) { return 1; }
              return 0;
            }
            """, "nulleq");
        check(eq.exitCode() == 0, "null equality exits 0");
        check(eq.output().contains("1"),
            "z === null, null === null true, null !== null false: " + eq.output());

        // A side-effecting null-typed operand keeps its evaluation order:
        // the call runs before the comparison.
        ExecResult operand = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean { return helper() === null; }
            """, "nulleqoperand");
        check(operand.exitCode() == 0, "null-operand equality exits 0");
        check(operand.output().contains("helper-ran"),
            "null-typed call operand runs: " + operand.output());
        check(operand.output().contains("true"),
            "helper() === null is true: " + operand.output());

        // A hoisted call in an if CONDITION runs before the condition line.
        ExecResult cond = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("cond-ran"); }
            export function test(): int {
              if (helper() === null) { return 1; }
              return 0;
            }
            """, "nulleqcond");
        check(cond.exitCode() == 0, "if-condition null equality exits 0");
        check(cond.output().contains("cond-ran"),
            "hoisted if-condition call runs: " + cond.output());
        check(cond.output().contains("1"),
            "if-condition null equality is true: " + cond.output());

        // A hoisted call in an ELSE-IF condition: Java forbids statements
        // between `}` and `else`, so the backend nests the chain in a plain
        // else block — the call must still run before the condition.
        ExecResult elseIf = compileAndRunJvm("""
            import * as console from "std/console"
            function cond(): null { console.log("elseif-ran"); }
            export function test(): int {
              if (false) {
                return 0;
              } else if (cond() === null) {
                return 1;
              } else {
                return 2;
              }
            }
            """, "nulleqelseif");
        check(elseIf.exitCode() == 0, "hoisted else-if condition exits 0");
        check(elseIf.output().contains("elseif-ran"),
            "hoisted else-if condition runs: " + elseIf.output());
        check(elseIf.output().contains("1"),
            "hoisted else-if condition computes 1: " + elseIf.output());

        // A deeper chain with the hoisted condition in the middle: the
        // nested form must keep every brace balanced and every branch
        // reachable.
        ExecResult deepChain = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("mid-ran"); }
            export function test(): int {
              if (false) {
                console.log("a");
                return 0;
              } else if (helper() === null) {
                console.log("b");
                return 1;
              } else if (true) {
                console.log("c");
                return 2;
              } else {
                console.log("d");
                return 3;
              }
            }
            """, "nulleqdeep");
        check(deepChain.exitCode() == 0, "deep chain with hoisted middle condition exits 0");
        check(deepChain.output().contains("mid-ran"),
            "deep chain middle condition runs: " + deepChain.output());
        check(deepChain.output().contains("1"),
            "deep chain middle branch computes 1: " + deepChain.output());

        // Ordering nulls is rejected by the FRONTEND (E3007 invalid operand
        // types) — only ===/!== are legal on null — so the backend's E6000
        // fallback is unreachable for this combination.
        Frontend f = compileFrontend(
            "export function test(): boolean { return null < null; }",
            "jvmtest-nullorder.deal");
        check(!f.errors().isEmpty()
                && f.errors().stream().anyMatch(d -> "E3007".equals(d.code())),
            "null ordering is rejected by the frontend: " + f.errors());
    }

    /** Standalone non-call/non-assignment expression statements (`x + 1;`)
     * are checker-accepted and evaluated by LuaJIT (an overflow there is an
     * observable E8004); the backend lowers them to dummy-local declarations
     * so they are genuinely evaluated instead of rejected or discarded. */
    private static void testStandaloneExpressionStatements() throws Exception {
        System.out.println("-- Standalone expression statements (javac + java) --");

        ExecResult discard = compileAndRunJvm("""
            export function test(): int {
              let x: int = 1;
              x + 1;
              return x;
            }
            """, "discardbinop");
        check(discard.exitCode() == 0, "discarded binop exits 0");
        check(discard.output().contains("1"),
            "discarded binop leaves x unchanged: " + discard.output());

        ExecResult overflow = compileAndRunJvm("""
            export function test(): int {
              9223372036854775807 + 1;
              return 0;
            }
            """, "discardoverflow");
        check(overflow.exitCode() == 1, "standalone overflow exits 1");
        check(overflow.output().contains("DEAL_ERROR_CODE: E8004"),
            "standalone overflow reports E8004: " + overflow.output());

        // A string-typed standalone expression gets a String dummy local.
        ExecResult strDiscard = compileAndRunJvm("""
            export function test(): int {
              let s: string = "a";
              s + "b";
              return 1;
            }
            """, "discardstring");
        check(strDiscard.exitCode() == 0, "discarded string concat exits 0");
        check(strDiscard.output().contains("1"),
            "discarded string concat runs: " + strDiscard.output());

        // Two consecutive standalone statements need distinct dummy locals.
        ExecResult twoStmts = compileAndRunJvm("""
            export function test(): int {
              let x: int = 1;
              x + 1;
              x * 2;
              return x;
            }
            """, "twodiscards");
        check(twoStmts.exitCode() == 0, "two standalone statements exit 0");
        check(twoStmts.output().contains("1"),
            "two standalone statements run: " + twoStmts.output());

        Frontend f = compileFrontend(
            "export function test(): int { let x: int = 1; x + 1; return x; }",
            "jvmtest-discard.deal");
        check(f.errors().isEmpty(), "standalone statement frontend clean");
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-discard.deal", "main");
            check(!res.hasErrors(), "standalone statement codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("__ignored"),
                    "standalone statement lowered to a dummy local");
            }
        }
    }

    /** Runtime coverage for number floored {@code %} on negative operands,
     * string {@code ===}/ordering, and {@code console.error} → stderr. */
    private static void testNumberModStringAndStderrRuntime() throws Exception {
        System.out.println("-- number %, string ops, console.error (javac + java) --");

        // Lua-style floored modulo: -7 % 3 == 2 (Java's truncated % gives -1).
        ExecResult numMod = compileAndRunJvm(
            "export function test(): number { return -7.0 % 3.0; }",
            "nummod");
        check(numMod.exitCode() == 0, "floored % on negatives exits 0");
        check(numMod.output().contains("2.0"),
            "floored % on negatives computes 2.0: " + numMod.output());

        ExecResult numMod2 = compileAndRunJvm(
            "export function test(): number { return 7.0 % -3.0; }",
            "nummod2");
        check(numMod2.exitCode() == 0, "floored % on negative divisor exits 0");
        check(numMod2.output().contains("-2.0"),
            "7.0 % -3.0 computes -2.0 (floor(-7/3)=-3): " + numMod2.output());

        // String equality and ordering end to end.
        ExecResult strings = compileAndRunJvm("""
            function classify(s: string, t: string): int {
              if (s === t) { return 1; }
              if (s < t) { return 2; }
              return 3;
            }
            export function test(): int {
              return classify("aaa", "aaa") * 100
                   + classify("a", "b") * 10
                   + classify("b", "a");
            }
            """, "strings");
        check(strings.exitCode() == 0, "string ops exit 0");
        check(strings.output().contains("123"),
            "string equality and ordering compute 123: " + strings.output());

        // console.error reaches stderr (merged into the captured stream).
        ExecResult stderr = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): null { console.error("err-chan"); }
            """, "stderr");
        check(stderr.exitCode() == 0, "console.error exits 0");
        check(stderr.output().contains("err-chan"),
            "console.error output observed: " + stderr.output());
    }

    /** Module-level statements run at load time inside static initializers. */
    private static void testModuleLevelStatements() throws Exception {
        // v1.2 grammar gate: module-level statements (lets, calls, ifs,
        // assignments) were removed — the v1.1 static-initializer surface
        // is a frontend parse error (E1049). The same statement shapes
        // inside functions are pinned by the while/if/null tests above.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            let x: int = 1;
            console.log("module-if-ran");
            if (x === 1) { console.log("module-if-true"); }
            x = 2;
            export function test(): int { return x; }
            """, "jvmtest-modstmts.deal");
        check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "module-level statements rejected with E1049: " + f.errors());

        Frontend interleaved = compileFrontend("""
            import * as console from "std/console"
            function f(): int { console.log("f-ran"); return 1; }
            function g(): int { console.log("g-ran"); return 2; }
            let a: int = f();
            console.log("mid");
            let b: int = g();
            export function test(): int { return a + b; }
            """, "jvmtest-modorder.deal");
        check(interleaved.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "interleaved module-level statements rejected with E1049: "
                + interleaved.errors());
    
    }

    /** A shadowed let whose initializer references the outer binding uses the
     * OUTER value (LuaJIT: `local x = x + 1` reads the outer x → 6). */
    private static void testShadowedInitializer() throws Exception {
        System.out.println("-- Shadowed initializer binds to the outer scope --");

        ExecResult exec = compileAndRunJvm("""
            export function test(): int {
              let x: int = 5;
              { let x: int = x + 1; return x; }
            }
            """, "shadowed");
        check(exec.exitCode() == 0, "shadowed initializer exits 0");
        check(exec.output().contains("6"),
            "shadowed initializer computes 6 from the outer x: " + exec.output());

        // v1.2 grammar gate: the module-field shadow shape (a module-level
        // let) was removed — E1049.
        Frontend fieldShadow = compileFrontend("""
            let counter: int = 5;
            export function test(): int {
              let counter: int = counter + 1;
              return counter;
            }
            """, "jvmtest-fieldshadow.deal");
        check(fieldShadow.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-field shadow rejected with E1049: " + fieldShadow.errors());
    }

    /**
     * ISSUE-0093 regression: a parameter or local that shadows a module
     * field (or any other visible binding) must emit ONE Java name for
     * the binding everywhere — the signature and the body. The old
     * backend declared the parameter through {@code declareLocal} (which
     * disambiguated against the visible module field, {@code x → x$1})
     * but wrote the signature with the raw {@link JvmBackend#javaName}
     * translation ({@code long x}), so the body read {@code x$1} and
     * javac rejected the artifact after the CLI reported success
     * ("cannot find symbol x$1"). The shadowed-{@code let} initializer
     * case was also broken: {@code declareLocal} compared DEAL names
     * (scope keys), not emitted names (scope values), so a local
     * shadowing a disambiguated parameter silently reused the
     * parameter's emitted name and its initializer's enclosing read then
     * referred to the uninitialized new binding
     * ({@code long g$1 = intAdd(g$1, 10L);} — "might not have been
     * initialized"). Both shapes now emit valid Java and compute the
     * LuaJIT values (Lua's {@code local x = x + 1} reads the enclosing
     * binding).
     *
     * <p>ISSUE-0093 rework: the triple-deep shadow chain (field →
     * parameter → body-top let → inner-block let) exposed the remaining
     * overwrite defect — the body-top {@code let} and the parameters
     * share ONE scope map, so {@code declareLocal}'s {@code put}
     * overwrites the parameter's key and its still-in-Java-scope emitted
     * name (JLS §6.4 forbids an inner block from redeclaring a method
     * parameter) vanished from the value scan; the inner-block let then
     * reused it and javac rejected the artifact after the CLI reported
     * success. The backend now reserves every per-function emitted name
     * (parameters + locals) in a set that outlives the map overwrite, and
     * both chain shapes (with and without a module field) emit distinct
     * names and run to the LuaJIT values.
     */
    private static void testParameterShadowing() throws Exception {
        // v1.2 grammar gate: module fields were removed, so the
        // parameter-shadows-field chains are frontend parse errors
        // (E1049). The parameter/local shadow chains survive in-function
        // and are pinned below (the no-field shapes).
        Frontend f = compileFrontend("""
            let x: int = 1;
            function f(x: int): int { return x + 1; }
            export function test(): int { return f(5); }
            """, "jvmtest-paramshadow.deal");
        check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "parameter-shadow-field shape rejected with E1049: " + f.errors());

        Frontend triple = compileFrontend("""
            let g: int = 1;
            function f(g: int): int {
              let g: int = g + 10;
              return g;
            }
            export function test(): int { return f(5) + g; }
            """, "jvmtest-tripleshadow.deal");
        check(triple.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "triple-shadow field shape rejected with E1049: " + triple.errors());

        // The no-field variant pins the same disambiguation defect class
        // without any module field: the body-top let overwrites the
        // parameter's key, and the inner block must never reuse the
        // parameter's emitted name (the old backend emitted `long g` over
        // the parameter's `long g` — a javac rejection). Every binding
        // now gets a distinct name and the artifact compiles.
        Frontend noField = compileFrontend("""
            function f(g: int): int {
              let g: int = g + 10;
              { let g: int = g + 1; }
              return g;
            }
            export function test(): int { return f(5); }
            """, "jvmtest-shadowchain-nofield.deal");
        if (!noField.errors().isEmpty()) {
            fail("checker must accept the no-field chain probe: "
                + noField.errors());
            return;
        }
        JvmBackend.JvmCodegenResult noFieldRes = JvmBackend.generate(
            noField.program(), noField.checkResult(),
            "jvmtest-shadowchain-nofield.deal", "main");
        check(!noFieldRes.hasErrors(), "no-field chain emits without E6000");
        check(noFieldRes.source().contains("static long f(long g)"),
            "no-field chain: parameter keeps its plain name");
        check(hasOriginCall(noFieldRes.source(), "long g$1 = intAdd(g, 10L,"),
            "no-field chain: body-top let takes g$1 and reads the "
                + "parameter");
        check(hasOriginCall(noFieldRes.source(), "long g$2 = intAdd(g$1, 1L,"),
            "no-field chain: inner-block let never reuses the parameter's "
                + "name (g$2, not g)");
        check(noFieldRes.source().contains("return g$1;"),
            "no-field chain: trailing read resolves to the body-top let");

        ExecResult noFieldRun = compileAndRunJvm("""
            function f(g: int): int {
              let g: int = g + 10;
              { let g: int = g + 1; }
              return g;
            }
            export function test(): int { return f(5); }
            """, "shadowchainnofield");
        check(noFieldRun.exitCode() == 0, "no-field chain exits 0");
        check(noFieldRun.output().contains("15"),
            "no-field chain computes 15: " + noFieldRun.output());

        // A let shadowing a parameter: the let's initializer binds to the
        // parameter (LuaJIT's `local g = g + 10` reads the outer binding
        // → 15).
        ExecResult letShadow = compileAndRunJvm("""
            function f(g: int): int {
              let g: int = g + 10;
              return g;
            }
            export function test(): int { return f(5); }
            """, "letshadowparam");
        check(letShadow.exitCode() == 0, "let-shadow-parameter exits 0");
        check(letShadow.output().contains("15"),
            "let-shadow-parameter computes 15: " + letShadow.output());

        // Double-nested local shadowing: each level reads the nearest
        // enclosing binding ({@code x$2 = x$1 + 1} = 3).
        ExecResult nested = compileAndRunJvm("""
            export function test(): int {
              { let x: int = 2; { let x: int = x + 1; return x; } }
            }
            """, "nestedshadow");
        check(nested.exitCode() == 0, "nested shadow exits 0");
        check(nested.output().contains("3"),
            "double-nested shadow computes 3: " + nested.output());
    
    }

    /** ISSUE-0095: local classes and nominal checks — emission shape and
     * real javac + java runs. */
    private static void testClassSlice() throws Exception {
        System.out.println("-- ISSUE-0095 class slice --");

        // Emission shape: generated nested class carrying its spec identity,
        // the nominal-check helper, the minimal table, construction with
        // declaration-order defaults, and a checked table read. A class
        // named like an emitted helper (DealError) stays collision-free
        // through the $C_ prefix.
        String source = """
            class Point {
              x: int = 1;
              y: int = 2;
            }
            class DealError { value: int = 0; }
            export function test(): int {
              let p: Point = { y: 5 };
              let holder: table = { item: p };
              let q: Point = holder.item;
              return q.x + q.y;
            }
            """;
        Frontend f = compileFrontend(source, "jvmtest-class.deal");
        check(f.errors().isEmpty(), "class slice frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult res =
            JvmBackend.generate(f.program(), f.checkResult(), "jvmtest-class.deal", "Main");
        check(!res.hasErrors(), "class slice codegen clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        String java = res.source();
        check(java.contains("static final class $C_Point extends $Base"),
            "generated class extends the identity base");
        check(java.contains("super(\"@Main/Point\")"),
            "generated class carries its spec ClassDescriptor identity");
        check(java.contains("static java.lang.Object $check(java.lang.String descriptor, java.lang.Object v)"),
            "the shared descriptor-driven runtime-check seam is emitted");
        check(java.contains("descriptor.equals(\"@Main/Point\")"),
            "the Point class contributes its nominal-check branch to the seam");
        check(java.contains("descriptor.equals(\"@Main/DealError\")"),
            "a class named like the error helper stays collision-free");
        check(java.contains("new $C_Point(1L, 5L)"),
            "construction fills declaration-order defaults around provided fields");
        check(java.contains("new $DealRt.Table().put(\"item\", p)"),
            "table literal chains put calls");
        check(java.contains("$check(\"@Main/Point\", (holder).get(\"item\")"),
            "class-typed table read runs the shared seam with the spec "
            + "class descriptor and the inherited origin arguments");
        check(hasOriginCall(java, "return intAdd((q).x, (q).y,"),
            "class field reads flow into arithmetic with the origin "
                + "literals");

        // Real artifact: per-construction defaults, a field write, and a
        // nominal-check success through the table boundary.
        ExecResult ok = compileAndRunJvm("""
            class Box { value: int = 0; }
            export function test(): int {
              let a: Box = {};
              let b: Box = { value: 41 };
              a.value = b.value + 1;
              let holder: table = { item: a };
              let c: Box = holder.item;
              return c.value;
            }
            """, "class-slice-ok");
        check(ok.exitCode() == 0 && ok.output().contains("42"),
            "class construction/field write/nominal check run to 42: " + ok.output());

        // Real artifact: an identically-shaped sibling class fails the
        // nominal check — identity is nominal, never structural.
        ExecResult err = compileAndRunJvm("""
            class A { x: int = 0; }
            class B { x: int = 0; }
            export function test(): int {
              let a: A = { x: 7 };
              let holder: table = { item: a };
              let b: B = holder.item;
              return b.x;
            }
            """, "class-slice-err");
        check(err.exitCode() == 1 && err.output().contains("DEAL_ERROR_CODE: E8001"),
            "nominal check failure reports E8001 with exit 1: " + err.output());

        // Real artifact: table-typed reads of a nested table pass through
        // the $check("table", ...) boundary.
        ExecResult tbl = compileAndRunJvm("""
            export function test(): int {
              let t: table = { inner: { n: 5 } };
              let inner: table = t.inner;
              return 1;
            }
            """, "class-slice-table");
        check(tbl.exitCode() == 0 && tbl.output().contains("1"),
            "table-typed boundary reads pass through: " + tbl.output());

        // ISSUE-0095 reviewer round 9: a provided construction value whose
        // emitted code can be the Lua nil (a nil-aware && over boolean[]
        // reads) must stay boxed through the construction materialization —
        // the constructor's booleanNotNull boundary raises E8001, never a
        // bare unboxing NPE (the pre-fix `boolean __t2 = __sc0;` crashed
        // with a NullPointerException instead of a DEAL error).
        ExecResult boolBoundary = compileAndRunJvm("""
            class P { b: boolean = false; }
            export function test(): int {
              let xs: boolean[] = [true, false];
              let p: P = { b: xs[0] && xs[5] };
              return 1;
            }
            """, "class-slice-bool-boundary");
        check(boolBoundary.exitCode() == 1
                && boolBoundary.output().contains("DEAL_ERROR_CODE: E8001"),
            "nil-aware construction value fails the boolean boundary with E8001: "
                + boolBoundary.output());

        // Positive control: an in-bounds nil-aware construction value
        // constructs normally (no over-rejection, no over-boxing).
        ExecResult boolOk = compileAndRunJvm("""
            class P { b: boolean = false; }
            export function test(): int {
              let xs: boolean[] = [true, false];
              let p: P = { b: xs[0] || xs[1] };
              if (p.b === true) { return 1; }
              return 0;
            }
            """, "class-slice-bool-ok");
        check(boolOk.exitCode() == 0 && boolOk.output().contains("1"),
            "in-bounds nil-aware construction value constructs normally: "
                + boolOk.output());

        // ISSUE-0095 reviewer round 9: class-field default expressions run
        // through checkExpression in the checker, so the backend's typeOf
        // sees real types — the pre-fix backend mis-typed `1 + 2` as
        // "ADD on error and error" (E6000) while LuaJIT compiles and runs
        // the same program.
        ExecResult defaultArith = compileAndRunJvm("""
            class Point { x: int = 1 + 2; }
            export function test(): int {
              let p: Point = {};
              return p.x;
            }
            """, "class-slice-default-arith");
        check(defaultArith.exitCode() == 0
                && defaultArith.output().contains("3"),
            "arithmetic default constructs and runs to 3: "
                + defaultArith.output());

        // A default containing a null-typed call: the checker's typeMap now
        // types the inner call, so the call is hoisted into a pre-statement
        // and the constructor argument is the null value — the pre-fix
        // backend emitted `new $C_P(wrap(noise()))` (javac: 'void' type not
        // allowed here) after the CLI reported success.
        ExecResult defaultNullCall = compileAndRunJvm("""
            function noise(): null { return; }
            function wrap(x: null): string { return "w"; }
            class P { x: string = wrap(noise()); }
            export function test(): int {
              let p: P = {};
              if (p.x === "w") { return 1; }
              return 0;
            }
            """, "class-slice-default-nullcall");
        check(defaultNullCall.exitCode() == 0
                && defaultNullCall.output().contains("1"),
            "null-typed call inside a default emits valid Java and runs to 1: "
                + defaultNullCall.output());

        // The nil-aware default boundary shape needs a module-level array
        // field, which v1.2 removed (E1049 grammar gate); the in-function
        // nil-aware boolean boundary is pinned by the nullable-slice tests.
        Frontend defaultBoolBoundaryShape = compileFrontend("""
            let xs: boolean[] = [true, false];
            class P { b: boolean = xs[0] && xs[5]; }
            export function test(): int {
              let p: P = {};
              return 1;
            }
            """, "jvmtest-class-slice-default-bool-boundary.deal");
        check(defaultBoolBoundaryShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level array field default shape rejected with E1049: "
                + defaultBoolBoundaryShape.errors());

        // ISSUE-0095 reviewer round 10, re-unified by ISSUE-0110: a
        // local class named `Table` is legal DEAL. Its nominal check
        // lives as a descriptor branch INSIDE the single shared seam —
        // the pre-fix shape declared `static $T $checkTable(Object)`
        // twice and javac rejected it ("method $checkTable(Object) is
        // already defined") after the CLI reported success. The shared
        // $check helper has the raw `$` (unspellable in DEAL — javaName
        // escapes it), so no per-kind helper name can collide with a
        // generated class branch any more.
        Frontend tableClass = compileFrontend("""
            class Table { x: int = 0; }
            export function test(): int {
              let t: Table = {};
              let holder: table = { item: t };
              let q: Table = holder.item;
              return q.x;
            }
            """, "jvmtest-class-table.deal");
        check(tableClass.errors().isEmpty(),
            "class named Table frontend clean: " + tableClass.errors());
        if (tableClass.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult tableRes = JvmBackend.generate(
                tableClass.program(), tableClass.checkResult(),
                "jvmtest-class-table.deal", "Main");
            check(!tableRes.hasErrors(),
                "class named Table codegen clean: " + tableRes.diagnostics());
            if (!tableRes.hasErrors()) {
                String tableJava = tableRes.source();
                check(occurrences(tableJava,
                        "static java.lang.Object $check(java.lang.String descriptor, java.lang.Object v)") == 1,
                    "the shared runtime-check seam is declared exactly "
                    + "once");
                check(occurrences(tableJava,
                        "descriptor.equals(\"@Main/Table\")") == 1,
                    "the class Table's nominal-check branch is declared "
                    + "exactly once inside the seam");
                check(tableJava.contains(
                        "$check(\"@Main/Table\", (holder).get(\"item\")"),
                    "the Table-typed read dispatches on the spec class "
                    + "descriptor: " + tableJava);
                check(!tableJava.contains("static $T $check$Table(")
                        && !tableJava.contains("static $T $checkTable("),
                    "no duplicate per-kind table-check helper remains: "
                    + tableJava);
            }
        }

        // The same program must compile and run as a real artifact:
        // construction of Table, the table round-trip through the
        // class-typed nominal check, and the field read.
        ExecResult tableRun = compileAndRunJvm("""
            class Table { x: int = 0; }
            export function test(): int {
              let t: Table = {};
              let holder: table = { item: t };
              let q: Table = holder.item;
              return q.x;
            }
            """, "class-table-collision");
        check(tableRun.exitCode() == 0 && tableRun.output().contains("0"),
            "the Table-named class artifact compiles and runs through the "
            + "nominal check to 0: " + tableRun.output());

        // Control probes: classes named like the other fixed runtime
        // helpers stay collision-free through the $C_/$check prefixes
        // (Point vs the identity base $Base, and the error-helper name
        // DealError, pinned by the emission checks above).
        ExecResult baseRun = compileAndRunJvm("""
            class Base { x: int = 7; }
            export function test(): int {
              let p: Base = {};
              return p.x;
            }
            """, "class-named-base");
        check(baseRun.exitCode() == 0 && baseRun.output().contains("7"),
            "a class named Base compiles and runs: " + baseRun.output());

        // ISSUE-0095 reviewer round 11: the class-field write branch
        // emitted the receiver inline and flushed the RHS's hoisted
        // pre-statements before the whole assignment statement, so a
        // hoisting RHS (a null-typed call argument, a boxed nil-aware
        // read) ran its side effects BEFORE the receiver's inline
        // effects — the pre-fix artifact for getBox().x =
        // make(note("value")) printed value → target → make while
        // LuaJIT's strict left-to-right order (spec-v1.2 §Operational
        // semantics rule 1: receiver before member/index/call
        // arguments) prints target → value → make. Both operands now
        // route through emitOperandsInOrder, which materializes the
        // receiver into a temporary assigned before the hoisted
        // statements — exactly the array-write branch's fix for the
        // same hazard.
        Frontend fieldWriteOrder = compileFrontend("""
            import * as console from "std/console"
            class Box { x: int = 0; }
            function note(s: string): null { console.log(s); return; }
            function getBox(): Box { note("target"); return { x: 0 }; }
            function make(v: null): int { note("make"); return 1; }
            export function test(): int {
              getBox().x = make(note("value"));
              return 0;
            }
            """, "jvmtest-class-write-order.deal");
        check(fieldWriteOrder.errors().isEmpty(),
            "field-write order probe frontend clean: " + fieldWriteOrder.errors());
        if (fieldWriteOrder.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult orderRes = JvmBackend.generate(
                fieldWriteOrder.program(), fieldWriteOrder.checkResult(),
                "jvmtest-class-write-order.deal", "Main");
            check(!orderRes.hasErrors(),
                "field-write order probe codegen clean: " + orderRes.diagnostics());
            if (!orderRes.hasErrors()) {
                String orderJava = orderRes.source();
                int receiverTemp = orderJava.indexOf(" = getBox();");
                int hoistedCall = orderJava.indexOf("note(\"value\");");
                int store = orderJava.indexOf(".x = make(null);");
                check(receiverTemp >= 0 && hoistedCall >= 0 && store >= 0
                        && receiverTemp < hoistedCall && hoistedCall < store,
                    "receiver materialized into a temp before the RHS's "
                    + "hoisted call, store last: " + orderJava);
            }
        }

        // The same program must run receiver → value → store as a real
        // artifact (LuaJIT parity, pinned by the cross-backend fixture
        // jvm-class-field-write-eval-order-parity).
        ExecResult writeOrderRun = compileAndRunJvm("""
            import * as console from "std/console"
            class Box { x: int = 0; }
            function note(s: string): null { console.log(s); return; }
            function getBox(): Box { note("target"); return { x: 0 }; }
            function make(v: null): int { note("make"); return 1; }
            export function test(): int {
              getBox().x = make(note("value"));
              return 0;
            }
            """, "class-write-order");
        check(writeOrderRun.exitCode() == 0
                && writeOrderRun.output().startsWith("target\nvalue\nmake"),
            "class field write evaluates receiver → value → store "
            + "(spec rule 1): " + writeOrderRun.output());

        // Error precedence: when the RHS raises at its typed boundary (a
        // nil-aware && over boolean[] reads), the receiver must still
        // evaluate first — the pre-fix artifact raised E8001 before the
        // receiver's inline call ran (no "target").
        ExecResult writeErrOrder = compileAndRunJvm("""
            import * as console from "std/console"
            class P { b: boolean = false; }
            function getP(): P { console.log("target"); return { b: false }; }
            export function test(): int {
              let xs: boolean[] = [true, false];
              getP().b = xs[0] && xs[5];
              return 1;
            }
            """, "class-write-err-order");
        check(writeErrOrder.exitCode() == 1
                && writeErrOrder.output().startsWith(
                    "target\nDEAL_ERROR_CODE: E8001"),
            "receiver effects run before the RHS's E8001 boundary "
            + "failure: " + writeErrOrder.output());

        // v1.2 grammar gate: the pure variant's module-level accumulator
        // string is a removed module field (E1049). The evaluation order
        // itself stays pinned by the console-based variant above.
        Frontend writeOrderPureShape = compileFrontend("""
            let noteLog: string = "";
            class Box { x: int = 0; }
            function note(s: string): null { noteLog = noteLog + s; return; }
            function getBox(): Box { note("target"); return { x: 0 }; }
            function make(v: null): int { note("make"); return 1; }
            export function test(): int {
              getBox().x = make(note("value"));
              if (noteLog === "targetvaluemake") { return 0; }
              return 1;
            }
            """, "jvmtest-class-write-order-pure.deal");
        check(writeOrderPureShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-accumulator field write shape rejected with E1049: "
                + writeOrderPureShape.errors());
    }
    // =========================================================================
    // ISSUE-0098 slice: function values and wrappers
    // =========================================================================

    /**
     * Function values and wrappers (ISSUE-0098): first-class function
     * values through the real frontend → JvmBackend codegen → javac →
     * java pipeline, with emission assertions that the artifact carries
     * the per-signature wrapper classes (descriptor strings included),
     * the per-declaration wrapper instance fields, indirect-call
     * dispatch through {@code invoke}, the int/number intrinsic wrapper
     * fields, and the arity-extension adapter shapes (static-method
     * delegation for module functions and effectively-final snapshot
     * temporaries for locals/parameters the enclosing body never
     * reassigns; a reassigned local/parameter and any non-identifier
     * adapter value — which LuaJIT reads live / re-evaluates per invoke —
     * are E6000 until ISSUE-0110, never a lambda, never a silent
     * divergence). Also covered: E8010 runtime signature checks at
     * callback and return boundaries (matching LuaJIT's wrapper checks)
     * with the checked value expression evaluated FIRST — the marker
     * probes pin the evaluate-then-check order with console markers (the
     * v1.2 grammar removed the v1.1 module-field counter), and a later
     * materialized nil-yielding {@code (int | null)[]} read keeps its
     * boxed Java shape (never a primitive-temp unboxing NPE) — wrapper
     * reference equality, the call-result-callee evaluation order (the
     * callee is materialized into a single-assignment temporary at its
     * evaluation position, BEFORE any argument's hoisted pre-statements —
     * spec §Operational semantics rule 1: picker() raises its own E8001 /
     * return-boundary E8010 before bump()'s negative-index read can run,
     * and the E8002 message is pinned out), the reassigned
     * local/parameter adapter E6000 (also firing when the reassignment
     * is hidden in a table-literal property value), and the deferred
     * signature shapes (nested function types, nullable function
     * types, arrays of functions) rejected with E6000 — async function
     * types are ISSUE-0099-slice, covered by testAsyncSlice. Every v1.1
     * module-field/load-time shape — the field adapter with LIVE static
     * -field delegation, the load-time indirect-call guards (a
     * module-level value use of a later-declared function, a field with
     * a not-statically-known value, an assigned function reaching a
     * later-declared function, the adapter live-read retargeted to a
     * later-declared function, the snapshot field capturing a
     * later-declared function, table-literal-hidden assignments,
     * same-statement assignments, load-time-called function bodies as
     * assignment and indirect-call sources, and the module-level
     * call-result callee hazards), the clean load-time indirect-call /
     * reassignment / snapshot-field shapes, and the rest function-type
     * arm — is a v1.2 frontend grammar gate (E1049/E1047) pinned here
     * instead: the v1.2 module top level holds only declarations, so
     * those shapes no longer reach a backend. The in-function shapes run
     * cross-backend with LuaJIT parity, and the removed module-level
     * shapes are E1049-gated in
     * {@code retired JSON slice jvm-function-values-slice}.
     */
    /**
     * Regression guard (MR-0339 review round 1, major finding): the
     * public 3-arg standalone entry point
     * {@code JvmBackend.generate(program, result, sourcePath)} chains
     * with {@code modulePath = sourcePath}, and the standalone
     * classification helpers must tolerate the equal (or null) paths —
     * {@code Set.of(modulePath, sourcePath)} threw
     * {@code IllegalArgumentException: duplicate element} for every
     * non-null input, breaking the public API with a raw exception
     * instead of returning a result.
     */
    private static void testLegacyGenerateOverloadChain() {
        System.out.println("-- Legacy generate overload chain: equal module/source paths --");

        // The checker's standalone adapter classifies the module path it
        // is seeded with as its own project root; seed it with "Main"
        // and drive the backend with the same path (the review probe:
        // JvmBackend.generate(program, result, "Main")).
        String source = """
            class Point {
              x: int = 1;
            }
            export function test(): int {
              let p: Point = { x: 3 };
              return p.x;
            }
            """;
        LexResult lex = new Lexer(source, "jvmtest-overload-chain.deal")
            .tokenize();
        check(!lex.hasErrors(),
            "overload-chain probe lexes clean: " + lex.diagnostics());
        if (lex.hasErrors()) return;
        ParseResult parse = new Parser(lex.tokens(),
            "jvmtest-overload-chain.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(),
            "overload-chain probe parses clean: " + parse.diagnostics());
        if (parse.hasErrors()) return;
        NameResolver nr = new NameResolver("Main",
            new StubModuleResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        CheckResult result = TypeChecker.check("Main", symTable, nr,
            parse.program());
        check(result.diagnostics().isEmpty(),
            "overload-chain probe types clean: " + result.diagnostics());
        if (!result.diagnostics().isEmpty()) return;

        // The exact defect trigger: the 3-arg overload with only the
        // source path (modulePath defaults to sourcePath inside).
        JvmBackend.JvmCodegenResult res;
        try {
            res = JvmBackend.generate(parse.program(), result, "Main");
        } catch (IllegalArgumentException e) {
            fail("3-arg generate throws instead of returning a result: "
                + e);
            return;
        }
        check(!res.hasErrors(),
            "3-arg generate clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        check(res.source().contains("super(\"@Main/Point\")"),
            "3-arg generate emits the module's class identity text");

        // The 2-arg overload with equal explicit paths drives the same
        // duplicate-tolerant iteration through the other helper.
        JvmBackend.JvmCodegenResult equal;
        try {
            equal = JvmBackend.generate(parse.program(), result,
                "Main", "Main");
        } catch (IllegalArgumentException e) {
            fail("2-arg generate with equal paths throws: " + e);
            return;
        }
        check(!equal.hasErrors(),
            "2-arg equal-path generate clean: " + equal.diagnostics());
        check(equal.source().contains("super(\"@Main/Point\")"),
            "2-arg equal-path generate emits the class identity text");

        // Distinct paths still classify both entries exactly once, and
        // the module path drives the emitted identity text.
        JvmBackend.JvmCodegenResult distinct = JvmBackend.generate(
            parse.program(), result, "Main", "models");
        check(!distinct.hasErrors(),
            "2-arg distinct-path generate clean: "
                + distinct.diagnostics());
        check(distinct.source().contains("super(\"@models/Point\")"),
            "distinct module path drives the class identity text");
    }

    private static void testFunctionValues() throws Exception {
        System.out.println("-- Function values and wrappers (ISSUE-0098) --");

        // Typed variable + indirect call through the wrapper.
        ExecResult typed = compileAndRunJvm("""
            function add(a: int, b: int): int { return a + b; }
            export function test(): int {
              let f: (a: int, b: int) => int = add;
              return f(20, 22);
            }
            """, "jvmtest-fv-typed");
        check(typed.exitCode() == 0, "typed function value exits 0");
        check(typed.output().contains("42"),
            "typed function value computes 42 through the wrapper: "
                + typed.output());

        // Emission assertions: wrapper classes, wrapper fields, indirect
        // dispatch, intrinsic wrappers, and the arity-extension adapter.
        Frontend f = compileFrontend("""
            function add(a: int, b: int): int { return a + b; }
            function inc(x: int): int { return x + 1; }
            export function test(): int {
              let f: (a: int, b: int) => int = add;
              let g: (a: int, b: int) => int = inc;
              return f(1, 2) + g(41, 999);
            }
            """, "jvmtest-fv-emission.deal");
        check(f.errors().isEmpty(), "emission probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-fv-emission.deal", "main");
            check(!res.hasErrors(), "emission probe codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String src = res.source();
                check(src.contains("static abstract class Fn2_I_I_R_I implements FnValue {"),
                    "shared per-signature wrapper class emitted inside $DealRt");
                check(src.contains(
                    "final java.lang.String descriptor = \"(int,int)->int\";"),
                    "wrapper carries the canonical descriptor");
                check(src.contains("static final $DealRt.Fn2_I_I_R_I add$fn = new $DealRt.Fn2_I_I_R_I()"),
                    "per-declaration wrapper instance field emitted");
                check(src.contains("f.invokeAt(") && src.contains(", 1L, 2L)"),
                    "indirect call dispatches through invokeAt with the "
                        + "call-site origin");
                check(src.contains(
                    "$DealRt.Fn2_I_I_R_I g = new $DealRt.Fn2_I_I_R_I() { @Override long invoke(long p0, long p1) { return Main.inc(p0); } };"),
                    "arity adapter delegates to the qualified static method, dropping p1");
                check(src.contains(
                        "static final $DealRt.Fn2_I_I_R_I add$fn = new $DealRt.Fn2_I_I_R_I() {")
                    && src.contains(
                        "long invoke(long p0, long p1) { return Main.add(p0, p1); }"),
                    "declaration wrapper delegates to the qualified static method");
                check(src.contains("static final $DealRt.Fn1_N_R_I _int$fn = new $DealRt.Fn1_N_R_I() {")
                    && src.contains("static final $DealRt.Fn1_I_R_N _number$fn = new $DealRt.Fn1_I_R_N() {"),
                    "intrinsic function-value wrappers emitted");
                check(!src.contains(" -> "),
                    "no lambda is emitted (descriptor strings may carry the arrow glyph)");
            }
        }

        // Review finding (MR-0081, review 0009): a DEAL function named
        // `invoke` — the wrapper classes' dispatch method — must work as
        // a direct value, a callback, and an arity-adapted value without
        // recursion (the pre-fix wrapper body called the bare name, which
        // resolved to the anonymous class's OWN invoke: infinite
        // recursion) or javac failure (the arity-adapter body called the
        // bare name with the overlapping-prefix arguments, which javac
        // rejected against the adapter's own wider invoke). The same
        // qualification covers `descriptor` — the wrapper classes'
        // descriptor field, which the pre-fix body shadowed into a
        // "cannot find symbol" javac failure.
        ExecResult invokeName = compileAndRunJvm("""
            function invoke(x: int): int { return x + 1; }
            function apply(f: (x: int) => int, v: int): int { return f(v); }
            export function test(): int {
              let f: (x: int) => int = invoke;
              let g: (a: int, b: int) => int = invoke;
              return f(41) + g(0, 999) + apply(invoke, 0);
            }
            """, "jvmtest-fv-invoke-name");
        check(invokeName.exitCode() == 0,
            "a function named invoke exits 0 (no recursion): " + invokeName.output());
        check(invokeName.output().contains("44"),
            "invoke as a direct value (42), arity-adapted value (1), and "
            + "callback (1) computes 44: " + invokeName.output());
        ExecResult descriptorName = compileAndRunJvm("""
            function descriptor(x: int): int { return x * 2; }
            export function test(): int {
              let f: (a: int, b: int) => int = descriptor;
              return f(21, 999);
            }
            """, "jvmtest-fv-descriptor-name");
        check(descriptorName.exitCode() == 0,
            "a function named descriptor exits 0: " + descriptorName.output());
        check(descriptorName.output().contains("42"),
            "descriptor as an arity-adapted value computes 42: "
                + descriptorName.output());
        Frontend invokeF = compileFrontend("""
            function invoke(x: int): int { return x + 1; }
            export function test(): int {
              let f: (x: int) => int = invoke;
              let g: (a: int, b: int) => int = invoke;
              return f(41) + g(0, 999);
            }
            """, "jvmtest-fv-invoke-name-emit.deal");
        check(invokeF.errors().isEmpty(),
            "invoke-name emission probe frontend clean: " + invokeF.errors());
        if (invokeF.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                invokeF.program(), invokeF.checkResult(),
                "jvmtest-fv-invoke-name-emit.deal", "main");
            check(!res.hasErrors(), "invoke-name emission probe codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("return Main.invoke(p0);"),
                    "the declaration wrapper delegates to the qualified static invoke");
                check(res.source().contains(
                        "$DealRt.Fn2_I_I_R_I g = new $DealRt.Fn2_I_I_R_I() { @Override long invoke(long p0, long p1) { return Main.invoke(p0); } };"),
                    "the arity adapter delegates to the qualified static invoke");
                check(!res.source().contains(
                        "{ @Override long invoke(long p0) { return invoke(p0); } }"),
                    "never a bare invoke call from the wrapper's own invoke "
                        + "body (only the abstract shape's invokeAt "
                        + "delegates to the abstract invoke)");
                check(res.source().contains(".invokeAt("),
                    "the DEAL indirect call sites dispatch through the "
                        + "invokeAt origin seam");
            }
        }

        // Adapter over a LOCAL function value: the adapter snapshots the
        // local's current value into an effectively-final temporary.
        ExecResult localAdapter = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            export function test(): int {
              let g: (x: int) => int = inc;
              let h: (a: int, b: int) => int = g;
              return h(41, 999);
            }
            """, "jvmtest-fv-local-adapter");
        check(localAdapter.exitCode() == 0, "local adapter exits 0");
        check(localAdapter.output().contains("42"),
            "local-value adapter computes 42: " + localAdapter.output());
        Frontend localF = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            export function test(): int {
              let g: (x: int) => int = inc;
              let h: (a: int, b: int) => int = g;
              return h(41, 999);
            }
            """, "jvmtest-fv-local-adapter-emit.deal");
        check(localF.errors().isEmpty(), "local adapter probe frontend clean");
        if (localF.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                localF.program(), localF.checkResult(),
                "jvmtest-fv-local-adapter-emit.deal", "main");
            check(!res.hasErrors(), "local adapter probe codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("$DealRt.Fn1_I_R_I __fn0 = g;"),
                    "adapter snapshots the local into an effectively-final temporary");
                check(res.source().contains("__fn0.invoke(p0)"),
                    "adapter delegates through the snapshot temporary (the "
                        + "plain host-facing invoke ABI)");
            }
        }

        // Adapter over a call result: LuaJIT re-evaluates the value
        // expression on EVERY invoke (side effects re-run); the JVM slice
        // cannot emit that without an effectively-final capture — E6000,
        // never a silent once-only evaluation divergence.
        Frontend callAdapterF = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            function picker(): (x: int) => int { return inc; }
            export function test(): int {
              let h: (a: int, b: int) => int = picker();
              return h(41, 999);
            }
            """, "jvmtest-fv-call-adapter.deal");
        check(callAdapterF.errors().isEmpty(),
            "call-result adapter probe frontend clean: " + callAdapterF.errors());
        if (callAdapterF.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                callAdapterF.program(), callAdapterF.checkResult(),
                "jvmtest-fv-call-adapter.deal", "main");
            check(res.hasErrors(), "call-result adapter is rejected");
            check(res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())),
                "E6000 for the call-result adapter: " + res.diagnostics());
        }

        // v1.2 grammar gate: module fields were removed, so the
        // module-field adapter shape (the adapter body reading the static
        // field LIVE on every invoke — LuaJIT's adapter re-reads the
        // chunk-local binding, so a reassignment after creation retargets
        // it) is a frontend parse error (E1049) before any backend. The
        // in-function local-adapter coverage above and the reassigned
        // local/parameter E6000 cases below keep the adapter semantics.
        Frontend fieldF = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            let g: (x: int) => int = inc;
            export function test(): int {
              let h: (a: int, b: int) => int = g;
              return h(41, 999);
            }
            """, "jvmtest-fv-field-adapter-emit.deal");
        check(fieldF.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "module-field adapter shape rejected with E1049: "
                + fieldF.errors());

        // v1.2 grammar gate: the load-time variant of the field adapter
        // (module-level wrapper fields, a load-time reassignment, and a
        // load-time indirect call) is a frontend parse error (E1049)
        // before any backend — module top level holds only declarations.
        Frontend loadFieldAdapter = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            function dbl(x: int): int { return x * 2; }
            let g: (x: int) => int = inc;
            let h: (a: int, b: int) => int = g;
            g = dbl;
            let r: int = h(10, 999);
            export function test(): int { return r; }
            """, "jvmtest-fv-load-field-adapter.deal");
        check(loadFieldAdapter.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "load-time field adapter shape rejected with E1049: "
                + loadFieldAdapter.errors());

        // A call-result callee evaluates COMPLETELY before every argument
        // (spec §Operational semantics rule 1 — LuaJIT evaluates the
        // callee expression first), even when a later argument hoists
        // side-effecting pre-statements: the callee is materialized into
        // a single-assignment temporary at its evaluation position, so
        // picker() runs before bump()'s negative-index read. The probe
        // pins the order with the ERROR: picker's own past-end int[] read
        // raises E8001, and bump's E8002 message never appears (the
        // pre-fix inline `picker().invoke(...)` form hoisted bump() first
        // and raised E8002).
        ExecResult calleeOrder = compileAndRunJvm("""
            function f2(a: int, b: boolean): int { return a; }
            function picker(): (a: int, b: boolean) => int {
              let xs: int[] = [1];
              let v: int = xs[99];
              return f2;
            }
            function bump(): int {
              let ys: int[] = [1];
              return ys[-1];
            }
            export function test(): int {
              let bs: boolean[] = [true];
              return picker()(bump(), true && bs[99]);
            }
            """, "jvmtest-fv-callee-order");
        check(calleeOrder.exitCode() == 1,
            "call-result callee evaluation probe exits 1");
        check(calleeOrder.output().contains("DEAL_ERROR_CODE: E8001"),
            "the callee's own E8001 raises before any argument runs: "
                + calleeOrder.output());
        check(!calleeOrder.output().contains("negative array index"),
            "bump() never runs before the callee: " + calleeOrder.output());

        // The same callee-first order holds when the callee's return
        // boundary raises E8010: picker() raises before bump() and the
        // hoisted && operand are evaluated.
        ExecResult calleeE8010 = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            function picker(): (a: int, b: boolean) => int { return inc; }
            function bump(): int {
              let ys: int[] = [1];
              return ys[-1];
            }
            export function test(): int {
              let bs: boolean[] = [true];
              return picker()(bump(), true && bs[99]);
            }
            """, "jvmtest-fv-callee-e8010");
        check(calleeE8010.exitCode() == 1,
            "call-result callee E8010 probe exits 1");
        check(calleeE8010.output().contains("DEAL_ERROR_CODE: E8010"),
            "the callee's return-boundary E8010 raises before any argument: "
                + calleeE8010.output());
        check(!calleeE8010.output().contains("negative array index"),
            "bump() never runs before the E8010 raise: "
                + calleeE8010.output());

        // Emission assertions: the callee temporary and the dispatch.
        Frontend calleeF = compileFrontend("""
            function add(a: int, b: int): int { return a + b; }
            function picker(): (a: int, b: int) => int { return add; }
            export function test(): int { return picker()(41, 1); }
            """, "jvmtest-fv-callee-emit.deal");
        check(calleeF.errors().isEmpty(),
            "call-result callee emit probe frontend clean: " + calleeF.errors());
        if (calleeF.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                calleeF.program(), calleeF.checkResult(),
                "jvmtest-fv-callee-emit.deal", "main");
            check(!res.hasErrors(), "call-result callee emit probe codegen "
                + "clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("$DealRt.Fn2_I_I_R_I __fn0 = picker();"),
                    "the call-result callee is materialized into a temporary "
                    + "at its evaluation position");
                check(res.source().contains("__fn0.invokeAt(")
                        && res.source().contains(", 41L, 1L)"),
                    "the dispatch goes through the callee temporary with "
                        + "the call-site origin");
                check(!res.source().contains("picker().invoke"),
                    "never an inline callee whose argument pre-statements "
                    + "would run first");
            }
        }

        // Adapter over a local/parameter that the enclosing body
        // reassigns: LuaJIT's adapter reads the binding live and observes
        // the later assignment; the JVM slice cannot emit a live capture
        // of a reassigned binding — E6000, never a silent snapshot
        // divergence.
        record ReassignedCase(String what, String source) {}
        List<ReassignedCase> reassigned = List.of(
            new ReassignedCase("reassigned local", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return x * 2; }
                export function test(): int {
                  let g: (x: int) => int = inc;
                  let h: (a: int, b: int) => int = g;
                  g = dbl;
                  return h(10, 999);
                }
                """),
            new ReassignedCase("reassigned parameter", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return x * 2; }
                function probe(g: (x: int) => int): int {
                  let h: (a: int, b: int) => int = g;
                  g = dbl;
                  return h(10, 999);
                }
                export function test(): int { return probe(inc); }
                """),
            new ReassignedCase(
                "reassigned local hidden in a table-literal property value", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return x * 2; }
                export function test(): int {
                  let g: (x: int) => int = inc;
                  let h: (a: int, b: int) => int = g;
                  let t = { x: (g = dbl) };
                  return h(10, 999);
                }
                """));
        for (ReassignedCase c : reassigned) {
            Frontend rf = compileFrontend(c.source,
                "jvmtest-fv-reassigned.deal");
            if (!rf.errors().isEmpty()) {
                fail("frontend must accept the reassigned-adapter case '"
                    + c.what() + "' (the backend rejects it): " + rf.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                rf.program(), rf.checkResult(), "jvmtest-fv-reassigned.deal",
                "main");
            check(res.hasErrors(), "backend rejects " + c.what());
            check(res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())),
                "E6000 for " + c.what() + ": " + res.diagnostics());
        }

        // E8010 signature check at a callback parameter boundary.
        ExecResult cbCheck = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            function apply(f: (a: int, b: string) => int, v: int): int { return f(v, "ignored"); }
            export function test(): int { return apply(inc, 41); }
            """, "jvmtest-fv-cb-check");
        check(cbCheck.exitCode() == 1, "callback signature check exits 1");
        check(cbCheck.output().contains("DEAL_ERROR_CODE: E8010"),
            "callback signature check raises E8010: " + cbCheck.output());
        check(cbCheck.output().contains(
            "function signature mismatch: expected (int,string)->int, got (int)->int"),
            "callback signature check carries LuaJIT's message: " + cbCheck.output());

        // E8010 signature check at a return boundary.
        ExecResult retCheck = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            function picker(): (a: int, b: int) => int { return inc; }
            export function test(): int {
              let f: (a: int, b: int) => int = picker();
              return f(41, 999);
            }
            """, "jvmtest-fv-ret-check");
        check(retCheck.exitCode() == 1, "return signature check exits 1");
        check(retCheck.output().contains("DEAL_ERROR_CODE: E8010"),
            "return signature check raises E8010: " + retCheck.output());

        // A later operand materialized after an E8010-checking argument
        // keeps the EMITTED code shape (ISSUE-0108 integration): the
        // nil-yielding `(int | null)[]` read past the end yields the DEAL
        // null (boxed `java.lang.Long`), so its materialization temporary
        // must be the boxed type — a `long` temp would auto-unbox the
        // null and crash with a bare Java NPE instead of the E8010 the
        // parameter boundary raises (LuaJIT evaluates the read — nil, no
        // error — and then raises E8010 at callee entry).
        ExecResult cbCheckNullable = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            function take(f: (a: int, b: string) => int, v: int | null): int { return 1; }
            export function test(): int {
              let xs: (int | null)[] = [];
              return take(inc, xs[0]);
            }
            """, "jvmtest-fv-cb-check-nullable");
        check(cbCheckNullable.exitCode() == 1,
            "nullable-later-operand E8010 probe exits 1");
        check(cbCheckNullable.output().contains("DEAL_ERROR_CODE: E8010"),
            "the E8010 raises (never a bare NPE on the null element): "
                + cbCheckNullable.output());
        check(!cbCheckNullable.output().contains("NullPointerException"),
            "no unboxing NPE from a primitive materialization temp: "
                + cbCheckNullable.output());

        // Two arity-mismatched function-valued arguments in ONE call,
        // with an impure later value expression (BOT-0716 finding): both
        // value expressions must evaluate left to right, the FIRST
        // parameter's boundary check must raise E8010 with the FIRST
        // parameter's descriptor, and the emitted artifact must be valid
        // Java. The pre-fix JVM materialized the later operand's RAISING
        // construction into an actual-shape temporary
        // (`Fn0_R_I __t0 = new Fn2_I_S_R_I() {…}`), which javac rejected
        // ("incompatible types") after the CLI reported success — and
        // which would have raised the SECOND parameter's check before
        // the first's.
        ExecResult twoChecks = compileAndRunJvm("""
            import * as console from "std/console"
            function inc(x: int): int { return x + 1; }
            function pickZero(): () => int {
              console.log("f2-e8010-two-mismatched-args-ok");
              return zero;
            }
            function zero(): int { return 0; }
            function apply2(f: (a: int, b: string) => int, g: (a: int, b: string) => int): int { return f(1, "s"); }
            export function test(): int { return apply2(inc, pickZero()); }
            """, "jvmtest-fv-cb-two-checks");
        check(twoChecks.exitCode() == 1,
            "two-mismatched-args E8010 probe exits 1");
        check(twoChecks.output().contains("f2-e8010-two-mismatched-args-ok"),
            "the later argument's value expression evaluates before the raise: "
                + twoChecks.output());
        check(twoChecks.output().contains("DEAL_ERROR_CODE: E8010"),
            "the two-mismatched-args E8010 raises: " + twoChecks.output());
        check(twoChecks.output().contains(
            "function signature mismatch: expected (int,string)->int, got (int)->int"),
            "the FIRST parameter's check raises with its descriptor: "
                + twoChecks.output());
        check(!twoChecks.output().contains("got ()->int"),
            "the second parameter's check never runs: " + twoChecks.output());

        // Emission shape: each check operand's VALUE is an actual-shape
        // temporary declared at its evaluation position and each raising
        // construction stays INLINE at its argument position — neither
        // materialization loop ever hoists the raising construction
        // (the pre-fix javac-rejected shape).
        Frontend twoChecksF = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            function pickZero(): () => int { return zero; }
            function zero(): int { return 0; }
            function apply2(f: (a: int, b: string) => int, g: (a: int, b: string) => int): int { return f(1, "s"); }
            export function test(): int { return apply2(inc, pickZero()); }
            """, "jvmtest-fv-cb-two-checks-emit.deal");
        check(twoChecksF.errors().isEmpty(),
            "two-check emission probe frontend clean: " + twoChecksF.errors());
        if (twoChecksF.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                twoChecksF.program(), twoChecksF.checkResult(),
                "jvmtest-fv-cb-two-checks-emit.deal", "main");
            check(!res.hasErrors(),
                "two-check emission probe codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String src = res.source();
                check(src.contains("$DealRt.Fn1_I_R_I __fn0 = inc$fn;"),
                    "the first check operand's value temp carries its ACTUAL shape");
                check(src.contains("$DealRt.Fn0_R_I __fn1 = pickZero();"),
                    "the later check operand's value temp carries its ACTUAL shape");
                check(!src.contains("Fn0_R_I __t")
                    && !src.contains("Fn2_I_S_R_I __t")
                    && !src.contains("Fn1_I_R_I __t"),
                    "no materialization temp holds a raising construction");
                check(src.contains("new $DealRt.Fn2_I_S_R_I() { { if (!checkSig(\"(int,string)->int\", \"(int)->int\"))")
                    && src.contains("new $DealRt.Fn2_I_S_R_I() { { if (!checkSig(\"(int,string)->int\", \"()->int\"))"),
                    "both raising constructions stay inline at their argument positions in parameter order");
                check(src.contains("apply2(new $DealRt.Fn2_I_S_R_I()"),
                    "the inline raise sits directly in the call argument list");
            }
        }

        // The checked value expression is evaluated BEFORE E8010 raises
        // (spec §Operational semantics rule 2 / strict return-value
        // evaluation — LuaJIT's evaluate-then-check order). The callback
        // probe pins the ORDER with console markers (the v1.2 grammar
        // removed the v1.1 module-field counter): the checked argument's
        // value expression prints "pre" and the later argument's value
        // prints "post" — both must appear in order before E8010, and
        // the pre-fix snapshot-check wrapper ran neither.
        ExecResult cbEval = compileAndRunJvm("""
            import * as console from "std/console"
            function inc(x: int): int { return x + 1; }
            function markF(tag: string, f: (x: int) => int): (x: int) => int {
              if (tag === "pre") { console.log("f2-e8010-callback-eval-order-pre"); }
              return f;
            }
            function markI(tag: string, v: int): int {
              if (tag === "post") { console.log("f2-e8010-callback-eval-order-post"); }
              return v;
            }
            function take(f: (a: int, b: string) => int, v: int): int { return f(v, "ignored"); }
            export function test(): int { return take(markF("pre", inc), markI("post", 1)); }
            """, "jvmtest-fv-cb-eval");
        check(cbEval.exitCode() == 1, "callback E8010 evaluation probe exits 1");
        check(cbEval.output().contains("f2-e8010-callback-eval-order-pre"),
            "the checked argument's value expression runs before E8010 raises: "
                + cbEval.output());
        check(cbEval.output().contains("f2-e8010-callback-eval-order-post"),
            "the later argument's value expression runs before E8010 raises: "
                + cbEval.output());
        check(cbEval.output().indexOf("f2-e8010-callback-eval-order-pre")
                < cbEval.output().indexOf("f2-e8010-callback-eval-order-post"),
            "checked-value marker precedes the later argument's marker: "
                + cbEval.output());
        check(cbEval.output().contains("DEAL_ERROR_CODE: E8010"),
            "the callback E8010 still raises: " + cbEval.output());

        ExecResult retEval = compileAndRunJvm("""
            import * as console from "std/console"
            function inc(x: int): int { return x + 1; }
            function markF(tag: string, f: (x: int) => int): (x: int) => int {
              if (tag === "pre") { console.log("f2-e8010-return-eval-ok"); }
              return f;
            }
            function picker(): (a: int, b: int) => int { return markF("pre", inc); }
            export function test(): int {
              let f: (a: int, b: int) => int = picker();
              return f(41, 999);
            }
            """, "jvmtest-fv-ret-eval");
        check(retEval.exitCode() == 1, "return E8010 evaluation probe exits 1");
        check(retEval.output().contains("f2-e8010-return-eval-ok"),
            "the returned value expression is evaluated before E8010 raises: "
                + retEval.output());
        check(retEval.output().contains("DEAL_ERROR_CODE: E8010"),
            "the return E8010 still raises: " + retEval.output());

        // v1.2 grammar gate: module fields were removed, so the
        // load-time clean shapes — an indirect call through a
        // function-typed module field whose value is statically known, a
        // load-time field reassignment before the call site, and an
        // equal-signature field snapshot — are frontend parse errors
        // (E1049) before any backend. Their semantics live on only in
        // the in-function local shapes above.
        List<String> loadFieldShapes = List.of(
            """
            function noop42(): int { return 42; }
            let g: () => int = noop42;
            let r: int = g();
            export function test(): int { return r; }
            """,
            """
            function inc(x: int): int { return x + 1; }
            function dbl(x: int): int { return x * 2; }
            let f: (x: int) => int = inc;
            f = dbl;
            let r: int = f(2);
            export function test(): int { return r; }
            """,
            """
            function inc(x: int): int { return x + 1; }
            function dbl(x: int): int { return x * 2; }
            let g1: (x: int) => int = inc;
            g1 = dbl;
            let g: (x: int) => int = g1;
            let r: int = g(21);
            export function test(): int { return r; }
            """);
        for (String shape : loadFieldShapes) {
            Frontend lf = compileFrontend(shape, "jvmtest-fv-load-shape.deal");
            check(lf.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "load-time field shape rejected with E1049: " + lf.errors());
        }

        // v1.2 grammar gate: every load-time guard shape (value use of a
        // later-declared function, a not-statically-known field value, an
        // assignment before the call site, and the load-time-called
        // function-body and call-result callee shapes) rests on
        // module-level executable statements, which the v1.2 grammar
        // removes — E1049 before any backend, never a Java forward
        // reference or a silently diverging load-time execution. The
        // in-function live-read value-set edges keep their E6000
        // coverage (the reassigned local/parameter adapter and the
        // call-result adapter cases above).
        record GuardCase(String what, String source) {}
        List<GuardCase> guards = List.of(
            new GuardCase("value use of a later-declared function", """
                let f: () => int = later;
                function later(): int { return 42; }
                export function test(): int { return f(); }
                """),
            new GuardCase("indirect call through a field with a call-valued initializer", """
                function noop42(): int { return 42; }
                function picker(): () => int { return noop42; }
                let g: () => int = picker();
                let r: int = g();
                export function test(): int { return r; }
                """),
            new GuardCase("indirect call whose assigned function reaches a later-declared function", """
                function h(): int { return later(); }
                let g: () => int = h;
                g = h;
                let r: int = g();
                function later(): int { return 1; }
                export function test(): int { return r; }
                """),
            new GuardCase("adapter live-read retargeted to a later-declared function", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return later(x); }
                let g: (x: int) => int = inc;
                let h: (a: int, b: int) => int = g;
                g = dbl;
                let r: int = h(10, 999);
                function later(x: int): int { return x * 2; }
                export function test(): int { return r; }
                """),
            new GuardCase("snapshot field capturing a later-declared function", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return later(x); }
                let g1: (x: int) => int = inc;
                g1 = dbl;
                let g: (x: int) => int = g1;
                let r: int = g(21);
                function later(x: int): int { return x * 2; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "table-literal-hidden field assignment before a load-time indirect call", """
                function zero(): int { return 0; }
                function one(): int { return two(); }
                let g: () => int = zero;
                let t = { x: (g = one) };
                let r: int = g();
                function two(): int { return 2; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "same-statement assignment before a load-time indirect call", """
                function zero(): int { return 0; }
                function one(): int { return two(); }
                function side(f: () => int): int { return f(); }
                let g: () => int = zero;
                let r: int = side(g = one) + g();
                function two(): int { return 2; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "while-body assignment before a load-time indirect call", """
                function inc(x: int): int { return x + 1; }
                function dbl(x: int): int { return later(x); }
                let f: (x: int) => int = inc;
                let c: boolean = true;
                let acc: int = 0;
                while (c) {
                  f = dbl;
                  acc = f(2);
                  c = false;
                }
                function later(x: int): int { return x * 2; }
                export function test(): int { return acc; }
                """),
            new GuardCase(
                "assignment inside a load-time-called function body", """
                function inc(x: int): int { return x + 1; }
                function a(): int { return b(); }
                let g: (x: int) => int = inc;
                function set(): null { g = a; }
                set();
                let r: int = g(2);
                function b(): int { return 42; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "indirect call inside a load-time-called function body", """
                function inc(x: int): int { return x + 1; }
                function a(): int { return b(); }
                let g: (x: int) => int = inc;
                function set(): null { g = a; }
                set();
                function run(): int { return g(2); }
                let r: int = run();
                function b(): int { return 42; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "held function invoking another field indirectly at load time", """
                function inc(x: int): int { return x + 1; }
                function a(): int { return b(); }
                let h: (x: int) => int = inc;
                function run(): int { return h(2); }
                let g: () => int = run;
                let r: int = g();
                function b(): int { return 42; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "sibling indirect call whose field may hold an assigning function", """
                function zero(): int { return 0; }
                let g: () => int = zero;
                function setG(): int { g = one; return 0; }
                function one(): int { return 2; }
                let h: () => int = setG;
                let r: int = h() + g();
                export function test(): int { return r; }
                """),
            new GuardCase(
                "sibling call-result indirect call in the walked statement", """
                function zero(): int { return 0; }
                function picker(): () => int { return zero; }
                let g: () => int = zero;
                let r: int = picker()() + g();
                export function test(): int { return r; }
                """),
            // Module-level indirect calls through NON-identifier callees
            // (a call or assignment producing a function value): the
            // produced value is not statically known to the load-time
            // guard, so every such load-time call is E6000 — LuaJIT
            // fails at load when the produced function reads or reaches
            // a not-yet-declared value, while Java would silently read
            // the uninitialized static wrapper field (a bare
            // NullPointerException) or run the hoisted method.
            new GuardCase(
                "module-level call-result callee returning a later-declared function", """
                function picker(): (x: int) => int { return inc; }
                let r: int = picker()(2);
                function inc(x: int): int { return x + 1; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "module-level call-result callee whose produced function reaches a later-declared function", """
                function mid(x: int): int { return laterFn(); }
                function picker(): (x: int) => int { return mid; }
                let r: int = picker()(2);
                function laterFn(): int { return 42; }
                export function test(): int { return r; }
                """),
            new GuardCase(
                "module-level assignment-produced callee", """
                function inc(x: int): int { return x + 1; }
                let g: (x: int) => int = inc;
                let r: int = (g = inc)(2);
                export function test(): int { return r; }
                """));
        for (GuardCase c : guards) {
            Frontend gf = compileFrontend(c.source, "jvmtest-fv-guard.deal");
            check(gf.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "load-time guard shape '" + c.what()
                    + "' rejected with E1049: " + gf.errors());
        }

        // ISSUE-0301: the shared wrapper scope covers the complete
        // canonical grammar, so function equality/inequality over
        // array/class/nullable-parameter signatures — the former
        // deferred E6000 shapes — now emits wrapper classes and
        // executes: wrapper equality is reference identity, so two
        // distinct declarations never compare equal.
        record DeferredCase(String what, String source) {}
        List<DeferredCase> promotedEquality = List.of(
            new DeferredCase(
                "function equality with array-parameter signatures", """
                function f(xs: int[]): int { return xs[0]; }
                function g(xs: int[]): int { return xs[0]; }
                export function test(): boolean { return f === g; }
                """),
            new DeferredCase(
                "function inequality with class-parameter signatures", """
                class C { v: int = 0; }
                function f(c: C): int { return c.v; }
                function g(c: C): int { return c.v; }
                export function test(): boolean { return f !== g; }
                """),
            new DeferredCase(
                "function equality with nullable-parameter signatures", """
                function f(x: int | null): int { return 1; }
                function g(x: int | null): int { return 2; }
                export function test(): boolean { return f === g; }
                """));
        for (DeferredCase c : promotedEquality) {
            Frontend df = compileFrontend(c.source, "jvmtest-fv-deferred.deal");
            if (!df.errors().isEmpty()) {
                fail("frontend must accept the promoted equality case '"
                    + c.what() + "': " + df.errors());
                continue;
            }
            ExecResult er = compileAndRunJvm(c.source, "jvmtest-fv-deferred");
            check(er.exitCode() == 0 && er.output().contains(
                    c.what().contains("inequality") ? "true" : "false"),
                c.what() + " runs through javac + java with reference "
                    + "identity semantics: " + er.output());
        }

        // ISSUE-0102: nested and nullable function types promoted out of
        // the deferred list — they now emit wrapper shapes.
        List<DeferredCase> promoted = List.of(
            new DeferredCase("nested function type", """
                function inc(x: int): int { return x + 1; }
                export function test(): int {
                  let h: (x: int) => (y: int) => int = function(x: int): (y: int) => int { return inc; };
                  return 1;
                }
                """),
            new DeferredCase("nullable function type", """
                function inc(x: int): int { return x + 1; }
                export function test(): int {
                  let f: ((x: int) => int) | null = inc;
                  return 1;
                }
                """));
        for (DeferredCase c : promoted) {
            Frontend df = compileFrontend(c.source, "jvmtest-fv-promoted.deal");
            if (!df.errors().isEmpty()) {
                fail("frontend must accept the promoted case '" + c.what()
                    + "': " + df.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                df.program(), df.checkResult(), "jvmtest-fv-promoted.deal",
                "main");
            check(!res.hasErrors(),
                "backend now accepts " + c.what() + ": " + res.diagnostics());
        }

        // v1.2 grammar gate: rest parameters and rest function-type arms
        // were removed from the language, so the v1.1 rest function-type
        // shape is a frontend parse error (E1047) before any backend —
        // the deferred-signature E6000 surface for rest arms no longer
        // exists.
        Frontend restShape = compileFrontend("""
            function join(a: int, ...xs: int[]): int { return 1; }
            export function test(): int {
              let f: (a: int, ...xs: int[]) => int = join;
              return 1;
            }
            """, "jvmtest-fv-deferred-rest.deal");
        check(restShape.errors().stream().anyMatch(d -> "E1047".equals(d.code())),
            "rest function-type shape rejected with E1047: " + restShape.errors());
    }

    /**
     * ISSUE-0301 shape-naming property cases (jvm-v12-runtime-value-
     * surface D2/D3, Verification 3): the injective encoding over the
     * complete canonical grammar. {@link JvmBackend#fnShapeId} maps
     * every distinct function signature — primitives including
     * {@code null} and {@code bytes}, arrays, nullables, classes (by
     * canonical identity text), and nested sync/async functions — to a
     * distinct identifier, and the array-shape id
     * ({@code __A$} + escaped descriptor) maps distinct element shapes
     * to distinct identifiers. Generated ids can never collide with
     * {@link JvmBackend#javaName} output: they contain {@code _} or
     * {@code $}, neither of which a translated user identifier can
     * contain.
     */
    private static void testSharedCarrierShapeEncoding() {
        System.out.println("-- Shared carrier shape encoding (ISSUE-0301) --");

        List<Type> types = List.of(
            Type.Boolean.INSTANCE,
            Type.Int.INSTANCE,
            Type.Number.INSTANCE,
            Type.String.INSTANCE,
            Type.Null.INSTANCE,
            Type.Bytes.INSTANCE,
            Type.Table.INSTANCE,
            new Type.Array(Type.Int.INSTANCE),
            new Type.Array(new Type.Array(Type.Int.INSTANCE)),
            new Type.Array(Type.Bytes.INSTANCE),
            new Type.Array(new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Int.INSTANCE, false)),
            new Type.Array(new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Int.INSTANCE, true)),
            new Type.Nullable(Type.Int.INSTANCE),
            new Type.Nullable(IdentityTestFixtures.classType("C", "lib")),
            new Type.Array(new Type.Nullable(Type.String.INSTANCE)),
            IdentityTestFixtures.classType("Box", "lib"),
            IdentityTestFixtures.classType("Box", "main"),
            IdentityTestFixtures.errorClassType(),
            new Type.Func(List.of(), Type.Int.INSTANCE, false),
            new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE, false),
            new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE, true),
            new Type.Func(List.of(Type.Int.INSTANCE, Type.String.INSTANCE),
                Type.Number.INSTANCE, false),
            new Type.Func(List.of(new Type.Array(Type.Int.INSTANCE)),
                Type.Boolean.INSTANCE, false),
            new Type.Func(List.of(new Type.Nullable(Type.Int.INSTANCE)),
                IdentityTestFixtures.classType("C", "lib"), false),
            new Type.Func(List.of(new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Int.INSTANCE, false)), Type.Int.INSTANCE, false),
            new Type.Func(List.of(new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Int.INSTANCE, true)), Type.Int.INSTANCE, false),
            new Type.Func(List.of(Type.Bytes.INSTANCE), Type.Null.INSTANCE,
                false));
        // The shape ids consume the ONE static JVM type-descriptor
        // emitter (ISSUE-0301 descriptor seam): class atoms project
        // from the carried canonical identities, so the property cases
        // exercise the service-driven class atoms.
        Map<String, Type> ids = new LinkedHashMap<>();
        for (Type t : types) {
            String id = t instanceof Type.Func f
                ? JvmBackend.fnShapeId(f)
                : "__A$" + JvmBackend.escapedIdentifier(
                    JvmBackend.typeDescriptor(t));
            Type previous = ids.putIfAbsent(id, t);
            check(previous == null,
                "distinct canonical type " + t + " maps to a distinct id '"
                    + id + "' (collision with " + previous + ")");
            check(id.contains("_") || id.contains("$"),
                "generated shape id '" + id + "' carries a character "
                    + "javaName output can never contain");
        }
        check(ids.size() == types.size(),
            "every canonical shape in the corpus produced a distinct id");
        // Pinned spot values: the primitive letter codes and the async
        // marker position survive the complete-grammar extension.
        check("Fn2_I_I_R_I".equals(JvmBackend.fnShapeId(
                new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
                    Type.Int.INSTANCE, false))),
            "sync (int,int)->int keeps the pinned Fn2_I_I_R_I id");
        check("FnA1_I_R_I".equals(JvmBackend.fnShapeId(
                new Type.Func(List.of(Type.Int.INSTANCE),
                    Type.Int.INSTANCE, true))),
            "async (int)->int maps to the distinct FnA1_I_R_I id");
        check("Fn1_Y_R_V".equals(JvmBackend.fnShapeId(
                new Type.Func(List.of(Type.Bytes.INSTANCE),
                    Type.Null.INSTANCE, false))),
            "bytes params map to the Y code (bytes is covered)");
        // User-name disjointness: javaName escapes $ and _, so no
        // translated user identifier can spell a generated id.
        for (String user : List.of("Fn1_I_R_I", "invoke", "descriptor",
                "__IntArray", "add", "x$1", "_x")) {
            String translated = JvmBackend.javaName(user);
            check(!translated.contains("_"),
                "javaName output never contains a raw underscore ("
                    + translated + ") — the generated ids' underscore "
                    + "positions are unreachable from any user identifier");
            check(!ids.containsKey(translated),
                "the translated user identifier '" + user + "' never "
                    + "equals a generated shape id");
        }
    }

    /**
     * ISSUE-0301 D4 deterministic collection order (the review-round
     * correction of the HashMap-seeded order): the collected
     * project-shape set is seeded ONLY through source-ordered walks —
     * the two intrinsic wrappers, the host declarations in
     * import-statement order (their export maps in declaration order),
     * then the AST walk (declaration order) closing every type
     * annotation and expression type. The result is a pinned exact
     * list: no hash-bucket iteration participates (the checker's
     * typeMap is a HashMap and the host export maps reach the backend
     * through unordered copies — the walk, not their iteration order,
     * drives the output).
     */
    private static void testSharedShapeCollectionOrder() {
        System.out.println("-- Shared shape collection order (ISSUE-0301) --");
        Map<String, Map<String, Type>> hostModules = new LinkedHashMap<>();
        Map<String, Type> hostExports = new LinkedHashMap<>();
        hostExports.put("take", new Type.Func(List.of(Type.String.INSTANCE),
            Type.Int.INSTANCE, false));
        hostExports.put("xs", new Type.Array(Type.Int.INSTANCE));
        hostModules.put("hostx", hostExports);
        Frontend f = compileFrontend("""
            import * as hostx from "hostx"
            function f1(x: int): int { return x; }
            export function g(): int {
              let a: int[] = [1];
              return f1(a[0]);
            }
            """, "jvmtest-shape-order.deal",
            new FixedModuleResolver(Map.of("hostx", hostExports)));
        check(f.errors().isEmpty(),
            "shape-order fixture frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;
        Map<String, CanonicalModuleIdentity> classification =
            new LinkedHashMap<>();
        classification.put("",
            CanonicalModuleIdentity.BuiltinModule.INSTANCE);
        for (String path : List.of("main", "jvmtest-shape-order.deal")) {
            classification.put(path,
                new CanonicalModuleIdentity.ProjectModule(
                    new ProjectModuleIdentity(path, path, List.of())));
        }
        ModuleIdentityResolver.IdentityIndex idx =
            ModuleIdentityResolver.buildIndex(classification);
        List<Type> shapes = JvmBackend.collectShapes(f.program(),
            f.checkResult(), "jvmtest-shape-order.deal", "main",
            Map.of(), Map.of(), hostModules, Map.of(),
            SemanticProfile.LEGACY_SAFE_INT, idx,
            idx.moduleIdentityLookup());
        List<Type> expected = List.of(
            new Type.Func(List.of(Type.Number.INSTANCE),
                Type.Int.INSTANCE, false),
            new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Number.INSTANCE, false),
            new Type.Func(List.of(Type.String.INSTANCE),
                Type.Int.INSTANCE, false),
            new Type.Array(Type.Int.INSTANCE),
            new Type.Func(List.of(Type.Int.INSTANCE),
                Type.Int.INSTANCE, false),
            new Type.Func(List.of(), Type.Int.INSTANCE, false));
        check(shapes.equals(expected),
            "the collected shape list is the pinned source-ordered "
                + "sequence " + expected + ", got: " + shapes);
    }

    /**
     * ISSUE-0301 $check realization behaviors (jvm-v12-runtime-value-
     * surface D5, Verification 4): the generated recursive [D] row
     * accepts the matching shared wrapper and an array-mode $DealRt.Table
     * (the __jsonTableValue dynamic representation — elements checked
     * recursively in index order, E8003 "array element {i} type
     * mismatch" at the first failing index), any other non-array value
     * raises E8001 "expected array"; the function row byte-compares the
     * carried canonical descriptor (a descriptor delta raises E8010, a
     * non-wrapper raises E8001 "expected function"); the bytes row
     * delegates to the $DealRt.Bytes carrier predicate. The array-mode
     * table fixtures build the dynamic representation through a
     * @jsonable class's table field (the __jsonTableValue output) and
     * cross it at a typed array boundary.
     */
    private static void testSharedCarrierCheckBehaviors() throws Exception {
        System.out.println("-- Shared carrier $check behaviors (ISSUE-0301) --");

        // Array-mode table accepted as the [int] dynamic representation.
        ExecResult ok = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): int {
              let w: Wrap | null = Wrap$fromJson(
                  "{\\"data\\": {\\"xs\\": [1, 2]}}");
              if (w !== null) {
                let holder: table = w.data;
                let xs: int[] = holder.xs;
                return xs[1];
              }
              return 0;
            }
            """, "carrier-dynarray-ok");
        check(ok.exitCode() == 0 && ok.output().contains("2"),
            "an array-mode $DealRt.Table crosses an [int] boundary with "
                + "recursive element checks: " + ok.output());

        // E8003 at the first failing index inside the dynamic array.
        ExecResult badElem = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): int {
              let w: Wrap | null = Wrap$fromJson(
                  "{\\"data\\": {\\"xs\\": [1, 2.5, 3]}}");
              if (w !== null) {
                let holder: table = w.data;
                let xs: int[] = holder.xs;
                return xs[0];
              }
              return 0;
            }
            """, "carrier-dynarray-badelem");
        check(badElem.exitCode() == 1
                && badElem.output().contains("DEAL_ERROR_CODE: E8003")
                && badElem.output().contains(
                    "array element 2 type mismatch"),
            "the first failing index raises E8003 \"array element 2 type "
                + "mismatch\" (the inner non-integer cause is suppressed "
                + "like LuaJIT's pcall-wrapped checks): " + badElem.output());

        // Recursive [D] over nested arrays: the dynamic [[int]] row
        // checks elements recursively in index order.
        ExecResult nestedOk = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): int {
              let w: Wrap | null = Wrap$fromJson(
                  "{\\"data\\": {\\"xs\\": [[1, 2], [3, 4]]}}");
              if (w !== null) {
                let holder: table = w.data;
                let rows: int[][] = holder.xs;
                return rows[1][1];
              }
              return 0;
            }
            """, "carrier-dynarray-nested-ok");
        check(nestedOk.exitCode() == 0 && nestedOk.output().contains("4"),
            "an array-mode table crosses a nested [[int]] boundary with "
                + "recursive element checks: " + nestedOk.output());

        ExecResult nestedBad = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): int {
              let w: Wrap | null = Wrap$fromJson(
                  "{\\"data\\": {\\"xs\\": [[1, 2], [3, \\"bad\\"]]}}");
              if (w !== null) {
                let holder: table = w.data;
                let rows: int[][] = holder.xs;
                return rows[0][0];
              }
              return 0;
            }
            """, "carrier-dynarray-nested-bad");
        check(nestedBad.exitCode() == 1
                && nestedBad.output().contains("DEAL_ERROR_CODE: E8003")
                && nestedBad.output().contains(
                    "array element 2 type mismatch"),
            "a failing nested element raises E8003 at the first failing "
                + "index (row 2): " + nestedBad.output());

        // An object-mode table (or any non-array value) raises E8001
        // "expected array" at the [D] boundary.
        ExecResult objMode = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): int {
              let w: Wrap | null = Wrap$fromJson(
                  "{\\"data\\": {\\"xs\\": {\\"x\\": 1}}}");
              if (w !== null) {
                let holder: table = w.data;
                let xs: int[] = holder.xs;
                return 0;
              }
              return 0;
            }
            """, "carrier-dynarray-objmode");
        check(objMode.exitCode() == 1
                && objMode.output().contains("DEAL_ERROR_CODE: E8001")
                && objMode.output().contains("expected array"),
            "an object-mode table raises E8001 \"expected array\" (the "
                + "element descriptor and the kind projection ride the "
                + "error fields): " + objMode.output());

        // A function-typed table read byte-compares the carried
        // descriptor; a non-wrapper raises E8001 "expected function".
        ExecResult fnValue = compileAndRunJvm("""
            function inc(x: int): int { return x + 1; }
            export function test(): int {
              let t: table = { fn: inc };
              let f: (x: int) => int = t.fn;
              return f(41);
            }
            """, "jvmtest-carrier-fnrow-ok");
        check(fnValue.exitCode() == 0 && fnValue.output().contains("42"),
            "a wrapper whose carried descriptor equals the expected text "
                + "passes the function row: " + fnValue.output());

        ExecResult fnBad = compileAndRunJvm("""
            export function test(): int {
              let t: table = { fn: 42 };
              let f: (x: int) => int = t.fn;
              return 0;
            }
            """, "jvmtest-carrier-fnrow-bad");
        check(fnBad.exitCode() == 1
                && fnBad.output().contains("DEAL_ERROR_CODE: E8001")
                && fnBad.output().contains("expected function"),
            "a non-wrapper value raises E8001 \"expected function\" at "
                + "the function row: " + fnBad.output());

        // Function-array [D] row: the emitted $checkArray accepts the
        // typed ((x:int)=>int)[] wrapper (identity) and converts a
        // dynamic array-mode table holding function wrappers with
        // recursive element checks — E8003 "array element {i} type
        // mismatch" at the first failing index. No DEAL expression can
        // build a dynamic table holding function values (functions are
        // not JSON), so the probe drives the REAL emitted helpers with
        // a hand-built runner over the production artifact.
        Frontend fnArrProbe = compileFrontend("""
            function inc(x: int): int { return x + 1; }
            export function test(): int {
              let holder: table = {};
              let fs: ((x: int) => int)[] = holder.fs;
              return 0;
            }
            """, "jvmtest-carrier-fnarr.deal");
        check(fnArrProbe.errors().isEmpty(),
            "function-array probe frontend clean: " + fnArrProbe.errors());
        if (fnArrProbe.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                fnArrProbe.program(), fnArrProbe.checkResult(),
                "jvmtest-carrier-fnarr.deal", "Main");
            check(!res.hasErrors(),
                "function-array probe codegen clean: " + res.diagnostics());
            Path dir = Files.createTempDirectory("jvmtest_fnarr_");
            Files.writeString(dir.resolve("Main.java"), res.source());
            Files.writeString(dir.resolve("Runner.java"), """
                public final class Runner {
                    public static void main(String[] args) {
                        try {
                            java.util.ArrayList<java.lang.Object> els =
                                new java.util.ArrayList<>();
                            els.add(Main.inc$fn);
                            els.add(java.lang.Long.valueOf(42));
                            $DealRt.Table t = new $DealRt.Table(els);
                            Main.$check("[(int)->int]", t);
                            System.out.println("no-error");
                        } catch (Main.DealError e) {
                            System.out.println("DEAL_ERROR_CODE: " + e.code);
                            System.out.println(e.getMessage());
                            System.exit(1);
                        }
                    }
                }
                """);
            StringBuilder javacErr = new StringBuilder();
            boolean javacOk = StubModuleResolver.compileWithJavac(dir,
                List.of("Main.java", "Runner.java"), javacErr);
            check(javacOk, "function-array probe artifacts compile: "
                + javacErr);
            if (javacOk) {
                ProcessBuilder java = new ProcessBuilder("java", "-cp",
                    dir.toString(), "Runner");
                java.redirectErrorStream(true);
                Process p = java.start();
                String out = new String(p.getInputStream().readAllBytes())
                    .trim();
                int exit = p.waitFor();
                check(exit == 1
                        && out.contains("DEAL_ERROR_CODE: E8003")
                        && out.contains("array element 2 type mismatch"),
                    "a dynamic function-array conversion raises E8003 at "
                        + "the first failing index (element 2, the Long "
                        + "is not a wrapper): " + out);
                Files.writeString(dir.resolve("Runner.java"), """
                    public final class Runner {
                        public static void main(String[] args) {
                            try {
                                java.util.ArrayList<java.lang.Object> els =
                                    new java.util.ArrayList<>();
                                els.add(Main.inc$fn);
                                $DealRt.Table t = new $DealRt.Table(els);
                                Main.$check("[(int)->int]", t);
                                System.out.println("fn-array-row-ok");
                            } catch (Main.DealError e) {
                                System.out.println("DEAL_ERROR_CODE: " + e.code);
                                System.exit(1);
                            }
                        }
                    }
                    """);
                ProcessBuilder javac2 = new ProcessBuilder("javac",
                    "-encoding", "UTF-8", "Main.java", "Runner.java");
                javac2.directory(dir.toFile());
                javac2.redirectErrorStream(true);
                Process p2 = javac2.start();
                String javacOut2 = new String(
                    p2.getInputStream().readAllBytes()).trim();
                int javacExit2 = p2.waitFor();
                check(javacExit2 == 0,
                    "positive runner compiles: " + javacOut2);
                ProcessBuilder java2 = new ProcessBuilder("java", "-cp",
                    dir.toString(), "Runner");
                java2.redirectErrorStream(true);
                Process p3 = java2.start();
                String out2 = new String(p3.getInputStream().readAllBytes())
                    .trim();
                int exit2 = p3.waitFor();
                check(exit2 == 0 && out2.contains("fn-array-row-ok"),
                    "a dynamic function-array of genuine wrappers passes "
                        + "the [D] row element-wise: " + out2);
            }
            try {
                Files.walk(dir).sorted(Comparator.reverseOrder())
                    .forEach(p2 -> { try { Files.deleteIfExists(p2); }
                        catch (IOException ignored) {} });
            } catch (IOException ignored) { }
        }

        // The bytes row delegates to the $DealRt.Bytes carrier predicate
        // (matcher table): emission inspection — the ISSUE-0158 bytes
        // lane constructs real $DealRt.Bytes values through the emitted
        // helpers (testBytesRuntimeLane exercises the behavior).
        Frontend bytesProbe = compileFrontend("""
            export function test(): int { return 1; }
            """, "jvmtest-carrier-bytesrow.deal");
        check(bytesProbe.errors().isEmpty(),
            "bytes-row probe frontend clean: " + bytesProbe.errors());
        if (bytesProbe.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                bytesProbe.program(), bytesProbe.checkResult(),
                "jvmtest-carrier-bytesrow.deal", "main");
            check(!res.hasErrors(), "bytes-row probe codegen clean: "
                + res.diagnostics());
            check(res.source().contains(
                    "if (descriptor.equals(\"bytes\")) { if (v "
                        + "instanceof $DealRt.Bytes b) return b;"),
                "the emitted $check carries the canonical bytes row over "
                    + "the $DealRt.Bytes carrier");
            check(res.source().contains(
                    "static final class Bytes {"),
                "the shared $DealRt scope carries the final Bytes wrapper "
                    + "over byte[]");
        }
    }

    /**
     * ISSUE-0301 identity/equality across module boundaries
     * (jvm-v12-runtime-value-surface Verification 5): wrapper reference
     * equality, alias-observed writes, and append stability hold when
     * the carriers cross a module boundary — the shared $DealRt classes
     * keep one identity per project. Executes the real orchestrator
     * pipeline (codegen → javac → java).
     */
    private static void testSharedCarrierCrossModuleIdentity()
            throws Exception {
        System.out.println("-- Shared carrier cross-module identity (ISSUE-0301) --");

        writeFile("src/lib.deal", """
            export function make(): int[] { return [5]; }
            export function sum(xs: int[]): int { return xs[0] + xs[1]; }
            export function picker(): (x: int) => int { return inc; }
            function inc(x: int): int { return x + 1; }
            """);
        writeFile("src/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int {
              let a: int[] = lib.make();
              a[1] = 7;
              a[0] = 9;
              let b: int[] = a;
              b[1] = 8;
              let f1: (x: int) => int = lib.picker();
              let f2: (x: int) => int = lib.picker();
              let eq: int = 0;
              if (f1 === f2) { eq = 1; }
              let t: table = { fn: lib.picker() };
              let f3: (x: int) => int = t.fn;
              return lib.sum(a) + a[1] + f1(40) + eq + f3(0);
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/carrier_identity");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success = orchestrator.compile();
        check(success, "shared-carrier identity project compiles: "
            + orchestrator.diagnostics());
        if (success && Files.exists(outputDir.resolve("Entry.java"))) {
            ExecResult exec = runJvmArtifacts(outputDir,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("68"),
                "cross-module identity holds: lib.sum(a)=17 (the lib-built "
                    + "array keeps its identity and observes the entry's "
                    + "append and aliased write when passed back), a[1]=8, "
                    + "f1(40)=41, wrapper reference equality =1, "
                    + "table-read wrapper byte-compare passes and f3(0)=1 "
                    + "→ 68: " + exec.output());
        }
    }

    /**
     * ISSUE-0301 host-class-typed shapes now flow on the ISSUE-0303
     * synthesized shared records: a project whose non-entry module
     * imports a host module with a class export pre-registers
     * shared-scope wrappers whose invoke signatures reference the
     * synthesized {@code $DealRt.$Host$...} record classes (single
     * emission point, canonical externals identity) — the pre-0303
     * state rejected the project at the import (the retired E6000
     * exclusion), and the pre-fix shared-scope wrapper over the
     * never-emitted host Java class can no longer exist. The project
     * compiles through the real orchestrator pipeline (collection seam
     * → codegen → publish), the entry artifact carries the synthesized
     * record and the wrapper reference, and the artifact set runs
     * against a real host implementation class.
     */
    private static void testSharedCarrierHostClassShapes()
            throws Exception {
        System.out.println("-- Shared carrier host-class shapes on the "
            + "synthesized records (ISSUE-0303) --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "externals": {
                "host/cfg": { "declaration": "bindings/cfg.d.deal" }
              }
            }
            """);
        writeFile("bindings/cfg.d.deal", """
            export class ServerConfig {
              port: int;
            }
            export function load(): ServerConfig;
            """);
        writeFile("src/hostshape_lib.deal", """
            import * as Cfg from "host/cfg"
            export function load(): Cfg.ServerConfig {
              return Cfg.load();
            }
            """);
        writeFile("src/hostshape_entry.deal", """
            import * as Lib from "./hostshape_lib"
            export function main(): null { return null; }
            """);
        // The host implementation class: the declared class's defaults
        // map (load-time capture) and a load() returning a synthesized
        // record instance.
        writeFile("HostCfg.java", """
            public final class HostCfg {
                public static final java.util.Map<String, Object> ServerConfig_defaults =
                    java.util.Map.of("port", Integer.valueOf(8080));
                public static Object load() {
                    return new $DealRt.$Host$host$scfg$ServerConfig(8080);
                }
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/hostshape_entry.deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get()
            .resolve("build/hostclass_shapes");
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        Map<String, String> externals = Map.of("host/cfg",
            tmpDir.get().resolve("bindings/cfg.d.deal").toString());
        check(Files.exists(tmpDir.get().resolve("bindings/cfg.d.deal")),
            "deal.json externals bind the host declaration");
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputRoot,
            false,
            false,
            false,
            false,
            Backend.JVM,
            externals,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean ok = orchestrator.compile();
        check(ok, "the host-class project compiles (the synthesized "
            + "records replace the retired import-time E6000): "
            + orchestrator.diagnostics());
        Path entryArtifact = outputRoot.resolve("Hostshape_entry.java");
        check(Files.exists(entryArtifact),
            "the entry artifact is published for the host-class project");
        if (Files.exists(entryArtifact)) {
            String java = Files.readString(entryArtifact);
            check(java.contains("$Host$host$scfg$ServerConfig"),
                "the shared $DealRt scope synthesizes the declared host "
                    + "class record (deterministic specifier + class name)");
            check(java.contains("interface FnValue"),
                "the shared $DealRt scope still carries the function "
                    + "carrier interface");
        }
        // The artifact set runs against the real host class: the load
        // method captures the defaults map reflectively and the
        // synthesized-record return crosses the class-typed boundary.
        Files.copy(tmpDir.get().resolve("HostCfg.java"),
            outputRoot.resolve("HostCfg.java"));
        ExecResult exec = runJvmArtifacts(outputRoot,
            parseProgram("export function main(): null { return null; }"),
            "Hostshape_entry");
        check(exec.exitCode() == 0,
            "the host-class artifact set runs against the real host "
                + "class (exit 0): " + exec.output());
    }

    /**
     * ISSUE-0570 acceptance remediation: declared host-class ARRAY
     * parameters/returns execute on the shared per-class
     * {@code $DealRt.$HostArr$...} {@code __RefArray} carrier — the
     * remaining import-time E6000 is removed
     * (jvm-v12-host-abi-completion D1's blanket gate removal). The
     * wrapper seam keeps the D2 boundary checks: carrier and
     * wrong-kind element failures raise E8010 (parameter {i} / return
     * value 1 mismatch) and a foreign-identity element raises the
     * pinned nominal E8001 (the class-typed identity rule extended to
     * class elements). The nullable-array and nullable-element forms
     * join the same carrier, and the record FIELD position keeps its
     * existing class-element array storage (the presence fixture's
     * peers pin).
     */
    private static void testHostClassArraySeamRuntime()
            throws Exception {
        System.out.println("-- Host class-array seam runtime support "
            + "(ISSUE-0570) --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "externals": {
                "host/cfg": { "declaration": "bindings/cfg.d.deal" },
                "host/other": { "declaration": "bindings/other.d.deal" }
              }
            }
            """);
        writeFile("bindings/cfg.d.deal", """
            export class ServerConfig {
              port: int;
            }
            export function make(): ServerConfig[];
            export function makeMaybe(): ServerConfig[] | null;
            export function makeForeign(): ServerConfig[];
            export function makeJunk(): ServerConfig[];
            export function makeBadCarrier(): ServerConfig[];
            export function makeWithNull(): ServerConfig[];
            export function take(cfgs: ServerConfig[]): int;
            export function takeMaybe(cfgs: (ServerConfig | null)[]): int;
            """);
        writeFile("bindings/other.d.deal", """
            export class ServerConfig {
              value: string;
            }
            """);
        writeFile("src/entry.deal", """
            import * as cfg from "host/cfg"
            import * as other from "host/other"
            export function main(): null { return null; }
            export function run(): int { let cs = cfg.make(); if (cs.length !== 2) { throw { code: "TEST_FAIL", message: "host class array return length mismatch" }; } return cfg.take(cs); }
            export function runMaybe(): int { let cs = cfg.makeMaybe(); if (cs !== null) { return cs.length; } return 0; }
            export function runTakeMaybe(): int { let holder: table = { v: cfg.make() }; let cs: (cfg.ServerConfig | null)[] = holder.v; return cfg.takeMaybe(cs); }
            export function runForeign(): int { let cs = cfg.makeForeign(); return cs.length; }
            export function runForeignParam(): int { let cs = cfg.makeForeign(); return cfg.take(cs); }
            export function runJunk(): int { let cs = cfg.makeJunk(); return cs.length; }
            export function runBadCarrier(): int { let cs = cfg.makeBadCarrier(); return cs.length; }
            export function runParamCarrier(): int { let holder: table = { v: "x" }; return cfg.take(holder.v); }
            export function runParamNullElem(): int { let cs = cfg.makeWithNull(); return cfg.take(cs); }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/class_array_runtime");
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        Map<String, String> externals = Map.of(
            "host/cfg",
            tmpDir.get().resolve("bindings/cfg.d.deal").toString(),
            "host/other",
            tmpDir.get().resolve("bindings/other.d.deal").toString());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputRoot,
            false,
            false,
            false,
            false,
            Backend.JVM,
            externals,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean ok = orchestrator.compile();
        check(ok, "the class-array host export shapes compile (the "
            + "import-time E6000 is gone): " + orchestrator.diagnostics());
        Path artifact = outputRoot.resolve("Entry.java");
        check(ok && Files.exists(artifact),
            "the entry artifact is published for the class-array project");
        if (ok && Files.exists(artifact)) {
            String java = Files.readString(artifact);
            check(java.contains("$HostArr$host$scfg$ServerConfig"),
                "the wrapper seam and the shared scope reference the "
                    + "per-class $HostArr$ carrier");
            check(java.contains("$Host$host$sother$ServerConfig"),
                "the second declared host class's record is synthesized "
                    + "in the shared scope");
        }
        if (ok) {
            Files.writeString(outputRoot.resolve("HostCfg.java"), """
                public final class HostCfg {
                    public static final java.util.Map<String, Object> ServerConfig_defaults =
                        java.util.Map.of("port", Integer.valueOf(8080));
                    public static Object make() {
                        return new $DealRt.$HostArr$host$scfg$ServerConfig(new Object[] {
                            new $DealRt.$Host$host$scfg$ServerConfig(Integer.valueOf(11)),
                            new $DealRt.$Host$host$scfg$ServerConfig(Integer.valueOf(22))
                        });
                    }
                    public static Object makeMaybe() { return null; }
                    public static Object makeForeign() {
                        return new $DealRt.$HostArr$host$scfg$ServerConfig(new Object[] {
                            new $DealRt.$Host$host$sother$ServerConfig("x")
                        });
                    }
                    public static Object makeJunk() {
                        return new $DealRt.$HostArr$host$scfg$ServerConfig(new Object[] { "junk" });
                    }
                    public static Object makeBadCarrier() {
                        return new $DealRt.__StringArray(new String[] { "a" });
                    }
                    public static Object makeWithNull() {
                        return new $DealRt.$HostArr$host$scfg$ServerConfig(new Object[] { null });
                    }
                    public static Object take($DealRt.$HostArr$host$scfg$ServerConfig cfgs) {
                        int t = 0;
                        for (java.lang.Object o : cfgs.data) {
                            t += ((Integer) (($DealRt.$Host$host$scfg$ServerConfig) o).port).intValue();
                        }
                        return Integer.valueOf(t);
                    }
                    public static Object takeMaybe($DealRt.$HostArr$host$scfg$ServerConfig cfgs) {
                        return Integer.valueOf(cfgs.data.length);
                    }
                }
                """);
            Files.writeString(outputRoot.resolve("HostOther.java"), """
                public final class HostOther {
                    public static final java.util.Map<String, Object> ServerConfig_defaults =
                        java.util.Map.of("value", new Object());
                }
                """);

            // Success scenario: the plain and nullable forms cross the
            // boundary on the one shared carrier (33 / 0 / 2).
            ExecResult okRun = runJvmArtifacts(outputRoot, parseProgram("""
                import * as cfg from "host/cfg"
                export function main(): null { return null; }
                export function run(): int { return 1; }
                export function runMaybe(): int { return 1; }
                export function runTakeMaybe(): int { return 1; }
                """), "Entry");
            check(okRun.exitCode() == 0
                    && okRun.output().equals("33\n0\n2"),
                "the class-array project executes against the real host "
                    + "(33/0/2): " + okRun.output());

            // Foreign-identity element on the RETURN side: the nominal
            // E8001 propagates unchanged (never wrapped E8010).
            ExecResult foreign = runJvmArtifacts(outputRoot, parseProgram("""
                import * as cfg from "host/cfg"
                export function main(): null { return null; }
                export function runForeign(): int { return 1; }
                """), "Entry");
            check(foreign.exitCode() == 1
                    && foreign.output().contains("DEAL_ERROR_CODE: E8001")
                    && foreign.output().contains("expected instance of"),
                "a foreign-identity class element in a host class-array "
                    + "RETURN raises the pinned nominal E8001: "
                    + foreign.output());

            // Foreign-identity element on the PARAMETER side: same E8001.
            ExecResult foreignParam = runJvmArtifacts(outputRoot,
                parseProgram("""
                    import * as cfg from "host/cfg"
                    export function main(): null { return null; }
                    export function runForeignParam(): int { return 1; }
                    """), "Entry");
            check(foreignParam.exitCode() == 1
                    && foreignParam.output().contains("DEAL_ERROR_CODE: E8001")
                    && foreignParam.output().contains("expected instance of"),
                "a foreign-identity class element in a host class-array "
                    + "PARAMETER raises the pinned nominal E8001: "
                    + foreignParam.output());

            // Wrong-kind element (return side): E8010 return mismatch
            // wrapping the E8003 element failure.
            ExecResult junk = runJvmArtifacts(outputRoot, parseProgram("""
                import * as cfg from "host/cfg"
                export function main(): null { return null; }
                export function runJunk(): int { return 1; }
                """), "Entry");
            check(junk.exitCode() == 1
                    && junk.output().contains("DEAL_ERROR_CODE: E8010")
                    && junk.output().contains("array element 1 type mismatch"),
                "a wrong-kind element in a host class-array return "
                    + "raises E8010: " + junk.output());

            // Wrong carrier (return side): E8010.
            ExecResult badCarrier = runJvmArtifacts(outputRoot,
                parseProgram("""
                    import * as cfg from "host/cfg"
                    export function main(): null { return null; }
                    export function runBadCarrier(): int { return 1; }
                    """), "Entry");
            check(badCarrier.exitCode() == 1
                    && badCarrier.output().contains("DEAL_ERROR_CODE: E8010"),
                "a wrong carrier in a host class-array return raises "
                    + "E8010: " + badCarrier.output());

            // Wrong carrier (parameter side, table-read deferral):
            // E8010 parameter mismatch at the call.
            ExecResult paramCarrier = runJvmArtifacts(outputRoot,
                parseProgram("""
                    import * as cfg from "host/cfg"
                    export function main(): null { return null; }
                    export function runParamCarrier(): int { return 1; }
                    """), "Entry");
            check(paramCarrier.exitCode() == 1
                    && paramCarrier.output().contains("DEAL_ERROR_CODE: E8010")
                    && paramCarrier.output().contains("parameter 1 type mismatch"),
                "a non-array argument at a host class-array parameter "
                    + "raises E8010 parameter mismatch: "
                    + paramCarrier.output());

            // Null element crossing the plain C[] parameter: E8010
            // (the single carrier serves both shapes, so the element
            // row rejects the null).
            ExecResult paramNull = runJvmArtifacts(outputRoot,
                parseProgram("""
                    import * as cfg from "host/cfg"
                    export function main(): null { return null; }
                    export function runParamNullElem(): int { return 1; }
                    """), "Entry");
            check(paramNull.exitCode() == 1
                    && paramNull.output().contains("DEAL_ERROR_CODE: E8010")
                    && paramNull.output().contains("array element 1 type mismatch"),
                "a null element crossing the plain C[] parameter raises "
                    + "E8010: " + paramNull.output());
        }

        // The record FIELD position keeps class-element arrays: the
        // presence-shape peers field still compiles through the
        // per-class $HostArr$ carrier.
        writeFile("bindings/cfg.d.deal", """
            export class ServerConfig {
              port: int;
              peers?: ServerConfig[];
            }
            export function ping(): string;
            """);
        writeFile("src/entry.deal", """
            import * as cfg from "host/cfg"
            export function main(): null { return null; }
            export function run(): string { return cfg.ping(); }
            """);
        Path outputRoot2 = tmpDir.get().resolve("build/class_array_field");
        Map<String, String> externals2 = Map.of("host/cfg",
            tmpDir.get().resolve("bindings/cfg.d.deal").toString());
        CompilationOrchestrator orchestrator2 = new CompilationOrchestrator(
            entryFile,
            outputRoot2,
            false,
            false,
            false,
            false,
            Backend.JVM,
            externals2,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean ok2 = orchestrator2.compile();
        check(ok2, "a class-array host-class FIELD stays supported (the "
            + "record storage maps onto the $HostArr$ carrier): "
            + orchestrator2.diagnostics());
        if (ok2) {
            Path artifact2 = outputRoot2.resolve("Entry.java");
            check(Files.exists(artifact2),
                "field-variant entry artifact published");
            if (Files.exists(artifact2)) {
                String java = Files.readString(artifact2);
                check(java.contains("$HostArr$host$scfg$ServerConfig"),
                    "the shared scope emits the per-class $HostArr$ "
                        + "wrapper for the class-array field");
            }
        }
    }

    /**
     * ISSUE-0301 qualified imported-class shapes in a NON-ENTRY module:
     * a checker-legal project where a non-entry module declares a
     * function with a qualified imported-class parameter must compile
     * into a javac-clean artifact set — the entry module's shared
     * {@code $DealRt} declares the collected wrapper classes and their
     * invoke signatures reference the real declaring module's emitted
     * class. Pre-fix defects: the silent collection resolver looked the
     * import ALIAS up in the RAW-path-keyed importResolutions map, so
     * the shape was silently dropped (Type.Error) from the project-wide
     * set, and the entry's shared-scope pre-registration resolved class
     * references only through its own direct imports, so a shape
     * referencing a class from a module the entry does not import
     * produced an artifact javac rejected ("cannot find symbol: class
     * Fn1_$$asrc$sU_R_I") after the CLI reported success. Both breaks
     * reproduce through the real orchestrator pipeline; the second
     * variant (entry directly imports the declaring module) pins the
     * alias-keyed collection fix, the first pins the compilation-wide
     * class-declaration identity surface.
     */
    private static void testSharedCarrierIndirectClassShape()
            throws Exception {
        System.out.println("-- Shared carrier indirect qualified-class shape (ISSUE-0301) --");

        writeFile("src/util.deal", """
            export class U {
              x: int = 0;
            }
            """);
        writeFile("src/lib.deal", """
            import * as util from "./util"
            export function make(): util.U { return { x: 5 }; }
            export function inc(u: util.U): int { return u.x; }
            """);
        writeFile("src/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int { return 42; }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal")
            .toAbsolutePath().normalize();
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());

        // Variant 1: the entry imports ONLY lib — the declaring module
        // (util) is not one of the entry's direct imports, so the
        // wrapper's Util.$C_U invoke reference must resolve through the
        // compilation-wide class-declaration identity surface.
        Path outputDir1 = tmpDir.get().resolve("build/indirect_class_shape");
        CompilationOrchestrator orchestrator1 = new CompilationOrchestrator(
            entryFile,
            outputDir1,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean ok1 = orchestrator1.compile();
        check(ok1, "indirect qualified-class project compiles (entry "
            + "imports only lib): " + orchestrator1.diagnostics());
        if (ok1) {
            Path entryArtifact = outputDir1.resolve("Entry.java");
            check(Files.exists(entryArtifact),
                "the two-pass site writes the clean entry artifact");
            if (Files.exists(entryArtifact)) {
                String artifact = Files.readString(entryArtifact);
                check(artifact.contains("Fn1_$$asrc$sU_R_I")
                        && artifact.contains("invoke(Util.$C_U p0)"),
                    "the entry's shared $DealRt declares the collected "
                        + "(util.U)->int wrapper whose invoke references "
                        + "the real declaring module's class (pre-fix: "
                        + "the shape was dropped by the raw-path-keyed "
                        + "silent resolver and Lib.java referenced a "
                        + "wrapper javac rejected as 'cannot find "
                        + "symbol')");
                check(artifact.contains("Fn0_R_$$asrc$sU")
                        && artifact.contains("Util.$C_U invoke()"),
                    "the ()->util.U wrapper (the make export) is "
                        + "pre-registered the same way");
            }
            ExecResult exec = runJvmArtifacts(outputDir1,
                parseProgram("export function run(): int { return 42; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("42"),
                "the full artifact set is javac-clean and executes: "
                    + exec.output());
        }

        // Variant 2: the entry imports lib AND util directly — the shape
        // is dropped during the NON-ENTRY module's collection (the
        // alias-keyed silent resolver) unless the silent QualifiedType
        // arm uses the alias map; the entry's own direct imports then
        // resolve the wrapper reference.
        writeFile("src/entry.deal", """
            import * as lib from "./lib"
            import * as util from "./util"
            export function main(): null { return null; }
            export function run(): int { return 42; }
            """);
        Path outputDir2 = tmpDir.get().resolve("build/direct_class_shape");
        CompilationOrchestrator orchestrator2 = new CompilationOrchestrator(
            entryFile,
            outputDir2,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean ok2 = orchestrator2.compile();
        check(ok2, "direct-import qualified-class project compiles (entry "
            + "imports lib and util): " + orchestrator2.diagnostics());
        if (ok2) {
            Path entryArtifact = outputDir2.resolve("Entry.java");
            check(Files.exists(entryArtifact),
                "the two-pass site writes the clean entry artifact");
            if (Files.exists(entryArtifact)) {
                String artifact = Files.readString(entryArtifact);
                check(artifact.contains("Fn1_$$asrc$sU_R_I")
                        && artifact.contains("invoke(Util.$C_U p0)"),
                    "the shared $DealRt declares the (util.U)->int "
                        + "wrapper in the direct-import variant too");
            }
            ExecResult exec = runJvmArtifacts(outputDir2,
                parseProgram("export function run(): int { return 42; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("42"),
                "the direct-import artifact set is javac-clean and "
                    + "executes: " + exec.output());
        }
    }

    /**
     * ISSUE-0301 cross-module function values on the shared $DealRt
     * carriers: the per-signature wrapper classes live in ONE shared
     * scope emitted by the selected entry module, so function values
     * cross a project-module boundary unchanged — a Func-typed argument
     * to an imported module call, a Func-typed call result used as an
     * assignment value, and an imported call-result callee all compile
     * and execute (the pre-fix per-module wrapper classes were artifacts
     * javac rejected after the CLI reported success), and the
     * member-call path now applies the same LuaJIT parameter-boundary
     * E8010 check the same-module path emits (an arity-extension
     * argument raises "function signature mismatch: expected
     * (int,string)->int, got (int)->int" at the imported call). The
     * The same four shapes are pinned directly by this focused
     * multi-module backend test.
     */
    private static void testCrossModuleFunctionValues() throws Exception {
        System.out.println("-- Orchestrator: cross-module function values on the shared carriers --");

        record XmodCase(String what, String libSource, String entrySource,
                        String expectedOutput, String expectedErrorCode) {}
        List<XmodCase> cases = List.of(
            new XmodCase("callback argument",
                "export function apply(f: (x: int) => int, v: int): int { return f(v); }\n",
                "import * as lib from \"./lib\"\n"
                    + "function inc(x: int): int { return x + 1; }\n"
                    + "export function main(): null { return null; }\n"
                    + "export function test(): int { return lib.apply(inc, 41); }\n",
                "42", null),
            new XmodCase("arity-extension argument (E8010 boundary)",
                "export function apply2(f: (a: int, b: string) => int, v: int): int { return f(v, \"i\"); }\n",
                "import * as lib from \"./lib\"\n"
                    + "function inc(x: int): int { return x + 1; }\n"
                    + "export function main(): null { return null; }\n"
                    + "export function test(): int { return lib.apply2(inc, 41); }\n",
                null, "E8010"),
            new XmodCase("returned function value",
                "export function picker(): (x: int) => int { return inc; }\n"
                    + "function inc(x: int): int { return x + 1; }\n",
                "import * as lib from \"./lib\"\n"
                    + "export function main(): null { return null; }\n"
                    + "export function test(): int {\n"
                    + "  let f: (x: int) => int = lib.picker();\n"
                    + "  return f(41);\n"
                    + "}\n",
                "42", null),
            new XmodCase("imported call-result callee",
                "export function picker(): (x: int) => int { return inc; }\n"
                    + "function inc(x: int): int { return x + 1; }\n",
                "import * as lib from \"./lib\"\n"
                    + "export function main(): null { return null; }\n"
                    + "export function test(): int { return lib.picker()(41); }\n",
                "42", null));

        for (XmodCase c : cases) {
            writeFile("src/lib.deal", c.libSource());
            writeFile("src/entry.deal", c.entrySource());

            Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
            Path outputDir = tmpDir.get().resolve("build/xmod_fv");
            List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

            boolean success = orchestrator.compile();
            check(success, "cross-module function-value case '" + c.what()
                + "' compiles: " + orchestrator.diagnostics());
            Path entryArtifact = outputDir.resolve("Entry.java");
            check(success && Files.exists(entryArtifact),
                "entry artifact written for '" + c.what() + "'");
            if (!success || !Files.exists(entryArtifact)) {
                continue;
            }
            ExecResult exec = runJvmArtifacts(outputDir,
                parseProgram("export function test(): int { return 0; }"),
                "Entry");
            if (c.expectedErrorCode() == null) {
                check(exec.exitCode() == 0
                        && exec.output().contains(c.expectedOutput()),
                    "cross-module case '" + c.what() + "' runs through "
                        + "javac + java and prints " + c.expectedOutput()
                        + ": " + exec.output());
            } else {
                check(exec.exitCode() == 1
                        && exec.output().contains("DEAL_ERROR_CODE: "
                            + c.expectedErrorCode()),
                    "cross-module case '" + c.what() + "' raises "
                        + c.expectedErrorCode() + " at the imported "
                        + "parameter boundary: " + exec.output());
            }

            if (Files.isDirectory(outputDir)) {
                try (var stream = Files.walk(outputDir)) {
                    stream.sorted(Comparator.reverseOrder()).forEach(f -> {
                        try { Files.deleteIfExists(f); } catch (IOException ignored) {}
                    });
                }
            }
        }
    }

    private static void testUseBeforeDeclarationRejected() {
        // v1.2 grammar gate: module-field use-before-declaration shapes
        // (module-level lets/ifs) are frontend parse errors (E1049). The
        // in-function shape keeps its E6000 backend rejection.
        List<String> sources = List.of(
            // self-reference in a local initializer
            "export function test(): int { let x: int = x + 1; return x; }",
            // use of a local before its declaration
            """
            import * as console from "std/console"
            export function test(): null {
              console.log(x);
              let x: string = "later";
            }
            """);

        for (String source : sources) {
            Frontend f = compileFrontend(source, "jvmtest-usebefore.deal");
            if (!f.errors().isEmpty()) {
                fail("checker must accept the use-before-declaration probe "
                    + "(the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f.program(), f.checkResult(),
                    "jvmtest-usebefore.deal", "main");
            check(res.hasErrors(), "backend rejects use-before-declaration");
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 for use-before-declaration: " + res.diagnostics());
        }

        List<String> moduleShapes = List.of(
            "let x: int = x + 1;\nexport function test(): int { return x; }",
            "let b: int = c + 1;\nlet c: int = 2;\nexport function test(): int { return b; }",
            """
            if (x === 1) { }
            let x: int = 1;
            export function test(): int { return x; }
            """);
        for (String shape : moduleShapes) {
            Frontend f = compileFrontend(shape, "jvmtest-usebefore.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "module-field use-before-declaration shape rejected with E1049: "
                    + f.errors());
        }
    
    }

    /**
     * A write to a later-declared function-local with no enclosing binding
     * must be rejected, never emitted as a Java forward reference that
     * javac rejects after the CLI reported success (`x = 5; let x = 1`
     * inside a function: LuaJIT writes the enclosing scope and then the
     * later `local` shadows it; Java has no forward-reference target).
     * Module-level writes to later-declared fields stay allowed
     * (JLS §8.3.3 forward-reference LHS exception; the later initializer
     * wins, exactly like LuaJIT), and so do function-body writes to a
     * module field declared BEFORE the function (LuaJIT's upvalue write —
     * full parity). Function-body writes to a field declared AFTER the
     * function are E6000 (LuaJIT binds them to the GLOBAL, leaving the
     * module-local untouched; a Java static-field write would pollute
     * later readers) — covered by
     * {@link #testFunctionBodyModuleFieldAccessGuards()}.
     */
    /**
     * Function-body access to a module field is governed by the field's
     * declaration order relative to the function:
     * <ul>
     * <li>a function declared AFTER the field reads/writes the
     * module-local upvalue — emitted as a plain static-field access,
     * full parity (the canonical write-then-read shape is allowed and
     * runs identically on both backends, pinned by the cross-backend
     * fixture {@code jvm-function-field-write-parity});</li>
     * <li>a function declared BEFORE the field does not capture the
     * module-local under LuaJIT (the local does not exist when the
     * function value is created): every access in its body binds to the
     * GLOBAL of the same name. A no-prior-write read reads the global
     * nil at call time and fails (E8001) while Java would silently read
     * the initialized static field; a write targets the global — the
     * module-local is untouched, so later readers observe the
     * initializer value — while Java would write the static field and
     * pollute every later reader. Both shapes are E6000 (the
     * write-then-read shape included: the function's own read observes
     * the global write under LuaJIT, but the polluted Java field remains
     * observable by later readers).</li>
     * </ul>
     */
    private static void testFunctionBodyModuleFieldAccessGuards() throws Exception {
        // v1.2 grammar gate: module fields were removed, so every
        // function-body module-field access shape (declared-before and
        // declared-after) is a frontend parse error (E1049). The
        // function-local access rules they guarded survive unchanged.
        List<String> shapes = List.of(
            """
            let x: int = 1;
            function f(): int { x = 5; return x; }
            export function test(): int { return f() + x; }
            """,
            """
            function f(): int { return x; }
            let x: int = 5;
            export function test(): int { return f(); }
            """,
            """
            function f(): null { if (true) { x = 5; } }
            let x: int = 1;
            export function test(): int { f(); return 1; }
            """);
        for (String shape : shapes) {
            Frontend f = compileFrontend(shape, "jvmtest-field-access-shape.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "function-body module-field access shape rejected with E1049: "
                    + f.errors());
        }
    
    }

    private static void testAssignmentBeforeDeclarationRejected() throws Exception {
        System.out.println("-- Assignment before declaration → E6000 --");

        List<String> rejected = List.of(
            // the reviewer's exact repro: assignment statement before the let
            "export function test(): int { x = 5; let x: int = 1; return x; }",
            // same write inside a block
            """
            export function test(): int {
              let r: int = 0;
              { x = 5; }
              let x: int = 1;
              return x;
            }
            """,
            // same write inside an if body
            """
            export function test(): int {
              if (true) { x = 5; }
              let x: int = 1;
              return x;
            }
            """,
            // assignment in a return value position
            """
            export function test(): int {
              if (true) { return x = 5; }
              let x: int = 1;
              return x;
            }
            """,
            // assignment in a call-argument position
            """
            function f(y: int): int { return y; }
            export function test(): int {
              let r: int = f(x = 5);
              let x: int = 1;
              return x;
            }
            """);

        for (String source : rejected) {
            Frontend f = compileFrontend(source, "jvmtest-assignbefore.deal");
            if (!f.errors().isEmpty()) {
                fail("checker must accept the assignment-before-declaration "
                    + "probe (the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f.program(), f.checkResult(),
                    "jvmtest-assignbefore.deal", "main");
            check(res.hasErrors(), "backend rejects the assignment before "
                + "declaration");
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 for the assignment before declaration: "
                    + res.diagnostics());
        }

        // v1.2 grammar gate: the allowed v1.1 module-field write shapes
        // (a module-level let) were removed with module fields — E1049.
        Frontend fieldShadowShape = compileFrontend("""
            let x: int = 1;
            export function test(): int { x = 5; return x; }
            """, "jvmtest-assignfieldshadow.deal");
        check(fieldShadowShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-field shadow write rejected with E1049: "
                + fieldShadowShape.errors());

        Frontend moduleLaterShape = compileFrontend("""
            x = 5;
            let x: int = 1;
            export function test(): int { return x; }
            """, "jvmtest-assignmodulelater.deal");
        check(moduleLaterShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level later-field write rejected with E1049: "
                + moduleLaterShape.errors());
    }

    /**
     * Dead code after a statement that cannot complete normally must never
     * be emitted: LuaJIT never executes it and javac rejects it as
     * unreachable (JLS §14.21) — emitting it produced exactly the broken
     * artifact the round-4 reviewer found (`return 3;` after a complete
     * all-returning if/else, reported as success by the CLI). Completion
     * tracking: a return cannot complete normally; an if/else whose
     * branches all cannot complete normally cannot complete normally; a
     * block ending in such a statement cannot complete normally. Skipping
     * is semantics-preserving (dead code never runs under LuaJIT) and
     * keeps every artifact valid Java.
     */
    private static void testDeadCodeAfterNonCompletingStatements() throws Exception {
        System.out.println("-- Dead code after non-completing statements is skipped --");

        // The reviewer's exact repro: a dead return after an all-returning
        // if/else. javac must accept the artifact and test() must return 1.
        ExecResult repro = compileAndRunJvm(
            "export function test(): int { if (true) { return 1; } "
                + "else { return 2; } return 3; }",
            "deadcodeifelse");
        check(repro.exitCode() == 0, "dead code after complete if/else exits 0");
        check(repro.output().contains("1"),
            "only the live path runs: " + repro.output());

        // Dead return after return (function level).
        ExecResult afterReturn = compileAndRunJvm(
            "export function test(): int { return 1; return 2; }", "deadcodereturn");
        check(afterReturn.exitCode() == 0, "dead return after return exits 0");
        check(afterReturn.output().contains("1"),
            "first return wins: " + afterReturn.output());

        // Dead code at block level: a block ending in a return cannot fall
        // through, so the following return, dead let, and dead standalone
        // expression statement are all skipped.
        ExecResult block = compileAndRunJvm(
            "export function test(): int { { return 1; } return 2; "
                + "let x: int = 5; x + 1; return x; }",
            "deadcodeblock");
        check(block.exitCode() == 0, "block-level dead code exits 0");
        check(block.output().contains("1"),
            "block-ending return wins: " + block.output());

        // A dead else-if chain whose condition hoists a null-typed
        // side-effecting call (the round-4 stress shape) plus a dead
        // trailing return: valid Java, helper never called.
        ExecResult chain = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): int {
              if (true) { return 1; }
              else if (helper() === null) { return 2; }
              else { return 3; }
              return 4;
            }
            """, "deadcodechain");
        check(chain.exitCode() == 0, "dead else-if chain exits 0");
        check(chain.output().contains("1"), "live branch runs: " + chain.output());
        check(!chain.output().contains("helper-ran"),
            "the dead branch's hoisted call never runs: " + chain.output());

        // No over-skipping: an if WITHOUT else can complete normally, so
        // the statement after it is live and must still be emitted.
        ExecResult live = compileAndRunJvm(
            "export function test(): int { let x: boolean = false; "
                + "if (x) { return 1; } return 2; }",
            "deadcodenoskip");
        check(live.exitCode() == 0, "live code after open if exits 0");
        check(live.output().contains("2"),
            "statement after an open if is not skipped: " + live.output());

        // Emission assertions: dead statements must not appear in the
        // generated Java source at all.
        Frontend f = compileFrontend(
            "export function test(): int { return 1; return 2; }",
            "jvmtest-deadcode-emit.deal");
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f.program(), f.checkResult(),
                    "jvmtest-deadcode-emit.deal", "main");
            check(!res.hasErrors(), "dead-code program has no diagnostics");
            check(res.source().contains("return 1L;"),
                "the live return is emitted");
            check(!res.source().contains("return 2L;"),
                "the dead return is skipped: " + res.source());
        } else {
            fail("checker must accept the dead-code probe: " + f.errors());
        }

        Frontend f2 = compileFrontend(
            "export function test(): int { if (true) { return 1; } "
                + "else { return 2; } let x: int = 5; return x; }",
            "jvmtest-deadcode-emit2.deal");
        if (f2.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res =
                JvmBackend.generate(f2.program(), f2.checkResult(),
                    "jvmtest-deadcode-emit2.deal", "main");
            check(!res.hasErrors(), "dead-let program has no diagnostics");
            check(!res.source().contains("long x = 5L;"),
                "the dead let declaration is skipped: " + res.source());
        } else {
            fail("checker must accept the dead-let probe: " + f2.errors());
        }
    }

    private static void testRuntimeErrorCodes() throws Exception {
        System.out.println("-- Runtime error codes via javac + java --");

        ExecResult divZero = compileAndRunJvm(
            "export function test(): int { let x: int = 1 / 0; return x; }",
            "divzero");
        check(divZero.exitCode() == 1, "int division by zero exits 1");
        check(divZero.output().contains("DEAL_ERROR_CODE: E8005"),
            "E8005 reported: " + divZero.output());

        ExecResult overflow = compileAndRunJvm(
            "export function test(): int { return 9223372036854775807 + 1; }",
            "overflow");
        check(overflow.exitCode() == 1, "int overflow exits 1");
        check(overflow.output().contains("DEAL_ERROR_CODE: E8004"),
            "E8004 reported: " + overflow.output());

        ExecResult intConvert = compileAndRunJvm(
            "export function test(): int { return int(2.5); }",
            "intconvert");
        check(intConvert.exitCode() == 1, "int(2.5) exits 1");
        check(intConvert.output().contains("DEAL_ERROR_CODE: E8001"),
            "E8001 reported: " + intConvert.output());

        ExecResult negExp = compileAndRunJvm(
            "export function test(): int { return 2 ** -1; }",
            "negexp");
        check(negExp.exitCode() == 1, "negative int exponent exits 1");
        check(negExp.output().contains("DEAL_ERROR_CODE: E8006"),
            "E8006 reported for negative exponent: " + negExp.output());

        // Extreme power: Math.pow overflows to Infinity; LuaJIT's check_int
        // reports E8001 ("expected int, got infinity"), not E8004.
        ExecResult powInf = compileAndRunJvm(
            "export function test(): int { return 10 ** 400; }",
            "powinf");
        check(powInf.exitCode() == 1, "extreme power exits 1");
        check(powInf.output().contains("DEAL_ERROR_CODE: E8001"),
            "E8001 reported for infinite power (LuaJIT check_int alignment): "
                + powInf.output());

        ExecResult ok = compileAndRunJvm(
            "export function test(): int { return int(2.0) + 3; }",
            "ok");
        check(ok.exitCode() == 0, "valid program exits 0");
        check(ok.output().contains("5"), "valid program prints 5: " + ok.output());
    }

    /**
     * DEAL int safe range ±(2^53-1) = ±9007199254740991 (deal/runtime.lua
     * check_int; spec "int | checked ... [-(2^53-1), 2^53-1]"). Every
     * int-producing operation must enforce the bound with E8004 — the
     * helpers check only Java long bounds (±2^63) otherwise, silently
     * computing values LuaJIT rejects (`9007199254740991 + 1` must raise
     * E8004, not print 9007199254740992). Int literals outside the safe
     * range are checked at their point of use (LuaJIT silently rounds such
     * literals to doubles inside arithmetic — e.g. `9223372036854775807
     * % 2` computes 0 there — which the JVM backend refuses to reproduce:
     * it raises E8004 for the invalid int value instead of silently
     * diverging).
     */
    private static void testIntSafeRange() throws Exception {
        System.out.println("-- Int safe range ±(2^53-1) (javac + java) --");

        // The boundary itself is in range (check_int's comparison is
        // exclusive of values outside, inclusive of the boundary).
        ExecResult maxOk = compileAndRunJvm(
            "export function test(): int { return 9007199254740991; }",
            "intmaxok");
        check(maxOk.exitCode() == 0, "2^53-1 exits 0: " + maxOk.output());
        check(maxOk.output().contains("9007199254740991"),
            "2^53-1 prints the value: " + maxOk.output());

        ExecResult minOk = compileAndRunJvm(
            "export function test(): int { return -9007199254740991; }",
            "intminok");
        check(minOk.exitCode() == 0, "-(2^53-1) exits 0: " + minOk.output());
        check(minOk.output().contains("-9007199254740991"),
            "-(2^53-1) prints the value: " + minOk.output());

        ExecResult boundaryAdd = compileAndRunJvm(
            "export function test(): int { return 9007199254740990 + 1; }",
            "intboundaryadd");
        check(boundaryAdd.exitCode() == 0
                && boundaryAdd.output().contains("9007199254740991"),
            "in-range add stays in range: " + boundaryAdd.output());

        // v1.2 grammar gate: the module-level out-of-range literal shape
        // (a module-level let) was removed — E1049. The in-function
        // out-of-range boundary is pinned by the int-boundary tests above.
        Frontend modLitShape = compileFrontend("""
            let x: int = 9223372036854775807;
            export function test(): int { return 1; }
            """, "jvmtest-modintlit.deal");
        check(modLitShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level literal field rejected with E1049: " + modLitShape.errors());

        // intFromNumber boundary: int(9007199254740991.0) is in range.
        ExecResult convOk = compileAndRunJvm(
            "export function test(): int { return int(9007199254740991.0); }",
            "intconvok");
        check(convOk.exitCode() == 0
                && convOk.output().contains("9007199254740991"),
            "int(2^53-1) stays in range: " + convOk.output());

        // Every int-producing operation enforces the bound with E8004.
        String[][] overflowCases = {
            {"9007199254740991 + 1", "intadd"},
            {"9007199254740991 - (-1)", "intsub"},
            {"9007199254740991 * 2", "intmul"},
            {"-9007199254740991 - 1", "intsubneg"},
            {"-9007199254740992", "intneglit"},
            {"2 ** 53", "intpow53"},
            {"2 ** 62", "intpow62"},
            {"(-2) ** 63", "intpowneg63"},
            {"int(9007199254740992.0)", "intfromnum"},
            {"9223372036854775807", "intlit"},
            {"9223372036854775807 % 2", "intmodlit"},
            {"9223372036854775807 / 1", "intdivlit"},
        };
        for (String[] c : overflowCases) {
            ExecResult r = compileAndRunJvm(
                "export function test(): int { return " + c[0] + "; }", c[1]);
            check(r.exitCode() == 1, c[1] + " exits 1: " + r.output());
            check(r.output().contains("DEAL_ERROR_CODE: E8004"),
                c[1] + " reports E8004: " + r.output());
        }

        // Emission shape: helpers check their results through checkInt with
        // the safe-range bound, and out-of-range literals are wrapped at
        // their point of use.
        Frontend f = compileFrontend(
            "export function test(): int { return 9223372036854775807; }",
            "jvmtest-intrange.deal");
        check(f.errors().isEmpty(), "int-range frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-intrange.deal", "main");
            check(!res.hasErrors(), "int-range codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("return checkInt(9223372036854775807L);"),
                    "out-of-range literal wrapped in checkInt");
                check(java.contains("static long checkInt(long v)"),
                    "checkInt helper emitted");
                check(java.contains("9007199254740991L"),
                    "safe-range bound present");
                check(java.contains("checkInt(java.lang.Math.addExact(a, b), "
                        + "oFile, oLine, oCol)"),
                    "intAdd checks its result against the safe range");
                check(java.contains("p > 9007199254740991.0"),
                    "intPow enforces the safe range, not the long bound");
                check(java.contains("v > 9007199254740991.0"),
                    "intFromNumber enforces the safe range, not the long bound");
            }
        }
    }

    /**
     * Unqualified java.lang references in generated code (System.out,
     * Math.addExact, Double.isNaN, the String/Void type names, …) would
     * bind to a user's field or local named System/Math/Double/String/Void
     * instead of java.lang, producing an artifact javac rejects while the
     * CLI reports success. Every generated reference must be fully
     * qualified.
     */
    private static void testJavaLangNameCollisions() throws Exception {
        // Locals shadowing every java.lang name the generated code touches.
        ExecResult locals = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): int {
              let System: int = 1;
              let Math: int = 2;
              let Double: int = 3;
              let String: int = 4;
              let Void: int = 5;
              let Integer: int = 6;
              let Character: int = 7;
              let RuntimeException: int = 8;
              let ArithmeticException: int = 9;
              console.log("names-ok");
              return System + Math + Double + String + Void
                   + Integer + Character + RuntimeException + ArithmeticException;
            }
            """, "namelocals");
        check(locals.exitCode() == 0, "shadowing locals exit 0: " + locals.output());
        check(locals.output().contains("45"),
            "shadowing locals compute 45: " + locals.output());

        // v1.2 grammar gate: module-field java.lang-name collision shapes
        // (module-level lets) were removed with module fields — E1049.
        // The in-function collision surface is pinned by namelocals and
        // the local variants below.
        List<String> moduleFieldShapes = List.of(
            """
            let Math: int = 1;
            export function test(): int { return Math + 2; }
            """,
            """
            let Double: int = 1;
            export function test(): int { return Double + 1; }
            """,
            """
            import * as console from "std/console"
            let System: int = 1;
            console.log("sys-field-ok");
            export function test(): int { return System; }
            """,
            """
            let Integer: int = 0;
            let Character: int = 0;
            export function test(): boolean {
              return "a" < "b";
            }
            """,
            """
            let RuntimeException: int = 1;
            export function test(): int { return RuntimeException / 0; }
            """);
        for (String shape : moduleFieldShapes) {
            Frontend f = compileFrontend(shape, "jvmtest-name-field-shape.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "java.lang-name module-field shape rejected with E1049: "
                    + f.errors());
        }

        // Local Double + a 1e999 literal (renders as
        // Double.POSITIVE_INFINITY).
        ExecResult doubleLocal = compileAndRunJvm("""
            export function test(): number {
              let Double: int = 1;
              let n: number = 1e999;
              return n + number(Double);
            }
            """, "doublelocal");
        check(doubleLocal.exitCode() == 0
                && doubleLocal.output().contains("Infinity"),
            "local Double + 1e999 literal: " + doubleLocal.output());

        // Local Math + number ** (inline Math.pow emission).
        ExecResult mathPow = compileAndRunJvm("""
            export function test(): number {
              let Math: int = 0;
              return 2.0 ** 3.0;
            }
            """, "mathpow");
        check(mathPow.exitCode() == 0 && mathPow.output().contains("8.0"),
            "local Math + number **: " + mathPow.output());

        // String-typed parameter named String (the mapped type name).
        ExecResult stringParam = compileAndRunJvm("""
            function f(String: string): string { return String; }
            export function test(): string { return f("param-ok"); }
            """, "stringparam");
        check(stringParam.exitCode() == 0
                && stringParam.output().contains("param-ok"),
            "parameter named String: " + stringParam.output());

        // Null-typed local named Void (the mapped boxed-null type name).
        ExecResult voidLocal = compileAndRunJvm("""
            export function test(): int {
              let Void: null = null;
              return 1;
            }
            """, "voidlocal");
        check(voidLocal.exitCode() == 0 && voidLocal.output().contains("1"),
            "local named Void: " + voidLocal.output());

        // Emission shape: no unqualified java.lang references remain.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            export function test(): number {
              console.log("qualified");
              return 1e999;
            }
            """, "jvmtest-qualified.deal");
        check(f.errors().isEmpty(), "qualified-name frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-qualified.deal", "main");
            check(!res.hasErrors(), "qualified-name codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("java.lang.System.out.println"),
                    "console.log targets java.lang.System.out");
                check(java.contains("java.lang.Math.addExact"),
                    "helpers use java.lang.Math.addExact");
                check(java.contains("java.lang.Double.isNaN"),
                    "helpers use java.lang.Double.isNaN");
                check(java.contains("java.lang.Double.POSITIVE_INFINITY"),
                    "non-finite literals use java.lang.Double constants");
                check(java.contains("extends java.lang.RuntimeException"),
                    "DealError extends java.lang.RuntimeException");
            }
        }
    
    }

    /**
     * The use-before-declaration guard must walk every condition of an
     * if/else-if chain: emitIf/emitIfContinuation emit the follow-on
     * conditions directly (no per-statement guard runs for them), so a
     * later-declared variable in an else-if condition previously emitted
     * an illegal forward reference (module level) or a
     * cannot-find-symbol reference (function body) that javac rejected
     * after the CLI reported success.
     */
    private static void testElseIfChainUseBeforeDeclaration() throws Exception {
        System.out.println("-- Else-if chain conditions: use-before-declaration → E6000 --");

        // v1.2 grammar gate: a module-level chain is a frontend parse
        // error (E1049) — module-level statements were removed.
        Frontend moduleCase = compileFrontend("""
            if (true) { } else if (z === 2) { }
            let z: int = 2;
            export function test(): int { return 1; }
            """, "jvmtest-elseif-module.deal");
        check(moduleCase.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level else-if chain rejected with E1049: "
                + moduleCase.errors());

        // Function-body chain: `x` is declared after the chain.
        Frontend bodyCase = compileFrontend(
            "export function test(): int { if (true) {} else if (x === 2) {} "
                + "let x: int = 2; return 1; }",
            "jvmtest-elseif-body.deal");
        check(bodyCase.errors().isEmpty(),
            "function-body else-if chain frontend clean: " + bodyCase.errors());
        if (bodyCase.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                bodyCase.program(), bodyCase.checkResult(),
                "jvmtest-elseif-body.deal", "main");
            check(res.hasErrors(),
                "function-body else-if forward reference rejected");
            check(res.diagnostics().stream()
                    .anyMatch(d -> d.message().contains("'x'")),
                "function-body diagnostic names x: " + res.diagnostics());
        }

        // Deep chain: the guard must walk past several else-if links to the
        // offending condition.
        Frontend deepCase = compileFrontend(
            "export function test(): int { let a: int = 1; "
                + "if (a === 0) {} else if (a === 1) {} else if (b === 2) {} "
                + "let b: int = 2; return 1; }",
            "jvmtest-elseif-deep.deal");
        check(deepCase.errors().isEmpty(),
            "deep else-if chain frontend clean: " + deepCase.errors());
        if (deepCase.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                deepCase.program(), deepCase.checkResult(),
                "jvmtest-elseif-deep.deal", "main");
            check(res.hasErrors(), "deep-chain forward reference rejected");
            check(res.diagnostics().stream()
                    .anyMatch(d -> d.message().contains("'b'")),
                "deep-chain diagnostic names b: " + res.diagnostics());
        }

        // Positive: chain conditions reading already-declared variables
        // stay clean and run (function body).
        ExecResult ok = compileAndRunJvm("""
            export function test(): int {
              let x: int = 2;
              if (x === 1) { return 0; } else if (x === 2) { return 7; }
              return 3;
            }
            """, "elseifok");
        check(ok.exitCode() == 0 && ok.output().contains("7"),
            "clean else-if chain runs: " + ok.output());

        // v1.2 grammar gate: the module-level positive chain shape was
        // removed with module-level statements (E1049); the function-body
        // positive chain above covers the semantics.
        Frontend modOkShape = compileFrontend("""
            let z: int = 2;
            let hit: boolean = false;
            if (z === 1) { } else if (z === 2) { hit = true; }
            export function test(): int { if (hit) { return 1; } return 0; }
            """, "jvmtest-elseifmodok.deal");
        check(modOkShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level positive chain rejected with E1049: "
                + modOkShape.errors());
    }

    /**
     * Number literals that overflow to Infinity (checker-accepted: the
     * parser stores Double.parseDouble("1e999") with no range check) must
     * render as the Double constants — a bare {@code Infinity} identifier
     * makes javac reject an artifact the CLI reported as successful. The
     * Lua backend emits {@code (1/0)} for the same literal.
     */
    private static void testNonFiniteNumberLiterals() throws Exception {
        System.out.println("-- Non-finite number literals (javac + java) --");

        ExecResult inf = compileAndRunJvm(
            "export function test(): number { let x: number = 1e999; return x; }",
            "inflit");
        check(inf.exitCode() == 0, "1e999 exits 0");
        check(inf.output().contains("Infinity"),
            "1e999 prints Infinity: " + inf.output());

        ExecResult negInf = compileAndRunJvm(
            "export function test(): number { let x: number = -1e999; return x; }",
            "neginflit");
        check(negInf.exitCode() == 0, "-1e999 exits 0");
        check(negInf.output().contains("-Infinity"),
            "-1e999 prints -Infinity: " + negInf.output());

        // Infinity compares equal to itself, like LuaJIT's (1/0) == (1/0).
        ExecResult eq = compileAndRunJvm(
            "export function test(): boolean { return 1e999 === 1e999; }",
            "infeq");
        check(eq.exitCode() == 0, "1e999 === 1e999 exits 0");
        check(eq.output().contains("true"),
            "1e999 === 1e999 is true: " + eq.output());

        // int(1e999) reports E8001, matching LuaJIT's check_int on infinity.
        ExecResult conv = compileAndRunJvm(
            "export function test(): int { return int(1e999); }",
            "infconv");
        check(conv.exitCode() == 1, "int(1e999) exits 1");
        check(conv.output().contains("DEAL_ERROR_CODE: E8001"),
            "int(1e999) reports E8001: " + conv.output());

        // Emission: the Double constant, never a bare Infinity identifier.
        Frontend f = compileFrontend(
            "export function test(): number { let x: number = 1e999; return x; }",
            "jvmtest-inflit.deal");
        check(f.errors().isEmpty(), "non-finite literal frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-inflit.deal", "main");
            check(!res.hasErrors(), "non-finite literal codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("= java.lang.Double.POSITIVE_INFINITY;"),
                    "1e999 renders as java.lang.Double.POSITIVE_INFINITY");
                check(!res.source().matches("(?s).*= Infinity;.*"),
                    "no bare Infinity identifier is emitted");
            }
        }
    }

    /**
     * {@code &&}/{@code ||} short-circuit: a null-typed side-effecting call
     * in a non-leading operand must NOT run when the left operand already
     * decides the result (LuaJIT's {@code and}/{@code or} semantics). The
     * hoisted pre-statements are guarded by the left operand, never flushed
     * unconditionally.
     */
    private static void testShortCircuitPreservation() throws Exception {
        System.out.println("-- && / || short-circuit preservation (javac + java) --");

        ExecResult andSkip = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean { return false && helper() === null; }
            """, "scandskip");
        check(andSkip.exitCode() == 0, "false && ... exits 0");
        check(andSkip.output().contains("false"),
            "false && ... computes false: " + andSkip.output());
        check(!andSkip.output().contains("helper-ran"),
            "right operand of false && is NOT evaluated: " + andSkip.output());

        ExecResult orSkip = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean { return true || helper() === null; }
            """, "scorskip");
        check(orSkip.exitCode() == 0, "true || ... exits 0");
        check(orSkip.output().contains("true"),
            "true || ... computes true: " + orSkip.output());
        check(!orSkip.output().contains("helper-ran"),
            "right operand of true || is NOT evaluated: " + orSkip.output());

        ExecResult andRuns = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean { return true && helper() === null; }
            """, "scandruns");
        check(andRuns.exitCode() == 0, "true && ... exits 0");
        check(andRuns.output().contains("helper-ran"),
            "right operand of true && IS evaluated: " + andRuns.output());
        check(andRuns.output().contains("true"),
            "true && (null === null) computes true: " + andRuns.output());

        ExecResult orRuns = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean { return false || helper() === null; }
            """, "scorruns");
        check(orRuns.exitCode() == 0, "false || ... exits 0");
        check(orRuns.output().contains("helper-ran"),
            "right operand of false || IS evaluated: " + orRuns.output());
        check(orRuns.output().contains("true"),
            "false || (null === null) computes true: " + orRuns.output());

        // Initializer position: the reviewer's `let b: boolean = ...` shape.
        ExecResult initSkip = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): int {
              let b: boolean = false && helper() === null;
              if (b) { console.log("b-true"); return 1; }
              console.log("b-false");
              return 0;
            }
            """, "scinitskip");
        check(initSkip.exitCode() == 0, "guarded initializer exits 0");
        check(initSkip.output().contains("b-false"),
            "initializer computes false: " + initSkip.output());
        check(!initSkip.output().contains("helper-ran"),
            "guarded initializer skips the call: " + initSkip.output());

        // Nested short-circuit: the inner guard nests inside the outer one.
        ExecResult nested = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean {
              return false && (true || helper() === null);
            }
            """, "scnested");
        check(nested.exitCode() == 0, "nested short-circuit exits 0");
        check(!nested.output().contains("helper-ran"),
            "nested guarded operand is NOT evaluated: " + nested.output());
        check(nested.output().contains("false"),
            "nested short-circuit computes false: " + nested.output());

        ExecResult nestedRuns = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean {
              return true && (false || helper() === null);
            }
            """, "scnestedruns");
        check(nestedRuns.exitCode() == 0, "nested short-circuit (runs) exits 0");
        check(nestedRuns.output().contains("helper-ran"),
            "nested reachable operand IS evaluated: " + nestedRuns.output());

        // Left-operand hoists stay unconditional; right-operand hoists are
        // guarded — evaluation order preserved.
        ExecResult both = compileAndRunJvm("""
            import * as console from "std/console"
            function first(): null { console.log("first-ran"); }
            function helper(): null { console.log("helper-ran"); }
            export function test(): boolean {
              return first() === null && helper() === null;
            }
            """, "scboth");
        check(both.exitCode() == 0, "left+right hoists exit 0");
        check(both.output().contains("first-ran"),
            "left-operand call runs: " + both.output());
        check(both.output().contains("helper-ran"),
            "guarded right-operand call runs (left was true): " + both.output());
        check(both.output().indexOf("first-ran")
                < both.output().indexOf("helper-ran"),
            "evaluation order preserved: " + both.output());

        // v1.2 grammar gate: module-level guarded field initializers were
        // removed with module-level lets (E1049); the guarded-operand
        // semantics run in-function in the shapes above.
        Frontend modSkipShape = compileFrontend("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            let b: boolean = false && helper() === null;
            export function test(): null { console.log("test-ran"); }
            """, "jvmtest-scmodskip.deal");
        check(modSkipShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level guarded initializer rejected with E1049: "
                + modSkipShape.errors());

        ExecResult modRuns = compileAndRunJvm("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): null {
              let b: boolean = true && helper() === null;
              console.log("test-ran");
            }
            """, "scmodruns");
        check(modRuns.exitCode() == 0, "guarded initializer (runs) exits 0");
        check(modRuns.output().contains("helper-ran"),
            "reachable guarded operand IS evaluated: " + modRuns.output());

        // Emission assertions: no lambdas; the guarded lowering runs
        // in-function (the module-level field variant is an E1049 gate
        // above — module fields were removed in v1.2).
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function helper(): null { console.log("helper-ran"); }
            export function test(): null {
              let b: boolean = false && helper() === null;
              console.log("test-ran");
            }
            """, "jvmtest-sc.deal");
        check(f.errors().isEmpty(), "short-circuit probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-sc.deal", "main");
            check(!res.hasErrors(), "short-circuit probe codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(!res.source().contains(" -> "),
                    "short-circuit lowering emits no lambda");
                check(res.source().contains("boolean b = __sc0;"),
                    "guarded initializer assigns the temporary in-function");
            }
        }
    }

    /** String ordering follows Unicode scalar values (LuaJIT's UTF-8
     * bytewise order), not UTF-16 code-unit order — supplementary
     * characters order after the whole BMP, exactly as under LuaJIT. */
    /**
     * DEAL/LuaJIT evaluate expressions strictly left to right and stop at
     * the first runtime error; a null-typed side-effecting call in a value
     * position is hoisted into a pre-statement flushed before the
     * containing statement, which used to make an EARLIER inline
     * side-effecting operand of the same statement run after it
     * ({@code f(g(), console.log("x"))} printed "x" before g() ran).
     * {@code emitOperandsInOrder} materializes such operands into
     * temporaries in evaluation order; this test pins the observable
     * order in every combination position via javac+java subprocesses.
     */
    private static void testEvaluationOrderPreservation() throws Exception {
        System.out.println("-- Evaluation-order preservation (javac + java) --");

        // The reviewer's exact repro: call-argument position, return.
        ExecResult ret = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): int { return f(g(), console.log("x")); }
            """, "evalorder-return");
        check(ret.exitCode() == 0, "call-args eval order exits 0");
        check(ret.output().indexOf("g-ran") >= 0
                && ret.output().indexOf("g-ran") < ret.output().indexOf("x"),
            "g() runs before the hoisted console.log (left to right): "
                + ret.output());

        // The same shape in a let-initializer position.
        ExecResult init = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): int {
              let r: int = f(g(), console.log("x"));
              return r;
            }
            """, "evalorder-init");
        check(init.exitCode() == 0, "initializer eval order exits 0");
        check(init.output().indexOf("g-ran") >= 0
                && init.output().indexOf("g-ran") < init.output().indexOf("x"),
            "initializer position: g() before console.log: " + init.output());

        // Standalone call-statement position.
        ExecResult stmt = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): null {
              f(g(), console.log("x"));
            }
            """, "evalorder-stmt");
        check(stmt.exitCode() == 0, "call-statement eval order exits 0");
        check(stmt.output().indexOf("g-ran") >= 0
                && stmt.output().indexOf("g-ran") < stmt.output().indexOf("x"),
            "call-statement position: g() before console.log: " + stmt.output());

        // If-condition position.
        ExecResult cond = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): null {
              if (f(g(), console.log("x")) === 7) { console.log("cond-ok"); }
            }
            """, "evalorder-cond");
        check(cond.exitCode() == 0, "if-condition eval order exits 0");
        check(cond.output().indexOf("g-ran") >= 0
                && cond.output().indexOf("g-ran") < cond.output().indexOf("x"),
            "if-condition position: g() before console.log: " + cond.output());

        // v1.2 grammar gate: the module-level field-initializer position
        // was removed with module-level lets (E1049); the in-function
        // initializer position above keeps the evaluation-order pin.
        Frontend fieldInitShape = compileFrontend("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            let a: int = f(g(), console.log("x"));
            export function test(): int { return a; }
            """, "jvmtest-evalorder-fieldinit.deal");
        check(fieldInitShape.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "field-initializer position rejected with E1049: "
                + fieldInitShape.errors());

        // Non-leading && operand: the short-circuit guard keeps the order.
        ExecResult sc = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): boolean {
              return true && f(g(), console.log("x")) === 7;
            }
            """, "evalorder-sc");
        check(sc.exitCode() == 0, "short-circuit operand eval order exits 0");
        check(sc.output().indexOf("g-ran") >= 0
                && sc.output().indexOf("g-ran") < sc.output().indexOf("x"),
            "guarded && operand: g() before console.log: " + sc.output());

        // Reverse shape: hoisted operand first, inline call after — the
        // hoisted statement legitimately precedes the later inline call.
        ExecResult reverse = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(x: null, y: int): int { return y; }
            export function test(): int { return f(console.log("x"), g()); }
            """, "evalorder-reverse");
        check(reverse.exitCode() == 0, "reverse shape exits 0");
        check(reverse.output().indexOf("x") >= 0
                && reverse.output().indexOf("x") < reverse.output().indexOf("g-ran"),
            "reverse shape: hoisted console.log before later g(): " + reverse.output());

        // Three mixed operands: hoisted, inline, hoisted.
        ExecResult mixed = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function h(v: null, w: int, u: null): int { return w; }
            export function test(): int {
              return h(console.log("a"), g(), console.log("b"));
            }
            """, "evalorder-mixed");
        check(mixed.exitCode() == 0, "mixed three-operand shape exits 0");
        check(mixed.output().indexOf("a") >= 0
                && mixed.output().indexOf("a") < mixed.output().indexOf("g-ran")
                && mixed.output().indexOf("g-ran") < mixed.output().indexOf("b"),
            "a, then g(), then b (left to right): " + mixed.output());

        // Nested combination: the first operand itself hoists (k's
        // null-typed argument) AND still carries an inline call (k(…))
        // after its own hoisted statement; that inline call must run
        // before the second operand's hoisted print. LuaJIT order:
        // g-ran, y, k-ran, x.
        ExecResult nested = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 1; }
            function k(x: null): int { console.log("k-ran"); return 2; }
            function f(y: int, x: null): int { return y; }
            export function test(): int {
              return f(g() + k(console.log("y")), console.log("x"));
            }
            """, "evalorder-nested");
        check(nested.exitCode() == 0, "nested combination exits 0");
        check(nested.output().indexOf("g-ran") >= 0
                && nested.output().indexOf("g-ran") < nested.output().indexOf("y")
                && nested.output().indexOf("y") < nested.output().indexOf("k-ran")
                && nested.output().indexOf("k-ran") < nested.output().indexOf("x"),
            "g-ran, y, k-ran, x (left to right through the nested "
                + "combination): " + nested.output());

        // Binary operands, both directions.
        ExecResult bin = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 3; }
            function f(x: null): int { return 4; }
            export function test(): int { return g() + f(console.log("x")); }
            """, "evalorder-bin");
        check(bin.exitCode() == 0, "binary operands exit 0");
        check(bin.output().indexOf("g-ran") >= 0
                && bin.output().indexOf("g-ran") < bin.output().indexOf("x"),
            "left binary operand g() runs before the hoisted call: " + bin.output());

        ExecResult binRev = compileAndRunJvm("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 3; }
            function f(x: null): int { return 4; }
            export function test(): int { return f(console.log("x")) + g(); }
            """, "evalorder-binrev");
        check(binRev.exitCode() == 0, "reversed binary operands exit 0");
        check(binRev.output().indexOf("x") >= 0
                && binRev.output().indexOf("x") < binRev.output().indexOf("g-ran"),
            "left hoisted operand precedes the later g(): " + binRev.output());

        // An earlier operand that RAISES must raise before the hoisted
        // call runs (LuaJIT stops at the first runtime error): a ** 400
        // raises E8004 and the console.log must never print.
        ExecResult raising = compileAndRunJvm("""
            import * as console from "std/console"
            function f(y: int, x: null): int { return y; }
            export function test(): int {
              let a: int = 2;
              return f(a ** 400, console.log("x"));
            }
            """, "evalorder-raise");
        check(raising.exitCode() != 0, "raising operand exits non-zero");
        check(!raising.output().contains("x"),
            "the hoisted console.log never runs when the earlier operand "
                + "raises: " + raising.output());
        check(raising.output().contains("E8004"),
            "the raising operand reports E8004: " + raising.output());

        // Emission shape: the earlier inline call is materialized into a
        // temporary BEFORE the hoisted statement, and no lambda is emitted.
        Frontend f = compileFrontend("""
            import * as console from "std/console"
            function g(): int { console.log("g-ran"); return 7; }
            function f(y: int, x: null): int { return y; }
            export function test(): int { return f(g(), console.log("x")); }
            """, "jvmtest-evalorder-emit.deal");
        check(f.errors().isEmpty(), "eval-order probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-evalorder-emit.deal", "main");
            check(!res.hasErrors(), "eval-order source emits without diagnostics");
            if (!res.hasErrors()) {
                String src = res.source();
                int tempIdx = src.indexOf("__t0 = g();");
                int logIdx = src.indexOf("java.lang.System.out.println(\"x\");");
                check(tempIdx >= 0 && logIdx >= 0 && tempIdx < logIdx,
                    "the earlier inline call is materialized before the "
                        + "hoisted println: " + src);
                check(!src.contains(" -> "), "no lambda is emitted");
            }
        }
    }

    private static void testStringScalarOrdering() throws Exception {
        System.out.println("-- String scalar-value ordering (javac + java) --");

        ExecResult sup = compileAndRunJvm(
            "export function test(): int { if (\"\uD83D\uDE00\" < \"\uE000\") { return 1; } return 0; }",
            "suporder");
        check(sup.exitCode() == 0, "supplementary ordering exits 0");
        check(sup.output().contains("0"),
            "U+1F600 < U+E000 is false in scalar order (UTF-16 says true): "
                + sup.output());

        ExecResult supReverse = compileAndRunJvm(
            "export function test(): int { if (\"\uE000\" < \"\uD83D\uDE00\") { return 1; } return 0; }",
            "suporder2");
        check(supReverse.exitCode() == 0, "reverse supplementary ordering exits 0");
        check(supReverse.output().contains("1"),
            "U+E000 < U+1F600 is true in scalar order: " + supReverse.output());

        ExecResult supEq = compileAndRunJvm(
            "export function test(): int { if (\"\uD83D\uDE00\" === \"\uD83D\uDE00\") { return 1; } return 0; }",
            "supeq");
        check(supEq.exitCode() == 0, "supplementary equality exits 0");
        check(supEq.output().contains("1"),
            "supplementary equality is exact: " + supEq.output());

        ExecResult ascii = compileAndRunJvm(
            "export function test(): int { if (\"a\" < \"b\") { return 1; } return 0; }",
            "asciiorder");
        check(ascii.exitCode() == 0, "ASCII ordering exits 0");
        check(ascii.output().contains("1"),
            "ASCII ordering still works: " + ascii.output());

        Frontend f = compileFrontend(
            "export function test(): boolean { return \"\uD83D\uDE00\" < \"\uE000\"; }",
            "jvmtest-sup.deal");
        check(f.errors().isEmpty(), "scalar-ordering probe frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-sup.deal", "main");
            check(!res.hasErrors(), "scalar-ordering probe codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains("scalarCompare("),
                    "string ordering goes through scalarCompare");
                check(!res.source().contains(".compareTo("),
                    "no UTF-16 compareTo for DEAL string ordering");
            }
        }
    }

    /** Module-level calls to functions whose bodies (transitively) read a
     * module field declared later than the call site are rejected with
     * E6000: LuaJIT fails at load with a nil read while Java would silently
     * read the field's default value. */
    private static void testModuleLevelCallReadingLaterField() throws Exception {
        // v1.2 grammar gate: every module-level call shape reading a later
        // module field (module-level lets removed) is a frontend parse
        // error (E1049) — the E6000 load-time analysis surface was removed
        // with the module-level statement grammar.
        List<String> rejected = List.of(
            """
            import * as console from "std/console"
            function f(): int { return x; }
            f();
            let x: int = 5;
            export function test(): null { console.log("test-ran"); }
            """,
            """
            import * as console from "std/console"
            f();
            let x: int = 5;
            function f(): int { return x; }
            export function test(): null { console.log("test-ran"); }
            """,
            """
            function f(): int { return g(); }
            function g(): int { return x; }
            f();
            let x: int = 5;
            export function test(): int { return 1; }
            """,
            """
            function f(): int { return x; }
            let y: int = f();
            let x: int = 5;
            export function test(): int { return y; }
            """,
            """
            function f(): int { return x; }
            if (f() === 1) { }
            let x: int = 5;
            export function test(): int { return 1; }
            """,
            """
            let x: int = f();
            function f(): int { return x; }
            export function test(): int { return x; }
            """);

        for (String source : rejected) {
            Frontend f = compileFrontend(source, "jvmtest-modcall.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "module-level call shape rejected with E1049: " + f.errors());
        }

        // Positive in-function shape: a block-local shadow of an outer
        // local is not an outer read.
        ExecResult shadow = compileAndRunJvm("""
            import * as console from "std/console"
            export function test(): int {
              let x: int = 5;
              { let x: int = 9; }
              return x;
            }
            """, "modcallshadow");
        check(shadow.exitCode() == 0, "local-shadow call exits 0");
        check(shadow.output().contains("5"),
            "block-local shadow does not overwrite the outer local: "
                + shadow.output());
    
    }

    /**
     * LuaJIT assigns each function value at its declaration point in source
     * order, so a module-level call that reaches a function declared at or
     * after the call site fails at load with a nil read — directly
     * (`f(); function f…`), transitively (`function f(): null { g(); } f();
     * function g…`: the callee is declared before the call but its body
     * reaches a later function), or from a field initializer (`let a: int =
     * f()` before `function f`). Java hoists methods and would silently run
     * them; the backend must reject these with E6000 instead. Calls whose
     * callee and transitive callees are all declared before the call site
     * stay allowed (LuaJIT parity, verified with real luajit runs).
     */
    private static void testModuleLevelCallBeforeFunctionDeclarationRejected()
            throws Exception {
        // v1.2 grammar gate: every module-level call shape (module-level
        // executable statements removed) is a frontend parse error
        // (E1049) — the E6000 call-before-declaration surface was removed
        // with the module-level statement grammar.
        List<String> rejected = List.of(
            """
            import * as console from "std/console"
            f();
            function f(): null { console.log("f-ran"); }
            export function test(): int { return 1; }
            """,
            """
            import * as console from "std/console"
            let a: int = f();
            console.log("mid");
            let b: int = g();
            function f(): int { console.log("f-ran"); return 1; }
            function g(): int { console.log("g-ran"); return 2; }
            export function test(): int { return a + b; }
            """,
            """
            import * as console from "std/console"
            function f(): null { g(); }
            f();
            function g(): null { console.log("g-ran"); }
            export function test(): int { return 1; }
            """,
            """
            import * as console from "std/console"
            function f(): null { h(); }
            function h(): null { g(); }
            f();
            function g(): null { console.log("g-ran"); }
            export function test(): int { return 1; }
            """,
            """
            let a: int = f();
            function f(): int { return 1; }
            export function test(): int { return a; }
            """,
            """
            import * as console from "std/console"
            test2();
            export function test2(): null { console.log("later"); }
            export function test(): int { return 1; }
            """);

        for (String source : rejected) {
            Frontend f = compileFrontend(source, "jvmtest-modfndecl.deal");
            check(f.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
                "module-level call shape rejected with E1049: " + f.errors());
        }

        // The positive function-declaration hoisting that the module-level
        // shapes exercised survives: forward calls from a function body to
        // a later-declared module function run normally.
        ExecResult direct = compileAndRunJvm("""
            import * as console from "std/console"
            function f(): int { console.log("f-ran"); return 1; }
            export function test(): int { return f(); }
            """, "modfnorderok");
        check(direct.exitCode() == 0, "post-declaration call exits 0");
        check(direct.output().contains("f-ran"),
            "in-function call ran: " + direct.output());

        ExecResult transitive = compileAndRunJvm("""
            function f(): int { return g(); }
            function g(): int { return 7; }
            export function test(): int { return f(); }
            """, "modfntransok");
        check(transitive.exitCode() == 0, "transitive call exits 0");
        check(transitive.output().contains("7"),
            "transitive call computes 7: " + transitive.output());
    
    }

    /** The DEAL_ERROR_CODE contract must hold for module-level errors
     * whether or not the module has a zero-arity export: with one, the
     * first auto-invocation triggers class initialization and the error
     * arrives as an ExceptionInInitializerError (a LinkageError, not a
     * RuntimeException) that the runner unwraps. */
    private static void testRunnerModuleErrorCodeWithExport() throws Exception {
        // v1.2 grammar gate: module-level error shapes (module-level
        // lets removed) are frontend parse errors (E1049) — there is no
        // module-load-time executable surface left to raise. The runtime
        // error codes themselves are pinned by the in-function boundary
        // tests (E8005 int division by zero etc.).
        Frontend withExport = compileFrontend("""
            export function test(): int { return 1; }
            let x: int = 1 / 0;
            """, "jvmtest-moderrwithexport.deal");
        check(withExport.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level error shape rejected with E1049: "
                + withExport.errors());

        Frontend noExport = compileFrontend("""
            let x: int = 1 / 0;
            export function takesArg(y: int): int { return y; }
            """, "jvmtest-moderrnoexport.deal");
        check(noExport.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level error without export rejected with E1049: "
                + noExport.errors());
    
    }

    /**
     * ISSUE-0374 profile plumb pins: the default generate overloads keep
     * their signatures and derive the backend-wide LEGACY int mode; the
     * explicit-profile overload derives the int32 mode from a real
     * {@code DEAL_V1_2_INT32} profile; and the orchestrator's
     * {@code codegenAllJvm} plumb carries
     * {@code invocation.semanticProfile()} into {@link JvmBackend#generate}
     * under both the default ({@code PRE_ACTIVATION → LEGACY_SAFE_INT})
     * and an explicit {@code V1_2_ACTIVE} invocation. Every mode
     * assertion reads the real stored backend state recorded on each
     * generated result — never a mirrored constant or a mocked profile.
     * ISSUE-0375 landed the carrier/range switch on top of the plumb, so
     * the profile variants now emit their own carrier surfaces: the
     * legacy arm stays byte-identical to the pre-tree base while the
     * int32 arm emits the signed32 carriers.
     */
    private static void testProfilePlumbIntMode() throws Exception {
        System.out.println("-- Profile plumb: backend-wide int mode derivation --");

        String source = "export function main(): null { return null; }\n"
            + "export function run(): int { return 41 + 1; }\n";
        Frontend f = compileFrontend(source, "jvmtest-profile-plumb.deal");
        check(f.errors().isEmpty(), "plumb fixture frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;

        // Default overload: legacy mode by construction, signature
        // unchanged.
        JvmBackend.JvmCodegenResult legacyDefault = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-profile-plumb.deal",
            "main");
        check(!legacyDefault.int32Mode(),
            "default generate overload derives the LEGACY int mode");
        check(!legacyDefault.hasErrors(),
            "default overload codegen clean: " + legacyDefault.diagnostics());

        // The same default emission through the new full profile entry:
        // an explicit LEGACY_SAFE_INT profile derives the legacy mode and
        // an identical artifact (the plumb adds no emission branch).
        JvmBackend.JvmCodegenResult legacyFull = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-profile-plumb.deal",
            "main", Map.of(), Map.of(), Map.of(), false, true,
            SemanticProfile.LEGACY_SAFE_INT);
        check(!legacyFull.int32Mode(),
            "explicit LEGACY_SAFE_INT profile derives the LEGACY mode");
        check(legacyDefault.source().equals(legacyFull.source()),
            "default overload and the profile entry emit byte-identical "
                + "artifacts under LEGACY_SAFE_INT");

        // The plumbed generate entry with a real DEAL_V1_2_INT32 profile:
        // the backend derives and stores the int32 mode.
        JvmBackend.JvmCodegenResult int32 = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-profile-plumb.deal",
            "main", Map.of(), Map.of(), Map.of(), false,
            SemanticProfile.DEAL_V1_2_INT32);
        check(int32.int32Mode(),
            "explicit DEAL_V1_2_INT32 profile derives the int32 mode");

        // The derivation boundary through the same plumbed entry: an
        // explicit LEGACY_SAFE_INT profile derives the legacy mode and an
        // identical artifact (no int32 emission exists yet).
        JvmBackend.JvmCodegenResult legacyExplicit = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-profile-plumb.deal",
            "main", Map.of(), Map.of(), Map.of(), false,
            SemanticProfile.LEGACY_SAFE_INT);
        check(!legacyExplicit.int32Mode(),
            "explicit LEGACY_SAFE_INT profile derives the LEGACY mode");
        check(!legacyExplicit.source().equals(int32.source()),
            "the plumbed int32 entry now emits the DEAL_V1_2_INT32 "
                + "carrier surface (ISSUE-0375 switch)");
        check(int32.source().contains(
                "static int checkInt(long v, java.lang.String oFile, "
                    + "int oLine, int oCol) "
                    + "{ if (v > 2147483647L"),
            "int32 artifact carries the signed32 checkInt gate (the "
                + "origin-threading overload)");
        check(int32.source().contains("static int intAdd(int a, int b)"),
            "int32 artifact carries the primitive int carriers");
        check(!legacyExplicit.source().contains("static int intAdd(int a, int b)"),
            "explicit LEGACY_SAFE_INT keeps the legacy long carriers");

        // The real plumb path: the orchestrator's codegenAllJvm passes
        // invocation.semanticProfile() into JvmBackend.generate, and the
        // recorded per-module result carries the real stored backend
        // mode.
        writeFile("src/plumb_main.deal", source);
        Path entryFile = tmpDir.get().resolve("src/plumb_main.deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/plumb");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilerInvocation int32Invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
        check(int32Invocation.semanticProfile()
                == SemanticProfile.DEAL_V1_2_INT32,
            "V1_2_ACTIVE invocation resolves DEAL_V1_2_INT32");
        check(int32Invocation.releaseState() == ReleaseState.V1_2_ACTIVE,
            "explicit invocation records V1_2_ACTIVE");

        CompilationOrchestrator int32Orchestrator =
            new CompilationOrchestrator(
                entryFile, outputRoot, false, false, false, false,
                Backend.JVM, null, roots,
                Path.of(".").toAbsolutePath().normalize(), null,
                int32Invocation);
        boolean int32Ok = int32Orchestrator.compile();
        check(int32Ok, "int32-profile orchestrator compile succeeds: "
            + int32Orchestrator.diagnostics());
        if (int32Ok) {
            JvmBackend.JvmCodegenResult plumbed =
                int32Orchestrator.jvmGeneratedResults()
                    .get(entryFile.toString());
            check(plumbed != null && plumbed.int32Mode(),
                "codegenAllJvm plumbed invocation.semanticProfile() into "
                    + "JvmBackend.generate: the recorded result carries "
                    + "the real stored int32 mode");
        }

        // ISSUE-0643 P4/P10 + ISSUE-0654: the default orchestrator
        // invocation is the release-owned production invocation — it runs
        // the production arm (no route plan, no per-module backend
        // results). The dual-shape fixture (an exported function called
        // from source) is realized by that arm: the source call runs the
        // exported function's recorded EXTERNAL_ENTRY through the closed
        // CALL(EXTERNAL) SHARED_BODY cell, so exactly one project artifact
        // stages; the harness invocation of the same fixture keeps the
        // int32-plumb evidence through the retained per-module backend.
        writeFile("src/plumb_dual.deal",
            "export function run(): int { return 41 + 1; }\n"
                + "export function main(): null { run() return null; }\n");
        Path dualEntryFile = tmpDir.get().resolve("src/plumb_dual.deal")
            .toAbsolutePath().normalize();
        CompilationOrchestrator defaultOrchestrator =
            new CompilationOrchestrator(
                dualEntryFile, outputRoot, false, false, false, Backend.JVM,
                null, roots, Path.of(".").toAbsolutePath().normalize());
        boolean defaultOk = defaultOrchestrator.compile();
        check(defaultOk,
            "the release-owned production invocation compiles the dual-shape "
                + "fixture: " + defaultOrchestrator.diagnostics());
        check(defaultOrchestrator.invocation().semanticProfile()
                == SemanticProfile.DEAL_V1_2_INT32,
            "the orchestrator default invocation derives DEAL_V1_2_INT32 "
                + "under the committed V1_2_ACTIVE release state");
        check(defaultOrchestrator.routePlan() == null
                && defaultOrchestrator.jvmGeneratedResults().isEmpty(),
            "the production arm consults no route plan and populates no "
                + "per-module backend results");
        check(defaultOk
                && defaultOrchestrator.semanticEmissionCount() == 1
                && defaultOrchestrator.retainedEmissionCount() == 0,
            "the dual-shape fixture emits exactly one project artifact and "
                + "zero retained artifacts: semantic="
                + defaultOrchestrator.semanticEmissionCount() + " retained="
                + defaultOrchestrator.retainedEmissionCount());
        Path dualClass = outputRoot.resolve(
            JvmBackend.classNameFor(dualEntryFile.getFileName().toString()
                .replace(".deal", "")) + ".java");
        check(Files.exists(dualClass),
            "the dual-shape production compile stages its project class at "
                + dualClass);
        CompilationOrchestrator defaultHarness = new CompilationOrchestrator(
            dualEntryFile, outputRoot, false, false, false, false, Backend.JVM,
            null, roots, Path.of(".").toAbsolutePath().normalize(), null,
            harnessInvocation());
        boolean defaultHarnessOk = defaultHarness.compile();
        check(defaultHarnessOk, "the harness invocation of the dual-shape "
            + "fixture compiles: " + defaultHarness.diagnostics());
        if (defaultHarnessOk) {
            JvmBackend.JvmCodegenResult plumbed =
                defaultHarness.jvmGeneratedResults()
                    .get(dualEntryFile.toString());
            check(plumbed != null && plumbed.int32Mode(),
                "the harness invocation plumbs the DEAL_V1_2_INT32 mode into "
                    + "the retained backend");
        }

        CompilationOrchestrator legacyOrchestrator =
            new CompilationOrchestrator(
                entryFile, outputRoot, false, false, false, false, Backend.JVM,
                null, roots, Path.of(".").toAbsolutePath().normalize(), null,
                CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                    CapabilityRegistry.releaseRegistry()));
        boolean legacyOk = legacyOrchestrator.compile();
        check(legacyOk, "explicit legacy orchestrator compile succeeds: "
            + legacyOrchestrator.diagnostics());
        check(legacyOrchestrator.invocation().semanticProfile()
                == SemanticProfile.LEGACY_SAFE_INT,
            "the explicit PRE_ACTIVATION invocation keeps LEGACY_SAFE_INT "
                + "(the internal matrix row)");
        if (legacyOk) {
            JvmBackend.JvmCodegenResult plumbed =
                legacyOrchestrator.jvmGeneratedResults()
                    .get(entryFile.toString());
            check(plumbed != null && !plumbed.int32Mode(),
                "the explicit legacy invocation plumbs the LEGACY int mode "
                    + "into the backend");
        }
        if (int32Ok && legacyOk) {
            String int32Source = int32Orchestrator.jvmGeneratedResults()
                .get(entryFile.toString()).source();
            String legacySource = legacyOrchestrator.jvmGeneratedResults()
                .get(entryFile.toString()).source();
            check(!int32Source.equals(legacySource),
                "orchestrator artifacts carry their profile's carrier "
                    + "surface (the int32 switch is profile-gated)");
            check(int32Source.contains("static int intAdd(int a, int b)")
                    && !legacySource.contains("static int intAdd(int a, int b)"),
                "orchestrator plumb selects the backend int mode: int32 "
                    + "carriers under V1_2_ACTIVE (the default), legacy "
                    + "carriers under the explicit PRE_ACTIVATION invocation");
        }
    }


    private static final String LEGACY_BASE_INT_HELPERS = String.join("\n",
        "// DEAL int safe range: \u00b1(2^53-1), mirroring deal/runtime.lua's",
        "    // check_int (v < -9007199254740991 or v > 9007199254740991 raises",
        "    // E8004). Every int-producing operation checks its result, exactly",
        "    // like LuaJIT's int_add = check_int(a + b) family.",
        "    static long checkInt(long v) { return checkInt(v, null, -1, -1); }",
        "    static long checkInt(long v, java.lang.String oFile, int oLine, int oCol) { if (v > 9007199254740991L || v < -9007199254740991L) throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); return v; }",
        "    // int arithmetic: E8004 out of safe range, E8005 division by zero, E8006 negative exponent.",
        "    static long intAdd(long a, long b) { return intAdd(a, b, null, -1, -1); }",
        "    static long intAdd(long a, long b, java.lang.String oFile, int oLine, int oCol) { try { return checkInt(java.lang.Math.addExact(a, b), oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    static long intSub(long a, long b) { return intSub(a, b, null, -1, -1); }",
        "    static long intSub(long a, long b, java.lang.String oFile, int oLine, int oCol) { try { return checkInt(java.lang.Math.subtractExact(a, b), oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    static long intMul(long a, long b) { return intMul(a, b, null, -1, -1); }",
        "    static long intMul(long a, long b, java.lang.String oFile, int oLine, int oCol) { try { return checkInt(java.lang.Math.multiplyExact(a, b), oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    static long intDiv(long a, long b) { return intDiv(a, b, null, -1, -1); }",
        "    static long intDiv(long a, long b, java.lang.String oFile, int oLine, int oCol) { if (b == 0L) throw new DealError(\"E8005\", \"integer division by zero\", oFile, oLine, oCol); try { return checkInt(a / b, oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    static long intMod(long a, long b) { return intMod(a, b, null, -1, -1); }",
        "    static long intMod(long a, long b, java.lang.String oFile, int oLine, int oCol) { if (b == 0L) throw new DealError(\"E8005\", \"integer division by zero\", oFile, oLine, oCol); try { return checkInt(a % b, oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    static long intPow(long a, long b) { return intPow(a, b, null, -1, -1); }",
        "    static long intPow(long a, long b, java.lang.String oFile, int oLine, int oCol) { if (b < 0L) throw new DealError(\"E8006\", \"integer exponent must be non-negative\", oFile, oLine, oCol); double p = java.lang.Math.pow((double) a, (double) b); if (java.lang.Double.isNaN(p)) throw new DealError(\"E8001\", \"expected int, got NaN\", oFile, oLine, oCol, \"int\", \"NaN\", null, null); if (java.lang.Double.isInfinite(p)) throw new DealError(\"E8001\", \"expected int, got infinity\", oFile, oLine, oCol, \"int\", \"infinity\", null, null); if (p > 9007199254740991.0 || p < -9007199254740991.0) throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); return (long) p; }",
        "    static long intNeg(long a) { return intNeg(a, null, -1, -1); }",
        "    static long intNeg(long a, java.lang.String oFile, int oLine, int oCol) { try { return checkInt(java.lang.Math.negateExact(a), oFile, oLine, oCol); } catch (java.lang.ArithmeticException e) { throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); } }",
        "    // number %: Lua-style floored modulo (a - floor(a/b)*b), unlike Java's truncated %.",
        "    static double numMod(double a, double b) { return a - java.lang.Math.floor(a / b) * b; }",
        "    // int(v) / number(v) conversion intrinsics (E8001 bad value, E8004 out of range).",
        "    static long intFromNumber(double v) { return intFromNumber(v, null, -1, -1); }",
        "    static long intFromNumber(double v, java.lang.String oFile, int oLine, int oCol) { if (java.lang.Double.isNaN(v)) throw new DealError(\"E8001\", \"expected int, got NaN\", oFile, oLine, oCol, \"int\", \"NaN\", null, null); if (java.lang.Double.isInfinite(v)) throw new DealError(\"E8001\", \"expected int, got infinity\", oFile, oLine, oCol, \"int\", \"infinity\", null, null); if (v != java.lang.Math.floor(v)) throw new DealError(\"E8001\", \"expected int, got non-integer number\", oFile, oLine, oCol, \"int\", \"number\", null, null); if (v > 9007199254740991.0 || v < -9007199254740991.0) throw new DealError(\"E8004\", \"int out of range\", oFile, oLine, oCol); return (long) v; }",
        "    static double numberFromInt(long v) { return (double) v; }");

    /** The pre-tree base emission of {@code emitStdlibTimeMemberCall} —
     * the retained {@code ()->int} time expression
     * ({@code (java.lang.System.currentTimeMillis() / 1000L) * 1000L};
     * jvm-int32-gate-activation-tree D4): the expression text must
     * appear in every emitted artifact byte-for-byte — no time
     * algorithm added or changed, no new code path introduced. The
     * ISSUE-0377 time pin compares the artifact's emitted expression
     * against this constant by equality. */
    private static final String RETAINED_TIME_EXPRESSION =
        "(java.lang.System.currentTimeMillis() / 1000L) * 1000L";

    // =========================================================================
    // ISSUE-0375 profile-gated carrier/range switch
    // =========================================================================

    /** Compiles and runs one real program through the full pipeline
     * (orchestrator → JvmBackend → javac → java) under the explicit
     * {@code DEAL_V1_2_INT32} invocation — the plumbed profile, never a
     * mirrored constant. The emitted artifact's recorded int32 mode is
     * asserted before execution, so a broken profile plumb (T1) fails
     * here even when the legacy program would not raise. */
    private static ExecResult runInt32Project(String source, String name)
            throws Exception {
        writeFile("src/i32_" + name + ".deal", source);
        Path entryFile = tmpDir.get().resolve("src/i32_" + name + ".deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/i32_" + name);
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilerInvocation invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, null, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean ok = orchestrator.compile();
        check(ok, "int32 orchestrator compile succeeds for " + name + ": "
            + orchestrator.diagnostics());
        if (!ok) return new ExecResult("", 1);
        JvmBackend.JvmCodegenResult res =
            orchestrator.jvmGeneratedResults().get(entryFile.toString());
        check(res != null && res.int32Mode(),
            "codegenAllJvm recorded the real stored int32 mode for " + name);
        if (res == null || !res.int32Mode()) return new ExecResult("", 1);
        Frontend f = compileFrontend(source, "i32_" + name + ".deal");
        Files.writeString(outputRoot.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(f.program(),
                res.className()));
        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(outputRoot)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                  .sorted()
                  .forEach(p -> javaFiles.add(p.getFileName().toString()));
        }
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(outputRoot,
            javaFiles, javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed for " + name + ": "
                + javacErr);
        }
        ProcessBuilder java = new ProcessBuilder("java", "-cp",
            outputRoot.toString(), "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        return new ExecResult(out, exit);
    }

    /** The same full-pipeline run under the explicit legacy invocation
     * ({@code PUBLIC_BUILD + PRE_ACTIVATION → LEGACY_SAFE_INT}, the
     * pre-activation matrix row that stays available as an internal
     * derivation after E12's flip) — the integration counterpart that
     * proves the retained legacy profile produces legacy artifacts where
     * the int32 edges do not raise. The default invocation is now the
     * committed V1_2_ACTIVE public build, so legacy negative controls
     * pass the legacy invocation explicitly. */
    private static ExecResult runLegacyProject(String source, String name)
            throws Exception {
        writeFile("src/legacy_" + name + ".deal", source);
        Path entryFile = tmpDir.get().resolve("src/legacy_" + name + ".deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/legacy_" + name);
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, null, roots,
            Path.of(".").toAbsolutePath().normalize(), null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
        boolean ok = orchestrator.compile();
        check(ok, "legacy orchestrator compile succeeds for " + name + ": "
            + orchestrator.diagnostics());
        if (!ok) return new ExecResult("", 1);
        JvmBackend.JvmCodegenResult res =
            orchestrator.jvmGeneratedResults().get(entryFile.toString());
        check(res != null && !res.int32Mode(),
            "the explicit legacy invocation plumbs the LEGACY int mode for " + name);
        if (res == null || res.int32Mode()) return new ExecResult("", 1);
        Frontend f = compileFrontend(source, "legacy_" + name + ".deal");
        Files.writeString(outputRoot.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(f.program(),
                res.className()));
        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(outputRoot)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                  .sorted()
                  .forEach(p -> javaFiles.add(p.getFileName().toString()));
        }
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(outputRoot,
            javaFiles, javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed for " + name + ": "
                + javacErr);
        }
        ProcessBuilder java = new ProcessBuilder("java", "-cp",
            outputRoot.toString(), "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        return new ExecResult(out, exit);
    }

    /** Writes the shared host-module project files for the int32
     * in-range boundary programs: deal.json (externals host/log), the
     * declaration bindings, the int32-mapped HostLog implementation
     * ({@code int}/{@code Integer} carriers — the dynamic value the host
     * seam range-checks), and the DEAL entry source. */
    private static void writeHostLogProject(String source, String name)
            throws IOException {
        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "externals": {
                "host/log": { "declaration": "bindings/log.d.deal" }
              }
            }
            """);
        writeFile("bindings/log.d.deal", """
            export function add(a: int, b: int): int;
            export async function fetchInt(): int;
            export function maybe(): int | null;
            """);
        writeFile("HostLog.java", """
            import java.util.concurrent.CompletableFuture;
            public final class HostLog {
                public static Object add(int a, int b) { return Integer.valueOf(a + b); }
                public static Object fetchInt() { return CompletableFuture.completedFuture(Integer.valueOf(7)); }
                public static Object maybe() { return null; }
            }
            """);
        writeFile("src/host_" + name + ".deal", source);
    }

    /** Full-pipeline run of one host-module program under the explicit
     * {@code DEAL_V1_2_INT32} invocation (orchestrator with the
     * externals-listed host module → JvmBackend → javac over the
     * artifacts + the real HostLog class + the runner → java). The host
     * class declares the int32-mapped signatures — the real boxed value
     * producer for the in-range boundary programs. */
    private static ExecResult runInt32HostProject(String source,
                                                  String name)
            throws Exception {
        writeHostLogProject(source, name);
        Path entryFile = tmpDir.get().resolve("src/host_" + name + ".deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/host_" + name);
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        Map<String, String> externals = Map.of("host/log",
            tmpDir.get().resolve("bindings/log.d.deal").toString());
        check(Files.exists(tmpDir.get().resolve("bindings/log.d.deal")),
            "deal.json with externals loads for " + name);
        CompilerInvocation invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, externals, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean ok = orchestrator.compile();
        check(ok, "int32 host orchestrator compile succeeds for " + name
            + ": " + orchestrator.diagnostics());
        if (!ok) return new ExecResult("", 1);
        JvmBackend.JvmCodegenResult res =
            orchestrator.jvmGeneratedResults().get(entryFile.toString());
        check(res != null && res.int32Mode(),
            "codegenAllJvm recorded the real stored int32 mode for " + name);
        if (res == null || !res.int32Mode()) return new ExecResult("", 1);
        Files.copy(tmpDir.get().resolve("HostLog.java"),
            outputRoot.resolve("HostLog.java"));
        Files.writeString(outputRoot.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(parseProgram("""
                export function main(): null { return null; }
                export function test(): int { return 0; }
                """), res.className()));
        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(outputRoot)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                  .sorted()
                  .forEach(p -> javaFiles.add(p.getFileName().toString()));
        }
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(outputRoot,
            javaFiles, javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed for " + name + ": "
                + javacErr);
        }
        ProcessBuilder java = new ProcessBuilder("java", "-cp",
            outputRoot.toString(), "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        return new ExecResult(out, exit);
    }

    /** The emitted entry artifact of one host-module program under the
     * explicit {@code DEAL_V1_2_INT32} invocation (the plumbed
     * orchestrator path). */
    private static String int32HostArtifact(String source, String name)
            throws IOException {
        writeHostLogProject(source, name);
        Path entryFile = tmpDir.get().resolve("src/host_" + name + ".deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/host_" + name);
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        Map<String, String> externals = Map.of("host/log",
            tmpDir.get().resolve("bindings/log.d.deal").toString());
        check(Files.exists(tmpDir.get().resolve("bindings/log.d.deal")),
            "deal.json with externals loads for " + name);
        CompilerInvocation invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, externals, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean ok = orchestrator.compile();
        check(ok, "int32 host artifact compile succeeds for " + name + ": "
            + orchestrator.diagnostics());
        if (!ok) return "";
        JvmBackend.JvmCodegenResult res =
            orchestrator.jvmGeneratedResults().get(entryFile.toString());
        check(res != null && res.int32Mode(),
            "codegenAllJvm recorded the real stored int32 mode for " + name);
        if (res == null || !res.int32Mode()) return "";
        return Files.readString(outputRoot.resolve(res.className() + ".java"));
    }


    /** The emitted artifact of {@code source} under the explicit
     * {@code DEAL_V1_2_INT32} profile (the plumbed generate entry, entry
     * module surface). */
    private static String int32Artifact(String source, String name) {
        Frontend f = compileFrontend(source, "jvmtest-" + name + ".deal");
        check(f.errors().isEmpty(), name + " frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return "";
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-" + name + ".deal",
            "main", Map.of(), Map.of(), Map.of(), true,
            SemanticProfile.DEAL_V1_2_INT32);
        check(res.int32Mode() && !res.hasErrors(),
            name + " int32 artifact clean: " + res.diagnostics());
        return res.source();
    }

    /** The emitted artifact of {@code source} under the default
     * {@code LEGACY_SAFE_INT} profile. */
    private static String legacyArtifact(String source, String name) {
        Frontend f = compileFrontend(source, "jvmtest-" + name + ".deal");
        check(f.errors().isEmpty(), name + " frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return "";
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-" + name + ".deal",
            "main");
        check(!res.int32Mode() && !res.hasErrors(),
            name + " legacy artifact clean: " + res.diagnostics());
        return res.source();
    }

    /** Counts non-overlapping occurrences of {@code needle} in
     * {@code haystack} (the exact-once raise pins). */
    private static int countOccurrences(String haystack,
                                        String needle) {
        return haystack.split(
            java.util.regex.Pattern.quote(needle), -1).length - 1;
    }

    /** The emitted origin argument list of one raise site (ISSUE-0604
     * D1): a Java string literal (the DEAL source file) followed by the
     * 1-based start line and start column, or the explicit absent
     * sentinel. */
    private static final java.util.regex.Pattern RAISE_ORIGIN_SUFFIX =
        java.util.regex.Pattern.compile(
            " \"[^\"]*\", -?\\d+, \\d+\\)");

    /**
     * True when {@code haystack} contains {@code callPrefix} (which must
     * end just before the origin argument list's leading space)
     * immediately followed by a compile-time origin argument list — the
     * ISSUE-0604 threading shape at every int arithmetic/conversion/
     * stdlib-int raise site.
     */
    private static boolean hasOriginCall(String haystack,
            String callPrefix) {
        for (int idx = haystack.indexOf(callPrefix); idx >= 0;
                idx = haystack.indexOf(callPrefix, idx + 1)) {
            java.util.regex.Matcher m =
                RAISE_ORIGIN_SUFFIX.matcher(haystack);
            m.region(idx + callPrefix.length(), haystack.length());
            if (m.lookingAt()) return true;
        }
        return false;
    }

    /**
     * The 1-based column of {@code needle} in the {@code lineNumber}-th
     * line (1-based) of {@code source} — the expected origin coordinate
     * of a raise site whose authoritative node starts at that text.
     */
    private static int columnOf(String source, int lineNumber,
            String needle) {
        String[] lines = source.split("\n", -1);
        return lines[lineNumber - 1].indexOf(needle) + 1;
    }

    /**
     * The emission seam's field surface and the closed D11 message
     * table (ISSUE-0603 leaf 1; jvm-canonical-error-snapshot-convergence
     * D2/D11), re-derived against the on-disk sidecars: the generated
     * artifact carries the complete DEALRuntimeError field surface and
     * the origin/message-threading helper signatures, and the closed
     * per-site message literals are visible at the pinned raise sites —
     * the intAdd declared-int binding-initializer addition and the
     * return/operand positions both raise “int out of safe range” (the
     * int32-overflow-source and int-add-overflow pins), the checkInt
     * absInt gate raises “int out of safe range” (the
     * stdlib/math/int-abs-min-overflow pin) while the declared-int time
     * boundary keeps the same text and never fabricates a span, and the
     * intFromNumber E8004 arm splits by profile: “int out of safe
     * range” under signed-int32 (int-conversion-out-of-range) versus
     * “int out of range” under legacy-safe-int
     * (runtime/int-convert-range). The runs observe the messages
     * through the real javac/java pipeline (anti-hollow).
     */
    private static void testEmissionSeamFieldSurfaceAndMessageSplit()
            throws Exception {
        System.out.println("-- Emission seam: DealError field surface + "
            + "the closed D11 message table --");

        String source = """
            export function main(): null { return null; }
            export function test(): int {
              let max: int = 2147483647;
              let one: int = 1;
              let sum: int = max + one;
              return sum;
            }
            """;
        String java = int32Artifact(source, "emission_seam_field_surface");
        check(java.contains("final java.lang.String code;")
                && java.contains("final java.lang.String file;")
                && java.contains("final int line;")
                && java.contains("final int column;")
                && java.contains("final java.lang.String expected;")
                && java.contains("final java.lang.String actual;")
                && java.contains("final java.lang.Integer frames;")
                && java.contains("final java.lang.String cause;"),
            "the emitted DealError carries the complete DEALRuntimeError "
                + "field surface");
        check(java.contains("DealError(java.lang.String code, "
                + "java.lang.String message, java.lang.String oFile, "
                + "int oLine, int oCol, java.lang.String expected, "
                + "java.lang.String actual, java.lang.Integer frames, "
                + "java.lang.String cause)"),
            "the DealError full constructor threads the origin and the "
                + "closed optional fields");
        check(java.contains("DealError(java.lang.String code, "
                + "java.lang.String message, java.lang.String oFile, "
                + "int oLine, int oCol)"),
            "the DealError origin constructor threads the span group");
        check(java.contains("this(code, message, null, -1, -1, null, null, "
                + "null, null);"),
            "the two-argument constructor is the explicit absent-origin "
                + "path (file=null, line=-1, column=-1)");

        // The intAdd binding-initializer addition carries the
        // authoritative operator expression's origin (ISSUE-0604 D3:
        // the int32-overflow-source 9:18 convention — the expression
        // start) and raises the pinned "int out of safe range" text.
        check(hasOriginCall(java, "intAdd(max, one,"),
            "the declared-int binding-initializer addition emits the "
                + "origin-threading site: "
                + java.lines().filter(l -> l.contains("intAdd("))
                    .findFirst().orElse("<missing>"));
        ExecResult initRun = runInt32Project(source, "emission_seam_init");
        check(initRun.exitCode() == 1 && initRun.output().contains(
                "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "the binding-initializer addition raises the pinned E8004 "
                + "message: " + initRun.output());

        String retSource = """
            export function main(): null { return null; }
            export function test(): int { return 2147483647 + 1; }
            """;
        String retJava = int32Artifact(retSource, "emission_seam_return");
        check(hasOriginCall(retJava, "return intAdd(2147483647, 1,"),
            "the return-position addition carries the operator "
                + "expression's origin (int-add-overflow 7:10): "
                + retJava.lines().filter(l -> l.contains("intAdd("))
                    .findFirst().orElse("<missing>"));
        ExecResult retRun = runInt32Project(retSource, "emission_seam_ret");
        check(retRun.exitCode() == 1 && retRun.output().contains(
                "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "the return-position addition raises the pinned E8004 "
                + "message: " + retRun.output());

        // The origin-threading helper overloads and the closed literals
        // under the signed-int32 profile.
        check(java.contains("static int intSub(int a, int b, "
                + "java.lang.String oFile, int oLine, int oCol)")
                && java.contains("throw new DealError(\"E8004\", "
                    + "\"int out of safe range\", oFile, oLine, oCol)"),
            "intSub threads the origin and raises \"int out of safe "
                + "range\"");
        check(java.contains("static int intMul(int a, int b, "
                + "java.lang.String oFile, int oLine, int oCol)"),
            "intMul threads the origin");
        check(java.contains("static int intNeg(int a, "
                + "java.lang.String oFile, int oLine, int oCol)"),
            "intNeg threads the origin");
        check(java.contains("static int intFromNumber(double v, "
                + "java.lang.String oFile, int oLine, int oCol)"),
            "intFromNumber threads the origin");
        check(java.contains("static int intPow(int a, int b, "
                + "java.lang.String oFile, int oLine, int oCol)")
                && java.contains("if (p > 2147483647.0 || p < "
                    + "-2147483648.0) throw new DealError(\"E8004\", "
                    + "\"int out of safe range\""),
            "intPow threads the origin and keeps \"int out of safe "
                + "range\"");
        check(java.contains("static int checkInt(long v, "
                + "java.lang.String oFile, int oLine, int oCol)"),
            "checkInt threads the origin");
        check(java.contains("if (v > 2147483647.0 || v < "
                + "-2147483648.0) throw new DealError(\"E8004\", "
                + "\"int out of safe range\""),
            "the signed-int32 intFromNumber E8004 arm pins \"int out of "
                + "safe range\" (int-conversion-out-of-range)");

        // The absInt result gate raises its pinned literal; the time
        // boundary keeps the same closed "int out of safe range" text
        // (pinned by testInt32TimeBoundary) and never fabricates a span.
        String absSource = """
            import * as math from "std/math";
            export function main(): null { return null; }
            export function test(): int { return math.absInt(-2147483648); }
            """;
        String absJava = int32Artifact(absSource, "emission_seam_absint");
        check(hasOriginCall(absJava,
                "checkInt(java.lang.Math.abs((long) -2147483648),"),
            "the absInt result gate routes through the origin-threading "
                + "checkInt entry (int-abs-min-overflow 9:10): "
                + absJava.lines().filter(l -> l.contains("absInt("))
                    .findFirst().orElse("<missing>"));
        ExecResult absRun = runInt32Project(absSource,
            "emission_seam_abs_run");
        check(absRun.exitCode() == 1 && absRun.output().contains(
                "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "the absInt result gate raises the pinned E8004 message: "
                + absRun.output());

        // The int32 E8004 conversion arm and the legacy regression
        // profile (the surviving E8004 split): signed-int32 pins "int
        // out of safe range", legacy-safe-int ~"int out of range~".
        ExecResult int32IntFrom = runInt32Project("""
            export function main(): null { return null; }
            export function test(): int { return int(2147483648.0); }
            """, "emission_seam_int32_intfrom");
        check(int32IntFrom.exitCode() == 1
                && int32IntFrom.output().contains(
                    "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "the signed-int32 intFromNumber arm raises the pinned E8004 "
                + "message: " + int32IntFrom.output());
        ExecResult legacyIntFrom = compileAndRunJvm("""
            export function test(): int { return int(9007199254740992.0); }
            """, "emission-seam-legacy-intfrom");
        check(legacyIntFrom.exitCode() == 1
                && legacyIntFrom.output().contains(
                    "DEAL_ERROR_CODE: E8004 int out of range"),
            "the legacy intFromNumber arm raises the pinned E8004 "
                + "message: " + legacyIntFrom.output());
    }

    /** The first emitted line containing {@code needle} (the failure
     * messages of the origin pins). */
    private static String emittedLine(String java, String needle) {
        return java.lines().filter(l -> l.contains(needle)).findFirst()
            .orElse("<missing>");
    }

    /**
     * ISSUE-0604 (jvm-canonical-error-snapshot-convergence D3/D4/D11):
     * every int arithmetic/conversion/stdlib-int raise site carries the
     * authoritative node's origin — the operator or intrinsic-call
     * expression start — as compile-time literals, and the closed
     * expected/actual projection at the arms whose sidecars pin the
     * pair. The origins are asserted against the fixture sources'
     * coordinates (computed from the source text, never guessed), the
     * message/projection literals at every route, and the sanctioned
     * time-boundary raise stays span-less (the one-argument
     * absent-origin {@code checkInt} entry).
     */
    private static void testArithmeticRaiseSiteOrigins() throws Exception {
        System.out.println("-- Arithmetic/conversion/stdlib-int raise-site "
            + "origins --");

        // 1. The int operators. D3: the authoritative node is the
        // operator expression start (its left end): int-add-overflow
        // 7:10, int32-overflow-source 9:18, int-sub-overflow/
        // int-mul-overflow/int32-pow-overflow 7:10, int-neg-min-source
        // 8:22.
        String opsSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n"
            + "  let a: int = 1;\n"
            + "  let b: int = 2;\n"
            + "  let c: int = a + b;\n"
            + "  let d: int = a - b;\n"
            + "  let e: int = a * b;\n"
            + "  let f: int = a / b;\n"
            + "  let g: int = a % b;\n"
            + "  let h: int = a ** b;\n"
            + "  let i: int = -a;\n"
            + "  return c + d + e + f + g + h + i;\n"
            + "}\n";
        String opsPath = "jvmtest-arith_origins.deal";
        String opsJava = int32Artifact(opsSource, "arith_origins");
        check(opsJava.contains("intAdd(a, b, \"" + opsPath + "\", 5, "
                + columnOf(opsSource, 5, "a + b") + ")"),
            "the binding-initializer intAdd carries the operator "
                + "expression's origin: "
                + emittedLine(opsJava, "intAdd(a, b,"));
        check(opsJava.contains("intSub(a, b, \"" + opsPath + "\", 6, "
                + columnOf(opsSource, 6, "a - b") + ")"),
            "intSub carries the operator expression's origin: "
                + emittedLine(opsJava, "intSub(a, b,"));
        check(opsJava.contains("intMul(a, b, \"" + opsPath + "\", 7, "
                + columnOf(opsSource, 7, "a * b") + ")"),
            "intMul carries the operator expression's origin: "
                + emittedLine(opsJava, "intMul(a, b,"));
        check(opsJava.contains("intDiv(a, b, \"" + opsPath + "\", 8, "
                + columnOf(opsSource, 8, "a / b") + ")"),
            "intDiv carries the operator expression's origin: "
                + emittedLine(opsJava, "intDiv(a, b,"));
        check(opsJava.contains("intMod(a, b, \"" + opsPath + "\", 9, "
                + columnOf(opsSource, 9, "a % b") + ")"),
            "intMod carries the operator expression's origin: "
                + emittedLine(opsJava, "intMod(a, b,"));
        check(opsJava.contains("intPow(a, b, \"" + opsPath + "\", 10, "
                + columnOf(opsSource, 10, "a ** b") + ")"),
            "intPow carries the operator expression's origin: "
                + emittedLine(opsJava, "intPow(a, b,"));
        check(opsJava.contains("intNeg(a, \"" + opsPath + "\", 11, "
                + columnOf(opsSource, 11, "-a") + ")"),
            "the unary int negation carries the unary expression's "
                + "origin: " + emittedLine(opsJava, "intNeg(a,"));

        // The closed per-branch messages of the same helpers: the
        // division family is E8005 and the negative exponent E8006
        // (int-div-zero/int-div-zero-e8005/rtc-035-remainder-zero-error
        // 7:10, error-inside-for-of/loop-error-source 9:27/8:27,
        // int-pow-negative 7:10), and intPow's NaN/infinity arms are
        // E8001 with the pinned expected/actual pair
        // (int32-pow-infinity 7:10: "int"/"infinity").
        check(opsJava.contains("throw new DealError(\"E8005\", "
                + "\"integer division by zero\", oFile, oLine, oCol)"),
            "intDiv/intMod raise E8005 'integer division by zero'");
        check(opsJava.contains("throw new DealError(\"E8006\", "
                + "\"integer exponent must be non-negative\", oFile, "
                + "oLine, oCol)"),
            "intPow raises E8006 'integer exponent must be non-negative'");
        check(opsJava.contains("throw new DealError(\"E8001\", "
                + "\"expected int, got NaN\", oFile, oLine, oCol, "
                + "\"int\", \"NaN\", null, null)"),
            "intPow's NaN arm raises the pinned expected/actual pair");
        check(opsJava.contains("throw new DealError(\"E8001\", "
                + "\"expected int, got infinity\", oFile, oLine, oCol, "
                + "\"int\", \"infinity\", null, null)"),
            "intPow's infinity arm raises the pinned expected/actual "
                + "pair");
        check(opsJava.contains("if (p > 2147483647.0 || p < "
                + "-2147483648.0) throw new DealError(\"E8004\", "
                + "\"int out of safe range\", oFile, oLine, oCol)"),
            "intPow's E8004 arm keeps the pinned \"int out of safe "
                + "range\" text with no optional pair (int32-pow-overflow)");

        // 2. The conversion intrinsics: the origin is the
        // intrinsic-call expression start (int-convert-fraction 7:10,
        // int-convert-infinity/-nan 9:10, int-conversion-out-of-range
        // 7:10, runtime/int-convert-* 7:10/8:10,
        // runtime/number-convert-null 8:10).
        String convSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n"
            + "  let n: number = 1.5;\n"
            + "  let m: int | null = 3;\n"
            + "  let x: number | null = 1.0;\n"
            + "  let a: int = int(n);\n"
            + "  let b: int = int(m);\n"
            + "  let c: number = number(x);\n"
            + "  return a + b;\n"
            + "}\n";
        String convPath = "jvmtest-arith_conv_origins.deal";
        String convJava = int32Artifact(convSource, "arith_conv_origins");
        check(convJava.contains("intFromNumber(n, \"" + convPath
                + "\", 6, " + columnOf(convSource, 6, "int(n)") + ")"),
            "the int(number) intrinsic carries the call expression's "
                + "origin: " + emittedLine(convJava, "intFromNumber(n,"));
        check(convJava.contains("intFromNullable(m, \"" + convPath
                + "\", 7, " + columnOf(convSource, 7, "int(m)") + ")"),
            "the int(int | null) intrinsic carries the call expression's "
                + "origin: " + emittedLine(convJava, "intFromNullable(m,"));
        check(convJava.contains("numberFromNullable(x, \"" + convPath
                + "\", 8, " + columnOf(convSource, 8, "number(x)") + ")"),
            "the number(number | null) intrinsic carries the call "
                + "expression's origin: "
                + emittedLine(convJava, "numberFromNullable(x,"));
        check(convJava.contains("throw new DealError(\"E8001\", "
                + "\"expected int, got NaN\", oFile, oLine, oCol, "
                + "\"int\", \"NaN\", null, null)")
                && convJava.contains("throw new DealError(\"E8001\", "
                    + "\"expected int, got infinity\", oFile, oLine, "
                    + "oCol, \"int\", \"infinity\", null, null)")
                && convJava.contains("throw new DealError(\"E8001\", "
                    + "\"expected int, got non-integer number\", "
                    + "oFile, oLine, oCol, \"int\", \"number\", null, "
                    + "null)"),
            "intFromNumber's NaN/infinity/non-integer arms raise the "
                + "pinned expected/actual pairs (int-convert-nan/-infinity/"
                + "fraction, runtime/int-convert-noninteger)");
        check(convJava.contains("if (v > 2147483647.0 || v < "
                + "-2147483648.0) throw new DealError(\"E8004\", "
                + "\"int out of safe range\", oFile, oLine, oCol)"),
            "the signed-int32 intFromNumber E8004 arm pins \"int out of "
                + "safe range\" (int-conversion-out-of-range)");
        check(convJava.contains("throw new DealError(\"E8001\", "
                + "\"cannot convert null to int\", oFile, oLine, oCol, "
                + "\"int\", \"null\", null, null)"),
            "the int(null) arm raises the pinned expected/actual pair "
                + "(runtime/int-convert-null)");
        check(convJava.contains("throw new DealError(\"E8001\", "
                + "\"cannot convert null to number\", oFile, oLine, "
                + "oCol, \"number\", \"null\", null, null)"),
            "the number(null) arm raises the pinned expected/actual pair "
                + "(runtime/number-convert-null)");

        // 3. The legacy-safe-int profile's surviving E8004 split: the
        // intFromNumber arm keeps "int out of range"
        // (runtime/int-convert-range) with the same closed E8001 pairs.
        String legacyConvJava = legacyArtifact(convSource,
            "arith_conv_origins_legacy");
        check(legacyConvJava.contains("if (v > 9007199254740991.0 || "
                + "v < -9007199254740991.0) throw new DealError(\"E8004\", "
                + "\"int out of range\", oFile, oLine, oCol)"),
            "the legacy intFromNumber E8004 arm keeps \"int out of "
                + "range\" (runtime/int-convert-range)");
        check(hasOriginCall(legacyConvJava, "intFromNumber(n,"),
            "the legacy conversion site carries the origin literals");

        // 4. The std/math absInt result gate: the intrinsic-call
        // expression's origin (int-abs-min-overflow 9:10) with the
        // pinned "int out of safe range" literal.
        String absSource = "import * as math from \"std/math\";\n"
            + "export function main(): null { return null; }\n"
            + "export function test(): int { return math.absInt(-2147483648); }\n";
        String absPath = "jvmtest-arith_abs_origin.deal";
        String absJava = int32Artifact(absSource, "arith_abs_origin");
        check(absJava.contains("return checkInt(java.lang.Math.abs((long) "
                + "-2147483648), \"" + absPath + "\", 3, "
                + columnOf(absSource, 3, "math.absInt(") + ")"),
            "the absInt result gate carries the intrinsic-call "
                + "expression's origin: "
                + emittedLine(absJava, "java.lang.Math.abs((long)"));

        // 5. The sanctioned span-less raise (D5): the locked time
        // selector's declared-int boundary keeps the one-argument
        // absent-origin checkInt entry — no origin is fabricated there.
        String timeSource = "import * as time from \"std/time\"\n"
            + "export function main(): null { return null; }\n"
            + "export function test(): int {\n"
            + "  let t: int = time.nowMillis();\n"
            + "  return t;\n"
            + "}\n";
        String timeJava = int32Artifact(timeSource, "arith_time_origin");
        check(timeJava.contains("int t = checkInt("
                + RETAINED_TIME_EXPRESSION + ");"),
            "the time boundary keeps the span-less (absent-origin) "
                + "checkInt entry: "
                + emittedLine(timeJava, "int t = checkInt("));
        check(opsJava.contains("static int intAdd(int a, int b) { return "
                + "intAdd(a, b, null, -1, -1); }"),
            "the short int-arithmetic overload keeps the explicit "
                + "absent-origin sentinel (the internal entries)");

        // The real pipeline observes the projections end to end: the
        // null-conversion arm raises the pinned E8001 message through
        // javac + java (the byte-exact sidecar convergence itself is the
        // differential gate's lane proof).
        ExecResult nullRun = runInt32Project("export function main(): "
            + "null { return null; }\n"
            + "export function test(): int {\n"
            + "  let x: int | null = null;\n"
            + "  return int(x);\n"
            + "}\n", "arith_origins_null");
        check(nullRun.exitCode() == 1 && nullRun.output().contains(
                "DEAL_ERROR_CODE: E8001 cannot convert null to int"),
            "the int(null) arm raises the pinned E8001 message through "
                + "the real pipeline: " + nullRun.output());
        ExecResult fracRun = runInt32Project("export function main(): "
            + "null { return null; }\n"
            + "export function test(): int { return int(3.5); }\n",
            "arith_origins_frac");
        check(fracRun.exitCode() == 1 && fracRun.output().contains(
                "DEAL_ERROR_CODE: E8001 expected int, got non-integer "
                    + "number"),
            "the int(non-integer) arm raises the pinned E8001 message "
                + "through the real pipeline: " + fracRun.output());
    }

    /** The DEAL time-boundary pins (ISSUE-0375 D4 / ISSUE-0377 time pin;
     * jvm-int32-gate-activation-tree D4, Verification 1): under
     * {@code DEAL_V1_2_INT32} a real compiled program calling
     * {@code time.nowMillis()} through the full pipeline (frontend →
     * checker → JvmBackend → javac → java) raises exactly E8004 with
     * {@code int out of safe range}, exactly once, at the declared int
     * boundary — pinned at both a declaration initializer and a direct
     * int return. The emitted artifact wraps the byte-identical retained
     * {@code emitStdlibTimeMemberCall} expression in {@code checkInt(...)}
     * and applies no bare {@code (int)} narrowing to it. The emitted
     * expression text equals the pre-tree base expression byte-for-byte
     * ({@link #RETAINED_TIME_EXPRESSION}, compared by equality, never by
     * containment alone). The untouched default invocation keeps the
     * legacy carriers and does not raise. */
    private static void testInt32TimeBoundary() throws Exception {
        System.out.println("-- Int32 time boundary: E8004 at the declared int boundary --");

        String initSource = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): int {
              let t: int = time.nowMillis();
              return t;
            }
            """;
        ExecResult init = runInt32Project(initSource, "time_init");
        check(init.exitCode() == 1, "int32 time initializer run exits 1: "
            + init.output());
        check(countOccurrences(init.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "declaration initializer raises exactly E8004 with the pinned "
                + "message, exactly once, at the declared int boundary: "
                + init.output());
        check(!init.output().contains("DEAL_ERROR_CODE: E8001"),
            "the declaration initializer surfaces no other code (never "
                + "E8001): " + init.output());

        String retSource = """
            import * as time from "std/time"
            export function main(): null { return null; }
            function now(): int { return time.nowMillis(); }
            export function test(): int { return now(); }
            """;
        ExecResult ret = runInt32Project(retSource, "time_return");
        check(ret.exitCode() == 1, "int32 time return run exits 1: "
            + ret.output());
        check(countOccurrences(ret.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "direct int return raises exactly E8004 with the pinned "
                + "message, exactly once, at the declared int boundary: "
                + ret.output());
        check(!ret.output().contains("DEAL_ERROR_CODE: E8001"),
            "the direct int return surfaces no other code (never E8001): "
                + ret.output());

        // Artifact pins: the retained time expression is byte-identical
        // and wrapped by the signed32 checkInt at the boundary; no bare
        // (int) narrowing of the time value exists anywhere in the
        // artifact.
        String java = int32Artifact(initSource, "time_init_pin");
        check(java.contains(
                "int t = checkInt(" + RETAINED_TIME_EXPRESSION + ");"),
            "artifact wraps the byte-identical retained time expression in "
                + "checkInt at the declaration initializer");
        check(!java.contains("(int) " + RETAINED_TIME_EXPRESSION),
            "no bare (int) narrowing of the retained time expression "
                + "(the narrowing lives inside checkInt, behind the "
                + "signed32 gate)");
        check(java.contains("static int checkInt(long v, java.lang.String oFile, int oLine, int oCol) { if (v > 2147483647L || v < -2147483648L) throw new DealError(\"E8004\", \"int out of safe range\", oFile, oLine, oCol); return (int) v; }"),
            "int32 checkInt gate is [-2147483648, 2147483647] with E8004 "
                + "and the threaded origin — the time-boundary raise "
                + "stays span-less through the absent-origin entry");

        // The direct int return artifact wraps the same retained
        // expression at the return boundary.
        String retJava = int32Artifact(retSource, "time_return_pin");
        check(retJava.contains(
                "return checkInt(" + RETAINED_TIME_EXPRESSION + ");"),
            "the direct int return wraps the retained expression in "
                + "checkInt: "
                + retJava.lines().filter(l -> l.contains("return checkInt("))
                .findFirst().orElse("<missing>"));
        check(!retJava.contains("(int) " + RETAINED_TIME_EXPRESSION),
            "no bare (int) narrowing of the retained time expression at "
                + "the return boundary");

        // Retained-expression byte-identity pins (ISSUE-0377): the
        // emitted expression text equals the pre-tree base expression
        // byte-for-byte — extracted from the artifact and compared by
        // equality, never by containment alone.
        int wrapStart = java.indexOf("int t = checkInt(");
        String int32Expr = "";
        if (wrapStart >= 0) {
            wrapStart += "int t = checkInt(".length();
            int wrapEnd = java.indexOf(");", wrapStart);
            if (wrapEnd > wrapStart) {
                int32Expr = java.substring(wrapStart, wrapEnd);
            }
        }
        check(RETAINED_TIME_EXPRESSION.equals(int32Expr),
            "the int32 artifact's checkInt-wrapped time expression is "
                + "byte-identical to the pre-tree base expression: '"
                + int32Expr + "'");

        // The untouched default invocation stays legacy: the retained
        // expression crosses no int32 gate, the program runs green, and
        // the positive second-truncated value is observable.
        String legacyJava = legacyArtifact(initSource, "time_init_legacy");
        check(legacyJava.contains(
                "long t = " + RETAINED_TIME_EXPRESSION + ";"),
            "default (PRE_ACTIVATION → LEGACY_SAFE_INT) artifact keeps the "
                + "retained expression byte-identical with no int32 wrap");
        int legacyStart = legacyJava.indexOf("long t = ");
        String legacyExpr = "";
        if (legacyStart >= 0) {
            legacyStart += "long t = ".length();
            int legacyEnd = legacyJava.indexOf(";", legacyStart);
            if (legacyEnd > legacyStart) {
                legacyExpr = legacyJava.substring(legacyStart, legacyEnd);
            }
        }
        check(RETAINED_TIME_EXPRESSION.equals(legacyExpr),
            "the legacy artifact's time expression is byte-identical to "
                + "the pre-tree base expression: '" + legacyExpr + "'");
        ExecResult legacy = runLegacyProject(initSource, "time_init_legacy");
        check(legacy.exitCode() == 0, "legacy time run exits 0: "
            + legacy.output());
        check(!legacy.output().contains("DEAL_ERROR_CODE"),
            "legacy time run raises nothing (no int32 gate): "
                + legacy.output());
        check(!legacy.output().isBlank(),
            "legacy time run printed its value: " + legacy.output());
    }

    /** The D3 declared-int-boundary seam coverage pins for the
     * review-cycle-2 sites (the intrinsic {@code number()} int argument
     * and the jsonable default-expression emission): under
     * {@code DEAL_V1_2_INT32} the retained time expression crossing
     * these int-typed boundaries routes through the signed32
     * {@code checkInt} — each raises exactly E8004 once at the boundary,
     * no javac-rejected narrowing mismatch is left behind, no unchecked
     * boxed Long is stored in the jsonable Object slot, and the
     * untouched default invocation keeps the pre-tree byte shape and
     * runs green. */
    private static void testInt32BoundarySeamSites() throws Exception {
        System.out.println("-- Int32 boundary seam sites: number() argument and jsonable defaults --");

        // The intrinsic number() int argument is a declared int boundary.
        String numSource = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): number {
              let n: number = number(time.nowMillis());
              return n;
            }
            """;
        ExecResult num = runInt32Project(numSource, "number_arg_boundary");
        check(num.exitCode() == 1, "number(time.nowMillis()) run exits 1: "
            + num.output());
        check(countOccurrences(num.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "number(time.nowMillis()) raises exactly E8004 once at the "
                + "number() argument boundary: " + num.output());
        String numJava = int32Artifact(numSource, "number_arg_artifact");
        check(numJava.contains("numberFromInt(checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L))"),
            "the number() int argument routes through the signed32 "
                + "checkInt: "
                + numJava.lines().filter(l -> l.contains("numberFromInt"))
                .findFirst().orElse("<missing>"));
        check(!numJava.contains("numberFromInt((java.lang.System.currentTimeMillis() / 1000L)"),
            "no bare long-to-int pass-through at the number() argument");

        // Jsonable required int default: the $fromJsonValue default is a
        // declared int boundary. The checkInt gate raises there, and the
        // public C$fromJson wrapper's never-throw contract (the
        // jsonable slice's pinned surface — LuaJIT's _json_from_instance
        // "never throws") converts the boundary raise to the DEAL null —
        // the gate provably ran, since an unchecked boxed-Long store
        // would return a live instance instead.
        String reqSource = """
            import * as time from "std/time"
            // @jsonable
            export class C {
              f: int = time.nowMillis();
            }
            export function main(): null { return null; }
            export function test(): string {
              let c: C | null = C$fromJson("{}");
              if (c === null) { return "null-ok"; }
              return "bad";
            }
            """;
        ExecResult req = runInt32Project(reqSource, "jsonable_req_default");
        check(req.exitCode() == 0,
            "jsonable required-int default run exits 0 (never-throw): "
                + req.output());
        check(req.output().contains("null-ok"),
            "jsonable required-int default boundary raise converts to "
                + "the DEAL null (the gate ran at the boundary): "
                + req.output());
        String reqJava = int32Artifact(reqSource, "jsonable_req_default_artifact");
        check(reqJava.contains("int f0 = 0;")
                && reqJava.contains(
                    "f0 = checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L);"),
            "the jsonable required-int default field slot gates through "
                + "checkInt at the ISSUE-0302 omitted-default phase (the "
                + "declaration carries the type-safe placeholder): "
                + reqJava.lines().filter(l -> l.contains("f0 = "))
                .findFirst().orElse("<missing>"));
        check(!reqJava.contains("int f0 = (java.lang.System.currentTimeMillis() / 1000L)"),
            "no javac-rejected long-to-int default field slot");

        // Jsonable nullable-required int default: the java.lang.Integer
        // field slot gates through checkInt the same way (pre-fix this
        // shape emitted a javac-rejected long-to-Integer default slot).
        String nullableReqSource = """
            import * as time from "std/time"
            // @jsonable
            export class C {
              f: int | null = time.nowMillis();
            }
            export function main(): null { return null; }
            export function test(): string {
              let c: C | null = C$fromJson("{}");
              if (c === null) { return "null-ok"; }
              return "bad";
            }
            """;
        ExecResult nullableReq = runInt32Project(nullableReqSource,
            "jsonable_nullable_req_default");
        check(nullableReq.exitCode() == 0
                && nullableReq.output().contains("null-ok"),
            "jsonable nullable-required int default boundary raise "
                + "converts to the DEAL null (never-throw): "
                + nullableReq.output());
        String nullableReqJava = int32Artifact(nullableReqSource,
            "jsonable_nullable_req_default_artifact");
        check(nullableReqJava.contains("java.lang.Integer f0 = null;")
                && nullableReqJava.contains(
                    "f0 = checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L);"),
            "the jsonable nullable-required int default Integer slot "
                + "gates through checkInt at the ISSUE-0302 "
                + "omitted-default phase: "
                + nullableReqJava.lines().filter(l -> l.contains("f0 = "))
                .findFirst().orElse("<missing>"));
        check(!nullableReqJava.contains("java.lang.Integer f0 = (java.lang.System.currentTimeMillis() / 1000L)"),
            "no javac-rejected long-to-Integer default field slot");

        // Jsonable optional int default: a declared default on an
        // OPTIONAL field is checker-validated metadata that NEVER
        // evaluates (provider-versioned-default-plans D2, runtime page
        // D1) — the omitted field stays ABSENT ($MISSING), so fromJson
        // publishes a live instance and no boundary ever raises.
        String optSource = """
            import * as time from "std/time"
            // @jsonable
            export class C {
              f?: int = time.nowMillis();
            }
            export function main(): null { return null; }
            export function test(): string {
              let c: C | null = C$fromJson("{}");
              if (c === null) { return "null-ok"; }
              return "bad";
            }
            """;
        ExecResult opt = runInt32Project(optSource, "jsonable_opt_default");
        check(opt.exitCode() == 0,
            "jsonable optional-int default run exits 0 (never-throw): "
                + opt.output());
        check(opt.output().contains("bad"),
            "the optional default never evaluates: fromJson publishes a "
                + "live instance with the omitted field absent (the "
                + "probe returns \"bad\"): " + opt.output());
        String optJava = int32Artifact(optSource, "jsonable_opt_default_artifact");
        check(optJava.contains("java.lang.Object f0 = $MISSING;"),
            "the jsonable optional-int slot holds the Missing sentinel "
                + "placeholder (the declared default never runs): "
                + optJava.lines().filter(l -> l.contains("f0 = "))
                .findFirst().orElse("<missing>"));
        check(!optJava.contains("f0 = checkInt("),
            "no default evaluation at the jsonable optional-int slot: "
                + optJava.lines().filter(l -> l.contains("f0 = "))
                .findFirst().orElse("<missing>"));

        // Jsonable optional int default at direct construction: the
        // omitted optional field stays absent — no default evaluation,
        // no E8004 raise, the construction succeeds.
        String ctorSource = """
            import * as time from "std/time"
            // @jsonable
            export class C {
              f?: int = time.nowMillis();
            }
            export function main(): null { return null; }
            export function test(): string {
              let c: C = {};
              return "ok";
            }
            """;
        ExecResult ctor = runInt32Project(ctorSource, "jsonable_ctor_opt_slot");
        check(ctor.exitCode() == 0,
            "jsonable constructor optional slot run exits 0 (the "
                + "optional default never evaluates): " + ctor.output());
        check(ctor.output().contains("ok")
                && !ctor.output().contains("DEAL_ERROR_CODE"),
            "jsonable constructor optional slot never raises (no "
                + "default evaluation at construction): "
                + ctor.output());
        String ctorJava = int32Artifact(ctorSource,
            "jsonable_ctor_opt_slot_artifact");
        check(ctorJava.contains("return new $C_C(f0);"),
            "the jsonable constructor optional slot constructs with the "
                + "Missing sentinel slot (never the default expression): "
                + ctorJava.lines().filter(l -> l.contains("new $C_C"))
                .findFirst().orElse("<missing>"));

        // Integration over the plumbed profile (T1): the same programs
        // under the untouched default invocation emit the legacy byte
        // shape (no checkInt at these sites) and run green.
        String legacyNumJava = legacyArtifact(numSource, "number_arg_legacy");
        check(legacyNumJava.contains("numberFromInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L)"),
            "legacy number() argument keeps the pre-tree byte shape "
                + "(no checkInt wrap)");
        ExecResult legacyOpt = runLegacyProject(optSource,
            "jsonable_opt_default_legacy");
        check(legacyOpt.exitCode() == 0,
            "legacy jsonable optional-int default run exits 0: "
                + legacyOpt.output());
        check(!legacyOpt.output().contains("DEAL_ERROR_CODE"),
            "legacy jsonable default raises nothing (no int32 gate): "
                + legacyOpt.output());
    }

    /** The ISSUE-0376 anti-hollow matrix: one real compiled program per
     * declared-int-boundary kind under the explicit
     * {@code DEAL_V1_2_INT32} invocation — an out-of-range value (the
     * retained time expression, the one wider producer under the int32
     * carriers) raising exactly {@code E8004} once at the boundary
     * before any storage or use, and an in-range value (a host-module
     * int checked at the host seam, a gated int-array read, or an
     * integral JSON-shaped double through the table seam) crossing and
     * staying usable with its exact value asserted at runtime. Each
     * artifact pins the {@code checkInt(...)} wrap where the seam routes
     * a wider value, the pass-through where the value is already int
     * code, and the absence of a bare {@code (int)} cast at the declared
     * boundary. The two boundary kinds whose out-of-range raise is
     * structurally impossible under the int32 carriers (await
     * completion, array element read) are pinned by the invariant that
     * makes them impossible plus the in-range programs — never by a
     * skip. */
    private static void testInt32DeclaredBoundaryMatrix() throws Exception {
        System.out.println("-- Int32 declared-boundary matrix (every boundary kind, full pipeline) --");

        // ---- Out-of-range: the retained time expression. ----

        // Assignment target.
        String assignSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): int {
              let t: int = 0;
              t = time.nowMillis();
              return t;
            }
            """;
        ExecResult assign = runInt32Project(assignSrc, "boundary_assign");
        check(assign.exitCode() == 1,
            "int32 assignment boundary run exits 1: " + assign.output());
        check(countOccurrences(assign.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "assignment boundary raises exactly E8004 once: "
                + assign.output());
        String assignJava = int32Artifact(assignSrc,
            "boundary_assign_artifact");
        check(assignJava.contains(
                "t = checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L);"),
            "the assignment boundary wraps the retained expression in "
                + "checkInt: "
                + assignJava.lines().filter(l -> l.contains("= checkInt("))
                .findFirst().orElse("<missing>"));
        check(!assignJava.contains(
                "(int) (java.lang.System.currentTimeMillis()"),
            "no bare (int) narrowing of the retained time expression at "
                + "the assignment boundary");

        // Call argument (direct function call).
        String callSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            function use(p: int): int { return p; }
            export function test(): int {
              return use(time.nowMillis());
            }
            """;
        ExecResult callArg = runInt32Project(callSrc, "boundary_callarg");
        check(callArg.exitCode() == 1,
            "int32 call-argument boundary run exits 1: "
                + callArg.output());
        check(countOccurrences(callArg.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "call-argument boundary raises exactly E8004 once: "
                + callArg.output());
        String callJava = int32Artifact(callSrc,
            "boundary_callarg_artifact");
        check(callJava.contains(
                "return use(checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L));"),
            "the call argument wraps the retained expression in checkInt");
        check(!callJava.contains(
                "(int) (java.lang.System.currentTimeMillis()"),
            "no bare (int) narrowing of the retained time expression at "
                + "the call-argument boundary");

        // Callback argument (function-value dispatch).
        String cbSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            function use(p: int): int { return p; }
            export function test(): int {
              let f: (x: int) => int = use;
              return f(time.nowMillis());
            }
            """;
        ExecResult cb = runInt32Project(cbSrc, "boundary_callback");
        check(cb.exitCode() == 1,
            "int32 callback-argument boundary run exits 1: "
                + cb.output());
        check(countOccurrences(cb.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "callback-argument boundary raises exactly E8004 once: "
                + cb.output());
        String cbJava = int32Artifact(cbSrc, "boundary_callback_artifact");
        check(cbJava.contains("f.invokeAt(")
                && cbJava.contains(
                    "checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L))"),
            "the callback argument wraps the retained expression in "
                + "checkInt and dispatches through the invokeAt origin "
                + "seam");
        check(!cbJava.contains(
                "(int) (java.lang.System.currentTimeMillis()"),
            "no bare (int) narrowing of the retained time expression at "
                + "the callback-argument boundary");

        // Array element write — and the raise happens BEFORE any
        // storage: a catch around the write reads the untouched
        // element back.
        String arrWriteSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): int {
              let xs: int[] = [1, 2];
              xs[0] = time.nowMillis();
              return xs[0];
            }
            """;
        ExecResult arrWrite = runInt32Project(arrWriteSrc,
            "boundary_arrwrite");
        check(arrWrite.exitCode() == 1,
            "int32 array-write boundary run exits 1: " + arrWrite.output());
        check(countOccurrences(arrWrite.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "array-write boundary raises exactly E8004 once: "
                + arrWrite.output());
        String arrWriteJava = int32Artifact(arrWriteSrc,
            "boundary_arrwrite_artifact");
        check(arrWriteJava.contains(
                "__intArrayWrite(xs, 0, checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L),"),
            "the array element write wraps the retained expression in "
                + "checkInt before the storage helper call");
        check(!arrWriteJava.contains(
                "(int) (java.lang.System.currentTimeMillis()"),
            "no bare (int) narrowing of the retained time expression at "
                + "the array-write boundary");
        String noStoreSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): int {
              let xs: int[] = [1, 2];
              try {
                xs[0] = time.nowMillis();
              } catch (e) {
                return xs[0];
              }
              return 0;
            }
            """;
        ExecResult noStore = runInt32Project(noStoreSrc, "boundary_no_store");
        check(noStore.exitCode() == 0
                && noStore.output().contains("1"),
            "the E8004 raise happens before any storage (the catch reads "
                + "the untouched element 1): " + noStore.output());

        // Await completion: under the int32 carriers no out-of-range
        // value can reach the await site itself — a DEAL async
        // function's declared-int return boundary raises E8004 first,
        // and a host async completion is checked at the host seam. The
        // raise is pinned at the async return boundary, and the await
        // site passes the already-int completion through unchanged.
        String asyncTimeSrc = """
            import * as time from "std/time"
            export function main(): null { return null; }
            async function g(): int { return time.nowMillis(); }
            export async function test(): int {
              return await g();
            }
            """;
        ExecResult asyncTime = runInt32Project(asyncTimeSrc,
            "boundary_await_site");
        check(asyncTime.exitCode() == 1,
            "int32 await-site run exits 1 (the raise surfaces at the "
                + "async return boundary): " + asyncTime.output());
        check(countOccurrences(asyncTime.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "exactly one E8004 — the async return boundary raises it: "
                + asyncTime.output());
        String asyncTimeJava = int32Artifact(asyncTimeSrc,
            "boundary_await_site_artifact");
        check(asyncTimeJava.contains(
                "return checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L);"),
            "the async return boundary wraps the retained expression in "
                + "checkInt");
        check(asyncTimeJava.contains("return g();"),
            "the await completion is already the int carrier and passes "
                + "through unchanged: "
                + asyncTimeJava.lines().filter(l -> l.contains("return g"))
                .findFirst().orElse("<missing>"));
        check(!asyncTimeJava.contains("checkInt(g())"),
            "no redundant checkInt wrap around the int-typed DEAL async "
                + "completion at the await site");

        // Table-read int target: an integral JSON-shaped double outside
        // the signed32 range stored in the table crosses the shared
        // $check seam's "int" branch, whose route through checkInt
        // raises exactly E8004 at the read boundary.
        String tableOutSrc = """
            export function main(): null { return null; }
            export function test(): int {
              let t: table = {x: 1000000000000.0};
              let v: int = t.x;
              return v;
            }
            """;
        ExecResult tableOut = runInt32Project(tableOutSrc,
            "boundary_tableread_out");
        check(tableOut.exitCode() == 1,
            "int32 out-of-range table read run exits 1: "
                + tableOut.output());
        check(countOccurrences(tableOut.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "out-of-range table read raises exactly E8004 once: "
                + tableOut.output());
        String tableOutJava = int32Artifact(tableOutSrc,
            "boundary_tableread_out_artifact");
        check(tableOutJava.contains(
                "int v = ((java.lang.Integer) $check(\"int\", (t).get(\"x\"),"),
            "the table-read int target routes through the shared $check "
                + "seam's int branch with the binding's declared "
                + "annotation as its origin");
        check(tableOutJava.contains(
                "if (v instanceof java.lang.Integer i) return checkInt(i, oFile, oLine, oCol);"),
            "the $check int branch routes through the signed32 checkInt "
                + "under int32 (the gate runs at the read boundary)");

        // Array element read: no out-of-range value can exist in int32
        // int storage — the write gate above raises before any store,
        // so every read yields an in-range int. The read boundary is
        // pinned by that invariant plus the in-range programs below.

        // ---- In-range: host-module values (the dynamic value crosses
        // the host seam's signed32 checkInt and returns as the
        // primitive int carrier), gated int-array reads, and an
        // integral in-range double through the table seam. Each asserts
        // the exact stored/returned/passed value at runtime. ----

        // Variable-declaration initializer.
        String hostInitSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function test(): int {
              let t: int = log.add(20, 22);
              return t;
            }
            """;
        ExecResult hostInit = runInt32HostProject(hostInitSrc,
            "boundary_init_in");
        check(hostInit.exitCode() == 0,
            "in-range host initializer run exits 0: " + hostInit.output());
        check(hostInit.output().contains("42"),
            "the in-range value crosses the declaration boundary and "
                + "stays usable (42): " + hostInit.output());
        String hostInitJava = int32HostArtifact(hostInitSrc,
            "boundary_init_in");
        check(hostInitJava.contains("int t = __host$log$add(20, 22, "),
            "the host call result is already the int carrier at the "
                + "declaration boundary (pass-through, no redundant "
                + "gate): "
                + hostInitJava.lines().filter(l -> l.contains("int t = "))
                .findFirst().orElse("<missing>"));
        check(hostInitJava.contains(
                "if (v instanceof java.lang.Integer i) return checkInt(i, oFile, oLine, oCol);"),
            "the dynamic host value crossed the signed32 checkInt at the "
                + "host seam (the gate ran, never skipped)");

        // Assignment target.
        String hostAssignSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function test(): int {
              let t: int = 0;
              t = log.add(2, 3);
              return t;
            }
            """;
        ExecResult hostAssign = runInt32HostProject(hostAssignSrc,
            "boundary_assign_in");
        check(hostAssign.exitCode() == 0
                && hostAssign.output().contains("5"),
            "in-range assignment value crosses and stays usable (5): "
                + hostAssign.output());
        String hostAssignJava = int32HostArtifact(hostAssignSrc,
            "boundary_assign_in");
        check(hostAssignJava.contains("t = __host$log$add(2, 3, "),
            "the host call result passes through the assignment boundary "
                + "as the int carrier");

        // Return.
        String hostRetSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function test(): int {
              return log.add(6, 7);
            }
            """;
        ExecResult hostRet = runInt32HostProject(hostRetSrc,
            "boundary_return_in");
        check(hostRet.exitCode() == 0 && hostRet.output().contains("13"),
            "in-range return value crosses and stays usable (13): "
                + hostRet.output());
        String hostRetJava = int32HostArtifact(hostRetSrc,
            "boundary_return_in");
        check(hostRetJava.contains("return __host$log$add(6, 7, "),
            "the host call result passes through the return boundary as "
                + "the int carrier");

        // Call argument (direct call).
        String hostArgSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            function use(p: int): int { return p; }
            export function test(): int {
              return use(log.add(8, 9));
            }
            """;
        ExecResult hostArg = runInt32HostProject(hostArgSrc,
            "boundary_callarg_in");
        check(hostArg.exitCode() == 0 && hostArg.output().contains("17"),
            "in-range call-argument value crosses and stays usable (17): "
                + hostArg.output());
        String hostArgJava = int32HostArtifact(hostArgSrc,
            "boundary_callarg_in");
        check(hostArgJava.contains("return use(__host$log$add(8, 9, "),
            "the host call result passes through the call-argument "
                + "boundary as the int carrier");

        // Callback argument (function-value dispatch).
        String hostCbSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            function use(p: int): int { return p; }
            export function test(): int {
              let f: (x: int) => int = use;
              return f(log.add(10, 11));
            }
            """;
        ExecResult hostCb = runInt32HostProject(hostCbSrc,
            "boundary_callback_in");
        check(hostCb.exitCode() == 0 && hostCb.output().contains("21"),
            "in-range callback-argument value crosses and stays usable "
                + "(21): " + hostCb.output());
        String hostCbJava = int32HostArtifact(hostCbSrc,
            "boundary_callback_in");
        check(hostCbJava.contains("f.invokeAt(")
                && hostCbJava.contains("__host$log$add(10, 11, "),
            "the host call result passes through the callback-argument "
                + "boundary as the int carrier (dispatched through the "
                + "invokeAt origin seam)");

        // Await completion (host async, boxed at the host seam).
        String hostAwaitSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export async function test(): int {
              return await log.fetchInt();
            }
            """;
        ExecResult hostAwait = runInt32HostProject(hostAwaitSrc,
            "boundary_await_in");
        check(hostAwait.exitCode() == 0 && hostAwait.output().contains("7"),
            "in-range host async completion crosses the await boundary "
                + "and stays usable (7): " + hostAwait.output());
        String hostAwaitJava = int32HostArtifact(hostAwaitSrc,
            "boundary_await_in");
        check(hostAwaitJava.contains("return __host$log$fetchInt("),
            "the host async completion passes through the await boundary "
                + "as the int carrier (the completion check ran inside "
                + "the host wrapper)");
        check(!hostAwaitJava.contains("checkInt(__host$log$fetchInt("),
            "no redundant gate around the already-checked host async "
                + "completion");

        // Array element write (in-range host value).
        String hostArrWriteSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function test(): int {
              let xs: int[] = [0];
              xs[0] = log.add(12, 13);
              return xs[0];
            }
            """;
        ExecResult hostArrWrite = runInt32HostProject(hostArrWriteSrc,
            "boundary_arrwrite_in");
        check(hostArrWrite.exitCode() == 0
                && hostArrWrite.output().contains("25"),
            "in-range array-write value crosses and stays usable (25): "
                + hostArrWrite.output());
        String hostArrWriteJava = int32HostArtifact(hostArrWriteSrc,
            "boundary_arrwrite_in");
        check(hostArrWriteJava.contains(
                "__intArrayWrite(xs, 0, __host$log$add(12, 13, "),
            "the host call result passes through the array-write "
                + "boundary as the int carrier");

        // Nullable host int return: the DEAL null crosses the
        // int | null boundary unchanged (the pre-fix seam wrapped the
        // boxed host value in checkInt and auto-unboxed the null into a
        // raw NullPointerException — the regression pin).
        String hostNullSrc = """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function test(): int {
              let n: int | null = log.maybe();
              if (n === null) { return 7; }
              return 0;
            }
            """;
        ExecResult hostNull = runInt32HostProject(hostNullSrc,
            "boundary_null_in");
        check(hostNull.exitCode() == 0 && hostNull.output().contains("7"),
            "the DEAL null from a nullable host return crosses the "
                + "int | null boundary unchanged (7): " + hostNull.output());
        String hostNullJava = int32HostArtifact(hostNullSrc,
            "boundary_null_in");
        check(hostNullJava.contains(
                "java.lang.Integer n = __host$log$maybe("),
            "the nullable host return passes through the int | null "
                + "boundary (no null-unsafe checkInt wrap)");
        check(!hostNullJava.contains("checkInt(__host$log$maybe("),
            "no null-unsafe checkInt wrap around the nullable host "
                + "return");

        // Array element read (in-range, gated storage).
        String arrReadSrc = """
            export function main(): null { return null; }
            export function test(): int {
              let xs: int[] = [33, 34];
              let a: int = xs[0];
              let b: int = xs[1];
              return a + b;
            }
            """;
        ExecResult arrRead = runInt32Project(arrReadSrc,
            "boundary_arrread_in");
        check(arrRead.exitCode() == 0 && arrRead.output().contains("67"),
            "in-range array reads cross the boundaries and stay usable "
                + "(67): " + arrRead.output());
        String arrReadJava = int32Artifact(arrReadSrc,
            "boundary_arrread_in_artifact");
        check(arrReadJava.contains("int a = __intArrayRead(xs, 0,"),
            "the int-array read emits the primitive int carrier at the "
                + "declaration boundary");
        check(arrReadJava.contains("int b = __intArrayRead(xs, 1,"),
            "the second read does the same");
        check(!arrReadJava.contains("checkInt(__intArrayRead("),
            "no redundant gate around the in-range gated-storage read");

        // Nullable array read (in-range boxed element, gated at write).
        String arrNullReadSrc = """
            export function main(): null { return null; }
            export function test(): int {
              let xs: (int | null)[] = [];
              xs[0] = 42;
              let n: int | null = xs[0];
              return int(n);
            }
            """;
        ExecResult arrNullRead = runInt32Project(arrNullReadSrc,
            "boundary_arrnullread_in");
        check(arrNullRead.exitCode() == 0
                && arrNullRead.output().contains("42"),
            "the in-range boxed nullable read crosses the int | null "
                + "boundary and stays usable (42): "
                + arrNullRead.output());
        String arrNullReadJava = int32Artifact(arrNullReadSrc,
            "boundary_arrnullread_in_artifact");
        check(arrNullReadJava.contains(
                "java.lang.Integer n = __intOrNullArrayRead(xs, 0,"),
            "the nullable int-array read emits the boxed element carrier "
                + "at the int | null boundary");
        check(!arrNullReadJava.contains("checkInt(__intOrNullArrayRead("),
            "no null-unsafe gate around the in-range nullable read "
                + "(storage is gated at write)");

        // Table-read int target (in-range integral double).
        String tableInSrc = """
            export function main(): null { return null; }
            export function test(): int {
              let t: table = {x: 42.0};
              let v: int = t.x;
              return v;
            }
            """;
        ExecResult tableIn = runInt32Project(tableInSrc,
            "boundary_tableread_in");
        check(tableIn.exitCode() == 0 && tableIn.output().contains("42"),
            "the in-range integral double crosses the table seam's "
                + "checkInt and stays usable (42): " + tableIn.output());
        String tableInJava = int32Artifact(tableInSrc,
            "boundary_tableread_in_artifact");
        check(tableInJava.contains(
                "int v = ((java.lang.Integer) $check(\"int\", (t).get(\"x\"),"),
            "the in-range table read routes through the same $check int "
                + "branch");

        // ---- Under LEGACY_SAFE_INT the seam adds nothing at any of
        // these sites — the pre-tree byte shapes stay. ----

        String legacyAssignJava = legacyArtifact(assignSrc,
            "boundary_assign_legacy");
        check(legacyAssignJava.contains(
                "t = (java.lang.System.currentTimeMillis() / 1000L) * 1000L;"),
            "legacy assignment keeps the pre-tree byte shape (no int32 "
                + "wrap)");
        check(!legacyAssignJava.contains(
                "checkInt((java.lang.System.currentTimeMillis()"),
            "no int32 gate leaks into the legacy assignment artifact");
        String legacyCbJava = legacyArtifact(cbSrc, "boundary_cb_legacy");
        check(legacyCbJava.contains("f.invokeAt(")
                && legacyCbJava.contains(
                    "(java.lang.System.currentTimeMillis() / 1000L) * 1000L)"),
            "legacy callback argument keeps the pre-tree byte shape (no "
                + "int32 wrap) and dispatches through the invokeAt origin "
                + "seam");
        String legacyArrWriteJava = legacyArtifact(arrWriteSrc,
            "boundary_arrwrite_legacy");
        check(legacyArrWriteJava.contains(
                "__intArrayWrite(xs, 0L, (java.lang.System.currentTimeMillis() / 1000L) * 1000L,"),
            "legacy array element write keeps the pre-tree byte shape "
                + "(the legacy helper gates the long carrier internally): "
                + legacyArrWriteJava.lines()
                    .filter(l -> l.contains("__intArrayWrite(xs"))
                    .findFirst().orElse("<missing>"));
        String legacyAwaitJava = legacyArtifact(asyncTimeSrc,
            "boundary_await_legacy");
        check(legacyAwaitJava.contains("checkInt(g())"),
            "legacy await keeps its pre-tree checkInt wrap over the long "
                + "completion (byte-identical)");
    }

    /** The signed32 helper edge matrix (ISSUE-0375 anti-hollow; the Task
     * verification edge list): one real program per edge, compiled and
     * run through the full pipeline under the explicit
     * {@code DEAL_V1_2_INT32} invocation, each asserting the exact code
     * (E8004/E8005/E8006/E8001) and message, with in-range cases
     * asserting the correct stored value. Every raise is observed from
     * the executed artifact — never from reading helper source.
     * ISSUE-0394 pins the two epic pow bands ({@code 2 ** 62} → E8004,
     * {@code 2 ** 1024} → E8001 infinity) and corrects the truncated
     * remainder pin {@code -2147483648 % -1} → {@code 0} (the
     * spec-v1.2 remainder rule; only the division raises on
     * {@code MIN_VALUE / -1}). */
    private static void testInt32EdgeMatrix() throws Exception {
        System.out.println("-- Int32 signed32 helper edge matrix (full pipeline) --");

        record EdgePin(String name, String body, String expected) {}
        List<EdgePin> pins = List.of(
            new EdgePin("add-overflow", "return 2147483647 + 1;",
                "E8004 int out of safe range"),
            new EdgePin("add-underflow", "return -2147483648 + (-1);",
                "E8004 int out of safe range"),
            new EdgePin("min-literal-in-range",
                "let x: int = -2147483648;\n      return x;",
                "-2147483648"),
            new EdgePin("sub-underflow", "return -2147483648 - 1;",
                "E8004 int out of safe range"),
            new EdgePin("sub-overflow", "return 2147483647 - (-1);",
                "E8004 int out of safe range"),
            new EdgePin("mul-overflow", "return 50000 * 50000;",
                "E8004 int out of safe range"),
            new EdgePin("mul-underflow", "return -50000 * 50000;",
                "E8004 int out of safe range"),
            new EdgePin("div-min-by-minus-one", "return -2147483648 / -1;",
                "E8004 int out of safe range"),
            new EdgePin("mod-min-by-minus-one", "return -2147483648 % -1;",
                "0"),
            new EdgePin("div-by-zero", "return 1 / 0;",
                "E8005 integer division by zero"),
            new EdgePin("mod-by-zero", "return 1 % 0;",
                "E8005 integer division by zero"),
            new EdgePin("neg-min", "return -(-2147483648);",
                "E8004 int out of safe range"),
            new EdgePin("neg-zero", "return -(0);", "0"),
            new EdgePin("pow-negative-exponent", "return 2 ** -1;",
                "E8006 integer exponent must be non-negative"),
            new EdgePin("pow-out-of-range", "return 2 ** 31;",
                "E8004 int out of safe range"),
            new EdgePin("pow-band-62", "return 2 ** 62;",
                "E8004 int out of safe range"),
            new EdgePin("pow-band-1024", "return 2 ** 1024;",
                "E8001 expected int, got infinity"),
            new EdgePin("pow-nonfinite", "return 10 ** 400;",
                "E8001 expected int, got infinity"),
            new EdgePin("pow-in-range", "return 2 ** 30;", "1073741824"),
            new EdgePin("intfrom-nan", "return int(0.0 / 0.0);",
                "E8001 expected int, got NaN"),
            new EdgePin("intfrom-infinity", "return int(1.0 / 0.0);",
                "E8001 expected int, got infinity"),
            new EdgePin("intfrom-noninteger", "return int(0.5);",
                "E8001 expected int, got non-integer number"),
            new EdgePin("intfrom-out-of-range-hi",
                "return int(2147483648.0);",
                "E8004 int out of safe range"),
            new EdgePin("intfrom-out-of-range-lo",
                "return int(-2147483649.0);",
                "E8004 int out of safe range"),
            new EdgePin("intfrom-in-range",
                "return int(2147483647.0) + int(-2147483648.0);", "-1"),
            new EdgePin("trunc-div", "return (-5) / 2;", "-2"),
            new EdgePin("trunc-mod", "return (-5) % 2;", "-1"));
        for (EdgePin pin : pins) {
            String source = "export function main(): null { return null; }\n"
                + "export function test(): int {\n      " + pin.body() + "\n"
                + "    }\n";
            ExecResult r = runInt32Project(source, pin.name());
            if (pin.expected().startsWith("E8")) {
                check(r.exitCode() == 1,
                    pin.name() + " run exits 1: " + r.output());
                check(r.output().contains("DEAL_ERROR_CODE: "
                        + pin.expected()),
                    pin.name() + " raises exactly " + pin.expected()
                        + ": " + r.output());
            } else {
                check(r.exitCode() == 0,
                    pin.name() + " run exits 0: " + r.output());
                check(r.output().contains(pin.expected()),
                    pin.name() + " stores the correct value "
                        + pin.expected() + ": " + r.output());
            }
        }

        // Artifact pins for the int32 minimum literal spelling
        // (ISSUE-0375 review): NEG(IntLiteral 2147483648) folds into the
        // Java int literal -2147483648 — never intNeg(checkInt(2147483648L)),
        // whose checkInt gate would raise the spurious E8004 before the
        // negation. The pinned -2147483648 - 1 edge runs with its literal
        // spelling and the inclusive gate range admits the minimum.
        String minSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n      let x: int = -2147483648;\n"
            + "      return x;\n    }\n";
        String minJava = int32Artifact(minSource, "min_literal_artifact");
        check(minJava.contains("int x = -2147483648;"),
            "min literal folds to the Java int literal -2147483648 at the "
                + "declaration initializer: "
                + minJava.lines().filter(l -> l.contains("2147483648")
                    && !l.contains("checkInt") && !l.contains("intPow")
                    && !l.contains("intFromNumber") && !l.contains("//"))
                .findFirst().orElse("<missing>"));
        check(!minJava.contains("intNeg(checkInt(2147483648L))")
                && !minJava.contains("checkInt(2147483648L)"),
            "no checkInt(2147483648L) gate for the min literal spelling "
                + "(no spurious E8004)");
        String subSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n      return -2147483648 - 1;\n"
            + "    }\n";
        String subJava = int32Artifact(subSource, "min_literal_sub_artifact");
        check(hasOriginCall(subJava, "return intSub(-2147483648, 1,"),
            "the pinned -2147483648 - 1 edge emits with its literal "
                + "spelling through intSub and the origin literals: "
                + subJava.lines().filter(l -> l.contains("intSub"))
                .findFirst().orElse("<missing>"));
        check(!subJava.contains("checkInt(2147483648L)"),
            "the -2147483648 - 1 literal operand never crosses the "
                + "out-of-range checkInt gate");

        // ISSUE-0394 direct literal emission: under the profile-aware
        // parser's E1036 guarantee the int32 branch emits plain Java int
        // literals with no point-of-use literal check (the legacy
        // point-of-use checkInt literal gate exists only in the legacy
        // branch).
        String maxSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n      let x: int = 2147483647;\n"
            + "      return x;\n    }\n";
        String maxJava = int32Artifact(maxSource, "max_literal_artifact");
        check(maxJava.contains("int x = 2147483647;"),
            "the int32 branch emits the max literal directly (in range by "
                + "E1036, no point-of-use literal check): "
                + maxJava.lines().filter(l -> l.contains("2147483647"))
                .findFirst().orElse("<missing>"));
        check(!maxJava.contains("checkInt(2147483647L)"),
            "no point-of-use literal check exists in the int32 branch");
        String legacyMaxJava = legacyArtifact("""
            export function test(): int {
              let x: int = 9223372036854775807;
              return x;
            }
            """, "legacy_max_literal_artifact");
        check(legacyMaxJava.contains("long x = checkInt(9223372036854775807L);"),
            "the legacy point-of-use literal check stays in the legacy "
                + "branch only: "
                + legacyMaxJava.lines().filter(l -> l.contains("checkInt"))
                .findFirst().orElse("<missing>"));

        // The integration proof over the plumbed profile (T1): the same
        // add-overflow program under the untouched DEFAULT invocation
        // emits legacy artifacts, where 2147483647 + 1 stays inside the
        // ±(2^53-1) safe range and does not raise — a missing or
        // defaulted profile can never produce the int32 raise.
        String addSource = "export function main(): null { return null; }\n"
            + "export function test(): int {\n      return 2147483647 + 1;\n"
            + "    }\n";
        ExecResult legacy = runLegacyProject(addSource, "add_overflow_legacy");
        check(legacy.exitCode() == 0,
            "default-profile add-overflow run exits 0: " + legacy.output());
        check(legacy.output().contains("2147483648"),
            "default-profile add-overflow stays in the legacy safe range: "
                + legacy.output());
    }

    /** The legacy byte-compat pin (ISSUE-0375 D1 legacy arm / Task
     * verification): under {@code LEGACY_SAFE_INT} the emitted
     * preamble/helpers are byte-identical to the pre-tree base (the
     * {@link #LEGACY_BASE_INT_HELPERS} capture), the int32 carrier never
     * leaks into the legacy artifact, the retained time expression stays
     * unwrapped, and the legacy runtime behavior is unchanged — a
     * 2147483648-scale safe-int value still passes while the ±(2^53-1)
     * overflow gate still raises E8004. */
    private static void testLegacyByteCompat() throws Exception {
        System.out.println("-- Legacy byte-compat pin (pre-tree base helpers) --");

        String source = """
            import * as time from "std/time"
            function add(a: int, b: int): int { return a + b; }
            export function test(): int {
              let t: int = time.nowMillis();
              let x: int = add(40, 2);
              let n: number = number(7);
              let i2: int = int(3.0);
              return x + i2 + int(n);
            }
            """;
        String java = legacyArtifact(source, "bytecompat");
        check(java.contains(LEGACY_BASE_INT_HELPERS),
            "LEGACY_SAFE_INT preamble/helpers are byte-identical to the "
                + "pre-tree base (the captured helper block appears "
                + "verbatim)");
        check(!java.contains("static int checkInt("),
            "no int32 checkInt carrier leaks into the legacy artifact");
        check(!java.contains("static int intAdd(int a, int b)"),
            "no int32 intAdd carrier leaks into the legacy artifact");
        check(java.contains("static long intAdd(long a, long b)"),
            "legacy long carriers kept");
        check(java.contains("long t = (java.lang.System.currentTimeMillis() / 1000L) * 1000L;"),
            "legacy retained time expression byte-identical, no int32 wrap");

        // Legacy runtime unchanged: a 2147483648-scale safe-int value
        // still passes, and the legacy overflow gate still raises E8004
        // at the ±(2^53-1) boundary.
        ExecResult inRange = compileAndRunJvm("""
            export function test(): int { return 2147483648; }
            """, "legacy-safe-scale");
        check(inRange.exitCode() == 0,
            "legacy safe-scale run exits 0: " + inRange.output());
        check(inRange.output().contains("2147483648"),
            "legacy ±(2^53-1) safe-int value unchanged: "
                + inRange.output());

        // The min-literal spelling under LEGACY_SAFE_INT keeps its
        // pre-tree emission shape intNeg(2147483648L) (the fold is
        // int32-only) and still stores -2147483648 correctly — the
        // regression guard for the int32 fold.
        String minLegacyJava = legacyArtifact("""
            export function test(): int { return -2147483648; }
            """, "legacy_min_literal_artifact");
        check(hasOriginCall(minLegacyJava, "return intNeg(2147483648L,"),
            "legacy min literal keeps the base emission shape "
                + "intNeg(2147483648L) with the origin literals: "
                + minLegacyJava.lines().filter(l -> l.contains("intNeg"))
                .findFirst().orElse("<missing>"));
        check(!minLegacyJava.contains("return -2147483648;"),
            "no int32 fold leaks into the legacy artifact");
        ExecResult legacyMin = compileAndRunJvm("""
            export function test(): int { return -2147483648; }
            """, "legacy-min-literal");
        check(legacyMin.exitCode() == 0,
            "legacy min-literal run exits 0: " + legacyMin.output());
        check(legacyMin.output().contains("-2147483648"),
            "legacy stores -2147483648 correctly: " + legacyMin.output());

        ExecResult over = compileAndRunJvm("""
            export function test(): int { return 9007199254740991 + 1; }
            """, "legacy-safe-overflow");
        check(over.exitCode() == 1
                && over.output().contains(
                    "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "legacy safe-range overflow gate unchanged: " + over.output());
    }

    /** The v1.2 IEEE number-pow wrapper (ISSUE-0394): under
     * {@code DEAL_V1_2_INT32} the emitted number {@code **} call is
     * {@code numPow(...)} — the pinned IEEE-754 wrapper correcting the
     * two Java-vs-IEEE deviations ({@code pow(1.0, NaN)} and
     * {@code pow(±1.0, ±Infinity)}) — while the
     * {@code LEGACY_SAFE_INT} emission stays the byte-identical raw
     * {@code java.lang.Math.pow} call (whose Java contract yields NaN on
     * exactly those two cases — the legacy negative controls prove the
     * wrapper is profile-gated). Every band case compiles and runs
     * through the full pipeline under the explicit
     * {@code DEAL_V1_2_INT32} invocation. */
    private static void testInt32NumberPowBand() throws Exception {
        System.out.println("-- Int32 IEEE number-pow band (numPow wrapper, full pipeline) --");

        // Emission pins: legacy keeps the raw Math.pow call
        // byte-identical; int32 emits the numPow wrapper with the pinned
        // corrections.
        String src = """
            export function main(): null { return null; }
            export function test(): number { return 2.0 ** 3.0; }
            """;
        String legacy = legacyArtifact(src, "numpow_legacy");
        check(legacy.contains("java.lang.Math.pow(2.0, 3.0)"),
            "legacy number pow keeps the raw Math.pow call: "
                + legacy.lines().filter(l -> l.contains("Math.pow"))
                .findFirst().orElse("<missing>"));
        check(!legacy.contains("numPow"),
            "no numPow wrapper leaks into the legacy artifact");
        String i32 = int32Artifact(src, "numpow_i32");
        check(i32.contains("numPow(2.0, 3.0)"),
            "int32 number pow emits the numPow wrapper call: "
                + i32.lines().filter(l -> l.contains("numPow"))
                .findFirst().orElse("<missing>"));
        check(i32.contains("static double numPow(double a, double b) { if (a == 1.0 && java.lang.Double.isNaN(b)) return 1.0; if (java.lang.Math.abs(a) == 1.0 && java.lang.Double.isInfinite(b)) return 1.0; return java.lang.Math.pow(a, b); }"),
            "int32 artifact carries the pinned IEEE numPow helper (the "
                + "two Java-vs-IEEE corrections)");
        check(!i32.contains("java.lang.Math.pow(2.0, 3.0)"),
            "no raw Math.pow call at the user number-pow site under v1.2");

        // Full-pipeline band: one real compiled+executed program per
        // pinned IEEE case under the explicit DEAL_V1_2_INT32
        // invocation.
        record PowPin(String name, String body, String expected) {}
        List<PowPin> pins = List.of(
            new PowPin("one-pow-nan", "return 1.0 ** (0.0 / 0.0);", "1.0"),
            new PowPin("neg-one-pow-infinity", "return (-1.0) ** (1.0 / 0.0);", "1.0"),
            new PowPin("zero-pow-zero", "return 0.0 ** 0.0;", "1.0"),
            new PowPin("zero-pow-neg-one", "return 0.0 ** -1.0;", "Infinity"),
            new PowPin("neg-two-pow-half", "return (-2.0) ** 0.5;", "NaN"),
            new PowPin("two-pow-1024", "return 2.0 ** 1024.0;", "Infinity"),
            new PowPin("two-pow-neg-1075", "return 2.0 ** -1075.0;", "0.0"),
            new PowPin("nan-pow-zero", "return (0.0 / 0.0) ** 0.0;", "1.0"),
            new PowPin("two-pow-ten", "return 2.0 ** 10.0;", "1024.0"),
            new PowPin("neg-two-pow-three", "return (-2.0) ** 3.0;", "-8.0"));
        for (PowPin pin : pins) {
            String source = "export function main(): null { return null; }\n"
                + "export function test(): number {\n      " + pin.body() + "\n"
                + "    }\n";
            ExecResult r = runInt32Project(source, "numpow_" + pin.name());
            check(r.exitCode() == 0,
                pin.name() + " run exits 0: " + r.output());
            check(r.output().contains(pin.expected()),
                pin.name() + " yields exactly " + pin.expected() + ": "
                    + r.output());
        }

        // Legacy negative controls: under LEGACY_SAFE_INT the raw Java
        // Math.pow contract stays byte-identical, so the two deviation
        // cases yield NaN (proving the IEEE corrections are
        // profile-gated).
        ExecResult legacyOne = runLegacyProject("""
            export function main(): null { return null; }
            export function test(): number { return 1.0 ** (0.0 / 0.0); }
            """, "numpow_one_nan");
        check(legacyOne.exitCode() == 0
                && legacyOne.output().contains("NaN"),
            "legacy 1.0 ** NaN keeps the raw Java Math.pow NaN result: "
                + legacyOne.output());
        ExecResult legacyNegOne = runLegacyProject("""
            export function main(): null { return null; }
            export function test(): number { return (-1.0) ** (1.0 / 0.0); }
            """, "numpow_neg_one_inf");
        check(legacyNegOne.exitCode() == 0
                && legacyNegOne.output().contains("NaN"),
            "legacy (-1.0) ** Infinity keeps the raw Java Math.pow NaN "
                + "result: " + legacyNegOne.output());
    }

    /** The int32 declared-boundary E8004 pins for the array-element and
     * class-field sites (ISSUE-0394 verification): under
     * {@code DEAL_V1_2_INT32} a wider value (the retained time
     * expression) crossing an {@code int[]} element-write boundary or a
     * class int-field construction boundary raises exactly E8004
     * {@code int out of safe range} once at the boundary, the emitted
     * artifact wraps the retained expression in the signed32
     * {@code checkInt}, and the untouched default invocation keeps the
     * legacy shape and does not raise. */
    private static void testInt32ArrayAndFieldBoundaries() throws Exception {
        System.out.println("-- Int32 array-element and class-field boundary E8004 --");

        String arraySource = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test(): int {
              let xs: int[] = [0];
              xs[0] = time.nowMillis();
              return xs[0];
            }
            """;
        ExecResult arr = runInt32Project(arraySource, "array_element_boundary");
        check(arr.exitCode() == 1, "int32 array element write run exits 1: "
            + arr.output());
        check(countOccurrences(arr.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "array element write raises exactly E8004 once at the "
                + "boundary: " + arr.output());
        String arrJava = int32Artifact(arraySource, "array_element_artifact");
        check(arrJava.contains("__intArrayWrite(xs, 0, checkInt((java.lang.System.currentTimeMillis() / 1000L) * 1000L),"),
            "the int[] element write routes through the signed32 "
                + "checkInt: "
                + arrJava.lines().filter(l -> l.contains("__intArrayWrite"))
                .findFirst().orElse("<missing>"));

        String fieldSource = """
            import * as time from "std/time"
            export class C {
              f: int = 0;
            }
            export function main(): null { return null; }
            export function test(): int {
              let c: C = {f: time.nowMillis()};
              return c.f;
            }
            """;
        ExecResult field = runInt32Project(fieldSource, "class_field_boundary");
        check(field.exitCode() == 1, "int32 class field boundary run exits 1: "
            + field.output());
        check(countOccurrences(field.output(),
                "DEAL_ERROR_CODE: E8004 int out of safe range") == 1,
            "class int-field construction boundary raises exactly E8004 "
                + "once: " + field.output());
        String fieldJava = int32Artifact(fieldSource, "class_field_artifact");
        check(fieldJava.contains("long __t0 = (java.lang.System.currentTimeMillis() / 1000L) * 1000L;"),
            "the class construction materializes the retained time "
                + "expression in its byte-identical long temp: "
                + fieldJava.lines().filter(l -> l.contains("__t0"))
                .findFirst().orElse("<missing>"));
        check(fieldJava.contains("new $C_C(checkInt(__t0))"),
            "the class int-field boundary routes through the signed32 "
                + "checkInt: "
                + fieldJava.lines().filter(l -> l.contains("new $C_C"))
                .findFirst().orElse("<missing>"));
        check(!fieldJava.contains("new $C_C((java.lang.System.currentTimeMillis() / 1000L)"),
            "no bare long pass-through at the class int-field boundary");

        // Legacy controls: the default invocation keeps the
        // byte-identical unwrapped retained expression and the programs
        // run green.
        ExecResult legacyArr = runLegacyProject(arraySource,
            "array_element_boundary_legacy");
        check(legacyArr.exitCode() == 0,
            "legacy array element write runs green (no int32 gate): "
                + legacyArr.output());
        ExecResult legacyField = runLegacyProject(fieldSource,
            "class_field_boundary_legacy");
        check(legacyField.exitCode() == 0,
            "legacy class field boundary runs green (no int32 gate): "
                + legacyField.output());
    }

    /** The {@code numPow} helper-collision guard (review-cycle-1
     * defect): the v1.2-only emitted helper
     * {@code static double numPow(double, double)} is registered in the
     * int32 runtime-helper signature table, so a valid DEAL v1.2 module
     * declaring its own {@code numPow(number, number): number} is
     * rejected with E6000 at codegen — never a compiler-success report
     * followed by a javac-rejected duplicate method. */
    private static void testInt32NumPowHelperCollision() throws Exception {
        System.out.println("-- Int32 numPow helper collision → E6000 --");

        String collision = """
            function numPow(a: number, b: number): number { return a; }
            export function main(): null { return null; }
            export function test(): number { return numPow(7.0, 1.0); }
            """;

        // Direct generate pin under DEAL_V1_2_INT32 (the review
        // reproduction): the guard fires, the user body is skipped, and
        // the artifact keeps exactly the one emitted IEEE helper.
        Frontend f = compileFrontend(collision,
            "jvmtest-numpow-collision.deal");
        check(f.errors().isEmpty(), "numPow collision frontend clean: "
            + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-numpow-collision.deal",
                "main", Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors(),
                "numPow collision is rejected under DEAL_V1_2_INT32: "
                    + res.diagnostics());
            check(res.diagnostics().stream().anyMatch(d ->
                    "E6000".equals(d.code())
                        && d.message().contains("collides with the emitted "
                            + "runtime helper 'numPow'")),
                "numPow collision E6000 names the emitted helper: "
                    + res.diagnostics());
            check(countOccurrences(res.source(), "static double numPow") == 1,
                "the rejected artifact keeps exactly the one emitted "
                    + "numPow helper (the user body is skipped, no "
                    + "duplicate javac would reject)");
        }

        // Full-pipeline pin: the orchestrator under the real int32
        // invocation rejects the module and records/writes no artifact —
        // javac never sees the duplicate numPow(double, double).
        writeFile("src/i32_numpow_collision.deal", collision);
        Path entryFile = tmpDir.get()
            .resolve("src/i32_numpow_collision.deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/i32_numpow_collision");
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilerInvocation invocation = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, null, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean ok = orchestrator.compile();
        check(!ok, "int32 orchestrator rejects the numPow collision");
        check(orchestrator.diagnostics().stream().anyMatch(d ->
                "E6000".equals(d.code())
                    && d.message().contains("collides with the emitted "
                        + "runtime helper 'numPow'")),
            "orchestrator reports the numPow helper collision: "
                + orchestrator.diagnostics());
        check(!orchestrator.jvmGeneratedResults()
                .containsKey(entryFile.toString()),
            "no generated result recorded for the rejected module");
        // Transactional publication (whole-project-artifact-publication
        // D3/D4): the rejection fails the whole compilation, so nothing
        // is published — the live root does not exist at all.
        check(!Files.exists(outputRoot),
            "the rejected module published no live root at all "
                + "(transactional whole-set contract)");
        if (Files.exists(outputRoot)) {
            try (var stream = Files.list(outputRoot)) {
                check(stream.noneMatch(p -> p.getFileName().toString()
                        .endsWith(".java")),
                    "the rejected module wrote no Java artifact (javac never "
                        + "sees a duplicate numPow)");
            }
        }

        // Parity control: the analogous numMod declaration hits the
        // pre-existing guard — numPow is now registered identically.
        Frontend fm = compileFrontend("""
            function numMod(a: number, b: number): number { return a; }
            export function main(): null { return null; }
            export function test(): number { return numMod(7.0, 1.0); }
            """, "jvmtest-nummod-collision.deal");
        check(fm.errors().isEmpty(), "numMod collision frontend clean: "
            + fm.errors());
        if (fm.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                fm.program(), fm.checkResult(), "jvmtest-nummod-collision.deal",
                "main", Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("collides with the emitted "
                            + "runtime helper 'numMod'")),
                "numMod collision keeps its E6000 guard: "
                    + res.diagnostics());
        }

        // Legacy negative controls: under LEGACY_SAFE_INT no numPow
        // helper is emitted, so the same declaration is not rejected —
        // the guard is profile-gated and the legacy surface stays
        // byte-identical.
        String legacyJava = legacyArtifact(collision, "numpow_collision");
        check(legacyJava.contains("static double numPow(double a, double b) {"),
            "legacy artifact emits the user numPow body (no helper guard "
                + "in legacy mode)");
        check(!legacyJava.contains("isNaN(b)) return 1.0"),
            "no IEEE numPow helper leaks into the legacy artifact");
        ExecResult legacy = runLegacyProject(collision, "numpow_collision");
        check(legacy.exitCode() == 0 && legacy.output().contains("7.0"),
            "legacy numPow-named function compiles and runs (7.0): "
                + legacy.output());
    }

    /** Compiles and runs one real program through the full pipeline
     * under the supplied invocation (any closed purpose×profile
     * combination), asserting the recorded int32 mode and the all-LEGACY
     * route plan for the {@code COMMON_SHADOW + DEAL_V1_2_INT32 +
     * PRE_ACTIVATION} matrix before executing the artifact. */
    private static ExecResult runInvocationProject(String source, String name,
                                                   CompilerInvocation invocation)
            throws Exception {
        writeFile("src/inv_" + name + ".deal", source);
        Path entryFile = tmpDir.get().resolve("src/inv_" + name + ".deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/inv_" + name);
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, null, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean ok = orchestrator.compile();
        check(ok, "invocation orchestrator compile succeeds for " + name
            + ": " + orchestrator.diagnostics());
        if (!ok) return new ExecResult("", 1);
        JvmBackend.JvmCodegenResult res =
            orchestrator.jvmGeneratedResults().get(entryFile.toString());
        check(res != null && res.int32Mode(),
            "the v1.2 invocation plumbs the real stored int32 mode for "
                + name);
        RoutePlanResult routePlan = orchestrator.routePlan();
        check(routePlan != null && routePlan.plan() != null
                && routePlan.plan().entries().values().stream()
                    .allMatch(r -> r == ModuleRoute.LEGACY)
                && routePlan.plan().shadowModules().isEmpty(),
            "the invocation routes every implementation module LEGACY "
                + "with no shadow entries for " + name);
        if (res == null || !res.int32Mode()) return new ExecResult("", 1);
        Frontend f = compileFrontend(source, "inv_" + name + ".deal");
        Files.writeString(outputRoot.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(f.program(),
                res.className()));
        List<String> javaFiles = new ArrayList<>();
        try (var stream = Files.list(outputRoot)) {
            stream.filter(p -> p.toString().endsWith(".java"))
                  .sorted()
                  .forEach(p -> javaFiles.add(p.getFileName().toString()));
        }
        StringBuilder javacErr = new StringBuilder();
        boolean javacOk = StubModuleResolver.compileWithJavac(outputRoot,
            javaFiles, javacErr);
        if (!javacOk) {
            throw new RuntimeException("javac failed for " + name + ": "
                + javacErr);
        }
        ProcessBuilder java = new ProcessBuilder("java", "-cp",
            outputRoot.toString(), "JvmConformanceRunner");
        java.redirectErrorStream(true);
        Process p2 = java.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        return new ExecResult(out, exit);
    }

    // =========================================================================
    // ISSUE-0158 v1.2 bytes lane (int32-bytes): helpers, emission, behavior
    // =========================================================================

    /**
     * The v1.2 bytes lane on the JVM backend (ISSUE-0158,
     * deal-v1.2-int32-and-bytes-architecture D3/D4): the emitted
     * artifact carries the four bytes helpers over the shared
     * {@code $DealRt.Bytes} byte[] carrier, and the real pipeline
     * (orchestrator → JvmBackend → javac → java under
     * DEAL_V1_2_INT32) executes the pinned helper contract: fresh
     * zero-filled allocation, the immutable signed-int32 {@code length},
     * unsigned 0..255 reads, exactly-one-byte writes with the returned
     * value, E8012 negative length / bounds (no append), E8013 value
     * range, reference aliasing/identity, per-instance class-field
     * isolation, and receiver/index/RHS single-evaluation order with
     * validation after the RHS and no storage change on a failed write.
     * The default (legacy) invocation compiles the same lane with the
     * profile-matched long index/value/result carriers (the E8012/E8013
     * gates before the narrowing) and must produce a javac-compiling,
     * correctly executing artifact too — never a long-into-int javac
     * rejection.
     */
    private static void testBytesRuntimeLane() throws Exception {
        System.out.println("-- v1.2 bytes runtime lane (ISSUE-0158) --");

        // ---- Emitted helper surface (int32 artifact inspection) ----
        String artifact = int32Artifact("""
            export function main(): null { return null; }
            export function run(): int {
              let b: bytes = bytes(1);
              return b.length;
            }
            """, "bytes_helpers_artifact");
        check(artifact.contains("static $DealRt.Bytes bytesNew(long length)"),
            "artifact emits bytesNew over the shared carrier");
        check(artifact.contains(
                "if (n < 0L) throw new DealError(\"E8012\", "
                    + "\"bytes length must be non-negative\", oFile, oLine, oCol)"),
            "bytesNew pins the E8012 negative-length gate");
        check(artifact.contains("static int bytesLength($DealRt.Bytes b)"),
            "artifact emits bytesLength");
        check(artifact.contains("return b.data[i] & 0xFF;"),
            "bytesGet returns the unsigned 0..255 byte");
        check(artifact.contains(
                "if (v < 0 || v > 255) throw new DealError(\"E8013\", "
                    + "\"bytes value out of range\", oFile, oLine, oCol)"),
            "bytesSet pins the E8013 value-range gate");
        check(artifact.contains(
                "if (i < 0 || i >= b.data.length) throw new DealError("
                    + "\"E8012\", \"bytes index out of bounds\", oFile, oLine, oCol)"),
            "bytesGet/bytesSet pin the E8012 bounds gate (never appends)");
        check(artifact.contains("bytesNew(") && artifact.contains(
                "bytesLength(") && artifact.contains("bytesGet(")
                && artifact.contains("bytesSet("),
            "the intrinsic call, .length, and index read/write lower to "
                + "the emitted helpers");

        // ---- Behavior battery (real pipeline under DEAL_V1_2_INT32) ----
        // prelude: module-level declarations (classes/helper functions)
        // spliced between main and the pinned test body — DEAL v1.2
        // module top level holds only declarations.
        record BytesPin(String name, String prelude, String body,
                        String expected) {}
        List<BytesPin> pins = List.of(
            new BytesPin("alloc-zero-fill", "",
                "let b: bytes = bytes(4);\n"
                    + "      if (b.length !== 4) { throw { code: \"TEST_FAIL\", message: \"length\" }; }\n"
                    + "      if (b[0] !== 0 || b[1] !== 0 || b[2] !== 0 || b[3] !== 0) { throw { code: \"TEST_FAIL\", message: \"zero fill\" }; }\n"
                    + "      return 1;",
                "1"),
            new BytesPin("unsigned-read-write", "",
                "let b: bytes = bytes(2);\n"
                    + "      b[0] = 255;\n"
                    + "      b[1] = 128;\n"
                    + "      let hi: int = b[0];\n"
                    + "      let lo: int = b[1];\n"
                    + "      if (hi !== 255 || lo !== 128) { throw { code: \"TEST_FAIL\", message: \"unsigned roundtrip\" }; }\n"
                    + "      return hi - lo;",
                "127"),
            new BytesPin("write-returns-value", "",
                "let b: bytes = bytes(1);\n"
                    + "      let v: int = (b[0] = 200);\n"
                    + "      return v;",
                "200"),
            new BytesPin("empty-buffer", "",
                "let b: bytes = bytes(0);\n"
                    + "      if (b.length !== 0) { throw { code: \"TEST_FAIL\", message: \"empty length\" }; }\n"
                    + "      return 0;",
                "0"),
            new BytesPin("empty-read-bounds", "",
                "let b: bytes = bytes(0);\n"
                    + "      return b[0];",
                "E8012"),
            new BytesPin("empty-write-bounds", "",
                "let b: bytes = bytes(0);\n"
                    + "      b[0] = 1;\n"
                    + "      return 0;",
                "E8012"),
            new BytesPin("negative-length", "",
                "let b: bytes = bytes(-1);\n"
                    + "      return 0;",
                "E8012"),
            new BytesPin("read-bounds-high", "",
                "let b: bytes = bytes(4);\n"
                    + "      return b[4];",
                "E8012"),
            new BytesPin("read-bounds-low", "",
                "let b: bytes = bytes(4);\n"
                    + "      return b[-1];",
                "E8012"),
            new BytesPin("write-bounds-high-no-append", "",
                "let b: bytes = bytes(2);\n"
                    + "      b[2] = 7;\n"
                    + "      return 0;",
                "E8012"),
            new BytesPin("write-bounds-low", "",
                "let b: bytes = bytes(2);\n"
                    + "      b[-1] = 7;\n"
                    + "      return 0;",
                "E8012"),
            new BytesPin("write-value-high", "",
                "let b: bytes = bytes(1);\n"
                    + "      b[0] = 256;\n"
                    + "      return 0;",
                "E8013"),
            new BytesPin("write-value-low", "",
                "let b: bytes = bytes(1);\n"
                    + "      b[0] = -1;\n"
                    + "      return 0;",
                "E8013"),
            new BytesPin("alias-mutation", "",
                "let b: bytes = bytes(4);\n"
                    + "      let alias: bytes = b;\n"
                    + "      alias[2] = 7;\n"
                    + "      return b[2];",
                "7"),
            new BytesPin("identity-alias-eq", "",
                "let a: bytes = bytes(2);\n"
                    + "      let b: bytes = a;\n"
                    + "      if (!(a === b)) { throw { code: \"TEST_FAIL\", message: \"alias identity\" }; }\n"
                    + "      return 1;",
                "1"),
            new BytesPin("identity-distinct-ne", "",
                "let a: bytes = bytes(2);\n"
                    + "      let c: bytes = bytes(2);\n"
                    + "      if (a === c) { throw { code: \"TEST_FAIL\", message: \"distinct buffers\" }; }\n"
                    + "      if (!(a !== c)) { throw { code: \"TEST_FAIL\", message: \"distinct ne\" }; }\n"
                    + "      return 1;",
                "1"),
            new BytesPin("identity-nullable-vs-null", "",
                "let n: bytes | null = null;\n"
                    + "      if (!(n === null)) { throw { code: \"TEST_FAIL\", message: \"null eq\" }; }\n"
                    + "      if (n !== null) { throw { code: \"TEST_FAIL\", message: \"null ne\" }; }\n"
                    + "      let m: bytes | null = bytes(1);\n"
                    + "      if (m === null) { throw { code: \"TEST_FAIL\", message: \"value eq\" }; }\n"
                    + "      if (!(m !== null)) { throw { code: \"TEST_FAIL\", message: \"value ne\" }; }\n"
                    + "      if (!(null === n)) { throw { code: \"TEST_FAIL\", message: \"null right\" }; }\n"
                    + "      return 1;",
                "1"),
            new BytesPin("identity-nullable-pair", "",
                "let a: bytes | null = bytes(1);\n"
                    + "      let b: bytes | null = a;\n"
                    + "      if (!(a === b)) { throw { code: \"TEST_FAIL\", message: \"pair eq\" }; }\n"
                    + "      let c: bytes | null = bytes(1);\n"
                    + "      if (a === c) { throw { code: \"TEST_FAIL\", message: \"pair distinct\" }; }\n"
                    + "      return 1;",
                "1"),
            new BytesPin("fresh-instances", "",
                "let a: bytes = bytes(2);\n"
                    + "      let c: bytes = bytes(2);\n"
                    + "      a[0] = 9;\n"
                    + "      return c[0];",
                "0"),
            new BytesPin("fn-param-return", "",
                "function first(b: bytes): int { return b[0]; }\n"
                    + "      function fill(b: bytes, v: int): bytes { b[0] = v; return b; }\n"
                    + "      let x: bytes = fill(bytes(3), 200);\n"
                    + "      return first(x) + x.length;",
                "203"),
            new BytesPin("eval-order",
                "class Log {\n"
                    + "  seq: int[] = [];\n"
                    + "  buf: bytes = bytes(4);\n"
                    + "}\n"
                    + "function record(l: Log, tag: int): int { l.seq[l.seq.length] = tag; return tag; }\n"
                    + "function pick(l: Log, tag: int): bytes { record(l, tag); return l.buf; }\n",
                "let l: Log = { seq: [], buf: bytes(4) };\n"
                    + "      pick(l, 1)[record(l, 2)] = record(l, 3);\n"
                    + "      if (l.seq.length !== 3 || l.seq[0] !== 1 || l.seq[1] !== 2 || l.seq[2] !== 3) { throw { code: \"TEST_FAIL\", message: \"order\" }; }\n"
                    + "      return l.buf[2];",
                "3"),
            new BytesPin("failed-write-nonmutation",
                "class Log {\n"
                    + "  seq: int[] = [];\n"
                    + "  buf: bytes = bytes(4);\n"
                    + "}\n"
                    + "function record(l: Log, tag: int): int { l.seq[l.seq.length] = tag; return tag; }\n"
                    + "function pick(l: Log, tag: int): bytes { record(l, tag); return l.buf; }\n"
                    + "function badValue(l: Log): int { record(l, 3); return 300; }\n",
                "let l: Log = { seq: [], buf: bytes(4) };\n"
                    + "      try { pick(l, 1)[record(l, 2)] = badValue(l); throw { code: \"TEST_FAIL\", message: \"no E8013\" }; }\n"
                    + "      catch (e) { if (e.code !== \"E8013\") { throw e; } }\n"
                    + "      if (l.seq.length !== 3 || l.seq[0] !== 1 || l.seq[1] !== 2 || l.seq[2] !== 3) { throw { code: \"TEST_FAIL\", message: \"side effects\" }; }\n"
                    + "      if (l.buf[1] !== 0) { throw { code: \"TEST_FAIL\", message: \"storage changed\" }; }\n"
                    + "      return 0;",
                "0"),
            new BytesPin("class-field-isolation",
                "class Payload {\n"
                    + "  data: bytes = bytes(2);\n"
                    + "  tag: string = \"\";\n"
                    + "}\n",
                "let p: Payload = { data: bytes(3), tag: \"a\" };\n"
                    + "      p.data[1] = 200;\n"
                    + "      let q: Payload = { data: bytes(1), tag: \"b\" };\n"
                    + "      if (q.data.length !== 1) { throw { code: \"TEST_FAIL\", message: \"second length\" }; }\n"
                    + "      if (p.data[1] !== 200) { throw { code: \"TEST_FAIL\", message: \"shared storage\" }; }\n"
                    + "      return p.data.length;",
                "3"),
            new BytesPin("length-int-arithmetic", "",
                "let b: bytes = bytes(3);\n"
                    + "      let l: int = b.length;\n"
                    + "      return l * 2 + 1;",
                "7"));
        for (BytesPin pin : pins) {
            String source = "export function main(): null { return null; }\n"
                + pin.prelude()
                + "export function test(): int {\n      " + pin.body() + "\n"
                + "    }\n";
            ExecResult r = runInt32Project(source, pin.name());
            if (pin.expected().startsWith("E8")) {
                check(r.exitCode() == 1,
                    pin.name() + " run exits 1: " + r.output());
                check(r.output().contains("DEAL_ERROR_CODE: "
                        + pin.expected()),
                    pin.name() + " raises exactly " + pin.expected()
                        + ": " + r.output());
            } else {
                check(r.exitCode() == 0,
                    pin.name() + " run exits 0: " + r.output());
                check(r.output().contains(pin.expected()),
                    pin.name() + " computes the pinned value "
                        + pin.expected() + ": " + r.output());
            }
        }

        // ---- Legacy-profile pin (LEGACY_SAFE_INT long carriers) ----
        // The explicit legacy invocation (PRE_ACTIVATION →
        // LEGACY_SAFE_INT) compiles v1.2 bytes programs with the legacy
        // long int carrier. The emitted bytes helpers must follow the
        // same carrier — long index/value parameters with the E8012/E8013
        // gates before the narrowing, and long results — so the artifact
        // compiles under javac and executes the pinned bytes semantics,
        // never the pre-fix long-into-int "possible lossy conversion"
        // artifact the review found.
        String legacyJava = legacyArtifact("""
            export function main(): null { return null; }
            export function run(): int {
              let b: bytes = bytes(1);
              return b.length;
            }
            """, "bytes_helpers_legacy_artifact");
        check(legacyJava.contains("static long bytesLength($DealRt.Bytes b)"),
            "legacy artifact emits the long-carrier bytesLength");
        check(legacyJava.contains(
                "static long bytesGet($DealRt.Bytes b, long i)"),
            "legacy artifact emits the long-carrier bytesGet");
        check(legacyJava.contains(
                "static long bytesSet($DealRt.Bytes b, long i, long v)"),
            "legacy artifact emits the long-carrier bytesSet");
        check(legacyJava.contains("b.data[(int) i]"),
            "legacy bytesGet/bytesSet narrow the index only after the "
                + "E8012 bounds gate");

        // The real legacy-invocation pipeline (orchestrator →
        // JvmBackend → javac → java): runLegacyProject compiles every
        // emitted artifact with javac and throws on any javac error, so
        // a green run is also a javac-compiling-artifact pin.
        ExecResult legacyRun = runLegacyProject("""
            export function main(): null { return null; }
            export function test(): int {
              let b: bytes = bytes(3);
              b[0] = 255;
              b[1] = 128;
              let alias: bytes = b;
              alias[2] = 7;
              if (b.length !== 3) { throw { code: "TEST_FAIL", message: "length" }; }
              if (b[0] !== 255 || b[1] !== 128 || b[2] !== 7) { throw { code: "TEST_FAIL", message: "roundtrip" }; }
              if (!(alias === b)) { throw { code: "TEST_FAIL", message: "identity" }; }
              return b[0] + b[1] + b[2];
            }
            """, "bytes_legacy_full");
        check(legacyRun.exitCode() == 0,
            "legacy bytes program compiles under javac and runs green: "
                + legacyRun.output());
        check(legacyRun.output().contains("390"),
            "legacy bytes program computes 255 + 128 + 7 = 390 with "
                + "unsigned reads through the long carriers: "
                + legacyRun.output());
        ExecResult legacyValue = runLegacyProject("""
            export function main(): null { return null; }
            export function test(): int {
              let b: bytes = bytes(1);
              b[0] = 300;
              return 0;
            }
            """, "bytes_legacy_e8013");
        check(legacyValue.exitCode() == 1
                && legacyValue.output().contains("DEAL_ERROR_CODE: E8013"),
            "legacy bytes value-range gate raises exactly E8013: "
                + legacyValue.output());
        ExecResult legacyBounds = runLegacyProject("""
            export function main(): null { return null; }
            export function test(): int { return bytes(1)[1]; }
            """, "bytes_legacy_e8012");
        check(legacyBounds.exitCode() == 1
                && legacyBounds.output().contains("DEAL_ERROR_CODE: E8012"),
            "legacy bytes bounds gate raises exactly E8012: "
                + legacyBounds.output());

        // The legacy collision table registers the long-carrier helper
        // signatures: a user function named bytesGet whose legacy-mapped
        // parameters equal the emitted legacy helper is rejected with
        // E6000 before emission — never a duplicate Java method.
        Frontend legacyCollision = compileFrontend("""
            function bytesGet(b: bytes, i: int): int { return b[i]; }
            export function main(): null { return null; }
            export function test(): int { return bytesGet(bytes(1), 0); }
            """, "jvmtest-bytesget-legacy-collision.deal");
        check(legacyCollision.errors().isEmpty(),
            "legacy bytesGet collision frontend clean: "
                + legacyCollision.errors());
        if (legacyCollision.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult collisionRes = JvmBackend.generate(
                legacyCollision.program(), legacyCollision.checkResult(),
                "jvmtest-bytesget-legacy-collision.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.LEGACY_SAFE_INT);
            check(collisionRes.hasErrors() && collisionRes.diagnostics()
                    .stream().anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("collides with the emitted "
                            + "runtime helper 'bytesGet'")),
                "legacy bytesGet-named function collides with the "
                    + "long-carrier legacy helper (E6000, never a "
                    + "duplicate Java method): "
                    + collisionRes.diagnostics());
        }
    }

    /** The recursive bytes-bearing type closure (ISSUE-0160/E8, consumed
     * by ISSUE-0306): arbitrary-depth Array/Nullable bytes compositions,
     * sync/async bytes-bearing function signatures, the shared
     * __BytesArray/__BytesOrNullArray carriers, the [bytes]/[?bytes]
     * $checkArray rows, the pinned JSON bytes rejection, and the host
     * bytes ABI arms — all through the real emitted artifact surface. */
    private static void testRecursiveBytesClosureLane() throws Exception {
        System.out.println("-- Recursive bytes-bearing type closure (ISSUE-0160) --");

        // ---- Emitted artifact surface (int32 artifact inspection) ----
        String artifact = int32Artifact("""
            // @jsonable
            export class Holder { payload: table = {}; }
            function id(b: bytes): bytes { return b; }
            async function echo(b: bytes): bytes { return b; }
            function bump(b: bytes, v: int): bytes { b[0] = b[0] + v; return b; }
            function picker(): (b: bytes) => bytes { return id; }
            function combine(f: (b: bytes) => bytes): (b: bytes) => bytes {
              return f;
            }
            class Box {
              cb: (b: bytes) => bytes = id;
              both: (b: bytes, v: int) => bytes = bump;
              maybe: ((b: bytes) => bytes) | null = null;
            }
            export function main(): null { return null; }
            export function run(): int {
              let b: bytes = bytes(2);
              let xs: bytes[] = [b];
              let ns: (bytes | null)[] = [];
              let fs: ((b: bytes) => bytes)[] = [id];
              let g: async (b: bytes) => bytes = echo;
              let t: table = {};
              t.x = b;
              let c: bytes = t.x;
              let d: bytes | null = t.x;
              let box: Box = {};
              let via: bytes = box.cb(bytes(1));
              return xs[0][0] + b.length + via.length;
            }
            """, "bytes_closure_artifact");
        check(artifact.contains(
                "static final class __BytesArray { Bytes[] data; "
                    + "__BytesArray(Bytes[] data) { this.data = data; } }"),
            "the shared scope carries the concrete __BytesArray carrier "
                + "over $DealRt.Bytes[] storage");
        check(artifact.contains(
                "static final class __BytesOrNullArray { Bytes[] data; "
                    + "__BytesOrNullArray(Bytes[] data) { this.data = data; } }"),
            "the shared scope carries the concrete __BytesOrNullArray "
                + "carrier");
        check(artifact.contains("static $DealRt.Bytes __bytesArrayRead("),
            "bytes[] reads lower to the typed __bytesArrayRead helper");
        check(artifact.contains("static $DealRt.Bytes __bytesArrayWrite("),
            "bytes[] writes lower to the typed __bytesArrayWrite helper");
        check(artifact.contains("static $DealRt.Bytes __bytesArrayReadBoxed("),
            "the boxed bytes[] read supports === / !== nil semantics");
        check(artifact.contains(
                "static $DealRt.Bytes __bytesOrNullArrayRead("),
            "(bytes | null)[] reads lower to the or-null helper");
        check(artifact.contains(
                "static $DealRt.Bytes __bytesOrNullArrayWrite("),
            "(bytes | null)[] writes lower to the or-null helper");
        check(artifact.contains(
                "\"expected bytes, got \" + $describe(v)"),
            "the bytes[] element policy rejects a null element with the "
                + "pinned E8001 shape");
        check(artifact.contains("descriptor.equals(\"[bytes]\")"),
            "the $checkArray seam carries the [bytes] row");
        check(artifact.contains("descriptor.equals(\"[?bytes]\")"),
            "the $checkArray seam carries the [?bytes] widening row");
        check(artifact.contains("static $DealRt.__BytesArray $dynamicBytesArray("),
            "an array-mode table converts through $dynamicBytesArray "
                + "with the E8003 element wrap");
        check(artifact.contains(
                "static $DealRt.__BytesOrNullArray $dynamicBytesOrNullArray("),
            "an array-mode table converts through $dynamicBytesOrNullArray");
        check(artifact.contains("static abstract class Fn1_Y_R_Y"),
            "(bytes)->bytes uses the shared Y-segment wrapper shape");
        check(artifact.contains(
                "static abstract class Fn1_Y_R_Y implements FnValue {\n"
                    + "        final java.lang.String descriptor = "
                    + "\"(bytes)->bytes\";"),
            "the (bytes)->bytes wrapper carries the complete canonical "
                + "descriptor text (bytes)->bytes");
        check(artifact.contains("static abstract class FnA1_Y_R_Y"),
            "async(bytes)->bytes uses the distinct async wrapper shape");
        check(artifact.contains(
                "final java.lang.String descriptor = \"async(bytes)->bytes\";"),
            "the async bytes wrapper carries the complete canonical "
                + "async(bytes)->bytes descriptor");
        check(artifact.contains("static abstract class Fn2_Y_I_R_Y"),
            "(bytes,int)->bytes uses the two-parameter Y-segment wrapper "
                + "shape (ISSUE-0548 sync function-shape closure)");
        check(artifact.contains(
                "static abstract class Fn2_Y_I_R_Y implements FnValue {\n"
                    + "        final java.lang.String descriptor = "
                    + "\"(bytes,int)->bytes\";"),
            "the (bytes,int)->bytes wrapper carries the complete "
                + "canonical descriptor text (bytes,int)->bytes");
        check(artifact.contains(
                "static abstract class Fn0_R_$$lbytes$r$m$gbytes "
                    + "implements FnValue {"),
            "()->(bytes)->bytes uses the descriptor-escaped nested "
                + "function shape id");
        check(artifact.contains(
                "        final java.lang.String descriptor = "
                    + "\"()->(bytes)->bytes\";"),
            "the ()->(bytes)->bytes wrapper carries the complete "
                + "canonical descriptor text ()->(bytes)->bytes");
        check(artifact.contains(
                "static abstract class "
                    + "Fn1_$$lbytes$r$m$gbytes_R_$$lbytes$r$m$gbytes "
                    + "implements FnValue {"),
            "((bytes)->bytes)->(bytes)->bytes uses the descriptor-escaped "
                + "nested function shape id");
        check(artifact.contains(
                "        final java.lang.String descriptor = "
                    + "\"((bytes)->bytes)->(bytes)->bytes\";"),
            "the ((bytes)->bytes)->(bytes)->bytes wrapper carries the "
                + "complete canonical descriptor text");
        check(artifact.contains("$DealRt.Fn1_Y_R_Y cb;"),
            "a plain class field of bytes-bearing function type stores "
                + "the shared wrapper reference");
        check(artifact.contains("$DealRt.Fn2_Y_I_R_Y both;"),
            "a two-parameter class field of bytes-bearing function "
                + "type stores the shared wrapper reference");
        check(artifact.contains("$DealRt.Fn1_Y_R_Y maybe;"),
            "a nullable class field of bytes-bearing function type "
                + "stores the shared wrapper reference (Java null is "
                + "the DEAL null)");
        check(artifact.contains(
                "$DealRt.Fn1_Y_R_Y __fn0 = (box).cb;"),
            "a call through a class field holding a bytes-bearing "
                + "function value materializes the callee FIELD READ "
                + "into a wrapper temporary at the callee's evaluation "
                + "position");
        check(artifact.contains("$DealRt.Bytes via = __fn0.invokeAt("),
            "the call through the class field dispatches through the "
                + "materialized wrapper temporary's invokeAt with the "
                + "call-site origin");
        check(!artifact.contains(
                "if (v instanceof $DealRt.Bytes) throw new DealError("
                    + "\"E8001\", \"unsupported type for JSON encoding: "
                    + "bytes\")"),
            "the stringifier carries no bytes-specific arm (the "
                + "unsupported-type message belongs to the std/json "
                + "stringify surface's encode_value-parity default arm, "
                + "not the @jsonable one)");
        check(artifact.contains(
                "static $DealRt.Table __jsonShape($DealRt.Table v) {"),
            "the @jsonable runtime emits the __jsonShape table-field "
                + "validation helper (deal/runtime.lua's "
                + "_json_table_shape mirror)");
        check(artifact.contains(
                "throw new DealError(\"E8001\", \"value is not "
                    + "JSON-shaped\", oFile, oLine, oCol);"),
            "the @jsonable shape walk raises the LuaJIT-equal "
                + "'value is not JSON-shaped' for a bytes value");
        check(artifact.contains("case \"bytes\":")
                && artifact.contains(
                    "if (v instanceof $DealRt.Bytes b) return b;"),
            "__hostCheck carries the bytes return-boundary branch");

        check(artifact.contains("(($DealRt.Bytes) $check(\"bytes\", "),
            "a bytes-typed table read lowers through the canonical "
                + "$check bytes row");
        check(artifact.contains("(($DealRt.Bytes) $check(\"?bytes\", "),
            "a (bytes | null) table read lowers through the canonical "
                + "$check ?bytes row");

        // ---- Behavior battery (real pipeline under DEAL_V1_2_INT32) ----
        record ClosurePin(String name, String prelude, String body,
                          String expected) {}
        List<ClosurePin> pins = List.of(
            new ClosurePin("nested-alias", "",
                "let b: bytes = bytes(2);\n"
                    + "      let xs: bytes[][] = [[b]];\n"
                    + "      xs[0][0][0] = 7;\n"
                    + "      if (b[0] !== 7) { throw { code: \"TEST_FAIL\", message: \"alias\" }; }\n"
                    + "      return b[0];",
                "7"),
            new ClosurePin("nested-read-write", "",
                "let xs: bytes[][] = [[bytes(1)], [bytes(2)]];\n"
                    + "      xs[1][0][0] = 9;\n"
                    + "      return xs[0][0][0] + xs[1][0][0];",
                "9"),
            new ClosurePin("nullable-elements", "",
                "let ns: (bytes | null)[] = [];\n"
                    + "      ns[ns.length] = bytes(1);\n"
                    + "      ns[ns.length] = null;\n"
                    + "      let first: bytes | null = ns[0];\n"
                    + "      if (first !== null) { first[0] = 9; }\n"
                    + "      if (ns[1] !== null) { throw { code: \"TEST_FAIL\", message: \"null element\" }; }\n"
                    + "      let again: bytes | null = ns[0];\n"
                    + "      if (again !== null) {\n"
                    + "        if (again[0] !== 9) { throw { code: \"TEST_FAIL\", message: \"write\" }; }\n"
                    + "        return again[0];\n"
                    + "      }\n"
                    + "      throw { code: \"TEST_FAIL\", message: \"lost element\" };",
                "9"),
            new ClosurePin("fn-array-invoke",
                "function bump(b: bytes, v: int): bytes { b[0] = b[0] + v; return b; }\n",
                "let fs: ((b: bytes, v: int) => bytes)[] = [bump, bump];\n"
                    + "      fs[fs.length] = bump;\n"
                    + "      let r: bytes = fs[0](bytes(2), 5);\n"
                    + "      return r[0];",
                "5"),
            new ClosurePin("fn-array-nullable",
                "function id(b: bytes): bytes { return b; }\n",
                "let ns: (((b: bytes) => bytes) | null)[] = [];\n"
                    + "      ns[ns.length] = id;\n"
                    + "      ns[ns.length] = null;\n"
                    + "      let g: ((b: bytes) => bytes) | null = ns[0];\n"
                    + "      if (g !== null) { return g(bytes(3)).length; }\n"
                    + "      throw { code: \"TEST_FAIL\", message: \"nullable fn\" };",
                "3"),
            new ClosurePin("array-identity",
                "function id(b: bytes): bytes { return b; }\n",
                "let b: bytes = bytes(2);\n"
                    + "      let xs: bytes[] = [b];\n"
                    + "      let copy: bytes[] = [bytes(2)];\n"
                    + "      if (!(xs[0] === b)) { throw { code: \"TEST_FAIL\", message: \"element identity\" }; }\n"
                    + "      if (xs === copy) { throw { code: \"TEST_FAIL\", message: \"array identity\" }; }\n"
                    + "      return 1;",
                "1"),
            new ClosurePin("past-end-read", "",
                "let xs: bytes[] = [];\n"
                    + "      return xs[0][0];",
                "E8001"),
            new ClosurePin("callee-first-field-read",
                "function markOne(b: bytes | null): bytes { if (b !== null) { b[0] = 1; return b; } return bytes(0); }\n"
                    + "    function markTwo(b: bytes | null): bytes { if (b !== null) { b[0] = 2; return b; } return bytes(0); }\n"
                    + "    class Box { cb: (b: bytes | null) => bytes = markOne; }\n"
                    + "    function retarget(box: Box): table { box.cb = markTwo; return { x: bytes(1) }; }\n",
                "let box: Box = {};\n"
                    + "      let r: bytes = box.cb(retarget(box).x);\n"
                    + "      if (r[0] !== 1) { throw { code: \"TEST_FAIL\", message: \"callee-first field read\" }; }\n"
                    + "      return r[0];",
                "1"),
            new ClosurePin("json-rejection",
                "// @jsonable\nexport class Holder { payload: table = {}; }\n",
                "let h: Holder = { payload: { inner: {} } };\n"
                    + "      h.payload.inner.b = bytes(2);\n"
                    + "      let s: string = Holder$toJson(h);\n"
                    + "      return 0;",
                "E8001"));
        for (ClosurePin pin : pins) {
            String source = "export function main(): null { return null; }\n"
                + pin.prelude()
                + "export function test(): int {\n      " + pin.body() + "\n"
                + "    }\n";
            ExecResult r = runInt32Project(source, pin.name());
            if (pin.expected().startsWith("E8")) {
                check(r.exitCode() == 1,
                    pin.name() + " run exits 1: " + r.output());
                check(r.output().contains("DEAL_ERROR_CODE: "
                        + pin.expected()),
                    pin.name() + " raises exactly " + pin.expected()
                        + ": " + r.output());
            } else {
                check(r.exitCode() == 0,
                    pin.name() + " run exits 0: " + r.output());
                check(r.output().contains(pin.expected()),
                    pin.name() + " computes the pinned value "
                        + pin.expected() + ": " + r.output());
            }
        }
        check(pins.stream().anyMatch(p ->
                p.name().equals("json-rejection")),
            "the JSON rejection pin ran");

        // Async bytes-bearing function values (await needs an async test
        // function, so these run as standalone sources).
        ExecResult asyncBytes = runInt32Project("""
            async function echo(b: bytes): bytes { return b; }
            export function main(): null { return null; }
            export async function test(): int {
              let f: async (b: bytes) => bytes = echo;
              let out: bytes = await f(bytes(2));
              return out.length;
            }
            """, "async_bytes_value");
        check(asyncBytes.exitCode() == 0,
            "async bytes function value run exits 0: " + asyncBytes.output());
        check(asyncBytes.output().contains("2"),
            "awaited async bytes function value completes with length 2: "
                + asyncBytes.output());
        ExecResult asyncContainer = runInt32Project("""
            async function echo(b: bytes): bytes { return b; }
            export function main(): null { return null; }
            export async function test(): int {
              let fs: ((async (b: bytes) => bytes) | null)[] = [];
              fs[fs.length] = echo;
              fs[fs.length] = null;
              let g: (async (b: bytes) => bytes) | null = fs[0];
              if (g !== null) {
                let again: bytes = await g(bytes(3));
                return again[0];
              }
              throw { code: "TEST_FAIL", message: "async container" };
            }
            """, "async_bytes_container");
        check(asyncContainer.exitCode() == 0,
            "containerized async bytes value run exits 0: "
                + asyncContainer.output());
        check(asyncContainer.output().contains("0"),
            "containerized async bytes value completes with the zero-filled "
                + "first byte: " + asyncContainer.output());
        // ISSUE-0549 (async bytes closure): function-typed class fields
        // hold async bytes-bearing wrapper references (the DEAL null for
        // the nullable form), direct member calls dispatch the field's
        // invoke through the await-site completion check, discard awaits
        // evaluate exactly once, awaited errors propagate, and bytes[]
        // signatures/callbacks flow through await.
        ExecResult asyncFieldCall = runInt32Project("""
            async function echo(b: bytes): bytes { return b; }
            export class Holder {
              cb: async (b: bytes) => bytes = echo;
              maybe: (async (b: bytes) => bytes) | null = null;
              n: int = 7;
            }
            export function main(): null { return null; }
            export async function test(): int {
              let h: Holder = { cb: echo, maybe: null, n: 9 };
              let via: bytes = await h.cb(bytes(5));
              let m: (async (b: bytes) => bytes) | null = h.maybe;
              if (m !== null) { throw { code: "TEST_FAIL", message: "null field" }; }
              h.maybe = echo;
              let m2: (async (b: bytes) => bytes) | null = h.maybe;
              if (m2 !== null) {
                let again: bytes = await m2(bytes(6));
                return via.length + h.n + again.length;
              }
              throw { code: "TEST_FAIL", message: "field write" };
            }
            """, "async_bytes_field_call");
        check(asyncFieldCall.exitCode() == 0,
            "async bytes class-field call run exits 0: "
                + asyncFieldCall.output());
        check(asyncFieldCall.output().contains("20"),
            "class fields hold the async bytes wrapper reference (5 + 9 + 6 "
                + "= 20) with the DEAL null default preserved: "
                + asyncFieldCall.output());
        ExecResult asyncClosureBattery = runInt32Project("""
            async function echo(b: bytes): bytes { return b; }
            async function countArr(a: bytes[]): int { return a.length; }
            async function applyBytes(f: async (b: bytes) => bytes, b: bytes): bytes {
              return await f(b);
            }
            async function failEcho(b: bytes): bytes {
              throw { code: "E_TEST", message: "boom" };
            }
            export function main(): null { return null; }
            export async function test(): int {
              let arr: bytes[] = [bytes(2), bytes(3)];
              let n: int = await countArr(arr);
              let via: bytes = await applyBytes(echo, bytes(4));
              let hits: int = 0;
              async function counter(b: bytes): bytes {
                hits = hits + 1;
                return b;
              }
              await counter(bytes(1));
              let caught: boolean = false;
              try {
                await failEcho(bytes(1));
              } catch (e) {
                caught = e.code === "E_TEST";
              }
              if (!caught) { throw { code: "TEST_FAIL", message: "propagate" }; }
              return n * 10 + via.length + hits;
            }
            """, "async_bytes_closure_battery");
        check(asyncClosureBattery.exitCode() == 0,
            "async bytes closure battery run exits 0: "
                + asyncClosureBattery.output());
        check(asyncClosureBattery.output().contains("25"),
            "bytes[] signature (2), callback (4), and exactly-once discard "
                + "await (1) complete through await: 2*10 + 4 + 1 = 25: "
                + asyncClosureBattery.output());
        // The @jsonable C$toJson surface validates table fields through
        // the emitted __jsonShape walk — deal/runtime.lua's
        // _json_table_shape mirror, before std/json's encode_value ever
        // runs — so a table-held bytes value raises E8001 "value is
        // not JSON-shaped", byte-identical to the LuaJIT @jsonable
        // reference. The std/json stringify surface (landed with
        // ISSUE-0302) keeps its own encode_value-parity arm — E8001
        // "unsupported type for JSON encoding: bytes" for the same
        // table — exactly like std/json.lua's explicit bytes arm, so
        // the two LuaJIT surfaces stay byte-distinct on the JVM.
        String jsonSource = "export function main(): null { return null; }\n"
            + "// @jsonable\nexport class Holder { payload: table = {}; }\n"
            + "export function test(): int {\n"
            + "      let h: Holder = { payload: { inner: {} } };\n"
            + "      h.payload.inner.b = bytes(2);\n"
            + "      let s: string = Holder$toJson(h);\n"
            + "      return 0;\n"
            + "    }\n";
        ExecResult jsonRun = runInt32Project(jsonSource, "json_rejection_msg");
        check(jsonRun.exitCode() == 1,
            "the bytes JSON rejection run exits 1: " + jsonRun.output());
        check(jsonRun.output().contains("DEAL_ERROR_CODE: E8001"),
            "the bytes JSON rejection raises E8001: " + jsonRun.output());
        check(jsonRun.output().contains("value is not JSON-shaped"),
            "the JVM stringifier raises the LuaJIT-equal default message: "
                + jsonRun.output());

        // The std/json stringify surface raises the encode_value-parity
        // message for the same table-held bytes value (std/json.lua's
        // explicit bytes arm) — the two JVM stringify surfaces stay
        // byte-distinct exactly like the LuaJIT reference runtime.
        ExecResult stdJsonBytes = compileAndRunJvm("""
            import * as json from "std/json"
            export function test(): string {
              let t: table = { inner: {} };
              t.inner.b = bytes(2);
              return json.stringify(t);
            }
            """, "std_json_stringify_bytes_msg");
        check(stdJsonBytes.output().contains("DEAL_ERROR_CODE: E8001"),
            "the std/json bytes stringify raises E8001: "
                + stdJsonBytes.output());
        check(stdJsonBytes.output().contains(
                "unsupported type for JSON encoding: bytes"),
            "the std/json stringify raises the encode_value-parity bytes "
                + "message: " + stdJsonBytes.output());

        // ISSUE-0551: a table-held typed bytes[] array reaches its
        // elements through the emitted __BytesArray/__BytesOrNullArray
        // serialization branches, so a bytes element raises the pinned
        // encode_value-parity bytes message — never the carrier's own
        // class name leaking into the error (LuaJIT walks the array and
        // rejects the element).
        ExecResult stdJsonBytesArray = compileAndRunJvm("""
            import * as json from "std/json"
            export function test(): string {
              let b: bytes = bytes(1);
              let arr: bytes[] = [b];
              let t: table = { inner: {} };
              t.inner.arr = arr;
              return json.stringify(t);
            }
            """, "std_json_stringify_bytes_array_msg");
        check(stdJsonBytesArray.output().contains("DEAL_ERROR_CODE: E8001"),
            "the std/json bytes-array stringify raises E8001: "
                + stdJsonBytesArray.output());
        check(stdJsonBytesArray.output().contains(
                "unsupported type for JSON encoding: bytes"),
            "the std/json stringify of a table-held bytes[] rejects the "
                + "element with the pinned bytes message: "
                + stdJsonBytesArray.output());
        check(!stdJsonBytesArray.output().contains("__BytesArray"),
            "no carrier class name leaks into the nested bytes rejection "
                + "message: " + stdJsonBytesArray.output());

        // ---- Dynamic scalar table-read boundary (ISSUE-0160 D5) ----
        // Table writes store the raw wrapper reference; a bytes-typed
        // read routes through the canonical $check realization — the
        // bytes row accepts exactly a $DealRt.Bytes (reference identity
        // preserved), the ?bytes row passes the DEAL null, and any
        // wrong-kind value raises E8001 "expected bytes, got {actual}".
        ExecResult tableBytesOk = runInt32Project("""
            export function main(): null { return null; }
            export function test(): int {
              let t: table = {};
              t.x = bytes(2);
              let b: bytes = t.x;
              b[0] = 7;
              let n: bytes | null = null;
              t.y = n;
              let d: bytes | null = t.y;
              let extra: int = 0;
              if (d !== null) { extra = 1; }
              let e: bytes | null = t.x;
              if (e !== null) { e[0] = 9; }
              return b[0] + extra;
            }
            """, "table_bytes_read_ok");
        check(tableBytesOk.exitCode() == 0,
            "table-held bytes read roundtrip runs green: "
                + tableBytesOk.output());
        check(tableBytesOk.output().contains("9"),
            "the bytes-typed table read preserves reference identity "
                + "(the re-read alias sees the 7 \u2192 9 write) and the "
                + "?bytes row passes the DEAL null: "
                + tableBytesOk.output());
        ExecResult tableBytesBad = runInt32Project("""
            export function main(): null { return null; }
            export function test(): int {
              let t: table = {};
              t.x = 7;
              let b: bytes = t.x;
              return b.length;
            }
            """, "table_bytes_read_bad");
        check(tableBytesBad.exitCode() == 1
                && tableBytesBad.output().contains(
                    "DEAL_ERROR_CODE: E8001")
                && tableBytesBad.output().contains("expected bytes"),
            "the bytes-typed table read raises E8001 with the closed "
                + "\"expected bytes\" message (the kind rides the error "
                + "field) for a wrong-kind value: "
                + tableBytesBad.output());
        ExecResult tableBytesBadNullable = runInt32Project("""
            export function main(): null { return null; }
            export function test(): int {
              let t: table = {};
              t.x = "nope";
              let b: bytes | null = t.x;
              let r: int = 0;
              if (b !== null) { r = b.length; }
              return r;
            }
            """, "table_bytes_read_bad_nullable");
        check(tableBytesBadNullable.exitCode() == 1
                && tableBytesBadNullable.output().contains(
                    "DEAL_ERROR_CODE: E8001")
                && tableBytesBadNullable.output().contains("expected bytes"),
            "the ?bytes table read raises E8001 with the closed message "
                + "for a wrong-kind value: "
                + tableBytesBadNullable.output());

        // ---- Legacy-profile pin (LEGACY_SAFE_INT long carriers) ----
        // The bytes-array carriers are profile-independent ($DealRt.Bytes
        // storage); the array helpers follow the emitted int carriers the
        // same way the bytes helpers do, so the closure shapes compile
        // and execute under the untouched default invocation.
        ExecResult legacyRun = runLegacyProject("""
            export function main(): null { return null; }
            function id(b: bytes): bytes { return b; }
            export function test(): int {
              let b: bytes = bytes(2);
              let xs: bytes[][] = [[b]];
              xs[0][0][0] = 7;
              let ns: (bytes | null)[] = [];
              ns[ns.length] = b;
              ns[ns.length] = null;
              let fs: ((b: bytes) => bytes)[] = [id];
              if (fs[0](b).length !== 2) { throw { code: "TEST_FAIL", message: "fn" }; }
              let extra: int = 0;
              if (ns[1] === null) { extra = 1; }
              return b[0] + extra;
            }
            """, "bytes_closure_legacy_full");
        check(legacyRun.exitCode() == 0,
            "legacy closure program compiles under javac and runs green: "
                + legacyRun.output());
        check(legacyRun.output().contains("8"),
            "legacy closure program computes 7 + 1 = 8: "
                + legacyRun.output());

        // ---- No-E6000-for-bytes negative pin (D9) ----
        // A bytes-closure program tripping an unrelated guard must name
        // the unrelated cause — never bytes nesting or function shape.
        Frontend reassigned = compileFrontend("""
            function id(b: bytes): bytes { return b; }
            export function main(): null { return null; }
            export function test(): int {
              let f: (b: bytes) => bytes = id;
              let g: (b: bytes, extra: int) => bytes = f;
              f = id;
              return 0;
            }
            """, "jvmtest-bytes-closure-reassigned.deal");
        check(reassigned.errors().isEmpty(),
            "bytes closure reassigned-adapter probe frontend clean: "
                + reassigned.errors());
        if (reassigned.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                reassigned.program(), reassigned.checkResult(),
                "jvmtest-bytes-closure-reassigned.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("reassigns")),
                "the reassigned-binding adapter guard fires with the "
                    + "reassignment reason (never bytes): "
                    + res.diagnostics());
            check(res.diagnostics().stream()
                    .noneMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("bytes")),
                "no E6000 names bytes nesting or function shape: "
                    + res.diagnostics());
        }

        // ---- Live module-field rebinding (the criterion's
        // module-binding surface; the LuaJIT side is pinned by
        // jvm-bytes-lua-ref-reassigned-adapter in
        // jvm-bytes-slice) ----
        // An arity adapter over a module-level function re-reads the
        // chunk local live on LuaJIT (id = stamp retargets the
        // (bytes,int)->bytes adapter), so the JVM backend must never
        // snapshot: it retains the reason-bearing E6000 for the
        // module-binding reassignment — never bytes nesting or function
        // shape.
        Frontend moduleRebind = compileFrontend("""
            function id(b: bytes): bytes { return b; }
            function stamp(b: bytes): bytes { b[0] = 5; return b; }
            export function main(): null { return null; }
            export function test(): int {
              let h: (b: bytes, extra: int) => bytes = id;
              id = stamp;
              return 0;
            }
            """, "jvmtest-bytes-closure-module-rebind.deal");
        check(moduleRebind.errors().isEmpty(),
            "bytes closure module-rebind adapter probe frontend clean "
                + "(LuaJIT compiles and retargets this shape; the JVM "
                + "backend rejects it): " + moduleRebind.errors());
        if (moduleRebind.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                moduleRebind.program(), moduleRebind.checkResult(),
                "jvmtest-bytes-closure-module-rebind.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("assignment to 'id'")),
                "the module-binding reassignment guard fires with the "
                    + "assignment reason (never bytes): "
                    + res.diagnostics());
            check(res.diagnostics().stream()
                    .noneMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("bytes")),
                "no E6000 names bytes nesting or function shape: "
                    + res.diagnostics());
        }
    }

    /** The combined T1+T3 verification (ISSUE-0394): the profile flows
     * from a {@code COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION}
     * invocation (the closed invocation matrix) through phase-0 parsing
     * (the profile-aware E1036 gate: in-range literals admitted,
     * {@code 2147483648} rejected) into the JVM emitter (the recorded
     * real int32 mode) — and the compiled artifact executes the pinned
     * edges correctly. A faulted invocation matrix, parser gate, or
     * emitter profile seam fails here. */
    private static void testCommonShadowInvocationPipeline() throws Exception {
        System.out.println("-- COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION: parser gate → JVM emitter pipeline --");

        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
        check(invocation.purpose() == InvocationPurpose.COMMON_SHADOW
                && invocation.semanticProfile()
                    == SemanticProfile.DEAL_V1_2_INT32
                && invocation.releaseState() == ReleaseState.PRE_ACTIVATION,
            "the invocation matrix admits COMMON_SHADOW + DEAL_V1_2_INT32 "
                + "under PRE_ACTIVATION");

        // In-range literal boundaries through phase-0 parsing plus the
        // pinned int32 remainder edge: -2147483648 % -1 runs to the
        // in-range truncated remainder 0.
        ExecResult mod = runInvocationProject("""
            export function main(): null { return null; }
            export function test(): int {
              let a: int = 2147483647;
              let b: int = -2147483648;
              return a + b + (-2147483648 % -1);
            }
            """, "inv_mod_min", invocation);
        check(mod.exitCode() == 0, "invocation mod run exits 0: "
            + mod.output());
        check(mod.output().contains("-1"),
            "2147483647 + (-2147483648) + (MIN % -1 = 0) stores -1 "
                + "(in-range literals admitted by the parser gate): "
                + mod.output());

        // The pinned pow band through the same invocation.
        ExecResult pow62 = runInvocationProject("""
            export function main(): null { return null; }
            export function test(): int { return 2 ** 62; }
            """, "inv_pow_62", invocation);
        check(pow62.exitCode() == 1
                && pow62.output().contains(
                    "DEAL_ERROR_CODE: E8004 int out of safe range"),
            "2 ** 62 raises exactly E8004 through the COMMON_SHADOW "
                + "pipeline: " + pow62.output());
        ExecResult pow1024 = runInvocationProject("""
            export function main(): null { return null; }
            export function test(): int { return 2 ** 1024; }
            """, "inv_pow_1024", invocation);
        check(pow1024.exitCode() == 1
                && pow1024.output().contains(
                    "DEAL_ERROR_CODE: E8001 expected int, got infinity"),
            "2 ** 1024 raises exactly E8001 infinity through the "
                + "COMMON_SHADOW pipeline: " + pow1024.output());

        // The v1.2 IEEE number-pow wrapper through the same invocation.
        ExecResult numPow = runInvocationProject("""
            export function main(): null { return null; }
            export function test(): number { return 1.0 ** (0.0 / 0.0); }
            """, "inv_numpow_one_nan", invocation);
        check(numPow.exitCode() == 0
                && numPow.output().contains("1.0"),
            "1.0 ** NaN yields exactly 1.0 through the COMMON_SHADOW "
                + "pipeline (the v1.2 numPow wrapper): " + numPow.output());

        // The parser-gate negative through the same invocation: the bare
        // 2147483648 literal reaches phase 0 and raises E1036 before any
        // backend emission.
        writeFile("src/inv_e1036.deal", """
            export function main(): null { return null; }
            export function test(): int { return 2147483648; }
            """);
        Path entryFile = tmpDir.get().resolve("src/inv_e1036.deal")
            .toAbsolutePath().normalize();
        Path outputRoot = tmpDir.get().resolve("build/inv_e1036");
        List<Path> roots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator e1036 = new CompilationOrchestrator(
            entryFile, outputRoot, false, false, false, false,
            Backend.JVM, null, roots,
            Path.of(".").toAbsolutePath().normalize(), null, invocation);
        boolean e1036Ok = e1036.compile();
        check(!e1036Ok,
            "the bare 2147483648 literal fails the compile under the "
                + "COMMON_SHADOW v1.2 invocation");
        check(e1036.diagnostics().stream()
                .anyMatch(d -> "E1036".equals(d.code())),
            "the parser gate raises exactly E1036 for 2147483648 under "
                + "the v1.2 profile: " + e1036.diagnostics());
    }

    private static void testOrchestratorJvmBackend() throws Exception {
        System.out.println("-- Orchestrator: Backend.JVM use site --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/jvm",
              "backend": "jvm"
            }""");
        writeFile("src/jvm_main.deal", """
            import * as console from "std/console"
            export function main(): null { return null; }
            function add(a: int, b: int): int { return a + b; }
            export function run(): int {
              console.log("jvm-orchestrator");
              return add(20, 22);
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/jvm_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/jvm");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        // ISSUE-0269: the project routes through production
        // ProjectLocator + the context-driven orchestrator.
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entryFile.toString(), null);
        check(located.context() != null && "jvm".equals(located.context().backend()),
            "strict locate succeeds with the manifest backend jvm: " + located.e2010());
        outputDir = Path.of(located.context().outputPath().absoluteNormalizedPath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, false, false, false, false, null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));

        boolean success = orchestrator.compile();
        check(success, "JVM orchestrator compile succeeds: "
            + orchestrator.diagnostics());
        if (!success) return;

        Path artifact = outputDir.resolve("Jvm_main.java");
        check(Files.exists(artifact), "orchestrator wrote Jvm_main.java");
        check(!Files.exists(outputDir.resolve("jvm_main.lua")),
            "no .lua artifact in JVM mode");
        check(!Files.exists(outputDir.resolve("deal/runtime.lua")),
            "no Lua runtime copied in JVM mode");

        if (Files.exists(artifact)) {
            String java = Files.readString(artifact);
            check(java.contains("public final class Jvm_main"),
                "artifact declares its class");
            check(java.contains("java.lang.System.out.println(\"jvm-orchestrator\")"),
                "console.log mapped to java.lang.System.out");
            check(hasOriginCall(java, "return intAdd(a, b,"),
                "int arithmetic emitted with the origin literals");

            // The production artifact must be real: javac compiles it.
            ProcessBuilder javac = new ProcessBuilder("javac", "-encoding", "UTF-8",
                artifact.toString());
            javac.directory(outputDir.toFile());
            javac.redirectErrorStream(true);
            Process p = javac.start();
            String javacOut = new String(p.getInputStream().readAllBytes()).trim();
            int javacExit = p.waitFor();
            check(javacExit == 0, "orchestrator artifact compiles with javac: "
                + javacOut);
            check(Files.exists(outputDir.resolve("Jvm_main.class")),
                "javac produced the class file");
        }
    }

    private static void testOrchestratorDefaultStaysLua() throws Exception {
        System.out.println("-- Orchestrator: LuaJIT remains the default --");

        writeFile("src/default_main.deal", """
            import * as console from "std/console"
            export function main(): null { return null; }
            export function run(): null { console.log("default-lua"); }
            """);

        Path entryFile = tmpDir.get().resolve("src/default_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/default_lua");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        // The pre-ISSUE-0091 constructor (no backend parameter; the
        // default backend stays LuaJIT). The harness invocation keeps the
        // retained per-module LuaJIT artifact the assertions below pin.
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.LUAJIT,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "default (LuaJIT) compile succeeds");
        check(Files.exists(outputDir.resolve("default_main.lua")),
            "default backend still emits .lua");
        check(!Files.exists(outputDir.resolve("Default_main.java")),
            "no .java artifact under the default backend");
        check(Files.exists(outputDir.resolve("deal/runtime.lua")),
            "Lua runtime still copied under the default backend");
    }

    private static void testOrchestratorJvmRejectsUnsupported() throws Exception {
        System.out.println("-- Orchestrator: JVM backend rejects out-of-scope constructs --");

        // ISSUE-0102: optional class fields (x?: int) are now supported
        // — the rejection pin moves to a still-out-of-scope shape (a
        // function-typed class field).
        writeFile("src/unsupported_main.deal", """
            export function main(): null { return null; }
            export class Point {
              x?: int;
            }
            export class CallbackHolder {
              cb: (x: int) => int = function(x: int): int { return x; };
            }
            export function run(): int { return 1; }
            """);

        Path entryFile = tmpDir.get().resolve("src/unsupported_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/unsupported");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(!success, "JVM backend rejects function-typed class fields");
        check(orchestrator.diagnostics().stream()
                .anyMatch(d -> "E6000".equals(d.code())),
            "orchestrator reports E6000: " + orchestrator.diagnostics());
        check(!Files.exists(outputDir.resolve("Unsupported_main.java")),
            "no artifact written when the backend reports errors");

        // The optional-field class alone now compiles through the
        // orchestrator (ISSUE-0102 promotion of optional class fields).
        writeFile("src/optional_main.deal", """
            export function main(): null { return null; }
            export class Point {
              x?: int;
            }
            export function run(): int { return 1; }
            """);
        Path optionalEntry = tmpDir.get().resolve("src/optional_main.deal")
            .toAbsolutePath();
        Path optionalOut = tmpDir.get().resolve("build/optional_supported");
        CompilationOrchestrator optionalOrchestrator =
            new CompilationOrchestrator(
            optionalEntry,
            optionalOut,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean optionalSuccess = optionalOrchestrator.compile();
        check(optionalSuccess,
            "optional class fields compile through the orchestrator: "
                + optionalOrchestrator.diagnostics());
        check(Files.exists(optionalOut.resolve("Optional_main.java")),
            "optional-class-field module writes its artifact");
    }

    // =========================================================================
    // ISSUE-0099 async/await slice: blocking-call lowering, await-site
    // completion checks, error propagation, and async function values
    // through the ISSUE-0098 wrapper machinery
    // =========================================================================

    /**
     * ISSUE-0099: async declarations emit plain static methods (the
     * spec-permitted JVM blocking-call lowering), await sites emit the
     * call plus the declared-return-type completion check (int
     * completions route through checkInt, null-returning awaits hoist
     * into pre-statements, discard positions evaluate the call), errors
     * raised by awaited operations propagate at the await site, and
     * async function values reuse the ISSUE-0098 wrapper machinery
     * unchanged — the per-signature wrapper shape class, the
     * per-declaration wrapper instance field assigned at the
     * declaration point, indirect awaited calls dispatching through
     * {@code invoke}, and the arity-extension adapter. ISSUE-0304
     * lifts the async-expressions lane: async function expressions and
     * block-level async function declarations emit through the sync
     * closure machinery with async descriptors and blocking bodies,
     * and an {@code await E;} statement evaluates exactly once with
     * the completion check. Non-representable function-type signatures
     * (table carriers) stay E6000, and the pre-rebase
     * module-level function-value read shapes are the v1.2 grammar
     * gate E1049 — never an artifact javac rejects after the CLI
     * reported success.
     */
    private static void testAsyncSlice() throws Exception {
        System.out.println("-- Async/await slice (javac + java) --");

        // Blocking-call lowering (spec-v1.2's permitted JVM form) plus
        // the await-site completion check: an async function emits a
        // plain static method with its declared return type; an int
        // await emits the call wrapped in checkInt. Async function
        // values reuse the ISSUE-0098 wrapper machinery — the
        // per-signature wrapper shape class and the per-declaration
        // wrapper instance field cover async markers, and awaited
        // indirect calls dispatch through invoke.
        String emission = """
            async function g(): int { return 42; }
            async function noop(): null { return; }
            async function value(): int { return 6; }
            async function apply(cb: async (x: int) => int, v: int): int { return await cb(v); }
            export async function test(): int {
              let a: int = await g();
              await noop();
              let f: async () => int = value;
              let b: int = await f();
              return a + b;
            }
            """;
        Frontend fe = compileFrontend(emission, "jvmtest-async.deal");
        check(fe.errors().isEmpty(), "async frontend clean: " + fe.errors());
        if (!fe.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            fe.program(), fe.checkResult(), "jvmtest-async.deal", "main");
        check(!res.hasErrors(), "async codegen clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        String java = res.source();
        check(java.contains("static long g()"),
            "async function g → plain static method");
        check(java.contains("static void noop()"),
            "null-returning async function → void method");
        check(java.contains("checkInt(g())"),
            "await of an int completion wraps the call in checkInt");
        check(java.contains("static abstract class FnA0_R_I"),
            "async () => int uses the shared wrapper shape class");
        check(java.contains("static abstract class FnA1_I_R_I"),
            "async (x: int) => int uses the shared wrapper shape class");
        check(java.contains("static final $DealRt.FnA0_R_I value$fn = new $DealRt.FnA0_R_I()"),
            "per-declaration wrapper instance field");
        check(java.contains("$DealRt.FnA0_R_I f = value$fn;"),
            "function-typed local initializes from the wrapper field");
        check(java.contains("checkInt(f.invokeAt("),
            "awaited indirect call dispatches through invokeAt with the "
                + "call-site origin");
        check(java.contains("checkInt(cb.invokeAt("),
            "await through a callback parameter dispatches through "
                + "invokeAt");
        check(java.contains("noop();"),
            "null-returning await hoists the call into a pre-statement");
        check(!java.contains("checkInt(noop()"),
            "no int check on a null completion");

        // Value/discard positions, nested awaits, and error propagation
        // execute through the real javac + java pipeline.
        ExecResult values = compileAndRunJvm("""
            async function inner(): int { return 7; }
            async function outer(x: int): int { return x + 1; }
            async function tick(): int { return 1; }
            export async function test(): int {
              await tick();
              return await outer(await inner());
            }
            """, "asyncvalues");
        check(values.exitCode() == 0, "value/discard/nested awaits exit 0");
        check(values.output().contains("8"),
            "await outer(await inner()) computes 8: " + values.output());

        ExecResult error = compileAndRunJvm("""
            async function innermost(): int { return 1 / 0; }
            async function mid(): int { return await innermost(); }
            export async function test(): int { return await mid(); }
            """, "asyncerror");
        check(error.exitCode() == 1,
            "awaited E8005 propagates → exit 1: " + error.output());
        check(error.output().contains("DEAL_ERROR_CODE: E8005"),
            "DEAL_ERROR_CODE: E8005 surfaces at the outermost await: "
                + error.output());

        ExecResult fnValue = compileAndRunJvm("""
            async function plus1(x: int): int { return x + 1; }
            async function apply(cb: async (x: int) => int, v: int): int { return await cb(v); }
            export async function test(): int { return await apply(plus1, 6); }
            """, "asyncfnvalue");
        check(fnValue.exitCode() == 0, "function-value callback exits 0");
        check(fnValue.output().contains("7"),
            "awaited indirect call through the callback computes 7: "
                + fnValue.output());

        // Arity extension inherits the ISSUE-0098 adapter machinery: a
        // narrower async signature at a wider async target wraps in a
        // delegating adapter whose invoke drops the extra parameters.
        ExecResult arity = compileAndRunJvm("""
            async function one(x: int): int { return x; }
            export async function test(): int {
              let f: async (x: int, y: int) => int = one;
              return await f(1, 2);
            }
            """, "asyncarity");
        check(arity.exitCode() == 0, "async arity extension exits 0");
        check(arity.output().contains("1"),
            "await f(1, 2) drops the extra argument and computes 1: "
                + arity.output());

        // Reassigned-binding guard descends into awaited calls: an
        // assignment hidden in an awaited call's argument list
        // (`apply(g = two, 1)`) reassigns the binding exactly like a
        // bare statement assignment, so the adapter over `g` must not
        // silently snapshot it. LuaJIT's adapter reads the binding live
        // on every invoke — pinned by the LuaJIT-only reference fixture
        // jvm-async-lua-ref-reassigned-adapter (the retargeted adapter
        // computes 11) — and the JVM slice cannot emit a live capture
        // of a reassigned binding: E6000, never a silent divergence.
        Frontend hidden = compileFrontend("""
            async function one(x: int): int { return x; }
            async function two(x: int): int { return x + 10; }
            async function apply(cb: async (x: int) => int, v: int): int { return await cb(v); }
            export async function test(): int {
              let g: async (x: int) => int = one;
              let h: async (x: int, y: int) => int = g;
              await apply(g = two, 1);
              return await h(1, 2);
            }
            """, "jvmtest-async-reassigned.deal");
        check(hidden.errors().isEmpty(),
            "frontend accepts the awaited-argument-hidden reassignment: "
                + hidden.errors());
        if (hidden.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult hiddenRes = JvmBackend.generate(
                hidden.program(), hidden.checkResult(),
                "jvmtest-async-reassigned.deal", "main");
            check(hiddenRes.hasErrors(),
                "backend rejects the awaited-argument-hidden reassignment");
            check(hiddenRes.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())),
                "E6000 for the awaited-argument-hidden reassignment: "
                    + hiddenRes.diagnostics());
        }

        // ISSUE-0304: async function expressions emit through the sync
        // closure machinery with the async descriptor marker and the
        // blocking body — the E6000 gate is lifted, the anonymous
        // subclass carries the async shape id (FnA0_R_I), and the
        // awaited indirect call runs the completion check (checkInt
        // around invoke) at the await site.
        Frontend expr = compileFrontend("""
            export async function test(): int {
              let f: async () => int = async function(): int { return 42; };
              return await f();
            }
            """, "jvmtest-async-expr.deal");
        check(expr.errors().isEmpty(),
            "frontend accepts the async function expression: "
                + expr.errors());
        if (!expr.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult exprRes = JvmBackend.generate(
            expr.program(), expr.checkResult(), "jvmtest-async-expr.deal", "main");
        check(!exprRes.hasErrors(),
            "async function expression codegen clean: "
                + exprRes.diagnostics());
        check(exprRes.source().contains(
                "$DealRt.FnA0_R_I f = new $DealRt.FnA0_R_I()"),
            "async function expression emits an anonymous FnA0_R_I "
                + "subclass into the typed local: " + exprRes.source());
        check(exprRes.source().contains("checkInt(f.invokeAt("),
            "awaited async function expression runs the completion "
                + "check at the await site: " + exprRes.source());
        ExecResult exprRun = compileAndRunJvm("""
            export async function test(): int {
              let f: async () => int = async function(): int { return 42; };
              return await f();
            }
            """, "asyncexpr");
        check(exprRun.exitCode() == 0,
            "async function expression executes: exit 0: "
                + exprRun.output());
        check(exprRun.output().contains("42"),
            "awaited async function expression computes 42: "
                + exprRun.output());

        // An async function expression body's awaits compile as direct
        // blocking calls with the completion check at the await site
        // (checkInt around the inner direct call), and captured
        // enclosing locals route through cells so a later reassignment
        // is observed by the wrapper's invoke (LuaJIT's upvalue
        // semantics) — the anonymous subclass with captured cells is
        // valid Java.
        Frontend exprAwait = compileFrontend("""
            async function base(): int { return 5; }
            export async function test(): int {
              let x: int = 41;
              let f: async () => int = async function(): int { return await base() + x; };
              x = 100;
              return await f();
            }
            """, "jvmtest-async-expr-await.deal");
        check(exprAwait.errors().isEmpty(),
            "frontend accepts the awaiting async function expression: "
                + exprAwait.errors());
        if (!exprAwait.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult exprAwaitRes = JvmBackend.generate(
            exprAwait.program(), exprAwait.checkResult(),
            "jvmtest-async-expr-await.deal", "main");
        check(!exprAwaitRes.hasErrors(),
            "awaiting async function expression codegen clean: "
                + exprAwaitRes.diagnostics());
        check(hasOriginCall(exprAwaitRes.source(),
                "return intAdd(checkInt(base()), x$c[0],"),
            "the expression body's await is a direct blocking call with "
                + "the completion check, and the captured local routes "
                + "through its cell: " + exprAwaitRes.source());
        ExecResult exprAwaitRun = compileAndRunJvm("""
            async function base(): int { return 5; }
            export async function test(): int {
              let x: int = 41;
              let f: async () => int = async function(): int { return await base() + x; };
              x = 100;
              return await f();
            }
            """, "asyncexprawait");
        check(exprAwaitRun.exitCode() == 0,
            "awaiting async function expression executes: exit 0: "
                + exprAwaitRun.output());
        check(exprAwaitRun.output().contains("105"),
            "the wrapper observes the reassigned cell (105 = 5 + 100): "
                + exprAwaitRun.output());

        // Block-level async function declarations (ISSUE-0304 D2/D3): a
        // block-level async function declares like the block-level sync
        // form — fresh cell plus anonymous wrapper instance at the
        // declaration's source position — with the async descriptor;
        // captured bindings cell-ify so the enclosing async function
        // observes the writes; an `await g();` statement evaluates the
        // call exactly once with the completion check and discards the
        // value.
        ExecResult block = compileAndRunJvm("""
            export async function f(): int {
              let completionState: int = 0;
              let completionCount: int = 0;
              async function g(): int {
                let result: int = 42;
                completionState = result;
                completionCount = completionCount + 1;
                return result;
              }
              await g();
              if (completionState !== 42 || completionCount !== 1) {
                throw { code: "TEST_FAIL", message: "block-level async" };
              }
              return 0;
            }
            """, "asyncblock");
        check(block.exitCode() == 0,
            "block-level async declaration executes: exit 0: "
                + block.output());
        check(block.output().contains("0"),
            "enclosing async function observes g's captured writes: "
                + block.output());

        // ISSUE-0301 shared carrier: array/nullable/class signature
        // shapes are representable in async ANNOTATIONS too — the
        // shared per-signature wrapper machinery carries every shape
        // the injective encoding covers (no E6000 remains for shapes
        // this surface covers), and the awaited call executes through
        // the real javac + java pipeline.
        ExecResult shape = compileAndRunJvm("""
            class C { v: int = 3; }
            async function total(xs: int[]): int { return xs[0]; }
            async function nul(x: int | null): int { return 1; }
            async function cls(c: C): int { return c.v; }
            export async function test(): int {
              let f: async (xs: int[]) => int = total;
              let g: async (x: int | null) => int = nul;
              let h: async (c: C) => int = cls;
              return await f([1]);
            }
            """, "asyncshape");
        check(shape.exitCode() == 0,
            "async array/nullable/class annotation signatures exit 0: "
                + shape.output());
        check(shape.output().contains("1"),
            "awaited call through the array-param wrapper computes 1: "
                + shape.output());

        // The table-carrier gate stays: a function-type ANNOTATION
        // whose signature contains a table carrier raises E6000 with
        // the table-carrier message (the ISSUE-0110 descriptor-join
        // family; the recursive bytes-bearing wrapper closure landed
        // with ISSUE-0160, so bytes carriers inside annotation
        // signatures are representable).
        Frontend tableSig = compileFrontend("""
            async function pick(t: table): int { return 1; }
            export async function test(): int {
              let f: async (t: table) => int = pick;
              return 0;
            }
            """, "jvmtest-async-tablesig.deal");
        check(tableSig.errors().isEmpty(),
            "frontend accepts the table-param annotation signature: "
                + tableSig.errors());
        if (tableSig.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult tableRes = JvmBackend.generate(
                tableSig.program(), tableSig.checkResult(),
                "jvmtest-async-tablesig.deal", "main");
            check(tableRes.hasErrors() && tableRes.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("table carriers")),
                "table carriers inside an annotation signature stay E6000 "
                    + "(table-carrier message): "
                    + tableRes.diagnostics());
        }

        // v1.2 grammar gate: the pre-rebase module-level function-value
        // read shapes (`let g: async () => int = value;` at top level,
        // and a module-level call transitively reading a later-declared
        // function's value) are E1049 at the frontend — the v1.2 module
        // top level holds only declarations, so the load-time guards
        // stay defensive and pinned exactly like the sibling ISSUE-0098
        // load-time guards.
        Frontend late = compileFrontend("""
            let g: async () => int = value;
            async function value(): int { return 1; }
            export async function test(): int { return await g(); }
            """, "jvmtest-async-late.deal");
        check(late.errors().stream()
                .anyMatch(d -> "E1049".equals(d.code())),
            "module-level function-value read rejected with E1049: "
                + late.errors());
    }
    // @jsonable slice (JSON serialization)
    // =========================================================================

    /**
     * The @jsonable slice: the generated {@code C$fromJson}/
     * {@code C$toJson} helpers, the per-class {@code $jsonFields}
     * descriptor table, fromJson/toJson validation semantics (null on
     * extra keys / malformed JSON / type mismatches / unpaired UTF-16
     * surrogate code units in decoded JSON strings, and invalid JSON
     * number spellings (leading zeros, a decimal point without a
     * fraction digit, a sign/digit-starved exponent, a missing integer
     * part — parse failures returning the DEAL null, RFC 8259 /
     * std/json.lua parity) — never a throw; E8001 for a NaN number
     * field in toJson; required no-default fields applying the
     * reference defaults table — the primitive zeroes, a fresh empty
     * table/array per call, never Java null, and a required
     * class-typed field's absent key as a fromJson validation
     * failure), and the slice boundaries
     * — optional/table-typed @jsonable fields, non-jsonable
     * array/class fields, and module-level calls of the generated
     * helpers stay E6000. Every runtime case compiles the emitted
     * artifact with javac and executes it with java; the same surface
     * runs through the legacy JSON conformance harness adapter in
     * {@code retired JSON slice jvm-jsonable-slice}.
     */
    private static void testJsonableSlice() throws Exception {
        System.out.println("-- @jsonable slice: generated helpers, descriptors, validation, boundaries --");

        ExecResult roundtrip = compileAndRunJvm("""
            // @jsonable
            export class User {
              name: string = "";
              age: int = 0;
            }
            export function test(): string {
              let u: User = { name: "Ada", age: 30 };
              let json: string = User$toJson(u);
              let u2: User | null = User$fromJson(json);
              if (u2 !== null) {
                if (u2.name !== "Ada" || u2.age !== 30) { return "bad"; }
                return "ok";
              }
              return "null";
            }
            """, "jsonable-roundtrip");
        check(roundtrip.exitCode() == 0, "jsonable roundtrip exits 0: "
            + roundtrip.output());
        check(roundtrip.output().contains("ok"), "jsonable roundtrip ok: "
            + roundtrip.output());

        // Extra keys, malformed JSON, type mismatches, and a non-object
        // top-level value all return the DEAL null.
        ExecResult failures = compileAndRunJvm("""
            // @jsonable
            export class User {
              name: string = "";
              age: int = 0;
            }
            export function test(): int {
              let a: User | null = User$fromJson("{\\"name\\":\\"Ada\\",\\"extra\\":1}");
              if (a === null) {
                let b: User | null = User$fromJson("{oops");
                if (b === null) {
                  let c: User | null = User$fromJson("{\\"name\\":\\"Ada\\",\\"age\\":2.5}");
                  if (c === null) {
                    let d: User | null = User$fromJson("[1,2]");
                    if (d === null) { return 1; }
                    return 0;
                  }
                  return 0;
                }
                return 0;
              }
              return 0;
            }
            """, "jsonable-failures");
        check(failures.exitCode() == 0, "jsonable failures exit 0: "
            + failures.output());
        check(failures.output().contains("1"), "jsonable failures return 1: "
            + failures.output());

        // A NaN number field raises E8001 in toJson (std/json.lua parity).
        ExecResult nan = compileAndRunJvm("""
            // @jsonable
            export class Metric {
              value: number = 0.0;
            }
            export function test(): string {
              let m: Metric = { value: 0.0 / 0.0 };
              return Metric$toJson(m);
            }
            """, "jsonable-nan");
        check(nan.output().contains("DEAL_ERROR_CODE: E8001"),
            "toJson of a NaN number field raises E8001: " + nan.output());

        // Emission pins: the artifact carries the descriptor table, the
        // translated helper names, and the JSON runtime — and a module
        // without @jsonable classes emits none of it.
        String source = """
            // @jsonable
            export class User {
              name: string = "";
              age: int = 0;
            }
            export function test(): int { return 1; }
            """;
        Frontend f = compileFrontend(source, "jvmtest-jsonable-pin.deal");
        check(f.errors().isEmpty(), "jsonable pin frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(), "jvmtest-jsonable-pin.deal", "Main");
            check(!res.hasErrors(), "jsonable pin codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "new java.lang.String[]{\"name\", \"string\", \"false\", \"false\"}"),
                    "the field descriptor rows carry {name, jtype, optional, nullable}");
                check(java.contains("public static $C_User User$dfromJson(java.lang.String s)"),
                    "the generated fromJson export uses the javaName translation");
                check(java.contains("return __jsonStringify("
                        + "$C_User.$toJsonValue(v, oFile, oLine, oCol), "
                        + "oFile, oLine, oCol);"),
                    "the generated toJson export stringifies the field "
                        + "serializer and threads the call-site origin");
                check(java.contains("static java.lang.Object __jsonParse("),
                    "the JSON parser is emitted for a module with @jsonable classes");
                check(java.contains("static final java.lang.String[][] $jsonFields"),
                    "the per-class $jsonFields descriptor is emitted");
                check(java.contains(
                        "catch (java.lang.StackOverflowError e) { return null; }"),
                    "the JSON parser converts deep-nesting stack exhaustion "
                    + "to the DEAL null");
                check(java.contains(
                        "try { return $C_User.$fromJsonValue(__jsonParse(s)); }"),
                    "the public fromJson export wraps the conversion so the "
                    + "exhaustion shapes never escape it");
                check(java.contains("static java.lang.Object __jsonTableValue"
                        + "(java.lang.Object raw, int depth) {"),
                    "the table-value conversion carries the bounded depth "
                    + "parameter");
                check(java.contains("if (depth > 512) throw new "
                        + "java.lang.RuntimeException(\"JSON nesting too "
                        + "deep\");"),
                    "the table-value conversion carries the bounded depth "
                    + "guard");
                check(java.contains("if (__hasUnpairedSurrogate(out)) throw "
                        + "new java.lang.RuntimeException(\"unpaired "
                        + "UTF-16 surrogate code unit in JSON string\");"),
                    "the JSON string parser rejects unpaired UTF-16 "
                    + "surrogate code units");
                check(java.contains("the strict RFC 8259 number"),
                    "the JSON number parser validates the strict RFC "
                    + "8259 number grammar");
                check(java.contains(
                        "if (i < s.length() && s.charAt(i) == '0') { i++; }"),
                    "the JSON number parser rejects leading zeros");
                check(java.contains("if (i >= s.length() || s.charAt(i) < '0' "
                        + "|| s.charAt(i) > '9') throw new "
                        + "java.lang.RuntimeException(\"bad JSON "
                        + "number\");"),
                    "the JSON number parser requires digits after the "
                    + "decimal point and the exponent");
            }
        }
        Frontend plain = compileFrontend("""
            export function test(): int { return 1; }
            """, "jvmtest-jsonable-plain.deal");
        check(plain.errors().isEmpty(), "plain module frontend clean");
        if (plain.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                plain.program(), plain.checkResult(), "jvmtest-jsonable-plain.deal", "Main");
            check(!res.source().contains("__jsonParse"),
                "a module without @jsonable classes emits no JSON runtime support");
        }

        // Runtime coverage for the optional and table field forms:
        // the three optional-nullable states (absent / present null /
        // present value with has() presence), the optional-with-default
        // form, table fields with nested objects, and nested JSON arrays
        // as array-mode tables.
        ExecResult optional = compileAndRunJvm("""
            // @jsonable
            export class User {
              name: string = "";
              nick?: string | null;
            }
            export function test(): string {
              let m: User = { name: "A" };
              let mj: string = User$toJson(m);
              let m2: User | null = User$fromJson(mj);
              if (m2 !== null) {
                if (has(m2.nick)) { return "has-missing"; }
              } else { return "m2"; }
              let n: User = { name: "B", nick: null };
              let nj: string = User$toJson(n);
              if (nj !== "{\\\"name\\\":\\\"B\\\",\\\"nick\\\":null}") { return "nj"; }
              let n2: User | null = User$fromJson(nj);
              if (n2 !== null) {
                if (!has(n2.nick) || n2.nick !== null) { return "n2"; }
              } else { return "n2null"; }
              let v: User = { name: "C", nick: "cee" };
              let v2: User | null = User$fromJson(User$toJson(v));
              if (v2 !== null) {
                if (!has(v2.nick)) { return "no-has"; }
                let nick: string | null = v2.nick;
                if (nick !== null) {
                  if (nick !== "cee") { return "bad"; }
                } else { return "nick-null"; }
              } else { return "v2null"; }
              return "ok";
            }
            """, "jsonable-optional");
        check(optional.exitCode() == 0 && optional.output().contains("ok"),
            "optional three-state roundtrip: " + optional.output());

        ExecResult table = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let w: Wrap = { data: { nested: { inner: "x" } } };
              let json: string = Wrap$toJson(w);
              let w2: Wrap | null = Wrap$fromJson(json);
              if (w2 !== null) {
                let nested: table = w2.data.nested;
                let inner: string = nested.inner;
                if (inner !== "x") { return "inner"; }
                return "ok";
              }
              return "null";
            }
            """, "jsonable-table");
        check(table.exitCode() == 0 && table.output().contains("ok"),
            "table field roundtrip: " + table.output());

        ExecResult tableArrays = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let w: Wrap | null = Wrap$fromJson("{\\\"data\\\":{\\\"values\\\":[[1,2],[3,4]]}}");
              if (w !== null) {
                let values: table = w.data.values;
                let json: string = Wrap$toJson(w);
                if (json !== "{\\\"data\\\":{\\\"values\\\":[[1,2],[3,4]]}}") { return "json"; }
                return "ok";
              }
              return "null";
            }
            """, "jsonable-table-arrays");
        check(tableArrays.exitCode() == 0
                && tableArrays.output().contains("ok"),
            "table field nested JSON arrays roundtrip: "
                + tableArrays.output());

        // Hostile deep-nesting pins: the fromJson export must return the
        // DEAL null on deeply nested JSON instead of crashing the
        // program. A ~20 KB payload of 20000 nested '[' ... ']' exhausts
        // the emitted parser's stack — the emitted parser converts its
        // StackOverflowError to the DEAL null exactly like LuaJIT's
        // pcall(__json_parse, s). Deep-but-parsable nesting inside a
        // table field (600 nested objects past the 512-level guard)
        // exercises the bounded depth guard of the table-value
        // conversion. Both shapes pin exit 0 and the DEAL null.
        ExecResult deepArrays = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let s: string = "{\\\"data\\\":";
              let i: int = 0;
              while (i < 20000) { s = s + "["; i = i + 1; }
              i = 0;
              while (i < 20000) { s = s + "]"; i = i + 1; }
              s = s + "}";
              let w: Wrap | null = Wrap$fromJson(s);
              if (w !== null) { return "not-null"; }
              return "ok";
            }
            """, "jsonable-deep-arrays");
        check(deepArrays.exitCode() == 0 && deepArrays.output().contains("ok"),
            "deeply nested JSON arrays return the DEAL null instead of "
            + "crashing the program: " + deepArrays.output());

        ExecResult deepTable = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let s: string = "{\\\"data\\\":";
              let i: int = 0;
              while (i < 600) { s = s + "{\\\"k\\\":"; i = i + 1; }
              s = s + "{\\\"k\\\":[1]}";
              i = 0;
              while (i < 600) { s = s + "}"; i = i + 1; }
              s = s + "}";
              let w: Wrap | null = Wrap$fromJson(s);
              if (w !== null) { return "not-null"; }
              return "ok";
            }
            """, "jsonable-deep-table-guard");
        check(deepTable.exitCode() == 0 && deepTable.output().contains("ok"),
            "the table-value depth guard converts deep nesting to the "
            + "DEAL null: " + deepTable.output());

        // Unpaired UTF-16 surrogate pin (reviewed defect): the JSON
        // parser's backslash-u escape decoding must reject lone
        // surrogates — a lone high (0xD800) or low (0xDC00) surrogate
        // in a string field or a table-field string leaf is a parse
        // failure returning the DEAL null exactly like LuaJIT's
        // std/json.lua decoder error inside pcall(__json_parse, s) —
        // while a valid high+low pair decodes and reads back. The
        // escape text is built with Java concatenation after the text
        // block via placeholder replacement: a raw backslash-u-D800 in
        // Java source would be a Java unicode escape (a lone surrogate
        // in the test source itself).
        ExecResult surrogates = compileAndRunJvm("""
            // @jsonable
            export class User {
              name: string = "";
            }
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let hi: User | null = User$fromJson("{\\"name\\":\\"<LONE_HIGH>\\"}");
              if (hi !== null) { return "hi-accepted"; }
              let lo: User | null = User$fromJson("{\\"name\\":\\"<LONE_LOW>\\"}");
              if (lo !== null) { return "lo-accepted"; }
              let pair: User | null = User$fromJson("{\\"name\\":\\"<VALID_PAIR>\\"}");
              if (pair !== null) {
                if (pair.name !== "<PAIR_EMOJI>") { return "pair-bad"; }
              } else { return "pair-null"; }
              let leaf: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"leaf\\":\\"<LONE_HIGH>\\"}}");
              if (leaf !== null) { return "leaf-accepted"; }
              return "ok";
            }
            """.replace("<LONE_HIGH>", "\\" + "uD800")
                .replace("<LONE_LOW>", "\\" + "uDC00")
                .replace("<VALID_PAIR>", "\\" + "uD83D" + "\\" + "uDE00")
                .replace("<PAIR_EMOJI>", "\uD83D\uDE00"),
            "jsonable-unpaired-surrogates");
        check(surrogates.exitCode() == 0
                && surrogates.output().contains("ok"),
            "lone UTF-16 surrogates in JSON strings return the DEAL null "
            + "while a valid surrogate pair decodes: " + surrogates.output());

        // Invalid JSON number spellings (reviewed defect): the emitted
        // parser must validate the strict RFC 8259 number grammar
        // before Double.parseDouble. A leading zero (01, -01, 00), a
        // decimal point without a fraction digit (1.), an exponent
        // without fraction digits (1.e2, 5.e+2), an exponent or sign
        // without digits (1e, 1e+), and a missing integer part (-.5)
        // are parse failures returning the DEAL null for a typed field
        // and for a table-field leaf — exactly like LuaJIT's
        // std/json.lua parse_error inside pcall(__json_parse, s) —
        // while valid spellings (0, 42, 2.5, -0.5, 1e2, 1.5e-2, and a
        // plain table-leaf number) still parse and read back, never an
        // over-rejection.
        ExecResult numbers = compileAndRunJvm("""
            // @jsonable
            export class P {
              age: int = 0;
              score: number = 0.0;
            }
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let a: P | null = P$fromJson("{\\"age\\":01}");
              if (a !== null) { return "01"; }
              let b: P | null = P$fromJson("{\\"age\\":-01}");
              if (b !== null) { return "-01"; }
              let c: P | null = P$fromJson("{\\"score\\":00}");
              if (c !== null) { return "00"; }
              let d: P | null = P$fromJson("{\\"score\\":1.}");
              if (d !== null) { return "1."; }
              let e: P | null = P$fromJson("{\\"score\\":1.e2}");
              if (e !== null) { return "1.e2"; }
              let f: P | null = P$fromJson("{\\"score\\":5.e+2}");
              if (f !== null) { return "5.e+2"; }
              let g: P | null = P$fromJson("{\\"score\\":-.5}");
              if (g !== null) { return "-.5"; }
              let h: P | null = P$fromJson("{\\"score\\":1e}");
              if (h !== null) { return "1e"; }
              let i: P | null = P$fromJson("{\\"score\\":1e+}");
              if (i !== null) { return "1e+"; }
              let t: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":01}}");
              if (t !== null) { return "table-01"; }
              let t2: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":-01}}");
              if (t2 !== null) { return "table--01"; }
              let t3: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":1.}}");
              if (t3 !== null) { return "table-1."; }
              let t4: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":1.e2}}");
              if (t4 !== null) { return "table-1.e2"; }
              let t5: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":-.5}}");
              if (t5 !== null) { return "table--.5"; }
              let ok: P | null = P$fromJson("{\\"age\\":42,\\"score\\":2.5}");
              if (ok !== null) {
                if (ok.age !== 42) { return "age"; }
                if (ok.score !== 2.5) { return "score"; }
              } else {
                return "ok-null";
              }
              let forms: P | null = P$fromJson("{\\"age\\":0,\\"score\\":-0.5}");
              if (forms !== null) {
                if (forms.age !== 0) { return "zero"; }
                if (forms.score !== -0.5) { return "neg"; }
              } else {
                return "forms-null";
              }
              let expo: P | null = P$fromJson("{\\"age\\":0,\\"score\\":1.5e-2}");
              if (expo !== null) {
                if (expo.score !== 0.015) { return "expo"; }
              } else {
                return "expo-null";
              }
              let e2: P | null = P$fromJson("{\\"age\\":0,\\"score\\":1e2}");
              if (e2 !== null) {
                if (e2.score !== 100.0) { return "e2"; }
              } else {
                return "e2-null";
              }
              let tv: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"n\\":10}}");
              if (tv === null) { return "table-10-null"; }
              return "ok";
            }
            """, "jsonable-number-grammar");
        check(numbers.exitCode() == 0 && numbers.output().contains("ok"),
            "invalid JSON number spellings return the DEAL null while "
            + "valid spellings parse: " + numbers.output());

        // Required no-default fields (the reviewed defect): the
        // reference defaults table (LuaBackend.defaultValueForTypeNode)
        // applies the per-type zeroes — 0 / 0.0 / false / "" — and a
        // FRESH empty table/array per call. The pre-fix emission stored
        // Java null into the non-nullable $DealRt.Table/__IntArray/$C
        // slots, so
        // fromJson("{}") produced toJson {"data":null} and the first
        // table read crashed with a raw NullPointerException
        // (LuaJIT: {"data":{}}, {} for arrays, and a DEAL-null read).
        ExecResult nodefault = compileAndRunJvm("""
            // @jsonable
            export class Child {
              x: int = 1;
            }
            // @jsonable
            export class Raw {
              i: int;
              n: number;
              b: boolean;
              s: string;
              data: table;
              xs: int[];
            }
            // @jsonable
            export class Holder {
              c: Child;
              i: int;
            }
            export function test(): string {
              let w: Raw | null = Raw$fromJson("{}");
              if (w !== null) {
                if (w.i !== 0) { return "i"; }
                if (w.n !== 0.0) { return "n"; }
                if (w.b !== false) { return "b"; }
                if (w.s !== "") { return "s"; }
                let j: string = Raw$toJson(w);
                if (j !== "{\\"i\\":0,\\"n\\":0.0,\\"b\\":false,\\"s\\":\\"\\",\\"data\\":{},\\"xs\\":[]}") { return "j:" + j; }
                let t: table = w.data;
                let miss: string | null = t.missing;
                if (miss !== null) { return "miss"; }
                if (w.xs.length !== 0) { return "len"; }
                let n0: int | null = w.xs[0];
                if (n0 !== null) { return "n0"; }
                w.xs[w.xs.length] = 7;
                let w2: Raw | null = Raw$fromJson("{}");
                if (w2 !== null) {
                  if (w2.xs.length !== 0) { return "shared"; }
                  let j2: string = Raw$toJson(w2);
                  if (j2 !== j) { return "j2"; }
                } else {
                  return "w2-null";
                }
                // A required CLASS-typed field with no declared default:
                // the reference defaults-table {} placeholder (a plain
                // Lua table, never a class instance) has no Java value
                // at the typed slot — an absent key is a fromJson
                // validation failure (the DEAL null), never Java null
                // crossing the non-nullable class boundary (the pre-fix
                // JVM silently read null at a typed read where LuaJIT
                // raises E8001).
                let h: Holder | null = Holder$fromJson("{}");
                if (h !== null) { return "h-not-null"; }
                let h2: Holder | null = Holder$fromJson("{\\"c\\":{\\"x\\":9}}");
                if (h2 !== null) {
                  if (h2.c.x !== 9) { return "x"; }
                  if (h2.i !== 0) { return "i"; }
                  let hj: string = Holder$toJson(h2);
                  if (hj !== "{\\"c\\":{\\"x\\":9},\\"i\\":0}") { return "hj:" + hj; }
                  return "ok";
                }
                return "h2-null";
              }
              return "w-null";
            }
            """, "jsonable-required-nodefault");
        check(nodefault.exitCode() == 0
                && nodefault.output().contains("ok"),
            "required no-default fromJson fields apply the reference "
            + "defaults (fresh {}/[] and the primitive zeroes), a "
            + "missing-key table/array read yields the DEAL null never "
            + "a raw NPE, and a required no-default class field's absent "
            + "key is a fromJson validation failure: " + nodefault.output());

        // Emission pins for the same shapes: the fresh table/array
        // defaults and the class-field absent-key validation-failure
        // guard.
        Frontend nodefaultPin = compileFrontend("""
            // @jsonable
            export class Child {
              x: int = 1;
            }
            // @jsonable
            export class Wrap {
              data: table;
              xs: int[];
              c: Child;
            }
            export function test(): int { return 1; }
            """, "jvmtest-jsonable-nodefault-pin.deal");
        check(nodefaultPin.errors().isEmpty(),
            "no-default pin frontend clean: " + nodefaultPin.errors());
        if (nodefaultPin.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                nodefaultPin.program(), nodefaultPin.checkResult(),
                "jvmtest-jsonable-nodefault-pin.deal", "Main");
            check(!res.hasErrors(), "no-default pin codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("$DealRt.Table f0 = null;")
                        && java.contains("f0 = new $DealRt.Table();"),
                    "a required no-default table field defaults to a "
                    + "fresh empty $DealRt.Table (never Java null) — "
                    + "ISSUE-0302 phase order: the declaration carries "
                    + "the type-safe placeholder and the omitted-default "
                    + "phase assigns the fresh table");
                check(java.contains(
                        "$DealRt.__IntArray f1 = null;")
                        && java.contains(
                        "f1 = new $DealRt.__IntArray(new long[0]);"),
                    "a required no-default array field defaults to a "
                    + "fresh empty wrapper (never Java null)");
                check(java.contains(
                        "if (!provided2) return null;"),
                    "a required no-default class field's absent key is "
                    + "a fromJson validation failure (the placeholder "
                    + "never crosses the typed boundary) — the "
                    + "ISSUE-0302 phase order guards on the provided "
                    + "flag after the omitted-default phase");
            }
        }

        // Slice boundaries: non-jsonable array/class fields and the
        // @jsonable optional-table form are E6000 — never silently
        // miscompiled. The optional-table gate pins the reviewed
        // defect: the pre-fix emission stored `data?: table` as the
        // table class and
        // later passed the Missing sentinel into that slot, leaving an
        // artifact javac rejected ('Object cannot be converted to the
        // table class')
        // after the CLI reported success — the field's read yields
        // `table | null`, a value shape the slice keeps out of its
        // typed positions. A module-level (load-time) call of a
        // generated helper is a v1.2 E1049 module-shape gate: the v1.2
        // module top level holds only declarations, so the v1.1
        // load-time shape (LuaJIT reads the helper's not-yet-assigned
        // chunk local and fails; Java would silently run the hoisted
        // method) is rejected before any backend.
        record Gate(String what, String source) {}
        // ISSUE-0102 lifted the NON-jsonable class surface: array,
        // table, and optional fields on non-@jsonable classes compile
        // and run (boxed slots plus $present flags). The @jsonable
        // slice keeps its own Missing-sentinel storage for optional
        // fields — these forms stay accepted alongside it.
        List<Gate> accepted = List.of(
            new Gate("array field of a non-jsonable class", """
                class Plain { v: int = 0; }
                class Outer { xs: Plain[] = []; }
                export function test(): int { return 1; }
                """),
            new Gate("table field of a non-jsonable class", """
                class Plain { v: int = 0; }
                class Outer { meta: table = {}; }
                export function test(): int { return 1; }
                """),
            new Gate("optional field of a non-jsonable class", """
                class Plain { v?: int; }
                export function test(): int { return 1; }
                """)
        );
        for (Gate g : accepted) {
            Frontend fg = compileFrontend(g.source(), "jvmtest-jsonable-gate.deal");
            if (!fg.errors().isEmpty()) {
                fail("frontend must accept '" + g.what() + "': "
                    + fg.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                fg.program(), fg.checkResult(), "jvmtest-jsonable-gate.deal", "Main");
            check(!res.hasErrors(), "backend accepts " + g.what() + ": "
                + res.diagnostics());
        }
        List<Gate> gates = List.of(
            new Gate("optional table field of an @jsonable class", """
                // @jsonable
                export class Wrap {
                  data?: table;
                }
                export function test(): int { return 1; }
                """),
            new Gate("nullable table field of an @jsonable class", """
                // @jsonable
                export class Wrap {
                  data: table | null = null;
                }
                export function test(): int { return 1; }
                """),
            new Gate("optional nullable table field of an @jsonable class", """
                // @jsonable
                export class Wrap {
                  data?: table | null;
                }
                export function test(): int { return 1; }
                """)
        );
        for (Gate g : gates) {
            Frontend fg = compileFrontend(g.source(), "jvmtest-jsonable-gate.deal");
            if (!fg.errors().isEmpty()) {
                fail("frontend must accept '" + g.what() + "' (the backend rejects it): "
                    + fg.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                fg.program(), fg.checkResult(), "jvmtest-jsonable-gate.deal", "Main");
            check(res.hasErrors(), "backend rejects " + g.what());
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 diagnostic for " + g.what() + ": " + res.diagnostics());
        }

        // The v1.2 module-shape gate for a load-time call of a generated
        // helper: the v1.2 module top level holds only declarations, so
        // the v1.1 load-time shape is E1049 before any backend runs.
        Frontend mod = compileFrontend("""
            // @jsonable
            export class User {
              name: string = "";
            }
            let u: User | null = User$fromJson("{}");
            export function test(): int { return 1; }
            """, "jvmtest-jsonable-module-shape.deal");
        check(mod.errors().stream().anyMatch(d -> "E1049".equals(d.code())),
            "the v1.2 module top level rejects a load-time call of the "
            + "generated helper with E1049: " + mod.errors());
    }

    /**
     * The std/json + @jsonable encode/decode raise-site origins
     * (jvm-canonical-error-snapshot-convergence D3/D4, the std/json leaf,
     * ISSUE-0608): every JSON encode/decode rejection passes the
     * json.stringify / json.parse call expression's span, threaded
     * unchanged through the recursive encode walk; the unsupported-type
     * raises populate the closed expected/actual projection; the cyclic
     * rejection fabricates neither; and the @jsonable toJson call site
     * hands its own call-expression origin to the generated helper.
     */
    private static void testJsonOriginLiterals() {
        System.out.println("-- std/json + @jsonable origin literals "
            + "(ISSUE-0608) --");
        String source = """
            import * as json from "std/json"

            // @jsonable
            export class Wrapper {
              data: table = {};
            }

            export function run(t: table, s: string): string {
              let a: table = json.parse(s);
              let b: string = json.stringify(t);
              let w: Wrapper = { data: {} };
              return Wrapper$toJson(w);
            }

            export function main(): null {
              return null;
            }
            """;
        String file = "jvmtest-json-origin-literals.deal";
        String[] lines = source.split("\n", -1);
        int parseLine = 0, parseCol = 0, stringifyLine = 0, stringifyCol = 0,
            toJsonLine = 0, toJsonCol = 0;
        for (int i = 0; i < lines.length; i++) {
            if (parseLine == 0) {
                int at = lines[i].indexOf("json.parse(");
                if (at >= 0) { parseLine = i + 1; parseCol = at + 1; }
            }
            if (stringifyLine == 0) {
                int at = lines[i].indexOf("json.stringify(");
                if (at >= 0) { stringifyLine = i + 1; stringifyCol = at + 1; }
            }
            if (toJsonLine == 0) {
                int at = lines[i].indexOf("Wrapper$toJson(");
                if (at >= 0) { toJsonLine = i + 1; toJsonCol = at + 1; }
            }
        }
        check(parseLine > 0 && stringifyLine > 0 && toJsonLine > 0,
            "the probe source carries the three call sites");
        Frontend f = compileFrontend(source, file);
        check(f.errors().isEmpty(), "json origin frontend clean: "
            + f.errors());
        if (!f.errors().isEmpty()) {
            return;
        }
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(f.program(),
            f.checkResult(), file, "Main");
        check(!res.hasErrors(), "json origin codegen clean: "
            + res.diagnostics());
        if (res.hasErrors()) {
            return;
        }
        String java = res.source();
        check(java.contains("__jsonStringify(t, \"" + file + "\", "
                + stringifyLine + ", " + stringifyCol + ")"),
            "the json.stringify call site passes its call-expression "
                + "origin (D3)");
        check(java.contains("$jsonParse(s, \"" + file + "\", "
                + parseLine + ", " + parseCol + ")"),
            "the json.parse call site passes its call-expression "
                + "origin (D3)");
        check(java.contains("Wrapper$dtoJson(w, \"" + file + "\", "
                + toJsonLine + ", " + toJsonCol + ")"),
            "the @jsonable toJson call site passes its call-expression "
                + "origin (D3)");
        check(java.contains("public static java.lang.String Wrapper$dtoJson("
                + "$C_Wrapper v, java.lang.String oFile, int oLine, "
                + "int oCol) {"),
            "the generated toJson helper receives the origin parameters");
        check(java.contains("static void __jsonAppend(java.lang.StringBuilder"
                + " sb, java.lang.Object v, java.util.Set<java.lang.Object>"
                + " stack, java.lang.String oFile, int oLine, int oCol) {"),
            "the recursive encode walk receives the origin parameters (D1)");
        check(java.contains("__jsonAppend(sb, e, stack, oFile, oLine, "
                + "oCol);"),
            "the recursive encode walk threads the origin unchanged (D3)");
        check(java.contains("throw new DealError(\"E8001\", \"unsupported "
                + "type for JSON encoding: \" + __jsonKind(v), oFile, oLine, "
                + "oCol, \"string, number, boolean, or table\", "
                + "__jsonKind(v), null, null);"),
            "the unsupported-type encode rejection carries the threaded "
                + "origin and the closed expected/actual projection (D4)");
        check(!java.contains("unsupported type for JSON encoding: \" + "
                + "(v instanceof"),
            "the kind projection is the closed helper, not an inline arm");
        check(java.contains("static java.lang.String __jsonKind("
                + "java.lang.Object v) {"),
            "the closed kind projection helper is emitted");
        check(java.contains("$toJsonValue($C_Wrapper v, java.lang.String "
                + "oFile, int oLine, int oCol) {"),
            "the @jsonable field serializer receives the threaded origin");
        check(java.contains("__jsonShape(v.data, oFile, oLine, oCol))"),
            "a table field's shape validation receives the threaded origin");
        check(java.contains("__jsonShapeWalk(v, seen, 0, oFile, oLine, "
                + "oCol);"),
            "the shape walk threads the origin through the recursion");
        check(java.contains("if (!seen.add(v)) throw new DealError(\"E8001\", "
                + "\"cyclic value cannot be encoded as JSON\", oFile, oLine, "
                + "oCol);"),
            "the cyclic rejection carries the threaded origin and no "
                + "expected/actual pair (never fabricated)");
        check(java.contains("static java.lang.String __jsonQuote("
                + "java.lang.String s, java.lang.String oFile, int oLine, "
                + "int oCol) {"),
            "the string quoter receives the origin parameters so every "
                + "encode rejection carries the call-site span (D3)");
        check(java.contains("sb.append(__jsonQuote(s, oFile, oLine, "
                + "oCol)); return; }"),
            "the string-value encode branch threads the origin into the "
                + "quoter");
        check(java.contains("if (__hasUnpairedSurrogate(s)) throw new "
                + "DealError(\"E8001\", \"cannot encode invalid UTF-8 as "
                + "JSON\", oFile, oLine, oCol);"),
            "the unpaired-surrogate encode rejection carries the threaded "
                + "call-site origin");
        check(java.contains("static $DealRt.Table __jsonShape($DealRt.Table "
                + "v, java.lang.String oFile, int oLine, int oCol) {"),
            "the shape helper receives the origin parameters (D1)");
    }

    /**
     * ISSUE-0302 (std/json boundary and @jsonable completion) unit
     * surface: std/json import support with json.parse/json.stringify
     * over the emitted shared JSON runtime, the fromJson top-level
     * input gate, the provided-fields-before-defaults phase order,
     * fresh per-level nested-array decoder locals (javac validity for
     * int[][] and deeper shapes), recursive array serialization for
     * table fields, the raw-control-character parse rejection, and the
     * stringify-side unpaired-surrogate scan.
     */
    private static void testJsonStdlibBoundary() throws Exception {
        System.out.println("-- ISSUE-0302: std/json boundary and @jsonable completion --");

        // std/json joins the supported set: json.parse returns the
        // shared $DealRt.Table (object mode for objects, array mode
        // for arrays, integral numbers as the int carrier) and
        // json.stringify roundtrips.
        ExecResult roundtrip = compileAndRunJvm("""
            import * as json from "std/json"
            import * as str from "std/string"
            export function test(): string {
              let doc: table = { count: 42, ratio: 2.5, flag: true, nothing: null, name: "Ada" };
              let encoded: string = json.stringify(doc);
              if (!str.contains(encoded, "\\\"count\\\":42")) { return "enc:" + encoded; }
              let back: table = json.parse(encoded);
              let count: int = back.count;
              let ratio: number = back.ratio;
              let flag: boolean = back.flag;
              let name: string = back.name;
              if (count !== 42 || ratio !== 2.5 || !flag || name !== "Ada") { return "back"; }
              return "ok";
            }
            """, "json-stdlib-roundtrip");
        check(roundtrip.exitCode() == 0
                && roundtrip.output().contains("ok"),
            "std/json parse/stringify roundtrip through the shared "
            + "runtime: " + roundtrip.output());

        // Malformed input raises E8001 (the decoder's stored message),
        // never a silent null and never a raw crash.
        ExecResult malformed = compileAndRunJvm("""
            import * as json from "std/json"
            export function test(): string {
              return json.parse("{oops").a;
            }
            """, "json-parse-malformed");
        check(malformed.output().contains("DEAL_ERROR_CODE: E8001")
                && malformed.output().contains("JSON parse error"),
            "json.parse of malformed input raises E8001 with the "
            + "decoder message: " + malformed.output());

        // Raw U+0000-U+001F control characters inside JSON strings are
        // rejected by json.parse with E8001 (std/json.lua parse_string
        // parity), while C$fromJson collapses the same parse failure to
        // the DEAL null.
        ExecResult control = compileAndRunJvm("""
            import * as json from "std/json"
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let collapsed: Wrap | null = Wrap$fromJson("{\\"data\\":{\\"leaf\\":\\"<RAW_CTL>\\"}}");
              if (collapsed !== null) { return "fromjson-accepted"; }
              return json.parse("{\\"data\\":\\"<RAW_CTL>\\"}").data;
            }
            """.replace("<RAW_CTL>", "\u0001"),
            "json-parse-raw-control");
        check(control.output().contains("DEAL_ERROR_CODE: E8001")
                && control.output().contains(
                    "raw control character in string (must be escaped)"),
            "raw control characters reject through json.parse with "
            + "E8001 and collapse to the DEAL null through C$fromJson: "
            + control.output());

        // Top-level input gate: scalar / null / non-empty array -> the
        // DEAL null; {} and [] both decode the defaulted instance and
        // roundtrip identically.
        ExecResult gate = compileAndRunJvm("""
            // @jsonable
            export class C {
              x: int = 0;
            }
            export function test(): string {
              if (C$fromJson("42") !== null) { return "42"; }
              if (C$fromJson("\\\"x\\\"") !== null) { return "str"; }
              if (C$fromJson("true") !== null) { return "true"; }
              if (C$fromJson("null") !== null) { return "null"; }
              if (C$fromJson("[1,2]") !== null) { return "arr"; }
              let from_obj: C | null = C$fromJson("{}");
              let from_arr: C | null = C$fromJson("[]");
              if (from_obj !== null) {
                if (from_arr !== null) {
                  if (C$toJson(from_obj) !== C$toJson(from_arr)) { return "neq"; }
                  return "ok";
                }
                return "arr-null";
              }
              return "obj-null";
            }
            """, "jsonable-top-level-gate");
        check(gate.exitCode() == 0 && gate.output().contains("ok"),
            "fromJson top-level gate: scalar/null/non-empty array -> "
            + "the DEAL null and {}/[] collapse identically: "
            + gate.output());

        // Nested-array decoder javac validity: int[][] and int[][][]
        // roundtrip — the emitted conversions allocate fresh local
        // names per nesting level (no l0/a0/i0/e0 redeclaration).
        ExecResult nested = compileAndRunJvm("""
            // @jsonable
            export class Matrix {
              values: int[][] = [];
            }
            // @jsonable
            export class Cube {
              values: int[][][] = [];
            }
            export function test(): string {
              let m: Matrix = { values: [[1, 2], [3, 4]] };
              let m2: Matrix | null = Matrix$fromJson(Matrix$toJson(m));
              if (m2 !== null) {
                if (m2.values[0][0] !== 1 || m2.values[1][1] !== 4) { return "m"; }
              } else { return "m-null"; }
              let c: Cube = { values: [[[1, 2], [3, 4]], [[5, 6], [7, 8]]] };
              let c2: Cube | null = Cube$fromJson(Cube$toJson(c));
              if (c2 !== null) {
                if (c2.values[0][0][0] !== 1 || c2.values[1][1][1] !== 8) { return "c"; }
              } else { return "c-null"; }
              return "ok";
            }
            """, "jsonable-nested-arrays-deep");
        check(nested.exitCode() == 0 && nested.output().contains("ok"),
            "nested array fields (int[][] and int[][][]) roundtrip with "
            + "fresh per-level decoder locals: " + nested.output());

        // Table fields holding nested arrays roundtrip recursively.
        ExecResult tableArrays = compileAndRunJvm("""
            // @jsonable
            export class Wrap {
              data: table = {};
            }
            export function test(): string {
              let w: Wrap = { data: { values: [[1, 2], [3, 4]] } };
              let w2: Wrap | null = Wrap$fromJson(Wrap$toJson(w));
              if (w2 !== null) {
                let w3: Wrap | null = Wrap$fromJson(Wrap$toJson(w2));
                if (w3 !== null) {
                  let t: table = w3.data;
                  let values: int[][] = t.values;
                  if (values[0][0] !== 1 || values[1][1] !== 4) { return "bad"; }
                  return "ok";
                }
                return "w3-null";
              }
              return "w2-null";
            }
            """, "jsonable-table-field-nested-arrays");
        check(tableArrays.exitCode() == 0
                && tableArrays.output().contains("ok"),
            "table fields holding [[1,2],[3,4]] roundtrip through "
            + "C$toJson/C$fromJson without E8001: "
            + tableArrays.output());

        // Phase order: provided fields decode and validate in class
        // source order BEFORE any omitted default evaluates — a
        // provided-value failure returns the DEAL null with zero
        // default side effects.
        ExecResult phase = compileAndRunJvm("""
            import * as console from "std/console"
            function markDefault(): int {
              console.log("DEFAULT-RAN");
              return 1;
            }
            // @jsonable
            export class Rec {
              a: int = 0;
              b: int = markDefault();
            }
            export function test(): string {
              let bad: Rec | null = Rec$fromJson("{\\"a\\":\\"x\\"}");
              if (bad !== null) { return "bad-not-null"; }
              let good: Rec | null = Rec$fromJson("{\\"a\\":7}");
              if (good !== null) {
                if (good.a !== 7) { return "a"; }
                if (good.b !== 1) { return "b"; }
              } else {
                return "good-null";
              }
              return "ok";
            }
            """, "jsonable-provided-before-defaults");
        check(phase.exitCode() == 0 && phase.output().contains("ok"),
            "fromJson decodes provided fields before evaluating omitted "
            + "defaults: " + phase.output());
        check(countOccurrences(phase.output(), "DEFAULT-RAN") == 1,
            "a provided-value failure runs no defaults (the default "
            + "side effect runs exactly once, for the successful "
            + "decode): " + phase.output());

        // Stringify-side unpaired-surrogate scan: a string value or a
        // map key carrying a lone surrogate through C$toJson /
        // json.stringify raises E8001 "cannot encode invalid UTF-8 as
        // JSON" and emits no JSON output (std/json.lua escape parity).
        ExecResult surrogateValue = compileAndRunJvm("""
            // @jsonable
            export class User {
              name: string = "";
            }
            export function test(): string {
              let u: User = { name: "<LONE_HIGH>" };
              return User$toJson(u);
            }
            """.replace("<LONE_HIGH>", "\ud800"),
            "jsonable-tojson-lone-surrogate");
        check(surrogateValue.output().contains("DEAL_ERROR_CODE: E8001")
                && surrogateValue.output().contains(
                    "cannot encode invalid UTF-8 as JSON")
                && !surrogateValue.output().contains("{"),
            "C$toJson of a lone-surrogate string value raises E8001 "
            + "with no JSON output: " + surrogateValue.output());

        Frontend keyPathPin = compileFrontend("""
            import * as json from "std/json"
            export function test(): string {
              let t: table = { a: 1 };
              return json.stringify(t);
            }
            """, "jvmtest-json-stringify-key-path.deal");
        check(keyPathPin.errors().isEmpty(),
            "key-path pin frontend clean: " + keyPathPin.errors());
        if (keyPathPin.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                keyPathPin.program(), keyPathPin.checkResult(),
                "jvmtest-json-stringify-key-path.deal", "Main");
            check(!res.hasErrors(),
                "key-path pin codegen clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "sb.append(__jsonQuote(java.lang.String.valueOf(e.getKey()), oFile, oLine, oCol))"),
                    "the JSON-object branch quotes map keys through the "
                    + "scanning __jsonQuote helper");
                check(java.contains(
                        "sb.append(__jsonQuote(e.getKey(), oFile, oLine, oCol))"),
                    "the $DealRt.Table object branch quotes table keys "
                    + "through the scanning __jsonQuote helper");
            }
        }

        // Emission pins: std/json imports emit the shared JSON runtime
        // (even without @jsonable classes), json.parse lowers to the
        // $jsonParse helper, and the stringify-side scan + raw-control
        // rejection sit in the emitted text.
        Frontend stdlibPin = compileFrontend("""
            import * as json from "std/json"
            export function test(): table {
              return json.parse("{\\"a\\":1}");
            }
            """, "jvmtest-json-stdlib-pin.deal");
        check(stdlibPin.errors().isEmpty(),
            "std/json pin frontend clean: " + stdlibPin.errors());
        if (stdlibPin.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                stdlibPin.program(), stdlibPin.checkResult(),
                "jvmtest-json-stdlib-pin.deal", "Main");
            check(!res.hasErrors(),
                "std/json import is not an E6000: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains("static java.lang.Object __jsonParse("),
                    "a std/json-importing module emits the shared JSON "
                    + "runtime even without @jsonable classes");
                check(java.contains(
                        "static $DealRt.Table $jsonParse(java.lang.String s) {"),
                    "the emitted $jsonParse helper backs json.parse");
                check(java.contains("return $jsonParse("),
                    "json.parse call sites lower to the $jsonParse helper");
                check(java.contains(
                        "if (__hasUnpairedSurrogate(s)) throw new "
                        + "DealError(\"E8001\", \"cannot encode "
                        + "invalid UTF-8 as JSON\", oFile, oLine, oCol);"),
                    "the emitted __jsonQuote carries the stringify-side "
                    + "unpaired-surrogate scan");
                check(java.contains(
                        "if (c < 0x20) throw new "
                        + "java.lang.RuntimeException(\"raw control "
                        + "character in string (must be escaped)\");"),
                    "the emitted parser rejects raw U+0000-U+001F "
                    + "control characters");
            }
        }
    }

    /**
     * ISSUE-0109: imported-class values, imported-class construction, and
     * cross-module nominal identity now compile and run through the real
     * orchestrator pipeline (module discovery → checking → per-module
     * JvmBackend codegen → javac → java), replacing the pre-ISSUE-0109
     * E6000 deferral. Locality is still decided from the Type.Class
     * MODULE PATH: a same-named local class must never satisfy the guard
     * for a foreign path, and the emitted Java type of an imported class
     * is the DECLARING module's generated nested class ({@code Lib.$C_C}),
     * never a local one.
     */
    private static void testImportedClassValues() throws Exception {
        System.out.println("-- Orchestrator: imported-class values, construction, and nominal identity --");



        // (1) An annotation-less local inferred from an imported module's
        // class-typed export: `let c = lib.getC()` declares c as
        // Lib.$C_C (the pre-ISSUE-0109 backend emitted `$C_C c =
        // Lib.getC();` and javac rejected the artifact after the CLI
        // reported success).
        writeFile("src/lib.deal", """
            class C { v: int = 0; }
            export function getC(): C { return { v: 1 }; }
            """);
        writeFile("src/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int {
              let c = lib.getC();
              return c.v + 1;
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/imported_class");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "JVM backend supports imported-class values: "
            + orchestrator.diagnostics());
        check(Files.exists(outputDir.resolve("Entry.java"))
                && Files.exists(outputDir.resolve("Lib.java")),
            "imported-class artifacts written");
        if (success && Files.exists(outputDir.resolve("Entry.java"))) {
            String java = Files.readString(outputDir.resolve("Entry.java"));
            check(java.contains("Lib.$C_C c = Lib.getC();"),
                "the inferred imported-class value declares the imported "
                + "module's generated class type: " + java);
            check(hasOriginCall(java, "return intAdd((c).v, 1,"),
                "the imported class field read emits a direct access fed "
                + "into int arithmetic with the origin literals: " + java);
            ExecResult exec = runJvmArtifacts(outputDir,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("2"),
                "the imported-class value reads back c.v + 1 = 2: "
                    + exec.output());
        }

        // (2) A same-named LOCAL class must not satisfy the imported-class
        // guard: lib.C stays Lib.$C_C while the local C stays
        // Entry.$C_C (the pre-fix name-keyed guard emitted `$C_C c =
        // Lib.getC();` — javac: incompatible types Lib.$C_C → Entry.$C_C
        // — after the CLI reported success).
        // The companion lives in its own directory: under the v1.2
        // identity carriage two files in one directory share the module
        // identity, so a same-named local class would be
        // identity-ambiguous with the imported one — the subdirectory
        // keeps the two nominal identities distinct (the pre-carriage
        // module-path isolation semantics this pin preserves).
        writeFile("src2/lib/index.deal", """
            class C { v: int = 0; }
            export function getC(): C { return { v: 9 }; }
            """);
        writeFile("src2/entry.deal", """
            import * as lib from "./lib"
            class C { v: int = 0; }
            export function main(): null { return null; }
            export function run(): int {
              let c = lib.getC();
              let localC: C = { v: 4 };
              return c.v * 10 + localC.v;
            }
            """);

        Path entryFile2 = tmpDir.get().resolve("src2/entry.deal").toAbsolutePath();
        Path outputDir2 = tmpDir.get().resolve("build/imported_class_same_name");
        List<Path> roots2 = List.of(tmpDir.get().resolve("src2").toAbsolutePath());

        CompilationOrchestrator orchestrator2 = new CompilationOrchestrator(
            entryFile2,
            outputDir2,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots2,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success2 = orchestrator2.compile();
        check(success2, "a same-named local class stays distinct from the "
            + "imported class: " + orchestrator2.diagnostics());
        if (success2 && Files.exists(outputDir2.resolve("Entry.java"))) {
            String java = Files.readString(outputDir2.resolve("Entry.java"));
            check(java.contains("LibIndex.$C_C c = LibIndex.getC();"),
                "the imported type references LibIndex.$C_C even with a "
                + "local C: " + java);
            check(java.contains("new $C_C(4)"),
                "the local construction keeps the local $C_C: " + java);
            ExecResult exec = runJvmArtifacts(outputDir2,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("94"),
                "imported 9 and local 4 stay distinct: 9 * 10 + 4 = 94: "
                    + exec.output());
        }

        // (3) Imported-class construction: a lib.C-context object literal
        // (`lib.takeC({ v: 9 })`) emits `new Lib.$C_C(9L)` in the module
        // that also declares its own C (the pre-fix silent
        // nominal-identity corruption tagged the literal with the LOCAL
        // module identity).
        writeFile("src3/lib.deal", """
            class C { v: int = 0; }
            export function takeC(c: C): int { return c.v; }
            """);
        writeFile("src3/entry.deal", """
            import * as lib from "./lib"
            class C { v: int = 0; }
            export function main(): null { return null; }
            export function run(): int {
              return lib.takeC({ v: 9 });
            }
            """);

        Path entryFile3 = tmpDir.get().resolve("src3/entry.deal").toAbsolutePath();
        Path outputDir3 = tmpDir.get().resolve("build/imported_class_construct");
        List<Path> roots3 = List.of(tmpDir.get().resolve("src3").toAbsolutePath());

        CompilationOrchestrator orchestrator3 = new CompilationOrchestrator(
            entryFile3,
            outputDir3,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots3,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success3 = orchestrator3.compile();
        check(success3, "construction of an imported class type compiles: "
            + orchestrator3.diagnostics());
        if (success3 && Files.exists(outputDir3.resolve("Entry.java"))) {
            String java = Files.readString(outputDir3.resolve("Entry.java"));
            check(java.contains("new Lib.$C_C(9)"),
                "the imported construction emits new Lib.$C_C(...): " + java);
            ExecResult exec = runJvmArtifacts(outputDir3,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("9"),
                "the imported construction runs to 9: " + exec.output());
        }

        // (4) Imported-class construction with defaulted fields: omitted
        // fields receive their declared literal defaults inline
        // (`new Lib.$C_Point(0L, 5L)` for `{ y: 5 }` over
        // `x: int = 0; y: int = 0`), and a provided field whose literal
        // order differs from declaration order lands in its declared
        // field.
        writeFile("src4/lib.deal", """
            export class Point {
              x: int = 10;
              y: int = 20;
            }
            export function sum(p: Point): int { return p.x + p.y; }
            """);
        writeFile("src4/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int {
              let a: lib.Point = {};
              let b: lib.Point = { y: 5, x: 2 };
              return a.x + a.y * 10 + lib.sum(b);
            }
            """);

        Path entryFile4 = tmpDir.get().resolve("src4/entry.deal").toAbsolutePath();
        Path outputDir4 = tmpDir.get().resolve("build/imported_class_defaults");
        List<Path> roots4 = List.of(tmpDir.get().resolve("src4").toAbsolutePath());

        CompilationOrchestrator orchestrator4 = new CompilationOrchestrator(
            entryFile4,
            outputDir4,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots4,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success4 = orchestrator4.compile();
        check(success4, "imported construction with literal defaults "
            + "compiles: " + orchestrator4.diagnostics());
        if (success4 && Files.exists(outputDir4.resolve("Entry.java"))) {
            String java = Files.readString(outputDir4.resolve("Entry.java"));
            check(java.contains(
                    "new Lib.$C_Point(Lib.$default$$C_Point$x(), "
                        + "Lib.$default$$C_Point$y())"),
                "the empty literal routes every omitted default through"
                    + " the provider's published-plan evaluator methods"
                    + " (ISSUE-0544 E7): " + java);
            check(java.contains("new Lib.$C_Point(2, 5)"),
                "provided fields land in declaration order regardless of "
                + "literal order: " + java);
            ExecResult exec = runJvmArtifacts(outputDir4,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("217"),
                "10 + 20 * 10 + (2 + 5) = 217: " + exec.output());
        }

        // (5) Cross-module nominal runtime checks: two modules export a
        // SAME-NAME class; an instance crossing an untyped table passes
        // its own module's check (Modela.$check("@src5/Item", …)
        // succeeds) and fails the foreign module's check with E8001
        // naming both canonical identities (@src5/Item vs
        // @src5/modelb/Item) — identity is
        // module-qualified, never bare-name. The foreign check raises the
        // IMPORTED module's DealError, which the conformance runner
        // reports with the DEAL_ERROR_CODE contract.
        writeFile("src5/modela.deal", """
            export class Item { tag: string = ""; }
            export function makeItem(tag: string): Item { return { tag: tag }; }
            export function readItem(i: Item): string { return i.tag; }
            """);
        // modelb lives in its own directory: under the v1.2 identity
        // carriage two files in one directory share the module identity
        // (relative components exclude the file stem), so same-named
        // same-directory classes would carry ONE nominal identity and
        // the foreign check could never mismatch — the subdirectory
        // keeps the two identities distinct and preserves the
        // module-qualified isolation semantics of this pin.
        writeFile("src5/modelb/index.deal", """
            export class Item { tag: string = ""; }
            export function makeItem(tag: string): Item { return { tag: tag }; }
            export function readItem(i: Item): string { return i.tag; }
            """);
        writeFile("src5/entry.deal", """
            import * as modela from "./modela"
            import * as modelb from "./modelb"
            export function main(): null { return null; }
            export function run(): string {
              let holder: table = { item: modela.makeItem("from-a") };
              let a: modela.Item = holder.item;
              return modela.readItem(a);
            }
            """);
        writeFile("src5/entry_fail.deal", """
            import * as modela from "./modela"
            import * as modelb from "./modelb"
            export function main(): null { return null; }
            export function run(): string {
              let holder: table = { item: modela.makeItem("from-a") };
              let b: modelb.Item = holder.item;
              return modelb.readItem(b);
            }
            """);

        Path outputDir5 = tmpDir.get().resolve("build/imported_nominal");
        // Success entry: entry.deal (the orchestrator resolves only the
        // imports each entry needs).
        CompilationOrchestrator orchestrator5 = new CompilationOrchestrator(
            tmpDir.get().resolve("src5/entry.deal").toAbsolutePath(),
            outputDir5,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            List.of(tmpDir.get().resolve("src5").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success5 = orchestrator5.compile();
        check(success5, "cross-module nominal check success shape compiles: "
            + orchestrator5.diagnostics());
        if (success5 && Files.exists(outputDir5.resolve("Entry.java"))) {
            String java = Files.readString(outputDir5.resolve("Entry.java"));
            check(java.contains("Modela.$check(\"@src5/Item\", ("),
                "the imported class-typed table read dispatches on the "
                + "declaring module's shared seam with the canonical "
                + "class descriptor: " + java);
            ExecResult exec = runJvmArtifacts(outputDir5,
                parseProgram("export function run(): string { return \"\"; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("from-a"),
                "the genuine instance passes its own module's nominal "
                + "check: " + exec.output());
        }

        Path outputDir6 = tmpDir.get().resolve("build/imported_nominal_fail");
        CompilationOrchestrator orchestrator6 = new CompilationOrchestrator(
            tmpDir.get().resolve("src5/entry_fail.deal").toAbsolutePath(),
            outputDir6,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            List.of(tmpDir.get().resolve("src5").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success6 = orchestrator6.compile();
        check(success6, "cross-module nominal check failure shape compiles: "
            + orchestrator6.diagnostics());
        if (success6 && Files.exists(outputDir6.resolve("Entry_fail.java"))) {
            ExecResult exec = runJvmArtifacts(outputDir6,
                parseProgram("export function run(): string { return \"\"; }"),
                "Entry_fail");
            check(exec.exitCode() == 1,
                "the wrong-module same-name instance fails at runtime "
                + "(exit 1): " + exec.output());
            check(exec.output().contains("DEAL_ERROR_CODE: E8001"),
                "the foreign nominal check reports E8001: " + exec.output());
            check(exec.output().contains(
                    "expected instance of @src5/modelb/Item, got @src5/Item"),
                "the E8001 message names both canonical identities: "
                    + exec.output());
        }

        // (6) Positive control: passing an imported class VALUE straight
        // through (`lib.takeC(lib.getC())`) never binds a local or
        // constructs with the foreign type, so it must compile and run —
        // the value is produced and consumed inside lib.
        writeFile("src6/lib.deal", """
            class C { v: int = 0; }
            export function getC(): C { return { v: 42 }; }
            export function takeC(c: C): int { return c.v; }
            """);
        writeFile("src6/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int {
              return lib.takeC(lib.getC());
            }
            """);

        Path entryFile6 = tmpDir.get().resolve("src6/entry.deal").toAbsolutePath();
        Path outputDir7 = tmpDir.get().resolve("build/imported_class_passthrough");
        List<Path> roots6 = List.of(tmpDir.get().resolve("src6").toAbsolutePath());

        CompilationOrchestrator orchestrator7 = new CompilationOrchestrator(
            entryFile6,
            outputDir7,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots6,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success7 = orchestrator7.compile();
        check(success7, "imported class value pass-through compiles: "
            + orchestrator7.diagnostics());
        check(Files.exists(outputDir7.resolve("Entry.java"))
                && Files.exists(outputDir7.resolve("Lib.java")),
            "pass-through artifacts written");
        if (success7 && Files.exists(outputDir7.resolve("Entry.java"))) {
            ExecResult exec = runJvmArtifacts(outputDir7,
                parseProgram("export function run(): int { return 1; }"),
                "Entry");
            check(exec.exitCode() == 0 && exec.output().contains("42"),
                "the pass-through call runs to 42: " + exec.output());
        }
    }

    /**
     * ISSUE-0108 nullable slice: the boxed reference representation of
     * {@code T | null} (Long/Double/Boolean for the numeric primitives,
     * String/class/array references), narrowed-read unboxing through the
     * null-check branches, nullable class fields, nullable parameters and
     * returns, {@code T[] | null} and {@code (T | null)[]} for the four
     * primitives and local classes, the table-read nullable boundary
     * checks (E8001 for a wrong inner value — the runtime probe lives in
     * the conformance fixture jvm-nullable-boundary-failure), the
     * nullable conversion intrinsics, and the still-rejected forms
     * ({@code table | null}, {@code (table | null)[]}, optional class
     * fields, class-typed class fields). Every runtime probe compiles
     * the emitted artifact with the real {@code javac} frontend and
     * executes it with {@code java}.
     */
    /**
     * ISSUE-0110: the single JVM type-descriptor emitter spells every
     * supported type form in the spec {@code RuntimeTypeDescriptor}
     * format — primitives, table/null/Error, nullables, arrays (nested
     * and nullable-element), nominal classes with module paths, function
     * types with array/class/nullable parameters, async operation types,
     * and rest arms.
     */
    private static void testTypeDescriptorEmitter() {
        System.out.println("-- Shared type-descriptor emitter (ISSUE-0110) --");
        check(JvmBackend.typeDescriptor(Type.Int.INSTANCE).equals("int"),
            "int spells 'int'");
        check(JvmBackend.typeDescriptor(Type.Number.INSTANCE).equals("number"),
            "number spells 'number'");
        check(JvmBackend.typeDescriptor(Type.Boolean.INSTANCE).equals("boolean"),
            "boolean spells 'boolean'");
        check(JvmBackend.typeDescriptor(Type.String.INSTANCE).equals("string"),
            "string spells 'string'");
        check(JvmBackend.typeDescriptor(Type.Table.INSTANCE).equals("table"),
            "table spells 'table'");
        check(JvmBackend.typeDescriptor(Type.Null.INSTANCE).equals("null"),
            "null spells 'null'");
        try {
            JvmBackend.typeDescriptor(Type.Error.INSTANCE);
            fail("typeDescriptor: the internal Type.Error sentinel must never be emitted");
        } catch (IllegalStateException expected) {
            check(true, "Type.Error has no canonical descriptor (the pinned internal invariant violation — never emitted, never an artifact)");
        }
        check(JvmBackend.typeDescriptor(Types.nullable(Type.Int.INSTANCE)).equals("?int"),
            "int | null spells '?int'");
        check(JvmBackend.typeDescriptor(Types.array(Type.Int.INSTANCE)).equals("[int]"),
            "int[] spells '[int]'");
        check(JvmBackend.typeDescriptor(
                Types.array(Types.array(Type.Int.INSTANCE))).equals("[[int]]"),
            "int[][] spells '[[int]]'");
        check(JvmBackend.typeDescriptor(
                Types.nullable(Types.array(Type.Int.INSTANCE))).equals("?[int]"),
            "int[] | null spells '?[int]'");
        check(JvmBackend.typeDescriptor(
                Types.array(Types.nullable(Type.Int.INSTANCE))).equals("[?int]"),
            "(int | null)[] spells '[?int]'");
        check(JvmBackend.typeDescriptor(Types.nullable(Types.array(
                Types.nullable(Type.Int.INSTANCE)))).equals("?[?int]"),
            "(int | null)[] | null spells '?[?int]'");
        check(JvmBackend.typeDescriptor(
                IdentityTestFixtures.classType("User", "models"))
                    .equals("@models/User"),
            "a class with a project identity spells '@models/User'");
        check(JvmBackend.typeDescriptor(
                IdentityTestFixtures.errorClassType())
                    .equals("@$builtin/Error"),
            "the intrinsic builtin Error class spells '@$builtin/Error'");
        try {
            JvmBackend.typeDescriptor(
                IdentityTestFixtures.classType("User", ""));
            fail("typeDescriptor: a bare class name must never be emitted");
        } catch (IllegalStateException expected) {
            check(true, "a bare class name is never emitted (the unrepresentable"
                + " builtin non-Error identity is the pinned internal "
                + "invariant violation)");
        }
        check(JvmBackend.typeDescriptor(Types.nullable(
                IdentityTestFixtures.classType("User", "app")))
                    .equals("?@app/User"),
            "User | null spells '?@app/User'");
        check(JvmBackend.typeDescriptor(Types.array(
                IdentityTestFixtures.classType("User", "app")))
                    .equals("[@app/User]"),
            "User[] spells '[@app/User]'");
        check(JvmBackend.typeDescriptor(Types.array(Types.nullable(
                IdentityTestFixtures.classType("User", "app"))))
                    .equals("[?@app/User]"),
            "(User | null)[] spells '[?@app/User]'");
        check(JvmBackend.typeDescriptor(Types.func(
                List.of(Type.Int.INSTANCE), Type.String.INSTANCE))
                .equals("(int)->string"),
            "(int)->string spells '(int)->string'");
        check(JvmBackend.typeDescriptor(Types.func(
                List.of(Type.Int.INSTANCE), Type.String.INSTANCE, true))
                .equals("async(int)->string"),
            "async(int)->string spells 'async(int)->string'");
        check(JvmBackend.typeDescriptor(Types.func(
                List.of(Types.array(Type.Int.INSTANCE)),
                Types.nullable(IdentityTestFixtures.classType("User", "app"))))
                .equals("([int])->?@app/User"),
            "an array parameter and a nullable class return compose in one "
            + "descriptor");
        check(JvmBackend.typeDescriptor(Types.func(
                List.of(Types.nullable(Type.String.INSTANCE)),
                Types.array(IdentityTestFixtures.classType("User", "app"))))
                .equals("(?string)->[@app/User]"),
            "a nullable parameter and a class-array return compose in one "
            + "descriptor");
        System.out.println("  typeDescriptor forms pinned");
    }

    /**
     * ISSUE-0110: every supported untyped table-read boundary emits ONE
     * shared {@code $check(descriptor, value)} call carrying the spec
     * {@code RuntimeTypeDescriptor} of the expected type — one
     * convention for classes, nullable classes, nullable primitives,
     * arrays, nullable-element arrays, nullable arrays, and tables —
     * and no retired per-kind helper remains in the artifact.
     */
    private static void testSharedCheckSeam() {
        System.out.println("-- Shared descriptor-driven runtime-check seam (ISSUE-0110) --");
        Frontend f = compileFrontend("""
            class Point { x: int = 0; }
            export function test(): int {
              let p0: Point = { x: 1 };
              let ps0: Point[] = [];
              ps0[0] = p0;
              let holder: table = { p: p0, n: 5, xs: [1], ps: ps0, inner: { k: 2 } };
              let p: Point = holder.p;
              let maybe: Point | null = holder.p;
              let n: int | null = holder.n;
              let xs: int[] = holder.xs;
              let ys: (int | null)[] = holder.xs;
              let zs: int[] | null = holder.xs;
              let ps: Point[] = holder.ps;
              let qs: (Point | null)[] = holder.ps;
              let inner: table = holder.inner;
              let total: int = p.x + xs[0] + ys.length + ps.length
                  + qs.length;
              if (maybe !== null) { total = total + maybe.x; }
              if (n !== null) { total = total + n; }
              if (zs !== null) { total = total + zs.length; }
              return total;
            }
            """, "jvmtest-seam.deal");
        check(f.errors().isEmpty(), "seam fixture frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-seam.deal", "Main");
        check(!res.hasErrors(), "seam fixture codegen clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        String java = res.source();
        check(java.contains("$check(\"@Main/Point\", "),
            "class-typed read dispatches on the spec class descriptor");
        check(java.contains("$check(\"?@Main/Point\", "),
            "nullable class read dispatches on '?@Main/Point'");
        check(java.contains("$check(\"?int\", "),
            "nullable int read dispatches on '?int'");
        check(java.contains("$check(\"[int]\", "),
            "int[] read dispatches on '[int]'");
        check(java.contains("$check(\"[?int]\", "),
            "(int | null)[] read dispatches on '[?int]'");
        check(java.contains("$check(\"?[int]\", "),
            "int[] | null read dispatches on '?[int]'");
        check(java.contains("$check(\"[@Main/Point]\", "),
            "Point[] read dispatches on '[@Main/Point]'");
        check(java.contains("$check(\"[?@Main/Point]\", "),
            "(Point | null)[] read dispatches on '[?@Main/Point]'");
        check(java.contains("$check(\"table\", "),
            "table read dispatches on 'table'");
        check(occurrences(java, "static java.lang.Object $check(java.lang.String descriptor, java.lang.Object v)") == 1,
            "exactly one shared $check seam is emitted");
        check(!java.contains("$check$Table") && !java.contains("$checkNullable")
                && !java.contains("$check$IntArray"),
            "no retired per-kind boundary helper remains in the artifact");
        // The seam artifact is real Java: compile it with javac.
        Path dir = null;
        try {
            dir = Files.createTempDirectory("jvmtest_seam_");
            Files.writeString(dir.resolve("Main.java"), java);
            Files.writeString(dir.resolve("JvmConformanceRunner.java"),
                StubModuleResolver.buildJvmRunner(f.program(), "Main"));
            StringBuilder err = new StringBuilder();
            boolean ok = StubModuleResolver.compileWithJavac(dir,
                List.of("Main.java", "JvmConformanceRunner.java"), err);
            check(ok, "the seam artifact compiles with javac: " + err);
        } catch (IOException e) {
            fail("seam javac I/O: " + e);
        } finally {
            if (dir != null) {
                try {
                    Files.walk(dir).sorted(Comparator.reverseOrder())
                        .forEach(p -> { try { Files.deleteIfExists(p); }
                        catch (IOException ignored) {} });
                } catch (IOException ignored) {}
            }
        }
        System.out.println("  seam dispatch descriptors pinned");
    }

    /**
     * D1 origin-threading surface (jvm-canonical-error-snapshot-convergence):
     * every raising helper of the retained emitter carries the origin
     * (file/line/column) parameters and propagates them unchanged into
     * every raise it performs — the wrapped E8003/E8010 re-raises
     * included — and the short overloads pass the explicit absent sentinel
     * (null, -1, -1). The user-throw raise statements pass the real origin
     * (the per-artifact `__SRC` path constant plus compile-time
     * line/column literals); every other emitted raise carries an origin
     * argument whose value is the received parameter (inside a threaded
     * helper) or the sentinel literal (the classes whose per-site origin
     * literals have not landed yet).
     */
    private static void testOriginThreadingSurface() {
        System.out.println("-- D1 origin-threading surface --");
        Frontend f = compileFrontend("""
            export function test(): int {
              let xs: int[] = [1, 2];
              xs[1] = 3;
              let b: bytes = bytes(4);
              let v: int = b[0];
              let n: int = xs.length;
              try {
                throw { code: "E1", message: "boom" };
              } catch (e) {
                if (e.code !== "E1") { return -1; }
              }
              return xs[0] + v + n;
            }
            """, "jvmtest-origin-threading.deal");
        check(f.errors().isEmpty(),
            "origin-threading fixture frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-origin-threading.deal", "Main");
            check(!res.hasErrors(), "origin-threading fixture codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "static long checkInt(long v, java.lang.String oFile, int oLine, int oCol)"),
                    "checkInt carries the origin parameters");
                check(java.contains(
                        "static long intAdd(long a, long b) { return intAdd(a, b, null, -1, -1); }"),
                    "the int helper's short overload passes the explicit "
                        + "absent sentinel");
                check(java.contains(
                        "static $DealRt.Bytes bytesNew(long length) { return bytesNew(length, null, -1, -1); }"),
                    "the bytes constructor's short overload passes the "
                        + "explicit absent sentinel");
                check(java.contains(
                        "static $DealRt.Bytes bytesNew(long length, java.lang.String oFile, int oLine, int oCol)"),
                    "bytesNew carries the origin parameters");
                check(java.contains(
                        "throw new DealError(\"E8012\", \"bytes length must be non-negative\", oFile, oLine, oCol);"),
                    "the bytes-construction raise propagates the origin");
                check(java.contains(
                        "static long bytesGet($DealRt.Bytes b, long i, java.lang.String oFile, int oLine, int oCol)"),
                    "bytesGet carries the origin parameters");
                check(java.contains(
                        "static long __intArrayRead($DealRt.__IntArray a, long i, java.lang.String oFile, int oLine, int oCol, java.lang.String bFile, int bLine, int bCol)"),
                    "the int-array read helper carries the origin parameters "
                        + "(the index expression and the consumer boundary)");
                check(java.contains(
                        "static long __intArrayWrite($DealRt.__IntArray a, long i, long v, java.lang.String oFile, int oLine, int oCol)"),
                    "the int-array write helper carries the origin parameters");
                check(java.contains(
                        "static boolean booleanNotNull(java.lang.Boolean v, java.lang.String oFile, int oLine, int oCol)"),
                    "the boolean boundary helper carries the origin parameters");
                check(java.contains(
                        "static java.lang.Object $check(java.lang.String descriptor, java.lang.Object v, java.lang.String oFile, int oLine, int oCol)"),
                    "the shared $check seam carries the origin parameters");
                check(java.contains(
                        "static java.lang.Object $checkArray(java.lang.String descriptor, java.lang.Object v, java.lang.String oFile, int oLine, int oCol)"),
                    "the recursive $checkArray realization carries the "
                        + "origin parameters");
                check(java.contains(
                        "static java.lang.Object $hostCheckArray(java.lang.String descriptor, java.lang.Object v, java.lang.String oFile, int oLine, int oCol)"),
                    "the host-boundary array seam carries the origin "
                        + "parameters");
                check(java.contains(
                        "static $DealRt.__IntArray $dynamicIntArray(java.lang.Object v, java.lang.String arrayText, java.lang.String elemText, java.lang.String oFile, int oLine, int oCol)"),
                    "the dynamic array conversion carries the origin "
                        + "parameters and the closed element projections");
                check(java.contains(
                        "throw new DealError(\"E8003\", \"array element \" + (i + 1) + \" type mismatch\", oFile, oLine, oCol, elemText, $kindOf(a.get(i)), null, null);"),
                    "the wrapped E8003 dynamic-element re-raise propagates "
                        + "the origin and the element projection");
                check(java.contains(
                        "throw new DealError(\"E8010\", \"parameter \" + i + \" type mismatch: \" + __hostInnerMessage(d, v, inner), oFile, oLine, oCol, desc, __hostKind(v));"),
                    "the wrapped E8010 host-parameter re-raise propagates "
                        + "the origin with the closed inner reason text "
                        + "and the expected/actual projections");
                check(java.contains(
                        "throw new DealError(\"E8011\", \"missing host export '\" + name + \"' in module '\" + module + \"'\", oFile, oLine, oCol);"),
                    "the host load-time E8011 raise propagates the origin "
                        + "with the pinned canonical message");
                check(java.contains(
                        "throw new DealError(\"E1\", \"boom\", __SRC, 8, 5);"),
                    "the user-throw raise statement passes the throw "
                        + "keyword's span — the per-artifact source path "
                        + "constant and the compile-time line/column "
                        + "literals (the D3 user-throw origin)");
                check(java.contains("static java.lang.Object __hostCheck(java.lang.String desc, java.lang.Object v, java.lang.String fn, boolean completion) { return __hostCheck(desc, v, fn, completion, null, -1, -1); }"),
                    "the host return check's short overload passes the "
                        + "explicit absent sentinel");

                // Structural guarantee: every emitted DealError
                // constructor call carries an origin argument — either
                // the received oFile/oLine/oCol or the sentinel literal.
                int raises = 0;
                int originLess = 0;
                int idx = java.indexOf("new DealError(");
                while (idx >= 0) {
                    raises++;
                    int end = java.indexOf(';', idx);
                    String args = end < 0 ? java.substring(idx)
                        : java.substring(idx, end);
                    if (!args.contains("oFile") && !args.contains("null, -1, -1")
                            && !args.contains("__SRC")
                            && !args.contains("bFile")) {
                        originLess++;
                    }
                    idx = java.indexOf("new DealError(", idx + 1);
                }
                check(raises > 20, "the fixture artifact emits a substantial "
                    + "raise surface: raises = " + raises);
                check(originLess == 0, "every emitted raise carries an "
                    + "origin argument (file/line/column parameters, the "
                    + "per-artifact source path constant, or the explicit "
                    + "absent sentinel): origin-less = " + originLess);
            }
        }

        // The JSON runtime's raising helpers carry the same surface.
        Frontend j = compileFrontend("""
            import * as json from "std/json"
            export function test(): string { return json.stringify({ a: 1 }); }
            """, "jvmtest-origin-threading-json.deal");
        check(j.errors().isEmpty(),
            "origin-threading JSON fixture frontend clean: " + j.errors());
        if (j.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                j.program(), j.checkResult(),
                "jvmtest-origin-threading-json.deal", "Main");
            check(!res.hasErrors(), "origin-threading JSON fixture codegen "
                + "clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "static $DealRt.Table $jsonParse(java.lang.String s) { return $jsonParse(s, null, -1, -1); }"),
                    "$jsonParse's short overload passes the explicit "
                        + "absent sentinel");
                check(java.contains(
                        "static void __jsonAppend(java.lang.StringBuilder sb, java.lang.Object v, java.util.Set<java.lang.Object> stack, java.lang.String oFile, int oLine, int oCol)"),
                    "the JSON encoder recursion carries the origin "
                        + "parameters");
                check(java.contains(
                        "static java.lang.String __jsonQuote(java.lang.String s, java.lang.String oFile, int oLine, int oCol)"),
                    "the JSON string quoting helper carries the origin "
                        + "parameters");
                check(java.contains(
                        "throw new DealError(\"E8001\", \"value is not JSON-shaped\", oFile, oLine, oCol);"),
                    "the JSON shape raise propagates the origin");
                check(java.contains(
                        "throw new DealError(\"E8001\", \"cannot encode invalid UTF-8 as JSON\", oFile, oLine, oCol);"),
                    "the JSON invalid-UTF-8 raise propagates the origin");
            }
        }
        System.out.println("  origin-threading helper surface pinned");
    }

    /**
     * The ISSUE-0605 origin literals and the closed D4 projections at the
     * array/bytes index and member-read raise sites
     * (jvm-canonical-error-snapshot-convergence D3/D4): the array index
     * read and write carry the index-expression start, the bytes get/set
     * and the bytes(...) construction carry the index/call expression
     * start, the past-end element read carries the index expression as
     * the E8002 origin and the consumer's boundary-check span as the
     * E8001 origin with the closed expected "int" / actual "nil"
     * projection, and the table member read consumed by an annotated
     * binding raises at the declared contextual target annotation (never
     * the member access) through the canonical declared-boundary seam.
     * The consumer boundary origin's file component is the module's
     * emitted artifact class file ({@code Main.java}), which the lane's
     * deployment map normalizes to the canonical corpus-relative path.
     */
    private static void testErrorSnapshotOriginLiterals() throws Exception {
        System.out.println("-- Error-snapshot origin literals (ISSUE-0605) --");

        // Array read/write, bytes read/write, and the bytes(...)
        // construction carry their index/call expression starts; the
        // table member read carries the declared contextual annotation.
        Frontend f = compileFrontend("""
            export function main(): null {
              let xs: int[] = [1];
              let b: bytes = bytes(2);
              xs[0] = b[1];
              let n: int = b[2];
              b[0] = 7;
              let t: table = { v: "bad" };
              let r: int = t.v;
              return null;
            }
            """, "jvmtest-origin-emission.deal");
        check(f.errors().isEmpty(), "origin emission frontend clean: "
            + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-origin-emission.deal", "main");
            check(!res.hasErrors(), "origin emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "bytesNew(2L, \"jvmtest-origin-emission.deal\", "
                            + "3, 18)"),
                    "the bytes(...) construction raises at the call "
                        + "expression start (3:18)");
                check(java.contains(
                        "bytesGet(b, 1L, \"jvmtest-origin-emission.deal\", "
                            + "4, 11)"),
                    "the bytes index read raises at the index expression "
                        + "start (4:11)");
                check(java.contains(
                        "bytesGet(b, 2L, \"jvmtest-origin-emission.deal\", "
                            + "5, 16)"),
                    "an annotated-binding bytes read keeps the index "
                        + "expression (5:16) as its single origin — never "
                        + "the int annotation");
                check(java.contains(
                        "bytesSet(b, 0L, 7L, "
                            + "\"jvmtest-origin-emission.deal\", 6, 3)"),
                    "the bytes element write raises at the index "
                        + "expression start (6:3)");
                check(java.contains(
                        "__intArrayWrite(xs, 0L, bytesGet(b, 1L, "
                            + "\"jvmtest-origin-emission.deal\", 4, 11), "
                            + "\"jvmtest-origin-emission.deal\", 4, 3)"),
                    "the array element write raises at the index "
                        + "expression start (4:3)");
                check(java.contains(
                        "$check(\"int\", (t).get(\"v\"), "
                            + "\"Main.java\", 8, 10)"),
                    "the table member read raises at the declared "
                        + "contextual target annotation (8:10) — never "
                        + "the member access — through the canonical "
                        + "declared-boundary seam");
            }
        }

        // The past-end element read carries the index expression start
        // with the closed projection: message "expected int", expected
        // "int", actual "nil".
        Frontend p = compileFrontend("""
            export function test(): int {
              let xs: int[] = [1];
              return xs[99];
            }
            """, "jvmtest-pastend-emission.deal");
        check(p.errors().isEmpty(), "past-end emission frontend clean: "
            + p.errors());
        if (p.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                p.program(), p.checkResult(),
                "jvmtest-pastend-emission.deal", "main");
            check(!res.hasErrors(), "past-end emission codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "if (i >= (long) a.data.length) throw new "
                            + "DealError(\"E8001\", \"expected int\", "
                            + "bFile, bLine, bCol, \"int\", \"nil\", "
                            + "null, null);"),
                    "the past-end element read raises the closed "
                        + "projection (expected int / actual nil) at the "
                        + "consumer's boundary-check origin");
                check(java.contains(
                        "__intArrayRead(xs, 99L, "
                            + "\"jvmtest-pastend-emission.deal\", 3, 10, "
                            + "\"Main.java\", 3, 10)"),
                    "the past-end element read raises at the index "
                        + "expression start (3:10) when no declared "
                        + "annotation overrides the consumer span");
            }
        }

        // The past-end boundary failure of an array read consumed by an
        // ANNOTATED binding raises at the declared contextual target
        // annotation — the pinned `let value: int = values[2];` 8:14
        // convention the real lane enforces for
        // backend-runtime/source-location/036-runtime-source-array-oob.deal
        // and nested-array-oob-source.deal — while the index-expression
        // origin stays the read itself for the E8002 raise. The bytes
        // read keeps the index expression even under an annotated
        // binding (the pinned bytes-negative-read-error 8:20
        // convention), so the two origins never collapse into one.
        Frontend c = compileFrontend("""
            export function test(): null {
              let values: int[] = [1];
              let value: int = values[2];
              let b: bytes = bytes(1);
              let v: int = b[5];
              return null;
            }
            """, "jvmtest-contextual-read-emission.deal");
        check(c.errors().isEmpty(), "contextual read emission frontend "
            + "clean: " + c.errors());
        if (c.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                c.program(), c.checkResult(),
                "jvmtest-contextual-read-emission.deal", "main");
            check(!res.hasErrors(), "contextual read emission codegen "
                + "clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                check(java.contains(
                        "__intArrayRead(values, 2L, "
                            + "\"jvmtest-contextual-read-emission.deal\", "
                            + "3, 20, "
                            + "\"Main.java\", 3, 14)"),
                    "the annotated-binding past-end read carries the "
                        + "index expression (3:20) as the E8002 origin and "
                        + "the declared int annotation (3:14) as the "
                        + "E8001 boundary origin");
                check(java.contains(
                        "bytesGet(b, 5L, "
                            + "\"jvmtest-contextual-read-emission.deal\", "
                            + "5, 16)"),
                    "the bytes read keeps the index expression (5:16) as "
                        + "its single origin even under an annotated "
                        + "binding");
            }
        }

        // The comparison-operand read shape (the boxed helper path):
        // the negative-index E8002 raised by the boxed helper carries
        // the read's index-expression origin, exactly like the
        // element-typed read the same site lowers for a typed target
        // (review cycle 2, finding 1 — the sentinel call form is gone).
        String boxedReadSource = """
            export function test(): boolean {
              let xs: int[] = [1];
              return xs[-1] === 5;
            }
            """;
        Frontend x = compileFrontend(boxedReadSource,
            "jvmtest-boxed-read-origin-emission.deal");
        check(x.errors().isEmpty(), "boxed read origin emission frontend "
            + "clean: " + x.errors());
        if (x.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                x.program(), x.checkResult(),
                "jvmtest-boxed-read-origin-emission.deal", "main");
            check(!res.hasErrors(), "boxed read origin emission codegen "
                + "clean: " + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                // ISSUE-0604 D3 threads the unary minus's own origin
                // into the index expression, so the boxed call carries
                // both origins: the read (3:10) for the E8002 raise and
                // the negation (3:13) for its own checkInt gate.
                check(java.contains(
                        "__intArrayReadBoxed(xs, intNeg(1L, "
                            + "\"jvmtest-boxed-read-origin-emission.deal\", "
                            + "3, " + columnOf(boxedReadSource, 3, "-1")
                            + "), "
                            + "\"jvmtest-boxed-read-origin-emission.deal\", "
                            + "3, " + columnOf(boxedReadSource, 3, "xs")
                            + ")"),
                    "the comparison-operand read passes the index "
                        + "expression origin (3:10) into the boxed "
                        + "helper call — never the span-absent sentinel: "
                        + emittedLine(java, "__intArrayReadBoxed"));
                check(!java.contains("__intArrayReadBoxed(xs, intNeg(1L));"),
                    "the sentinel two-argument boxed call form is gone: "
                        + emittedLine(java, "__intArrayReadBoxed"));
            }
        }
    }

    /**
     * The emitted-helper collision guard against the origin-threading
     * overloads (ISSUE-0605): a DEAL function whose mapped parameter
     * list equals an emitted helper overload exactly is rejected with
     * E6000, so no duplicate Java method can be emitted. Under
     * {@code DEAL_V1_2_INT32} the origin parameters are Java
     * {@code int}s, reachable from DEAL's int mapping; under
     * {@code LEGACY_SAFE_INT} the same declaration maps to the long
     * carrier and is therefore a legal overload (the helper's origin
     * parameters are unreachable from DEAL's legacy int mapping) — the
     * full legacy pipeline must compile and run it.
     */
    private static void testOriginThreadingHelperCollisions() throws Exception {
        System.out.println("-- Emitted-helper collision guard: origin-threading "
            + "overloads (ISSUE-0605) --");

        // int32: the mapped parameter list equals the emitted
        // origin-threading bytesGet/bytesSet helpers exactly.
        String bytesGetCollision = """
            function bytesGet(b: bytes, i: int, f: string, l: int, c: int): int { return b[i]; }
            export function main(): null { return null; }
            export function test(): int { return bytesGet(bytes(1), 0, "x", 0, 0); }
            """;
        Frontend f = compileFrontend(bytesGetCollision,
            "jvmtest-bytesget-origin-collision.deal");
        check(f.errors().isEmpty(),
            "bytesGet origin-collision frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-bytesget-origin-collision.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("collides with the emitted "
                            + "runtime helper 'bytesGet'")),
                "the int32 bytesGet origin-threading overload collision "
                    + "is rejected E6000 (never a duplicate Java method): "
                    + res.diagnostics());
        }

        String bytesSetCollision = """
            function bytesSet(b: bytes, i: int, v: int, f: string, l: int, c: int): int { b[i] = v; return 1; }
            export function main(): null { return null; }
            export function test(): int { return bytesSet(bytes(1), 0, 1, "x", 0, 0); }
            """;
        Frontend s = compileFrontend(bytesSetCollision,
            "jvmtest-bytesset-origin-collision.deal");
        check(s.errors().isEmpty(),
            "bytesSet origin-collision frontend clean: " + s.errors());
        if (s.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                s.program(), s.checkResult(),
                "jvmtest-bytesset-origin-collision.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(res.hasErrors() && res.diagnostics().stream()
                    .anyMatch(d -> "E6000".equals(d.code())
                        && d.message().contains("collides with the emitted "
                            + "runtime helper 'bytesSet'")),
                "the int32 bytesSet origin-threading overload collision "
                    + "is rejected E6000 (never a duplicate Java method): "
                    + res.diagnostics());
        }

        // The four-parameter negative control maps to no emitted
        // overload: the declaration stays legal.
        Frontend neg = compileFrontend("""
            function bytesGet(b: bytes, i: int, f: string, l: int): int { return b[i]; }
            export function main(): null { return null; }
            export function test(): int { return bytesGet(bytes(1), 0, "x", 0); }
            """, "jvmtest-bytesget-negative-control.deal");
        check(neg.errors().isEmpty(), "negative-control frontend clean: "
            + neg.errors());
        if (neg.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                neg.program(), neg.checkResult(),
                "jvmtest-bytesget-negative-control.deal", "main",
                Map.of(), Map.of(), Map.of(), true,
                SemanticProfile.DEAL_V1_2_INT32);
            check(!res.hasErrors(), "the four-parameter bytesGet is a legal "
                + "overload under int32: " + res.diagnostics());
        }

        // Legacy: the same origin-bearing declaration maps to the long
        // carrier (never the helper's int origin parameters) — a legal
        // overload the full legacy pipeline must compile and run.
        ExecResult legacy = runLegacyProject("""
            function bytesGet(b: bytes, i: int, f: string, l: int, c: int): int { return b[i] + l + c; }
            export function main(): null { return null; }
            export function test(): int { return bytesGet(bytes(3), 1, "x", 2, 3); }
            """, "bytesget_legacy_origin_overload");
        check(legacy.exitCode() == 0 && legacy.output().contains("5"),
            "the legacy no-collision overload javac-compiles and runs "
                + "(the helper's int origin parameters are unreachable "
                + "from DEAL's legacy int mapping): " + legacy.output());
    }

    /**
     * ISSUE-0606 declared-boundary origin emission
     * (jvm-canonical-error-snapshot-convergence D3/D4/D6): the emitted
     * artifacts carry the authoritative declared-boundary origin
     * literals — the callee's declared parameter-type annotation for a
     * call argument, the caller's return expression for a return
     * boundary, the binding's declared contextual annotation for a
     * typed binding (the E8003 wrap included), the caller's declared
     * function-type annotation for the typed-binding E8010 shape, the
     * callee's declared parameter annotation for the call-argument
     * E8010 shape, the call expression for a stdlib parameter
     * boundary, and the declaring module's parameter annotation across
     * the D6 import seam — with the closed expected/actual projections
     * (the runtime-kind vocabulary, the descriptor texts). The
     * sanctioned span-less time raise keeps the 2-argument checkInt
     * route.
     */
    private static void testDeclaredBoundaryOrigins() throws Exception {
        System.out.println("-- Declared-boundary origin emission (ISSUE-0606) --");

        Frontend f = compileFrontend("""
            import * as console from "std/console"
            import * as json from "std/json"
            import * as time from "std/time"

            class Box { value: int = 0; }

            function needInt(x: int): int { return x; }

            export function test_origins(): int {
              let t: table = { value: "bad" };
              console.log(t.value);
              let g: (x: int) => int = t.f;
              let n: int = time.nowMillis();
              return needInt(t.value);
            }

            export function test_return(): Box {
              let holder: table = { item: 1 };
              return holder.item;
            }

            export function test_arr(): int {
              let t: table = json.parse("{\\"values\\":[1,\\"bad\\"]}");
              let xs: int[] = t.values;
              return xs[0];
            }
            """, "jvmtest-declared-boundaries.deal");
        check(f.errors().isEmpty(),
            "declared-boundaries fixture frontend clean: " + f.errors());
        if (f.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-declared-boundaries.deal", "Main",
                SemanticProfile.DEAL_V1_2_INT32);
            check(!res.hasErrors(),
                "declared-boundaries fixture codegen clean: "
                    + res.diagnostics());
            if (!res.hasErrors()) {
                String java = res.source();
                // D2: the complete DEALRuntimeError field surface.
                check(java.contains("final java.lang.String file;")
                        && java.contains("final int line;")
                        && java.contains("final int column;")
                        && java.contains("final java.lang.String expected;")
                        && java.contains("final java.lang.String actual;")
                        && java.contains("final java.lang.Integer frames;")
                        && java.contains("final java.lang.String cause;"),
                    "the emitted DealError carries the closed "
                        + "DEALRuntimeError field surface");
                // D3: the callee's declared parameter annotation is the
                // call-argument boundary origin (needInt's `int` at
                // 7:21).
                check(java.contains("$check(\"int\", (t).get(\"value\"), "
                        + "\"Main.java\", 7, 21)"),
                    "the callee's declared parameter annotation is the "
                        + "call-argument boundary origin: " + java);
                // D3: the caller's return expression is the class-return
                // boundary origin (`holder.item` at 19:10).
                check(java.contains("$check(\"@Main/Box\", "
                        + "(holder).get(\"item\"), \"Main.java\", 19, "
                        + "10)"),
                    "the caller's return expression is the class-return "
                        + "boundary origin: " + java);
                // D3: the caller's declared function-type annotation is
                // the typed-binding E8010 origin (`(x: int) => int` at
                // 12:10).
                check(java.contains("$check(\"(int)->int\", "
                        + "(t).get(\"f\"), \"Main.java\", 12, 10)"),
                    "the caller's declared function-type annotation is "
                        + "the typed-binding E8010 origin: " + java);
                // D3: the binding's declared contextual array annotation
                // is the E8003 wrap origin (`int[]` at 24:11).
                check(java.contains("$check(\"[int]\", __t0, "
                        + "\"Main.java\", 24, 11)"),
                    "the declared contextual array annotation is the "
                        + "E8003 wrap origin: " + java);
                // D3: the stdlib call expression is the declared-
                // parameter boundary origin (`console.log(...)` at
                // 11:3).
                check(java.contains("$check(\"string\", "
                        + "(t).get(\"value\"), \"Main.java\", 11, 3)"),
                    "the stdlib call expression is the declared-"
                        + "parameter boundary origin: " + java);
                // D5: the locked time selector's declared-int boundary
                // stays span-less (the 2-argument checkInt route).
                check(java.contains("checkInt((java.lang.System"
                        + ".currentTimeMillis() / 1000L) * 1000L)"),
                    "the sanctioned time raise keeps the span-less "
                        + "checkInt route: " + java);
                // D4: the closed projections and the runtime-kind
                // vocabulary.
                check(java.contains("throw new DealError(\"E8001\", "
                        + "\"expected int\", oFile, oLine, oCol, \"int\", "
                        + "$kindOf(v), null, null);")
                        && java.contains("if (v == null) return \"nil\";")
                        && java.contains("if (v instanceof "
                            + "java.lang.String) return \"string\";")
                        && java.contains("if (v instanceof "
                            + "java.lang.Double) return \"number\";"),
                    "the shared seam carries the closed expected/actual "
                        + "projections and the runtime-kind vocabulary");
                check(java.contains("throw new DealError(\"E8003\", "
                        + "\"array element \" + (i + 1) + \" type "
                        + "mismatch\", oFile, oLine, oCol, elemText, "
                        + "$kindOf(a.get(i)), null, null);"),
                    "the array-element wrap carries the origin and the "
                        + "element descriptor/kind projections");
            }
        }

        // D3 (call-argument E8010 shape): a function-typed argument
        // whose static signature is narrower than the callee's declared
        // parameter annotation raises E8010 in the checking wrapper,
        // carrying the declared annotation's origin (line 3, column 20)
        // and the closed descriptor projections.
        Frontend e8010F = compileFrontend("""
            function inc(x: int): int { return x; }

            function apply2(f: (a: int, b: string) => int, v: int): int { return f(v, "s"); }

            export function test(): int {
              return apply2(inc, 1);
            }
            """, "jvmtest-e8010-callarg.deal");
        check(e8010F.errors().isEmpty(),
            "E8010 call-argument fixture frontend clean: "
                + e8010F.errors());
        if (e8010F.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult e8010Res = JvmBackend.generate(
                e8010F.program(), e8010F.checkResult(),
                "jvmtest-e8010-callarg.deal", "Main",
                SemanticProfile.DEAL_V1_2_INT32);
            check(!e8010Res.hasErrors(),
                "E8010 call-argument fixture codegen clean: "
                    + e8010Res.diagnostics());
            if (!e8010Res.hasErrors()) {
                check(e8010Res.source().contains(
                        "if (!checkSig(\"(int,string)->int\", "
                            + "\"(int)->int\")) { throw new DealError("
                            + "\"E8010\", \"function signature mismatch: "
                            + "expected (int,string)->int, got (int)->int\", "
                            + "\"Main.java\", 3, 20, \"(int,string)->int\", "
                            + "\"(int)->int\", null, null); }"),
                    "the E8010 call-argument shape carries the callee's "
                        + "declared parameter annotation origin and the "
                        + "closed descriptor projections: "
                        + e8010Res.source());
            }
        }

        // D6: an imported companion's declared parameter annotation is
        // the cross-module boundary origin — the declaring module's
        // artifact file, never the caller's. The two-module project
        // flows through the production orchestrator, so the assertion
        // also proves the import-context seam carries the companion's
        // function declarations into the importing module's codegen.
        writeFile("src/lib_origins.deal", """
            export class Box { value: int = 0; }
            export function needBox(b: Box): int { return b.value; }
            """);
        writeFile("src/entry_origins.deal", """
            import * as Lib from "./lib_origins"
            export function main(): null { return null; }
            export function run(): int {
              let holder: table = { item: 1 };
              return Lib.needBox(holder.item);
            }
            """);
        Path originsEntry = tmpDir.get().resolve("src/entry_origins.deal")
            .toAbsolutePath();
        Path originsOut = tmpDir.get().resolve("build/canonical_origins");
        List<Path> originsRoots = List.of(
            tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator originsOrchestrator =
            new CompilationOrchestrator(
            originsEntry,
            originsOut,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            originsRoots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean originsOk = originsOrchestrator.compile();
        check(originsOk, "canonical-origins project compiles: "
            + originsOrchestrator.diagnostics());
        if (originsOk) {
            Path originsArtifact = originsOut.resolve("Entry_origins.java");
            check(Files.exists(originsArtifact),
                "the importing module's artifact exists");
            if (Files.exists(originsArtifact)) {
                String originsEmitted = Files.readString(originsArtifact);
                check(originsEmitted.contains(
                        "Lib_origins.$check(\"@src/Box\", "
                            + "(holder).get(\"item\"), "
                            + "\"Lib_origins.java\", 2, 28)"),
                    "the imported companion's declared parameter "
                        + "annotation is the cross-module boundary origin "
                        + "(the declaring module's artifact): "
                        + originsEmitted);
            }
        }
    }

    /**
     * The user-throw origin leaf (jvm-canonical-error-snapshot-convergence
     * D3's user-throw/rethrow row and D5's production-side split): the
     * emitted Error literal in a throw position carries the `throw`
     * keyword's DEAL span — the per-artifact source path constant plus the
     * compile-time start line/column literals — so the thrown object names
     * the original site; the rethrow re-raises the SAME DealError
     * (exactly one construction, never a fabricated re-raise site); a
     * companion module's artifact carries the companion's OWN source path
     * constant; and the sanctioned span-less raise stays span-less — the
     * locked time selector's declared-int boundary keeps the explicit
     * absent-origin entry (no origin literal is ever added at that site)
     * while the throw site carries one.
     */
    private static void testUserThrowOrigins() throws Exception {
        System.out.println("-- User-throw origins: throw-keyword span, "
            + "rethrow object preservation, module constant, D5 split --");

        // The throw-keyword span (line 3, column 5 of the fixture source)
        // and the rethrow's object identity: the literal constructs
        // exactly one DealError carrying the throw site, and the
        // catch-side rethrow emits a plain rethrow of the SAME object, so
        // the original origin survives the catch boundary.
        String rethrowSource = """
            export function test_rethrow_preserves_code(): null {
              try {
                throw { code: "ORIGIN_PROBE", message: "boom" };
              } catch (e) {
                throw e;
              }
              return null;
            }
            export function main(): null { return null; }
            """;
        String rethrowJava = legacyArtifact(rethrowSource, "throw_origin");
        check(rethrowJava.contains(
                "throw new DealError(\"ORIGIN_PROBE\", \"boom\", __SRC, 3, 5);"),
            "the object-literal throw passes the throw keyword's span "
                + "(line 3, column 5) through the per-artifact path "
                + "constant: " + rethrowJava.lines()
                    .filter(l -> l.contains("new DealError"))
                    .findFirst().orElse("<missing>"));
        check(rethrowJava.contains(
                "static final java.lang.String __SRC = "
                    + "\"jvmtest-throw_origin.deal\";"),
            "the artifact carries its own DEAL source path constant");
        check(countOccurrences(rethrowJava,
                "new DealError(\"ORIGIN_PROBE\", \"boom\", __SRC, 3, 5)") == 1,
            "exactly one DealError construction exists for the thrown "
                + "literal (the rethrow re-raises the same object, never "
                + "a fabricated re-raise site)");
        check(rethrowJava.contains("throw (e);"),
            "the rethrow re-raises the caught DealError object unchanged: "
                + rethrowJava.lines().filter(l -> l.contains("throw ("))
                    .findFirst().orElse("<missing>"));

        // A companion module's artifact carries the COMPANION's own
        // source path constant — the same throw shape under a different
        // module path, so the captured file names the module that
        // actually raised (the lane normalizes it to the corpus path).
        Frontend companion = compileFrontend("""
            export function fail(): null {
              throw { code: "COMPANION_PROBE", message: "fail" };
            }
            """, "companion_lib.deal");
        check(companion.errors().isEmpty(),
            "companion fixture frontend clean: " + companion.errors());
        if (companion.errors().isEmpty()) {
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                companion.program(), companion.checkResult(),
                "companion_lib.deal", "lib");
            check(!res.hasErrors(), "companion fixture codegen clean: "
                + res.diagnostics());
            if (!res.hasErrors()) {
                check(res.source().contains(
                        "static final java.lang.String __SRC = "
                            + "\"companion_lib.deal\";"),
                    "the companion artifact carries the companion's own "
                        + "source path constant, never the importer's");
                check(res.source().contains(
                        "throw new DealError(\"COMPANION_PROBE\", \"fail\", "
                            + "__SRC, 2, 3);"),
                    "the companion's throw carries the companion file "
                        + "constant and its own span: " + res.source().lines()
                            .filter(l -> l.contains("new DealError"))
                            .findFirst().orElse("<missing>"));
            }
        }

        // The D5 split inside one artifact: the locked time selector's
        // declared-int boundary keeps the explicit absent-origin entry
        // while the throw site in the same artifact carries the origin
        // literal.
        String splitSource = """
            import * as time from "std/time"
            export function main(): null { return null; }
            export function test_split(): null {
              let t: int = time.nowMillis();
              throw { code: "SPLIT_PROBE", message: "split" };
            }
            """;
        String splitJava = int32Artifact(splitSource, "throw_split");
        check(splitJava.contains(
                "int t = checkInt(" + RETAINED_TIME_EXPRESSION + ");"),
            "the sanctioned span-less raise takes the explicit "
                + "absent-origin entry at the declared-int time boundary: "
                + splitJava.lines().filter(l -> l.contains("checkInt("))
                    .findFirst().orElse("<missing>"));
        check(!splitJava.contains(
                "checkInt(" + RETAINED_TIME_EXPRESSION + ", "),
            "no origin literal is ever added at the time boundary (the "
                + "span-less shape is permanent)");
        check(splitJava.contains(
                "throw new DealError(\"SPLIT_PROBE\", \"split\", "
                    + "__SRC, 5, 3);"),
            "the throw site in the same artifact carries the origin "
                + "literal: " + splitJava.lines()
                    .filter(l -> l.contains("new DealError"))
                    .findFirst().orElse("<missing>"));
        check(!splitJava.contains("DealError(\"SPLIT_PROBE\", \"split\", null"),
            "the throw site never falls back to the absent sentinel");
        System.out.println("  user-throw origins pinned");
    }

    private static void testSharedCheckSeamCanonicalParsing()
            throws Exception {
        System.out.println("-- Shared $check seam: canonical parsing precedes the legacy '?' shortcut (ISSUE-0315) --");
        Frontend f = compileFrontend("""
            export function test(): int { return 1; }
            """, "jvmtest-seam-canonical.deal");
        check(f.errors().isEmpty(),
            "seam-canonical fixture frontend clean: " + f.errors());
        if (!f.errors().isEmpty()) return;
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-seam-canonical.deal",
            "Main");
        check(!res.hasErrors(),
            "seam-canonical fixture codegen clean: " + res.diagnostics());
        if (res.hasErrors()) return;
        // The probe runner drives the emitted $check(descriptor, value)
        // seam directly: every parse-rejected spelling must raise E8001
        // with the pinned defensive message even for a NULL carrier (the
        // retired '?' shortcut would have passed ?null/?[]/?/?int[] with
        // null); canonical ? forms still pass null through.
        StringBuilder runner = new StringBuilder();
        runner.append("public final class CheckSeamProbeRunner {\n");
        runner.append("    public static void main(String[] args) {\n");
        runner.append("        java.lang.String[] spells = {\"?null\", \"?[]\", \"?\", \"?int[]\", \"int[]\", \"string|null\", \"(string,...int[])\", \"Error\", \"User\", \"@src.models.User\", \"@a/b.C\", \"@Foo\", \"??int\"};\n");
        runner.append("        for (java.lang.String s : spells) {\n");
        runner.append("            try {\n");
        runner.append("                Main.$check(s, null);\n");
        runner.append("                System.out.println(\"PASSED: \" + s);\n");
        runner.append("            } catch (Main.DealError e) {\n");
        runner.append("                System.out.println(\"REJECTED: \" + s + \" | \" + e.code + \" | \" + e.getMessage());\n");
        runner.append("            }\n");
        runner.append("        }\n");
        runner.append("        try {\n");
        runner.append("            System.out.println(\"ALPH_SPACE: \" + Main.__canonical(\"@a b/c\"));\n");
        runner.append("            System.out.println(\"ALPH_ASTRAL: \" + Main.__canonical(\"@\" + java.lang.Character.toString(0x1F600) + \"/User\"));\n");
        runner.append("            System.out.println(\"ALPH_LONE_HI: \" + Main.__canonical(\"@a\" + (char)0xD83D + \"/b\"));\n");
        runner.append("            System.out.println(\"ALPH_LONE_LO: \" + Main.__canonical(\"@a\" + (char)0xDE00 + \"/b\"));\n");
        runner.append("        } catch (Main.DealError e) {\n");
        runner.append("            System.out.println(\"ALPH_FAIL: \" + e.code + \" | \" + e.getMessage());\n");
        runner.append("        }\n");
        runner.append("        try {\n");
        runner.append("            Main.$check(\"@a b/c\", null);\n");
        runner.append("            System.out.println(\"SPACE_CHECK: none\");\n");
        runner.append("        } catch (Main.DealError e) {\n");
        runner.append("            System.out.println(\"SPACE_CHECK: \" + e.code + \" | \" + e.getMessage());\n");
        runner.append("        }\n");
        runner.append("        try {\n");
        runner.append("            Main.$check(\"@\" + java.lang.Character.toString(0x1F600) + \"/User\", null);\n");
        runner.append("            System.out.println(\"ASTRAL_CHECK: none\");\n");
        runner.append("        } catch (Main.DealError e) {\n");
        runner.append("            System.out.println(\"ASTRAL_CHECK: \" + e.code + \" | \" + e.getMessage());\n");
        runner.append("        }\n");
        runner.append("        try {\n");
        runner.append("            System.out.println(\"CANON_OK: ?int -> \" + (Main.$check(\"?int\", null) == null));\n");
        runner.append("            System.out.println(\"CANON_OK: ?[int] -> \" + (Main.$check(\"?[int]\", null) == null));\n");
        runner.append("            System.out.println(\"CANON_OK: ?(int)->int -> \" + (Main.$check(\"?(int)->int\", null) == null));\n");
        runner.append("            System.out.println(\"CANON_OK: ?@Main/Point -> \" + (Main.$check(\"?@Main/Point\", null) == null));\n");
        runner.append("        } catch (Main.DealError e) {\n");
        runner.append("            System.out.println(\"CANON_FAIL: \" + e.code + \" | \" + e.getMessage());\n");
        runner.append("        }\n");
        runner.append("        try {\n");
        runner.append("            Main.$check(\"?int\", \"x\");\n");
        runner.append("            System.out.println(\"MISMATCH: none\");\n");
        runner.append("        } catch (Main.DealError e) {\n");
        runner.append("            System.out.println(\"MISMATCH: \" + e.code);\n");
        runner.append("        }\n");
        runner.append("    }\n");
        runner.append("}\n");
        Path dir = null;
        try {
            dir = Files.createTempDirectory("jvmtest_seam_canonical_");
            Files.writeString(dir.resolve("Main.java"), res.source());
            Files.writeString(dir.resolve("CheckSeamProbeRunner.java"),
                runner.toString());
            StringBuilder err = new StringBuilder();
            boolean ok = StubModuleResolver.compileWithJavac(dir,
                List.of("Main.java", "CheckSeamProbeRunner.java"), err);
            check(ok, "the seam-canonical artifact compiles with javac: "
                + err);
            if (!ok) return;
            ProcessBuilder java = new ProcessBuilder("java", "-cp",
                dir.toString(), "CheckSeamProbeRunner");
            java.redirectErrorStream(true);
            Process p = java.start();
            String out = new String(p.getInputStream().readAllBytes())
                .trim();
            int exit = p.waitFor();
            check(exit == 0, "seam-canonical probe exits 0: " + out);
            for (String spelling : List.of("?null", "?[]", "?", "?int[]",
                    "int[]", "string|null", "(string,...int[])", "Error",
                    "User", "@src.models.User", "@a/b.C", "@Foo", "??int")) {
                check(out.contains("REJECTED: " + spelling + " | E8001 | "
                        + "internal: cannot parse type descriptor: "
                        + spelling),
                    "parse-rejected spelling '" + spelling
                        + "' raises E8001 even for a null carrier: " + out);
                check(!out.contains("PASSED: " + spelling),
                    "parse-rejected spelling '" + spelling
                        + "' never passes: " + out);
            }
            check(out.contains("CANON_OK: ?int -> true"),
                "canonical '?int' passes null: " + out);
            check(out.contains("CANON_OK: ?[int] -> true"),
                "canonical '?[int]' passes null: " + out);
            check(out.contains("CANON_OK: ?(int)->int -> true"),
                "canonical '?(int)->int' passes null: " + out);
            check(out.contains("CANON_OK: ?@Main/Point -> true"),
                "canonical '?@Main/Point' passes null: " + out);
            check(out.contains("MISMATCH: E8001"),
                "a wrong-kind value against a canonical descriptor keeps"
                    + " the pinned E8001: " + out);
            check(out.contains("ALPH_SPACE: false"),
                "space-bearing class-atom component fails __canonical: "
                    + out);
            check(out.contains("ALPH_ASTRAL: true"),
                "astral scalar in a non-final component passes __canonical: "
                    + out);
            check(out.contains("ALPH_LONE_HI: false"),
                "lone high surrogate rejected by __canonical: " + out);
            check(out.contains("ALPH_LONE_LO: false"),
                "lone low surrogate rejected by __canonical: " + out);
            check(out.contains("SPACE_CHECK: E8001 | internal: cannot parse"
                    + " type descriptor: @a b/c"),
                "space-bearing atom raises the pinned E8001 defensive"
                    + " parse message: " + out);
            String astralAtom = "@" + new String(Character.toChars(0x1F600))
                + "/User";
            check(out.contains("ASTRAL_CHECK: E8001 | expected " + astralAtom),
                "canonical astral atom passes parsing and reaches the"
                    + " matcher fallback (the closed boundary message"
                    + " names the expected descriptor; the actual kind"
                    + " rides the error field): " + out);
        } catch (IOException e) {
            fail("seam-canonical javac/java I/O: " + e);
        } finally {
            if (dir != null) {
                try {
                    Files.walk(dir).sorted(Comparator.reverseOrder())
                        .forEach(p -> { try { Files.deleteIfExists(p); }
                        catch (IOException ignored) {} });
                } catch (IOException ignored) {}
            }
        }
        System.out.println("  $check canonical parsing pins verified");
    }


    private static void testNullableSlice() throws Exception {
        System.out.println("-- Nullable slice (ISSUE-0108): boxed representation, narrowing, nullable arrays --");

        ExecResult flow = compileAndRunJvm("""
            class Holder {
              i: int | null = 1;
              s: string | null = null;
            }
            function pick(when: int, y: int | null): int | null {
              if (when === 0) { return null; }
              return y;
            }
            export function test(): int {
              let n: int | null = 5;
              let r: int = 0;
              if (n !== null) { r = n; }
              let m: int | null = null;
              if (m === null) { r = r + 10; } else { r = 99; }
              let s: string | null = "ab";
              if (s !== null) { if (s + "c" === "abc") { r = r + 1; } }
              let b: boolean | null = true;
              if (b !== null) { if (b) { r = r + 1; } }
              let xs: int[] | null = [1, 2];
              if (xs !== null) { r = r + xs[0] + xs[1] + xs.length; }
              let ys: (int | null)[] = [];
              ys[0] = null;
              ys[1] = 7;
              let y0: int | null = ys[0];
              if (y0 === null) { r = r + 1; }
              let y1: int | null = ys[1];
              if (y1 !== null) { r = r + y1; }
              let p: int | null = pick(3, 20);
              if (p !== null) { r = r + p; }
              let z: int | null = pick(0, 1);
              if (z === null) { r = r + 1; }
              let h: Holder = {};
              let hi: int | null = h.i;
              if (hi !== null) { r = r + hi; }
              h.s = "x";
              let hs: string | null = h.s;
              if (hs !== null) { if (hs === "x") { r = r + 1; } }
              let t: table = { v: 2 };
              let tv: int | null = t.v;
              if (tv !== null) { r = r + tv; }
              return r;
            }
            """, "nullable-flow");
        check(flow.exitCode() == 0, "nullable flow runs clean: " + flow.output());
        check(flow.output().contains("55"), "nullable flow value 55: " + flow.output());

        ExecResult neg = compileAndRunJvm("""
            export function test(): int {
              let ys: (int | null)[] = [];
              let a: int | null = ys[-1];
              if (a === null) { return 0; }
              return 1;
            }
            """, "nullable-neg-index");
        check(neg.output().contains("DEAL_ERROR_CODE: E8002"),
            "negative index into (int | null)[] raises E8002: " + neg.output());

        record Gate(String what, String source) {}
        List<Gate> gates = List.of(
            new Gate("nullable table type", """
                export function test(): null {
                  let t: table | null = null;
                }
                """),
            new Gate("array of nullable table elements", """
                export function test(): null {
                  let xs: (table | null)[] = [];
                }
                """)
        );
        for (Gate g : gates) {
            Frontend f = compileFrontend(g.source(), "jvmtest-nullable-gate.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept nullable gate '" + g.what()
                    + "' (the backend rejects it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-nullable-gate.deal", "main");
            check(res.hasErrors(), "backend rejects " + g.what());
            check(res.diagnostics().stream().anyMatch(d -> "E6000".equals(d.code())),
                "E6000 diagnostic for " + g.what() + ": " + res.diagnostics());
        }

        // ISSUE-0102: optional and class-typed class fields promoted out
        // of the E6000 gate — they now compile (and run through the
        // class fixtures above).
        List<Gate> promoted = List.of(
            new Gate("optional class field", """
                class Point { x?: int; }
                export function test(): int { return 1; }
                """),
            new Gate("class-typed class field", """
                class Inner { v: int = 0; }
                class Outer { inner: Inner = {}; }
                export function test(): int { return 1; }
                """)
        );
        for (Gate g : promoted) {
            Frontend f = compileFrontend(g.source(), "jvmtest-nullable-gate.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept promoted gate '" + g.what()
                    + "': " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(
                f.program(), f.checkResult(),
                "jvmtest-nullable-gate.deal", "main");
            check(!res.hasErrors(),
                "backend now accepts " + g.what() + ": " + res.diagnostics());
        }
    }

    /** An import of a COMPILED project module (ISSUE-0096) is supported by
     * the orchestrator's JVM path — even when the import is never used — and
     * the imported module's load-time side effects still run (the import
     * emits the {@code __init$} initialization trigger exactly where
     * LuaJIT runs require). */
    private static void testOrchestratorJvmImportSupported() throws Exception {
        System.out.println("-- Orchestrator: unused project-module import runs load-time code --");

        // v1.2: the imported module's load-time side effect moves inside
        // an exported function (module-level statements were removed); the
        // load-time trigger surface itself is exercised by the
        // init-trigger fixture in the backend conformance suite.
        writeFile("src/other.deal", """
            import * as console from "std/console"
            export function unused(): int { return 1; }
            export function announce(): null { console.log("other-module-ran"); }
            """);
        writeFile("src/entry.deal", """
            import * as m from "./other"
            export function main(): null { return null; }
            export function run(): int { return 1; }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/import_supported");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "unused project-module import compiles: "
            + orchestrator.diagnostics());
        if (!success) return;

        Path entryArtifact = outputDir.resolve("Entry.java");
        Path otherArtifact = outputDir.resolve("Other.java");
        check(Files.exists(entryArtifact), "entry artifact written");
        check(Files.exists(otherArtifact), "imported module artifact written");

        if (Files.exists(entryArtifact) && Files.exists(otherArtifact)) {
            String java = Files.readString(entryArtifact);
            check(java.contains("Other.__init$();"),
                "the import emits the init trigger for the imported class");
            check(java.contains("static {"),
                "the trigger sits in a load-time static block");

            // The emitted artifacts must be real: javac + java run the
            // imported module's init trigger even though the alias is
            // never used (v1.2: module top level holds only declarations,
            // so the only load-time work is the imported module's own
            // initialization).
            Files.writeString(outputDir.resolve("JvmConformanceRunner.java"),
                StubModuleResolver.buildJvmRunner(
                    parseProgram("""
                        export function run(): int { return 1; }
                        """), "Entry"));
            ProcessBuilder javac = new ProcessBuilder("javac", "-encoding", "UTF-8",
                "Entry.java", "Other.java", "JvmConformanceRunner.java");
            javac.directory(outputDir.toFile());
            javac.redirectErrorStream(true);
            Process p = javac.start();
            String javacOut = new String(p.getInputStream().readAllBytes()).trim();
            int javacExit = p.waitFor();
            check(javacExit == 0, "orchestrator artifacts compile with javac: "
                + javacOut);

            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                outputDir.toString(), "JvmConformanceRunner");
            javaRun.redirectErrorStream(true);
            Process p2 = javaRun.start();
            String out = new String(p2.getInputStream().readAllBytes()).trim();
            int exit = p2.waitFor();
            check(exit == 0, "runner exits 0");
            check(!out.contains("other-module-ran"),
                "the unused import ran no load-time print (v1.2 top level "
                + "holds only declarations): " + out);
        }
    }

    // =========================================================================
    // ISSUE-0097 stdlib boundary slice: std/console, std/string, std/math, std/time
    // =========================================================================

    /** The supported stdlib aliases emit the ISSUE-0097 call forms:
     * {@code __str*}/{@code __mathSqrt} helpers, plain-text
     * {@code String.contains/startsWith/endsWith}, fully-qualified
     * {@code java.lang.Math} expressions, and the second-truncated
     * {@code nowMillis()} form — with every helper definition present in
     * the module class. */
    private static void testStdlibCallEmission() {
        System.out.println("-- Stdlib call emission (ISSUE-0097) --");

        Frontend f = compileFrontend("""
            import * as str from "std/string"
            import * as math from "std/math"
            import * as time from "std/time"
            export function run(): string {
              let n: int = str.length("abc");
              let sub: string = str.substring("hello", 1, 4);
              let c: boolean = str.contains("hello", "ell");
              let sw: boolean = str.startsWith("hello", "h");
              let ew: boolean = str.endsWith("hello", "o");
              let r: string = str.replace("a", "a", "b");
              let parts: string[] = str.split("a,b", ",");
              let t: string = str.trim("  x  ");
              let fl: number = math.floor(1.9);
              let ce: number = math.ceil(1.1);
              let sq: number = math.sqrt(4.0);
              let ai: int = math.absInt(-3);
              let an: number = math.absNumber(-1.5);
              let mn: int = math.minInt(2, 3);
              let mx: int = math.maxInt(2, 3);
              let now: int = time.nowMillis();
              return sub;
            }
            """, "jvmtest-stdlib-emission.deal");
        if (!f.errors().isEmpty()) {
            fail("frontend must accept the stdlib program: " + f.errors());
            return;
        }
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(f.program(),
            f.checkResult(), "jvmtest-stdlib-emission.deal", "main");
        if (res.hasErrors()) {
            fail("backend must accept the stdlib program: " + res.diagnostics());
            return;
        }
        String java = res.source();
        check(java.contains("__strLength("), "length emits __strLength");
        check(java.contains("__strSubstring("), "substring emits __strSubstring");
        check(java.contains(").contains("), "contains emits String.contains");
        check(java.contains(").startsWith("), "startsWith emits String.startsWith");
        check(java.contains(").endsWith("), "endsWith emits String.endsWith");
        check(java.contains("__strReplace("), "replace emits __strReplace");
        check(java.contains("__strSplit("), "split emits __strSplit");
        check(java.contains("__strTrim("), "trim emits __strTrim");
        check(java.contains("java.lang.Math.floor("), "floor emits Math.floor");
        check(java.contains("java.lang.Math.ceil("), "ceil emits Math.ceil");
        check(java.contains("__mathSqrt("), "sqrt emits __mathSqrt");
        check(java.contains("checkInt(java.lang.Math.abs("),
            "absInt re-checks with checkInt");
        check(java.contains("java.lang.Math.abs("), "absNumber emits Math.abs");
        check(java.contains("java.lang.Math.min("), "minInt emits Math.min");
        check(java.contains("java.lang.Math.max("), "maxInt emits Math.max");
        check(java.contains("(java.lang.System.currentTimeMillis() / 1000L) * 1000L"),
            "nowMillis emits the second-truncated form");
        check(java.contains("static long __strLength(java.lang.String s)"),
            "the __strLength helper definition is emitted");
        check(java.contains("static java.lang.String __strSubstring("),
            "the __strSubstring helper definition is emitted");
        check(java.contains("static $DealRt.__StringArray __strSplit("),
            "the __strSplit helper definition is emitted");
        check(java.contains("static double __mathSqrt(double x)"),
            "the __mathSqrt helper definition is emitted");
    }

    /** {@code std/table} and {@code std/json} imports — used and unused —
     * compile through the supported-stdlib seam (ISSUE-0102 for
     * {@code std/table}, ISSUE-0302 for {@code std/json}): their
     * functions execute over the shared table carrier and the emitted
     * shared JSON runtime, and the import is never an E6000. */
    private static void testStdlibTableBoundaryAccepted() throws Exception {
        System.out.println("-- Stdlib table-boundary imports compile (std/table, std/json) --");

        record Case(String what, String source, String module) {}
        List<Case> cases = List.of(
            new Case("std/table import + table use", """
                import * as t from "std/table"
                export function test(): int {
                  let tbl: table = {};
                  return 1;
                }
                """, "std/table"),
            new Case("unused std/table import", """
                import * as t from "std/table"
                export function test(): int { return 1; }
                """, "std/table"),
            new Case("std/json import + call", """
                import * as j from "std/json"
                export function test(): int {
                  let parsed: table = j.parse("{}");
                  return 1;
                }
                """, "std/json"),
            new Case("unused std/json import", """
                import * as j from "std/json"
                export function test(): int { return 1; }
                """, "std/json")
        );
        for (Case c : cases) {
            Frontend f = compileFrontend(c.source(), "jvmtest-stdlib-boundary.deal");
            if (!f.errors().isEmpty()) {
                fail("frontend must accept the table-boundary stdlib import '"
                    + c.what() + "' (the backend compiles it): " + f.errors());
                continue;
            }
            JvmBackend.JvmCodegenResult res = JvmBackend.generate(f.program(),
                f.checkResult(), "jvmtest-stdlib-boundary.deal", "main");
            check(!res.hasErrors(),
                "backend accepts " + c.what() + ": " + res.diagnostics());
            if (c.module().equals("std/table")) {
                // ISSUE-0102: std/table.keys executes — tables map as
                // first-class values, so the import compiles (the emitted
                // artifact carries the __tableKeys helper).
                check(res.source().contains("__tableKeys"),
                    "std/table import emits the keys helper");
                continue;
            }
            // ISSUE-0302: a std/json-importing module emits the shared
            // JSON runtime — the parse/stringify helpers back
            // json.parse/json.stringify even without @jsonable classes.
            check(res.source().contains("static java.lang.Object __jsonParse("),
                "std/json import emits the shared JSON parser");
            check(res.source().contains(
                    "static $DealRt.Table $jsonParse(java.lang.String s) {"),
                "std/json import emits the $jsonParse helper");
            check(res.source().contains("static java.lang.String __jsonStringify("),
                "std/json import emits the __jsonStringify helper");
        }

        // The orchestrator's JVM path compiles the std/json-importing
        // module and writes its artifact (the import is never a
        // rejection site).
        writeFile("src/table_import.deal", """
            import * as j from "std/json"
            export function main(): null { return null; }
            export function run(): int { return 1; }
            """);
        Path entryFile = tmpDir.get().resolve("src/table_import.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/table_boundary");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success = orchestrator.compile();
        check(success, "orchestrator JVM path compiles std/json imports: "
            + orchestrator.diagnostics());
        check(Files.exists(outputDir.resolve("Table_import.java")),
            "the artifact is written for the std/json-importing module");
    }

    /** Real stdlib execution through the emitted artifact: every supported
     * std/string and std/math function computes its LuaJIT reference value,
     * including the substring clipping and the v1.2 negative-bound semantics
     * (a negative start behaves as 0, a negative end yields the empty
     * string). */
    private static void testStdlibExecution() throws Exception {
        System.out.println("-- Stdlib execution (ISSUE-0097) --");

        ExecResult res = compileAndRunJvm("""
            import * as str from "std/string"
            import * as math from "std/math"
            import * as console from "std/console"
            export function run(): string {
              let n: int = str.length("hello");
              let sub: string = str.substring("hello", 1, 4);
              let clip: string = str.substring("abc", 1, 10);
              let past: string = str.substring("abc", 5, 10);
              let neg: string = str.substring("abc", -3, 3);
              let negEnd: string = str.substring("abc", 1, -1);
              let negBoth: string = str.substring("abc", 0, -1);
              let negStartMid: string = str.substring("abc", -2, 2);
              let trimmed: string = str.trim("  deal  ");
              let replaced: string = str.replace("a-b-c", "-", ":");
              let kept: string = str.replace("hello", "", "x");
              let parts: string[] = str.split("a,,b", ",");
              let fl: int = int(math.floor(3.8));
              let ce: int = int(math.ceil(3.2));
              let sq: int = int(math.sqrt(9.0));
              let ai: int = math.absInt(-7);
              let an: number = math.absNumber(-2.5);
              let mn: int = math.minInt(3, 9);
              let mx: int = math.maxInt(3, 9);
              let vt: string = str.trim("\u000bhello\u000b");
              let ff: string = str.trim("\u000chello\u000c");
              if (n !== 5 || sub !== "ell" || clip !== "bc" || past !== ""
                  || neg !== "abc" || negEnd !== "" || negBoth !== ""
                  || negStartMid !== "ab" || trimmed !== "deal"
                  || replaced !== "a:b:c" || kept !== "hello"
                  || fl !== 3 || ce !== 4 || sq !== 3 || ai !== 7
                  || an !== 2.5 || mn !== 3 || mx !== 9
                  || vt !== "hello" || ff !== "hello") {
                console.log("stdlib-bad");
                return "bad";
              }
              if (parts.length !== 3 || parts[0] !== "a"
                  || parts[1] !== "" || parts[2] !== "b") {
                console.log("stdlib-bad");
                return "bad";
              }
              console.log("stdlib-ok");
              return "stdlib-done";
            }
            """, "stdlib-execution");
        check(res.exitCode() == 0, "stdlib execution exits 0: " + res.output());
        check(res.output().contains("stdlib-ok"),
            "stdlib execution prints stdlib-ok: " + res.output());
        check(res.output().contains("stdlib-done"),
            "stdlib execution returns the final value: " + res.output());
    }

    /** {@code math.sqrt} of a negative number raises E8001 exactly like
     * std/math.lua — a real runtime error surfaced by executing the
     * emitted artifact. */
    private static void testStdlibSqrtNegativeRuntimeError() throws Exception {
        System.out.println("-- Stdlib sqrt(-1) → E8001 --");

        ExecResult res = compileAndRunJvm("""
            import * as math from "std/math"
            export function run(): number { return math.sqrt(-1.0); }
            """, "stdlib-sqrt-neg");
        check(res.exitCode() == 1, "sqrt(-1) exits 1: " + res.output());
        check(res.output().contains("DEAL_ERROR_CODE: E8001"),
            "sqrt(-1) reports E8001: " + res.output());
        check(res.output().contains("sqrt of negative number"),
            "sqrt(-1) reports the std/math.lua message: " + res.output());
    }

    /** ISSUE-0106 v1.2 Unicode scalar-value semantics: {@code
     * length("héllo")} is 5 scalar values, {@code substring} positions
     * are scalar values ({"é"} at position 1..2), and a supplementary
     * character counts as ONE scalar value everywhere. */
    private static void testStdlibScalarSemantics() throws Exception {
        System.out.println("-- Stdlib Unicode scalar-value semantics --");

        ExecResult res = compileAndRunJvm("""
            import * as str from "std/string"
            export function run(): string {
              let scalars: int = str.length("héllo");
              let e: string = str.substring("héllo", 1, 2);
              let sup: int = str.length("\ud83d\ude00");
              let cut: string = str.substring("a\ud83d\ude00b", 1, 2);
              if (scalars !== 5) { return "bad-scalars"; }
              if (e !== "é") { return "bad-e"; }
              if (sup !== 1) { return "bad-sup"; }
              if (cut !== "\ud83d\ude00") { return "bad-cut"; }
              return "scalars-ok";
            }
            """, "stdlib-scalars");
        check(res.exitCode() == 0, "scalar-semantics run exits 0: " + res.output());
        check(res.output().contains("scalars-ok"),
            "scalar-value semantics compute the v1.2 values: " + res.output());
    }

    /** {@code nowMillis()} reproduces LuaJIT's {@code os.time() * 1000}:
     * positive, near the current epoch, and second-truncated. */
    private static void testStdlibTimeNowMillis() throws Exception {
        System.out.println("-- Stdlib nowMillis (ISSUE-0097) --");

        ExecResult res = compileAndRunJvm("""
            import * as time from "std/time"
            export function run(): int {
              let t: int = time.nowMillis();
              let g: int = t % 1000;
              if (t > 1700000000000 && g === 0) { return 1; }
              return 0;
            }
            """, "stdlib-nowmillis");
        check(res.exitCode() == 0, "nowMillis run exits 0: " + res.output());
        check(res.output().contains("1"), "nowMillis is positive, recent, and "
            + "second-truncated: " + res.output());
    }

    /** DEAL functions named like the emitted stdlib helpers coexist with
     * them: {@link JvmBackend#javaName} escapes every underscore, so the
     * user functions translate to {@code $u$u…} names and never collide
     * with the {@code __str*}/{@code __mathSqrt} helpers. */
    private static void testStdlibHelperNameCollisions() throws Exception {
        System.out.println("-- Stdlib helper name collisions --");

        ExecResult res = compileAndRunJvm("""
            function __strLength(s: string): int { return 1; }
            function __strTrim(s: string): string { return s; }
            function __strSplit(s: string, sep: string): string[] { return []; }
            function __strReplace(s: string, o: string, to: string): string { return s; }
            function __mathSqrt(x: number): number { return x; }
            export function run(): string {
              let a: int = __strLength("abc");
              let b: string = __strTrim("  x  ");
              let c: string[] = __strSplit("a", ",");
              let d: string = __strReplace("a", "a", "b");
              let e: number = __mathSqrt(4.0);
              if (a !== 1 || b !== "  x  " || c.length !== 0
                  || d !== "a" || e !== 4.0) {
                return "collision-bad";
              }
              return "collision-ok";
            }
            """, "stdlib-helper-collide");
        check(res.exitCode() == 0, "helper-name-collision run exits 0: "
            + res.output());
        check(res.output().contains("collision-ok"),
            "user functions named like stdlib helpers coexist and run: "
                + res.output());
    }

    /** The orchestrator's JVM path resolves stdlib imports from the real
     * stdlib declarations, emits the supported stdlib calls, and the
     * emitted artifacts compile and execute. */
    private static void testOrchestratorJvmStdlibImport() throws Exception {
        System.out.println("-- Orchestrator: stdlib imports through the JVM path --");

        writeFile("src/strings.deal", """
            import * as str from "std/string"
            export function wordCount(s: string): int {
              let parts: string[] = str.split(s, " ");
              return parts.length;
            }
            """);
        writeFile("src/entry.deal", """
            import * as strings from "./strings"
            import * as math from "std/math"
            export function main(): null { return null; }
            export function run(): int {
              let words: int = strings.wordCount("a b c");
              return math.absInt(words - 6);
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/stdlib_import");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "stdlib-importing project compiles through the "
            + "orchestrator JVM path: " + orchestrator.diagnostics());
        if (!success) return;

        Path entryArtifact = outputDir.resolve("Entry.java");
        Path stringsArtifact = outputDir.resolve("Strings.java");
        check(Files.exists(entryArtifact), "entry artifact written");
        check(Files.exists(stringsArtifact), "imported module artifact written");

        if (Files.exists(entryArtifact) && Files.exists(stringsArtifact)) {
            String java = Files.readString(stringsArtifact);
            check(java.contains("__strSplit("),
                "the imported module emits the std/string split helper call");

            Files.writeString(outputDir.resolve("JvmConformanceRunner.java"),
                StubModuleResolver.buildJvmRunner(
                    parseProgram("""
                        export function run(): int { return 3; }
                        """), "Entry"));
            ProcessBuilder javac = new ProcessBuilder("javac", "-encoding", "UTF-8",
                "Entry.java", "Strings.java", "JvmConformanceRunner.java");
            javac.directory(outputDir.toFile());
            javac.redirectErrorStream(true);
            Process p = javac.start();
            String javacOut = new String(p.getInputStream().readAllBytes()).trim();
            int javacExit = p.waitFor();
            check(javacExit == 0, "orchestrator stdlib artifacts compile with "
                + "javac: " + javacOut);

            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                outputDir.toString(), "JvmConformanceRunner");
            javaRun.redirectErrorStream(true);
            Process p2 = javaRun.start();
            String out = new String(p2.getInputStream().readAllBytes()).trim();
            int exit = p2.waitFor();
            check(exit == 0, "runner exits 0: " + out);
            check(out.contains("3"),
                "stdlib helpers compute through the cross-module call: " + out);
        }
    }

    /** ISSUE-0100: a relative (./) declaration-file import is now a HOST
     * module on the JVM path — the same classification the LuaJIT use
     * site applies (host-module-abi D5(4)) — so it compiles into host
     * wrapper methods instead of the pre-slice E6000. An unsupported
     * declared export shape (a class export) still fails E6000 at the
     * import statement. */
    private static void testOrchestratorJvmDeclarationImportRejected() throws Exception {
        System.out.println("-- Orchestrator: declaration-file import = host module (ISSUE-0100) --");

        writeFile("src/hostlib.d.deal", """
            export function foo(): int;
            """);
        writeFile("src/entry.deal", """
            import * as m from "./hostlib"
            export function main(): null { return null; }
            export function run(): int { return m.foo(); }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/import_decl_rejected");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "relative declaration-file import compiles as a "
            + "host module: " + orchestrator.diagnostics());
        Path entryArtifact = outputDir.resolve("Entry.java");
        check(Files.exists(entryArtifact), "host-importing module artifact written");
        if (Files.exists(entryArtifact)) {
            String java = Files.readString(entryArtifact);
            check(java.contains("__host$m$foo("),
                "the host export emits its wrapper method");
            check(java.contains("java.lang.Class.forName(\"Hostlib\")"),
                "the wrapper loads the host class derived from the module path");
            check(java.contains("__hostMethod(__h, \"./hostlib\", \"foo\", \"()->int\""),
                "the load-time presence check names the declared export");
        }

        // A class in an unlisted relative .d.deal is E2010 at the class
        // name span unconditionally at the declaration (ISSUE-0269, D6
        // rule (d)) — the retired E6000-at-the-import backend surface
        // never fires because the frontend gate fails the compile before
        // codegen.
        writeFile("src/hostlib.d.deal", """
            export class User { name: string; }
            """);
        writeFile("src/entry.deal", """
            import * as m from "./hostlib"
            export function main(): null { return null; }
            export function run(): int { return 1; }
            """);
        Path outputDir2 = tmpDir.get().resolve("build/import_decl_class");
        CompilationOrchestrator orchestrator2 = new CompilationOrchestrator(
            entryFile,
            outputDir2,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());
        boolean success2 = orchestrator2.compile();
        check(!success2, "a class in an unlisted declaration fails the JVM compile");
        check(orchestrator2.diagnostics().stream()
                .anyMatch(d -> "E2010".equals(d.code())
                    && d.message().contains("Class 'User'")),
            "the unlisted declaration class is E2010 at the class name span: "
                + orchestrator2.diagnostics());
        check(!Files.exists(outputDir2.resolve("Entry.java")),
            "no artifact for the module with the identity-less class export");
    }

    /** ISSUE-0100 end-to-end: an externals-listed host module compiles
     * through the real orchestrator pipeline (deal.json externals → host
     * declaration discovery → typing → JvmBackend host bindings) and the
     * emitted artifact runs against a real host implementation class —
     * declared export exposure, load-time presence checks (E8011 for a
     * missing export), the sync return boundary (E8010 for a wrong
     * runtime kind), the async operation shape and completion checks
     * (E8010/E8001), and the nullable/null boundary. */
    private static void testHostAbiSlice() throws Exception {
        System.out.println("-- Host ABI slice (ISSUE-0100) --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/jvm",
              "backend": "jvm",
              "externals": {
                "host/log": { "declaration": "bindings/log.d.deal" }
              }
            }
            """);
        writeFile("bindings/log.d.deal", """
            export function info(level: int, s: string): null;
            export function add(a: int, b: int): int;
            export function find(s: string): string | null;
            export function value(): string;
            export async function fetch(): string;
            """);
        writeFile("src/entry.deal", """
            import * as console from "std/console"
            import * as log from "host/log"
            export function main(): null {
              log.info(1, "hello");
              let f: string | null = log.find("x");
              if (f === null) { console.log("null"); } else { console.log(f); }
              return null;
            }
            export function run(): int { return log.add(2, 3); }
            """);
        writeFile("HostLog.java", """
            import java.util.concurrent.CompletableFuture;
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return "v"; }
                public static Object fetch() { return CompletableFuture.completedFuture("d"); }
            }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        // ISSUE-0269: the externals-listed project routes through
        // production ProjectLocator + the context-driven orchestrator
        // (the retired DealConfig/roots/stdlibDir pipeline is gone).
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entryFile.toString(), null);
        check(located.context() != null,
            "deal.json with externals locates strictly: " + located.e2010());
        Path outputDir =
            Path.of(located.context().outputPath().absoluteNormalizedPath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entryFile, false, false, false, false, null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
        boolean success = orchestrator.compile();
        check(success, "externals-listed host module compiles: "
            + orchestrator.diagnostics());
        Path entryArtifact = outputDir.resolve("Entry.java");
        check(Files.exists(entryArtifact), "entry artifact written");
        if (!Files.exists(entryArtifact)) return;

        String java = Files.readString(entryArtifact);
        check(java.contains("static java.lang.reflect.Method $host$log$add$m;"),
            "the declared export emits its cached Method field");
        check(java.contains("java.lang.Class.forName(\"HostLog\")"),
            "the load method loads the module-path-derived host class");
        check(java.contains("__hostMethod(__h, \"host/log\", \"add\", \"(int,int)->int\""),
            "the presence check carries the declared descriptor");
        check(java.contains(
                "static long __host$log$add(java.lang.Object __a0, "
                    + "java.lang.Object __a1, java.lang.String oFile, "
                    + "int oLine, int oCol, java.lang.String "
                    + "oAwaitFile, int oAwaitLine, int oAwaitCol)"),
            "the wrapper signature takes java.lang.Object parameters and "
                + "the call-site/await-site origin triples "
                + "(ISSUE-0303 D2: the wrapper checks each argument "
                + "against the declared descriptor at the call)");
        check(java.contains("__a0 = __hostParamCheck(1, \"int\", __a0, "
                + "oFile, oLine, oCol);"),
            "the wrapper checks each argument at the call "
                + "(HOST_PARAMETER boundary, E8010 'parameter {i} type "
                + "mismatch') with the call-site origin");
        check(java.contains("__hostCheck(\"int\", __r, \"host/log.add\", "
                + "false, oFile, oLine, oCol)"),
            "the sync wrapper checks the return boundary (E8010 path) at "
                + "the call site");
        check(java.contains("__hostCheck(\"string\", __v, \"host/log.fetch\", "
                + "true, oAwaitFile, oAwaitLine, oAwaitCol)"),
            "the async wrapper checks the completion value (E8001 path) at "
                + "the await site");
        check(java.contains("__unpairedSurrogateReason(s)")
                && java.contains("expected string, got invalid UTF-8 encoding")
                && java.contains(
                    "expected string, got UTF-16 surrogate code point"),
            "the host check's string branch runs the v1.2 unpaired-surrogate "
                + "scan and carries the closed reason texts "
                + "(E8010 sync / E8001 completion)");
        check(java.contains(
                "static DealError __hostReturnFail(boolean completion, "
                    + "java.lang.String desc, java.lang.Object v, "
                    + "java.lang.String reason, java.lang.String oFile, "
                    + "int oLine, int oCol)"),
            "the host return/completion failure factory takes the origin "
                + "and builds the closed projections");
        check(java.contains(
                "return new DealError(completion ? \"E8001\" : \"E8010\", "
                    + "completion ? reason : \"return value 1 type mismatch: "
                    + "\" + reason, oFile, oLine, oCol, desc, "
                    + "__hostKind(v));"),
            "the host return/completion re-raise carries the call-site "
                + "origin, the declared descriptor as expected, and the "
                + "closed runtime-kind projection as actual");
        check(java.contains(
                "throw new DealError(\"E8010\", \"parameter \" + i + \" "
                    + "type mismatch: \" + __hostInnerMessage(d, v, inner), "
                    + "oFile, oLine, oCol, desc, __hostKind(v));"),
            "the host parameter re-raise propagates the call-site origin, "
                + "the closed message, and the declared-descriptor/kind "
                + "pair");
        check(java.contains(
                "throw new DealError(\"E8010\", \"host async function "
                    + "must return an async operation, got \" + "
                    + "__hostKind(__r), oFile, oLine, oCol, "
                    + "\"async operation\", __hostKind(__r));"),
            "the host async shape raise reports the call-site origin with "
                + "the pinned expected/actual pair");
        check(java.contains(
                "throw new DealError(\"E8011\", \"missing host export '\" "
                    + "+ name + \"' in module '\" + module + \"'\", "
                    + "oFile, oLine, oCol);"),
            "the missing-export load-time raise reports the pinned message "
                + "and the import-site origin");
        check(java.contains("return __host$log$add(2L, 3L, \"")
                && java.contains("src/entry.deal\", 9, 37, \""),
            "the direct host call threads the call-expression origin "
                + "(the DEAL source-path file literal at the pinned "
                + "line/column) into the wrapper, got: "
                + java.lines()
                    .filter(l -> l.contains("__host$log$add(")
                        && l.contains("entry.deal"))
                    .findFirst().orElse("<no host call>"));
        check(java.contains("static {\n        __hostLoad$log(\""),
            "the import statement emits the load-time presence-check block "
                + "with the import-site origin");

        // Real execution: javac over the artifacts + host class + runner,
        // then java. The host's load-time call, the nullable return, and
        // the exported add run end to end.
        Files.copy(tmpDir.get().resolve("HostLog.java"), outputDir.resolve("HostLog.java"));
        Files.writeString(outputDir.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export function run(): int { return 1; }
                    """), "Entry"));
        ProcessBuilder javac = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry.java", "HostLog.java", "JvmConformanceRunner.java");
        javac.directory(outputDir.toFile());
        javac.redirectErrorStream(true);
        Process p = javac.start();
        String javacOut = new String(p.getInputStream().readAllBytes()).trim();
        check(p.waitFor() == 0, "host artifacts compile with javac: " + javacOut);

        ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
            outputDir.toString(), "JvmConformanceRunner");
        javaRun.redirectErrorStream(true);
        Process p2 = javaRun.start();
        String out = new String(p2.getInputStream().readAllBytes()).trim();
        int exit = p2.waitFor();
        check(exit == 0, "host fixture runs: " + out);
        check(out.contains("x") && out.contains("5"),
            "the nullable host return and the exported add run: " + out);

        // Missing declared export: the host class lacks add → E8011 at
        // module load, raised by the load-time presence check.
        writeFile("HostLogMissing.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object find(String s) { return s; }
                public static Object value() { return "v"; }
                public static Object fetch() { return java.util.concurrent.CompletableFuture.completedFuture("d"); }
            }
            """);
        Path outputDir2 = tmpDir.get().resolve("build/host_abi_missing");
        CompilationOrchestrator orchestrator2 = jvmTestOrchestrator(entryFile, outputDir2);
        check(orchestrator2.compile(), "missing-export project still compiles (the check is load-time): "
            + orchestrator2.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogMissing.java"),
            outputDir2.resolve("HostLog.java"));
        Files.writeString(outputDir2.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export function run(): int { return 1; }
                    """), "Entry"));
        ProcessBuilder javac2 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry.java", "HostLog.java", "JvmConformanceRunner.java");
        javac2.directory(outputDir2.toFile());
        javac2.redirectErrorStream(true);
        Process p3 = javac2.start();
        String javacOut2 = new String(p3.getInputStream().readAllBytes()).trim();
        check(p3.waitFor() == 0, "missing-export artifacts compile with javac: " + javacOut2);
        ProcessBuilder javaRun2 = new ProcessBuilder("java", "-cp",
            outputDir2.toString(), "JvmConformanceRunner");
        javaRun2.redirectErrorStream(true);
        Process p4 = javaRun2.start();
        String out2 = new String(p4.getInputStream().readAllBytes()).trim();
        int exit2 = p4.waitFor();
        check(exit2 == 1, "missing declared export fails at load: " + out2);
        check(out2.contains("DEAL_ERROR_CODE: E8011"),
            "missing declared export reports E8011: " + out2);

        // Bad sync return: value() returns a Long for a declared string.
        writeFile("HostLogBad.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return Long.valueOf(42L); }
                public static Object fetch() { return java.util.concurrent.CompletableFuture.completedFuture("d"); }
            }
            """);
        writeFile("src/entry_bad.deal", """
            import * as log from "host/log"
            export function main(): null { return null; }
            export function run(): string { return log.value(); }
            """);
        Path entryBad = tmpDir.get().resolve("src/entry_bad.deal").toAbsolutePath();
        Path outputDir3 = tmpDir.get().resolve("build/host_abi_bad_ret");
        CompilationOrchestrator orchestrator3 = jvmTestOrchestrator(entryBad, outputDir3);
        check(orchestrator3.compile(), "bad-return project compiles: "
            + orchestrator3.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogBad.java"),
            outputDir3.resolve("HostLog.java"));
        Files.writeString(outputDir3.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export function run(): string { return "x"; }
                    """), "Entry_bad"));
        ProcessBuilder javac3 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_bad.java", "HostLog.java", "JvmConformanceRunner.java");
        javac3.directory(outputDir3.toFile());
        javac3.redirectErrorStream(true);
        Process p5 = javac3.start();
        String javacOut3 = new String(p5.getInputStream().readAllBytes()).trim();
        check(p5.waitFor() == 0, "bad-return artifacts compile with javac: " + javacOut3);
        ProcessBuilder javaRun3 = new ProcessBuilder("java", "-cp",
            outputDir3.toString(), "JvmConformanceRunner");
        javaRun3.redirectErrorStream(true);
        Process p6 = javaRun3.start();
        String out3 = new String(p6.getInputStream().readAllBytes()).trim();
        int exit3 = p6.waitFor();
        check(exit3 == 1, "wrong-kind host return fails: " + out3);
        check(out3.contains("DEAL_ERROR_CODE: E8010"),
            "wrong-kind host return reports E8010: " + out3);

        // ISSUE-0106 v1.2 boundary string validation at the host return
        // boundary: a sync string return carrying an unpaired UTF-16
        // surrogate (a lone high surrogate) is rejected with E8010 and
        // the seam's message — the host boundary is an ingress where an
        // invalid encoding can enter DEAL.
        writeFile("HostLogBadSurrogate.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return "a" + (char) 0xD800 + "b"; }
                public static Object fetch() { return java.util.concurrent.CompletableFuture.completedFuture("d"); }
            }
            """);
        Path outputDirSur = tmpDir.get().resolve("build/host_abi_bad_surrogate");
        CompilationOrchestrator orchestratorSur = jvmTestOrchestrator(entryBad, outputDirSur);
        check(orchestratorSur.compile(), "surrogate-return project compiles: "
            + orchestratorSur.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogBadSurrogate.java"),
            outputDirSur.resolve("HostLog.java"));
        Files.writeString(outputDirSur.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function run(): string { return "x"; }
                    """), "Entry_bad"));
        ProcessBuilder javacSur = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_bad.java", "HostLog.java", "JvmConformanceRunner.java");
        javacSur.directory(outputDirSur.toFile());
        javacSur.redirectErrorStream(true);
        Process pSur = javacSur.start();
        String javacOutSur = new String(pSur.getInputStream().readAllBytes()).trim();
        check(pSur.waitFor() == 0, "surrogate-return artifacts compile with javac: "
            + javacOutSur);
        ProcessBuilder javaRunSur = new ProcessBuilder("java", "-cp",
            outputDirSur.toString(), "JvmConformanceRunner");
        javaRunSur.redirectErrorStream(true);
        Process pSurRun = javaRunSur.start();
        String outSur = new String(pSurRun.getInputStream().readAllBytes()).trim();
        int exitSur = pSurRun.waitFor();
        check(exitSur == 1 && outSur.contains("DEAL_ERROR_CODE: E8010"),
            "unpaired-surrogate host return reports E8010: " + outSur);
        check(outSur.contains("return value 1 type mismatch: expected string, "
                + "got invalid UTF-8 encoding"),
            "the sync boundary rejection carries the pinned host message: "
                + outSur);

        // Async: an entry that awaits the host async export, with the
        // shape (E8010) and completion (E8001) failures.
        writeFile("src/entry_async.deal", """
            import * as log from "host/log"
            export function main(): null { return null; }
            export async function run(): string { return await log.fetch(); }
            """);
        Path entryAsync = tmpDir.get().resolve("src/entry_async.deal").toAbsolutePath();
        Path outputDir4 = tmpDir.get().resolve("build/host_abi_async_ok");
        CompilationOrchestrator orchestrator4 = jvmTestOrchestrator(entryAsync, outputDir4);
        check(orchestrator4.compile(), "async host import compiles: "
            + orchestrator4.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLog.java"),
            outputDir4.resolve("HostLog.java"));
        Files.writeString(outputDir4.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export async function run(): string { return "x"; }
                    """), "Entry_async"));
        ProcessBuilder javac4 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_async.java", "HostLog.java", "JvmConformanceRunner.java");
        javac4.directory(outputDir4.toFile());
        javac4.redirectErrorStream(true);
        Process p7 = javac4.start();
        String javacOut4 = new String(p7.getInputStream().readAllBytes()).trim();
        check(p7.waitFor() == 0, "async artifacts compile with javac: " + javacOut4);
        ProcessBuilder javaRun4 = new ProcessBuilder("java", "-cp",
            outputDir4.toString(), "JvmConformanceRunner");
        javaRun4.redirectErrorStream(true);
        Process p8 = javaRun4.start();
        String out4 = new String(p8.getInputStream().readAllBytes()).trim();
        int exit4 = p8.waitFor();
        check(exit4 == 0 && out4.contains("d"),
            "await joins the host async operation and checks the completion: "
                + out4);

        writeFile("HostLogAsyncShape.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return "v"; }
                public static Object fetch() { return "not-an-operation"; }
            }
            """);
        Path outputDir5 = tmpDir.get().resolve("build/host_abi_async_shape");
        CompilationOrchestrator orchestrator5 = jvmTestOrchestrator(entryAsync, outputDir5);
        check(orchestrator5.compile(), "async shape project compiles: "
            + orchestrator5.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogAsyncShape.java"),
            outputDir5.resolve("HostLog.java"));
        Files.writeString(outputDir5.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export async function run(): string { return "x"; }
                    """), "Entry_async"));
        ProcessBuilder javac5 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_async.java", "HostLog.java", "JvmConformanceRunner.java");
        javac5.directory(outputDir5.toFile());
        javac5.redirectErrorStream(true);
        Process p9 = javac5.start();
        String javacOut5 = new String(p9.getInputStream().readAllBytes()).trim();
        check(p9.waitFor() == 0, "async-shape artifacts compile with javac: " + javacOut5);
        ProcessBuilder javaRun5 = new ProcessBuilder("java", "-cp",
            outputDir5.toString(), "JvmConformanceRunner");
        javaRun5.redirectErrorStream(true);
        Process p10 = javaRun5.start();
        String out5 = new String(p10.getInputStream().readAllBytes()).trim();
        int exit5 = p10.waitFor();
        check(exit5 == 1 && out5.contains("DEAL_ERROR_CODE: E8010"),
            "non-operation host async return reports E8010: " + out5);

        writeFile("HostLogAsyncCompletion.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return "v"; }
                public static Object fetch() { return java.util.concurrent.CompletableFuture.completedFuture(Long.valueOf(7L)); }
            }
            """);
        Path outputDir6 = tmpDir.get().resolve("build/host_abi_async_completion");
        CompilationOrchestrator orchestrator6 = jvmTestOrchestrator(entryAsync, outputDir6);
        check(orchestrator6.compile(), "async completion project compiles: "
            + orchestrator6.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogAsyncCompletion.java"),
            outputDir6.resolve("HostLog.java"));
        Files.writeString(outputDir6.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export async function run(): string { return "x"; }
                    """), "Entry_async"));
        ProcessBuilder javac6 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_async.java", "HostLog.java", "JvmConformanceRunner.java");
        javac6.directory(outputDir6.toFile());
        javac6.redirectErrorStream(true);
        Process p11 = javac6.start();
        String javacOut6 = new String(p11.getInputStream().readAllBytes()).trim();
        check(p11.waitFor() == 0, "async-completion artifacts compile with javac: " + javacOut6);
        ProcessBuilder javaRun6 = new ProcessBuilder("java", "-cp",
            outputDir6.toString(), "JvmConformanceRunner");
        javaRun6.redirectErrorStream(true);
        Process p12 = javaRun6.start();
        String out6 = new String(p12.getInputStream().readAllBytes()).trim();
        int exit6 = p12.waitFor();
        check(exit6 == 1 && out6.contains("DEAL_ERROR_CODE: E8001"),
            "wrong completion value reports E8001 at the await site: " + out6);

        // ISSUE-0106: the same v1.2 boundary string validation applies to
        // async completion values — a lone low surrogate completes the
        // operation and the await site raises E8001 with the seam's
        // message (the completion check, not the sync E8010 path).
        writeFile("HostLogAsyncSurrogate.java", """
            public final class HostLog {
                public static Object info(long level, String s) { return null; }
                public static Object add(long a, long b) { return Long.valueOf(a + b); }
                public static Object find(String s) { return s; }
                public static Object value() { return "v"; }
                public static Object fetch() { return java.util.concurrent.CompletableFuture.completedFuture("a" + (char) 0xDC00 + "b"); }
            }
            """);
        Path outputDir7 = tmpDir.get().resolve("build/host_abi_async_surrogate");
        CompilationOrchestrator orchestrator7 = jvmTestOrchestrator(entryAsync, outputDir7);
        check(orchestrator7.compile(), "async surrogate project compiles: "
            + orchestrator7.diagnostics());
        Files.copy(tmpDir.get().resolve("HostLogAsyncSurrogate.java"),
            outputDir7.resolve("HostLog.java"));
        Files.writeString(outputDir7.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export async function run(): string { return "x"; }
                    """), "Entry_async"));
        ProcessBuilder javac7 = new ProcessBuilder("javac", "-encoding", "UTF-8",
            "Entry_async.java", "HostLog.java", "JvmConformanceRunner.java");
        javac7.directory(outputDir7.toFile());
        javac7.redirectErrorStream(true);
        Process p13 = javac7.start();
        String javacOut7 = new String(p13.getInputStream().readAllBytes()).trim();
        check(p13.waitFor() == 0, "async-surrogate artifacts compile with javac: "
            + javacOut7);
        ProcessBuilder javaRun7 = new ProcessBuilder("java", "-cp",
            outputDir7.toString(), "JvmConformanceRunner");
        javaRun7.redirectErrorStream(true);
        Process p14 = javaRun7.start();
        String out7 = new String(p14.getInputStream().readAllBytes()).trim();
        int exit7 = p14.waitFor();
        check(exit7 == 1 && out7.contains("DEAL_ERROR_CODE: E8001"),
            "unpaired-surrogate async completion reports E8001 at the await site: "
                + out7);
        check(out7.contains(
                "expected string, got invalid UTF-8 encoding"),
            "the completion boundary rejection carries the pinned reason "
                + "text: " + out7);

        // ISSUE-0551: declared bytes host parameters/returns ride the
        // shared $DealRt.Bytes carrier. The emitted wrapper keys the
        // load-time class literal, the call-time parameter check, and the
        // return check on the canonical "bytes" descriptor; a wrong-kind
        // argument raises E8010 before the host method runs (the call
        // counter stays unchanged), and a wrong-kind host return raises
        // E8010 with the pinned host-function message.
        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/jvm_bytes",
              "backend": "jvm",
              "externals": {
                "host/byteshost": { "declaration": "bindings/byteshost.d.deal" }
              }
            }
            """);
        writeFile("bindings/byteshost.d.deal", """
            export function echoBytes(b: bytes): bytes;
            export function nullableBytes(b: bytes | null): bytes | null;
            export function calls(): int;
            """);
        writeFile("src/entry_bytes.deal", """
            import * as host from "host/byteshost"
            export function main(): null { return null; }
            export function run(): string {
              let b: bytes = bytes(2);
              b[0] = 7;
              let echo: bytes = host.echoBytes(b);
              if (!(echo === b)) { throw { code: "TEST_FAIL", message: "echo identity" }; }
              if (host.nullableBytes(null) !== null) { throw { code: "TEST_FAIL", message: "null roundtrip" }; }
              let before: int = host.calls();
              let holder: table = { item: "bad" };
              let failed: boolean = false;
              try {
                let x: bytes = host.echoBytes(holder.item);
              } catch (e) {
                if (e.code !== "E8010") { throw { code: "TEST_FAIL", message: "wrong code " + e.code }; }
                failed = true;
              }
              if (!failed) { throw { code: "TEST_FAIL", message: "no E8010" }; }
              if (host.calls() !== before) { throw { code: "TEST_FAIL", message: "host ran after failed param check" }; }
              return "bytes-host-ok";
            }
            """);
        writeFile("HostByteshost.java", """
            public final class HostByteshost {
                private static int calls;
                public static Object echoBytes($DealRt.Bytes b) { calls += 1; return b; }
                public static Object nullableBytes($DealRt.Bytes b) { calls += 1; return b; }
                public static long calls() { return calls; }
            }
            """);
        Path entryBytes = tmpDir.get().resolve("src/entry_bytes.deal").toAbsolutePath();
        Path outputDirBytes = tmpDir.get().resolve("build/jvm_bytes");
        CompilationOrchestrator orchestratorBytes = new CompilationOrchestrator(
            entryBytes, outputDirBytes, false, false, false, false,
            Backend.JVM,
            Map.of("host/byteshost",
                tmpDir.get().resolve("bindings/byteshost.d.deal").toString()),
            List.of(tmpDir.get().resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(), null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
        check(orchestratorBytes.compile(), "bytes host project compiles: "
            + orchestratorBytes.diagnostics());
        Path entryBytesArtifact = outputDirBytes.resolve("Entry_bytes.java");
        check(Files.exists(entryBytesArtifact), "bytes host entry artifact written");
        if (Files.exists(entryBytesArtifact)) {
            String javaBytes = Files.readString(entryBytesArtifact);
            check(javaBytes.contains("$DealRt.Bytes.class"),
                "the bytes parameter resolves its load-time class literal "
                    + "as the shared $DealRt.Bytes carrier");
            check(javaBytes.contains(
                    "static $DealRt.Bytes __host$host$echoBytes("
                        + "java.lang.Object __a0, java.lang.String oFile, "
                        + "int oLine, int oCol, java.lang.String "
                        + "oAwaitFile, int oAwaitLine, int oAwaitCol)"),
                "the bytes wrapper returns the shared carrier and carries "
                    + "the origin triples");
            check(javaBytes.contains("__a0 = __hostParamCheck(1, \"bytes\", "
                    + "__a0, oFile, oLine, oCol);"),
                "the bytes parameter check keys on the canonical \"bytes\" "
                    + "descriptor at the call (call-site origin)");
            check(javaBytes.contains(
                    "__hostCheck(\"bytes\", __r, "
                        + "\"host/byteshost.echoBytes\", false, "
                        + "oFile, oLine, oCol)"),
                "the bytes return check keys on the canonical \"bytes\" "
                    + "descriptor at the call site");
        }
        Files.copy(tmpDir.get().resolve("HostByteshost.java"),
            outputDirBytes.resolve("HostByteshost.java"));
        Files.writeString(outputDirBytes.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export function run(): string { return "x"; }
                    """), "Entry_bytes"));
        ProcessBuilder javacBytes = new ProcessBuilder("javac",
            "-encoding", "UTF-8", "Entry_bytes.java",
            "HostByteshost.java", "JvmConformanceRunner.java");
        javacBytes.directory(outputDirBytes.toFile());
        javacBytes.redirectErrorStream(true);
        Process pBytes = javacBytes.start();
        String javacOutBytes = new String(pBytes.getInputStream().readAllBytes()).trim();
        check(pBytes.waitFor() == 0, "bytes host artifacts compile with javac: "
            + javacOutBytes);
        ProcessBuilder javaRunBytes = new ProcessBuilder("java", "-cp",
            outputDirBytes.toString(), "JvmConformanceRunner");
        javaRunBytes.redirectErrorStream(true);
        Process pBytesRun = javaRunBytes.start();
        String outBytes = new String(pBytesRun.getInputStream().readAllBytes()).trim();
        int exitBytes = pBytesRun.waitFor();
        check(exitBytes == 0, "bytes host roundtrip + no-call-on-failure run: "
            + outBytes);

        // Wrong-kind bytes host return: E8010 with the pinned
        // host-function message naming the declared descriptor.
        writeFile("HostByteshostBad.java", """
            public final class HostByteshost {
                private static int calls;
                public static Object echoBytes($DealRt.Bytes b) { return "junk"; }
                public static Object nullableBytes($DealRt.Bytes b) { return b; }
                public static int calls() { return calls; }
            }
            """);
        writeFile("src/entry_bytes_bad.deal", """
            import * as host from "host/byteshost"
            export function main(): null { return null; }
            export function run(): bytes {
              let b: bytes = bytes(1);
              return host.echoBytes(b);
            }
            """);
        Path entryBytesBad = tmpDir.get().resolve("src/entry_bytes_bad.deal").toAbsolutePath();
        Path outputDirBytesBad = tmpDir.get().resolve("build/jvm_bytes_bad");
        CompilationOrchestrator orchestratorBytesBad = new CompilationOrchestrator(
            entryBytesBad, outputDirBytesBad, false, false, false, false,
            Backend.JVM,
            Map.of("host/byteshost",
                tmpDir.get().resolve("bindings/byteshost.d.deal").toString()),
            List.of(tmpDir.get().resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(), null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
        check(orchestratorBytesBad.compile(), "bytes bad-return project compiles: "
            + orchestratorBytesBad.diagnostics());
        Files.copy(tmpDir.get().resolve("HostByteshostBad.java"),
            outputDirBytesBad.resolve("HostByteshost.java"));
        Files.writeString(outputDirBytesBad.resolve("JvmConformanceRunner.java"),
            StubModuleResolver.buildJvmRunner(
                parseProgram("""
                    export function main(): null { return null; }
                    export function run(): bytes { return bytes(0); }
                    """), "Entry_bytes_bad"));
        ProcessBuilder javacBytesBad = new ProcessBuilder("javac",
            "-encoding", "UTF-8", "Entry_bytes_bad.java",
            "HostByteshost.java", "JvmConformanceRunner.java");
        javacBytesBad.directory(outputDirBytesBad.toFile());
        javacBytesBad.redirectErrorStream(true);
        Process pBytesBad = javacBytesBad.start();
        String javacOutBytesBad = new String(pBytesBad.getInputStream().readAllBytes()).trim();
        check(pBytesBad.waitFor() == 0, "bytes bad-return artifacts compile with javac: "
            + javacOutBytesBad);
        ProcessBuilder javaRunBytesBad = new ProcessBuilder("java", "-cp",
            outputDirBytesBad.toString(), "JvmConformanceRunner");
        javaRunBytesBad.redirectErrorStream(true);
        Process pBytesBadRun = javaRunBytesBad.start();
        String outBytesBad = new String(pBytesBadRun.getInputStream().readAllBytes()).trim();
        int exitBytesBad = pBytesBadRun.waitFor();
        check(exitBytesBad == 1 && outBytesBad.contains("DEAL_ERROR_CODE: E8010"),
            "wrong-kind bytes host return reports E8010: " + outBytesBad);
        check(outBytesBad.contains(
                "return value 1 type mismatch: expected bytes"),
            "the bytes return rejection carries the pinned host-return "
                + "message: " + outBytesBad);
    }

    /**
     * The test-only isolated-phase orchestrator over the externals
     * wiring of the host-ABI fixture (raw specifier → absolute
     * declaration path; the production conformance harness routes the
     * same project shape through ProjectLocator).
     */
    private static CompilationOrchestrator jvmTestOrchestrator(Path entryFile,
            Path outputDir) {
        // The explicit legacy invocation keeps this helper's emission
        // pins (the host-ABI slice's long-parameter HostLog fixtures and
        // the legacy carrier pins) valid under the committed post-flip
        // default — the legacy profile stays an internal derivation row
        // (PUBLIC_BUILD + PRE_ACTIVATION), never a production rollback
        // target. The activated default is pinned separately by
        // testProfilePlumbIntMode and the E12 activation suite.
        return new CompilationOrchestrator(entryFile, outputDir, false, false,
            false, false, Backend.JVM,
            Map.of("host/log",
                tmpDir.get().resolve("bindings/log.d.deal").toString()),
            List.of(tmpDir.get().resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize(), null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
    }

    /** Parses a small DEAL snippet with the real lexer+parser for runner
     * construction (no type checking — the orchestrator already checked the
     * real module). */
    private static ProgramNode parseProgram(String source) {
        try {
            LexResult lex = new Lexer(source, "jvmtest-runner.deal").tokenize();
            if (lex.hasErrors()) throw new IllegalStateException("lex: " + lex.diagnostics());
            ParseResult parse = new Parser(lex.tokens(), "jvmtest-runner.deal", lex.directiveEvents()).parse();
            if (parse.hasErrors()) throw new IllegalStateException("parse: " + parse.diagnostics());
            return parse.program();
        } catch (IllegalStateException e) {
            throw e;
        } catch (Exception e) {
            throw new IllegalStateException(e);
        }
    }

    /**
     * Multi-module compilation through the orchestrator's JVM path
     * (ISSUE-0096): the entry imports lib and calls its exported add()
     * through the alias; the emitted entry artifact carries the load-time
     * init trigger and the static cross-class call, and the artifacts run
     * with javac + java.
     */
    private static void testModuleImports() throws Exception {
        System.out.println("-- Orchestrator: multi-module import + imported direct call --");

        writeFile("src/lib.deal", """
            function double(x: int): int { return x * 2; }
            export function add(a: int, b: int): int { return double(a) + double(b); }
            """);
        writeFile("src/entry.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int { return lib.add(10, 20); }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/imports");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "multi-module JVM compile succeeds: "
            + orchestrator.diagnostics());
        if (!success) return;

        Path entryArtifact = outputDir.resolve("Entry.java");
        Path libArtifact = outputDir.resolve("Lib.java");
        check(Files.exists(entryArtifact), "entry artifact written");
        check(Files.exists(libArtifact), "imported module artifact written");

        if (Files.exists(entryArtifact)) {
            String java = Files.readString(entryArtifact);
            check(java.contains("Lib.__init$();"),
                "the import emits the load-time init trigger for Lib");
            check(java.contains("return Lib.add(10, 20);"),
                "the imported direct call emits a static call on the "
                + "imported class: " + java);
        }

        ExecResult exec = runJvmArtifacts(outputDir,
            parseProgram("export function run(): int { return 0; }"), "Entry");
        check(exec.exitCode() == 0, "artifacts run with exit 0");
        check(exec.output().contains("60"),
            "imported call computes double(10) + double(20) = 60: "
                + exec.output());
    }

    /**
     * Module class-name isolation (ISSUE-0096): two same-basename modules
     * in different directories derive distinct artifact classes
     * ({@code a/calc → ACalc}, {@code b/calc → BCalc}), each with its own
     * same-named export, and the entry calls both through distinct aliases.
     */
    private static void testModuleClassIsolation() throws Exception {
        System.out.println("-- Orchestrator: module class-name isolation --");

        writeFile("src/a/calc.deal", """
            export function compute(): int { return 1; }
            """);
        writeFile("src/b/calc.deal", """
            export function compute(): int { return 2; }
            """);
        writeFile("src/entry.deal", """
            import * as aCalc from "./a/calc"
            import * as bCalc from "./b/calc"
            export function main(): null { return null; }
            export function run(): int { return aCalc.compute() * 10 + bCalc.compute(); }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/isolation");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "class-isolation project compiles: "
            + orchestrator.diagnostics());
        if (!success) return;

        Path aArtifact = outputDir.resolve("ACalc.java");
        Path bArtifact = outputDir.resolve("BCalc.java");
        Path entryArtifact = outputDir.resolve("Entry.java");
        check(Files.exists(aArtifact), "ACalc.java written for a/calc");
        check(Files.exists(bArtifact), "BCalc.java written for b/calc");
        check(Files.exists(entryArtifact), "Entry.java written");
        if (Files.exists(aArtifact)) {
            check(Files.readString(aArtifact).contains("public final class ACalc"),
                "a/calc derives class ACalc");
        }
        if (Files.exists(bArtifact)) {
            check(Files.readString(bArtifact).contains("public final class BCalc"),
                "b/calc derives class BCalc");
        }

        ExecResult exec = runJvmArtifacts(outputDir,
            parseProgram("export function run(): int { return 0; }"), "Entry");
        check(exec.exitCode() == 0, "artifacts run with exit 0");
        check(exec.output().contains("12"),
            "isolated classes compute 1 * 10 + 2 = 12: " + exec.output());
    }

    /**
     * Sibling-import load-time ordering (ISSUE-0096): two project-module
     * imports initialize depth-first in import order (b-load, then c-load),
     * before the importing module's own load-time statements — exactly
     * where LuaJIT runs each require.
     */
    private static void testModuleUnusedImportLoadTime() throws Exception {
        System.out.println("-- Orchestrator: sibling imports run load-time code in import order --");

        // v1.2 module top level has no executable statements: the
        // observable ordering moves inside the exported functions.
        writeFile("src/b.deal", """
            export function plus(x: int): int { return x + 1; }
            """);
        writeFile("src/c.deal", """
            export function base(): int { return 10; }
            """);
        writeFile("src/entry.deal", """
            import * as b from "./b"
            import * as c from "./c"
            export function main(): null { return null; }
            export function run(): int { return b.plus(c.base()); }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/sibling_imports");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(success, "sibling-import project compiles: "
            + orchestrator.diagnostics());
        if (!success) return;

        ExecResult exec = runJvmArtifacts(outputDir,
            parseProgram("export function run(): int { return 0; }"), "Entry");
        check(exec.exitCode() == 0, "artifacts run with exit 0");
        check(!exec.output().contains("load"),
            "no load-time prints in v1.2 (module top level holds only "
            + "declarations): " + exec.output());
        check(exec.output().contains("11"),
            "b.plus(c.base()) = 11: " + exec.output());
    }

    /**
     * Backend-level emission checks for module imports (ISSUE-0096): without
     * an import resolution map the import stays E6000 (the pre-existing
     * rejection, unchanged for the no-map overloads); with the map the
     * import emits the load-time init trigger, the imported direct call
     * emits a static call on the imported class, and an imported
     * null-returning call hoists as a pre-statement.
     */
    private static void testModuleImportBackendEmission() {
        System.out.println("-- Module import codegen emission (ISSUE-0096) --");

        Map<String, Map<String, Type>> modules = Map.of(
            "./lib", Map.of("add", Types.func(
                List.of(Type.Int.INSTANCE, Type.Int.INSTANCE), Type.Int.INSTANCE)));
        Frontend f = compileFrontend("""
            import * as lib from "./lib"
            export function run(): int { return lib.add(10, 20); }
            """, "jvmtest-import.deal", new FixedModuleResolver(modules));
        if (!f.errors().isEmpty()) {
            fail("checker must accept the module-import probe: " + f.errors());
            return;
        }

        // Without an import resolution map the import is E6000 — the
        // imported module's require-time side effects can never be silently
        // dropped (the pre-existing no-map overloads keep this behavior).
        JvmBackend.JvmCodegenResult bare = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-import.deal", "main");
        check(bare.hasErrors(), "import without a resolution map is E6000");
        check(bare.diagnostics().stream().anyMatch(d -> d.message()
                .contains("project modules")),
            "the rejection names the supported import forms: "
                + bare.diagnostics());

        // With the map the import is accepted: the alias maps to the
        // imported module path, the call emits a static call on the
        // imported class, and the import statement emits the load-time
        // init trigger.
        JvmBackend.JvmCodegenResult res = JvmBackend.generate(
            f.program(), f.checkResult(), "jvmtest-import.deal", "main",
            Map.of("./lib", "lib"));
        check(!res.hasErrors(), "module import emits without E6000: "
            + res.diagnostics());
        check(res.source().contains("    static {\n        Lib.__init$();\n    }"),
            "the import emits the load-time init trigger for Lib");
        check(res.source().contains("return Lib.add(10L, 20L);"),
            "the imported direct call emits Lib.add(10L, 20L)");

        // An imported null-returning call is a void pre-statement.
        Map<String, Map<String, Type>> voidModules = Map.of(
            "./lib", Map.of("tick", Types.func(List.of(), Type.Null.INSTANCE)));
        Frontend voidF = compileFrontend("""
            import * as lib from "./lib"
            export function run(): null { lib.tick(); }
            """, "jvmtest-import-void.deal",
            new FixedModuleResolver(voidModules));
        if (!voidF.errors().isEmpty()) {
            fail("checker must accept the imported void-call probe: "
                + voidF.errors());
            return;
        }
        JvmBackend.JvmCodegenResult voidRes = JvmBackend.generate(
            voidF.program(), voidF.checkResult(), "jvmtest-import-void.deal",
            "main", Map.of("./lib", "lib"));
        check(!voidRes.hasErrors(), "imported void call emits without E6000: "
            + voidRes.diagnostics());
        check(voidRes.source().contains("Lib.tick();"),
            "the imported void call emits Lib.tick(); as a pre-statement");
    }

    /**
     * A module-level use of an import alias before its import statement is
     * E6000 (ISSUE-0096): LuaJIT emits the {@code require} at the import's
     * source position, so an earlier use reads the not-yet-required global
     * and fails at load — verified with real luajit for both shapes —
     * while Java would silently initialize the imported class. The
     * transitive shape (a module-level call of a function whose body uses
     * a later import) is included.
     */
    private static void testModuleImportUseBeforeImportRejected() {
        System.out.println("-- Module-level alias use before its import → E6000 --");

        Map<String, Map<String, Type>> modules = Map.of(
            "./lib", Map.of("value", Types.func(List.of(), Type.Int.INSTANCE)));

        // v1.2 grammar gate: every use-before-import shape rests on
        // module-level executable statements, which the v1.2 grammar
        // removes (E1049/E1048). The import-first trigger emission is
        // pinned by testModuleImportBackendEmission below.
        List<String> sources = List.of(
            """
            let base: int = lib.value();
            import * as lib from "./lib"
            export function run(): int { return base; }
            """,
            """
            if (lib.value() === 40) { }
            import * as lib from "./lib"
            export function run(): int { return 1; }
            """,
            """
            function f(): int { return lib.value(); }
            f();
            import * as lib from "./lib"
            export function run(): int { return 1; }
            """,
            """
            import * as lib from "./lib"
            let base: int = lib.value();
            export function run(): int { return base; }
            """,
            // indirect (ISSUE-0098): a module-level indirect call through a
            // function-typed field whose held function uses the alias, with
            // the import declared after the call site — the load-time
            // indirect-call guard applies the same import hazard check as
            // the direct-call path (LuaJIT reads the not-yet-required
            // global at load; Java would silently initialize the imported
            // class).
            """
            function f(): int { return lib.value(); }
            let g: () => int = f;
            let r: int = g();
            import * as lib from "./lib"
            export function run(): int { return r; }
            """);

        for (String source : sources) {
            Frontend f = compileFrontend(source, "jvmtest-import-order.deal",
                new FixedModuleResolver(modules));
            check(f.errors().stream().anyMatch(d ->
                    "E1049".equals(d.code()) || "E1048".equals(d.code())),
                "use-before-import shape rejected with E1049/E1048: "
                    + f.errors());
        }
    }

    /** Two modules whose paths differ only in case would derive the same
     * class name; the orchestrator reports an E6000 instead of silently
     * overwriting one module's artifact. */
    private static void testOrchestratorJvmClassCollision() throws Exception {
        System.out.println("-- Orchestrator: JVM class-name collision → E6000 --");

        writeFile("src/App.deal", """
            export function run(): int { return 1; }
            """);
        writeFile("src/app.deal", """
            export function run(): int { return 2; }
            """);
        writeFile("src/entry.deal", """
            import * as a from "./App"
            import * as b from "./app"
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.get().resolve("src/entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/collision");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile,
            outputDir,
            false,
            false,
            false,
            false,
            Backend.JVM,
            null,
            roots,
            Path.of(".").toAbsolutePath().normalize(),
            null,
            harnessInvocation());

        boolean success = orchestrator.compile();
        check(!success, "class-name collision fails the JVM compile");
        check(orchestrator.diagnostics().stream()
                .anyMatch(d -> "E6000".equals(d.code())
                    && d.message().contains("both derive")),
            "orchestrator reports the class-name collision: " + orchestrator.diagnostics());

        // Anchorless site (D5/D6): the collision diagnostic carries the
        // canonical synthetic range plus a construct-naming note.
        CompilerDiagnostic collision = orchestrator.diagnostics().stream()
            .filter(d -> "E6000".equals(d.code())
                && d.message().contains("both derive"))
            .findFirst().orElse(null);
        check(collision != null, "collision E6000 present for the synthetic pin");
        if (collision != null) {
            check(collision.range().isCanonicalSynthetic()
                    && collision.range().origin() == RangeOrigin.SYNTHETIC,
                "collision E6000 range is canonical synthetic: "
                    + collision.range());
            check(collision.notes().stream().anyMatch(n -> n.message().contains(
                    "missing anchor: module class-name collision between '")),
                "collision E6000 note names the colliding modules: "
                    + collision.notes());
        }
    }

    /**
     * {@code --source-map} combined with {@code --backend jvm} produces no
     * sidecars; the release-owned production compile prints the pinned C9
     * warning instead of silently ignoring the request (ISSUE-0091 rework
     * round 3; the C9 disposition of ISSUE-0643).
     */
    private static void testOrchestratorJvmSourceMapWarning() throws Exception {
        System.out.println("-- Orchestrator: JVM path warns on --source-map --");

        writeFile("src/sm_main.deal", """
            export function main(): null { return null; }
            export function run(): int { return 1; }
            """);

        Path entryFile = tmpDir.get().resolve("src/sm_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.get().resolve("build/sm_jvm");
        List<Path> roots = List.of(tmpDir.get().resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, false, true, Backend.JVM,
            null, roots, Path.of(".").toAbsolutePath().normalize());

        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        boolean success;
        try {
            ERR_CAPTURE.set(captured);
            success = orchestrator.compile();
        } finally {
            ERR_CAPTURE.remove();
        }
        check(success, "JVM compile with --source-map succeeds");
        String warning = captured.toString(StandardCharsets.UTF_8);
        check((deal.module.ProductionProjectEmission.WARNING_JVM + "\n")
                .equals(warning),
            "the pinned C9 warning prints exactly once on the JVM production "
                + "path: " + warning);
        check(Files.exists(outputDir.resolve("Sm_main.java")),
            "the one project artifact is still written");
        try (var stream = Files.walk(outputDir)) {
            check(stream.noneMatch(p -> p.toString().endsWith(".deal.map.json")),
                "no source-map sidecars under the JVM backend");
        }

        // --dump-ir derives the sourceMap flag internally (IR hardening
        // enables source maps with dumps) but is NOT an explicit
        // --source-map request: the warning must not fire.
        Path dumpIrOut = tmpDir.get().resolve("build/sm_dumpir");
        CompilationOrchestrator dumpIrOnly = new CompilationOrchestrator(
            entryFile, dumpIrOut, false, true, true, false, Backend.JVM,
            null, roots, Path.of(".").toAbsolutePath().normalize());
        ByteArrayOutputStream capturedDumpIr = new ByteArrayOutputStream();
        boolean dumpIrSuccess;
        try {
            ERR_CAPTURE.set(capturedDumpIr);
            dumpIrSuccess = dumpIrOnly.compile();
        } finally {
            ERR_CAPTURE.remove();
        }
        check(dumpIrSuccess, "JVM compile with --dump-ir (no --source-map) succeeds");
        check(!capturedDumpIr.toString(StandardCharsets.UTF_8).contains("source-map"),
            "no source-map warning for a --dump-ir-derived sourceMap flag: "
                + capturedDumpIr.toString(StandardCharsets.UTF_8));
        check(Files.exists(dumpIrOut.resolve("Sm_main.java")),
            "the --dump-ir compile still writes the .java artifact");

        // Explicit --source-map together with --dump-ir still warns.
        CompilationOrchestrator both = new CompilationOrchestrator(
            entryFile, outputDir, false, true, true, true, Backend.JVM,
            null, roots, Path.of(".").toAbsolutePath().normalize());
        ByteArrayOutputStream capturedBoth = new ByteArrayOutputStream();
        boolean bothSuccess;
        try {
            ERR_CAPTURE.set(capturedBoth);
            bothSuccess = both.compile();
        } finally {
            ERR_CAPTURE.remove();
        }
        check(bothSuccess, "JVM compile with --dump-ir --source-map succeeds");
        check(capturedBoth.toString(StandardCharsets.UTF_8).contains("source-map"),
            "--dump-ir --source-map still prints the warning: "
                + capturedBoth.toString(StandardCharsets.UTF_8));
    }

    /**
     * Strict backend-field pins (ISSUE-0269; ISSUE-0169 remediation,
     * ISSUE-0471): the manifest backend is exactly {@code "luajit"} |
     * {@code "jvm"} | {@code "js"} — the tolerant {@code lua}/
     * case/whitespace variants are E2010 at the backend value range,
     * and a valid CLI alias {@code lua|luajit|jvm|js} overrides a valid
     * manifest (the retired DealConfig surface).
     */
    private static void testStrictBackendField() {
        System.out.println("-- Strict manifest backend field --");

        try {
            // Valid strict values parse cleanly through the strict parser.
            for (String ok : new String[] {
                    "{\"languageVersion\": \"1.2\", \"backend\": \"jvm\"}",
                    "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\"}",
                    "{\"languageVersion\": \"1.2\", \"backend\": \"js\"}"}) {
                StrictManifestParser.StrictManifestParseResult r =
                    StrictManifestParser.parse("deal.json", ok);
                check(r.failure() == null && r.manifest() != null,
                    "deal.json " + ok + " parses strictly: " + r.failure());
            }

            // The retired tolerant aliases are E2010 at the backend value
            // range (exactly one diagnostic, no manifest published).
            for (String bad : new String[] {
                    "{\"languageVersion\": \"1.2\", \"backend\": \"lua\"}",
                    "{\"languageVersion\": \"1.2\", \"backend\": \"JVM\"}",
                    "{\"languageVersion\": \"1.2\", \"backend\": \"  Lua \"}",
                    "{\"languageVersion\": \"1.2\", \"backend\": \"wasm\"}"}) {
                StrictManifestParser.StrictManifestParseResult r =
                    StrictManifestParser.parse("deal.json", bad);
                check(r.manifest() == null && r.failure() != null,
                    "deal.json " + bad + " is rejected strictly");
                if (r.failure() != null) {
                    CompilerDiagnostic d = r.failure();
                    check("E2010".equals(d.code()) && "error".equals(d.severity()),
                        "unsupported backend is an E2010 error: " + d);
                    check(d.message().contains("luajit")
                            && d.message().contains("jvm")
                            && d.message().contains("js"),
                        "error message names supported backends: " + d.message());
                    check(d.range().origin() == RangeOrigin.SOURCE
                            && "deal.json".equals(d.range().file()),
                        "backend E2010 is SOURCE-anchored at the manifest path: "
                            + d.range());
                }
            }
        } catch (Exception e) {
            fail("strict backend field: " + e.getMessage());
        }

        // End to end: a valid CLI alias --backend lua selects LuaJIT
        // through the CLI exactly like --backend luajit; the strict
        // manifest carries no backend. The per-thread temp root may
        // still hold the orchestrator-jvm fixture's deal.json — the
        // alias project must be the only ancestor manifest, so the root
        // manifest is removed first.
        try {
            Files.deleteIfExists(tmpDir.get().resolve("deal.json"));
            writeFile("lua_proj/deal.json",
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"]}\n");
            writeFile("lua_proj/src/lua_alias_main.deal",
                "export function main(): null { return null; }\n"
                + "export function run(): null {}");
            Path luaEntry = tmpDir.get().resolve("lua_proj/src/lua_alias_main.deal")
                .toAbsolutePath();
            Path luaOut = tmpDir.get().resolve("build/lua_alias");
            int rc = deal.Main.run(new String[] {
                "compile", luaEntry.toString(),
                "--output", luaOut.toString(),
                "--backend", "lua"});
            check(rc == 0, "--backend lua alias compiles");
            check(Files.exists(luaOut.resolve("lua_alias_main.lua")),
                "--backend lua emits the .lua artifact");
            check(!Files.exists(luaOut.resolve("Lua_alias_main.java")),
                "--backend lua emits no .java artifact");
        } catch (IOException e) {
            fail("CLI 'lua' alias test IO: " + e.getMessage());
        }

        // End to end: the strict manifest backend "jvm" selects the JVM
        // backend through the CLI (no --backend flag).
        try {
            Files.deleteIfExists(tmpDir.get().resolve("deal.json"));
            writeFile("jvm_proj/deal.json",
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"], \"backend\": \"jvm\"}\n");
            writeFile("jvm_proj/src/jvm_alias_main.deal",
                "export function main(): null { return null; }\n"
                + "export function run(): int { return 6 * 7; }");
            Path jvmEntry = tmpDir.get().resolve("jvm_proj/src/jvm_alias_main.deal")
                .toAbsolutePath();
            Path jvmOut = tmpDir.get().resolve("build/jvm_alias");
            int rc = deal.Main.run(new String[] {
                "compile", jvmEntry.toString(),
                "--output", jvmOut.toString()});
            check(rc == 0, "deal.json backend 'jvm' compiles");
            check(Files.exists(jvmOut.resolve("Jvm_alias_main.java")),
                "deal.json 'jvm' emits the .java artifact");
            check(!Files.exists(jvmOut.resolve("jvm_alias_main.lua")),
                "deal.json 'jvm' emits no .lua artifact");

            // A manifest "backend": "lua" is E2010 through the CLI — the
            // retired tolerant alias never reaches compilation.
            writeFile("bad_proj/deal.json",
                "{\"languageVersion\": \"1.2\", \"backend\": \"lua\"}\n");
            writeFile("bad_proj/src/bad_main.deal",
                "export function main(): null { return null; }\n");
            Path badEntry = tmpDir.get().resolve("bad_proj/src/bad_main.deal")
                .toAbsolutePath();
            ByteArrayOutputStream badErr = new ByteArrayOutputStream();
            int badRc;
            try {
                ERR_CAPTURE.set(new PrintStream(badErr, true, StandardCharsets.UTF_8));
                badRc = deal.Main.run(new String[] {
                    "compile", badEntry.toString(),
                    "--output", tmpDir.get().resolve("build/bad_alias").toString()});
            } finally {
                ERR_CAPTURE.remove();
            }
            check(badRc == 1, "deal.json backend 'lua' exits 1");
            check(badErr.toString(StandardCharsets.UTF_8).contains("E2010"),
                "deal.json 'lua' is E2010 through the CLI: "
                    + badErr.toString(StandardCharsets.UTF_8));
        } catch (IOException e) {
            fail("CLI strict backend test IO: " + e.getMessage());
        }
    }

    private static void testCliBackendFlag() {
        System.out.println("-- CLI --backend flag --");

        try {
            // ISSUE-0269: the CLI locates exactly one ancestor exact-v1.2
            // manifest — the temp project carries its own (backend
            // absent: the CLI flags / default drive the backend).
            writeFile("deal.json",
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"]}\n");
            writeFile("src/cli_main.deal", """
                import * as console from "std/console"
                export function main(): null { return null; }
                export function run(): int {
                  console.log("cli-jvm");
                  return 6 * 7;
                }
                """);

            Path entry = tmpDir.get().resolve("src/cli_main.deal").toAbsolutePath();
            Path outDir = tmpDir.get().resolve("build/cli_jvm");

            int rc = deal.Main.run(new String[] {
                "compile", entry.toString(),
                "--output", outDir.toString(),
                "--backend", "jvm"});
            check(rc == 0, "CLI --backend jvm exits 0");
            check(Files.exists(outDir.resolve("Cli_main.java")),
                "CLI emitted the .java artifact");
            check(!Files.exists(outDir.resolve("cli_main.lua")),
                "CLI emitted no .lua artifact for jvm");

            int rcBad = deal.Main.run(new String[] {
                "compile", entry.toString(),
                "--output", outDir.toString(),
                "--backend", "wasm"});
            check(rcBad == 1, "CLI rejects unknown backend");

            // Default (no flag, no manifest backend field) stays LuaJIT.
            Path outLua = tmpDir.get().resolve("build/cli_default");
            int rcDefault = deal.Main.run(new String[] {
                "compile", entry.toString(),
                "--output", outLua.toString()});
            check(rcDefault == 0, "CLI default backend compiles");
            check(Files.exists(outLua.resolve("cli_main.lua")),
                "CLI default backend emits .lua");

            // --dump-ir derives the sourceMap flag internally (IR hardening
            // enables source maps with dumps); the JVM source-map warning
            // must fire only for an explicit --source-map request.
            ByteArrayOutputStream capturedDump = new ByteArrayOutputStream();
            try {
                ERR_CAPTURE.set(capturedDump);
                int rcDump = deal.Main.run(new String[] {
                    "compile", entry.toString(),
                    "--output", outDir.toString(),
                    "--backend", "jvm", "--dump-ir"});
                check(rcDump == 0, "CLI --backend jvm --dump-ir exits 0");
            } finally {
                ERR_CAPTURE.remove();
            }
            check(!capturedDump.toString(StandardCharsets.UTF_8).contains("source-map"),
                "--dump-ir alone prints no JVM source-map warning: "
                    + capturedDump.toString(StandardCharsets.UTF_8));

            ByteArrayOutputStream capturedBoth = new ByteArrayOutputStream();
            try {
                ERR_CAPTURE.set(capturedBoth);
                int rcBoth = deal.Main.run(new String[] {
                    "compile", entry.toString(),
                    "--output", outDir.toString(),
                    "--backend", "jvm", "--dump-ir", "--source-map"});
                check(rcBoth == 0, "CLI --backend jvm --dump-ir --source-map exits 0");
            } finally {
                ERR_CAPTURE.remove();
            }
            check(capturedBoth.toString(StandardCharsets.UTF_8).contains("source-map"),
                "--dump-ir --source-map prints the JVM source-map warning: "
                    + capturedBoth.toString(StandardCharsets.UTF_8));
        } catch (IOException e) {
            fail("CLI backend test IO: " + e.getMessage());
        }
    }

    /**
     * ISSUE-0358 IR-pin migration: exact IR-dump assertions for the
     * twelve multi-module JSON-slice cases whose
     * {@code irContains}/{@code irNotContains} pins ran against the
     * concatenated orchestrator {@code --dump-ir} output
     * (legacy JSON conformance harness.collectIrDumps framing: one
     * {@code === IR: <file> ===} header per module dump, sorted by
     * file name). Every expected block is the exact dump text with
     * the per-test temp project root normalized to {@code <PROJECT>};
     * the comparison is full-text equality — never a substring check.
     */
    private static void testIrDumpExactMigration() throws Exception {
        System.out.println("-- IR-dump exact migration (ISSUE-0358) --");

        { // jvm-async-slice :: jvm-async-multi-module
            String proj = "irpin00";
            writeFile(proj + "/lib.deal", "export async function plus(a: int, b: int): int { return a + b; }\nexport async function tag(s: string): string { return \"[\" + s + \"]\"; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\nexport async function test(): int {\n  let s: string = await lib.tag(\"x\");\n  if (s === \"[x]\") { return await lib.plus(2, 3); }\n  return 0;\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-async-slice :: jvm-async-multi-module: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation fails the cross-module async closure closed with
            // E6005 SHARED_EMITTER_COVERAGE (EXTERNAL_ASYNC_CALL) and
            // stages nothing (the per-module async-entry linkage is the
            // calls child's).
            CompilationOrchestrator irPinAsyncProduction =
                new CompilationOrchestrator(
                    irPinEntry, irPinRoot.resolve("out-production"), false,
                    false, false, false, Backend.JVM, irPinExternals,
                    List.of(irPinRoot), null, null,
                    CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
                        ReleaseConfiguration.releaseCapabilityRegistry()));
            check(!irPinAsyncProduction.compile()
                    && irPinAsyncProduction.diagnostics().stream().anyMatch(d ->
                        "E6005".equals(d.code())
                            && d.message().contains("EXTERNAL_ASYNC_CALL")),
                "jvm-async-slice :: jvm-async-multi-module: the release-owned "
                    + "production invocation fails the closure closed: "
                    + irPinAsyncProduction.diagnostics());
            check(!Files.exists(irPinRoot.resolve("out-production")),
                "jvm-async-slice :: jvm-async-multi-module: the production "
                    + "failure stages no artifact");
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-2:71
  export @<PROJECT>/lib.deal:1:1-2:6
    [boundary: export]
    async function plus: int @<PROJECT>/lib.deal:1:8-2:6
      param a: int @<PROJECT>/lib.deal:1:28-1:34
        [boundary: param-entry]
      param b: int @<PROJECT>/lib.deal:1:36-1:42
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:1:51-1:65
          [boundary: async-completion]
          binary + : int @<PROJECT>/lib.deal:1:58-1:62
            ident a : int @<PROJECT>/lib.deal:1:58-1:58
            ident b : int @<PROJECT>/lib.deal:1:62-1:62
  export @<PROJECT>/lib.deal:2:1-2:71
    [boundary: export]
    async function tag: string @<PROJECT>/lib.deal:2:8-2:71
      param s: string @<PROJECT>/lib.deal:2:27-2:36
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:2:48-2:70
          [boundary: async-completion]
          binary + : string @<PROJECT>/lib.deal:2:55-2:67
            binary + : string @<PROJECT>/lib.deal:2:55-2:61
              literal "[" : string @<PROJECT>/lib.deal:2:55-2:57
              ident s : string @<PROJECT>/lib.deal:2:61-2:61
            literal "]" : string @<PROJECT>/lib.deal:2:65-2:67

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-7:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-3:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-3:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:3:1-7:2
    [boundary: export]
    async function test: int @<PROJECT>/main.deal:3:8-7:2
      body
        let s: string @<PROJECT>/main.deal:4:3-5:4
          [boundary: var-annotation]
          await : string @<PROJECT>/main.deal:4:19-4:36
            call : string @<PROJECT>/main.deal:4:25-4:36
              member .tag : async(string)->string @<PROJECT>/main.deal:4:25-4:31
                [boundary: table-read]
                ident lib : table @<PROJECT>/main.deal:4:25-4:27
                  [boundary: import]
              literal "x" : string @<PROJECT>/main.deal:4:33-4:35
        if @<PROJECT>/main.deal:5:3-6:8
          binary === : boolean @<PROJECT>/main.deal:5:7-5:17
            ident s : string @<PROJECT>/main.deal:5:7-5:7
            literal "[x]" : string @<PROJECT>/main.deal:5:13-5:17
          block @<PROJECT>/main.deal:5:20-5:51
            return @<PROJECT>/main.deal:5:22-5:51
              [boundary: async-completion]
              await : int @<PROJECT>/main.deal:5:29-5:48
                call : int @<PROJECT>/main.deal:5:35-5:48
                  member .plus : async(int,int)->int @<PROJECT>/main.deal:5:35-5:42
                    [boundary: table-read]
                    ident lib : table @<PROJECT>/main.deal:5:35-5:37
                      [boundary: import]
                  literal 2 : int @<PROJECT>/main.deal:5:44-5:44
                  literal 3 : int @<PROJECT>/main.deal:5:47-5:47
        return @<PROJECT>/main.deal:6:3-7:1
          [boundary: async-completion]
          literal 0 : int @<PROJECT>/main.deal:6:10-6:10
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-async-slice :: jvm-async-multi-module: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-host-abi-slice :: jvm-host-export-presence
            String proj = "irpin01";
            writeFile(proj + "/" + "bindings/log.d.deal", "export function info(level: int, s: string): null;\nexport function add(a: int, b: int): int;");
            writeFile(proj + "/entry.deal", "import * as log from \"host/log\"\nexport function main(): null {\n  log.info(1, \"hello\");\n  return null;\n}\nexport function run(): int { return log.add(2, 3); }");
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("entry.deal");
            Path irPinOut = irPinRoot.resolve("out");
            // The test-only isolated-phase path: the externals wiring is
            // the raw specifier → absolute declaration path map (the
            // production conformance harness routes the same fixture
            // through ProjectLocator).
            Map<String, String> irPinExternals = Map.of("host/log",
                irPinRoot.resolve("bindings/log.d.deal").toString());
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-host-abi-slice :: jvm-host-export-presence: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation fails the host-importing closure closed with
            // E6005 SHARED_EMITTER_COVERAGE (HOST_MODULE_IMPORT) and
            // stages nothing (the host load is the calls/FFI children's).
            CompilationOrchestrator irPinHostProduction =
                new CompilationOrchestrator(
                    irPinEntry, irPinRoot.resolve("out-production"), false,
                    false, false, false, Backend.JVM, irPinExternals,
                    List.of(irPinRoot), null, null,
                    CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
                        ReleaseConfiguration.releaseCapabilityRegistry()));
            check(!irPinHostProduction.compile()
                    && irPinHostProduction.diagnostics().stream().anyMatch(d ->
                        "E6005".equals(d.code())
                            && d.message().contains("HOST_MODULE_IMPORT")),
                "jvm-host-abi-slice :: jvm-host-export-presence: the "
                    + "release-owned production invocation fails the closure "
                    + "closed: " + irPinHostProduction.diagnostics());
            check(!Files.exists(irPinRoot.resolve("out-production")),
                "jvm-host-abi-slice :: jvm-host-export-presence: the "
                    + "production failure stages no artifact");
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: entry.ir.txt ===
module @<PROJECT>/entry.deal:1:1-6:53
  import * as log from "host/log" @<PROJECT>/entry.deal:1:1-2:6
    [boundary: host-in]
    [boundary: import]
  export @<PROJECT>/entry.deal:2:1-6:6
    [boundary: export]
    function main: null @<PROJECT>/entry.deal:2:8-6:6
      body
        expr-stmt @<PROJECT>/entry.deal:3:3-3:22
          call : null @<PROJECT>/entry.deal:3:3-3:22
            [boundary: external-boundary]
            member .info : (int,string)->null @<PROJECT>/entry.deal:3:3-3:10
              [boundary: table-read]
              ident log : table @<PROJECT>/entry.deal:3:3-3:5
                [boundary: import]
            literal 1 : int @<PROJECT>/entry.deal:3:12-3:12
            literal "hello" : string @<PROJECT>/entry.deal:3:15-3:21
        return @<PROJECT>/entry.deal:4:3-5:1
          literal null : null @<PROJECT>/entry.deal:4:10-4:13
  export @<PROJECT>/entry.deal:6:1-6:53
    [boundary: export]
    function run: int @<PROJECT>/entry.deal:6:8-6:53
      body
        return @<PROJECT>/entry.deal:6:30-6:52
          [boundary: return]
          call : int @<PROJECT>/entry.deal:6:37-6:49
            [boundary: external-boundary]
            member .add : (int,int)->int @<PROJECT>/entry.deal:6:37-6:43
              [boundary: table-read]
              ident log : table @<PROJECT>/entry.deal:6:37-6:39
                [boundary: import]
            literal 2 : int @<PROJECT>/entry.deal:6:45-6:45
            literal 3 : int @<PROJECT>/entry.deal:6:48-6:48
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-host-abi-slice :: jvm-host-export-presence: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-integration-join :: jvm-join-xmod-class-descriptor
            String proj = "irpin02";
            writeFile(proj + "/lib.deal", "export class Point { x: int = 0; }\nexport function make(x: int): Point { return { x: x }; }\n");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nfunction use(p: lib.Point): int { return p.x; }\nexport function run(): int {\n  let got: int = use(lib.make(7));\n  return got;\n}\nexport function main(): null { return null; }\n");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-integration-join :: jvm-join-xmod-class-descriptor: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-3:1
  export @<PROJECT>/lib.deal:1:1-2:6
    [boundary: export]
    class Point @<PROJECT>/lib.deal:1:8-1:34
      field x: int @<PROJECT>/lib.deal:1:22-1:34
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:1:31-1:31
  export @<PROJECT>/lib.deal:2:1-3:1
    [boundary: export]
    function make: Point @<PROJECT>/lib.deal:2:8-3:1
      param x: int @<PROJECT>/lib.deal:2:22-2:28
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:2:39-2:56
          [boundary: return]
          object : @irpin02/Point @<PROJECT>/lib.deal:2:46-2:53
            [boundary: class-construct]
            ident x : int @<PROJECT>/lib.deal:2:51-2:51

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-8:1
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:8
    [boundary: import]
  function use: int @<PROJECT>/main.deal:2:1-3:6
    param p: @lib/Point @<PROJECT>/main.deal:2:14-2:26
      [boundary: param-entry]
    body
      return @<PROJECT>/main.deal:2:35-2:47
        [boundary: return]
        member .x : int @<PROJECT>/main.deal:2:42-2:44
          ident p : @irpin02/Point @<PROJECT>/main.deal:2:42-2:42
  export @<PROJECT>/main.deal:3:1-7:6
    [boundary: export]
    function run: int @<PROJECT>/main.deal:3:8-7:6
      body
        let got: int @<PROJECT>/main.deal:4:3-5:8
          [boundary: var-annotation]
          call : int @<PROJECT>/main.deal:4:18-4:33
            ident use : (@irpin02/Point)->int @<PROJECT>/main.deal:4:18-4:20
            call : @irpin02/Point @<PROJECT>/main.deal:4:22-4:32
              member .make : (int)->@irpin02/Point @<PROJECT>/main.deal:4:22-4:29
                [boundary: table-read]
                ident lib : table @<PROJECT>/main.deal:4:22-4:24
                  [boundary: import]
              literal 7 : int @<PROJECT>/main.deal:4:31-4:31
        return @<PROJECT>/main.deal:5:3-6:1
          [boundary: return]
          ident got : int @<PROJECT>/main.deal:5:10-5:12
  export @<PROJECT>/main.deal:7:1-8:1
    [boundary: export]
    function main: null @<PROJECT>/main.deal:7:8-8:1
      body
        return @<PROJECT>/main.deal:7:32-7:45
          literal null : null @<PROJECT>/main.deal:7:39-7:42
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-integration-join :: jvm-join-xmod-class-descriptor: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-integration-join :: jvm-join-xmod-table-read-desc
            String proj = "irpin03";
            writeFile(proj + "/lib.deal", "export class Item { tag: string = \"\"; }\nexport function make(tag: string): Item { return { tag: tag }; }\n");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function run(): string {\n  let holder: table = { item: lib.make(\"x\") };\n  let i: lib.Item = holder.item;\n  return i.tag;\n}\nexport function main(): null { return null; }\n");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-integration-join :: jvm-join-xmod-table-read-desc: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-3:1
  export @<PROJECT>/lib.deal:1:1-2:6
    [boundary: export]
    class Item @<PROJECT>/lib.deal:1:8-1:39
      field tag: string @<PROJECT>/lib.deal:1:21-1:39
        [boundary: class-default]
        literal "" : string @<PROJECT>/lib.deal:1:35-1:36
  export @<PROJECT>/lib.deal:2:1-3:1
    [boundary: export]
    function make: Item @<PROJECT>/lib.deal:2:8-3:1
      param tag: string @<PROJECT>/lib.deal:2:22-2:33
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:2:43-2:64
          [boundary: return]
          object : @irpin03/Item @<PROJECT>/lib.deal:2:50-2:61
            [boundary: class-construct]
            ident tag : string @<PROJECT>/lib.deal:2:57-2:59

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-8:1
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-7:6
    [boundary: export]
    function run: string @<PROJECT>/main.deal:2:8-7:6
      body
        let holder: table @<PROJECT>/main.deal:3:3-4:5
          [boundary: var-annotation]
          object : table @<PROJECT>/main.deal:3:23-3:45
            call : @irpin03/Item @<PROJECT>/main.deal:3:31-3:43
              member .make : (string)->@irpin03/Item @<PROJECT>/main.deal:3:31-3:38
                [boundary: table-read]
                ident lib : table @<PROJECT>/main.deal:3:31-3:33
                  [boundary: import]
              literal "x" : string @<PROJECT>/main.deal:3:40-3:42
        let i: @irpin03/Item @<PROJECT>/main.deal:4:3-5:8
          [boundary: var-annotation]
          member .item : @irpin03/Item @<PROJECT>/main.deal:4:21-4:31
            [boundary: table-read]
            ident holder : table @<PROJECT>/main.deal:4:21-4:26
        return @<PROJECT>/main.deal:5:3-6:1
          [boundary: return]
          member .tag : string @<PROJECT>/main.deal:5:10-5:14
            ident i : @irpin03/Item @<PROJECT>/main.deal:5:10-5:10
  export @<PROJECT>/main.deal:7:1-8:1
    [boundary: export]
    function main: null @<PROJECT>/main.deal:7:8-8:1
      body
        return @<PROJECT>/main.deal:7:32-7:45
          literal null : null @<PROJECT>/main.deal:7:39-7:42
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-integration-join :: jvm-join-xmod-table-read-desc: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-integration-join :: jvm-join-xmod-mismatch-desc
            String proj = "irpin04";
            writeFile(proj + "/modela.deal", "export class Item { tag: string = \"\"; }\nexport function make(tag: string): Item { return { tag: tag }; }\n");
            writeFile(proj + "/modelb.deal", "export class Item { tag: string = \"\"; }\n");
            writeFile(proj + "/main.deal", "import * as modela from \"./modela\"\nimport * as modelb from \"./modelb\"\nexport function run(): string {\n  let holder: table = { item: modela.make(\"a\") };\n  let b: modelb.Item = holder.item;\n  return b.tag;\n}\nexport function main(): null { return null; }\n");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-integration-join :: jvm-join-xmod-mismatch-desc: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-9:1
  import * as modela from "./modela" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  import * as modelb from "./modelb" @<PROJECT>/main.deal:2:1-3:6
    [boundary: import]
  export @<PROJECT>/main.deal:3:1-8:6
    [boundary: export]
    function run: string @<PROJECT>/main.deal:3:8-8:6
      body
        let holder: table @<PROJECT>/main.deal:4:3-5:5
          [boundary: var-annotation]
          object : table @<PROJECT>/main.deal:4:23-4:48
            call : @irpin04/Item @<PROJECT>/main.deal:4:31-4:46
              member .make : (string)->@irpin04/Item @<PROJECT>/main.deal:4:31-4:41
                [boundary: table-read]
                ident modela : table @<PROJECT>/main.deal:4:31-4:36
                  [boundary: import]
              literal "a" : string @<PROJECT>/main.deal:4:43-4:45
        let b: @irpin04/Item @<PROJECT>/main.deal:5:3-6:8
          [boundary: var-annotation]
          member .item : @irpin04/Item @<PROJECT>/main.deal:5:24-5:34
            [boundary: table-read]
            ident holder : table @<PROJECT>/main.deal:5:24-5:29
        return @<PROJECT>/main.deal:6:3-7:1
          [boundary: return]
          member .tag : string @<PROJECT>/main.deal:6:10-6:14
            ident b : @irpin04/Item @<PROJECT>/main.deal:6:10-6:10
  export @<PROJECT>/main.deal:8:1-9:1
    [boundary: export]
    function main: null @<PROJECT>/main.deal:8:8-9:1
      body
        return @<PROJECT>/main.deal:8:32-8:45
          literal null : null @<PROJECT>/main.deal:8:39-8:42

=== IR: modela.ir.txt ===
module @<PROJECT>/modela.deal:1:1-3:1
  export @<PROJECT>/modela.deal:1:1-2:6
    [boundary: export]
    class Item @<PROJECT>/modela.deal:1:8-1:39
      field tag: string @<PROJECT>/modela.deal:1:21-1:39
        [boundary: class-default]
        literal "" : string @<PROJECT>/modela.deal:1:35-1:36
  export @<PROJECT>/modela.deal:2:1-3:1
    [boundary: export]
    function make: Item @<PROJECT>/modela.deal:2:8-3:1
      param tag: string @<PROJECT>/modela.deal:2:22-2:33
        [boundary: param-entry]
      body
        return @<PROJECT>/modela.deal:2:43-2:64
          [boundary: return]
          object : @irpin04/Item @<PROJECT>/modela.deal:2:50-2:61
            [boundary: class-construct]
            ident tag : string @<PROJECT>/modela.deal:2:57-2:59

=== IR: modelb.ir.txt ===
module @<PROJECT>/modelb.deal:1:1-2:1
  export @<PROJECT>/modelb.deal:1:1-2:1
    [boundary: export]
    class Item @<PROJECT>/modelb.deal:1:8-1:39
      field tag: string @<PROJECT>/modelb.deal:1:21-1:39
        [boundary: class-default]
        literal "" : string @<PROJECT>/modelb.deal:1:35-1:36
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-integration-join :: jvm-join-xmod-mismatch-desc: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-modules-slice :: jvm-mod-imported-direct-call
            String proj = "irpin05";
            writeFile(proj + "/lib.deal", "export function add(a: int, b: int): int { return a + b; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nexport function run(): int { return lib.add(2, 3); }");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-modules-slice :: jvm-mod-imported-direct-call: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());

            // ISSUE-0654: the release-owned production invocation
            // compiles the cross-module-call closure through the realized
            // CALL(EXTERNAL) SHARED_BODY arm (the callee unit's
            // EXTERNAL_ENTRY inside the one project class) and stages its
            // one project artifact.
            Path irPinProductionOut = irPinRoot.resolve("out-production");
            CompilationOrchestrator irPinCallProduction =
                new CompilationOrchestrator(
                    irPinEntry, irPinProductionOut, false,
                    false, false, false, Backend.JVM, irPinExternals,
                    List.of(irPinRoot), null, null,
                    CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
                        ReleaseConfiguration.releaseCapabilityRegistry()));
            boolean irPinProductionOk = irPinCallProduction.compile();
            check(irPinProductionOk
                    && irPinCallProduction.diagnostics().isEmpty(),
                "jvm-modules-slice :: jvm-mod-imported-direct-call: the "
                    + "release-owned production invocation compiles the closure: "
                    + irPinCallProduction.diagnostics());
            check(irPinProductionOk
                    && irPinCallProduction.semanticEmissionCount() == 1
                    && irPinCallProduction.retainedEmissionCount() == 0,
                "jvm-modules-slice :: jvm-mod-imported-direct-call: the "
                    + "production compile emits one project artifact and no "
                    + "retained artifact: semantic="
                    + irPinCallProduction.semanticEmissionCount() + " retained="
                    + irPinCallProduction.retainedEmissionCount());
            check(Files.exists(irPinProductionOut.resolve("Main.java")),
                "jvm-modules-slice :: jvm-mod-imported-direct-call: the "
                    + "production compile stages the entry project class");
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-1:59
  export @<PROJECT>/lib.deal:1:1-1:59
    [boundary: export]
    function add: int @<PROJECT>/lib.deal:1:8-1:59
      param a: int @<PROJECT>/lib.deal:1:21-1:27
        [boundary: param-entry]
      param b: int @<PROJECT>/lib.deal:1:29-1:35
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:1:44-1:58
          [boundary: return]
          binary + : int @<PROJECT>/lib.deal:1:51-1:55
            ident a : int @<PROJECT>/lib.deal:1:51-1:51
            ident b : int @<PROJECT>/lib.deal:1:55-1:55

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-4:53
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:4:1-4:53
    [boundary: export]
    function run: int @<PROJECT>/main.deal:4:8-4:53
      body
        return @<PROJECT>/main.deal:4:30-4:52
          [boundary: return]
          call : int @<PROJECT>/main.deal:4:37-4:49
            member .add : (int,int)->int @<PROJECT>/main.deal:4:37-4:43
              [boundary: table-read]
              ident lib : table @<PROJECT>/main.deal:4:37-4:39
                [boundary: import]
            literal 2 : int @<PROJECT>/main.deal:4:45-4:45
            literal 3 : int @<PROJECT>/main.deal:4:48-4:48
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-modules-slice :: jvm-mod-imported-direct-call: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-class-export-import
            String proj = "irpin06";
            writeFile(proj + "/lib.deal", "export class Point {\n  x: int = 0;\n  y: int = 0;\n}\nexport function make(x: int, y: int): Point { return { x: x, y: y }; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nexport function run(): int {\n  let p: lib.Point = lib.make(3, 4);\n  return p.x * 10 + p.y;\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-class-export-import: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-5:71
  export @<PROJECT>/lib.deal:1:1-5:6
    [boundary: export]
    class Point @<PROJECT>/lib.deal:1:8-4:1
      field x: int @<PROJECT>/lib.deal:2:3-3:3
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:2:12-2:12
      field y: int @<PROJECT>/lib.deal:3:3-4:1
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:3:12-3:12
  export @<PROJECT>/lib.deal:5:1-5:71
    [boundary: export]
    function make: Point @<PROJECT>/lib.deal:5:8-5:71
      param x: int @<PROJECT>/lib.deal:5:22-5:28
        [boundary: param-entry]
      param y: int @<PROJECT>/lib.deal:5:30-5:36
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:5:47-5:70
          [boundary: return]
          object : @irpin06/Point @<PROJECT>/lib.deal:5:54-5:67
            [boundary: class-construct]
            ident x : int @<PROJECT>/lib.deal:5:59-5:59
            ident y : int @<PROJECT>/lib.deal:5:65-5:65

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-7:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:4:1-7:2
    [boundary: export]
    function run: int @<PROJECT>/main.deal:4:8-7:2
      body
        let p: @irpin06/Point @<PROJECT>/main.deal:5:3-6:8
          [boundary: var-annotation]
          call : @irpin06/Point @<PROJECT>/main.deal:5:22-5:35
            member .make : (int,int)->@irpin06/Point @<PROJECT>/main.deal:5:22-5:29
              [boundary: table-read]
              ident lib : table @<PROJECT>/main.deal:5:22-5:24
                [boundary: import]
            literal 3 : int @<PROJECT>/main.deal:5:31-5:31
            literal 4 : int @<PROJECT>/main.deal:5:34-5:34
        return @<PROJECT>/main.deal:6:3-7:1
          [boundary: return]
          binary + : int @<PROJECT>/main.deal:6:10-6:23
            binary * : int @<PROJECT>/main.deal:6:10-6:17
              member .x : int @<PROJECT>/main.deal:6:10-6:12
                ident p : @irpin06/Point @<PROJECT>/main.deal:6:10-6:10
              literal 10 : int @<PROJECT>/main.deal:6:16-6:17
            member .y : int @<PROJECT>/main.deal:6:21-6:23
              ident p : @irpin06/Point @<PROJECT>/main.deal:6:21-6:21
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-class-export-import: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-class-construction-defaults
            String proj = "irpin07";
            writeFile(proj + "/lib.deal", "export class Point {\n  x: int = 10;\n  y: int = 20;\n}\nexport function sum(p: Point): int { return p.x + p.y; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nexport function run(): int {\n  let a: lib.Point = {};\n  let b: lib.Point = { y: 5, x: 2 };\n  return a.x + a.y * 10 + lib.sum(b);\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-class-construction-defaults: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-5:57
  export @<PROJECT>/lib.deal:1:1-5:6
    [boundary: export]
    class Point @<PROJECT>/lib.deal:1:8-4:1
      field x: int @<PROJECT>/lib.deal:2:3-3:3
        [boundary: class-default]
        literal 10 : int @<PROJECT>/lib.deal:2:12-2:13
      field y: int @<PROJECT>/lib.deal:3:3-4:1
        [boundary: class-default]
        literal 20 : int @<PROJECT>/lib.deal:3:12-3:13
  export @<PROJECT>/lib.deal:5:1-5:57
    [boundary: export]
    function sum: int @<PROJECT>/lib.deal:5:8-5:57
      param p: Point @<PROJECT>/lib.deal:5:21-5:29
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:5:38-5:56
          [boundary: return]
          binary + : int @<PROJECT>/lib.deal:5:45-5:53
            member .x : int @<PROJECT>/lib.deal:5:45-5:47
              ident p : @irpin07/Point @<PROJECT>/lib.deal:5:45-5:45
            member .y : int @<PROJECT>/lib.deal:5:51-5:53
              ident p : @irpin07/Point @<PROJECT>/lib.deal:5:51-5:51

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-8:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:4:1-8:2
    [boundary: export]
    function run: int @<PROJECT>/main.deal:4:8-8:2
      body
        let a: @irpin07/Point @<PROJECT>/main.deal:5:3-6:5
          [boundary: var-annotation]
          object : @irpin07/Point @<PROJECT>/main.deal:5:22-5:23
            [boundary: class-construct]
        let b: @irpin07/Point @<PROJECT>/main.deal:6:3-7:8
          [boundary: var-annotation]
          object : @irpin07/Point @<PROJECT>/main.deal:6:22-6:35
            [boundary: class-construct]
            literal 5 : int @<PROJECT>/main.deal:6:27-6:27
            literal 2 : int @<PROJECT>/main.deal:6:33-6:33
        return @<PROJECT>/main.deal:7:3-8:1
          [boundary: return]
          binary + : int @<PROJECT>/main.deal:7:10-7:36
            binary + : int @<PROJECT>/main.deal:7:10-7:23
              member .x : int @<PROJECT>/main.deal:7:10-7:12
                ident a : @irpin07/Point @<PROJECT>/main.deal:7:10-7:10
              binary * : int @<PROJECT>/main.deal:7:16-7:23
                member .y : int @<PROJECT>/main.deal:7:16-7:18
                  ident a : @irpin07/Point @<PROJECT>/main.deal:7:16-7:16
                literal 10 : int @<PROJECT>/main.deal:7:22-7:23
            call : int @<PROJECT>/main.deal:7:27-7:36
              member .sum : (@irpin07/Point)->int @<PROJECT>/main.deal:7:27-7:33
                [boundary: table-read]
                ident lib : table @<PROJECT>/main.deal:7:27-7:29
                  [boundary: import]
              ident b : @irpin07/Point @<PROJECT>/main.deal:7:35-7:35
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-class-construction-defaults: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-class-param-pass
            String proj = "irpin08";
            writeFile(proj + "/lib.deal", "export class Pair {\n  left: int = 0;\n  right: int = 0;\n}\nexport function sum(p: Pair): int { return p.left + p.right; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nexport function run(): int {\n  let p: lib.Pair = { left: 5, right: 7 };\n  return lib.sum(p);\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-class-param-pass: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-5:63
  export @<PROJECT>/lib.deal:1:1-5:6
    [boundary: export]
    class Pair @<PROJECT>/lib.deal:1:8-4:1
      field left: int @<PROJECT>/lib.deal:2:3-3:7
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:2:15-2:15
      field right: int @<PROJECT>/lib.deal:3:3-4:1
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:3:16-3:16
  export @<PROJECT>/lib.deal:5:1-5:63
    [boundary: export]
    function sum: int @<PROJECT>/lib.deal:5:8-5:63
      param p: Pair @<PROJECT>/lib.deal:5:21-5:28
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:5:37-5:62
          [boundary: return]
          binary + : int @<PROJECT>/lib.deal:5:44-5:59
            member .left : int @<PROJECT>/lib.deal:5:44-5:49
              ident p : @irpin08/Pair @<PROJECT>/lib.deal:5:44-5:44
            member .right : int @<PROJECT>/lib.deal:5:53-5:59
              ident p : @irpin08/Pair @<PROJECT>/lib.deal:5:53-5:53

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-7:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:4:1-7:2
    [boundary: export]
    function run: int @<PROJECT>/main.deal:4:8-7:2
      body
        let p: @irpin08/Pair @<PROJECT>/main.deal:5:3-6:8
          [boundary: var-annotation]
          object : @irpin08/Pair @<PROJECT>/main.deal:5:21-5:41
            [boundary: class-construct]
            literal 5 : int @<PROJECT>/main.deal:5:29-5:29
            literal 7 : int @<PROJECT>/main.deal:5:39-5:39
        return @<PROJECT>/main.deal:6:3-7:1
          [boundary: return]
          call : int @<PROJECT>/main.deal:6:10-6:19
            member .sum : (@irpin08/Pair)->int @<PROJECT>/main.deal:6:10-6:16
              [boundary: table-read]
              ident lib : table @<PROJECT>/main.deal:6:10-6:12
                [boundary: import]
            ident p : @irpin08/Pair @<PROJECT>/main.deal:6:18-6:18
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-class-param-pass: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-class-return-mutate-roundtrip
            String proj = "irpin09";
            writeFile(proj + "/lib.deal", "export class Box {\n  value: int = 0;\n}\nexport function makeBox(): Box { return { value: 7 }; }\nexport function readBox(b: Box): int { return b.value; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nexport function run(): int {\n  let b: lib.Box = lib.makeBox();\n  b.value = b.value + 5;\n  return lib.readBox(b);\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-class-return-mutate-roundtrip: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-5:57
  export @<PROJECT>/lib.deal:1:1-4:6
    [boundary: export]
    class Box @<PROJECT>/lib.deal:1:8-3:1
      field value: int @<PROJECT>/lib.deal:2:3-3:1
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:2:16-2:16
  export @<PROJECT>/lib.deal:4:1-5:6
    [boundary: export]
    function makeBox: Box @<PROJECT>/lib.deal:4:8-5:6
      body
        return @<PROJECT>/lib.deal:4:34-4:55
          [boundary: return]
          object : @irpin09/Box @<PROJECT>/lib.deal:4:41-4:52
            [boundary: class-construct]
            literal 7 : int @<PROJECT>/lib.deal:4:50-4:50
  export @<PROJECT>/lib.deal:5:1-5:57
    [boundary: export]
    function readBox: int @<PROJECT>/lib.deal:5:8-5:57
      param b: Box @<PROJECT>/lib.deal:5:25-5:31
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:5:40-5:56
          [boundary: return]
          member .value : int @<PROJECT>/lib.deal:5:47-5:53
            ident b : @irpin09/Box @<PROJECT>/lib.deal:5:47-5:47

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-8:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:6
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  export @<PROJECT>/main.deal:4:1-8:2
    [boundary: export]
    function run: int @<PROJECT>/main.deal:4:8-8:2
      body
        let b: @irpin09/Box @<PROJECT>/main.deal:5:3-6:3
          [boundary: var-annotation]
          call : @irpin09/Box @<PROJECT>/main.deal:5:20-5:32
            member .makeBox : ()->@irpin09/Box @<PROJECT>/main.deal:5:20-5:30
              [boundary: table-read]
              ident lib : table @<PROJECT>/main.deal:5:20-5:22
                [boundary: import]
        expr-stmt @<PROJECT>/main.deal:6:3-6:23
          assign = : int @<PROJECT>/main.deal:6:3-6:23
            [boundary: field-write]
            member .value : int @<PROJECT>/main.deal:6:3-6:9
              ident b : @irpin09/Box @<PROJECT>/main.deal:6:3-6:3
            binary + : int @<PROJECT>/main.deal:6:13-6:23
              member .value : int @<PROJECT>/main.deal:6:13-6:19
                ident b : @irpin09/Box @<PROJECT>/main.deal:6:13-6:13
              literal 5 : int @<PROJECT>/main.deal:6:23-6:23
        return @<PROJECT>/main.deal:7:3-8:1
          [boundary: return]
          call : int @<PROJECT>/main.deal:7:10-7:23
            member .readBox : (@irpin09/Box)->int @<PROJECT>/main.deal:7:10-7:20
              [boundary: table-read]
              ident lib : table @<PROJECT>/main.deal:7:10-7:12
                [boundary: import]
            ident b : @irpin09/Box @<PROJECT>/main.deal:7:22-7:22
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-class-return-mutate-roundtrip: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-same-name-isolation
            String proj = "irpin10";
            writeFile(proj + "/modela.deal", "export class Item {\n  tag: string = \"\";\n}\nexport function tag(i: Item): string { return \"a:\" + i.tag; }");
            writeFile(proj + "/modelb.deal", "export class Item {\n  tag: string = \"\";\n}\nexport function tag(i: Item): string { return \"b:\" + i.tag; }");
            writeFile(proj + "/main.deal", "import * as modela from \"./modela\"\nimport * as modelb from \"./modelb\"\nimport * as console from \"std/console\"\nexport function main(): null { return null; }\n\nexport function run(): null {\n  let a: modela.Item = { tag: \"one\" };\n  let b: modelb.Item = { tag: \"two\" };\n  console.log(modela.tag(a));\n  console.log(modelb.tag(b));\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-same-name-isolation: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-11:2
  import * as modela from "./modela" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  import * as modelb from "./modelb" @<PROJECT>/main.deal:2:1-3:6
    [boundary: import]
  import * as console from "std/console" @<PROJECT>/main.deal:3:1-4:6
    [boundary: host-in]
    [boundary: import]
  export @<PROJECT>/main.deal:4:1-6:6
    [boundary: export]
    function main: null @<PROJECT>/main.deal:4:8-6:6
      body
        return @<PROJECT>/main.deal:4:32-4:45
          literal null : null @<PROJECT>/main.deal:4:39-4:42
  export @<PROJECT>/main.deal:6:1-11:2
    [boundary: export]
    function run: null @<PROJECT>/main.deal:6:8-11:2
      body
        let a: @irpin10/Item @<PROJECT>/main.deal:7:3-8:5
          [boundary: var-annotation]
          object : @irpin10/Item @<PROJECT>/main.deal:7:24-7:37
            [boundary: class-construct]
            literal "one" : string @<PROJECT>/main.deal:7:31-7:35
        let b: @irpin10/Item @<PROJECT>/main.deal:8:3-9:9
          [boundary: var-annotation]
          object : @irpin10/Item @<PROJECT>/main.deal:8:24-8:37
            [boundary: class-construct]
            literal "two" : string @<PROJECT>/main.deal:8:31-8:35
        expr-stmt @<PROJECT>/main.deal:9:3-9:28
          call : null @<PROJECT>/main.deal:9:3-9:28
            [boundary: stdlib-boundary]
            member .log : (string)->null @<PROJECT>/main.deal:9:3-9:13
              [boundary: table-read]
              ident console : table @<PROJECT>/main.deal:9:3-9:9
                [boundary: import]
            call : string @<PROJECT>/main.deal:9:15-9:27
              member .tag : (@irpin10/Item)->string @<PROJECT>/main.deal:9:15-9:24
                [boundary: table-read]
                ident modela : table @<PROJECT>/main.deal:9:15-9:20
                  [boundary: import]
              ident a : @irpin10/Item @<PROJECT>/main.deal:9:26-9:26
        expr-stmt @<PROJECT>/main.deal:10:3-10:28
          call : null @<PROJECT>/main.deal:10:3-10:28
            [boundary: stdlib-boundary]
            member .log : (string)->null @<PROJECT>/main.deal:10:3-10:13
              [boundary: table-read]
              ident console : table @<PROJECT>/main.deal:10:3-10:9
                [boundary: import]
            call : string @<PROJECT>/main.deal:10:15-10:27
              member .tag : (@irpin10/Item)->string @<PROJECT>/main.deal:10:15-10:24
                [boundary: table-read]
                ident modelb : table @<PROJECT>/main.deal:10:15-10:20
                  [boundary: import]
              ident b : @irpin10/Item @<PROJECT>/main.deal:10:26-10:26

=== IR: modela.ir.txt ===
module @<PROJECT>/modela.deal:1:1-4:62
  export @<PROJECT>/modela.deal:1:1-4:6
    [boundary: export]
    class Item @<PROJECT>/modela.deal:1:8-3:1
      field tag: string @<PROJECT>/modela.deal:2:3-3:1
        [boundary: class-default]
        literal "" : string @<PROJECT>/modela.deal:2:17-2:18
  export @<PROJECT>/modela.deal:4:1-4:62
    [boundary: export]
    function tag: string @<PROJECT>/modela.deal:4:8-4:62
      param i: Item @<PROJECT>/modela.deal:4:21-4:28
        [boundary: param-entry]
      body
        return @<PROJECT>/modela.deal:4:40-4:61
          [boundary: return]
          binary + : string @<PROJECT>/modela.deal:4:47-4:58
            literal "a:" : string @<PROJECT>/modela.deal:4:47-4:50
            member .tag : string @<PROJECT>/modela.deal:4:54-4:58
              ident i : @irpin10/Item @<PROJECT>/modela.deal:4:54-4:54

=== IR: modelb.ir.txt ===
module @<PROJECT>/modelb.deal:1:1-4:62
  export @<PROJECT>/modelb.deal:1:1-4:6
    [boundary: export]
    class Item @<PROJECT>/modelb.deal:1:8-3:1
      field tag: string @<PROJECT>/modelb.deal:2:3-3:1
        [boundary: class-default]
        literal "" : string @<PROJECT>/modelb.deal:2:17-2:18
  export @<PROJECT>/modelb.deal:4:1-4:62
    [boundary: export]
    function tag: string @<PROJECT>/modelb.deal:4:8-4:62
      param i: Item @<PROJECT>/modelb.deal:4:21-4:28
        [boundary: param-entry]
      body
        return @<PROJECT>/modelb.deal:4:40-4:61
          [boundary: return]
          binary + : string @<PROJECT>/modelb.deal:4:47-4:58
            literal "b:" : string @<PROJECT>/modelb.deal:4:47-4:50
            member .tag : string @<PROJECT>/modelb.deal:4:54-4:58
              ident i : @irpin10/Item @<PROJECT>/modelb.deal:4:54-4:54
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-same-name-isolation: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

        { // jvm-xmod-classes-slice :: jvm-xmod-class-param-return-local-fn
            String proj = "irpin11";
            writeFile(proj + "/lib.deal", "export class Point {\n  x: int = 0;\n  y: int = 0;\n}\nexport function sum(p: Point): int { return p.x + p.y; }");
            writeFile(proj + "/main.deal", "import * as lib from \"./lib\"\nexport function main(): null { return null; }\n\nfunction shift(p: lib.Point): lib.Point {\n  p.x = p.x + 1;\n  return p;\n}\nexport function run(): int {\n  let p: lib.Point = { x: 3, y: 4 };\n  let q: lib.Point = shift(p);\n  return lib.sum(q) + q.y;\n}");
            Map<String, String> irPinExternals = null;
            Path irPinRoot = tmpDir.get().resolve(proj).toAbsolutePath().normalize();
            Path irPinEntry = irPinRoot.resolve("main.deal");
            Path irPinOut = irPinRoot.resolve("out");
            CompilationOrchestrator irPinOrch = new CompilationOrchestrator(
            irPinEntry,
            irPinOut,
            false,
            true,
            false,
            false,
            Backend.JVM,
            irPinExternals,
            List.of(irPinRoot),
            null,
            null,
            harnessInvocation());
            boolean irPinOk = irPinOrch.compile();
            check(irPinOk, "jvm-xmod-classes-slice :: jvm-xmod-class-param-return-local-fn: orchestrator --dump-ir compile succeeds: "
                + irPinOrch.diagnostics());
            StringBuilder irPinActual = new StringBuilder();
            List<Path> irPinDumps = new ArrayList<>();
            try (var stream = Files.list(irPinOut)) {
                stream.filter(p -> p.toString().endsWith(".ir.txt"))
                      .sorted()
                      .forEach(irPinDumps::add);
            }
            for (Path irPinDump : irPinDumps) {
                irPinActual.append("=== IR: ").append(irPinDump.getFileName())
                    .append(" ===\n");
                irPinActual.append(Files.readString(irPinDump));
                irPinActual.append("\n");
            }
            String irPinNormalized = irPinActual.toString()
                .replace(irPinRoot.toString(), "<PROJECT>");
            String irPinExpected = """
=== IR: lib.ir.txt ===
module @<PROJECT>/lib.deal:1:1-5:57
  export @<PROJECT>/lib.deal:1:1-5:6
    [boundary: export]
    class Point @<PROJECT>/lib.deal:1:8-4:1
      field x: int @<PROJECT>/lib.deal:2:3-3:3
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:2:12-2:12
      field y: int @<PROJECT>/lib.deal:3:3-4:1
        [boundary: class-default]
        literal 0 : int @<PROJECT>/lib.deal:3:12-3:12
  export @<PROJECT>/lib.deal:5:1-5:57
    [boundary: export]
    function sum: int @<PROJECT>/lib.deal:5:8-5:57
      param p: Point @<PROJECT>/lib.deal:5:21-5:29
        [boundary: param-entry]
      body
        return @<PROJECT>/lib.deal:5:38-5:56
          [boundary: return]
          binary + : int @<PROJECT>/lib.deal:5:45-5:53
            member .x : int @<PROJECT>/lib.deal:5:45-5:47
              ident p : @irpin11/Point @<PROJECT>/lib.deal:5:45-5:45
            member .y : int @<PROJECT>/lib.deal:5:51-5:53
              ident p : @irpin11/Point @<PROJECT>/lib.deal:5:51-5:51

=== IR: main.ir.txt ===
module @<PROJECT>/main.deal:1:1-12:2
  import * as lib from "./lib" @<PROJECT>/main.deal:1:1-2:6
    [boundary: import]
  export @<PROJECT>/main.deal:2:1-4:8
    [boundary: export]
    function main: null @<PROJECT>/main.deal:2:8-4:8
      body
        return @<PROJECT>/main.deal:2:32-2:45
          literal null : null @<PROJECT>/main.deal:2:39-2:42
  function shift: @lib/Point @<PROJECT>/main.deal:4:1-8:6
    param p: @lib/Point @<PROJECT>/main.deal:4:16-4:28
      [boundary: param-entry]
    body
      expr-stmt @<PROJECT>/main.deal:5:3-5:15
        assign = : int @<PROJECT>/main.deal:5:3-5:15
          [boundary: field-write]
          member .x : int @<PROJECT>/main.deal:5:3-5:5
            ident p : @irpin11/Point @<PROJECT>/main.deal:5:3-5:3
          binary + : int @<PROJECT>/main.deal:5:9-5:15
            member .x : int @<PROJECT>/main.deal:5:9-5:11
              ident p : @irpin11/Point @<PROJECT>/main.deal:5:9-5:9
            literal 1 : int @<PROJECT>/main.deal:5:15-5:15
      return @<PROJECT>/main.deal:6:3-7:1
        [boundary: return]
        ident p : @irpin11/Point @<PROJECT>/main.deal:6:10-6:10
  export @<PROJECT>/main.deal:8:1-12:2
    [boundary: export]
    function run: int @<PROJECT>/main.deal:8:8-12:2
      body
        let p: @irpin11/Point @<PROJECT>/main.deal:9:3-10:5
          [boundary: var-annotation]
          object : @irpin11/Point @<PROJECT>/main.deal:9:22-9:35
            [boundary: class-construct]
            literal 3 : int @<PROJECT>/main.deal:9:27-9:27
            literal 4 : int @<PROJECT>/main.deal:9:33-9:33
        let q: @irpin11/Point @<PROJECT>/main.deal:10:3-11:8
          [boundary: var-annotation]
          call : @irpin11/Point @<PROJECT>/main.deal:10:22-10:29
            ident shift : (@irpin11/Point)->@irpin11/Point @<PROJECT>/main.deal:10:22-10:26
            ident p : @irpin11/Point @<PROJECT>/main.deal:10:28-10:28
        return @<PROJECT>/main.deal:11:3-12:1
          [boundary: return]
          binary + : int @<PROJECT>/main.deal:11:10-11:25
            call : int @<PROJECT>/main.deal:11:10-11:19
              member .sum : (@irpin11/Point)->int @<PROJECT>/main.deal:11:10-11:16
                [boundary: table-read]
                ident lib : table @<PROJECT>/main.deal:11:10-11:12
                  [boundary: import]
              ident q : @irpin11/Point @<PROJECT>/main.deal:11:18-11:18
            member .y : int @<PROJECT>/main.deal:11:23-11:25
              ident q : @irpin11/Point @<PROJECT>/main.deal:11:23-11:23
""";
            if (!(irPinExpected + "\n").equals(irPinNormalized)) {
                check(false, "jvm-xmod-classes-slice :: jvm-xmod-class-param-return-local-fn: exact IR dump mismatch");
                System.err.println("---- expected IR dump ----");
                System.err.println(irPinExpected);
                System.err.println("---- actual IR dump ----");
                System.err.println(irPinNormalized);
            }
        }

    }
}
