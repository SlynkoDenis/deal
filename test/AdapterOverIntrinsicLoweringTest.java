package deal.semantic;

import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.StructuredBodyTable;
import deal.types.Type;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0680: the adapter-over-intrinsic asynchronous lowering sites. The
 * checker admits no async use of a conversion intrinsic (E3013 — the design
 * source {@code conversion-intrinsic-function-values} J3: the conversion
 * intrinsics are synchronous values), so these drives lower the two async
 * sites directly and pin the closed shape each records:
 *
 * <ol>
 *   <li>The {@code await} over an adapter whose recorded source is the seeded
 *       intrinsic identity: the outer adapter-over-async task with the xN
 *       target-signature {@code FUNCTION_PARAMETER} cells and its
 *       {@code ADAPTER_INNER} alias token, and the nested source
 *       {@code ASYNC_START} carrying the {@code IntrinsicFunction} callee,
 *       the {@code ELIDED_BY_ADAPTER} mode, the leading-M operand, and zero
 *       return boundaries (the AWAIT owns the single
 *       {@code ASYNC_COMPLETION} cell).</li>
 *   <li>The {@code await} over the intrinsic's own registration: the closed
 *       {@code DEAL_BODY} start with the declared-signature
 *       {@code FUNCTION_PARAMETER} cell and zero return boundaries.</li>
 * </ol>
 *
 * <p>Both arms are the deterministic closed treatment of a doctored site
 * (never a fail-closed producer defect); their execution is verified end to
 * end by {@code deal.test.AdapterOverIntrinsicTest}'s adapter-over-async
 * drive, which runs the doctored shape through the oracle and both
 * production artifacts.</p>
 */
public class AdapterOverIntrinsicLoweringTest {

    private static int passed = 0;
    private static int failed = 0;

    private static final ModuleId MODULE = new ModuleId("test");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual), message + " (expected "
            + expected + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    /** The corpus/design drive: the adapted declaration over the intrinsic, awaited. */
    private static final String ADAPTED_AWAIT_SOURCE = """
        export async function test(): int {
          let f: (x: number, y: number) => int = int;
          let r: int = await f(9.0, 1.0);
          return r;
        }
        """;

    /** The intrinsic's own registration awaited (the bare async form). */
    private static final String DIRECT_AWAIT_SOURCE = """
        export async function test(): int {
          let r: int = await int(3.0);
          return r;
        }
        """;

    private record Lowered(LoweredModuleUnit unit, StructuredBodyTable table) {
    }

    /**
     * Lowers one source through the module walk even though the checker
     * rejects the async intrinsic use (E3013): the error recovery keeps the
     * checker's type facts, and the walk's async sites are the production
     * arms this drive pins.
     */
    private static Lowered lower(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver resolver = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symbols = resolver.resolve(parse.program());
        check(resolver.diagnostics().isEmpty(), what + ": resolves cleanly: "
            + resolver.diagnostics());
        if (!resolver.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(SOURCE_ID, symbols, resolver,
            parse.program());
        check(checks.hasErrors(), what + ": the checker rejects the async intrinsic "
            + "use (E3013): " + checks.diagnostics());
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
        ExternalModuleInterface ownInterface = new ExternalModuleInterface(MODULE,
            ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
            InitializationMode.ONCE_AFTER_DEPENDENCIES);
        SemanticLowerer.ModuleLowerer lowerer = new SemanticLowerer.ModuleLowerer(MODULE,
            SOURCE_ID, checks, allocator, true, true, true, false, false, false,
            parse.program().span(), true, true, ownInterface, Map.of());
        lowerer.setModuleImports(List.of());
        lowerer.setRegistrationSeeds(ClassRegistrationSeeds.builtinErrorOnly());
        lowerer.setDeclaredConversionIntrinsics(
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT));
        lowerer.setE7Facts(List.of(), Map.of(), Map.of(), Set.of());
        try {
            lowerer.lowerProjectModule(parse.program().statements());
            LoweredModuleUnit unit = lowerer.buildUnit(Map.of(), List.of(),
                new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                    Map.of(MODULE, ownInterface)).interfaceIndexDigest(),
                REGISTRY_HASH, ContainerClaimingSeam.E9_GATE_ACTIVATION);
            return new Lowered(unit, lowerer.bodyTable());
        } catch (RuntimeException defect) {
            fail(what + ": the walk produces the unit: " + defect);
            return null;
        }
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath,
                    String importingModule, Set<String> modulesInProgress)
                    throws ModuleResolver.ModuleNotFoundException {
                Map<String, Map<String, Type>> exports =
                    deal.module.StdlibModuleResolver.stdlibExports(
                        Path.of("std").toAbsolutePath().toString());
                Map<String, Type> moduleExports = exports.get(modulePath);
                if (moduleExports == null) {
                    throw new ModuleResolver.ModuleNotFoundException(
                        "Module not found: " + modulePath);
                }
                return moduleExports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className,
                    String modulePath, String importingModule) {
                return null;
            }
        };
    }

    private static List<SemanticOp> starts(LoweredModuleUnit unit) {
        List<SemanticOp> found = new java.util.ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.ASYNC_START) {
                found.add(op);
            }
        }
        return found;
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    private static long seedIdentity(LoweredModuleUnit unit, IntrinsicKind kind) {
        for (Map.Entry<deal.semantic.ir.FunctionAllocationIdentity,
                FunctionExecutionBinding> entry : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic && intrinsic.kind() == kind) {
                return entry.getKey().id();
            }
        }
        return -1;
    }

    // =========================================================================
    // 1. The awaited adapted declaration over the intrinsic
    // =========================================================================

    private static void testAdapterOverAsyncSite() {
        System.out.println("-- the adapter-over-async site over the intrinsic: the "
            + "outer adapter task and the nested intrinsic source start --");
        Lowered lowered = lower(ADAPTED_AWAIT_SOURCE, "adapter-over-async site");
        if (lowered == null) {
            return;
        }
        LoweredModuleUnit unit = lowered.unit();
        long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
        check(seed > 0, "the unit carries the int seed identity");
        if (seed < 0) {
            return;
        }
        List<SemanticOp> starts = starts(unit);
        checkEq(2, starts.size(), "the adapter-over-async site carries the outer and "
            + "the nested source start");
        if (starts.size() != 2) {
            return;
        }
        SemanticOp outer = null;
        SemanticOp nested = null;
        for (SemanticOp candidate : starts) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) candidate.payload();
            if (payload.callee() instanceof KindPayload.CallCallee.Static callee
                    && callee.binding() instanceof FunctionExecutionBinding.AdapterBinding) {
                outer = candidate;
            } else {
                nested = candidate;
            }
        }
        check(outer != null && nested != null,
            "the two starts are the outer adapter task and the nested source start");
        if (outer == null || nested == null) {
            return;
        }
        KindPayload.AsyncStartPayload outerPayload =
            (KindPayload.AsyncStartPayload) outer.payload();
        FunctionExecutionBinding.AdapterBinding adapter =
            (FunctionExecutionBinding.AdapterBinding)
                ((KindPayload.CallCallee.Static) outerPayload.callee()).binding();
        checkEq(CaptureMode.VALUE, adapter.captureMode(),
            "the outer adapter records the VALUE capture mode");
        check(adapter.sourceRef() instanceof deal.semantic.ir.AdaptSourceRef.Value value
                && value.value().id() == seed,
            "the adapter's recorded source is the seeded intrinsic identity");
        checkEq(AsyncStartSource.DEAL_BODY, outerPayload.source(),
            "the outer adapter task is the closed DEAL_BODY task");
        checkEq(ParameterBoundaryMode.RUN, outerPayload.parameterBoundaryMode(),
            "the outer task runs the xN target-signature parameter cells");
        checkEq(2, outerPayload.parameterBoundaryOpIds().size(),
            "the outer task records the two target-signature cells");
        for (OpId boundaryId : outerPayload.parameterBoundaryOpIds()) {
            SemanticOp boundary = opOf(unit, boundaryId);
            check(boundary != null && boundary.payload()
                    instanceof KindPayload.BoundaryPayload payload
                    && payload.kind() == BoundaryKind.FUNCTION_PARAMETER,
                "the outer parameter cell is the FUNCTION_PARAMETER family");
        }
        check(outerPayload.returnBoundaryOpId() == null,
            "the outer adapter task runs zero return boundaries (delegation)");
        check(outer.result() instanceof AsyncTokenId.Alias alias
                && alias.linkKind() == AsyncLinkKind.ADAPTER_INNER,
            "the outer token is the ADAPTER_INNER alias");
        KindPayload.AsyncStartPayload nestedPayload =
            (KindPayload.AsyncStartPayload) nested.payload();
        check(nestedPayload.callee() instanceof KindPayload.CallCallee.Static callee
                && callee.binding() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic
                && intrinsic.kind() == IntrinsicKind.INT_CONVERT
                && intrinsic.descriptor().equals(
                    IntrinsicKind.INT_CONVERT.declaredSignature()),
            "the nested source start resolves the seeded IntrinsicFunction callee");
        checkEq(AsyncStartSource.DEAL_BODY, nestedPayload.source(),
            "the nested source start is the closed DEAL_BODY task (the synchronous "
                + "conversion completes immediately)");
        checkEq(ParameterBoundaryMode.ELIDED_BY_ADAPTER,
            nestedPayload.parameterBoundaryMode(),
            "the nested source start elides its parameter boundaries");
        check(nestedPayload.parameterBoundaryOpIds().isEmpty(),
            "the nested source start records zero parameter cells");
        check(nestedPayload.returnBoundaryOpId() == null,
            "the nested source start records zero return boundaries");
        checkEq(1, nested.operands().size(),
            "the nested source start carries the single leading-M operand");
        checkEq(outer.opId(), nested.origin().parentOpId(),
            "the nested source start parents to the outer adapter start");
        check(nested.result() instanceof AsyncTokenId.Canonical token
                && token.owner() == AsyncTokenOwner.DEAL_BODY_TASK,
            "the nested token is a canonical DEAL_BODY_TASK token");
        int awaits = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.AWAIT) {
                awaits++;
                KindPayload.AwaitPayload payload =
                    (KindPayload.AwaitPayload) op.payload();
                checkEq(outer.result(), payload.token(),
                    "the single AWAIT drains the outer adapter token");
            }
        }
        checkEq(1, awaits, "the site carries exactly one AWAIT");
        check(lowered.table() != null, "the walk produces the block table");

        // The emitted artifacts run the conversion inside the nested task.
        String lua = LuaSemanticEmitter.emitModule(unit, lowered.table());
        check(lua.contains("pcall(__intConv,"),
            "the LuaJIT nested source start runs the conversion inside its task");
        String jvm = JvmSemanticEmitter.emitModule(unit, lowered.table()).source();
        check(jvm.contains("JvmRuntime.intConv("),
            "the JVM nested source start runs the conversion inside its task");
    }

    // =========================================================================
    // 2. The intrinsic's own registration awaited
    // =========================================================================

    private static void testDirectAwaitSite() {
        System.out.println("-- the bare async form: the intrinsic's own registration "
            + "awaited records the closed DEAL_BODY start --");
        Lowered lowered = lower(DIRECT_AWAIT_SOURCE, "direct async intrinsic site");
        if (lowered == null) {
            return;
        }
        LoweredModuleUnit unit = lowered.unit();
        List<SemanticOp> starts = starts(unit);
        checkEq(1, starts.size(), "the direct await produces the single intrinsic start");
        if (starts.size() != 1) {
            return;
        }
        SemanticOp start = starts.get(0);
        KindPayload.AsyncStartPayload payload =
            (KindPayload.AsyncStartPayload) start.payload();
        check(payload.callee() instanceof KindPayload.CallCallee.Static callee
                && callee.binding() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic
                && intrinsic.kind() == IntrinsicKind.INT_CONVERT,
            "the start resolves the seeded IntrinsicFunction callee");
        checkEq(AsyncStartSource.DEAL_BODY, payload.source(),
            "the start is the closed DEAL_BODY task");
        checkEq(ParameterBoundaryMode.RUN, payload.parameterBoundaryMode(),
            "the start runs its declared-signature parameter cells");
        checkEq(1, payload.parameterBoundaryOpIds().size(),
            "the start records the intrinsic's single declared parameter cell");
        SemanticOp boundary = opOf(unit, payload.parameterBoundaryOpIds().get(0));
        check(boundary != null
                && boundary.payload() instanceof KindPayload.BoundaryPayload cell
                && cell.kind() == BoundaryKind.FUNCTION_PARAMETER
                && cell.descriptor().equals(IntrinsicKind.INT_CONVERT
                    .declaredSignature().paramTypes().get(0))
                && boundary.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "the parameter cell is FUNCTION_PARAMETER on the intrinsic's declared "
                + "parameter descriptor");
        check(payload.returnBoundaryOpId() == null,
            "the start records zero return boundaries (the AWAIT owns the "
                + "completion cell)");
        RuntimeDescriptor completion = payload.completionDescriptor();
        checkEq(IntrinsicKind.INT_CONVERT.declaredSignature().returnType(), completion,
            "the completion descriptor is the intrinsic's declared return descriptor");
        int awaits = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.AWAIT) {
                awaits++;
            }
        }
        checkEq(1, awaits, "the site carries exactly one AWAIT");
        String lua = LuaSemanticEmitter.emitModule(unit, lowered.table());
        check(lua.contains("pcall(__intConv,"),
            "the LuaJIT start runs the conversion inside its task");
        String jvm = JvmSemanticEmitter.emitModule(unit, lowered.table()).source();
        check(jvm.contains("JvmRuntime.intConv("),
            "the JVM start runs the conversion inside its task");
    }

    public static void main(String[] args) {
        System.out.println("=== Adapter-over-Intrinsic Async Lowering Tests "
            + "(ISSUE-0680) ===\n");
        testAdapterOverAsyncSite();
        testDirectAwaitSite();
        System.out.println("\nAdapter-over-intrinsic async lowering: " + passed
            + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
