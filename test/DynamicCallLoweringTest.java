package deal.semantic;

import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.ModuleResolver.ModuleNotFoundException;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0657 — the dynamic call shape production
 * ({@code dynamic-call-shape-production-and-emission} Y1/Y4 and the
 * dynamic call/async-start shape contracts;
 * {@code semantic-ir-construct-coverage-cutover} K5 and K12's form (b)).
 *
 * <ol>
 *   <li>a checker-valid call whose callee value has no statically
 *       resolvable execution binding lowers one {@code CALL(INDIRECT)}
 *       with {@code CallCallee.Dynamic(calleeValue)}, one
 *       declared-signature {@code FUNCTION_PARAMETER} boundary child per
 *       argument in one-based order, and the three recorded
 *       {@code DynamicReturnBoundary} cells: a {@code FUNCTION_RETURN} on
 *       the declared return descriptor parented to the call-owned
 *       {@code RETURN} that names the {@code CALL} (the K12 form (b)
 *       cell, never parented to the CALL op), the
 *       {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} cell, and the
 *       {@code EXTERNAL_RETURN} cell — the single return
 *       {@code returnBoundaryOpId} stays unrecorded;</li>
 *   <li>the same shape in {@code await} position: one
 *       {@code ASYNC_START} with {@code CallCallee.Dynamic}, the recorded
 *       source {@code DEAL_BODY}, {@code RUN} parameter mode, the
 *       declared signature's {@code FUNCTION_PARAMETER} children, and the
 *       single recorded task cell — a {@code FUNCTION_RETURN} on the
 *       declared completion descriptor parented to the call-owned
 *       {@code RETURN} that names the {@code ASYNC_START} — consumed by
 *       exactly one {@code AWAIT} running the single
 *       {@code ASYNC_COMPLETION} boundary;</li>
 *   <li>the produced units pass the closed gate and the composed per-unit
 *       chain for every callee whose value-side execution class is
 *       statically produced at this boundary (a closure carrier): the
 *       canonical {@code CallCallee.Dynamic} and its three cells pass
 *       R-BOUNDARY-TRIPLE and its parent rule, the control-flow validator
 *       admits the call-owned return record outside the block tree, the
 *       bindings production validator passes, and repeated lowerings
 *       produce byte-identical dumps;</li>
 *   <li>a callee value whose materialization registration is the
 *       function-typed-value child's (K11's {@code DynamicFunctionValue})
 *       produces the same shape and stops the closed gate exactly at that
 *       pending clause (R-FUNCTION-BINDING), never at a dynamic-cell or
 *       parent-rule clause — the identifier-callee arm is reached through
 *       the package-internal project walk, because the project entry
 *       discards a unit that a later rule rejects;</li>
 *   <li>the static call and async arms are unchanged: a statically
 *       resolvable callee keeps {@code CallCallee.Static} and its single
 *       recorded return boundary, and no dynamic shape appears;</li>
 *   <li>the negative seeds: a hand-built unit whose dynamic cells carry a
 *       wrong kind, a wrong descriptor, a non-{@code INDIRECT} mode, a
 *       missing cell, or a parent outside the call-owned {@code RETURN}
 *       fails the closed gate.</li>
 * </ol>
 */
public class DynamicCallLoweringTest {

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

    private static final ModuleId MODULE = new ModuleId("app");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;

    // =========================================================================
    // Fixtures
    // =========================================================================

    /** A closure carrier callee value: the gate-clean dynamic CALL fixture. */
    private static final String IIFE_SYNC_SOURCE = """
        export function main(): null {
          let r: int = (function(x: int): int { return x; })(1)
          return null
        }
        """;

    /** A closure carrier callee value: the gate-clean dynamic ASYNC_START fixture. */
    private static final String IIFE_ASYNC_SOURCE = """
        async function run(): int {
          return await (async function(): int { return 1; })()
        }

        export function main(): null {
          return null
        }
        """;

    /** The identifier-callee fixture: function-typed parameter loads. */
    private static final String PARAMETER_SOURCE = """
        function apply(f: (x: int) => int, x: int): int {
          return f(x)
        }

        async function applyAsync(f: async () => int): int {
          return await f()
        }

        function double(x: int): int {
          return x * 2
        }

        export function main(): null {
          let r: int = apply(double, 21)
          return null
        }
        """;

    /** The static control: a statically resolvable callee keeps the static arm. */
    private static final String STATIC_SOURCE = """
        function double(x: int): int {
          return x * 2
        }

        export function main(): null {
          let g: (x: int) => int = double
          let r: int = g(21)
          return null
        }
        """;

    // =========================================================================
    // The frontend + project harness
    // =========================================================================

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record Fixture(CheckedProjectInput input, ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           CheckedModuleInput module) {
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath, String importingModule,
                    Set<String> modulesInProgress) throws ModuleNotFoundException {
                Map<String, Map<String, Type>> exports =
                    deal.module.StdlibModuleResolver.stdlibExports(
                        Path.of("std").toAbsolutePath().toString());
                Map<String, Type> moduleExports = exports.get(modulePath);
                if (moduleExports == null) {
                    throw new ModuleNotFoundException("Module not found: " + modulePath);
                }
                return moduleExports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                    String importingModule) {
                return null;
            }
        };
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": checks cleanly: "
            + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    private static List<ExportInterface> exportsOf(ProgramNode program) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ExportDeclaration export
                    && export.declaration() instanceof FunctionDeclaration function) {
                exports.add(new ExportInterface(function.name(), "function"));
            }
        }
        return exports;
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static Fixture fixture(String source, String what) {
        CheckedSlice slice = checkSlice(source, what);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput module = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of("test.deal"), slice.program(), slice.checks(), List.<ResolvedImport>of(),
            exportsOf(slice.program()), CheckedModuleKind.IMPLEMENTATION);
        List<ModuleFact> facts = List.of(new ModuleFact(SOURCE_ID, MODULE, false, false,
            slice.program(), Map.of(), slice.symbols(), slice.checks(), List.of()));
        CompilerInvocation invocation = invocation();
        CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation, MODULE, facts);
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            what + ": the checked project builds: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifestResult = LoweringSupport.computeManifests(
            invocation, built.input(), built.index());
        check(manifestResult != null && manifestResult.diagnostics().isEmpty(),
            what + ": the requirement manifests compute: "
                + (manifestResult == null ? "null" : manifestResult.diagnostics()));
        if (manifestResult == null || !manifestResult.diagnostics().isEmpty()) {
            return null;
        }
        return new Fixture(built.input(), built.index(), manifestResult.manifests(), module);
    }

    /** The one project lowering entry over the fixture. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(invocation(), fixture.input(), fixture.index(),
            fixture.manifests(), new HostDeclarationSurface(Map.of()), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(fixture.module().ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    /** The direct per-module project walk (the produced, pre-gate unit). */
    private record RawLowering(LoweredModuleUnit unit, StructuredBodyTable table,
                               SemanticLowerer.ModuleLowerer lowerer) {
    }

    private static RawLowering rawLower(Fixture fixture, String what) {
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
        ExternalModuleInterface ownInterface = fixture.index().modules().get(MODULE);
        SemanticLowerer.ModuleLowerer lowerer = new SemanticLowerer.ModuleLowerer(
            MODULE, SOURCE_ID, fixture.module().checks(), allocator,
            true, true, true, false, false, false, fixture.module().ast().span(),
            true, true, ownInterface, Map.of());
        lowerer.setModuleImports(fixture.module().imports());
        lowerer.setRegistrationSeeds(ClassRegistrationSeeds.builtinErrorOnly());
        lowerer.setDeclaredConversionIntrinsics(
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT));
        lowerer.setE7Facts(fixture.module().exports(), Map.of(), Map.of(), Set.of());
        try {
            lowerer.lowerProjectModule(fixture.module().ast().statements());
        } catch (RuntimeException defect) {
            fail(what + ": the walk produces the unit: " + defect);
            return null;
        }
        LoweredModuleUnit unit = lowerer.buildUnit(
            fixture.manifests().get(0).constructCoverage(),
            fixture.module().imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            fixture.index().interfaceIndexDigest(), REGISTRY_HASH,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        return new RawLowering(unit, lowerer.bodyTable(), lowerer);
    }

    // =========================================================================
    // Op lookup helpers
    // =========================================================================

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp producerOf(LoweredModuleUnit unit, ValueId valueId) {
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId value && value.equals(valueId)) {
                return op;
            }
        }
        return null;
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    private static SemanticOp dynamicCall(LoweredModuleUnit unit) {
        for (SemanticOp op : ofKind(unit, SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp dynamicAsyncStart(LoweredModuleUnit unit) {
        for (SemanticOp op : ofKind(unit, SemanticOpKind.ASYNC_START)) {
            if (op.payload() instanceof KindPayload.AsyncStartPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    private static KindPayload.BoundaryPayload boundaryOf(SemanticOp op) {
        return (KindPayload.BoundaryPayload) op.payload();
    }

    // =========================================================================
    // 1. The dynamic CALL shape (gate-clean closure carrier)
    // =========================================================================

    private static void testDynamicCallShape() {
        System.out.println("-- The dynamic CALL shape: CallCallee.Dynamic and the three "
            + "recorded return cells --");
        Fixture fixture = fixture(IIFE_SYNC_SOURCE, "iife sync");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "iife sync");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        check(call != null, "the call lowers the dynamic callee shape");
        if (call == null) {
            return;
        }
        KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
        check(payload.mode() == CallMode.INDIRECT,
            "a Dynamic callee is lowered under Mode INDIRECT, got " + payload.mode());
        check(payload.callee() instanceof KindPayload.CallCallee.Dynamic,
            "the callee records the evaluated callee value");
        check(payload.returnBoundaryOpId() == null,
            "a Dynamic callee records no single returnBoundaryOpId");
        check(payload.bodyBlock() == null && payload.externalEntryRef() == null,
            "a Dynamic CALL records neither a body block nor an external-entry ref");
        check(payload.signature().paramTypes().size() == 1
                && payload.signature().returnType().equals(INT),
            "the recorded signature is the callee's checked descriptor (int)->int, got "
                + payload.signature());

        check(payload.parameterBoundaryOpIds().size() == 1,
            "one FUNCTION_PARAMETER child per argument in one-based order, got "
                + payload.parameterBoundaryOpIds().size());
        if (payload.parameterBoundaryOpIds().size() == 1) {
            SemanticOp parameter = opOf(unit, payload.parameterBoundaryOpIds().get(0));
            check(parameter != null && boundaryOf(parameter).kind()
                    == BoundaryKind.FUNCTION_PARAMETER,
                "the parameter child is a FUNCTION_PARAMETER boundary");
            check(parameter != null && call.opId().equals(parameter.origin().parentOpId()),
                "the parameter child is parented to the CALL");
            check(parameter != null && boundaryOf(parameter).descriptor()
                    .equals(payload.signature().paramTypes().get(0)),
                "the parameter child carries the declared parameter descriptor");
        }

        KindPayload.DynamicReturnBoundary recorded = payload.dynamicReturnBoundary();
        check(recorded != null, "the dynamic return-boundary set is recorded");
        if (recorded == null) {
            return;
        }
        check(!recorded.dealBodyBoundaryOpId().equals(recorded.hostBoundaryOpId())
                && !recorded.dealBodyBoundaryOpId().equals(recorded.externalBoundaryOpId())
                && !recorded.hostBoundaryOpId().equals(recorded.externalBoundaryOpId()),
            "the three recorded cells are mutually distinct");

        SemanticOp dealCell = opOf(unit, recorded.dealBodyBoundaryOpId());
        check(dealCell != null && boundaryOf(dealCell).kind() == BoundaryKind.FUNCTION_RETURN,
            "the DEAL-body cell is a FUNCTION_RETURN boundary");
        check(dealCell != null && boundaryOf(dealCell).descriptor()
                .equals(payload.signature().returnType()),
            "the DEAL-body cell checks the declared return descriptor");
        check(dealCell != null && dealCell.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "the DEAL-body cell carries the descriptor-kind policy, got "
                + (dealCell == null ? "null" : dealCell.failurePolicy()));
        SemanticOp dealReturn = dealCell == null ? null
            : opOf(unit, dealCell.origin().parentOpId());
        check(dealReturn != null && dealReturn.kind() == SemanticOpKind.RETURN,
            "the DEAL-body cell is parented to a RETURN op (never to the CALL op)");
        if (dealReturn != null
                && dealReturn.payload() instanceof KindPayload.ReturnPayload returned) {
            check(call.opId().equals(returned.enclosingInvocationOpId()),
                "the call-owned RETURN names the dynamic CALL as its "
                    + "enclosingInvocationOpId");
            check(returned.returnBoundaryOpId().equals(recorded.dealBodyBoundaryOpId()),
                "the call-owned RETURN records the DEAL-body cell as its return boundary");
            check(!unit.functions().containsKey(returned.function()),
                "the call-owned RETURN carries the record's reserved function identity "
                    + "(the callee body is runtime-resolved)");
        } else {
            fail("the DEAL-body cell's parent is a RETURN op");
        }
        check(dealReturn != null && raw.table().opBlocks().get(dealReturn.opId()) == null,
            "the call-owned RETURN record is a member of no block (the invocation op "
                + "executes the cell; the block walk never does)");

        SemanticOp hostCell = opOf(unit, recorded.hostBoundaryOpId());
        check(hostCell != null && boundaryOf(hostCell).kind() == BoundaryKind.HOST_TO_DEAL
                && hostCell.failurePolicy() == FailurePolicyId.HOST_SYNC_RETURN
                && boundaryOf(hostCell).descriptor().equals(payload.signature().returnType()),
            "the host cell is HOST_TO_DEAL + HOST_SYNC_RETURN on the declared return "
                + "descriptor");
        check(hostCell != null && call.opId().equals(hostCell.origin().parentOpId()),
            "the host cell is run by the call op");

        SemanticOp externalCell = opOf(unit, recorded.externalBoundaryOpId());
        check(externalCell != null
                && boundaryOf(externalCell).kind() == BoundaryKind.EXTERNAL_RETURN
                && externalCell.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR
                && boundaryOf(externalCell).descriptor()
                    .equals(payload.signature().returnType()),
            "the retained-ABI cell is EXTERNAL_RETURN under the descriptor-kind rule on "
                + "the declared return descriptor");
        check(externalCell != null && call.opId().equals(externalCell.origin().parentOpId()),
            "the external cell is run by the call op");

        SemanticOp calleeProducer = producerOf(unit,
            ((KindPayload.CallCallee.Dynamic) payload.callee()).callee());
        check(calleeProducer != null && calleeProducer.kind() == SemanticOpKind.CLOSURE_NEW,
            "the dynamic callee value is the evaluated callee expression's carrier, got "
                + (calleeProducer == null ? "null" : calleeProducer.kind()));

        assertClosedGatePass(unit, raw, "the dynamic CALL");
    }

    // =========================================================================
    // 2. The dynamic ASYNC_START shape (gate-clean closure carrier)
    // =========================================================================

    private static void testDynamicAsyncShape() {
        System.out.println("-- The dynamic ASYNC_START shape: the recorded DEAL_BODY task "
            + "cell --");
        Fixture fixture = fixture(IIFE_ASYNC_SOURCE, "iife async");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "iife async");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp start = dynamicAsyncStart(unit);
        check(start != null, "the await lowers the dynamic callee shape");
        if (start == null) {
            return;
        }
        KindPayload.AsyncStartPayload payload =
            (KindPayload.AsyncStartPayload) start.payload();
        check(payload.callee() instanceof KindPayload.CallCallee.Dynamic,
            "the ASYNC_START records the dynamic callee shape");
        check(payload.source() == AsyncStartSource.DEAL_BODY,
            "a Dynamic ASYNC_START records source DEAL_BODY, got " + payload.source());
        check(payload.parameterBoundaryMode() == ParameterBoundaryMode.RUN,
            "a Dynamic ASYNC_START runs its recorded parameter boundaries, got "
                + payload.parameterBoundaryMode());
        check(payload.hostOperationLabel() == null && payload.externalAsyncLink() == null,
            "a Dynamic ASYNC_START records no host operation label and no external link");
        check(payload.returnBoundaryOpId() != null,
            "the single DEAL_BODY task cell is recorded");
        if (payload.returnBoundaryOpId() == null) {
            return;
        }
        SemanticOp taskCell = opOf(unit, payload.returnBoundaryOpId());
        check(taskCell != null && boundaryOf(taskCell).kind() == BoundaryKind.FUNCTION_RETURN,
            "the task cell is a FUNCTION_RETURN boundary");
        check(taskCell != null && boundaryOf(taskCell).descriptor()
                .equals(payload.completionDescriptor()),
            "the task cell checks the declared completion descriptor");
        SemanticOp taskReturn = taskCell == null ? null
            : opOf(unit, taskCell.origin().parentOpId());
        check(taskReturn != null && taskReturn.kind() == SemanticOpKind.RETURN,
            "the task cell is parented to a RETURN op (never to the start op)");
        if (taskReturn != null
                && taskReturn.payload() instanceof KindPayload.ReturnPayload returned) {
            check(start.opId().equals(returned.enclosingInvocationOpId()),
                "the task-owned RETURN names the ASYNC_START as its "
                    + "enclosingInvocationOpId");
            check(returned.returnBoundaryOpId().equals(payload.returnBoundaryOpId()),
                "the task-owned RETURN records the task cell as its return boundary");
        } else {
            fail("the task cell's parent is a RETURN op");
        }
        check(taskReturn != null && raw.table().opBlocks().get(taskReturn.opId()) == null,
            "the task-owned RETURN record is a member of no block");

        List<SemanticOp> awaits = ofKind(unit, SemanticOpKind.AWAIT);
        check(awaits.size() == 1, "exactly one AWAIT consumes the start's token, got "
            + awaits.size());
        if (awaits.size() == 1
                && awaits.get(0).payload() instanceof KindPayload.AwaitPayload await) {
            check(await.token().equals(start.result()),
                "the AWAIT consumes the ASYNC_START's token");
            check(await.completionDescriptor().equals(payload.completionDescriptor()),
                "the AWAIT carries the declared completion descriptor");
            SemanticOp completion = opOf(unit, await.completionBoundaryOpId());
            check(completion != null && boundaryOf(completion).kind()
                    == BoundaryKind.ASYNC_COMPLETION
                    && completion.failurePolicy() == FailurePolicyId.ASYNC_COMPLETION,
                "the single ASYNC_COMPLETION boundary is parented to the AWAIT");
        }

        assertClosedGatePass(unit, raw, "the dynamic ASYNC_START");
    }

    /** The closed gate plus the composed per-unit chain over the produced unit. */
    private static void assertClosedGatePass(LoweredModuleUnit unit, RawLowering raw,
                                             String what) {
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        Optional<CompilerDiagnostic> gate = SemanticIrValidator.validate(unit, facts);
        check(gate.isEmpty(), what + ": the closed gate passes: "
            + gate.map(CompilerDiagnostic::message).orElse(""));
        Optional<CompilerDiagnostic> chains = AddressChainProtocol.validate(unit);
        check(chains.isEmpty(), what + ": the address-chain protocol passes: "
            + chains.map(CompilerDiagnostic::message).orElse(""));
        Optional<CompilerDiagnostic> controlFlow =
            ControlFlowValidator.validate(unit, raw.table());
        check(controlFlow.isEmpty(), what + ": the control-flow validator passes "
            + "(the call-owned return record is admitted outside the block tree): "
            + controlFlow.map(CompilerDiagnostic::message).orElse(""));
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), what + ": the bindings production validator passes: "
            + bindings.map(CompilerDiagnostic::message).orElse(""));
    }

    // =========================================================================
    // 3. The identifier-callee arm and its pending materialization clause
    // =========================================================================

    private static void testIdentifierCalleeArm() {
        System.out.println("-- lowerUserCallBinding / lowerAwaitExpression: the "
            + "function-typed parameter callee --");
        Fixture fixture = fixture(PARAMETER_SOURCE, "parameter callee");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "parameter callee");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        check(call != null, "f(x) inside apply(f, x) lowers CALL(INDIRECT) with a Dynamic "
            + "callee");
        SemanticOp start = dynamicAsyncStart(unit);
        check(start != null, "await f() inside applyAsync(f) lowers ASYNC_START with a "
            + "Dynamic callee");
        if (call != null) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            check(payload.mode() == CallMode.INDIRECT
                    && payload.returnBoundaryOpId() == null
                    && payload.dynamicReturnBoundary() != null
                    && payload.parameterBoundaryOpIds().size() == 1,
                "the parameter callee records the declared parameter cell and the three "
                    + "dynamic cells");
            SemanticOp calleeValue = producerOf(unit,
                ((KindPayload.CallCallee.Dynamic) payload.callee()).callee());
            check(calleeValue != null
                    && calleeValue.kind() == SemanticOpKind.BINDING_LOAD,
                "the callee value is the identifier's carrier read (BINDING_LOAD), got "
                    + (calleeValue == null ? "null" : calleeValue.kind()));
            check(calleeValue != null && calleeValue.resultType() instanceof RuntimeDescriptor.Func,
                "the carrier read publishes the callee's function descriptor");
            SemanticOp dealCell = opOf(unit,
                payload.dynamicReturnBoundary().dealBodyBoundaryOpId());
            SemanticOp dealReturn = dealCell == null ? null
                : opOf(unit, dealCell.origin().parentOpId());
            check(dealReturn != null && dealReturn.payload()
                    instanceof KindPayload.ReturnPayload returned
                    && call.opId().equals(returned.enclosingInvocationOpId()),
                "the DEAL-body cell is parented to the call-owned RETURN naming the CALL");
        }
        if (start != null) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) start.payload();
            check(payload.source() == AsyncStartSource.DEAL_BODY
                    && payload.completionDescriptor() != null,
                "the awaited parameter callee records source DEAL_BODY and the declared "
                    + "completion descriptor");
            SemanticOp taskCell = opOf(unit, payload.returnBoundaryOpId());
            SemanticOp taskReturn = taskCell == null ? null
                : opOf(unit, taskCell.origin().parentOpId());
            check(taskReturn != null && taskReturn.payload()
                    instanceof KindPayload.ReturnPayload returned
                    && start.opId().equals(returned.enclosingInvocationOpId()),
                "the task cell is parented to the RETURN naming the ASYNC_START");
        }
        Optional<CompilerDiagnostic> controlFlow =
            ControlFlowValidator.validate(unit, raw.table());
        check(controlFlow.isEmpty(), "the control-flow validator accepts the "
            + "parameter-callee unit: " + controlFlow.map(CompilerDiagnostic::message)
                .orElse(""));
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), "the bindings production validator accepts the "
            + "parameter-callee unit: " + bindings.map(CompilerDiagnostic::message)
                .orElse(""));

        // Exactly one function-typed result carries no registration at this
        // boundary: the callee's carrier read (the function-typed-value child's
        // DynamicFunctionValue producer rule registers it).
        List<Long> pending = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (!(op.result() instanceof ValueId value)
                    || !(op.resultType() instanceof RuntimeDescriptor.Func)) {
                continue;
            }
            boolean registered = false;
            for (FunctionAllocationIdentity identity : unit.functionBindings().keySet()) {
                if (identity.id() == value.id()) {
                    registered = true;
                    break;
                }
            }
            if (!registered) {
                pending.add(value.id());
            }
        }
        check(pending.size() == 2,
            "exactly the two carrier reads (the sync and the awaited callee) carry no "
                + "registration at this boundary (the function-typed-value child's "
                + "DynamicFunctionValue producer rule), got " + pending);

        // The project entry's verdict: the shape itself passes every dynamic
        // cell clause; the gate stops at the pending materialization rule.
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() == null, "the project entry returns no project while the "
            + "materialization registration is pending");
        check(result.diagnostics().size() == 1
                && result.diagnostics().stream().anyMatch(diagnostic ->
                    "E6005".equals(diagnostic.code())
                        && diagnostic.message().contains("R-FUNCTION-BINDING")),
            "the project entry's first failure is R-FUNCTION-BINDING (the pending "
                + "materialization registration), so R-BOUNDARY-TRIPLE and the DEAL-body "
                + "cell's parent rule passed: " + result.diagnostics());
    }

    // =========================================================================
    // 4. The static arms are unchanged
    // =========================================================================

    private static void testStaticArmsUnchanged() {
        System.out.println("-- The static arms: a statically resolvable callee keeps the "
            + "static resolution --");
        Fixture fixture = fixture(STATIC_SOURCE, "static callee");
        if (fixture == null) {
            return;
        }
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null, "the static fixture still lowers to one project: "
            + result.diagnostics());
        RawLowering raw = rawLower(fixture, "static callee");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        check(dynamicCall(unit) == null && dynamicAsyncStart(unit) == null,
            "no dynamic shape is produced for a statically resolvable callee");
        SemanticOp indirect = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.mode() == CallMode.INDIRECT) {
                indirect = op;
                break;
            }
        }
        check(indirect != null, "the statically resolved call keeps an INDIRECT CALL");
        if (indirect != null
                && indirect.payload() instanceof KindPayload.CallPayload payload) {
            check(payload.callee() instanceof KindPayload.CallCallee.Static,
                "the statically resolved call records CallCallee.Static");
            check(payload.returnBoundaryOpId() != null
                    && payload.dynamicReturnBoundary() == null,
                "the statically resolved call records its single return boundary and no "
                    + "dynamic set");
        }
    }

    // =========================================================================
    // 5. Determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- Determinism: repeated lowerings produce byte-identical "
            + "dumps --");
        for (String[] spec : List.of(
                new String[] {IIFE_SYNC_SOURCE, "iife sync"},
                new String[] {IIFE_ASYNC_SOURCE, "iife async"},
                new String[] {PARAMETER_SOURCE, "parameter callee"})) {
            Fixture first = fixture(spec[0], spec[1] + " (dump 1)");
            Fixture second = fixture(spec[0], spec[1] + " (dump 2)");
            if (first == null || second == null) {
                continue;
            }
            RawLowering firstUnit = rawLower(first, spec[1]);
            RawLowering secondUnit = rawLower(second, spec[1]);
            if (firstUnit == null || secondUnit == null) {
                continue;
            }
            check(SemanticIrValidator.toUnitText(firstUnit.unit())
                    .equals(SemanticIrValidator.toUnitText(secondUnit.unit())),
                spec[1] + ": repeated lowerings produce byte-identical dumps");
        }
    }

    // =========================================================================
    // 6. Negative seeds
    // =========================================================================

    private static void testNegativeSeeds() {
        System.out.println("-- Negative seeds: the dynamic cell rules are load-bearing --");
        Fixture fixture = fixture(IIFE_SYNC_SOURCE, "negative seeds");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "negative seeds");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        if (call == null) {
            fail("the negative seeds need the produced dynamic CALL");
            return;
        }
        KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
        KindPayload.DynamicReturnBoundary cells = payload.dynamicReturnBoundary();

        String wrongKind = negativeVerdict(unit, call, cells.dealBodyBoundaryOpId(),
            BoundaryKind.HOST_TO_DEAL, null, null);
        check(wrongKind != null && wrongKind.contains("FUNCTION_RETURN"),
            "a wrong-kind DEAL-body cell fails R-BOUNDARY-TRIPLE: " + wrongKind);

        String wrongDescriptor = negativeVerdict(unit, call, cells.dealBodyBoundaryOpId(),
            BoundaryKind.FUNCTION_RETURN, RuntimeDescriptor.String.INSTANCE, null);
        check(wrongDescriptor != null,
            "a DEAL-body cell on a wrong descriptor fails the closed gate: "
                + wrongDescriptor);

        String wrongMode = nonIndirectModeVerdict(unit);
        check(wrongMode != null && wrongMode.contains("INDIRECT"),
            "a Dynamic callee under a non-INDIRECT mode fails the closed gate: "
                + wrongMode);

        String missingCells = missingCellsVerdict(unit);
        check(missingCells != null,
            "a DYNAMIC call without its recorded cells fails the closed gate: "
                + missingCells);

        String wrongParent = negativeVerdict(unit, call, cells.dealBodyBoundaryOpId(),
            BoundaryKind.FUNCTION_RETURN, null, call.opId());
        check(wrongParent != null && wrongParent.contains("parented to a RETURN naming "
                + "the CALL"),
            "a DEAL-body cell parented to the CALL op fails the parent rule: "
                + wrongParent);
    }

    /**
     * Rebuilds the unit with the dynamic shape corrupted (the hand-built
     * closed-rule violation surface) and returns the gate's first failure text.
     * {@code kind}/{@code descriptor} rewrite the DEAL-body cell's payload and
     * {@code retargetParent} moves the cell's parent.
     */
    private static String negativeVerdict(LoweredModuleUnit unit, SemanticOp call,
                                          OpId dealCellId, BoundaryKind kind,
                                          RuntimeDescriptor descriptor,
                                          OpId retargetParent) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(call.opId())) {
                KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
                ops.add(rebuild(op, new KindPayload.CallPayload(payload.mode(),
                    payload.callee(), payload.signature(), payload.parameterBoundaryOpIds(),
                    payload.returnBoundaryOpId(), payload.dynamicReturnBoundary(),
                    payload.bodyBlock(), payload.externalEntryRef())));
                continue;
            }
            if (op.opId().equals(dealCellId) && (kind != null || descriptor != null
                    || retargetParent != null)) {
                KindPayload.BoundaryPayload boundary = boundaryOf(op);
                SourceOrigin origin = retargetParent == null ? op.origin()
                    : new SourceOrigin(op.origin().sourceId(), op.origin().span(),
                        op.origin().kind(), op.origin().anchorId(), retargetParent);
                KindPayload.BoundaryPayload rewritten = new KindPayload.BoundaryPayload(
                    kind == null ? boundary.kind() : kind,
                    descriptor == null ? boundary.descriptor() : descriptor,
                    boundary.input(), boundary.realization());
                ops.add(new SemanticOp(op.opId(), op.kind(), origin, op.result(),
                    op.resultType(), op.operands(), op.operandTypes(), rewritten,
                    op.failurePolicy(), contractOf(op, rewritten)));
                continue;
            }
            ops.add(op);
        }
        return validateUnit(corrupted(unit, ops));
    }

    private static String nonIndirectModeVerdict(LoweredModuleUnit unit) {
        String corrupted = substitutePayloadLeaf(SemanticIrValidator.toUnitText(unit),
            SemanticOpKind.CALL, "mode", "HOST", true);
        if (corrupted == null) {
            return null;
        }
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        return SemanticIrValidator.validateText(corrupted, facts)
            .map(CompilerDiagnostic::message).orElse(null);
    }

    /**
     * The missing-cells negative at the text surface: the closed construction
     * requires a Dynamic callee to record its set, so the recorded object is
     * dropped from the canonical text.
     */
    private static String missingCellsVerdict(LoweredModuleUnit unit) {
        String corrupted = dropPayloadLeaf(SemanticIrValidator.toUnitText(unit),
            SemanticOpKind.CALL, "dynamicReturnBoundary", true);
        if (corrupted == null) {
            return null;
        }
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        return SemanticIrValidator.validateText(corrupted, facts)
            .map(CompilerDiagnostic::message).orElse(null);
    }

    // =========================================================================
    // The canonical-text corruption surface (the S6 text-surface negatives)
    // =========================================================================

    /** Substitutes one payload leaf of the {@code dynamicCallee} CALL op. */
    private static String substitutePayloadLeaf(String text, SemanticOpKind kind, String key,
                                                String to, boolean dynamicCallee) {
        deal.semantic.ir.CanonicalJson.Obj op = dynamicCalleeOp(text, kind, dynamicCallee);
        if (op == null) {
            return null;
        }
        deal.semantic.ir.CanonicalJson.Obj payload =
            (deal.semantic.ir.CanonicalJson.Obj) at(op, "payload");
        deal.semantic.ir.CanonicalJson.Obj payload2 = withEntry(payload, key,
            deal.semantic.ir.CanonicalJson.str(to));
        return renderOp(text, op, payload2);
    }

    /** Drops one payload leaf of the {@code dynamicCallee} CALL op. */
    private static String dropPayloadLeaf(String text, SemanticOpKind kind, String key,
                                          boolean dynamicCallee) {
        deal.semantic.ir.CanonicalJson.Obj op = dynamicCalleeOp(text, kind, dynamicCallee);
        if (op == null) {
            return null;
        }
        deal.semantic.ir.CanonicalJson.Obj payload =
            (deal.semantic.ir.CanonicalJson.Obj) at(op, "payload");
        deal.semantic.ir.CanonicalJson.Obj payload2 = withoutEntry(payload, key);
        return renderOp(text, op, payload2);
    }

    /** The first op of the kind whose callee is the dynamic shape. */
    private static deal.semantic.ir.CanonicalJson.Obj dynamicCalleeOp(
            String text, SemanticOpKind kind, boolean dynamicCallee) {
        deal.semantic.ir.CanonicalJson.Obj root =
            (deal.semantic.ir.CanonicalJson.Obj) deal.semantic.ir.CanonicalJson.parse(text);
        deal.semantic.ir.CanonicalJson.Arr ops =
            (deal.semantic.ir.CanonicalJson.Arr) at(root, "ops");
        for (deal.semantic.ir.CanonicalJson.Value item : ops.items()) {
            deal.semantic.ir.CanonicalJson.Obj op =
                (deal.semantic.ir.CanonicalJson.Obj) item;
            if (!kind.name().equals(strAt(op, "kind"))) {
                continue;
            }
            deal.semantic.ir.CanonicalJson.Obj payload =
                (deal.semantic.ir.CanonicalJson.Obj) at(op, "payload");
            deal.semantic.ir.CanonicalJson.Obj callee =
                (deal.semantic.ir.CanonicalJson.Obj) at(payload, "callee");
            if (dynamicCallee == "dynamic".equals(strAt(callee, "type"))) {
                return op;
            }
        }
        fail("the text-surface negative needs the rendered dynamic CALL op");
        return null;
    }

    /** One op re-rendered with a replaced payload and its recomputed contract. */
    private static String renderOp(String text, deal.semantic.ir.CanonicalJson.Obj op,
                                   deal.semantic.ir.CanonicalJson.Obj payload) {
        deal.semantic.ir.CanonicalJson.Obj contract =
            (deal.semantic.ir.CanonicalJson.Obj) at(op, "contract");
        deal.semantic.ir.CanonicalJson.Obj contract2 = withEntry(contract, "payload", payload);
        contract2 = withEntry(contract2, "canonicalDigest",
            deal.semantic.ir.CanonicalJson.str(recomputeContractDigest(contract2)));
        deal.semantic.ir.CanonicalJson.Obj op2 = withEntry(op, "payload", payload);
        op2 = withEntry(op2, "contract", contract2);
        deal.semantic.ir.CanonicalJson.Obj root =
            (deal.semantic.ir.CanonicalJson.Obj) deal.semantic.ir.CanonicalJson.parse(text);
        deal.semantic.ir.CanonicalJson.Arr ops =
            (deal.semantic.ir.CanonicalJson.Arr) at(root, "ops");
        List<deal.semantic.ir.CanonicalJson.Value> items = new ArrayList<>();
        for (deal.semantic.ir.CanonicalJson.Value item : ops.items()) {
            deal.semantic.ir.CanonicalJson.Obj candidate =
                (deal.semantic.ir.CanonicalJson.Obj) item;
            items.add(((deal.semantic.ir.CanonicalJson.Obj) at(candidate, "opId"))
                    .equals(at(op, "opId")) ? op2 : candidate);
        }
        return deal.semantic.ir.CanonicalJson.serializeText(
            withEntry(root, "ops", deal.semantic.ir.CanonicalJson.arr(items)));
    }

    private static String recomputeContractDigest(
            deal.semantic.ir.CanonicalJson.Obj contract) {
        List<deal.semantic.ir.CanonicalJson.Entry> eight = new ArrayList<>();
        for (deal.semantic.ir.CanonicalJson.Entry entry : contract.entries()) {
            if (!"canonicalDigest".equals(entry.key())) {
                eight.add(entry);
            }
        }
        return deal.semantic.ir.CanonicalJson.sha256Hex(
            deal.semantic.ir.CanonicalJson.serializeBytes(
                deal.semantic.ir.CanonicalJson.obj(eight)));
    }

    private static deal.semantic.ir.CanonicalJson.Value at(
            deal.semantic.ir.CanonicalJson.Obj obj, String key) {
        for (deal.semantic.ir.CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }

    private static String strAt(deal.semantic.ir.CanonicalJson.Obj obj, String key) {
        deal.semantic.ir.CanonicalJson.Value value = at(obj, key);
        return value instanceof deal.semantic.ir.CanonicalJson.Str str ? str.value() : null;
    }

    private static deal.semantic.ir.CanonicalJson.Obj withEntry(
            deal.semantic.ir.CanonicalJson.Obj obj, String key,
            deal.semantic.ir.CanonicalJson.Value value) {
        List<deal.semantic.ir.CanonicalJson.Entry> entries = new ArrayList<>();
        boolean replaced = false;
        for (deal.semantic.ir.CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                entries.add(new deal.semantic.ir.CanonicalJson.Entry(key, value));
                replaced = true;
            } else {
                entries.add(entry);
            }
        }
        if (!replaced) {
            fail("the text-surface negative needs the rendered contract field '" + key + "'");
        }
        return deal.semantic.ir.CanonicalJson.obj(entries);
    }

    private static deal.semantic.ir.CanonicalJson.Obj withoutEntry(
            deal.semantic.ir.CanonicalJson.Obj obj, String key) {
        List<deal.semantic.ir.CanonicalJson.Entry> entries = new ArrayList<>();
        for (deal.semantic.ir.CanonicalJson.Entry entry : obj.entries()) {
            if (!entry.key().equals(key)) {
                entries.add(entry);
            }
        }
        return deal.semantic.ir.CanonicalJson.obj(entries);
    }

    /** One op with a replaced payload and its rewired contract snapshot. */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contractOf(op, payload));
    }

    /** The rewired contract snapshot of one rebuilt payload. */
    private static deal.semantic.ir.OperationContractSnapshot contractOf(SemanticOp op,
                                                                         KindPayload payload) {
        deal.semantic.ir.OperationContractSnapshot placeholder =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(),
                op.resultType(), op.operandTypes(), null, payload, op.failurePolicy(),
                List.of(), "placeholder");
        String digest = deal.semantic.ir.ContractSnapshotCanonicalizer.digest(placeholder);
        return new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(), digest);
    }

    private static LoweredModuleUnit corrupted(LoweredModuleUnit unit, List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    private static String validateUnit(LoweredModuleUnit unit) {
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        return SemanticIrValidator.validate(unit, facts)
            .map(CompilerDiagnostic::message).orElse(null);
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Dynamic Call Shape Production Test (ISSUE-0657) ===\n");
        testDynamicCallShape();
        testDynamicAsyncShape();
        testIdentifierCalleeArm();
        testStaticArmsUnchanged();
        testDeterminism();
        testNegativeSeeds();
        System.out.println();
        System.out.println("Dynamic call shape production: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
