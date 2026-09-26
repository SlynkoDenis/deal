package deal.semantic;

import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.ModuleResolver.ModuleNotFoundException;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
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
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0674 — the closed gate of the function-typed materialization: the
 * producing-position clause, the callee-position exclusivity, the dynamic
 * cell family, and the refinements the identity-preserving function-typed
 * load of the seeded intrinsic binding requires (wiki
 * {@code function-typed-value-materialization-and-dispatch} M2 item 4 and
 * M3 items 3-6; wiki {@code conversion-intrinsic-function-values} J1).
 *
 * <ol>
 *   <li><b>Producing position.</b>
 *       {@code BindingsProductionValidator.REGISTRY_ONE_TO_ONE} admits a
 *       {@code DynamicFunctionValue} key exactly when the op its record
 *       names produces that key identity and the key carries no static
 *       producing position: a closure/adapt/export-read production, a
 *       function-typed {@code HOST_TO_DEAL} crossing input, and a
 *       producer-less seed {@code BINDING_INIT} operand each keep the
 *       closed gate rejecting, and the group family keeps its own closed
 *       class (exactly one {@code LoweredBody} per member). The producer
 *       rule's dynamic arms — a function-typed binding load, a member read
 *       with a function-typed result, a call result, and an awaited
 *       completion (the {@code AWAIT} result) — are admitted as the
 *       record's producing op. Every other key
 *       keeps its landed clause; the exactly-one registration discipline is
 *       unchanged.</li>
 *   <li><b>Callee position.</b> A {@code DynamicFunctionValue}
 *       registration is admissible exactly as a dynamic
 *       ({@code CallCallee.Dynamic}) call/await callee: the indirect callee
 *       spelling over the same identity fails closed as a producer defect
 *       ({@code R-FUNCTION-BINDING}, the dynamic callee-position
 *       exclusivity) on both the typed and the canonical text surface, and
 *       the inline static spelling stays rejected by the
 *       closed nested shape enumeration ({@code R-ENUM}). The indirect cell
 *       switch gains no dynamic case: the dynamic return-boundary set stays
 *       the registration's only cell family and the indirect spelling is
 *       never routed to it.</li>
 *   <li><b>Cell family.</b> A call whose callee registration is
 *       {@code dynamicFunctionValue} takes the landed dynamic return-cell
 *       arm on both the typed and the canonical text surface.</li>
 *   <li><b>Identity-preserving intrinsic load (J1).</b> A
 *       {@code BINDING_LOAD} naming the seed {@code BINDING_INIT}'s
 *       {@code {binding, generation}} that publishes that init's operand
 *       identity is not a producing position for the seed clause, while a
 *       load naming any other binding or generation and any other op
 *       carrying the seeded identity keep the clause rejecting; the
 *       converse clause is unchanged.</li>
 *   <li><b>VALUE-over-intrinsic exemption (J1).</b> The arity-extension
 *       unit's {@code VALUE} operand is the seeded intrinsic identity
 *       itself, so it passes {@code ADAPTER_SOURCE_SHAPE} with or without
 *       its proof; a proof recorded for it must name the seeded
 *       binding/generation; every other {@code VALUE} operand keeps the
 *       landed proof rule and the creation shape is unchanged.</li>
 * </ol>
 *
 * <p><b>Anti-hollow.</b> The positives are the real production walk's units
 * (the dynamic callee carrier reads of the identifier-callee fixture and
 * the seeded arity-extension adapter) with the registrations and the
 * identity-preserving load added exactly as the producer rule produces
 * them; every negative is one mutation of a passing unit, and each combined
 * drive runs the schema rules and the production rules over the same unit in
 * one run.</p>
 */
public class DynamicFunctionValueGateTest {

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

    // =========================================================================
    // Fixed invocation facts and the frontend/project harness
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("app");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new ExternalModuleInterface(MODULE, ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor.Func SIG0 =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Int.INSTANCE);
    private static final RuntimeDescriptor.Func SIG1 =
        new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Number.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);

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
        check(parse.diagnostics().isEmpty(), what + ": the fixture parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": the fixture resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": the fixture checks cleanly: "
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

    /**
     * The production walk's unit of one fixture (the unified walk's own
     * produced unit and block table, before the project entry's gate verdict)
     * plus the session's pinned write facts.
     */
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
            fail(what + ": the production walk produces the unit: " + defect);
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
    // Fixtures
    // =========================================================================

    /**
     * The identifier-callee fixture: a function-typed parameter invoked
     * directly and awaited. Both callees are dynamic
     * ({@code CallCallee.Dynamic}) over a function-typed {@code BINDING_LOAD}
     * whose cell value identity is not statically tracked — the
     * runtime-resolved callee values the producer rule registers as
     * {@code DynamicFunctionValue}.
     */
    private static final String DYNAMIC_CALLEE_SOURCE = """
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

    /**
     * The arity-extension fixture: the {@code int} conversion intrinsic is
     * assigned to a two-parameter target through the adapted declaration (the
     * shape map's VALUE-over-intrinsic arm, no proof in the payload), and a
     * binding is read once so the identifier construct row keeps its produced
     * load.
     */
    private static final String ARITY_EXTENSION_SOURCE = """
        let f: (x: number, y: number) => int = int;
        let x: int = 1;
        let r: int = x;

        export function main(): null {
          return null
        }
        """;

    // =========================================================================
    // Op construction and unit doctoring
    // =========================================================================

    private static int nextOp = 9000;
    private static int nextVal = 9000;

    private static OpId nextOpId() {
        return new OpId(MODULE, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp newOp(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy,
            OpId parent) {
        OperationContractSnapshot contract = contractFor(kind, payload, resultType, List.of(),
            policy, "placeholder");
        contract = contractFor(kind, payload, resultType, List.of(), policy,
            ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp opWith(SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy,
            OpId parent) {
        return newOp(nextOpId(), kind, payload, result, resultType, policy, parent);
    }

    private static SemanticOp opWithOperands(SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, List<ValueId> operands,
            List<RuntimeDescriptor> operandTypes, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract = contractFor(kind, payload, resultType,
            operandTypes, policy, "placeholder");
        contract = contractFor(kind, payload, resultType, operandTypes, policy,
            ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(nextOpId(), kind, origin(parent), result, resultType, operands,
            operandTypes, payload, policy, contract);
    }

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind,
            RuntimeDescriptor descriptor, ValueId input, FailurePolicyId policy, OpId parent) {
        return newOp(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("check")),
            null, null, policy, parent);
    }

    /** Replaces one op's payload, recomputing its contract digest (same op id and origin). */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload,
            OpResultType resultType) {
        OperationContractSnapshot contract = contractFor(op.kind(), payload, resultType,
            op.operandTypes(), op.failurePolicy(), "placeholder");
        contract = contractFor(op.kind(), payload, resultType, op.operandTypes(),
            op.failurePolicy(), ContractSnapshotCanonicalizer.digest(contract));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(), resultType,
            op.operands(), op.operandTypes(), payload, op.failurePolicy(), contract);
    }

    private static LoweredModuleUnit copy(LoweredModuleUnit unit,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), registry, ops);
    }

    private static LoweredModuleUnit withRegistry(LoweredModuleUnit unit,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry) {
        return copy(unit, registry, unit.ops());
    }

    private static LoweredModuleUnit withOp(LoweredModuleUnit unit, SemanticOp op) {
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        ops.add(op);
        return copy(unit, unit.functionBindings(), ops);
    }

    private static LoweredModuleUnit replaceOp(LoweredModuleUnit unit, SemanticOp target,
            KindPayload payload, OpResultType resultType) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op == target ? rebuild(op, payload, resultType) : op);
        }
        return copy(unit, unit.functionBindings(), ops);
    }

    private static StructuredBodyTable withTableOp(StructuredBodyTable table, SemanticOp op,
            BlockId block) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
            blockOps.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        blockOps.computeIfAbsent(block, k -> new ArrayList<>()).add(op.opId());
        Map<OpId, BlockId> inverse = new LinkedHashMap<>(table.opBlocks());
        inverse.put(op.opId(), block);
        return new StructuredBodyTable(blockOps, inverse);
    }

    /** The synthetic single-block unit of the clause-level drives. */
    private static LoweredModuleUnit syntheticUnit(
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry,
            Map<FunctionId, LoweredFunction> functions, List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MODULE, INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH),
            Set.of(), Map.of(), Map.of(), functions,
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), registry, ops);
    }

    private static StructuredBodyTable syntheticTable(List<SemanticOp> ops) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        Map<OpId, BlockId> inverse = new LinkedHashMap<>();
        List<OpId> ids = new ArrayList<>();
        for (SemanticOp op : ops) {
            ids.add(op.opId());
            inverse.put(op.opId(), new BlockId(0));
        }
        blockOps.put(new BlockId(0), ids);
        return new StructuredBodyTable(blockOps, inverse);
    }

    // =========================================================================
    // Assertions
    // =========================================================================

    private static SemanticIrValidator.ComparisonFacts facts(LoweredModuleUnit unit) {
        return new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    private static void assertBindingsPass(Optional<CompilerDiagnostic> failure, String what) {
        check(failure.isEmpty(), what + " passes the production gate: "
            + failure.map(CompilerDiagnostic::message).orElse("admission"));
    }

    private static void assertSchemaPass(Optional<CompilerDiagnostic> failure, String what) {
        check(failure.isEmpty(), what + " passes the closed schema gate: "
            + failure.map(CompilerDiagnostic::message).orElse("admission"));
    }

    /** Asserts the named production rule with the given message fragments. */
    private static void assertBindingsRule(Optional<CompilerDiagnostic> failure, String rule,
            String what, String... contains) {
        check(failure.isPresent(), what + " fails the production gate");
        if (failure.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = failure.get();
        check("E6005".equals(diagnostic.code()), what + " is rejected with E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            what + " carries the canonical E6005 code");
        String message = diagnostic.message();
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the production rule " + rule + "; got \"" + message + "\"");
        for (String fragment : contains) {
            check(message.contains(fragment),
                what + " message contains \"" + fragment + "\"; got \"" + message + "\"");
        }
    }

    /** Asserts the named closed schema rule with the given message fragments. */
    private static void assertSchemaRule(Optional<CompilerDiagnostic> failure, String rule,
            String what, String... contains) {
        check(failure.isPresent(), what + " fails the closed schema gate");
        if (failure.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = failure.get();
        check("E6005".equals(diagnostic.code()), what + " is rejected with E6005");
        String message = diagnostic.message();
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the closed schema rule " + rule + "; got \"" + message + "\"");
        for (String fragment : contains) {
            check(message.contains(fragment),
                what + " message contains \"" + fragment + "\"; got \"" + message + "\"");
        }
    }

    // =========================================================================
    // Op lookup helpers
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

    /** The function-typed {@code BINDING_LOAD}s of the unit (the dynamic producer arm's shape). */
    private static List<SemanticOp> functionTypedLoads(LoweredModuleUnit unit) {
        List<SemanticOp> loads = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_LOAD
                    && op.resultType() instanceof RuntimeDescriptor.Func) {
                loads.add(op);
            }
        }
        return loads;
    }

    /**
     * The runtime-resolved callee carrier reads of the dynamic-callee fixture:
     * the call's and the await's callee value producers.
     */
    private static List<SemanticOp> dynamicCalleeLoads(LoweredModuleUnit unit) {
        List<ValueId> callees = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload call
                    && call.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                callees.add(dynamic.callee());
            }
            if (op.payload() instanceof KindPayload.AsyncStartPayload start
                    && start.callee() instanceof KindPayload.CallCallee.Dynamic dynamic) {
                callees.add(dynamic.callee());
            }
        }
        List<SemanticOp> loads = new ArrayList<>();
        for (SemanticOp load : functionTypedLoads(unit)) {
            if (callees.contains((ValueId) load.result())) {
                loads.add(load);
            }
        }
        return loads;
    }

    /** The registry of the fixture plus one {@code DynamicFunctionValue} per callee carrier. */
    private static Map<FunctionAllocationIdentity, FunctionExecutionBinding>
            registerDynamicCallees(LoweredModuleUnit unit) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry =
            new LinkedHashMap<>(unit.functionBindings());
        for (SemanticOp load : dynamicCalleeLoads(unit)) {
            registry.put(new FunctionAllocationIdentity(((ValueId) load.result()).id()),
                new FunctionExecutionBinding.DynamicFunctionValue(load.opId(),
                    (RuntimeDescriptor.Func) load.resultType()));
        }
        return registry;
    }

    // =========================================================================
    // 1. REGISTRY_ONE_TO_ONE: the producing position of a dynamic key
    // =========================================================================

    private static void testProducingPositionClause() {
        System.out.println("-- REGISTRY_ONE_TO_ONE: the dynamic key's producing position --");

        Fixture fixture = fixture(DYNAMIC_CALLEE_SOURCE, "dynamic callee");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "dynamic callee");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        List<SemanticOp> loads = dynamicCalleeLoads(unit);
        check(loads.size() == 2, "the fixture carries the two runtime-resolved callee carrier "
            + "reads (the call's and the await's); got " + loads.size());
        if (loads.size() != 2) {
            return;
        }
        for (SemanticOp load : loads) {
            check(load.resultType() instanceof RuntimeDescriptor.Func
                    && !unit.functionBindings().containsKey(
                        new FunctionAllocationIdentity(((ValueId) load.result()).id())),
                "the callee carrier read " + load.opId() + " publishes an unregistered "
                    + "function-typed identity (the dynamic producer arm's materialization)");
        }

        // The positive: the two registrations of the dynamic callee values.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry =
            registerDynamicCallees(unit);
        LoweredModuleUnit registered = withRegistry(unit, registry);
        assertBindingsPass(BindingsProductionValidator.validate(registered, raw.table(),
            raw.lowerer().pinnedWriteFacts()),
            "a unit whose DynamicFunctionValue keys name exactly the ops publishing them and "
                + "carry no static producing position");

        // The negative (a static producing position): a dynamic registration
        // keyed by a load that republishes a CLOSURE_NEW identity.
        SemanticOp closureLoad = null;
        long closureKey = -1;
        for (SemanticOp load : functionTypedLoads(unit)) {
            long key = ((ValueId) load.result()).id();
            if (!loads.contains(load)
                    && unit.functionBindings().get(new FunctionAllocationIdentity(key))
                        instanceof FunctionExecutionBinding.LoweredBody) {
                closureLoad = load;
                closureKey = key;
                break;
            }
        }
        check(closureLoad != null, "the fixture carries a function-typed load republishing a "
            + "LoweredBody-registered (closure) identity");
        if (closureLoad != null) {
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> closureRegistry =
                new LinkedHashMap<>(registry);
            closureRegistry.put(new FunctionAllocationIdentity(closureKey),
                new FunctionExecutionBinding.DynamicFunctionValue(closureLoad.opId(),
                    (RuntimeDescriptor.Func) closureLoad.resultType()));
            LoweredModuleUnit closureUnit = withRegistry(unit, closureRegistry);
            assertBindingsRule(BindingsProductionValidator.validate(closureUnit, raw.table(),
                    raw.lowerer().pinnedWriteFacts()), "REGISTRY_ONE_TO_ONE",
                "a dynamic registration keyed by a load republishing a CLOSURE_NEW identity",
                "is produced by 1 static producing op(s)", "carries no static producing position");
        }

        // The negative (the producing-op correlation): the registration names
        // the other load's op.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> swapped =
            new LinkedHashMap<>(unit.functionBindings());
        swapped.put(new FunctionAllocationIdentity(((ValueId) loads.get(0).result()).id()),
            new FunctionExecutionBinding.DynamicFunctionValue(loads.get(1).opId(),
                (RuntimeDescriptor.Func) loads.get(0).resultType()));
        swapped.put(new FunctionAllocationIdentity(((ValueId) loads.get(1).result()).id()),
            new FunctionExecutionBinding.DynamicFunctionValue(loads.get(1).opId(),
                (RuntimeDescriptor.Func) loads.get(1).resultType()));
        LoweredModuleUnit swappedUnit = withRegistry(unit, swapped);
        assertBindingsRule(BindingsProductionValidator.validate(swappedUnit, raw.table(),
            raw.lowerer().pinnedWriteFacts()), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration whose named op does not publish its key",
            "whose result identity is not that key");

        // The negative (an absent producing op): a dangling correlation id.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> dangling =
            new LinkedHashMap<>(registry);
        dangling.put(new FunctionAllocationIdentity(((ValueId) loads.get(0).result()).id()),
            new FunctionExecutionBinding.DynamicFunctionValue(new OpId(MODULE, 987654),
                (RuntimeDescriptor.Func) loads.get(0).resultType()));
        LoweredModuleUnit danglingUnit = withRegistry(unit, dangling);
        assertBindingsRule(BindingsProductionValidator.validate(danglingUnit, raw.table(),
            raw.lowerer().pinnedWriteFacts()), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration naming no op of the unit",
            "which is no op of the unit");
    }

    // =========================================================================
    // 2. The closed static producing-position families
    // =========================================================================

    private static void testProducingPositionFamilies() {
        System.out.println("-- the closed static producing-position families --");

        ValueId key = new ValueId(500);
        ValueId operand = new ValueId(501);
        BindingId sourceBinding = new BindingId(1);
        SemanticOp sourceAlloc = opWith(SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(sourceBinding, new BlockId(0), true,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp sourceValue = opWith(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(7)),
            operand, INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp sourceInit = opWith(SemanticOpKind.BINDING_INIT,
            new KindPayload.BindingInitPayload(sourceBinding, 0, operand), null, null,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp load = opWith(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(sourceBinding, 0), key, SIG0,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry =
            Map.of(new FunctionAllocationIdentity(key.id()),
                new FunctionExecutionBinding.DynamicFunctionValue(load.opId(), SIG0));

        // The positive control: a function-typed BINDING_LOAD publishes the key
        // and the registration names that load.
        assertBindingsPass(BindingsProductionValidator.validate(
                syntheticUnit(registry, Map.of(),
                    List.of(sourceAlloc, sourceValue, sourceInit, load)),
                syntheticTable(List.of(sourceAlloc, sourceValue, sourceInit, load))),
            "a dynamic key whose single producing op is the load publishing it");

        // The read-arm positive control: a container/class member read with a
        // function-typed result is a *dynamic* producer (the read allocates the
        // identity and the producer rule registers DynamicFunctionValue for
        // it), so it is not a static producing position of the dynamic clause.
        ValueId readKey = new ValueId(520);
        ValueId receiver = new ValueId(521);
        SemanticOp memberRead = opWithOperands(SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(receiver, "f"),
            readKey, SIG0, List.of(receiver), List.of(SIG0),
            FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsPass(BindingsProductionValidator.validate(
                syntheticUnit(Map.of(new FunctionAllocationIdentity(readKey.id()),
                        new FunctionExecutionBinding.DynamicFunctionValue(
                            memberRead.opId(), SIG0)),
                    Map.of(), List.of(memberRead)),
                syntheticTable(List.of(memberRead))),
            "a dynamic registration keyed by a function-typed MEMBER_READ result "
                + "(the read is the materialization's producing op)");

        // The correlation still applies to the read family: a registration whose
        // named op is not the read publishing the key fails closed.
        SemanticOp otherRead = opWithOperands(SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(receiver, "g"),
            nextValue(), SIG0, List.of(receiver), List.of(SIG0),
            FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsRule(BindingsProductionValidator.validate(
                syntheticUnit(Map.of(new FunctionAllocationIdentity(readKey.id()),
                        new FunctionExecutionBinding.DynamicFunctionValue(
                            otherRead.opId(), SIG0)),
                    Map.of(), List.of(memberRead, otherRead)),
                syntheticTable(List.of(memberRead, otherRead))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration naming a member read that publishes another "
                + "identity",
            "whose result identity is not that key");

        // The call-result and awaited-completion arms: the CALL op and the AWAIT
        // op (the op that allocates and publishes the completion value identity
        // — the ASYNC_START result is the token, never a value) are dynamic
        // producers of their function-typed results.
        ValueId callKey = new ValueId(522);
        SemanticOp callOp = opWith(SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Dynamic(new ValueId(523)), SIG0, List.of(),
                null, new KindPayload.DynamicReturnBoundary(nextOpId(), nextOpId(),
                    nextOpId()), null, null),
            callKey, SIG0, FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsPass(BindingsProductionValidator.validate(
                syntheticUnit(Map.of(new FunctionAllocationIdentity(callKey.id()),
                        new FunctionExecutionBinding.DynamicFunctionValue(callOp.opId(),
                            SIG0)),
                    Map.of(), List.of(callOp)),
                syntheticTable(List.of(callOp))),
            "a dynamic registration keyed by a function-typed CALL result");

        ValueId completionKey = new ValueId(524);
        OpId completionBoundary = nextOpId();
        SemanticOp awaitOp = opWith(SemanticOpKind.AWAIT,
            new KindPayload.AwaitPayload(
                new AsyncTokenId.Canonical(4242, AsyncTokenOwner.DEAL_BODY_TASK), SIG0,
                completionBoundary),
            completionKey, SIG0, FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsPass(BindingsProductionValidator.validate(
                syntheticUnit(Map.of(new FunctionAllocationIdentity(completionKey.id()),
                        new FunctionExecutionBinding.DynamicFunctionValue(awaitOp.opId(),
                            SIG0)),
                    Map.of(), List.of(awaitOp)),
                syntheticTable(List.of(awaitOp))),
            "a dynamic registration keyed by a function-typed AWAIT completion result");

        // (a) An adapter production of the same key.
        RuntimeDescriptor.Func adaptTarget = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Number.INSTANCE, RuntimeDescriptor.Number.INSTANCE),
            RuntimeDescriptor.Int.INSTANCE);
        SemanticOp adapt = opWithOperands(SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(SIG1, adaptTarget, CaptureMode.VALUE,
                new AdaptSourceRef.Value(operand), null),
            key, adaptTarget, List.of(operand), List.of(SIG1),
            FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsRule(BindingsProductionValidator.validate(
                syntheticUnit(registry, Map.of(), List.of(adapt)),
                syntheticTable(List.of(adapt))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration keyed by a FUNCTION_ADAPT result",
            "is produced by 1 static producing op(s)");

        // (b) An export-read production of the same key.
        SemanticOp exportRead = opWith(SemanticOpKind.EXPORT_READ,
            new KindPayload.ExportReadPayload(new ModuleId("lib"), "f", SIG0, key),
            nextValue(), SIG0, FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsRule(BindingsProductionValidator.validate(
                syntheticUnit(registry, Map.of(), List.of(exportRead)),
                syntheticTable(List.of(exportRead))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration keyed by an EXPORT_READ value",
            "is produced by 1 static producing op(s)");

        // (c) A function-typed HOST_TO_DEAL crossing input of the same key.
        SemanticOp crossing = boundaryWith(nextOpId(), BoundaryKind.HOST_TO_DEAL, SIG0, key,
            FailurePolicyId.HOST_SYNC_RETURN, null);
        assertBindingsRule(BindingsProductionValidator.validate(
                syntheticUnit(registry, Map.of(), List.of(crossing)),
                syntheticTable(List.of(crossing))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration keyed by a function-typed host crossing input",
            "is produced by 0 static producing op(s)",
            "1 function-typed host crossing(s)");

        // (d) A producer-less seed BINDING_INIT operand.
        BindingId seedBinding = new BindingId(2);
        SemanticOp alloc = opWith(SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(seedBinding, new BlockId(0), false,
                BindingCellKind.DIRECT, 0),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp seedInit = opWith(SemanticOpKind.BINDING_INIT,
            new KindPayload.BindingInitPayload(seedBinding, 0, key), null, null,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsRule(BindingsProductionValidator.validate(
                syntheticUnit(registry, Map.of(), List.of(alloc, seedInit)),
                syntheticTable(List.of(alloc, seedInit))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration keyed by a producer-less seed BINDING_INIT operand",
            "and 1 seed BINDING_INIT(s)", "carries no static producing position");

        // (d2) The same seed operand carrying an identity-preserving load: the
        // load is not a producing position for the seed clause, so a dynamic
        // registration for the seeded identity still fails the clause.
        SemanticOp seededLoad = opWith(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(seedBinding, 0), key, SIG0,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        assertBindingsRule(BindingsProductionValidator.validate(syntheticUnit(registry,
                Map.of(), List.of(alloc, seedInit, seededLoad)),
                syntheticTable(List.of(alloc, seedInit, seededLoad))), "REGISTRY_ONE_TO_ONE",
            "a dynamic registration keyed by the seeded identity a load republishes",
            "and 1 seed BINDING_INIT(s)");

        // (e) A group member identity: the group family keeps its own closed
        // class (exactly one LoweredBody per member).
        FunctionId member = new FunctionId(77);
        BlockId memberBody = new BlockId(78);
        SemanticOp group = opWith(SemanticOpKind.RECURSIVE_GROUP_INIT,
            new KindPayload.RecursiveGroupInitPayload(List.of(new BindingId(3)),
                List.of(member)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit groupUnit = syntheticUnit(
            Map.of(new FunctionAllocationIdentity(key.id()),
                new FunctionExecutionBinding.DynamicFunctionValue(load.opId(), SIG0)),
            Map.of(member, new LoweredFunction(member, SIG0, List.of(), memberBody)),
            List.of(group));
        assertBindingsRule(BindingsProductionValidator.validate(groupUnit,
            syntheticTable(List.of(group))), "GROUP_SHAPE",
            "a group member identity carrying a dynamic registration",
            "has no LoweredBody registration");
    }

    // =========================================================================
    // 3. The callee position and the dynamic cell family
    // =========================================================================

    /**
     * The synthetic callee unit: one function-typed carrier read, the
     * terminal cells, and one invocation whose callee is the carrier read.
     * The {@code dynamic} arm records the closed cell family of the
     * {@code Dynamic} callee; the indirect arm records the single return
     * boundary of the static families.
     */
    private static LoweredModuleUnit calleeUnit(boolean async, boolean dynamic) {
        ValueId calleeValue = new ValueId(601);
        OpId invocationOp = nextOpId();
        ValueId operand = new ValueId(602);
        List<SemanticOp> ops = new ArrayList<>();
        SemanticOp load = opWith(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(new BindingId(9), 0), calleeValue, SIG0,
            FailurePolicyId.NO_DEAL_FAILURE, null);
        ops.add(load);
        KindPayload payload;
        OpResultType resultType;
        if (async) {
            OpId taskCellId = null;
            if (dynamic) {
                OpId taskReturn = nextOpId();
                SemanticOp taskCell = boundaryWith(nextOpId(), BoundaryKind.FUNCTION_RETURN,
                    INT, operand, FailurePolicyId.TYPE_DESCRIPTOR, taskReturn);
                ops.add(taskCell);
                ops.add(newOp(taskReturn, SemanticOpKind.RETURN,
                    new KindPayload.ReturnPayload(operand, new FunctionId(1), invocationOp,
                        taskCell.opId()),
                    null, null, FailurePolicyId.NO_DEAL_FAILURE, invocationOp));
                taskCellId = taskCell.opId();
            }
            payload = new KindPayload.AsyncStartPayload(dynamic
                    ? new KindPayload.CallCallee.Dynamic(calleeValue)
                    : new KindPayload.CallCallee.Indirect(calleeValue),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(), INT,
                taskCellId, null, null);
            resultType = InternalResultType.INTERNAL_ASYNC;
        } else {
            OpId callReturn = nextOpId();
            SemanticOp dealCell = boundaryWith(nextOpId(), BoundaryKind.FUNCTION_RETURN, INT,
                operand, FailurePolicyId.TYPE_DESCRIPTOR, callReturn);
            ops.add(dealCell);
            ops.add(newOp(callReturn, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(operand, new FunctionId(1), invocationOp,
                    dealCell.opId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, invocationOp));
            SemanticOp hostCell = dynamic
                ? boundaryWith(nextOpId(), BoundaryKind.HOST_TO_DEAL, INT, operand,
                    FailurePolicyId.HOST_SYNC_RETURN, invocationOp) : null;
            SemanticOp externalCell = dynamic
                ? boundaryWith(nextOpId(), BoundaryKind.EXTERNAL_RETURN, INT, operand,
                    FailurePolicyId.TYPE_DESCRIPTOR, invocationOp) : null;
            if (dynamic) {
                ops.add(hostCell);
                ops.add(externalCell);
            }
            payload = new KindPayload.CallPayload(CallMode.INDIRECT, dynamic
                    ? new KindPayload.CallCallee.Dynamic(calleeValue)
                    : new KindPayload.CallCallee.Indirect(calleeValue),
                SIG0, List.of(), dynamic ? null : dealCell.opId(),
                dynamic ? new KindPayload.DynamicReturnBoundary(dealCell.opId(),
                    hostCell.opId(), externalCell.opId()) : null,
                null, null);
            resultType = INT;
        }
        ops.add(newOp(invocationOp, async ? SemanticOpKind.ASYNC_START : SemanticOpKind.CALL,
            payload, nextValue(), resultType, FailurePolicyId.NO_DEAL_FAILURE, null));
        return syntheticUnit(Map.of(new FunctionAllocationIdentity(calleeValue.id()),
            new FunctionExecutionBinding.DynamicFunctionValue(load.opId(), SIG0)),
            Map.of(), ops);
    }

    private static void testCalleePositionAndCellFamily() {
        System.out.println("-- the callee position and the dynamic cell family --");

        LoweredModuleUnit dynamicCall = calleeUnit(false, true);
        assertSchemaPass(SemanticIrValidator.validate(dynamicCall, facts(dynamicCall)),
            "a dynamic CALLEE over a DynamicFunctionValue registration");
        assertSchemaPass(SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(dynamicCall), facts(dynamicCall)),
            "the same unit on the canonical text surface");
        SemanticOp call = ofKind(dynamicCall, SemanticOpKind.CALL).get(0);
        check(call.payload() instanceof KindPayload.CallPayload payload
                && payload.callee() instanceof KindPayload.CallCallee.Dynamic
                && payload.dynamicReturnBoundary() != null
                && payload.returnBoundaryOpId() == null,
            "the call whose callee registration is dynamicFunctionValue takes the landed "
                + "dynamic return-cell arm (the three recorded cells, no single return id)");

        LoweredModuleUnit dynamicStart = calleeUnit(true, true);
        assertSchemaPass(SemanticIrValidator.validate(dynamicStart, facts(dynamicStart)),
            "a dynamic ASYNC_START callee over a DynamicFunctionValue registration");
        SemanticOp start = ofKind(dynamicStart, SemanticOpKind.ASYNC_START).get(0);
        check(start.payload() instanceof KindPayload.AsyncStartPayload payload
                && payload.callee() instanceof KindPayload.CallCallee.Dynamic
                && payload.returnBoundaryOpId() != null,
            "the await whose callee registration is dynamicFunctionValue takes the landed "
                + "DEAL_BODY task cell");

        // The negatives: the indirect callee spelling over the same identity
        // (the indirect cell switch admits no dynamic case).
        LoweredModuleUnit indirectCall = calleeUnit(false, false);
        assertSchemaRule(SemanticIrValidator.validate(indirectCall, facts(indirectCall)),
            "R-FUNCTION-BINDING",
            "an Indirect CALL callee resolving to a DynamicFunctionValue registration",
            "resolves its callee to a DynamicFunctionValue registration",
            "admissible exactly as a Dynamic call/await callee");

        LoweredModuleUnit indirectStart = calleeUnit(true, false);
        assertSchemaRule(SemanticIrValidator.validate(indirectStart, facts(indirectStart)),
            "R-FUNCTION-BINDING",
            "an Indirect ASYNC_START callee resolving to a DynamicFunctionValue registration",
            "resolves its callee to a DynamicFunctionValue registration",
            "admissible exactly as a Dynamic call/await callee");

        // The same negatives on the canonical text surface: the clause reads the
        // serialized callee and binding records, not the in-memory objects.
        assertSchemaRule(SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(indirectCall), facts(indirectCall)),
            "R-FUNCTION-BINDING",
            "the Indirect CALL callee on the canonical text surface",
            "resolves its callee to a DynamicFunctionValue registration");
        assertSchemaRule(SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(indirectStart), facts(indirectStart)),
            "R-FUNCTION-BINDING",
            "the Indirect ASYNC_START callee on the canonical text surface",
            "resolves its callee to a DynamicFunctionValue registration");

        // The static spelling stays rejected by the closed nested shape
        // enumeration (the landed R-ENUM clause).
        KindPayload staticPayload = new KindPayload.CallPayload(CallMode.INDIRECT,
            new KindPayload.CallCallee.Static(
                new FunctionExecutionBinding.DynamicFunctionValue(new OpId(MODULE, 9001), SIG0)),
            SIG0, List.of(), null, null, null, null);
        LoweredModuleUnit staticUnit = syntheticUnit(Map.of(), Map.of(),
            List.of(opWith(SemanticOpKind.CALL, staticPayload, nextValue(), INT,
                FailurePolicyId.NO_DEAL_FAILURE, null)));
        assertSchemaRule(SemanticIrValidator.validate(staticUnit, facts(staticUnit)), "R-ENUM",
            "a DynamicFunctionValue named inline in a static CALLEE position",
            "in a closed FunctionExecutionBinding shape position");
    }

    // =========================================================================
    // 4. The combined drive: the shape plus its dynamic registration
    // =========================================================================

    private static void testCombinedGates() {
        System.out.println("-- combined: the shape plus its dynamic registration through "
            + "both gates in one run --");

        Fixture fixture = fixture(DYNAMIC_CALLEE_SOURCE, "combined dynamic callee");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "combined dynamic callee");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        LoweredModuleUnit registered = withRegistry(unit, registerDynamicCallees(unit));

        // One run over one unit: the schema gates (typed and canonical text)
        // and the production gates.
        assertSchemaPass(SemanticIrValidator.validate(registered, facts(registered)),
            "the dynamic registrations on the typed schema surface");
        assertSchemaPass(SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(registered), facts(registered)),
            "the dynamic registrations on the canonical text schema surface");
        assertBindingsPass(BindingsProductionValidator.validate(registered, raw.table(),
            raw.lowerer().pinnedWriteFacts()),
            "the dynamic registrations through the production gates");

        // The drive is load-bearing: a registration whose producing-op position
        // is absent is rejected by the closed shape admission, and a
        // mis-correlated one by the correlation clause.
        String text = SemanticIrValidator.toUnitText(registered);
        String withoutOp = text.replaceFirst(
            "\"materializingBoundaryOpId\":\\{[^}]*\\}",
            "\"materializingBoundaryOpId\":null");
        check(!withoutOp.equals(text),
            "the canonical text carries the producing-op position on the landed key");
        assertSchemaRule(SemanticIrValidator.validateText(withoutOp, facts(registered)),
            "R-ENUM", "a registration whose producing-op position is absent",
            "carries no producing op id and descriptor text");

        List<SemanticOp> loads = dynamicCalleeLoads(unit);
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> misCorrelated =
            new LinkedHashMap<>(unit.functionBindings());
        misCorrelated.put(new FunctionAllocationIdentity(((ValueId) loads.get(0).result()).id()),
            new FunctionExecutionBinding.DynamicFunctionValue(loads.get(1).opId(),
                (RuntimeDescriptor.Func) loads.get(0).resultType()));
        misCorrelated.put(new FunctionAllocationIdentity(((ValueId) loads.get(1).result()).id()),
            new FunctionExecutionBinding.DynamicFunctionValue(loads.get(1).opId(),
                (RuntimeDescriptor.Func) loads.get(1).resultType()));
        LoweredModuleUnit misCorrelatedUnit = withRegistry(unit, misCorrelated);
        assertSchemaRule(SemanticIrValidator.validate(misCorrelatedUnit,
            facts(misCorrelatedUnit)), "R-FUNCTION-BINDING",
            "a mis-correlated registration on the typed schema surface",
            "does not carry the registered allocation identity as its result");
    }

    // =========================================================================
    // 5. The identity-preserving intrinsic load and the adapter exemption
    // =========================================================================

    private static void testAdapterValueOverIntrinsicExemption() {
        System.out.println("-- J1: the identity-preserving intrinsic load and the "
            + "VALUE-over-intrinsic exemption --");

        Fixture fixture = fixture(ARITY_EXTENSION_SOURCE, "arity extension");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "arity extension");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();

        // The seeded intrinsic identity and its seed BINDING_INIT.
        long seedKey = -1;
        BindingId seedBinding = null;
        long seedGeneration = -1;
        FunctionExecutionBinding.IntrinsicFunction intrinsic = null;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction value
                    && value.kind() == IntrinsicKind.INT_CONVERT) {
                seedKey = entry.getKey().id();
                intrinsic = value;
            }
        }
        check(seedKey > 0 && intrinsic != null,
            "the unit carries the INT_CONVERT seed registration");
        if (seedKey < 0) {
            return;
        }
        BlockId seedBlock = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() == seedKey) {
                seedBinding = init.binding();
                seedGeneration = init.generation();
                seedBlock = raw.table().opBlocks().get(op.opId());
            }
        }
        check(seedBinding != null && seedBlock != null,
            "the seed BINDING_INIT names the seeded binding/generation");
        if (seedBinding == null || seedBlock == null) {
            return;
        }

        // The adapter's recorded source is the seeded identity itself: the
        // creation shape is unchanged (VALUE over the intrinsic identity, no
        // proof in the payload).
        SemanticOp adaptOp = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adaptOp = op;
            }
        }
        check(adaptOp != null, "the arity-extension unit carries the FUNCTION_ADAPT");
        if (adaptOp == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload adaptPayload =
            (KindPayload.FunctionAdaptPayload) adaptOp.payload();
        check(adaptPayload.mode() == CaptureMode.VALUE
                && adaptPayload.source() instanceof AdaptSourceRef.Value value
                && value.value().id() == seedKey
                && adaptPayload.proof() == null,
            "the adapter's recorded source is the seeded intrinsic identity with no proof "
                + "(the creation shape is unchanged)");

        // The identity-preserving load of the seeded binding: the producer
        // rule's load-shaped materialization.
        SemanticOp preserved = opWith(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(seedBinding, seedGeneration),
            new ValueId(seedKey), intrinsic.descriptor(), FailurePolicyId.NO_DEAL_FAILURE,
            null);
        LoweredModuleUnit loaded = withOp(unit, preserved);
        StructuredBodyTable loadedTable = withTableOp(raw.table(), preserved, seedBlock);

        assertBindingsPass(BindingsProductionValidator.validate(loaded, loadedTable,
            raw.lowerer().pinnedWriteFacts()),
            "the unit carrying the function-typed load of the seeded intrinsic binding "
                + "(REGISTRY_ONE_TO_ONE and the ADAPTER_SOURCE_SHAPE VALUE-over-intrinsic "
                + "exemption)");
        assertSchemaPass(SemanticIrValidator.validate(loaded, facts(loaded)),
            "the load-carrying unit on the typed schema surface");
        assertSchemaPass(SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(loaded), facts(loaded)),
            "the load-carrying unit on the canonical text surface");

        // The exemption is closed: a load naming another binding is not an
        // identity-preserving load of the seeded binding, so the landed proof
        // rule governs the operand again.
        BindingId otherBinding = null;
        long otherGeneration = -1;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() != seedKey) {
                otherBinding = init.binding();
                otherGeneration = init.generation();
            }
        }
        check(otherBinding != null, "the unit carries a second binding initialization "
            + "(the non-qualifying load's target)");
        if (otherBinding == null) {
            return;
        }
        SemanticOp foreignLoad = opWith(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(otherBinding, otherGeneration),
            new ValueId(seedKey), intrinsic.descriptor(), FailurePolicyId.NO_DEAL_FAILURE,
            null);
        LoweredModuleUnit foreignUnit = withOp(unit, foreignLoad);
        assertBindingsRule(BindingsProductionValidator.validate(foreignUnit,
            withTableOp(raw.table(), foreignLoad, seedBlock),
            raw.lowerer().pinnedWriteFacts()), "ADAPTER_SOURCE_SHAPE",
            "a load naming another binding over the seeded identity",
            "carries a binding-load operand", "without its proof");

        // A proof recorded for the seeded operand must name the seeded
        // binding/generation.
        BindingId otherSeedBinding = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() != seedKey
                    && unit.functionBindings().get(new FunctionAllocationIdentity(
                        init.value().id()))
                        instanceof FunctionExecutionBinding.IntrinsicFunction) {
                otherSeedBinding = init.binding();
            }
        }
        check(otherSeedBinding != null, "the unit carries the other intrinsic seed binding");
        if (otherSeedBinding != null) {
            LoweredModuleUnit foreignProof = replaceOp(unit, adaptOp,
                new KindPayload.FunctionAdaptPayload(adaptPayload.sourceSignature(),
                    adaptPayload.targetSignature(), adaptPayload.mode(),
                    adaptPayload.source(),
                    new BindingImmutabilityProof(otherSeedBinding, seedGeneration)),
                adaptOp.resultType());
            assertBindingsRule(BindingsProductionValidator.validate(foreignProof, raw.table(),
                raw.lowerer().pinnedWriteFacts()), "ADAPTER_SOURCE_SHAPE",
                "a proof over the seeded intrinsic identity naming another binding",
                "naming no seeded binding/generation");
            assertSchemaPass(SemanticIrValidator.validate(foreignProof,
                facts(foreignProof)), "the mis-proved adapter unit on the schema surface");
        }

        // The seeded proof and the proof-less seeded operand: admissible with
        // or without the proof.
        LoweredModuleUnit seededProof = replaceOp(unit, adaptOp,
            new KindPayload.FunctionAdaptPayload(adaptPayload.sourceSignature(),
                adaptPayload.targetSignature(), adaptPayload.mode(), adaptPayload.source(),
                new BindingImmutabilityProof(seedBinding, seedGeneration)),
            adaptOp.resultType());
        assertBindingsPass(BindingsProductionValidator.validate(seededProof, raw.table(),
            raw.lowerer().pinnedWriteFacts()),
            "a proof naming the seeded binding/generation over the intrinsic operand");
        assertSchemaPass(SemanticIrValidator.validate(seededProof, facts(seededProof)),
            "the seeded-proof adapter unit on the schema surface");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Dynamic Function Value Gate / Identity-Preserving "
            + "Intrinsic Load Tests (ISSUE-0674) ===\n");

        testProducingPositionClause();
        testProducingPositionFamilies();
        testCalleePositionAndCellFamily();
        testCombinedGates();
        testAdapterValueOverIntrinsicExemption();

        System.out.println("\nDynamic function value gate: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
