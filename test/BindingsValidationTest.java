package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The validation child's tests (ISSUE-0451 sequencing item 8): the B9
 * production-time structural validation of the BINDINGS capability —
 * the closed rule set {@code GROUP_SHAPE}, {@code CAPTURE_RESOLUTION},
 * {@code BINDING_GENERATION_RESOLUTION}, {@code BINDING_INIT_ONCE},
 * {@code INIT_DOMINATES_LOAD}, {@code ADAPTER_PAIR},
 * {@code ADAPTER_SOURCE_SHAPE}, {@code REGISTRY_ONE_TO_ONE}, and
 * {@code NO_ADAPTER_AT_BOUNDARY} over the one uniform resolution
 * context (R1-R4) — enforced at the production site by the walk
 * ({@link SemanticLowerer#lowerModuleValidationCore}) and exposed as a
 * closed IR-level surface ({@link BindingsProductionValidator}).
 *
 * <p><b>Positive corpus (each validates).</b> The store-to-pre-init
 * {@code let x: int = (x = 1);} (stores are exempt — the rule covers
 * loads only); size-1 self-recursion; forward module-function body
 * references; group-member body loads (the publication arm);
 * parameter/catch/{@code FOR_EACH} entry-transfer captures (arm 2 at
 * the creation site); nested size-1 self-recursion (the own-name arm
 * along the chain); the doubly-nested capture shape of
 * {@code test/conformance/backend-runtime/closures/nested-closure-mutation.deal}
 * (creation-site dominance transitively along the detaching chain —
 * the equivalent chain over declared functions, the fixture's runtime
 * constructs being outside this walk's window); structured
 * child-block loads of ancestor bindings (R1); thunk-block captures of
 * closures created inside thunks (R3 with the chain closing at the
 * {@code FUNCTION_ADAPT} creation site); the for-let counter's
 * generation-0 condition/update/body-top references under the
 * intra-{@code LOOP} init→condition→body→update sequencing (arm 1);
 * default-block module-level references (R4's module-level arm,
 * unit-level — source-level {@code CLASS_DEFAULT} production is
 * ISSUE-0238's); VALUE-over-proof single loads (arm 1); and the
 * combined all-three-modes corpus over the earlier children's
 * production.</p>
 *
 * <p><b>Negative corpus (each fails with exactly one E6005 naming the
 * rule).</b> {@code let x: int = x;} and the
 * closure-capturing-own-initializer shape (INIT_DOMINATES_LOAD);
 * stale generations (BINDING_GENERATION_RESOLUTION); capture chains
 * closing with zero or multiple producing allocations and detached
 * free references outside {@code captures}/{@code capturedBindings}
 * (CAPTURE_RESOLUTION); group-shape violations (GROUP_SHAPE); exact or
 * non-assignable adapter pairs (ADAPTER_PAIR); mode/source shape
 * mismatches, VALUE-over-binding without its proof, and a proof
 * naming the wrong binding/generation (ADAPTER_SOURCE_SHAPE);
 * duplicate/missing/orphan registry entries including the
 * host/external seam and {@code HostFunctionValue} registrations
 * (REGISTRY_ONE_TO_ONE; the function-typed-result-without-binding
 * rejection stays R-FUNCTION-BINDING at the schema, which keeps
 * running on both surfaces); and an adapter result wired into a
 * non-position boundary op (NO_ADAPTER_AT_BOUNDARY).</p>
 *
 * <p><b>Boundary-scope discipline.</b> The {@code ADAPTER_PAIR} tests
 * assert pair-level assignability only: the closed function-signature
 * predicates (exact equality and the arity-extension assignability
 * over {@code RuntimeDescriptor.Func}) re-derive the pair — they never
 * produce, execute, or claim a boundary check. No fixture in this
 * class calls a boundary realization, so this child's suites contain
 * no executed boundary check (the executed {@code FUNCTION_SIGNATURE}
 * E8010 is E4's boundary machinery, exercised by the integration
 * child).</p>
 *
 * <p><b>Cell-kind invariant.</b> {@code deriveCellKinds} — the closed
 * B2 iff over the union of the three capture reference sets plus the
 * pinned special cases — is asserted against every emitted
 * {@code BINDING_ALLOC} payload of the full positive corpus; a unit
 * violating the complete iff fails the assertion (the closed
 * 14-condition schema validator stays unchanged).</p>
 *
 * <p><b>Determinism.</b> The same checked module lowers repeatedly to
 * byte-identical {@code deal.semantic-ir/1} dump text.</p>
 */
public class BindingsValidationTest {

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
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new deal.semantic.ir.ExternalModuleInterface(MODULE,
                deal.semantic.ir.ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(),
                deal.semantic.ir.InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Source-level driver (the validation entry point)
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(),
            "the slice checks cleanly: " + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    private static SemanticLowerer.ValidationCoreResult lowerSlice(String source) {
        CheckedSlice slice = checkSlice(source);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleValidationCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /** A lowered, schema/chain/control-flow/B9-validated unit for the named test. */
    private static SemanticLowerer.ValidationCoreResult validatedResult(String source,
                                                                        String what) {
        SemanticLowerer.ValidationCoreResult result = lowerSlice(source);
        if (result == null) {
            return null;
        }
        check(result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers to a B9-validated unit: "
                + (result.lowering() == null ? "null" : result.lowering().diagnostics()));
        if (result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    private static void assertE6005(SemanticLowerer.ValidationCoreResult result, String rule,
                                    String what) {
        check(result != null, what + " lowers (the production-time check is the rejecting "
            + "authority)");
        if (result == null) {
            return;
        }
        check(result.lowering() != null && result.lowering().hasErrors(),
            what + " is rejected with E6005");
        if (result.lowering() == null || !result.lowering().hasErrors()) {
            return;
        }
        List<CompilerDiagnostic> diagnostics = result.lowering().diagnostics();
        check(diagnostics.size() == 1, what + " produces exactly one diagnostic; got "
            + diagnostics.size());
        for (CompilerDiagnostic diagnostic : diagnostics) {
            check("E6005".equals(diagnostic.code()), what + " diagnostic code is E6005");
            check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
                what + " diagnosticCode is E6005");
            check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
                what + " phase is BACKEND_LOWERING");
            String message = diagnostic.message();
            check(message.startsWith("Common semantic lowering failed"),
                what + " message instantiates the registry-owned E6005 template");
            String[] byRule = message.split("validatorRule ");
            check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
                what + " is named as the validator rule " + rule + " (exactly one rule "
                    + "per fixture); got \"" + message + "\"");
            check(message.contains("capability BINDINGS"),
                what + " message carries capability BINDINGS");
            check(message.contains("deal.semantic-ir/1"),
                what + " message carries the IR version");
            check(message.contains("BindingsProductionValidator " + rule),
                what + " message carries the BindingsProductionValidator origin");
        }
    }

    // =========================================================================
    // IR-level synthetic fixtures (the SemanticIrValidatorTest discipline)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.binding");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor.Func SIG0 =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);
    private static final RuntimeDescriptor.Func SIG1 = new RuntimeDescriptor.Func(
        List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Null.INSTANCE);
    private static final RuntimeDescriptor.Func SIG2 = new RuntimeDescriptor.Func(
        List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
        RuntimeDescriptor.Null.INSTANCE);

    private static final BlockId INIT_BLOCK = new BlockId(0);

    private static int nextOp = 1;
    private static int nextVal = 1;
    private static int nextBinding = 1;
    private static int nextFunction = 1;
    private static int nextBlock = 100;
    private static int nextIdentity = 1000;

    private static OpId nextOpId() {
        return new OpId(MOD, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static BindingId nextBindingId() {
        return new BindingId(nextBinding++);
    }

    private static FunctionId nextFunctionId() {
        return new FunctionId(nextFunction++);
    }

    private static BlockId nextBlock() {
        return new BlockId(nextBlock++);
    }

    private static FunctionAllocationIdentity nextIdentity() {
        return new FunctionAllocationIdentity(nextIdentity++);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin("test.deal", SourceSpan.synthetic("test.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            List<ValueId> operands, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, operandTypes, policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, operandTypes, policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, operands,
            operandTypes, payload, policy, contract);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        return opWith(nextOpId(), kind, payload, result, resultType, List.of(), List.of(),
            policy, parent);
    }

    private static SemanticOp opWithOperand(SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, ValueId operand,
            RuntimeDescriptor operandType, FailurePolicyId policy, OpId parent) {
        return opWith(nextOpId(), kind, payload, result, resultType, List.of(operandType),
            List.of(operand), policy, parent);
    }

    private static SemanticOp constInt() {
        return op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp allocOp(BindingId binding, BlockId scope, long generation) {
        return op(SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(binding, scope, true, BindingCellKind.DIRECT,
                generation),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp initOp(BindingId binding, long generation, ValueId value) {
        return op(SemanticOpKind.BINDING_INIT,
            new KindPayload.BindingInitPayload(binding, generation, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp loadOp(BindingId binding, long generation) {
        return op(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(binding, generation),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp functionLoadOp(BindingId binding, long generation) {
        return op(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(binding, generation),
            nextValue(), SIG0, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp storeOp(BindingId binding, long generation, ValueId value) {
        return op(SemanticOpKind.BINDING_STORE,
            new KindPayload.BindingStorePayload(binding, generation, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    /** The generation-0-pinned capture entries of one hand-built seed. */
    private static List<BindingGeneration> pins(BindingId... bindings) {
        List<BindingGeneration> entries = new java.util.ArrayList<>();
        for (BindingId binding : bindings) {
            entries.add(new BindingGeneration(binding, 0));
        }
        return entries;
    }

    private static SemanticOp closureNewOp(FunctionId function, RuntimeDescriptor.Func signature,
            List<BindingGeneration> captures, BlockId body, ValueId result) {
        return op(SemanticOpKind.CLOSURE_NEW,
            new KindPayload.ClosureNewPayload(function, signature, captures,
                new FunctionExecutionBinding.LoweredBody(function, body)),
            result, signature, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp groupOp(List<BindingId> bindings, List<FunctionId> functions) {
        return op(SemanticOpKind.RECURSIVE_GROUP_INIT,
            new KindPayload.RecursiveGroupInitPayload(bindings, functions),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp adaptOp(CaptureMode mode, AdaptSourceRef source,
            RuntimeDescriptor.Func sourceSignature, RuntimeDescriptor.Func targetSignature,
            BindingImmutabilityProof proof, List<ValueId> operands,
            List<RuntimeDescriptor> operandTypes, ValueId result) {
        return opWith(nextOpId(), SemanticOpKind.FUNCTION_ADAPT,
            new KindPayload.FunctionAdaptPayload(sourceSignature, targetSignature, mode, source,
                proof),
            result, targetSignature, operandTypes, operands,
            FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp forEachOp(BindingId binding, long generation, BlockId body) {
        return op(SemanticOpKind.FOR_EACH,
            new KindPayload.ForEachPayload(deal.semantic.ir.IterationMode.STRING_SCALARS,
                nextValue(), binding, generation, body),
            null, null, FailurePolicyId.TYPE_DESCRIPTOR, null);
    }

    private static SemanticOp tryCatchOp(BlockId tryBlock, BindingId catchBinding,
            BlockId catchBlock) {
        return op(SemanticOpKind.TRY_CATCH,
            new KindPayload.TryCatchPayload(tryBlock, catchBinding, catchBlock),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp branchOp(BlockId selected, BlockId alternate) {
        return op(SemanticOpKind.BRANCH,
            new KindPayload.BranchPayload(deal.semantic.ir.ControlSelector.IF, nextValue(),
                selected, alternate),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp loopOp(BlockId init, ValueId condition, BlockId body,
            BlockId update) {
        return op(SemanticOpKind.LOOP,
            new KindPayload.LoopPayload(deal.semantic.ir.ControlSelector.FOR, init,
                condition, body, update),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    /**
     * The IR-level for-let header fixture blocks: the LOOP op in the
     * enclosing block, the counter's generation-0 ALLOC/INIT and the
     * first condition production in the init block, the generation-1
     * per-iteration ALLOC/INIT in the body block, and a closure
     * capturing the counter plus the condition re-production in the
     * update block (C-D4 placement; B1's two-incarnation shape).
     */
    private record ForLetHeaderFixture(LoweredModuleUnit unit,
                                       StructuredBodyTable table,
                                       BindingId counter,
                                       BlockId loopInit) {
    }

    /** Builds the update-block-capture fixture with the given closure-body load generation. */
    private static ForLetHeaderFixture forLetHeaderFixture(long closureBodyGeneration) {
        BindingId counter = nextBindingId();
        BlockId loopInit = nextBlock();
        BlockId loopBody = nextBlock();
        BlockId loopUpdate = nextBlock();
        BlockId closureBody = nextBlock();
        FunctionId closureFn = nextFunctionId();
        ValueId closureIdentity = nextValue();
        ValueId conditionFirst = nextValue();
        ValueId conditionRepro = nextValue();
        SemanticOp alloc0 = allocOp(counter, loopInit, 0);
        // The generation-0 INIT's operand is produced inside the unit (the
        // initializer's value; REGISTRY_ONE_TO_ONE admits a producer-less
        // init operand only under the intrinsic seed registrations).
        SemanticOp init0Value = constInt();
        SemanticOp init0 = initOp(counter, 0, (ValueId) init0Value.result());
        SemanticOp condition1 = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(counter, 0),
            conditionFirst, INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp loop = loopOp(loopInit, conditionFirst, loopBody, loopUpdate);
        SemanticOp alloc1 = allocOp(counter, loopBody, 1);
        SemanticOp init1Value = constInt();
        SemanticOp init1 = initOp(counter, 1, (ValueId) init1Value.result());
        SemanticOp closure = closureNewOp(closureFn, SIG0, pins(counter), closureBody,
            closureIdentity);
        SemanticOp condition2 = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(counter, 0),
            conditionRepro, INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp loadInBody = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(counter, closureBodyGeneration),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unit = unit(
            Map.of(closureFn, function(closureFn, SIG0, pins(counter), closureBody)),
            Map.of(new FunctionAllocationIdentity(closureIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(closureFn, closureBody)),
            List.of(loop, alloc0, init0Value, init0, condition1, alloc1, init1Value, init1,
                closure, condition2, loadInBody));
        StructuredBodyTable table = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(loop)),
            Map.entry(loopInit, List.of(alloc0, init0Value, init0, condition1)),
            Map.entry(loopBody, List.of(alloc1, init1Value, init1)),
            Map.entry(loopUpdate, List.of(closure, condition2)),
            Map.entry(closureBody, List.of(loadInBody))));
        return new ForLetHeaderFixture(unit, table, counter, loopInit);
    }

    private static SemanticOp boundaryOp(BoundaryKind kind, RuntimeDescriptor descriptor,
            ValueId input) {
        return op(SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, input,
                new BoundaryRealization.RuntimeValidation("runtime-validation")),
            null, null, descriptor instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR, null);
    }

    private static SemanticOp moduleImportOp(BindingId... aliasCells) {
        return op(SemanticOpKind.MODULE_IMPORT,
            new KindPayload.ModuleImportPayload("lib.math", new ModuleId("lib.math"),
                deal.semantic.ir.ModuleImportKind.COMPILED, List.of(aliasCells)),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp classDefaultOp(BlockId defaultBlock) {
        return op(SemanticOpKind.CLASS_DEFAULT,
            new KindPayload.ClassDefaultPayload(new ClassId("mod.binding", "C"), "handler",
                defaultBlock),
            nextValue(), SIG1, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static LoweredFunction function(FunctionId id, RuntimeDescriptor.Func signature,
            List<BindingGeneration> captures, BlockId body) {
        return new LoweredFunction(id, signature, captures, body);
    }

    private static LoweredModuleUnit unit(Map<FunctionId, LoweredFunction> functions,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, LCH, Set.of(), Map.of(), Map.of(),
            functions, new ModuleInitPlan(List.of(), INIT_BLOCK), ExportPlan.empty(), registry,
            ops);
    }

    /** Builds a table from block → ops and derives the exact inverse map. */
    private static StructuredBodyTable tableOf(Map<BlockId, List<SemanticOp>> blocks) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<SemanticOp>> entry : blocks.entrySet()) {
            List<OpId> ids = new ArrayList<>();
            for (SemanticOp op : entry.getValue()) {
                ids.add(op.opId());
                opBlocks.put(op.opId(), entry.getKey());
            }
            blockOps.put(entry.getKey(), ids);
        }
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    private static void assertPass(Optional<CompilerDiagnostic> diagnostic, String what) {
        check(diagnostic.isEmpty(), what + " passes validation"
            + (diagnostic.isPresent() ? ": " + diagnostic.get().message() : ""));
    }

    private static void assertE6005(Optional<CompilerDiagnostic> diagnostic, String rule,
            String what, String... contains) {
        check(diagnostic.isPresent(), what + " is rejected with E6005 " + rule);
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()), what + " diagnostic code is E6005");
        check(d.diagnosticCode() == DiagnosticCode.E6005, what + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            what + " phase is BACKEND_LOWERING");
        String message = d.message();
        check(message.startsWith("Common semantic lowering failed"),
            what + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the validator rule " + rule + " (exactly one rule per "
                + "fixture); got \"" + message + "\"");
        check(message.contains("capability BINDINGS"),
            what + " message carries capability BINDINGS");
        check(message.contains("deal.semantic-ir/1"), what + " message carries the IR version");
        check(message.contains("mod.binding"), what + " message carries the module path");
        check(message.contains("BindingsProductionValidator " + rule),
            what + " message carries the BindingsProductionValidator origin");
        for (String c : contains) {
            check(message.contains(c), what + " message contains \"" + c + "\"; got \""
                + message + "\"");
        }
    }

    // =========================================================================
    // 1. Surface and rule-name contract
    // =========================================================================

    private static void testSurfaceAndRules() {
        System.out.println("-- surface and pinned rule names --");

        check(BindingsProductionValidator.GROUP_SHAPE.equals("GROUP_SHAPE"),
            "GROUP_SHAPE rule name is pinned");
        check(BindingsProductionValidator.CAPTURE_RESOLUTION.equals("CAPTURE_RESOLUTION"),
            "CAPTURE_RESOLUTION rule name is pinned");
        check(BindingsProductionValidator.BINDING_GENERATION_RESOLUTION
                .equals("BINDING_GENERATION_RESOLUTION"),
            "BINDING_GENERATION_RESOLUTION rule name is pinned");
        check(BindingsProductionValidator.BINDING_INIT_ONCE.equals("BINDING_INIT_ONCE"),
            "BINDING_INIT_ONCE rule name is pinned");
        check(BindingsProductionValidator.INIT_DOMINATES_LOAD.equals("INIT_DOMINATES_LOAD"),
            "INIT_DOMINATES_LOAD rule name is pinned");
        check(BindingsProductionValidator.ADAPTER_PAIR.equals("ADAPTER_PAIR"),
            "ADAPTER_PAIR rule name is pinned");
        check(BindingsProductionValidator.ADAPTER_SOURCE_SHAPE.equals("ADAPTER_SOURCE_SHAPE"),
            "ADAPTER_SOURCE_SHAPE rule name is pinned");
        check(BindingsProductionValidator.REGISTRY_ONE_TO_ONE.equals("REGISTRY_ONE_TO_ONE"),
            "REGISTRY_ONE_TO_ONE rule name is pinned");
        check(BindingsProductionValidator.NO_ADAPTER_AT_BOUNDARY
                .equals("NO_ADAPTER_AT_BOUNDARY"),
            "NO_ADAPTER_AT_BOUNDARY rule name is pinned");

        expectNpe(() -> BindingsProductionValidator.validate(null, tableOf(Map.of())),
            "validate with a null unit");
        expectNpe(() -> BindingsProductionValidator.validate(
                unit(Map.of(), Map.of(), List.of()), null),
            "validate with a null table");

        // Purity and determinism: repeated validation of the same inputs
        // yields the identical outcome.
        SemanticOp x = constInt();
        LoweredModuleUnit simple = unit(Map.of(), Map.of(), List.of(x));
        StructuredBodyTable table = tableOf(Map.of(INIT_BLOCK, List.of(x)));
        Optional<CompilerDiagnostic> first = BindingsProductionValidator.validate(simple, table);
        Optional<CompilerDiagnostic> second = BindingsProductionValidator.validate(simple, table);
        check(first.equals(second), "repeated validation of the same unit is identical");
    }

    private static void expectNpe(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected NullPointerException for " + what + ", but no exception was raised");
        } catch (NullPointerException expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected NullPointerException for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    // =========================================================================
    // 2. Source-level positive corpus (each must validate)
    // =========================================================================

    private static void testSourceLevelPositives() {
        System.out.println("-- source-level positive corpus (each must validate) --");

        // (a) The store-to-pre-init shape: stores are exempt from
        // INIT_DOMINATES_LOAD — the store commits the assigned value and
        // the INIT then commits the initializer's result; no uninitialized
        // read occurs.
        validatedResult("let x: int = (x = 1);",
            "(a) the checker-admitted store-to-pre-init shape");

        // (b) Size-1 self-recursion: the own-name arm (INIT is the
        // immediate commit after CLOSURE_NEW).
        validatedResult("function f(): null { let g: () => null = f; }",
            "(b) size-1 self-recursion");

        // (c) Forward module-function body references: the
        // module-init-completion arm.
        validatedResult("""
            function first(): null { let h: () => null = laterFn; }
            function laterFn(): null {}
            """,
            "(c) forward module-function body references");

        // (d) Group-member body loads: the group-publication arm; member
        // cells are SHARED_CELL with no separate ALLOC/INIT.
        validatedResult("""
            function even(): null { let oddRef: () => null = odd; }
            function odd(): null { let evenRef: () => null = even; }
            """,
            "(d) group-member body loads");

        // (e) The one-level parameter capture: the parameter-transfer
        // entry dominates the closure creation (arm 2 at the creation
        // site).
        validatedResult("""
            function f(p: int): null {
              let g: () => null = function(): null { let read: int = p; };
            }
            """,
            "(e) the one-level parameter capture");

        // (f) The catch-binding capture: the catch-entry transfer
        // dominates the closure created in the catch block.
        validatedResult("""
            function f(): null {
              try { let t = 1; }
              catch (e) { let g: () => null = function(): null { let copy = e; }; }
            }
            """,
            "(f) the catch-binding capture");

        // (g) The FOR_EACH iteration-binding capture: the FOR_EACH
        // per-iteration transfer dominates its body block through the
        // structured edge.
        validatedResult("""
            function f(): null {
              for (let c: string of "ab") {
                let g: () => null = function(): null { let read: string = c; };
              }
            }
            """,
            "(g) the FOR_EACH iteration-binding capture");

        // (h) Nested size-1 self-recursion: the own-name arm along the
        // detaching chain.
        validatedResult("""
            function outer(): null {
              function g(): null { let copy: () => null = g; }
            }
            """,
            "(h) nested size-1 self-recursion");

        // (i) The doubly-nested capture chain pinned by
        // test/conformance/backend-runtime/closures/nested-closure-mutation.deal
        // (runtime-ok across luajit/jvm/js): x's INIT in t's body
        // dominates make's creation; the chain closes in t's body region
        // (creation-site dominance transitively along the detaching
        // chain). The fixture's call/return/throw constructs are outside
        // this walk's window, so the equivalent chain over declared
        // functions pins the same resolution shape.
        validatedResult("""
            function t(): null {
              let x: int = 1;
              function make(): null {
                let inner: () => null = function(): null { let read: int = x; };
              }
            }
            """,
            "(i) the doubly-nested nested-closure-mutation capture chain");

        // (j) Structured child-block loads of ancestor bindings (R1):
        // loads in the try and catch blocks resolve the ancestor ALLOC
        // through the structured edges and are dominated by its INIT.
        validatedResult("""
            function f(): null {
              let x = 1;
              try { let t = x; } catch (e) { let y = x; }
            }
            """,
            "(j) structured child-block loads of ancestor bindings");

        // (k) Thunk-block captures of closures created inside thunks:
        // the inner closure's capture resolves through the thunk's
        // pinned capturedBindings and the chain closes at the
        // FUNCTION_ADAPT creation site (R3).
        validatedResult("""
            function main(): null {
              let x = 1;
              let s: () => null = function(): null { let read: int = x; };
              let k: (a: int, b: int) => null = (s = function(): null { let read2: int = x; });
            }
            """,
            "(k) thunk-block captures of closures created inside thunks");

        // (l) The for-let counter's generation-0 condition/update/
        // body-top references under the intra-LOOP init→condition→body→
        // update sequencing (arm 1).
        validatedResult("for (let i = 0; i < 3; i = i + 1) { let j = i; }",
            "(l) the for-let counter's generation-0 references");

        // (l2) The for-let per-iteration capture: body-created closures
        // resolve the generation-1 incarnation (the body-top ALLOC/INIT
        // dominate the closure creation under the intra-LOOP sequencing).
        validatedResult("""
            function f(): null {
              for (let i = 0; i < 3; i = i + 1) {
                let g: () => null = function(): null { let read: int = i; };
              }
            }
            """,
            "(l2) the for-let per-iteration closure capture");

        // (m) VALUE-over-proof single loads: the proved binding's INIT
        // precedes the load at the adaptation position (arm 1).
        validatedResult("""
            function main(): null {
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
            }
            function inner(x: int): null {}
            """,
            "(m) VALUE-over-proof single loads");
    }

    // =========================================================================
    // 3. Source-level negatives
    // =========================================================================

    private static void testSourceLevelNegatives() {
        System.out.println("-- source-level negatives (each fails with E6005 naming the rule) --");

        // The checker-admitted self-read: the load is dominated only by
        // the producing ALLOC — an uninitialized cell read.
        assertE6005(lowerSlice("let x: int = x;"), "INIT_DOMINATES_LOAD",
            "the self-read let x: int = x;");
    }

    // =========================================================================
    // 4. IR-level negatives
    // =========================================================================

    private static void testIrLevelNegatives() {
        System.out.println("-- IR-level negatives (each fails with E6005 naming the rule) --");

        testInitDominatesLoadNegative();
        testStaleGenerationNegatives();
        testCaptureResolutionNegatives();
        testGroupShapeNegatives();
        testAdapterPairNegatives();
        testAdapterSourceShapeNegatives();
        testRegistryOneToOneNegatives();
        testNoAdapterAtBoundaryNegative();
        testBindingInitOnceNegatives();
    }

    /**
     * The closure-capturing-own-initializer shape of
     * {@code let x: int = g(() => x);}: the closure is created inside
     * x's initializer before INIT(x) commits, so the load would read an
     * uninitialized cell — the chain's closing step fails arm 2.
     */
    private static void testInitDominatesLoadNegative() {
        // The enclosing function F with its name binding.
        BindingId fBinding = nextBindingId();
        FunctionId fFunction = nextFunctionId();
        BlockId fBody = nextBlock();
        ValueId fIdentity = nextValue();
        // x's declaration and the capturing closure inside F's body.
        BindingId xBinding = nextBindingId();
        FunctionId closureFunction = nextFunctionId();
        BlockId closureBody = nextBlock();
        ValueId closureIdentity = nextValue();
        ValueId constValue = nextValue();
        SemanticOp allocF = allocOp(fBinding, INIT_BLOCK, 0);
        SemanticOp closureF = closureNewOp(fFunction, SIG0, List.of(), fBody, fIdentity);
        SemanticOp initF = initOp(fBinding, 0, fIdentity);
        SemanticOp allocX = allocOp(xBinding, fBody, 0);
        SemanticOp captureClosure = closureNewOp(closureFunction, SIG0, pins(xBinding),
            closureBody, closureIdentity);
        SemanticOp filler = op(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            constValue, INT, FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp initX = initOp(xBinding, 0, constValue);
        SemanticOp loadX = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(xBinding, 0),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unit = unit(
            Map.of(fFunction, function(fFunction, SIG0, List.of(), fBody),
                closureFunction, function(closureFunction, SIG0, pins(xBinding),
                    closureBody)),
            Map.of(new FunctionAllocationIdentity(fIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(fFunction, fBody),
                new FunctionAllocationIdentity(closureIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(closureFunction, closureBody)),
            List.of(allocF, closureF, initF, allocX, captureClosure, filler, initX, loadX));
        StructuredBodyTable table = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(allocF, closureF, initF)),
            Map.entry(fBody, List.of(allocX, captureClosure, filler, initX)),
            Map.entry(closureBody, List.of(loadX))));
        assertE6005(BindingsProductionValidator.validate(unit, table), "INIT_DOMINATES_LOAD",
            "the closure-capturing-own-initializer shape", "not dominated by");
    }

    private static void testStaleGenerationNegatives() {
        // A stale generation: the load names a generation no producing
        // allocation carries.
        BindingId x = nextBindingId();
        ValueId constValue = nextValue();
        SemanticOp alloc = allocOp(x, INIT_BLOCK, 0);
        SemanticOp init = initOp(x, 0, constValue);
        SemanticOp stale = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(x, 5),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unit = unit(Map.of(), Map.of(),
            List.of(alloc, init, stale));
        StructuredBodyTable table = tableOf(Map.of(INIT_BLOCK, List.of(alloc, init, stale)));
        assertE6005(BindingsProductionValidator.validate(unit, table),
            "BINDING_GENERATION_RESOLUTION", "a stale-generation load",
            "stale/unresolvable");

        // A stale store generation is the same rule (stores are exempt
        // only from INIT_DOMINATES_LOAD, never from generation
        // resolution).
        BindingId y = nextBindingId();
        SemanticOp allocY = allocOp(y, INIT_BLOCK, 0);
        SemanticOp initY = initOp(y, 0, nextValue());
        SemanticOp staleStore = op(SemanticOpKind.BINDING_STORE,
            new KindPayload.BindingStorePayload(y, 7, nextValue()),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unitY = unit(Map.of(), Map.of(),
            List.of(allocY, initY, staleStore));
        StructuredBodyTable tableY = tableOf(Map.of(INIT_BLOCK,
            List.of(allocY, initY, staleStore)));
        assertE6005(BindingsProductionValidator.validate(unitY, tableY),
            "BINDING_GENERATION_RESOLUTION", "a stale-generation store",
            "stale/unresolvable");

        // Generation equality at every chain step: a closure created in
        // the for-let update block captures the counter, which resolves
        // to the generation-0 incarnation at header sites (B1/B2 — the
        // per-iteration generation-1 incarnation is out of lexical
        // scope there), so a closure body load naming generation 1 is
        // stale/unresolvable.
        ForLetHeaderFixture staleCapture = forLetHeaderFixture(1L);
        assertE6005(BindingsProductionValidator.validate(staleCapture.unit(),
                staleCapture.table()),
            "BINDING_GENERATION_RESOLUTION",
            "an update-block capture whose closure body names the generation-1 "
                + "incarnation",
            "stale/unresolvable");
    }

    private static void testCaptureResolutionNegatives() {
        // A capture chain closing with zero producing allocations: the
        // capture names a binding with no producing allocation anywhere.
        BindingId ghost = nextBindingId();
        FunctionId fn = nextFunctionId();
        BlockId body = nextBlock();
        LoweredModuleUnit unit = unit(
            Map.of(fn, function(fn, SIG0, pins(ghost), body)),
            Map.of(), List.of());
        StructuredBodyTable table = tableOf(Map.of(INIT_BLOCK, List.of(),
            body, List.of()));
        assertE6005(BindingsProductionValidator.validate(unit, table), "CAPTURE_RESOLUTION",
            "a capture chain closing with zero producing allocations");

        // A capture chain closing with multiple producing allocations:
        // two ALLOCs of one binding in two sibling BRANCH arms, both
        // visible at the closure's creation site after the branch.
        BindingId ambiguous = nextBindingId();
        FunctionId closureFn = nextFunctionId();
        BlockId closureBody = nextBlock();
        BlockId arm1 = nextBlock();
        BlockId arm2 = nextBlock();
        ValueId identity = nextValue();
        SemanticOp alloc1 = allocOp(ambiguous, arm1, 0);
        SemanticOp alloc2 = allocOp(ambiguous, arm2, 0);
        SemanticOp branch = branchOp(arm1, arm2);
        SemanticOp closure = closureNewOp(closureFn, SIG0, pins(ambiguous), closureBody,
            identity);
        LoweredModuleUnit unitM = unit(
            Map.of(closureFn, function(closureFn, SIG0, pins(ambiguous), closureBody)),
            Map.of(new FunctionAllocationIdentity(identity.id()),
                new FunctionExecutionBinding.LoweredBody(closureFn, closureBody)),
            List.of(branch, closure, alloc1, alloc2));
        StructuredBodyTable tableM = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(branch, closure)),
            Map.entry(arm1, List.of(alloc1)),
            Map.entry(arm2, List.of(alloc2)),
            Map.entry(closureBody, List.of())));
        assertE6005(BindingsProductionValidator.validate(unitM, tableM), "CAPTURE_RESOLUTION",
            "a capture chain closing with multiple producing allocations");

        // A detached-body free reference outside the captures list.
        BindingId free = nextBindingId();
        FunctionId outer = nextFunctionId();
        BlockId outerBody = nextBlock();
        ValueId outerIdentity = nextValue();
        SemanticOp allocFree = allocOp(free, INIT_BLOCK, 0);
        SemanticOp initFree = initOp(free, 0, nextValue());
        SemanticOp closureOuter = closureNewOp(outer, SIG0, List.of(), outerBody,
            outerIdentity);
        SemanticOp loadFree = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(free, 0),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unitF = unit(
            Map.of(outer, function(outer, SIG0, List.of(), outerBody)),
            Map.of(new FunctionAllocationIdentity(outerIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(outer, outerBody)),
            List.of(allocFree, initFree, closureOuter, loadFree));
        StructuredBodyTable tableF = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(allocFree, initFree, closureOuter)),
            Map.entry(outerBody, List.of(loadFree))));
        assertE6005(BindingsProductionValidator.validate(unitF, tableF), "CAPTURE_RESOLUTION",
            "a detached-body free reference outside the captures list",
            "outside the captures");

        // A thunk-block free reference outside the pinned
        // capturedBindings.
        BindingId thunkFree = nextBindingId();
        BlockId thunkBlock = nextBlock();
        ValueId adapterResult = nextValue();
        SemanticOp allocThunkFree = allocOp(thunkFree, INIT_BLOCK, 0);
        SemanticOp initThunkFree = initOp(thunkFree, 0, nextValue());
        SemanticOp thunkLoad = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(thunkFree, 0),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp adapt = adaptOp(CaptureMode.REEVALUATE_THUNK,
            new AdaptSourceRef.Thunk(thunkBlock, List.of()),
            SIG0, SIG2, null, List.of(), List.of(), adapterResult);
        LoweredModuleUnit unitT = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult.id()),
                new FunctionExecutionBinding.AdapterBinding(adapt.opId(),
                    CaptureMode.REEVALUATE_THUNK, new AdaptSourceRef.Thunk(thunkBlock,
                        List.of()), SIG0, SIG2)),
            List.of(allocThunkFree, initThunkFree, adapt, thunkLoad));
        StructuredBodyTable tableT = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(allocThunkFree, initThunkFree, adapt)),
            Map.entry(thunkBlock, List.of(thunkLoad))));
        assertE6005(BindingsProductionValidator.validate(unitT, tableT), "CAPTURE_RESOLUTION",
            "a thunk-block free reference outside the pinned capturedBindings",
            "outside the pinned capturedBindings");
    }

    private static void testGroupShapeNegatives() {
        // An empty bindings list.
        FunctionId member = nextFunctionId();
        BlockId body = nextBlock();
        LoweredModuleUnit unitEmpty = unit(
            Map.of(member, function(member, SIG0, List.of(), body)),
            Map.of(nextIdentity(),
                new FunctionExecutionBinding.LoweredBody(member, body)),
            List.of(groupOp(List.of(), List.of(member))));
        StructuredBodyTable tableEmpty = tableOf(Map.of(INIT_BLOCK,
            List.of(groupOp(List.of(), List.of(member))), body, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitEmpty, tableEmpty), "GROUP_SHAPE",
            "an empty group bindings list");

        // A bindings/functions length mismatch.
        BindingId b1 = nextBindingId();
        FunctionId f1 = nextFunctionId();
        FunctionId f2 = nextFunctionId();
        BlockId b1Body = nextBlock();
        BlockId b2Body = nextBlock();
        LoweredModuleUnit unitMismatch = unit(
            Map.of(f1, function(f1, SIG0, List.of(), b1Body),
                f2, function(f2, SIG0, List.of(), b2Body)),
            Map.of(nextIdentity(),
                new FunctionExecutionBinding.LoweredBody(f1, b1Body),
                nextIdentity(),
                new FunctionExecutionBinding.LoweredBody(f2, b2Body)),
            List.of(groupOp(List.of(b1), List.of(f1, f2))));
        StructuredBodyTable tableMismatch = tableOf(Map.of(INIT_BLOCK,
            List.of(groupOp(List.of(b1), List.of(f1, f2))), b1Body, List.of(),
            b2Body, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitMismatch, tableMismatch),
            "GROUP_SHAPE", "a bindings/functions length mismatch");

        // A member binding with a separate ALLOC.
        BindingId b2 = nextBindingId();
        FunctionId f3 = nextFunctionId();
        BlockId b3Body = nextBlock();
        SemanticOp group = groupOp(List.of(b2), List.of(f3));
        SemanticOp rogueAlloc = allocOp(b2, INIT_BLOCK, 0);
        LoweredModuleUnit unitAlloc = unit(
            Map.of(f3, function(f3, SIG0, List.of(), b3Body)),
            Map.of(new FunctionAllocationIdentity(nextVal++),
                new FunctionExecutionBinding.LoweredBody(f3, b3Body)),
            List.of(group, rogueAlloc));
        StructuredBodyTable tableAlloc = tableOf(Map.of(INIT_BLOCK,
            List.of(group, rogueAlloc), b3Body, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitAlloc, tableAlloc), "GROUP_SHAPE",
            "a group member binding with a separate ALLOC", "separate BINDING_ALLOC");
    }

    private static void testAdapterPairNegatives() {
        // An exact pair: exact-signature positions store the value
        // directly — an exact pair is invalid IR for FUNCTION_ADAPT.
        BindingId x = nextBindingId();
        ValueId adapterResult = nextValue();
        SemanticOp alloc = allocOp(x, INIT_BLOCK, 0);
        SemanticOp init = initOp(x, 0, nextValue());
        SemanticOp exact = adaptOp(CaptureMode.SHARED_CELL,
            new AdaptSourceRef.SharedCell(x, 0), SIG1, SIG1, null, List.of(), List.of(),
            adapterResult);
        LoweredModuleUnit unitExact = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult.id()),
                new FunctionExecutionBinding.AdapterBinding(exact.opId(),
                    CaptureMode.SHARED_CELL, new AdaptSourceRef.SharedCell(x, 0), SIG1,
                    SIG1)),
            List.of(alloc, init, exact));
        StructuredBodyTable tableExact = tableOf(Map.of(INIT_BLOCK,
            List.of(alloc, init, exact)));
        assertE6005(BindingsProductionValidator.validate(unitExact, tableExact), "ADAPTER_PAIR",
            "an exact adapter pair (M == N)", "does not re-derive");

        // A non-assignable pair: M > N — the checker already rejects
        // such positions, and the IR-level rule re-derives the pair.
        BindingId y = nextBindingId();
        ValueId adapterResult2 = nextValue();
        SemanticOp allocY = allocOp(y, INIT_BLOCK, 0);
        SemanticOp initY = initOp(y, 0, nextValue());
        SemanticOp nonAssignable = adaptOp(CaptureMode.SHARED_CELL,
            new AdaptSourceRef.SharedCell(y, 0), SIG2, SIG1, null, List.of(), List.of(),
            adapterResult2);
        LoweredModuleUnit unitNon = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult2.id()),
                new FunctionExecutionBinding.AdapterBinding(nonAssignable.opId(),
                    CaptureMode.SHARED_CELL, new AdaptSourceRef.SharedCell(y, 0), SIG2,
                    SIG1)),
            List.of(allocY, initY, nonAssignable));
        StructuredBodyTable tableNon = tableOf(Map.of(INIT_BLOCK,
            List.of(allocY, initY, nonAssignable)));
        assertE6005(BindingsProductionValidator.validate(unitNon, tableNon), "ADAPTER_PAIR",
            "a non-assignable adapter pair (M > N)", "does not re-derive");

        // Boundary-scope discipline: the pair re-derivation is
        // pair-level only — these fixtures assert the predicate through
        // the validator's ADAPTER_PAIR rule and contain no boundary
        // realization, so no executed boundary check exists in this
        // suite (the executed FUNCTION_SIGNATURE E8010 is E4's
        // machinery, exercised by the integration child).
        check(true, "the ADAPTER_PAIR fixtures assert pair-level assignability only "
            + "(no boundary realization is produced or executed by this child)");
    }

    private static void testAdapterSourceShapeNegatives() {
        // A mode/source shape mismatch: SHARED_CELL carrying a Value.
        BindingId x = nextBindingId();
        ValueId operand = nextValue();
        ValueId adapterResult = nextValue();
        SemanticOp alloc = allocOp(x, INIT_BLOCK, 0);
        SemanticOp init = initOp(x, 0, operand);
        SemanticOp mismatch = adaptOp(CaptureMode.SHARED_CELL, new AdaptSourceRef.Value(operand),
            SIG1, SIG2, null, List.of(), List.of(), adapterResult);
        LoweredModuleUnit unitMismatch = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult.id()),
                new FunctionExecutionBinding.AdapterBinding(mismatch.opId(),
                    CaptureMode.SHARED_CELL, new AdaptSourceRef.Value(operand), SIG1,
                    SIG2)),
            List.of(alloc, init, mismatch));
        StructuredBodyTable tableMismatch = tableOf(Map.of(INIT_BLOCK,
            List.of(alloc, init, mismatch)));
        assertE6005(BindingsProductionValidator.validate(unitMismatch, tableMismatch),
            "ADAPTER_SOURCE_SHAPE", "a mode/source shape mismatch",
            "mode must match the source shape");

        // VALUE-over-binding without the proof: the operand is produced
        // by exactly one binding load (no closure re-publishes the
        // identity) and the payload carries no proof.
        BindingId b = nextBindingId();
        ValueId loadResult = nextValue();
        ValueId adapterResult2 = nextValue();
        SemanticOp allocB = allocOp(b, INIT_BLOCK, 0);
        SemanticOp initB = initOp(b, 0, nextValue());
        SemanticOp loadB = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(b, 0),
            loadResult, SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp unproved = adaptOp(CaptureMode.VALUE, new AdaptSourceRef.Value(loadResult),
            SIG1, SIG2, null, List.of(loadResult), List.of(SIG1), adapterResult2);
        LoweredModuleUnit unitUnproved = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult2.id()),
                new FunctionExecutionBinding.AdapterBinding(unproved.opId(),
                    CaptureMode.VALUE, new AdaptSourceRef.Value(loadResult), SIG1, SIG2)),
            List.of(allocB, initB, loadB, unproved));
        StructuredBodyTable tableUnproved = tableOf(Map.of(INIT_BLOCK,
            List.of(allocB, initB, loadB, unproved)));
        assertE6005(BindingsProductionValidator.validate(unitUnproved, tableUnproved),
            "ADAPTER_SOURCE_SHAPE", "VALUE-over-binding without its proof",
            "without its proof");

        // A proof naming the wrong binding/generation: the operand is
        // the load of {b, 0} but the proof names {other, 0}.
        BindingId b2 = nextBindingId();
        BindingId other = nextBindingId();
        ValueId loadResult2 = nextValue();
        ValueId adapterResult3 = nextValue();
        SemanticOp allocB2 = allocOp(b2, INIT_BLOCK, 0);
        SemanticOp initB2 = initOp(b2, 0, nextValue());
        SemanticOp allocOther = allocOp(other, INIT_BLOCK, 0);
        SemanticOp initOther = initOp(other, 0, nextValue());
        SemanticOp loadB2 = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(b2, 0),
            loadResult2, SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp wrongProof = adaptOp(CaptureMode.VALUE,
            new AdaptSourceRef.Value(loadResult2), SIG1, SIG2,
            new BindingImmutabilityProof(other, 0), List.of(loadResult2), List.of(SIG1),
            adapterResult3);
        LoweredModuleUnit unitWrong = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult3.id()),
                new FunctionExecutionBinding.AdapterBinding(wrongProof.opId(),
                    CaptureMode.VALUE, new AdaptSourceRef.Value(loadResult2), SIG1,
                    SIG2)),
            List.of(allocB2, initB2, allocOther, initOther, loadB2, wrongProof));
        StructuredBodyTable tableWrong = tableOf(Map.of(INIT_BLOCK,
            List.of(allocB2, initB2, allocOther, initOther, loadB2, wrongProof)));
        assertE6005(BindingsProductionValidator.validate(unitWrong, tableWrong),
            "ADAPTER_SOURCE_SHAPE", "a proof naming the wrong binding/generation",
            "naming no producing load");

        // A proof over a non-load operand: the operand is a CLOSURE_NEW
        // result but the payload carries a proof.
        BindingId b3 = nextBindingId();
        FunctionId fn = nextFunctionId();
        BlockId body = nextBlock();
        ValueId closureResult = nextValue();
        ValueId adapterResult4 = nextValue();
        SemanticOp allocB3 = allocOp(b3, INIT_BLOCK, 0);
        SemanticOp initB3 = initOp(b3, 0, nextValue());
        SemanticOp closure = closureNewOp(fn, SIG1, List.of(), body, closureResult);
        SemanticOp nonLoadProof = adaptOp(CaptureMode.VALUE,
            new AdaptSourceRef.Value(closureResult), SIG1, SIG2,
            new BindingImmutabilityProof(b3, 0), List.of(closureResult), List.of(SIG1),
            adapterResult4);
        LoweredModuleUnit unitNonLoad = unit(
            Map.of(fn, function(fn, SIG1, List.of(), body)),
            Map.of(new FunctionAllocationIdentity(closureResult.id()),
                new FunctionExecutionBinding.LoweredBody(fn, body),
                new FunctionAllocationIdentity(adapterResult4.id()),
                new FunctionExecutionBinding.AdapterBinding(nonLoadProof.opId(),
                    CaptureMode.VALUE, new AdaptSourceRef.Value(closureResult), SIG1,
                    SIG2)),
            List.of(allocB3, initB3, closure, nonLoadProof));
        StructuredBodyTable tableNonLoad = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(allocB3, initB3, closure, nonLoadProof)),
            Map.entry(body, List.of())));
        assertE6005(BindingsProductionValidator.validate(unitNonLoad, tableNonLoad),
            "ADAPTER_SOURCE_SHAPE", "a proof over a non-load operand",
            "proof over a non-load operand");
    }

    private static void testRegistryOneToOneNegatives() {
        // An orphan key: a registration no producing op publishes.
        FunctionId orphanFn = nextFunctionId();
        BlockId orphanBody = nextBlock();
        LoweredModuleUnit unitOrphan = unit(
            Map.of(orphanFn, function(orphanFn, SIG0, List.of(), orphanBody)),
            Map.of(nextIdentity(),
                new FunctionExecutionBinding.LoweredBody(orphanFn, orphanBody)),
            List.of());
        StructuredBodyTable tableOrphan = tableOf(Map.of(INIT_BLOCK, List.of(),
            orphanBody, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitOrphan, tableOrphan),
            "REGISTRY_ONE_TO_ONE", "an orphan registry key", "produced by 0");

        // A missing registration: a CLOSURE_NEW without a registry entry.
        FunctionId missingFn = nextFunctionId();
        BlockId missingBody = nextBlock();
        ValueId identity = nextValue();
        SemanticOp closure = closureNewOp(missingFn, SIG0, List.of(), missingBody, identity);
        LoweredModuleUnit unitMissing = unit(
            Map.of(missingFn, function(missingFn, SIG0, List.of(), missingBody)),
            Map.of(), List.of(closure));
        StructuredBodyTable tableMissing = tableOf(Map.of(INIT_BLOCK, List.of(closure),
            missingBody, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitMissing, tableMissing),
            "REGISTRY_ONE_TO_ONE", "a missing closure registration",
            "missing registration");

        // A duplicate production: two CLOSURE_NEW ops publish one
        // allocation identity with a single registration.
        FunctionId dupFn = nextFunctionId();
        BlockId dupBody = nextBlock();
        ValueId dupIdentity = nextValue();
        SemanticOp closureA = closureNewOp(dupFn, SIG0, List.of(), dupBody, dupIdentity);
        SemanticOp closureB = closureNewOp(dupFn, SIG0, List.of(), dupBody, dupIdentity);
        LoweredModuleUnit unitDup = unit(
            Map.of(dupFn, function(dupFn, SIG0, List.of(), dupBody)),
            Map.of(new FunctionAllocationIdentity(dupIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(dupFn, dupBody)),
            List.of(closureA, closureB));
        StructuredBodyTable tableDup = tableOf(Map.of(INIT_BLOCK,
            List.of(closureA, closureB), dupBody, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitDup, tableDup),
            "REGISTRY_ONE_TO_ONE", "a duplicate production of one key",
            "produced by 2");

        // A HostFunctionValue obligation missing at a HOST_TO_DEAL
        // function-typed boundary crossing.
        ValueId hostValue = nextValue();
        SemanticOp hostBoundary = boundaryOp(BoundaryKind.HOST_TO_DEAL, SIG1, hostValue);
        LoweredModuleUnit unitHost = unit(Map.of(), Map.of(), List.of(hostBoundary));
        StructuredBodyTable tableHost = tableOf(Map.of(INIT_BLOCK, List.of(hostBoundary)));
        assertE6005(BindingsProductionValidator.validate(unitHost, tableHost),
            "REGISTRY_ONE_TO_ONE", "a host-materialized function value without its "
                + "HostFunctionValue registration", "HostFunctionValue");

        // The host/external seam: an orphan HostFunction registration
        // (a registry key no import member read produces).
        LoweredModuleUnit unitOrphanHost = unit(Map.of(),
            Map.of(nextIdentity(),
                new FunctionExecutionBinding.HostFunction(new ModuleId("host"), "g", SIG1)),
            List.of());
        StructuredBodyTable tableOrphanHost = tableOf(Map.of(INIT_BLOCK, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitOrphanHost, tableOrphanHost),
            "REGISTRY_ONE_TO_ONE", "an orphan HostFunction registration",
            "produced by 0");

        // The host/external seam: an orphan ExternalFunction
        // registration (a registry key no export read produces).
        LoweredModuleUnit unitOrphanExternal = unit(Map.of(),
            Map.of(nextIdentity(),
                new FunctionExecutionBinding.ExternalFunction(new ModuleId("lib.math"),
                    "g", SIG1, deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY)),
            List.of());
        StructuredBodyTable tableOrphanExternal = tableOf(Map.of(INIT_BLOCK, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitOrphanExternal,
                tableOrphanExternal),
            "REGISTRY_ONE_TO_ONE", "an orphan ExternalFunction registration",
            "produced by 0");

        // The host/external seam: a duplicate production — two import
        // member reads publishing one HostFunction key.
        ValueId readIdentity = nextValue();
        SemanticOp memberReadA = opWith(nextOpId(), SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(nextValue(), "g"),
            readIdentity, SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            null);
        SemanticOp memberReadB = opWith(nextOpId(), SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(nextValue(), "g"),
            readIdentity, SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            null);
        LoweredModuleUnit unitDupRead = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(readIdentity.id()),
                new FunctionExecutionBinding.HostFunction(new ModuleId("host"), "g", SIG1)),
            List.of(memberReadA, memberReadB));
        StructuredBodyTable tableDupRead = tableOf(Map.of(INIT_BLOCK,
            List.of(memberReadA, memberReadB)));
        assertE6005(BindingsProductionValidator.validate(unitDupRead, tableDupRead),
            "REGISTRY_ONE_TO_ONE", "a duplicate import member-read production of one "
                + "HostFunction key", "produced by 2");

        // The host/external seam: a duplicate production — two export
        // reads publishing one ExternalFunction key.
        ValueId exportIdentity = nextValue();
        SemanticOp exportReadA = opWith(nextOpId(), SemanticOpKind.EXPORT_READ,
            new KindPayload.ExportReadPayload(new ModuleId("lib.math"), "g", SIG1,
                exportIdentity),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp exportReadB = opWith(nextOpId(), SemanticOpKind.EXPORT_READ,
            new KindPayload.ExportReadPayload(new ModuleId("lib.math"), "g", SIG1,
                exportIdentity),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unitDupExport = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(exportIdentity.id()),
                new FunctionExecutionBinding.ExternalFunction(new ModuleId("lib.math"),
                    "g", SIG1, deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY)),
            List.of(exportReadA, exportReadB));
        StructuredBodyTable tableDupExport = tableOf(Map.of(INIT_BLOCK,
            List.of(exportReadA, exportReadB)));
        assertE6005(BindingsProductionValidator.validate(unitDupExport, tableDupExport),
            "REGISTRY_ONE_TO_ONE", "a duplicate export-read production of one "
                + "ExternalFunction key", "produced by 2");
    }

    private static void testNoAdapterAtBoundaryNegative() {
        // An adapter result wired directly into a non-position boundary
        // op (a function return): typed boundary positions never adapt.
        BindingId x = nextBindingId();
        ValueId adapterResult = nextValue();
        SemanticOp alloc = allocOp(x, INIT_BLOCK, 0);
        SemanticOp initValue = constInt();
        SemanticOp init = initOp(x, 0, (ValueId) initValue.result());
        SemanticOp adapt = adaptOp(CaptureMode.SHARED_CELL,
            new AdaptSourceRef.SharedCell(x, 0), SIG1, SIG2, null, List.of(), List.of(),
            adapterResult);
        SemanticOp returnBoundary = boundaryOp(BoundaryKind.FUNCTION_RETURN, SIG2,
            adapterResult);
        LoweredModuleUnit unit = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(adapterResult.id()),
                new FunctionExecutionBinding.AdapterBinding(adapt.opId(),
                    CaptureMode.SHARED_CELL, new AdaptSourceRef.SharedCell(x, 0), SIG1,
                    SIG2)),
            List.of(alloc, initValue, init, adapt, returnBoundary));
        StructuredBodyTable table = tableOf(Map.of(INIT_BLOCK,
            List.of(alloc, initValue, init, adapt, returnBoundary)));
        assertE6005(BindingsProductionValidator.validate(unit, table), "NO_ADAPTER_AT_BOUNDARY",
            "an adapter result wired into a FUNCTION_RETURN boundary op",
            "FUNCTION_RETURN");
    }

    private static void testBindingInitOnceNegatives() {
        // Two INITs for one incarnation.
        BindingId x = nextBindingId();
        ValueId v1 = nextValue();
        ValueId v2 = nextValue();
        SemanticOp alloc = allocOp(x, INIT_BLOCK, 0);
        SemanticOp initA = initOp(x, 0, v1);
        SemanticOp initB = initOp(x, 0, v2);
        LoweredModuleUnit unit = unit(Map.of(), Map.of(),
            List.of(alloc, initA, initB));
        StructuredBodyTable table = tableOf(Map.of(INIT_BLOCK, List.of(alloc, initA, initB)));
        assertE6005(BindingsProductionValidator.validate(unit, table), "BINDING_INIT_ONCE",
            "two INITs for one incarnation", "exactly one per source-declaration "
                + "incarnation");

        // An INIT targeting a FOR_EACH iteration binding's cell.
        BindingId loopBinding = nextBindingId();
        BlockId loopBody = nextBlock();
        SemanticOp forEach = forEachOp(loopBinding, 0, loopBody);
        SemanticOp rogueInit = initOp(loopBinding, 0, nextValue());
        LoweredModuleUnit unitFor = unit(Map.of(), Map.of(),
            List.of(forEach, rogueInit));
        StructuredBodyTable tableFor = tableOf(Map.of(INIT_BLOCK,
            List.of(forEach, rogueInit), loopBody, List.of()));
        assertE6005(BindingsProductionValidator.validate(unitFor, tableFor),
            "BINDING_INIT_ONCE", "an INIT targeting a FOR_EACH iteration binding's cell",
            "never carries a BINDING_INIT");

        // An INIT targeting a parameter cell: the unit payload alone
        // cannot distinguish a parameter ALLOC from a local ALLOC (both
        // mutable=true, generation 0, body-root block), so the walk's
        // checker facts name the parameter binding (the synthetic
        // parameter-transfer entry write is the invoking machinery's
        // pinned initializing write).
        BindingId parameter = nextBindingId();
        FunctionId paramFn = nextFunctionId();
        BlockId paramBody = nextBlock();
        ValueId paramIdentity = nextValue();
        SemanticOp paramAlloc = allocOp(parameter, paramBody, 0);
        SemanticOp rogueParamInit = initOp(parameter, 0, nextValue());
        SemanticOp paramClosure = closureNewOp(paramFn, SIG0, List.of(), paramBody,
            paramIdentity);
        LoweredModuleUnit unitParam = unit(
            Map.of(paramFn, function(paramFn, SIG0, List.of(), paramBody)),
            Map.of(new FunctionAllocationIdentity(paramIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(paramFn, paramBody)),
            List.of(paramClosure, paramAlloc, rogueParamInit));
        StructuredBodyTable tableParam = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(paramClosure)),
            Map.entry(paramBody, List.of(paramAlloc, rogueParamInit))));
        assertE6005(BindingsProductionValidator.validate(unitParam, tableParam,
                new BindingsProductionValidator.PinnedWriteFacts(Set.of(parameter), Set.of())),
            "BINDING_INIT_ONCE", "an INIT targeting a parameter cell", "parameter cell");

        // An INIT targeting an import-alias cell: the unit payload
        // alone cannot distinguish an alias ALLOC from an intrinsic
        // ALLOC (both module-region mutable=false ALLOCs), so the
        // walk's checker facts name the alias binding (the
        // MODULE_IMPORT completion write is the pinned initializing
        // write).
        BindingId alias = nextBindingId();
        SemanticOp aliasAlloc = allocOp(alias, INIT_BLOCK, 0);
        SemanticOp rogueAliasInit = initOp(alias, 0, nextValue());
        SemanticOp moduleImport = moduleImportOp();
        LoweredModuleUnit unitAlias = unit(Map.of(), Map.of(),
            List.of(aliasAlloc, rogueAliasInit, moduleImport));
        StructuredBodyTable tableAlias = tableOf(Map.of(INIT_BLOCK,
            List.of(aliasAlloc, rogueAliasInit, moduleImport)));
        assertE6005(BindingsProductionValidator.validate(unitAlias, tableAlias,
                new BindingsProductionValidator.PinnedWriteFacts(Set.of(), Set.of(alias))),
            "BINDING_INIT_ONCE", "an INIT targeting an import-alias cell",
            "import-alias cell");
    }

    // =========================================================================
    // 5. IR-level positives
    // =========================================================================

    private static void testIrLevelPositives() {
        System.out.println("-- IR-level positives (unit-level; each must validate) --");

        // The default-block module-level reference (R4's module-level
        // arm, unit-level — source-level CLASS_DEFAULT production is
        // ISSUE-0238's): a default block loading a later-declared
        // module function validates under the module-init-completion
        // arm extended to per-construction default blocks.
        BindingId makeFactory = nextBindingId();
        FunctionId fn = nextFunctionId();
        BlockId fnBody = nextBlock();
        ValueId identity = nextValue();
        BlockId defaultBlock = nextBlock();
        SemanticOp alloc = allocOp(makeFactory, INIT_BLOCK, 0);
        SemanticOp closure = closureNewOp(fn, SIG1, List.of(), fnBody, identity);
        SemanticOp init = initOp(makeFactory, 0, identity);
        SemanticOp classDefault = classDefaultOp(defaultBlock);
        SemanticOp defaultLoad = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(makeFactory, 0),
            nextValue(), SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unit = unit(
            Map.of(fn, function(fn, SIG1, List.of(), fnBody)),
            Map.of(new FunctionAllocationIdentity(identity.id()),
                new FunctionExecutionBinding.LoweredBody(fn, fnBody)),
            List.of(alloc, closure, init, classDefault, defaultLoad));
        StructuredBodyTable table = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(alloc, closure, init, classDefault)),
            Map.entry(fnBody, List.of()),
            Map.entry(defaultBlock, List.of(defaultLoad))));
        assertPass(BindingsProductionValidator.validate(unit, table),
            "the default-block module-level reference (R4's module-level arm)");

        // The import-alias synthetic write: the MODULE_IMPORT
        // completion names the alias cell in its payload and dominates
        // alias loads in the module block.
        BindingId alias = nextBindingId();
        SemanticOp aliasAlloc = allocOp(alias, INIT_BLOCK, 0);
        SemanticOp moduleImport = moduleImportOp(alias);
        SemanticOp aliasLoad = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(alias, 0),
            nextValue(), RuntimeDescriptor.Table.INSTANCE, List.of(), List.of(),
            FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unitAlias = unit(Map.of(), Map.of(),
            List.of(aliasAlloc, moduleImport, aliasLoad));
        StructuredBodyTable tableAlias = tableOf(Map.of(INIT_BLOCK,
            List.of(aliasAlloc, moduleImport, aliasLoad)));
        assertPass(BindingsProductionValidator.validate(unitAlias, tableAlias),
            "the import-alias MODULE_IMPORT completion write");

        // A parameter's synthetic entry write dominates body loads.
        BindingId parameter = nextBindingId();
        FunctionId paramFn = nextFunctionId();
        BlockId paramBody = nextBlock();
        ValueId paramIdentity = nextValue();
        SemanticOp paramAlloc = allocOp(parameter, paramBody, 0);
        SemanticOp paramLoad = opWith(nextOpId(), SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(parameter, 0),
            nextValue(), INT, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        SemanticOp paramClosure = closureNewOp(paramFn, SIG0, List.of(), paramBody,
            paramIdentity);
        LoweredModuleUnit unitParam = unit(
            Map.of(paramFn, function(paramFn, SIG0, List.of(), paramBody)),
            Map.of(new FunctionAllocationIdentity(paramIdentity.id()),
                new FunctionExecutionBinding.LoweredBody(paramFn, paramBody)),
            List.of(paramClosure, paramAlloc, paramLoad));
        StructuredBodyTable tableParam = tableOf(Map.ofEntries(
            Map.entry(INIT_BLOCK, List.of(paramClosure)),
            Map.entry(paramBody, List.of(paramAlloc, paramLoad))));
        assertPass(BindingsProductionValidator.validate(unitParam, tableParam),
            "the parameter-transfer entry write dominates body loads");

        // The for-let header capture (B1/B2): a closure created in the
        // update block captures the generation-0 counter — the
        // per-iteration incarnation is out of lexical scope at header
        // sites, so the capture resolves to the counter, the closure
        // body's generation-0 loads match, and the counter derives
        // SHARED_CELL (DIRECT unless a closure in the condition/update
        // captures it).
        ForLetHeaderFixture updateCapture = forLetHeaderFixture(0L);
        assertPass(BindingsProductionValidator.validate(updateCapture.unit(),
                updateCapture.table()),
            "the for-let update-block capture of the generation-0 counter");
        List<BindingsProductionValidator.DerivedCellKind> derived =
            BindingsProductionValidator.deriveCellKinds(updateCapture.unit(),
                updateCapture.table());
        check(derived.stream().anyMatch(row ->
                row.key().binding().equals(updateCapture.counter())
                    && row.key().generation() == 0
                    && row.key().scope().equals(updateCapture.loopInit())
                    && row.kind() == BindingCellKind.SHARED_CELL),
            "the update-site capture makes the generation-0 counter derive SHARED_CELL "
                + "(the B2 condition/update-capture arm)");

        // A HostFunctionValue whose identity later crosses an ordinary
        // VARIABLE_DECLARATION boundary (identity-preserving flow):
        // only the producing HOST_TO_DEAL crossing counts toward the
        // exactly-one requirement.
        ValueId hostValue = nextValue();
        SemanticOp hostCrossing = boundaryOp(BoundaryKind.HOST_TO_DEAL, SIG1, hostValue);
        SemanticOp laterDeclaration = boundaryOp(BoundaryKind.VARIABLE_DECLARATION, SIG1,
            hostValue);
        LoweredModuleUnit unitHostFlow = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(hostValue.id()),
                new FunctionExecutionBinding.HostFunctionValue(MOD,
                    hostCrossing.opId(), SIG1)),
            List.of(hostCrossing, laterDeclaration));
        StructuredBodyTable tableHostFlow = tableOf(Map.of(INIT_BLOCK,
            List.of(hostCrossing, laterDeclaration)));
        assertPass(BindingsProductionValidator.validate(unitHostFlow, tableHostFlow),
            "a HostFunctionValue followed by an identity-preserving VARIABLE_DECLARATION "
                + "crossing");

        // A HostFunction produced by exactly one import member read
        // (the host/external seam's producing site).
        ValueId memberReadResult = nextValue();
        SemanticOp memberRead = opWith(nextOpId(), SemanticOpKind.MEMBER_READ,
            new KindPayload.MemberReadPayload(nextValue(), "g"),
            memberReadResult, SIG1, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE,
            null);
        LoweredModuleUnit unitHostRead = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(memberReadResult.id()),
                new FunctionExecutionBinding.HostFunction(new ModuleId("host"), "g", SIG1)),
            List.of(memberRead));
        StructuredBodyTable tableHostRead = tableOf(Map.of(INIT_BLOCK, List.of(memberRead)));
        assertPass(BindingsProductionValidator.validate(unitHostRead, tableHostRead),
            "a HostFunction produced by exactly one import member read");

        // An ExternalFunction produced by exactly one export read.
        ValueId exportReadValue = nextValue();
        SemanticOp exportRead = opWith(nextOpId(), SemanticOpKind.EXPORT_READ,
            new KindPayload.ExportReadPayload(new ModuleId("lib.math"), "g", SIG1,
                exportReadValue),
            null, null, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE, null);
        LoweredModuleUnit unitExternalRead = unit(Map.of(),
            Map.of(new FunctionAllocationIdentity(exportReadValue.id()),
                new FunctionExecutionBinding.ExternalFunction(new ModuleId("lib.math"),
                    "g", SIG1, deal.semantic.ir.ExternalExecutionOwner.SHARED_BODY)),
            List.of(exportRead));
        StructuredBodyTable tableExternalRead = tableOf(Map.of(INIT_BLOCK,
            List.of(exportRead)));
        assertPass(BindingsProductionValidator.validate(unitExternalRead, tableExternalRead),
            "an ExternalFunction produced by exactly one export read");
    }

    // =========================================================================
    // 6. Cell-kind invariant (the complete B2 iff over the corpus)
    // =========================================================================

    private static void testCellKindInvariant() {
        System.out.println("-- cell-kind invariant: the closed B2 iff across the corpus --");

        List<String> corpus = List.of(
            "let x: int = (x = 1);",
            "function f(): null { let g: () => null = f; }",
            """
            function even(): null { let oddRef: () => null = odd; }
            function odd(): null { let evenRef: () => null = even; }
            """,
            "for (let i = 0; i < 3; i = i + 1) { let j = i; }",
            """
            function f(): null {
              for (let c: string of "ab") {
                let g: () => null = function(): null { let read: string = c; };
              }
            }
            """,
            combinedCorpusSource());
        for (String source : corpus) {
            SemanticLowerer.ValidationCoreResult result = validatedResult(source,
                "the cell-kind invariant corpus slice [" + source.strip().split("\n")[0]
                    + "...]");
            if (result == null) {
                continue;
            }
            LoweredModuleUnit unit = result.lowering().unit();
            List<BindingsProductionValidator.DerivedCellKind> derived =
                BindingsProductionValidator.deriveCellKinds(unit, result.lowering().table());
            Map<String, BindingCellKind> byKey = new LinkedHashMap<>();
            for (BindingsProductionValidator.DerivedCellKind row : derived) {
                byKey.put(row.key().binding().id() + "|" + row.key().generation() + "|"
                    + row.key().scope().id(), row.kind());
            }
            for (SemanticOp op : unit.ops()) {
                if (op.payload() instanceof KindPayload.BindingAllocPayload alloc) {
                    String key = alloc.binding().id() + "|" + alloc.generation() + "|"
                        + alloc.scope().id();
                    BindingCellKind expected = byKey.get(key);
                    check(expected != null, "the derivation covers every emitted ALLOC "
                        + key);
                    if (expected != null) {
                        check(expected == alloc.cellKind(), "the emitted cell kind of "
                            + key + " equals the closed derivation ("
                            + alloc.cellKind() + " == " + expected + ")");
                    }
                }
                if (op.payload() instanceof KindPayload.ForEachPayload forEach) {
                    boolean sharedDerived = derived.stream().anyMatch(row ->
                        row.key().binding().equals(forEach.binding())
                            && row.key().generation() == forEach.generation()
                            && row.kind() == BindingCellKind.SHARED_CELL);
                    check(sharedDerived, "the FOR_EACH iteration binding derives "
                        + "SHARED_CELL (the pinned special case)");
                }
                if (op.payload() instanceof KindPayload.RecursiveGroupInitPayload group) {
                    for (BindingId member : group.bindings()) {
                        boolean memberShared = derived.stream().anyMatch(row ->
                            row.key().binding().equals(member) && row.key().generation() == 0
                                && row.kind() == BindingCellKind.SHARED_CELL);
                        check(memberShared, "the group member " + member + " derives "
                            + "SHARED_CELL by construction (B2)");
                    }
                }
            }
        }
    }

    // =========================================================================
    // 7. The combined corpus and byte-identical repeated lowering
    // =========================================================================

    private static void testCombinedCorpusAndDeterminism() {
        System.out.println("-- combined corpus: all three modes + byte-identical repetition --");

        String source = combinedCorpusSource();
        SemanticLowerer.ValidationCoreResult first = validatedResult(source,
            "the combined corpus (first lowering)");
        SemanticLowerer.ValidationCoreResult second = validatedResult(source,
            "the combined corpus (second lowering)");
        if (first == null || second == null) {
            return;
        }
        LoweredModuleUnit unit = first.lowering().unit();
        List<SemanticOp> ops = unit.ops();
        Map<CaptureMode, Integer> modeCounts = new java.util.EnumMap<>(CaptureMode.class);
        int adapters = 0;
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adapters++;
                KindPayload.FunctionAdaptPayload payload =
                    (KindPayload.FunctionAdaptPayload) op.payload();
                modeCounts.merge(payload.mode(), 1, Integer::sum);
            }
        }
        check(adapters == 6, "six adapters over the earlier children's production; got "
            + adapters);
        check(modeCounts.getOrDefault(CaptureMode.VALUE, 0) == 3,
            "three VALUE adapters (g over the proved load, m over the CLOSURE_NEW "
                + "result, n over the intrinsic identity); got "
                + modeCounts.getOrDefault(CaptureMode.VALUE, 0));
        check(modeCounts.getOrDefault(CaptureMode.SHARED_CELL, 0) == 1,
            "one SHARED_CELL adapter (h over the reassigned f); got "
                + modeCounts.getOrDefault(CaptureMode.SHARED_CELL, 0));
        check(modeCounts.getOrDefault(CaptureMode.REEVALUATE_THUNK, 0) == 2,
            "two REEVALUATE_THUNK adapters (k's declaration and k's assignment over "
                + "the (s = inner) composite source); got "
                + modeCounts.getOrDefault(CaptureMode.REEVALUATE_THUNK, 0));

        // Registry one-to-one across the corpus: every AdapterBinding key
        // is distinct and registered exactly once.
        Set<Long> adapterKeys = new java.util.HashSet<>();
        int adapterBindings = 0;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.AdapterBinding) {
                adapterBindings++;
                check(adapterKeys.add(entry.getKey().id()),
                    "the adapter registration keys are distinct");
            }
        }
        check(adapterBindings == 6, "six AdapterBinding registrations; got " + adapterBindings);

        // Byte-identical repeated lowering (D10: dependency order, source
        // order, semantic role, synthetic ordinal).
        byte[] firstDump = SemanticIrDumper.dumpModule(first.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.lowering().unit());
        check(Arrays.equals(firstDump, secondDump),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dumps");
        check(first.shapeMapFacts().equals(second.shapeMapFacts()),
            "repeated lowering records identical shape-map facts");
        check(BindingsProductionValidator.deriveCellKinds(first.lowering().unit(),
                first.lowering().table())
                .equals(BindingsProductionValidator.deriveCellKinds(second.lowering().unit(),
                    second.lowering().table())),
            "repeated lowering derives identical cell kinds");
    }

    /** The fixed combined-corpus source over the earlier children's production. */
    private static String combinedCorpusSource() {
        return """
            function inner(x: int): null {}
            function even(): null {
              let oddRef: () => null = odd;
            }
            function odd(): null {
              let evenRef: () => null = even;
            }
            function main(): null {
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
              f = f;
              let h: (a: int, b: int) => null = f;
              let s: (x: int) => null = inner;
              let k: (a: int, b: int) => null = (s = inner);
              k = (s = inner);
              let m: (a: int, b: int) => null = function(x: int): null {};
              let n: (a: number, b: number) => int = int;
              let p: (a: int, b: int) => null = g;
            }
            """;
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Bindings Production Validation Test (ISSUE-0451 B9 "
            + "child) ===\n");

        testSurfaceAndRules();
        testSourceLevelPositives();
        testSourceLevelNegatives();
        testIrLevelNegatives();
        testIrLevelPositives();
        testCellKindInvariant();
        testCombinedCorpusAndDeterminism();

        System.out.println("\nBindings production validation: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
