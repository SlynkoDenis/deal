package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.ControlFlowValidator;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Verifies the ISSUE-0408 component surface:
 * {@link StructuredBodyTable} (control-flow-structures C-D1 — the
 * block-membership production record with the ordered per-block ops and
 * the inverse membership map) and {@link ControlFlowValidator}
 * (control-flow-structures C-D2 — the production-time block-tree,
 * dominance, and exit checks producing E6005 with
 * {@code validatorRule CONTROL_BLOCK_TREE}/{@code CONTROL_EXIT} and
 * {@code capability EVALUATION_ORDER}, outside the foundation
 * validator's closed 14-condition rule set).
 *
 * <p>Pinned cases (task verification):
 * <ol>
 *   <li>Record surface: defensive copies, unmodifiable maps, null
 *       rejection, the pinned rule names.</li>
 *   <li>Positive corpus: {@code BRANCH(IF)} with selected/alternate
 *       blocks, {@code BRANCH(LOGICAL_AND|OR)} with the right-operand
 *       block, {@code LOOP(WHILE)} with the per-iteration condition block
 *       in {@code initBlock}, {@code LOOP(FOR)} with init/body/update
 *       blocks, the test-less FOR shape ({@code CONST true} in
 *       {@code initBlock}, update ops only in {@code updateBlock}),
 *       {@code FOR_EACH(ARRAY_VALUES)} with a body block,
 *       {@code TRY_CATCH} with try/catch blocks, nested structures,
 *       break/continue/return targets including transfer across a
 *       try boundary, and the five module-level kinds
 *       ({@code MODULE_INIT}/{@code EXTERNAL_ENTRY}/
 *       {@code CLASS_FACTORY}/{@code CALLBACK_INVOKE}/
 *       {@code ENTRY_INVOKE}) absent from the table — each
 *       validates.</li>
 *   <li>Negative corpus, each producing exactly one E6005 with the
 *       correct rule and {@link deal.semantic.ir.LoweringFailureDetail}
 *       fields: orphan block, double-referenced block, cyclic nesting, an
 *       op in two blocks, inverse-map conflicts, an unknown
 *       {@code BlockId} in a payload, an op after
 *       {@code RETURN}/{@code BREAK}/{@code CONTINUE}/{@code THROW} in a
 *       block, a root block referenced by a control position, a structure
 *       op outside every block, an op of a lowered function that is a
 *       member of no block (the unit-to-table completeness direction —
 *       a {@code CONST} plus an {@code ASSIGN} in neither map), an op
 *       listed for a block that is not a unit op, a missing function
 *       body/module-init block — all {@code CONTROL_BLOCK_TREE} (the
 *       {@code BREAK} member-of-no-block fixture now stops at this
 *       earlier membership rejection too); {@code BREAK} targeting a
 *       non-loop op, an unknown op, or a non-enclosing loop, and
 *       {@code RETURN} naming a different or unknown function — all
 *       {@code CONTROL_EXIT}.</li>
 *   <li>Determinism and purity: identical inputs produce identical
 *       outcomes and the unit and table are never mutated.</li>
 *   <li>Null-argument rejection.</li>
 * </ol>
 */
public class ControlFlowValidatorTest {

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
    // Shared synthetic fixtures (the SemanticIrValidatorTest discipline)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.flow");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor BOOL = RuntimeDescriptor.Boolean.INSTANCE;
    private static final RuntimeDescriptor.Func SIG =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);

    private static final BlockId INIT = new BlockId(0);
    private static final BlockId B0 = new BlockId(10);
    private static final FunctionId MAIN = new FunctionId(1);
    private static final FunctionId HELPER = new FunctionId(2);
    private static final BindingId CATCH_BINDING = new BindingId(3);
    private static final BindingId LOOP_BINDING = new BindingId(4);

    private static int nextOp = 1;
    private static int nextVal = 1;

    private static BlockId b(long id) {
        return new BlockId(id);
    }

    private static OpId nextOpId() {
        return new OpId(MOD, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
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
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        return opWith(nextOpId(), kind, payload, result, resultType, policy, parent);
    }

    private static SemanticOp constInt() {
        return op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp constTrue() {
        return op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Boolean(true)),
            nextValue(), BOOL, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp discard(ValueId value) {
        return op(SemanticOpKind.DISCARD, new KindPayload.DiscardPayload(value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp branchOp(ControlSelector selector, BlockId selected,
            BlockId alternate) {
        return op(SemanticOpKind.BRANCH,
            new KindPayload.BranchPayload(selector, nextValue(), selected, alternate),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp loopOp(ControlSelector selector, BlockId init, BlockId body,
            BlockId update) {
        return op(SemanticOpKind.LOOP,
            new KindPayload.LoopPayload(selector, init, nextValue(), body, update),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp forEachOp(BlockId body) {
        return op(SemanticOpKind.FOR_EACH,
            new KindPayload.ForEachPayload(IterationMode.ARRAY_VALUES, nextValue(), LOOP_BINDING,
                0, body),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp tryCatchOp(BlockId tryBlock, BlockId catchBlock) {
        return op(SemanticOpKind.TRY_CATCH,
            new KindPayload.TryCatchPayload(tryBlock, CATCH_BINDING, catchBlock),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp throwOp() {
        return op(SemanticOpKind.THROW, new KindPayload.ThrowPayload(nextValue()),
            null, null, FailurePolicyId.THROW_TRANSFER, null);
    }

    private static SemanticOp breakOp(OpId loopId) {
        return op(SemanticOpKind.BREAK, new KindPayload.BreakPayload(loopId),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp continueOp(OpId loopId) {
        return op(SemanticOpKind.CONTINUE, new KindPayload.ContinuePayload(loopId),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static SemanticOp returnOp(FunctionId function) {
        return op(SemanticOpKind.RETURN,
            new KindPayload.ReturnPayload(null, function, nextOpId(), nextOpId()),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
    }

    private static LoweredFunction function(FunctionId id, BlockId body) {
        return new LoweredFunction(id, SIG, List.of(), body);
    }

    private static LoweredModuleUnit unit(Map<FunctionId, LoweredFunction> functions,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD, IFACE, LCH, Set.of(), Map.of(), Map.of(),
            functions, new ModuleInitPlan(List.of(), INIT), ExportPlan.empty(), Map.of(), ops);
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
            String... contains) {
        check(diagnostic.isPresent(), rule + " is rejected with E6005");
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()), rule + " diagnostic code is E6005");
        check(d.diagnosticCode() == DiagnosticCode.E6005, rule + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            rule + " phase is BACKEND_LOWERING");
        check("error".equals(d.severity()), rule + " severity is error");
        String message = d.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            rule + " is named as the validator rule (exactly one rule per fixture); got \""
                + message + "\"");
        check(message.contains("capability EVALUATION_ORDER"),
            rule + " message carries capability EVALUATION_ORDER");
        check(message.contains("deal.semantic-ir/1"), rule + " message carries the IR version");
        check(message.contains("mod.flow"), rule + " message carries the module path");
        check(message.contains("ControlFlowValidator " + rule),
            rule + " message carries the ControlFlowValidator origin");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \""
                + message + "\"");
        }
    }

    // =========================================================================
    // 1. Surface and record contract
    // =========================================================================

    private static void testSurfaceAndRecord() {
        System.out.println("-- Surface and StructuredBodyTable record contract --");

        check(ControlFlowValidator.CONTROL_BLOCK_TREE.equals("CONTROL_BLOCK_TREE"),
            "CONTROL_BLOCK_TREE rule name is pinned");
        check(ControlFlowValidator.CONTROL_EXIT.equals("CONTROL_EXIT"),
            "CONTROL_EXIT rule name is pinned");

        // Defensive copies: later mutation of the constructor arguments is invisible.
        SemanticOp x = constInt();
        SemanticOp y = constInt();
        Map<BlockId, List<OpId>> mutableOps = new LinkedHashMap<>();
        mutableOps.put(INIT, new ArrayList<>(List.of(x.opId(), y.opId())));
        Map<OpId, BlockId> mutableInverse = new LinkedHashMap<>();
        mutableInverse.put(x.opId(), INIT);
        mutableInverse.put(y.opId(), INIT);
        StructuredBodyTable table = new StructuredBodyTable(mutableOps, mutableInverse);
        mutableOps.put(b(9), new ArrayList<>());
        mutableInverse.clear();
        check(table.blockOps().size() == 1 && table.opBlocks().size() == 2,
            "the record copies the constructor maps (later mutation is invisible)");

        // Unmodifiable surface.
        try {
            table.blockOps().put(b(9), List.of());
            fail("expected UnsupportedOperationException on blockOps mutation");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
        try {
            table.opBlocks().put(nextOpId(), INIT);
            fail("expected UnsupportedOperationException on opBlocks mutation");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
        try {
            table.blockOps().get(INIT).add(nextOpId());
            fail("expected UnsupportedOperationException on a per-block list mutation");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
    }

    // =========================================================================
    // 2. Positive corpus: every construct shape validates
    // =========================================================================

    private static void testPositives() {
        System.out.println("-- Positive corpus: every construct shape validates --");

        // BRANCH(IF) with selected/alternate blocks.
        {
            SemanticOp c0 = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(1), b(2));
            SemanticOp c1 = constInt();
            SemanticOp c2 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br, c1, c2));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, br)),
                Map.entry(b(1), List.of(c1)),
                Map.entry(b(2), List.of(c2))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "BRANCH(IF) with selected/alternate blocks");
        }

        // BRANCH(LOGICAL_AND|OR) with the right-operand block; IF without else.
        {
            SemanticOp c0 = constInt();
            SemanticOp brAnd = branchOp(ControlSelector.LOGICAL_AND, b(1), null);
            SemanticOp brOr = branchOp(ControlSelector.LOGICAL_OR, b(2), null);
            SemanticOp brIf = branchOp(ControlSelector.IF, b(3), null);
            SemanticOp c1 = constInt();
            SemanticOp c2 = constInt();
            SemanticOp c3 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, brAnd, brOr, brIf, c1, c2, c3));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, brAnd, brOr, brIf)),
                Map.entry(b(1), List.of(c1)),
                Map.entry(b(2), List.of(c2)),
                Map.entry(b(3), List.of(c3))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "BRANCH(LOGICAL_AND|OR) right-operand blocks and an else-less IF");
        }

        // LOOP(WHILE) with the per-iteration condition block in initBlock and a
        // continue landing at the condition block.
        {
            SemanticOp c0 = constInt();
            SemanticOp loop = loopOp(ControlSelector.WHILE, b(1), b(2), null);
            SemanticOp cCond = constInt();
            SemanticOp cBody = constInt();
            SemanticOp cont = continueOp(loop.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, loop, cCond, cBody, cont));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, loop)),
                Map.entry(b(1), List.of(cCond)),
                Map.entry(b(2), List.of(cBody, cont))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "LOOP(WHILE) with condition block in initBlock and continue to the condition");
        }

        // LOOP(FOR) with init/body/update blocks.
        {
            SemanticOp c0 = constInt();
            SemanticOp loop = loopOp(ControlSelector.FOR, b(1), b(2), b(3));
            SemanticOp cInit = constInt();
            SemanticOp cBody = constInt();
            SemanticOp cUpdate = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, loop, cInit, cBody, cUpdate));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, loop)),
                Map.entry(b(1), List.of(cInit)),
                Map.entry(b(2), List.of(cBody)),
                Map.entry(b(3), List.of(cUpdate))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "LOOP(FOR) with init/body/update blocks");
        }

        // Test-less FOR: the CONST true condition production in initBlock and
        // update ops only in updateBlock.
        {
            SemanticOp c0 = constInt();
            SemanticOp loop = loopOp(ControlSelector.FOR, b(1), b(2), b(3));
            SemanticOp condTrue = constTrue();
            SemanticOp cBody = constInt();
            SemanticOp upd = discard(nextValue());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, loop, condTrue, cBody, upd));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, loop)),
                Map.entry(b(1), List.of(condTrue)),
                Map.entry(b(2), List.of(cBody)),
                Map.entry(b(3), List.of(upd))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "test-less FOR shape (CONST true in initBlock, update ops only in updateBlock)");
        }

        // FOR_EACH(ARRAY_VALUES) with a body block and break/continue targets.
        {
            SemanticOp c0 = constInt();
            SemanticOp forEach = forEachOp(b(1));
            SemanticOp cBody = constInt();
            SemanticOp brk = breakOp(forEach.opId());
            SemanticOp forEach2 = forEachOp(b(2));
            SemanticOp cBody2 = constInt();
            SemanticOp cont = continueOp(forEach2.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, forEach, cBody, brk, forEach2, cBody2, cont));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, forEach, forEach2)),
                Map.entry(b(1), List.of(cBody, brk)),
                Map.entry(b(2), List.of(cBody2, cont))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "FOR_EACH(ARRAY_VALUES) with break/continue targeting the for-of");
        }

        // TRY_CATCH with try/catch blocks and a THROW terminator.
        {
            SemanticOp c0 = constInt();
            SemanticOp tc = tryCatchOp(b(1), b(2));
            SemanticOp cTry = constInt();
            SemanticOp throwOp = throwOp();
            SemanticOp cCatch = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, tc, cTry, throwOp, cCatch));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, tc)),
                Map.entry(b(1), List.of(cTry, throwOp)),
                Map.entry(b(2), List.of(cCatch))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "TRY_CATCH with try/catch blocks and a THROW terminator");
        }

        // Nested structures: a loop body branch nesting a try/catch; break and
        // continue cross the try boundary; returns name the containing function.
        {
            SemanticOp c0 = constInt();
            SemanticOp loop = loopOp(ControlSelector.FOR, b(1), b(2), b(4));
            SemanticOp ret0 = returnOp(MAIN);
            SemanticOp cInit = constInt();
            SemanticOp cUpdate = constInt();
            SemanticOp cBody = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(3), b(5));
            SemanticOp tc = tryCatchOp(b(6), b(7));
            SemanticOp cTry = constInt();
            SemanticOp brk = breakOp(loop.opId());
            SemanticOp cCatch = constInt();
            SemanticOp cont = continueOp(loop.opId());
            SemanticOp cAlt = constInt();
            SemanticOp ret = returnOp(MAIN);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, loop, ret0, cInit, cUpdate, cBody, br, tc, cTry, brk, cCatch, cont,
                    cAlt, ret));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, loop, ret0)),
                Map.entry(b(1), List.of(cInit)),
                Map.entry(b(2), List.of(cBody, br)),
                Map.entry(b(3), List.of(tc)),
                Map.entry(b(4), List.of(cUpdate)),
                Map.entry(b(5), List.of(cAlt, ret)),
                Map.entry(b(6), List.of(cTry, brk)),
                Map.entry(b(7), List.of(cCatch, cont))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "nested loop/branch/try-catch with break and continue across the try boundary");
        }

        // RETURN naming the containing function (own body and a nested block).
        {
            SemanticOp ret = returnOp(MAIN);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(ret));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(ret))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "RETURN naming the containing function");
        }

        // Two functions, each RETURN naming its own containing function.
        {
            SemanticOp retMain = returnOp(MAIN);
            SemanticOp retHelper = returnOp(HELPER);
            LoweredModuleUnit unit = unit(Map.of(
                    MAIN, function(MAIN, B0),
                    HELPER, function(HELPER, b(1))),
                List.of(retMain, retHelper));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(retMain)),
                Map.entry(b(1), List.of(retHelper))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "each function's RETURN names its own containing function");
        }

        // The five module-level kinds may be absent from the table: they are
        // not ops of a lowered function (the completeness exemption).
        {
            SemanticOp moduleInit = op(SemanticOpKind.MODULE_INIT,
                new KindPayload.ModuleInitPayload(MOD, List.of(), INIT),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp externalEntry = op(SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("export", MAIN, SIG, false, nextOpId(), null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp classFactory = op(SemanticOpKind.CLASS_FACTORY,
                new KindPayload.ClassFactoryPayload(new ClassId("mod.flow", "Box"), List.of(),
                    nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp callbackInvoke = op(SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(nextValue(), SIG, List.of(), nextOpId()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp entryInvoke = op(SemanticOpKind.ENTRY_INVOKE,
                new KindPayload.EntryInvokePayload(MOD, MAIN),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(moduleInit, externalEntry, classFactory, callbackInvoke, entryInvoke));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.<SemanticOp>of())));
            assertPass(ControlFlowValidator.validate(unit, table),
                "the five module-level kinds may be absent from the block table");
        }
    }

    // =========================================================================
    // 3. Negative corpus: one defect per fixture, correct rule and detail
    // =========================================================================

    private static void testNegatives() {
        System.out.println("-- Negative corpus: each defect produces the pinned E6005 --");

        // Orphan block.
        {
            SemanticOp c0 = constInt();
            SemanticOp orphanOp = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, orphanOp));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0)),
                Map.entry(b(9), List.of(orphanOp))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "orphan block BlockId(9)");
        }

        // Double-referenced block (same op, both branch positions).
        {
            SemanticOp c0 = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(1), b(1));
            SemanticOp c1 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br, c1));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, br)),
                Map.entry(b(1), List.of(c1))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "referenced by more than one control payload position");
        }

        // Double-referenced block (two distinct ops).
        {
            SemanticOp c0 = constInt();
            SemanticOp br1 = branchOp(ControlSelector.IF, b(1), null);
            SemanticOp br2 = branchOp(ControlSelector.IF, b(1), null);
            SemanticOp c1 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br1, br2, c1));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, br1, br2)),
                Map.entry(b(1), List.of(c1))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "referenced by more than one control payload position");
        }

        // Cyclic nesting: two blocks each containing a loop whose body is the
        // other block.
        {
            SemanticOp c0 = constInt();
            SemanticOp loop1 = loopOp(ControlSelector.FOR, null, b(2), null);
            SemanticOp loop2 = loopOp(ControlSelector.FOR, null, b(1), null);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, loop1, loop2));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0)),
                Map.entry(b(1), List.of(loop1)),
                Map.entry(b(2), List.of(loop2))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "cyclic block nesting");
        }

        // An op in two blocks.
        {
            SemanticOp shared = constInt();
            SemanticOp other = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(shared, other));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(shared)),
                Map.entry(b(1), List.of(shared, other))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "member of more than one block");
        }

        // Inverse-map conflict: the inverse entry names a different block.
        {
            SemanticOp shared = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(shared));
            Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
            blockOps.put(INIT, List.of());
            blockOps.put(B0, List.of(shared.opId()));
            Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
            opBlocks.put(shared.opId(), b(1));
            assertE6005(ControlFlowValidator.validate(unit,
                    new StructuredBodyTable(blockOps, opBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "inverse-map conflict");
        }

        // Inverse-map conflict: a listed op has no inverse entry.
        {
            SemanticOp shared = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(shared));
            Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
            blockOps.put(INIT, List.of());
            blockOps.put(B0, List.of(shared.opId()));
            assertE6005(ControlFlowValidator.validate(unit,
                    new StructuredBodyTable(blockOps, Map.of())),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "has no inverse membership entry");
        }

        // Inverse-map conflict: an inverse entry without a block-list membership.
        {
            SemanticOp listed = constInt();
            SemanticOp extra = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(listed, extra));
            Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
            blockOps.put(INIT, List.of());
            blockOps.put(B0, List.of(listed.opId()));
            Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
            opBlocks.put(listed.opId(), B0);
            opBlocks.put(extra.opId(), b(1));
            assertE6005(ControlFlowValidator.validate(unit,
                    new StructuredBodyTable(blockOps, opBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "listed in no block");
        }

        // Unknown BlockId in a payload position.
        {
            SemanticOp c0 = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(77), null);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, br))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "references block BlockId(77) which is not a block of the table");
        }

        // An op after RETURN / BREAK / CONTINUE / THROW in a block.
        {
            SemanticOp[] terminators = {
                returnOp(MAIN),
                breakOp(nextOpId()),
                continueOp(nextOpId()),
                throwOp()
            };
            for (SemanticOp terminator : terminators) {
                SemanticOp after = constInt();
                LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                    List.of(terminator, after));
                StructuredBodyTable table = tableOf(Map.ofEntries(
                    Map.entry(INIT, List.<SemanticOp>of()),
                    Map.entry(B0, List.of(terminator, after))));
                assertE6005(ControlFlowValidator.validate(unit, table),
                    ControlFlowValidator.CONTROL_BLOCK_TREE, "after a terminator");
            }
        }

        // A root block referenced by a control payload position.
        {
            SemanticOp c0 = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(0), null);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0, br))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "root block BlockId(0)");
        }

        // A control structure op outside every block.
        {
            SemanticOp c0 = constInt();
            SemanticOp br = branchOp(ControlSelector.IF, b(1), null);
            SemanticOp c1 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c0, br, c1));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c0)),
                Map.entry(b(1), List.of(c1))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "is not a member of any block");
        }

        // An op listed in a block but not produced by the unit.
        {
            SemanticOp c0 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(c0));
            Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
            blockOps.put(INIT, List.of());
            blockOps.put(B0, List.of(c0.opId(), new OpId(MOD, 999)));
            Map<OpId, BlockId> opBlocks = new LinkedHashMap<>();
            opBlocks.put(c0.opId(), B0);
            opBlocks.put(new OpId(MOD, 999), B0);
            assertE6005(ControlFlowValidator.validate(unit,
                    new StructuredBodyTable(blockOps, opBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "is not a produced op of the unit");
        }

        // A function body block missing from the table.
        {
            SemanticOp c0 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(c0));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(b(1), List.of(c0))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "body block BlockId(10)");
        }

        // The module init block missing from the table.
        {
            SemanticOp c0 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(c0));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(B0, List.of(c0))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "module init block BlockId(0)");
        }

        // BREAK targeting a non-loop op.
        {
            SemanticOp c = constInt();
            SemanticOp brk = breakOp(c.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c, brk));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c, brk))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "is not a LOOP or FOR_EACH op");
        }

        // BREAK targeting an op that is not a unit op.
        {
            SemanticOp brk = breakOp(new OpId(MOD, 999));
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(brk));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(brk))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "is not a LOOP or FOR_EACH op");
        }

        // BREAK targeting a non-enclosing loop (the sibling loop's op).
        {
            SemanticOp loop1 = loopOp(ControlSelector.FOR, null, b(1), null);
            SemanticOp loop2 = loopOp(ControlSelector.FOR, null, b(2), null);
            SemanticOp brk = breakOp(loop2.opId());
            SemanticOp c2 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(loop1, loop2, brk, c2));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(loop1, loop2)),
                Map.entry(b(1), List.of(brk)),
                Map.entry(b(2), List.of(c2))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "does not enclose its block");
        }

        // Ops of a lowered function that are members of no block: a CONST
        // and an ASSIGN op in neither the block lists nor the inverse map
        // (the C-D1 unit-to-table completeness direction).
        {
            SemanticOp c = constInt();
            SemanticOp assign = op(SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(AssignTargetKind.VARIABLE, List.of()),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c, assign));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.<SemanticOp>of())));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "is a member of no block");
        }

        // BREAK as a member of no block: the completeness check stops the
        // unit before any exit analysis, so the pinned rule is the earlier
        // CONTROL_BLOCK_TREE rejection, never CONTROL_EXIT.
        {
            SemanticOp loop = loopOp(ControlSelector.FOR, null, b(1), null);
            SemanticOp brk = breakOp(loop.opId());
            SemanticOp c1 = constInt();
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(loop, brk, c1));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(loop)),
                Map.entry(b(1), List.of(c1))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "is a member of no block");
        }

        // RETURN naming a different function.
        {
            SemanticOp ret = returnOp(HELPER);
            LoweredModuleUnit unit = unit(Map.of(
                    MAIN, function(MAIN, B0),
                    HELPER, function(HELPER, b(1))),
                List.of(ret));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(ret)),
                Map.entry(b(1), List.<SemanticOp>of())));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "belongs to the block tree rooted at BlockId(10)");
        }

        // RETURN naming a function that is not a function of the unit.
        {
            SemanticOp ret = returnOp(new FunctionId(99));
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(ret));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(ret))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "is not a function of the unit");
        }
    }

    // =========================================================================
    // 4b. The dynamic invocation's call-owned return records (ISSUE-0657)
    // =========================================================================

    /**
     * The invocation-owned return record of a dynamic {@code CALL} — the
     * {@code FUNCTION_RETURN} cell's parent RETURN — is admitted outside the
     * block tree, and every other unattached RETURN keeps the completeness and
     * exit rules.
     */
    private static void testCallOwnedReturnRecords() {
        System.out.println("-- Call-owned return records: the dynamic invocation's "
            + "record is admitted outside the block tree --");

        // Positive: the dynamic CALL's DEAL-body cell is parented to a RETURN
        // naming the CALL; the record is a member of no block and names no unit
        // function (the callee body is runtime-resolved).
        {
            OpId dealCellId = nextOpId();
            OpId hostCellId = nextOpId();
            OpId externalCellId = nextOpId();
            SemanticOp call = op(SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(nextValue()), SIG, List.of(), null,
                    new KindPayload.DynamicReturnBoundary(dealCellId, hostCellId,
                        externalCellId),
                    null, null),
                nextValue(), RuntimeDescriptor.Null.INSTANCE,
                FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp record = opWith(nextOpId(), SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, new FunctionId(99), call.opId(),
                    dealCellId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp dealCell = opWith(dealCellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, record.opId());
            SemanticOp hostCell = opWith(hostCellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.HOST_SYNC_RETURN, call.opId());
            SemanticOp externalCell = opWith(externalCellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.EXTERNAL_RETURN,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, call.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(call, record, dealCell, hostCell, externalCell));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(call, dealCell, hostCell, externalCell))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "the dynamic CALL's call-owned return record");
        }

        // Positive: the dynamic ASYNC_START's recorded task cell's parent RETURN.
        {
            OpId taskCellId = nextOpId();
            SemanticOp start = op(SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Dynamic(nextValue()),
                    deal.semantic.ir.AsyncStartSource.DEAL_BODY,
                    deal.semantic.ir.ParameterBoundaryMode.RUN, List.of(),
                    RuntimeDescriptor.Null.INSTANCE, taskCellId, null, null),
                new deal.semantic.ir.AsyncTokenId.Canonical(1,
                    deal.semantic.ir.AsyncTokenOwner.DEAL_BODY_TASK),
                deal.semantic.ir.InternalResultType.INTERNAL_ASYNC,
                FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp record = opWith(nextOpId(), SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, new FunctionId(99), start.opId(),
                    taskCellId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp taskCell = opWith(taskCellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, record.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(start, record, taskCell));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(start, taskCell))));
            assertPass(ControlFlowValidator.validate(unit, table),
                "the dynamic ASYNC_START's call-owned return record");
        }

        // Negative: the same unattached record whose parent is a static CALL
        // (no dynamic invocation records it) stays a member of no block.
        {
            OpId cellId = nextOpId();
            SemanticOp call = op(SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(MAIN, B0)),
                    SIG, List.of(), cellId, null, B0, null),
                nextValue(), RuntimeDescriptor.Null.INSTANCE,
                FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp record = opWith(nextOpId(), SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, MAIN, call.opId(), cellId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp cell = opWith(cellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, record.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(call, record, cell));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(call, cell))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "is a member of no block");
        }

        // Negative: a call-owned record that is a block member keeps the exit
        // rule (the exemption covers the invocation-owned record outside the
        // block tree only).
        {
            OpId dealCellId = nextOpId();
            OpId hostCellId = nextOpId();
            OpId externalCellId = nextOpId();
            SemanticOp call = op(SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Dynamic(nextValue()), SIG, List.of(), null,
                    new KindPayload.DynamicReturnBoundary(dealCellId, hostCellId,
                        externalCellId),
                    null, null),
                nextValue(), RuntimeDescriptor.Null.INSTANCE,
                FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp record = opWith(nextOpId(), SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(null, new FunctionId(99), call.opId(),
                    dealCellId),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null);
            SemanticOp dealCell = opWith(dealCellId, SemanticOpKind.BOUNDARY,
                new KindPayload.BoundaryPayload(BoundaryKind.FUNCTION_RETURN,
                    RuntimeDescriptor.Null.INSTANCE, nextValue(),
                    new BoundaryRealization.RuntimeValidation("runtime-validation")),
                null, null, FailurePolicyId.TYPE_DESCRIPTOR, record.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(call, record, dealCell));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(call, dealCell, record))));
            assertE6005(ControlFlowValidator.validate(unit, table),
                ControlFlowValidator.CONTROL_EXIT, "is not a function of the unit");
        }
    }

    // =========================================================================
    // 5. Determinism and purity
    // =========================================================================

    private static void testDeterminismAndPurity() {
        System.out.println("-- Determinism and purity --");

        // Identical outcome across repeated runs over identical inputs.
        {
            SemanticOp c = constInt();
            SemanticOp brk = breakOp(c.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c, brk));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c, brk))));
            String firstMessage = null;
            for (int i = 0; i < 4; i++) {
                Optional<CompilerDiagnostic> outcome = ControlFlowValidator.validate(unit, table);
                if (firstMessage == null) {
                    firstMessage = outcome.orElseThrow().message();
                } else {
                    check(outcome.isPresent() && outcome.get().message().equals(firstMessage),
                        "identical inputs produce identical outcomes (run " + i + ")");
                }
            }
        }

        // Purity: the unit and the table are never mutated.
        {
            SemanticOp c = constInt();
            SemanticOp brk = breakOp(c.opId());
            LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)),
                List.of(c, brk));
            StructuredBodyTable table = tableOf(Map.ofEntries(
                Map.entry(INIT, List.<SemanticOp>of()),
                Map.entry(B0, List.of(c, brk))));
            Map<BlockId, List<OpId>> blockOpsBefore = new LinkedHashMap<>(table.blockOps());
            Map<OpId, BlockId> opBlocksBefore = new LinkedHashMap<>(table.opBlocks());
            List<SemanticOp> opsBefore = new ArrayList<>(unit.ops());
            Optional<CompilerDiagnostic> outcome = ControlFlowValidator.validate(unit, table);
            check(outcome.isPresent(), "the purity fixture fails validation as scripted");
            check(table.blockOps().equals(blockOpsBefore) && table.opBlocks().equals(opBlocksBefore),
                "the validator leaves the table unchanged");
            check(unit.ops().equals(opsBefore), "the validator leaves the unit unchanged");
        }
    }

    // =========================================================================
    // 5. Null-argument rejection
    // =========================================================================

    private static void testNullArgs() {
        System.out.println("-- Null-argument rejection --");

        SemanticOp c0 = constInt();
        LoweredModuleUnit unit = unit(Map.of(MAIN, function(MAIN, B0)), List.of(c0));
        StructuredBodyTable table = tableOf(Map.ofEntries(
            Map.entry(INIT, List.<SemanticOp>of()),
            Map.entry(B0, List.of(c0))));

        expectNpe(() -> ControlFlowValidator.validate(null, table), "a null unit");
        expectNpe(() -> ControlFlowValidator.validate(unit, null), "a null table");
        expectNpe(() -> new StructuredBodyTable(null, Map.of()), "a null blockOps map");
        expectNpe(() -> new StructuredBodyTable(Map.of(), null), "a null opBlocks map");
        expectNpe(() -> new StructuredBodyTable(Map.of(INIT, List.of(c0.opId(), null)),
            Map.of(c0.opId(), INIT)), "a null op in a block list");
        Map<BlockId, List<OpId>> nullKey = new LinkedHashMap<>();
        nullKey.put(null, List.of());
        expectNpe(() -> new StructuredBodyTable(nullKey, Map.of()), "a null block key");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Control Flow Validator Test (ISSUE-0408) ===\n");

        testSurfaceAndRecord();
        testPositives();
        testNegatives();
        testCallOwnedReturnRecords();
        testDeterminismAndPurity();
        testNullArgs();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
