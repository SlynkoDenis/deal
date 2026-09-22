package deal.test;

import deal.ast.AssignmentExpr;
import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.ContinueStatement;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.LiteralExpr;
import deal.ast.MemberAccessExpr;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.WhileStatement;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
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
import deal.semantic.ContainerClaimingSeam;
import deal.semantic.ControlFlowValidator;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
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
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Verifies the ISSUE-0409 control-flow lowering arms of
 * {@link SemanticLowerer} (control-flow-structures C-D3..C-D8): the
 * pinned construct→op map for {@code BRANCH} (IF + logical short
 * circuit), {@code LOOP(WHILE|FOR)} including the test-less FOR row,
 * {@code FOR_EACH(ARRAY_VALUES)}, {@code TRY_CATCH}, {@code THROW},
 * {@code BREAK}/{@code CONTINUE}, and {@code DISCARD} — plus the
 * produced {@link StructuredBodyTable} (C-D1), the production-time
 * {@link ControlFlowValidator} seam (C-D2), the detector coverage rows,
 * the T2 chains-inside-blocks composition, and byte-identical
 * determinism.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>{@code if} → {@code BRANCH(IF)}: the condition's producing ops
 *       complete in the enclosing block before the {@code BRANCH} op;
 *       exactly one of {@code selectedBlock}/{@code alternateBlock}
 *       executes (block membership); an absent {@code else} produces
 *       {@code alternateBlock = null}; an {@code else if} chain nests
 *       its {@code BRANCH} in the alternate block; SUCCESS publishes no
 *       result.</li>
 *   <li>{@code &&}/{@code ||} → {@code BRANCH(LOGICAL_AND/OR)} (never
 *       {@code BINARY}): the left operand completes before START as the
 *       condition; the right operand's producing ops live in
 *       {@code selectedBlock} only; the op's result {@code ValueId} is
 *       the right operand's value identity with result type boolean;
 *       chained {@code &&}/{@code ||} nest in source order.</li>
 *   <li>{@code while} → {@code LOOP(WHILE)} with {@code initBlock} =
 *       the per-iteration condition block and {@code updateBlock =
 *       null}.</li>
 *   <li>{@code for} → {@code LOOP(FOR)}: init + first condition
 *       production in {@code initBlock}; update + condition
 *       re-production in {@code updateBlock} publishing the same
 *       condition {@code ValueId}; a test-less {@code for (;;)} produces
 *       exactly one {@code CONST true} in {@code initBlock} and
 *       {@code updateBlock} carries only the update ops.</li>
 *   <li>{@code for-of} over arrays → {@code FOR_EACH(ARRAY_VALUES)}
 *       (iterable prior step once, fresh binding, initial generation,
 *       {@code TYPE_DESCRIPTOR}); {@code BREAK}/{@code CONTINUE} target
 *       the recorded innermost loop.</li>
 *   <li>{@code try/catch} → {@code TRY_CATCH} with try/catch blocks and
 *       the producer-allocated {@code catchBinding}; a load of the catch
 *       variable lowers to {@code BINDING_LOAD} of that binding;
 *       {@code throw} → {@code THROW} with {@code THROW_TRANSFER} whose
 *       operand completes before START.</li>
 *   <li>Expression statements → {@code DISCARD} (role
 *       {@code SYNTHETIC}).</li>
 *   <li>Every lowered function's block table passes
 *       {@link ControlFlowValidator} (tree, dominance, exits); mutated
 *       units — an op after a terminator, a {@code BREAK} targeting a
 *       non-loop, an orphan block — fail E6005
 *       {@code CONTROL_BLOCK_TREE}/{@code CONTROL_EXIT}.</li>
 *   <li>T2 composition: a while condition block carrying an
 *       assignment chain (receiver/key/RHS) lowers with the chain's
 *       child order intact inside the block and the whole unit validates
 *       end-to-end.</li>
 *   <li>Coverage: {@code constructCoverage} carries the extended
 *       detector rows for the lowered constructs; no new
 *       {@code ConstructKind} values are introduced.</li>
 *   <li>Determinism: repeated lowering produces byte-identical
 *       {@code deal.semantic-ir/1} dumps.</li>
 * </ol>
 */
public class ControlFlowLoweringTest {

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
            new ExternalModuleInterface(MODULE, ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal").parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver("test.deal", (ModuleResolver) null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check("test.deal", symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), "the slice checks cleanly: " + result.diagnostics());
        if (!result.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of("test.deal"), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    /** The foundation detector's recorded coverage rows for the slice. */
    private static Map<ConstructKind, List<SemanticOpKind>> detectedCoverage(
            CheckedSlice slice) {
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        ModuleFact fact = new ModuleFact(SOURCE_ID, MODULE, false, false, slice.program(),
            Map.of(), slice.symbols(), slice.checks(), List.of());
        deal.semantic.CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation,
            MODULE, List.of(fact));
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            "the checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return Map.of();
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests() != null && manifests.manifests().size() == 1,
            "the foundation detector produces exactly one requirement manifest: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests() == null || manifests.manifests().size() != 1) {
            return Map.of();
        }
        return manifests.manifests().get(0).constructCoverage();
    }

    private static SemanticLowerer.LoweringResult lower(CheckedSlice slice,
            Map<ConstructKind, List<SemanticOpKind>> coverage) {
        return SemanticLowerer.lowerModule(moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32,
            coverage, INTERFACE_HASH, REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
    }

    private static SemanticLowerer.LoweringResult lowerDetected(CheckedSlice slice) {
        return lower(slice, detectedCoverage(slice));
    }

    // =========================================================================
    // Finders (source-order walks)
    // =========================================================================

    private static <T> T first(ProgramNode program, Class<T> kind) {
        List<StatementNode> statements = new ArrayList<>();
        List<ExpressionNode> expressions = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            collect(statement, statements, expressions);
        }
        for (StatementNode statement : statements) {
            if (kind.isInstance(statement)) {
                return kind.cast(statement);
            }
        }
        for (ExpressionNode expression : expressions) {
            if (kind.isInstance(expression)) {
                return kind.cast(expression);
            }
        }
        return null;
    }

    private static void collect(StatementNode statement, List<StatementNode> statements,
                                List<ExpressionNode> expressions) {
        statements.add(statement);
        switch (statement) {
            case Block block -> {
                for (StatementNode child : block.statements()) {
                    collect(child, statements, expressions);
                }
            }
            case IfStatement ifStatement -> {
                collectExpression(ifStatement.condition(), expressions);
                for (StatementNode child : ifStatement.thenBlock().statements()) {
                    collect(child, statements, expressions);
                }
                ifStatement.elseBranch().ifPresent(branch -> {
                    switch (branch) {
                        case deal.ast.Either.Left<IfStatement, Block> left ->
                            collect(left.value(), statements, expressions);
                        case deal.ast.Either.Right<IfStatement, Block> right -> {
                            for (StatementNode child : right.value().statements()) {
                                collect(child, statements, expressions);
                            }
                        }
                    }
                });
            }
            case WhileStatement whileStatement -> {
                collectExpression(whileStatement.condition(), expressions);
                for (StatementNode child : whileStatement.body().statements()) {
                    collect(child, statements, expressions);
                }
            }
            case ForStatement forStatement -> {
                forStatement.init().ifPresent(init -> {
                    switch (init) {
                        case deal.ast.ForInit.AssignExpr assign ->
                            collectExpression(assign.expr(), expressions);
                        case deal.ast.ForInit.VarDecl decl ->
                            collectExpression(decl.decl().initializer(), expressions);
                    }
                });
                forStatement.condition().ifPresent(condition ->
                    collectExpression(condition, expressions));
                forStatement.update().ifPresent(update ->
                    collectExpression(update, expressions));
                for (StatementNode child : forStatement.body().statements()) {
                    collect(child, statements, expressions);
                }
            }
            case ForOfStatement forOf -> {
                collectExpression(forOf.iterable(), expressions);
                for (StatementNode child : forOf.body().statements()) {
                    collect(child, statements, expressions);
                }
            }
            case TryStatement tryStatement -> {
                for (StatementNode child : tryStatement.tryBlock().statements()) {
                    collect(child, statements, expressions);
                }
                for (StatementNode child : tryStatement.catchBlock().statements()) {
                    collect(child, statements, expressions);
                }
            }
            case ThrowStatement throwStatement ->
                collectExpression(throwStatement.expr(), expressions);
            case ExpressionStatement expressionStatement ->
                collectExpression(expressionStatement.expr(), expressions);
            case BreakStatement ignoredBreak -> {
                // no sub-constructs
            }
            case ContinueStatement ignoredContinue -> {
                // no sub-constructs
            }
            default -> {
                // other statements (function/class/import/export/delete/return)
            }
        }
    }

    private static void collectExpression(ExpressionNode expression,
                                          List<ExpressionNode> expressions) {
        expressions.add(expression);
        switch (expression) {
            case BinaryExpr binary -> {
                collectExpression(binary.left(), expressions);
                collectExpression(binary.right(), expressions);
            }
            case AssignmentExpr assignment -> {
                collectExpression(assignment.target(), expressions);
                collectExpression(assignment.value(), expressions);
            }
            case MemberAccessExpr access -> collectExpression(access.object(), expressions);
            case deal.ast.IndexExpr index -> {
                collectExpression(index.array(), expressions);
                collectExpression(index.index(), expressions);
            }
            case deal.ast.ArrayLiteralExpr array -> {
                for (ExpressionNode element : array.elements()) {
                    collectExpression(element, expressions);
                }
            }
            case deal.ast.ObjectLiteralExpr object -> {
                for (deal.ast.Property property : object.properties()) {
                    collectExpression(property.value(), expressions);
                }
            }
            case deal.ast.TemplateLiteralExpr template -> {
                for (ExpressionNode part : template.parts()) {
                    collectExpression(part, expressions);
                }
            }
            case deal.ast.UnaryExpr unary -> collectExpression(unary.expr(), expressions);
            case deal.ast.CallExpr call -> {
                collectExpression(call.callee(), expressions);
                for (ExpressionNode argument : call.args()) {
                    collectExpression(argument, expressions);
                }
            }
            default -> {
                // literals and identifiers carry no sub-expressions
            }
        }
    }

    private static SemanticOp opById(List<SemanticOp> ops, OpId id) {
        for (SemanticOp op : ops) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    private static void checkOrigin(String what, SemanticOp op, Span expected,
                                    SourceOriginKind kind, OpId parent) {
        check(SOURCE_ID.equals(op.origin().sourceId()),
            what + " origin sourceId is the module's stable source identity");
        check(expected.file().equals(op.origin().span().file())
                && op.origin().span().startLine() == expected.startLine()
                && op.origin().span().startColumn() == expected.startColumn(),
            what + " origin span starts at the statement's span");
        check(op.origin().kind() == kind,
            what + " origin kind " + op.origin().kind() + " == " + kind);
        check(java.util.Objects.equals(op.origin().parentOpId(), parent),
            what + " origin parentOpId " + op.origin().parentOpId() + " == " + parent);
    }

    private static void checkNoResult(String what, SemanticOp op) {
        check(op.result() == null && op.resultType() == null,
            what + " publishes no result (result/resultType none)");
    }

    // =========================================================================
    // 1. BRANCH(IF)
    // =========================================================================

    static void testIfBranchArm() {
        System.out.println("-- BRANCH(IF): condition, selected/alternate blocks --");

        CheckedSlice slice = checkSlice("if ({flag: true}.flag) { \"a\"; } else { \"b\"; }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors() && result.unit() != null,
            "the if/else slice lowers to a validated unit: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors() || result.unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.unit();
        List<SemanticOp> ops = unit.ops();
        List<SemanticOp> branches = ofKind(ops, SemanticOpKind.BRANCH);
        check(branches.size() == 1, "exactly one BRANCH op; got " + branches.size());
        if (branches.size() != 1) {
            return;
        }
        SemanticOp branch = branches.get(0);
        KindPayload.BranchPayload payload = (KindPayload.BranchPayload) branch.payload();
        check(payload.selector() == ControlSelector.IF,
            "the BRANCH selector is IF");
        check(branch.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the BRANCH carries NO_DEAL_FAILURE");
        checkNoResult("BRANCH(IF)", branch);

        // The condition's producing ops complete in the enclosing block
        // before the BRANCH op: CONST(true), TABLE_NEW, MEMBER_READ,
        // CONTEXTUAL_TABLE_READ child — all members of the module-init
        // block, emitted before the BRANCH op.
        int branchIndex = ops.indexOf(branch);
        SemanticOp memberRead = ofKind(ops, SemanticOpKind.MEMBER_READ).get(0);
        check(payload.condition().equals(memberRead.result()),
            "the BRANCH condition is the MEMBER_READ result (the if-condition)");
        check(ops.indexOf(memberRead) < branchIndex,
            "the condition's producing ops precede the BRANCH op in the unit list");
        StructuredBodyTable table = result.table();
        BlockId moduleInit = unit.moduleInit().initBlock();
        check(table.blockOps().get(moduleInit).contains(memberRead.opId())
                && table.blockOps().get(moduleInit).contains(branch.opId()),
            "the condition ops and the BRANCH op are members of the module-init block");

        // Block membership: selected = the then-block, alternate = the
        // else-block; each carries exactly its DISCARD statement.
        BlockId selected = payload.selectedBlock();
        BlockId alternate = payload.alternateBlock();
        check(selected != null && alternate != null,
            "the if/else shape carries both block ids");
        List<OpId> selectedOps = table.blockOps().get(selected);
        List<OpId> alternateOps = table.blockOps().get(alternate);
        check(selectedOps.size() == 2 && alternateOps.size() == 2,
            "each child block carries its two statement ops (CONST + DISCARD)");
        for (OpId id : selectedOps) {
            SemanticOp op = opById(ops, id);
            check(branch.opId().equals(op.origin().parentOpId()),
                "selected-block op records the BRANCH as parentOpId");
        }
        for (OpId id : alternateOps) {
            SemanticOp op = opById(ops, id);
            check(branch.opId().equals(op.origin().parentOpId()),
                "alternate-block op records the BRANCH as parentOpId");
        }
        IfStatement statement = first(slice.program(), IfStatement.class);
        checkOrigin("BRANCH", branch, statement.span(), SourceOriginKind.USER, null);

        // Else-less shape: alternateBlock null.
        CheckedSlice noElse = checkSlice("if (true) {}");
        if (noElse != null) {
            SemanticLowerer.LoweringResult noElseResult = lowerDetected(noElse);
            check(noElseResult != null && !noElseResult.hasErrors(),
                "the else-less if lowers: "
                    + (noElseResult == null ? "null" : noElseResult.diagnostics()));
            if (noElseResult != null && !noElseResult.hasErrors()) {
                KindPayload.BranchPayload noElsePayload =
                    (KindPayload.BranchPayload) ofKind(noElseResult.unit().ops(),
                        SemanticOpKind.BRANCH).get(0).payload();
                check(noElsePayload.alternateBlock() == null,
                    "an absent else produces alternateBlock = null");
                check(noElseResult.table().blockOps().get(noElsePayload.selectedBlock())
                        .isEmpty(),
                    "the empty then-block is an empty block of the table");
            }
        }
    }

    static void testIfElseChainArm() {
        System.out.println("-- BRANCH(IF): else-if chains nest in the alternate block --");

        CheckedSlice slice = checkSlice(
            "if (true) {} else if (false) { \"x\"; } else {}");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the else-if chain lowers: " + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> branches = ofKind(result.unit().ops(), SemanticOpKind.BRANCH);
        check(branches.size() == 2,
            "the else-if chain produces exactly two BRANCH ops; got " + branches.size());
        if (branches.size() != 2) {
            return;
        }
        SemanticOp outer = branches.get(0);
        SemanticOp inner = branches.get(1);
        KindPayload.BranchPayload outerPayload = (KindPayload.BranchPayload) outer.payload();
        KindPayload.BranchPayload innerPayload = (KindPayload.BranchPayload) inner.payload();
        check(outerPayload.alternateBlock() != null,
            "the outer BRANCH carries an alternate block (the else-if)");
        check(result.table().blockOps().get(outerPayload.alternateBlock())
                .contains(inner.opId()),
            "the inner BRANCH op is a member of the outer's alternate block");
        check(outer.opId().equals(inner.origin().parentOpId()),
            "the inner BRANCH records the outer BRANCH as parentOpId");
        check(innerPayload.selector() == ControlSelector.IF
                && innerPayload.alternateBlock() != null,
            "the inner BRANCH is IF with the final else as its alternate block");
    }

    // =========================================================================
    // 2. BRANCH(LOGICAL_AND/LOGICAL_OR) — short circuit
    // =========================================================================

    static void testLogicalShortCircuitArm() {
        System.out.println("-- BRANCH(LOGICAL_AND/OR): right ops in selectedBlock only --");

        CheckedSlice slice = checkSlice(
            "(({a: true}).a = false) && (({b: true}).b = false);");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the && slice lowers: " + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> branches = ofKind(ops, SemanticOpKind.BRANCH);
        check(branches.size() == 1, "exactly one BRANCH op; got " + branches.size());
        if (branches.size() != 1) {
            return;
        }
        SemanticOp branch = branches.get(0);
        KindPayload.BranchPayload payload = (KindPayload.BranchPayload) branch.payload();
        check(payload.selector() == ControlSelector.LOGICAL_AND,
            "the selector is LOGICAL_AND");
        check(payload.alternateBlock() == null,
            "the logical BRANCH carries no alternate block");
        check(branch.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the logical BRANCH carries NO_DEAL_FAILURE");

        // The left operand (the condition) is the left chain's committed
        // value; the op's result is the right operand's value identity
        // with the boolean result type.
        List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
        check(assigns.size() == 2, "the two assignment chains produce two ASSIGN ops");
        SemanticOp leftAssign = assigns.get(0);
        SemanticOp rightAssign = assigns.get(1);
        check(payload.condition().equals(leftAssign.result()),
            "the BRANCH condition is the left operand's producing value");
        check(branch.result().equals(rightAssign.result()),
            "the BRANCH result is the right operand's value identity (the right chain's "
                + "committed value)");
        check(branch.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE),
            "the BRANCH resultType is D(boolean) — a boolean either way");

        // The right operand's producing ops live in selectedBlock only and
        // execute only when the left value does not decide the result.
        StructuredBodyTable table = result.table();
        List<OpId> selectedOps = table.blockOps().get(payload.selectedBlock());
        check(selectedOps.contains(rightAssign.opId()),
            "the right chain op is a member of the selected block");
        check(!selectedOps.contains(leftAssign.opId()),
            "the left chain op is not a member of the selected block");
        BlockId moduleInit = result.unit().moduleInit().initBlock();
        check(table.blockOps().get(moduleInit).contains(branch.opId())
                && table.blockOps().get(moduleInit).contains(leftAssign.opId()),
            "the BRANCH op and the left operand ops are members of the enclosing block");
        for (OpId id : selectedOps) {
            SemanticOp op = opById(ops, id);
            if (op.kind() == SemanticOpKind.ASSIGN) {
                check(branch.opId().equals(op.origin().parentOpId()),
                    "the right chain op records the BRANCH as parentOpId (a block op of the "
                        + "selected block)");
            } else {
                check(rightAssign.opId().equals(op.origin().parentOpId()),
                    "the right chain's children record the chain ASSIGN as parentOpId "
                        + "(A-D2 — chain parentage wins over the block parent)");
            }
        }
        int branchIndex = ops.indexOf(branch);
        check(ops.indexOf(leftAssign) < branchIndex && branchIndex < ops.indexOf(rightAssign),
            "the unit list order is left ops, BRANCH, right ops (the BRANCH precedes its "
                + "child block)");
        check(ofKind(ops, SemanticOpKind.DISCARD).size() == 1,
            "the expression statement produces exactly one DISCARD");
        SemanticOp discard = ofKind(ops, SemanticOpKind.DISCARD).get(0);
        check(branch.result().equals(((KindPayload.DiscardPayload) discard.payload()).value()),
            "the DISCARD consumes the BRANCH's published boolean result");

        // The OR row.
        CheckedSlice orSlice = checkSlice(
            "(({a: false}).a = true) || (({b: false}).b = true);");
        if (orSlice != null) {
            SemanticLowerer.LoweringResult orResult = lowerDetected(orSlice);
            check(orResult != null && !orResult.hasErrors(),
                "the || slice lowers: "
                    + (orResult == null ? "null" : orResult.diagnostics()));
            if (orResult != null && !orResult.hasErrors()) {
                SemanticOp orBranch = ofKind(orResult.unit().ops(), SemanticOpKind.BRANCH)
                    .get(0);
                check(((KindPayload.BranchPayload) orBranch.payload()).selector()
                        == ControlSelector.LOGICAL_OR,
                    "the || selector is LOGICAL_OR");
                check(orBranch.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE),
                    "the || BRANCH resultType is D(boolean)");
            }
        }
    }

    static void testLogicalChainedNesting() {
        System.out.println("-- BRANCH(LOGICAL_*): chained nesting in source order --");

        CheckedSlice slice = checkSlice(
            "(({a: true}).a = false) && (({b: true}).b = false)"
                + " && (({c: true}).c = false);");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the chained && slice lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> branches = ofKind(ops, SemanticOpKind.BRANCH);
        check(branches.size() == 2, "the chained && produces exactly two nested BRANCH ops");
        if (branches.size() != 2) {
            return;
        }
        // The && chain is left-associative: a && b && c parses as
        // (a && b) && c, so the unit list carries the inner BRANCH (a &&
        // b) first, then the outer BRANCH whose left operand is the inner
        // BRANCH's result and whose selectedBlock carries the third
        // chain's ops only (nesting in source order).
        SemanticOp inner = branches.get(0);
        SemanticOp outer = branches.get(1);
        check(ops.indexOf(inner) < ops.indexOf(outer),
            "the inner BRANCH precedes the outer BRANCH in the unit list (source order)");
        KindPayload.BranchPayload outerPayload = (KindPayload.BranchPayload) outer.payload();
        KindPayload.BranchPayload innerPayload = (KindPayload.BranchPayload) inner.payload();
        check(result.table().blockOps().get(result.unit().moduleInit().initBlock())
                .contains(inner.opId()),
            "the inner BRANCH is a member of the enclosing block (the outer's left "
                + "operand, completed before the outer's START)");
        check(result.table().blockOps().get(outerPayload.selectedBlock())
                .contains(ofKind(ops, SemanticOpKind.ASSIGN).get(2).opId()),
            "the third chain's ops live in the outer's selectedBlock only");
        check(!result.table().blockOps().get(outerPayload.selectedBlock())
                .contains(inner.opId()),
            "the inner BRANCH is not a member of the outer's selectedBlock");
        check(outer.result().equals(ofKind(ops, SemanticOpKind.ASSIGN).get(2).result()),
            "the outer BRANCH result is the third chain's committed value (the right "
                + "operand's value identity)");
        check(outer.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE)
                && inner.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE),
            "both BRANCH results carry D(boolean)");
        List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
        check(assigns.size() == 3, "the three chains produce three ASSIGN ops");
        check(innerPayload.condition().equals(assigns.get(0).result()),
            "the inner BRANCH condition is the first chain's value");
        check(outerPayload.condition().equals(inner.result()),
            "the outer BRANCH condition is the inner BRANCH's result (the left operand "
                + "value identity)");
        check(inner.result().equals(assigns.get(1).result()),
            "the inner BRANCH result is the second chain's committed value (its right "
                + "operand identity)");
    }

    // =========================================================================
    // 3. LOOP(WHILE) / LOOP(FOR) / test-less FOR
    // =========================================================================

    static void testWhileArm() {
        System.out.println("-- LOOP(WHILE): condition block in initBlock, updateBlock null --");

        CheckedSlice slice = checkSlice("while (({b: true}).b = false) {}");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the while slice lowers: " + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> loops = ofKind(ops, SemanticOpKind.LOOP);
        check(loops.size() == 1, "exactly one LOOP op; got " + loops.size());
        if (loops.size() != 1) {
            return;
        }
        SemanticOp loop = loops.get(0);
        KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
        check(payload.selector() == ControlSelector.WHILE,
            "the LOOP selector is WHILE");
        check(payload.updateBlock() == null,
            "the WHILE updateBlock is null");
        check(loop.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the LOOP carries NO_DEAL_FAILURE");
        checkNoResult("LOOP(WHILE)", loop);

        // initBlock is the per-iteration condition block: the condition
        // chain's producing ops are its explicit members; bodyBlock is the
        // (empty) body block.
        StructuredBodyTable table = result.table();
        BlockId initBlock = payload.initBlock();
        BlockId bodyBlock = payload.bodyBlock();
        check(initBlock != null && !initBlock.equals(bodyBlock),
            "the WHILE carries distinct init/body blocks");
        List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
        check(assigns.size() == 1, "the condition chain produces one ASSIGN op");
        check(payload.condition().equals(assigns.get(0).result()),
            "the LOOP condition is the condition chain's committed value");
        List<OpId> initOps = table.blockOps().get(initBlock);
        check(initOps.contains(assigns.get(0).opId()),
            "the init block carries the condition chain's ASSIGN op");
        check(initOps.size() == 5,
            "the init block carries exactly the condition chain's five ops "
                + "(CONST true, TABLE_NEW, CONST false, MEMBER_WRITE, ASSIGN); got "
                + initOps.size());
        check(table.blockOps().get(bodyBlock).isEmpty(),
            "the empty body block is an empty block of the table");
        check(table.blockOps().get(result.unit().moduleInit().initBlock())
                .contains(loop.opId()),
            "the LOOP op is a member of the module-init block");
        for (OpId id : initOps) {
            SemanticOp op = opById(ops, id);
            if (op.kind() == SemanticOpKind.ASSIGN) {
                check(loop.opId().equals(op.origin().parentOpId()),
                    "the condition chain op records the LOOP as parentOpId (a block op of "
                        + "the condition block)");
            } else {
                check(assigns.get(0).opId().equals(op.origin().parentOpId()),
                    "the chain child records the ASSIGN as parentOpId (A-D2 — chain "
                        + "parentage wins over the block parent)");
            }
        }
        int loopIndex = ops.indexOf(loop);
        check(loopIndex == 0, "the LOOP op precedes its child block ops in the unit list");
        WhileStatement statement = first(slice.program(), WhileStatement.class);
        checkOrigin("LOOP(WHILE)", loop, statement.span(), SourceOriginKind.USER, null);
    }

    static void testForArm() {
        System.out.println("-- LOOP(FOR): init + first condition production, update + re-test --");

        CheckedSlice slice = checkSlice(
            "for (({i: 0}).i = 0; ({c: true}).c; ({u: 0}).u = 0) {}");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the for slice lowers: " + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> loops = ofKind(ops, SemanticOpKind.LOOP);
        check(loops.size() == 1, "exactly one LOOP op; got " + loops.size());
        if (loops.size() != 1) {
            return;
        }
        SemanticOp loop = loops.get(0);
        KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
        check(payload.selector() == ControlSelector.FOR,
            "the LOOP selector is FOR");
        check(payload.initBlock() != null && payload.bodyBlock() != null
                && payload.updateBlock() != null,
            "the FOR carries init/body/update block ids");
        check(loop.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the LOOP carries NO_DEAL_FAILURE");
        checkNoResult("LOOP(FOR)", loop);

        StructuredBodyTable table = result.table();
        List<OpId> initOps = table.blockOps().get(payload.initBlock());
        List<OpId> updateOps = table.blockOps().get(payload.updateBlock());

        // initBlock = init chain (5 ops) + first condition production
        // (CONST, TABLE_NEW, MEMBER_READ, CONTEXTUAL_TABLE_READ child).
        check(initOps.size() == 9,
            "initBlock carries the init chain (5 ops) + the first condition production "
                + "(4 ops); got " + initOps.size());
        check(updateOps.size() == 9,
            "updateBlock carries the update chain (5 ops) + the condition re-production "
                + "(4 ops); got " + updateOps.size());
        List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
        check(assigns.size() == 2, "the init and update chains produce two ASSIGN ops");
        check(initOps.contains(assigns.get(0).opId()),
            "the init chain op is a member of initBlock");
        check(updateOps.contains(assigns.get(1).opId()),
            "the update chain op is a member of updateBlock");
        check(initOps.indexOf(assigns.get(0).opId()) < initOps.size() - 4
                && updateOps.indexOf(assigns.get(1).opId()) < updateOps.size() - 4,
            "the update ops precede the condition productions inside each block "
                + "(update then re-test)");

        // The condition ValueId: one identity, re-produced by the
        // updateBlock production (two producing ops publish it).
        List<SemanticOp> reads = ofKind(ops, SemanticOpKind.MEMBER_READ);
        check(reads.size() == 2, "the condition lowers to exactly two MEMBER_READ ops");
        check(reads.get(0).result().equals(reads.get(1).result()),
            "both condition productions publish the same condition ValueId (one identity, "
                + "re-produced per iteration)");
        check(payload.condition().equals(reads.get(0).result()),
            "the payload condition is the shared condition ValueId");
        check(initOps.contains(reads.get(0).opId())
                && updateOps.contains(reads.get(1).opId()),
            "the first production is an initBlock member and the re-production is an "
                + "updateBlock member");
        for (SemanticOp read : reads) {
            check(loop.opId().equals(read.origin().parentOpId()),
                "each condition production records the LOOP as parentOpId");
        }
        check(table.blockOps().get(payload.bodyBlock()).isEmpty(),
            "the empty body block is an empty block of the table");
        check(ops.indexOf(loop) == 0,
            "the LOOP op precedes its child block ops in the unit list");
        check(ops.indexOf(reads.get(0)) < ops.indexOf(reads.get(1)),
            "the first condition production precedes the re-production in the unit list");
        ForStatement statement = first(slice.program(), ForStatement.class);
        checkOrigin("LOOP(FOR)", loop, statement.span(), SourceOriginKind.USER, null);
    }

    static void testTestlessForArm() {
        System.out.println("-- Test-less FOR: one CONST true in initBlock, update ops only --");

        CheckedSlice slice = checkSlice("for (;;) { break; }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the test-less for lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> loops = ofKind(ops, SemanticOpKind.LOOP);
        check(loops.size() == 1, "exactly one LOOP op; got " + loops.size());
        if (loops.size() != 1) {
            return;
        }
        SemanticOp loop = loops.get(0);
        KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
        check(payload.selector() == ControlSelector.FOR,
            "the LOOP selector is FOR");
        StructuredBodyTable table = result.table();
        List<OpId> initOps = table.blockOps().get(payload.initBlock());
        List<OpId> updateOps = table.blockOps().get(payload.updateBlock());
        List<OpId> bodyOps = table.blockOps().get(payload.bodyBlock());
        check(initOps.size() == 1,
            "initBlock carries exactly one op — the CONST true condition production; got "
                + initOps.size());
        SemanticOp constTrue = opById(ops, initOps.get(0));
        check(constTrue.kind() == SemanticOpKind.CONST
                && constTrue.payload() instanceof KindPayload.ConstPayload constPayload
                && constPayload.value().equals(new ScalarValue.Boolean(true)),
            "the single initBlock op is the CONST with the boolean value true");
        check(constTrue.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE),
            "the CONST true resultType is D(boolean)");
        check(constTrue.origin().kind() == SourceOriginKind.SYNTHETIC,
            "the CONST true condition production is SYNTHETIC (no source test)");
        check(payload.condition().equals(constTrue.result()),
            "the payload condition is the CONST true's result, produced once");
        check(updateOps.isEmpty(),
            "updateBlock carries only the update ops — zero for the update-less test-less "
                + "row (no condition-producing op appears)");
        check(bodyOps.size() == 1,
            "bodyBlock carries exactly the BREAK; got " + bodyOps.size());
        SemanticOp breakOp = opById(ops, bodyOps.get(0));
        check(breakOp.kind() == SemanticOpKind.BREAK,
            "the body op is the BREAK");
        check(loop.opId().equals(((KindPayload.BreakPayload) breakOp.payload()).loopId()),
            "the BREAK targets the LOOP op");
        check(loop.opId().equals(breakOp.origin().parentOpId()),
            "the BREAK records the LOOP as parentOpId");
        check(ops.indexOf(loop) == 0,
            "the LOOP op precedes its child block ops in the unit list");
    }

    static void testForEachArrayValuesArm() {
        System.out.println("-- FOR_EACH(ARRAY_VALUES): iterable once, fresh binding, break target --");

        CheckedSlice slice = checkSlice("for (let x: int of [1, 2]) { break; }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the array for-of lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> forEaches = ofKind(ops, SemanticOpKind.FOR_EACH);
        check(forEaches.size() == 1, "exactly one FOR_EACH op; got " + forEaches.size());
        if (forEaches.size() != 1) {
            return;
        }
        SemanticOp forEach = forEaches.get(0);
        KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) forEach.payload();
        check(payload.mode() == IterationMode.ARRAY_VALUES,
            "the mode is ARRAY_VALUES");
        check(forEach.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "the FOR_EACH carries TYPE_DESCRIPTOR (the op's own element terminal check)");
        checkNoResult("FOR_EACH(ARRAY_VALUES)", forEach);
        SemanticOp arrayNew = ofKind(ops, SemanticOpKind.ARRAY_NEW).get(0);
        check(payload.iterable().equals(arrayNew.result()),
            "the iterable operand is the ARRAY_NEW prior step (evaluated once before the op)");
        check(ops.indexOf(arrayNew) < ops.indexOf(forEach),
            "the iterable prior step precedes the FOR_EACH op in the unit list");
        check(payload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
            "the payload generation is the pinned initial generation (fresh binding per "
                + "iteration, mechanics E6)");
        check(payload.binding() != null, "the payload carries the loop-binding identity");
        StructuredBodyTable table = result.table();
        List<OpId> bodyOps = table.blockOps().get(payload.body());
        check(bodyOps.size() == 1, "the body block carries exactly the BREAK");
        SemanticOp breakOp = opById(ops, bodyOps.get(0));
        check(breakOp.kind() == SemanticOpKind.BREAK
                && forEach.opId().equals(
                    ((KindPayload.BreakPayload) breakOp.payload()).loopId()),
            "the BREAK targets the FOR_EACH op");
        check(forEach.opId().equals(breakOp.origin().parentOpId()),
            "the BREAK records the FOR_EACH as parentOpId");
        check(table.blockOps().get(result.unit().moduleInit().initBlock())
                .contains(forEach.opId()),
            "the FOR_EACH op is a member of the module-init block");
        ForOfStatement statement = first(slice.program(), ForOfStatement.class);
        checkOrigin("FOR_EACH", forEach, statement.span(), SourceOriginKind.USER, null);

        // A load of the loop binding inside the body resolves to the
        // payload binding with the initial generation.
        CheckedSlice loadSlice = checkSlice("for (let b: boolean of [true]) { break; }");
        if (loadSlice != null) {
            SemanticLowerer.LoweringResult loadResult = lowerDetected(loadSlice);
            check(loadResult != null && !loadResult.hasErrors(),
                "the boolean-array for-of lowers: "
                    + (loadResult == null ? "null" : loadResult.diagnostics()));
        }
    }

    // =========================================================================
    // 4. TRY_CATCH / THROW
    // =========================================================================

    static void testTryCatchThrowArm() {
        System.out.println("-- TRY_CATCH/THROW: blocks, catchBinding, THROW_TRANSFER --");

        CheckedSlice slice = checkSlice("try {} catch (e) { throw e }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the try/catch/throw slice lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> tryCatches = ofKind(ops, SemanticOpKind.TRY_CATCH);
        check(tryCatches.size() == 1, "exactly one TRY_CATCH op; got " + tryCatches.size());
        if (tryCatches.size() != 1) {
            return;
        }
        SemanticOp tryCatch = tryCatches.get(0);
        KindPayload.TryCatchPayload payload = (KindPayload.TryCatchPayload) tryCatch.payload();
        check(tryCatch.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the TRY_CATCH carries NO_DEAL_FAILURE");
        checkNoResult("TRY_CATCH", tryCatch);
        StructuredBodyTable table = result.table();
        check(table.blockOps().get(payload.tryBlock()).isEmpty(),
            "the empty try block is an empty block of the table");
        check(payload.catchBinding() != null,
            "the payload carries the producer-allocated catchBinding");

        List<OpId> catchOps = table.blockOps().get(payload.catchBlock());
        check(catchOps.size() == 3,
            "catchBlock carries the catch binding's BINDING_ALLOC, the BINDING_LOAD,"
                + " and the THROW; got " + catchOps.size());
        SemanticOp alloc = opById(ops, catchOps.get(0));
        SemanticOp load = opById(ops, catchOps.get(1));
        SemanticOp throwOp = opById(ops, catchOps.get(2));
        check(alloc.kind() == SemanticOpKind.BINDING_ALLOC,
            "the first catch-block op is the catch binding's producing ALLOC "
                + "(the catch-entry write's incarnation)");
        KindPayload.BindingAllocPayload allocPayload =
            (KindPayload.BindingAllocPayload) alloc.payload();
        check(allocPayload.binding().equals(payload.catchBinding())
                && allocPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION
                && allocPayload.cellKind() == deal.semantic.ir.BindingCellKind.DIRECT
                && allocPayload.scope().equals(payload.catchBlock()),
            "the catch ALLOC is the catch binding's {scope=catch block, generation 0, "
                + "DIRECT} incarnation");
        check(load.kind() == SemanticOpKind.BINDING_LOAD,
            "the second catch-block op is the BINDING_LOAD of the catch variable");
        KindPayload.BindingLoadPayload loadPayload = (KindPayload.BindingLoadPayload) load.payload();
        check(loadPayload.binding().equals(payload.catchBinding()),
            "the load carries the TRY_CATCH payload's catch binding");
        check(loadPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
            "the load carries the pinned initial generation");
        check(load.resultType().equals(new RuntimeDescriptor.Class(
                new deal.semantic.ir.ClassId("", "Error"))),
            "the load resultType is D(Error) (the catch variable's checked type); got "
                + load.resultType());
        check(throwOp.kind() == SemanticOpKind.THROW,
            "the third catch-block op is the THROW");
        check(throwOp.failurePolicy() == FailurePolicyId.THROW_TRANSFER,
            "the THROW carries THROW_TRANSFER (code/message preserved, origin = the THROW "
                + "origin)");
        checkNoResult("THROW", throwOp);
        check(load.result().equals(((KindPayload.ThrowPayload) throwOp.payload()).errorValue()),
            "the THROW operand is the load's produced Error value (completes before START)");
        for (SemanticOp op : List.of(alloc, load, throwOp)) {
            check(tryCatch.opId().equals(op.origin().parentOpId()),
                op.kind() + " records the TRY_CATCH as parentOpId");
        }
        TryStatement statement = first(slice.program(), TryStatement.class);
        checkOrigin("TRY_CATCH", tryCatch, statement.span(), SourceOriginKind.USER, null);
        check(ops.indexOf(tryCatch) == 0,
            "the TRY_CATCH op precedes its child block ops in the unit list");
    }

    // =========================================================================
    // 5. BREAK / CONTINUE targets
    // =========================================================================

    static void testBreakContinueTargets() {
        System.out.println("-- BREAK/CONTINUE: the recorded innermost loop --");

        CheckedSlice slice = checkSlice(
            "while (true) { while (false) { break; } continue; }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the nested-loop slice lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> loops = ofKind(ops, SemanticOpKind.LOOP);
        check(loops.size() == 2, "the nested loops produce two LOOP ops");
        if (loops.size() != 2) {
            return;
        }
        SemanticOp outer = loops.get(0);
        SemanticOp inner = loops.get(1);
        List<SemanticOp> breaks = ofKind(ops, SemanticOpKind.BREAK);
        List<SemanticOp> continues = ofKind(ops, SemanticOpKind.CONTINUE);
        check(breaks.size() == 1 && continues.size() == 1,
            "exactly one BREAK and one CONTINUE");
        check(inner.opId().equals(((KindPayload.BreakPayload) breaks.get(0).payload()).loopId()),
            "the BREAK targets the innermost (inner) LOOP");
        check(outer.opId().equals(
                ((KindPayload.ContinuePayload) continues.get(0).payload()).loopId()),
            "the CONTINUE targets the enclosing (outer) LOOP");
        check(breaks.get(0).failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE
                && continues.get(0).failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "BREAK and CONTINUE carry NO_DEAL_FAILURE");
        checkNoResult("BREAK", breaks.get(0));
        checkNoResult("CONTINUE", continues.get(0));
        StructuredBodyTable table = result.table();
        KindPayload.LoopPayload innerPayload = (KindPayload.LoopPayload) inner.payload();
        KindPayload.LoopPayload outerPayload = (KindPayload.LoopPayload) outer.payload();
        check(table.blockOps().get(innerPayload.bodyBlock())
                .contains(breaks.get(0).opId()),
            "the BREAK is a member of the inner body block");
        check(table.blockOps().get(outerPayload.bodyBlock())
                .contains(continues.get(0).opId())
                && table.blockOps().get(outerPayload.bodyBlock()).contains(inner.opId()),
            "the CONTINUE and the inner LOOP are members of the outer body block");
        check(inner.opId().equals(breaks.get(0).origin().parentOpId()),
            "the BREAK records the inner LOOP as parentOpId");
        check(outer.opId().equals(continues.get(0).origin().parentOpId()),
            "the CONTINUE records the outer LOOP as parentOpId");
        BreakStatement breakStatement = first(slice.program(), BreakStatement.class);
        checkOrigin("BREAK", breaks.get(0), breakStatement.span(), SourceOriginKind.USER,
            inner.opId());
    }

    // =========================================================================
    // 6. DISCARD
    // =========================================================================

    /**
     * The five module-level kinds outside the block-membership table (the
     * C-D1/C-D2 completeness exemption of {@code ControlFlowValidator};
     * ISSUE-0590 adds the lowerer-produced {@code MODULE_INIT} envelope).
     */
    private static final Set<SemanticOpKind> MODULE_LEVEL_KINDS = Set.of(
        SemanticOpKind.MODULE_INIT,
        SemanticOpKind.EXTERNAL_ENTRY,
        SemanticOpKind.CLASS_FACTORY,
        SemanticOpKind.CALLBACK_INVOKE,
        SemanticOpKind.ENTRY_INVOKE);

    static void testDiscardArm() {
        System.out.println("-- DISCARD: expression statements, SYNTHETIC, audited --");

        CheckedSlice slice = checkSlice("\"probe\";");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the expression-statement slice lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        // The lowerer appends one detached module-level MODULE_INIT
        // envelope op per unit (ISSUE-0590 E3/E8); the statement's own ops
        // are the CONST + DISCARD pair.
        List<SemanticOp> ops = result.unit().ops().stream()
            .filter(op -> !MODULE_LEVEL_KINDS.contains(op.kind()))
            .toList();
        check(ops.size() == 2 && ops.get(0).kind() == SemanticOpKind.CONST
                && ops.get(1).kind() == SemanticOpKind.DISCARD,
            "the slice produces exactly CONST + DISCARD; got " + ops.size());
        SemanticOp discard = ops.get(1);
        check(discard.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the DISCARD carries NO_DEAL_FAILURE");
        checkNoResult("DISCARD", discard);
        check(ops.get(0).result().equals(((KindPayload.DiscardPayload) discard.payload()).value()),
            "the DISCARD carries its expression's producing value (the CONST result)");
        check(discard.origin().kind() == SourceOriginKind.SYNTHETIC,
            "the DISCARD origin kind is SYNTHETIC (the intentional discard is audited in "
                + "the op stream and traces, never inferred away)");
        ExpressionStatement statement = first(slice.program(), ExpressionStatement.class);
        checkOrigin("DISCARD", discard, statement.span(), SourceOriginKind.SYNTHETIC, null);
    }

    // =========================================================================
    // 7. StructuredBodyTable + ControlFlowValidator (T6 combined)
    // =========================================================================

    static void testBlockTableAndValidator() {
        System.out.println("-- StructuredBodyTable production + ControlFlowValidator --");

        CheckedSlice slice = checkSlice("""
            while (({b: true}).b = false) {
              if (({f: true}).f) { "a"; }
              for (;;) { break; }
            }
            try {} catch (e) { throw e }
            for (let x: int of [1, 2]) { continue; }
            """);
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the combined corpus lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        LoweredModuleUnit unit = result.unit();
        StructuredBodyTable table = result.table();
        check(table != null, "the seam returns the produced block-membership table");

        // The produced table passes the production-time control-flow
        // validator (tree, dominance, exits).
        Optional<CompilerDiagnostic> validation = ControlFlowValidator.validate(unit, table);
        check(validation.isEmpty(),
            "the produced table passes ControlFlowValidator: " + validation);

        // C-D1: every op of the unit whose kind is not one of the five
        // module-level kinds (the validator's completeness exemption) is a
        // member of exactly one block, and the root block is the
        // module-init block.
        Map<OpId, BlockId> opBlocks = table.opBlocks();
        long functionOps = unit.ops().stream()
            .filter(op -> !MODULE_LEVEL_KINDS.contains(op.kind()))
            .count();
        for (SemanticOp op : unit.ops()) {
            if (MODULE_LEVEL_KINDS.contains(op.kind())) {
                continue;
            }
            check(opBlocks.get(op.opId()) != null,
                "op " + op.opId() + " (" + op.kind() + ") is a member of exactly one block");
        }
        check(opBlocks.size() == functionOps,
            "the inverse membership covers every produced function op exactly once");
        check(table.blockOps().containsKey(unit.moduleInit().initBlock()),
            "the module-init block (the root) is a block of the table");
        check(opBlocks.get(result.unit().ops().stream()
                .filter(op -> op.kind() == SemanticOpKind.LOOP).findFirst().get().opId())
                .equals(unit.moduleInit().initBlock()),
            "the outer LOOP op is a member of the root block");

        // Every payload-referenced block exists in the table (empty child
        // blocks included) — spot-check the structure families.
        for (SemanticOp op : unit.ops()) {
            switch (op.kind()) {
                case BRANCH -> {
                    KindPayload.BranchPayload payload =
                        (KindPayload.BranchPayload) op.payload();
                    check(table.blockOps().containsKey(payload.selectedBlock()),
                        "the BRANCH selectedBlock is a block of the table");
                }
                case LOOP -> {
                    KindPayload.LoopPayload payload = (KindPayload.LoopPayload) op.payload();
                    check(table.blockOps().containsKey(payload.initBlock())
                            && table.blockOps().containsKey(payload.bodyBlock()),
                        "the LOOP init/body blocks are blocks of the table");
                    if (payload.updateBlock() != null) {
                        check(table.blockOps().containsKey(payload.updateBlock()),
                            "the LOOP update block is a block of the table");
                    }
                }
                case FOR_EACH ->
                    check(table.blockOps().containsKey(
                            ((KindPayload.ForEachPayload) op.payload()).body()),
                        "the FOR_EACH body is a block of the table");
                case TRY_CATCH -> {
                    KindPayload.TryCatchPayload payload =
                        (KindPayload.TryCatchPayload) op.payload();
                    check(table.blockOps().containsKey(payload.tryBlock())
                            && table.blockOps().containsKey(payload.catchBlock()),
                        "every TRY_CATCH block is a block of the table");
                }
                default -> {
                    // other op families carry no block payload positions
                }
            }
        }
    }

    static void testValidatorNegatives() {
        System.out.println("-- Mutated units: E6005 CONTROL_BLOCK_TREE/CONTROL_EXIT --");

        CheckedSlice slice = checkSlice("for (;;) { break; }");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        if (result == null || result.hasErrors() || result.unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.unit();
        StructuredBodyTable table = result.table();

        // --- (a) An op after a terminator in its block: append a synthetic
        //     CONST op to the body block after the BREAK. ---
        {
            SemanticOp breakOp = ofKind(unit.ops(), SemanticOpKind.BREAK).get(0);
            OpId extraId = new OpId(MODULE, 999_999);
            SemanticOp extra = syntheticOp(extraId, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                new ValueId(999_999), RuntimeDescriptor.Int.INSTANCE,
                FailurePolicyId.NO_DEAL_FAILURE, null);
            List<SemanticOp> corruptOps = new ArrayList<>(unit.ops());
            corruptOps.add(extra);
            Map<BlockId, List<OpId>> corruptBlocks = new LinkedHashMap<>();
            for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
                List<OpId> ids = new ArrayList<>(entry.getValue());
                if (ids.contains(breakOp.opId())) {
                    ids.add(extraId);
                }
                corruptBlocks.put(entry.getKey(), ids);
            }
            StructuredBodyTable corrupt = rebuildTable(corruptBlocks, unit);
            assertControlE6005(
                ControlFlowValidator.validate(withOps(unit, corruptOps), corrupt),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "after a terminator");
        }

        // --- (b) A BREAK targeting a non-loop op. ---
        {
            SemanticOp breakOp = ofKind(unit.ops(), SemanticOpKind.BREAK).get(0);
            SemanticOp constOp = ofKind(unit.ops(), SemanticOpKind.CONST).get(0);
            SemanticOp retargeted = rebuildOp(breakOp,
                new KindPayload.BreakPayload(constOp.opId()));
            List<SemanticOp> corruptOps = new ArrayList<>(unit.ops());
            corruptOps.set(corruptOps.indexOf(breakOp), retargeted);
            assertControlE6005(
                ControlFlowValidator.validate(withOps(unit, corruptOps), table),
                ControlFlowValidator.CONTROL_EXIT, "not a LOOP or FOR_EACH");
        }

        // --- (c) An orphan block: an extra table block referenced by no
        //     payload position. ---
        {
            Map<BlockId, List<OpId>> corruptBlocks = new LinkedHashMap<>(
                table.blockOps());
            corruptBlocks.put(new BlockId(7_777), List.of());
            assertControlE6005(
                ControlFlowValidator.validate(unit, rebuildTable(corruptBlocks, unit)),
                ControlFlowValidator.CONTROL_BLOCK_TREE, "orphan block");
        }
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit, List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    private static StructuredBodyTable rebuildTable(Map<BlockId, List<OpId>> blocks,
                                                    LoweredModuleUnit unit) {
        Map<OpId, BlockId> inverse = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<OpId>> entry : blocks.entrySet()) {
            for (OpId id : entry.getValue()) {
                inverse.put(id, entry.getKey());
            }
        }
        return new StructuredBodyTable(blocks, inverse);
    }

    private static SemanticOp syntheticOp(OpId id, SemanticOpKind kind, KindPayload payload,
                                          SemanticValue result, OpResultType resultType,
                                          FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot placeholder = contractFor(kind, payload, resultType,
            List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = contractFor(kind, payload, resultType, List.of(),
            policy, digest);
        SourceOrigin origin = new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
        return new SemanticOp(id, kind, origin, result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp rebuildOp(SemanticOp original, KindPayload payload) {
        OperationContractSnapshot placeholder = contractFor(original.kind(), payload,
            original.resultType(), original.operandTypes(), original.failurePolicy(),
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = contractFor(original.kind(), payload,
            original.resultType(), original.operandTypes(), original.failurePolicy(), digest);
        return new SemanticOp(original.opId(), original.kind(), original.origin(),
            original.result(), original.resultType(), original.operands(),
            original.operandTypes(), payload, original.failurePolicy(), contract);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static void assertControlE6005(Optional<CompilerDiagnostic> diagnostic,
                                           String rule, String contains) {
        check(diagnostic.isPresent(), rule + " is rejected with E6005");
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()) && d.diagnosticCode() == DiagnosticCode.E6005
                && "error".equals(d.severity()),
            rule + " diagnostic is error-severity E6005");
        check(d.message().contains("validatorRule " + rule + ","),
            rule + " is named as the validator rule; got \"" + d.message() + "\"");
        check(d.message().contains("capability EVALUATION_ORDER"),
            rule + " message carries capability EVALUATION_ORDER");
        check(d.message().contains("ControlFlowValidator " + rule),
            rule + " message carries the ControlFlowValidator origin");
        check(d.message().contains(contains),
            rule + " message contains \"" + contains + "\"; got \"" + d.message() + "\"");
    }

    // =========================================================================
    // 8. T2 composition: chains inside blocks
    // =========================================================================

    static void testChainsInsideBlocksT2() {
        System.out.println("-- T2 composition: assignment chains inside a loop condition block --");

        // Table-index chain (receiver/key/RHS) as the while condition.
        CheckedSlice slice = checkSlice("while (({k: true})[\"k\"] = false) {}");
        if (slice == null) {
            return;
        }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors(),
            "the table-index chain condition lowers to a validated unit (validator + "
                + "address-chain protocol + control-flow validator): "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors()) {
            return;
        }
        List<SemanticOp> ops = result.unit().ops();
        List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
        check(assigns.size() == 1, "the condition chain produces one ASSIGN op");
        KindPayload.AssignPayload chainPayload =
            (KindPayload.AssignPayload) assigns.get(0).payload();
        check(chainPayload.childOps().size() == 5,
            "the chain carries its five children (containerOp, keyOp, valueOp, normalizeOp, "
                + "commitOp); got " + chainPayload.childOps().size());
        if (chainPayload.childOps().size() == 5) {
            check(opById(ops, chainPayload.childOps().get(0)).kind()
                    == SemanticOpKind.TABLE_NEW,
                "child 0 is the containerOp (the receiver TABLE_NEW)");
            check(opById(ops, chainPayload.childOps().get(1)).kind()
                    == SemanticOpKind.CONST,
                "child 1 is the keyOp (the literal string key)");
            check(opById(ops, chainPayload.childOps().get(2)).kind()
                    == SemanticOpKind.CONST,
                "child 2 is the valueOp (the RHS)");
            check(opById(ops, chainPayload.childOps().get(3)).kind()
                    == SemanticOpKind.INDEX_NORMALIZE,
                "child 3 is the normalizeOp (INDEX_NORMALIZE TABLE_WRITE)");
            check(opById(ops, chainPayload.childOps().get(4)).kind()
                    == SemanticOpKind.INDEX_WRITE,
                "child 4 is the commitOp (INDEX_WRITE, single-last commit)");
        }
        SemanticOp loop = ofKind(ops, SemanticOpKind.LOOP).get(0);
        KindPayload.LoopPayload loopPayload = (KindPayload.LoopPayload) loop.payload();
        check(loopPayload.selector() == ControlSelector.WHILE
                && loopPayload.condition().equals(assigns.get(0).result()),
            "the LOOP condition is the chain's committed value");
        List<OpId> initOps = result.table().blockOps().get(loopPayload.initBlock());
        check(initOps.size() == 7,
            "the condition block carries exactly the chain's seven ops — CONST(true) "
                + "receiver entry, TABLE_NEW containerOp, CONST keyOp, CONST valueOp, "
                + "INDEX_NORMALIZE, INDEX_WRITE, ASSIGN; got " + initOps.size());
        for (OpId childId : chainPayload.childOps()) {
            check(initOps.contains(childId),
                "chain child " + opById(ops, childId).kind() + " is a member of the "
                    + "condition block");
        }
        for (int i = 1; i < chainPayload.childOps().size(); i++) {
            check(initOps.indexOf(chainPayload.childOps().get(i - 1))
                    < initOps.indexOf(chainPayload.childOps().get(i)),
                "chain children appear in payload order inside the condition block");
        }
        check(initOps.contains(assigns.get(0).opId())
                && initOps.indexOf(chainPayload.childOps().get(
                    chainPayload.childOps().size() - 1)) < initOps.indexOf(
                        assigns.get(0).opId()),
            "the ASSIGN op is the last chain op of the condition block");
        for (OpId childId : chainPayload.childOps()) {
            check(assigns.get(0).opId().equals(opById(ops, childId).origin().parentOpId()),
                "chain child records the ASSIGN as parentOpId (child order intact inside "
                    + "the block)");
        }
        check(loop.opId().equals(assigns.get(0).origin().parentOpId()),
            "the ASSIGN op records the LOOP as parentOpId (a block op of the condition "
                + "block)");

        // Array chain (receiver/key/RHS + length read) as the condition.
        CheckedSlice arraySlice = checkSlice("while (([true])[0] = false) {}");
        if (arraySlice != null) {
            SemanticLowerer.LoweringResult arrayResult = lowerDetected(arraySlice);
            check(arrayResult != null && !arrayResult.hasErrors(),
                "the array-index chain condition lowers to a validated unit: "
                    + (arrayResult == null ? "null" : arrayResult.diagnostics()));
            if (arrayResult != null && !arrayResult.hasErrors()) {
                List<SemanticOp> arrayOps = arrayResult.unit().ops();
                KindPayload.AssignPayload arrayChain = (KindPayload.AssignPayload) ofKind(
                    arrayOps, SemanticOpKind.ASSIGN).get(0).payload();
                check(arrayChain.childOps().size() == 7,
                    "the array chain carries its seven children (containerOp, keyOp, "
                        + "valueOp, lengthOp, normalizeOp, boundaryOp, commitOp); got "
                        + arrayChain.childOps().size());
                SemanticOp arrayLoop = ofKind(arrayOps, SemanticOpKind.LOOP).get(0);
                KindPayload.LoopPayload arrayPayload =
                    (KindPayload.LoopPayload) arrayLoop.payload();
                check(arrayResult.table().blockOps().get(arrayPayload.initBlock())
                        .contains(arrayChain.childOps().get(0)),
                    "the array chain's children are members of the condition block");
            }
        }
    }

    // =========================================================================
    // 9. Coverage rows + determinism
    // =========================================================================

    static void testCoverageRows() {
        System.out.println("-- Detector coverage rows for the lowered constructs --");

        // The closed ConstructKind set carries no new values (the fixed
        // rows are extended, never the set).
        check(ConstructKind.values().length == 23,
            "the closed ConstructKind set carries exactly its 23 pinned values; got "
                + ConstructKind.values().length);

        CheckedSlice slice = checkSlice("""
            if (true) {}
            while (false) { break; }
            for (;;) { continue; }
            for (let x: int of [1]) {}
            try {} catch (e) { throw e }
            "probe";
            """);
        if (slice == null) {
            return;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage = detectedCoverage(slice);
        check(coverage.containsKey(ConstructKind.IF_WHILE_FOR_FOR_OF)
                && coverage.containsKey(ConstructKind.BREAK_CONTINUE)
                && coverage.containsKey(ConstructKind.TRY_CATCH_THROW)
                && coverage.containsKey(ConstructKind.RETURN_EXPRESSION_STATEMENT),
            "the detector records the extended rows for the lowered constructs: "
                + coverage.keySet());
        for (ConstructKind row : List.of(ConstructKind.IF_WHILE_FOR_FOR_OF,
                ConstructKind.BREAK_CONTINUE, ConstructKind.TRY_CATCH_THROW,
                ConstructKind.RETURN_EXPRESSION_STATEMENT)) {
            check(coverage.containsKey(row)
                    && coverage.get(row).equals(row.mappedOpKinds()),
                "the recorded " + row + " row carries the closed construct→op detector "
                    + "table verbatim");
        }
        check(coverage.get(ConstructKind.IF_WHILE_FOR_FOR_OF)
                .equals(List.of(SemanticOpKind.BRANCH, SemanticOpKind.LOOP,
                    SemanticOpKind.FOR_EACH)),
            "IF_WHILE_FOR_FOR_OF maps to [BRANCH, LOOP, FOR_EACH]");
        check(coverage.get(ConstructKind.BREAK_CONTINUE)
                .equals(List.of(SemanticOpKind.BREAK, SemanticOpKind.CONTINUE)),
            "BREAK_CONTINUE maps to [BREAK, CONTINUE]");
        check(coverage.get(ConstructKind.TRY_CATCH_THROW)
                .equals(List.of(SemanticOpKind.TRY_CATCH, SemanticOpKind.THROW)),
            "TRY_CATCH_THROW maps to [TRY_CATCH, THROW]");
        check(coverage.get(ConstructKind.RETURN_EXPRESSION_STATEMENT)
                .equals(List.of(SemanticOpKind.RETURN, SemanticOpKind.DISCARD)),
            "RETURN_EXPRESSION_STATEMENT maps to [RETURN, DISCARD]");

        // The whole slice lowers with the detected rows end-to-end
        // (R-COVERAGE green on the real produced op set).
        SemanticLowerer.LoweringResult result = lower(slice, coverage);
        check(result != null && !result.hasErrors() && result.unit() != null,
            "the multi-construct slice lowers with the detected rows end-to-end: "
                + (result == null ? "null" : result.diagnostics()));
        if (result != null && !result.hasErrors() && result.unit() != null) {
            for (SemanticOpKind kind : List.of(SemanticOpKind.BRANCH, SemanticOpKind.LOOP,
                    SemanticOpKind.FOR_EACH, SemanticOpKind.BREAK,
                    SemanticOpKind.CONTINUE, SemanticOpKind.TRY_CATCH,
                    SemanticOpKind.THROW, SemanticOpKind.DISCARD)) {
                check(!ofKind(result.unit().ops(), kind).isEmpty(),
                    "the slice produces at least one " + kind + " op");
            }
            // The EVALUATION_ORDER claim: the slice fully evidences
            // {BRANCH, LOOP, DISCARD} and claims EVALUATION_ORDER at E5's
            // gate.
            check(result.unit().requiredCapabilities()
                    .contains(SemanticCapability.EVALUATION_ORDER),
                "the slice's unit claims EVALUATION_ORDER (BRANCH + LOOP + DISCARD fully "
                    + "evidence the row at E5's gate); got "
                    + result.unit().requiredCapabilities());
        }
    }

    static void testDeterminism() {
        System.out.println("-- Determinism: byte-identical repeated lowerings --");

        CheckedSlice slice = checkSlice("""
            while (({b: true}).b = false) {
              if (({f: true}).f) { "a"; }
              for (;;) { break; }
            }
            try {} catch (e) { throw e }
            for (let x: int of [1, 2]) { continue; }
            """);
        if (slice == null) {
            return;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage = detectedCoverage(slice);
        SemanticLowerer.LoweringResult first = lower(slice, coverage);
        SemanticLowerer.LoweringResult second = lower(slice, coverage);
        check(first != null && !first.hasErrors() && second != null && !second.hasErrors(),
            "both lowerings validate: " + (first == null ? "null" : first.diagnostics())
                + " / " + (second == null ? "null" : second.diagnostics()));
        if (first == null || first.hasErrors() || second == null || second.hasErrors()) {
            return;
        }
        byte[] firstDump = SemanticIrDumper.dumpModule(first.unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.unit());
        check(Arrays.equals(firstDump, secondDump) && firstDump.length > 0,
            "two fresh lowerings produce byte-identical deal.semantic-ir/1 dumps (D8); "
                + firstDump.length + " bytes");
        check(SemanticIrDumper.dumpModuleText(first.unit())
                .equals(SemanticIrDumper.dumpModuleText(second.unit())),
            "two fresh lowerings produce byte-identical dump text");
        List<String> firstDigests = new ArrayList<>();
        List<String> secondDigests = new ArrayList<>();
        for (SemanticOp op : first.unit().ops()) {
            firstDigests.add(op.contract().canonicalDigest());
        }
        for (SemanticOp op : second.unit().ops()) {
            secondDigests.add(op.contract().canonicalDigest());
        }
        check(firstDigests.equals(secondDigests) && !firstDigests.isEmpty(),
            "canonical contract digests are byte-identical across the two repetitions");
        check(first.unit().requiredCapabilities()
                .equals(second.unit().requiredCapabilities()),
            "the repeated unit's claim set is identical");
        check(ControlFlowValidator.validate(first.unit(), first.table()).isEmpty()
                && ControlFlowValidator.validate(second.unit(), second.table()).isEmpty(),
            "both produced tables pass ControlFlowValidator");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Control Flow Lowering Test (ISSUE-0409) ===\n");

        testIfBranchArm();
        testIfElseChainArm();
        testLogicalShortCircuitArm();
        testLogicalChainedNesting();
        testWhileArm();
        testForArm();
        testTestlessForArm();
        testForEachArrayValuesArm();
        testTryCatchThrowArm();
        testBreakContinueTargets();
        testDiscardArm();
        testBlockTableAndValidator();
        testValidatorNegatives();
        testChainsInsideBlocksT2();
        testCoverageRows();
        testDeterminism();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
