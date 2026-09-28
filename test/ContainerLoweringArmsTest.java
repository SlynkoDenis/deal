package deal.test;

import deal.ast.AwaitExpression;
import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ContinueStatement;
import deal.ast.DeleteStatement;
import deal.ast.Either;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.HasExpr;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.ImportDeclaration;
import deal.ast.IndexExpr;
import deal.ast.LiteralExpr;
import deal.ast.LiteralValue;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.ProgramNode;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
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
import deal.semantic.ContainerPayloadDescriptors;
import deal.semantic.SemanticLowerer;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContainerOpsExecutor;
import deal.semantic.ir.ContainerOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ContainerOpsExecutor.BoundaryResult;
import deal.semantic.ir.ContainerOpsExecutor.Outcome;
import deal.semantic.ir.ContainerOpsExecutor.Value;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
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
 * Verifies the ISSUE-0386 container/string lowering arms of the common
 * lowerer ({@link SemanticLowerer}): the D1 closed construct→op shape map
 * for {@code CONST} (scalar literals and template fragments),
 * {@code BINDING_LOAD} (the loop-binding load-resolution rule),
 * {@code ARRAY_NEW} (+ {@code ARRAY_LITERAL_ELEMENT} children),
 * {@code TABLE_NEW}, {@code ARRAY_LENGTH}, {@code MEMBER_READ}
 * (+ {@code CONTEXTUAL_TABLE_READ} child), {@code STRING_CONCAT}
 * (string {@code +} and templates), and {@code FOR_EACH(STRING_SCALARS)},
 * plus the fail-closed E6005 arms and the combined dependency step over
 * the produced validated unit executed through
 * {@link ContainerOpsExecutor} with a fixture
 * {@link BoundaryCheckRunner}.
 *
 * <p>Pinned cases (the task verification; wiki Verification 1 and 7 layer 2):
 * <ol>
 *   <li>per-construct checked-source slices — scalar literals (each
 *       closed scalar), identifier (loop-binding load carrying the
 *       enclosing {@code FOR_EACH} payload's initial generation), array
 *       literals (empty, nested, and the side-effecting
 *       {@code a, b, i, c, v} source-order shape), table literals
 *       (duplicate keys), string {@code +}, templates (multi-part with
 *       interpolation at both ends and the single-fragment no-fold
 *       shape), array {@code .length}, table member reads in checked
 *       contextual positions, and string for-of — each asserted against
 *       the exact op kind, payload fields, policy, result/operand types,
 *       child order, {@code parentOpId}, and origin spans;</li>
 *   <li>negatives — string {@code +} never emits {@code BINARY}; an
 *       array for-of raises E6005 {@code CONSTRUCT_UNLOWERED} as a hard
 *       failure with the exact {@link LoweringFailureDetail} (and the
 *       same hard failure for class-typed literals, class/member access,
 *       and the bytes {@code .length} arm's receiver); the module member
 *       access arm is the
 *       value position of the one import-member read production
 *       (ISSUE-0659) — with the resolved import fact installed and a
 *       declaration matching the closed catalog row it produces the
 *       realized {@code EXPORT_READ}, while a declaration diverging from
 *       the catalog row's declared descriptor fails closed with the
 *       descriptor-equality guard; a
 *       {@code Type.Error} descriptor position raises E6005
 *       {@code DESCRIPTOR_UNREPRESENTABLE} with the exact detail (the bytes
 *       element position lowers: its descriptor is representable and the
 *       bytes construct is production-covered);</li>
 *   <li>the combined dependency step — an array literal with
 *       side-effecting elements and a table literal with duplicate keys
 *       lowered to their validated unit and executed through
 *       {@link ContainerOpsExecutor} (C3) with a fixture
 *       {@link BoundaryCheckRunner}, asserting the allocate-after-checks
 *       order and the pinned first-insertion table order — this test
 *       fails if C3's executor or C4's descriptor bridge is broken;</li>
 *   <li>the module-level seam — the positionable string spine lowers to
 *       a validated ∅-claim unit with byte-identical repeated dumps, and
 *       an uncovered row fails R-COVERAGE.</li>
 * </ol>
 */
public class ContainerLoweringArmsTest {

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

    private static SemanticIrValidator.ComparisonFacts facts() {
        return new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    private static SemanticLowerer.ModuleLowerer lowerer(CheckResult checks) {
        return new SemanticLowerer.ModuleLowerer(MODULE, SOURCE_ID, checks,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    // =========================================================================
    // Checked-source slices
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        return checkSlice(source, null);
    }

    private static CheckedSlice checkSlice(String source, ModuleResolver resolver) {
        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver("test.deal", resolver);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check("test.deal", symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(),
            "the slice checks cleanly: " + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of("test.deal"), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    // =========================================================================
    // AST finders (source-order walk over statements and expressions)
    // =========================================================================

    private static void collectStatements(StatementNode node, List<StatementNode> outStatements,
                                          List<ExpressionNode> outExpressions) {
        if (node == null) {
            return;
        }
        outStatements.add(node);
        switch (node) {
            case FunctionDeclaration fd -> collectStatements(fd.body(), outStatements,
                outExpressions);
            case VariableDeclaration vd ->
                collectExpressions(vd.initializer(), outExpressions);
            case ReturnStatement rs ->
                rs.expr().ifPresent(e -> collectExpressions(e, outExpressions));
            case IfStatement is -> {
                collectExpressions(is.condition(), outExpressions);
                collectStatements(is.thenBlock(), outStatements, outExpressions);
                is.elseBranch().ifPresent(branch -> {
                    if (branch instanceof Either.Left<IfStatement, Block> left) {
                        collectStatements(left.value(), outStatements, outExpressions);
                    } else if (branch instanceof Either.Right<IfStatement, Block> right) {
                        collectStatements(right.value(), outStatements, outExpressions);
                    }
                });
            }
            case WhileStatement ws -> {
                collectExpressions(ws.condition(), outExpressions);
                collectStatements(ws.body(), outStatements, outExpressions);
            }
            case ForStatement fs -> {
                fs.init().ifPresent(init -> {
                    if (init instanceof ForInit.VarDecl decl) {
                        collectExpressions(decl.decl().initializer(), outExpressions);
                    } else if (init instanceof ForInit.AssignExpr assign) {
                        collectExpressions(assign.expr(), outExpressions);
                    }
                });
                fs.condition().ifPresent(c -> collectExpressions(c, outExpressions));
                fs.update().ifPresent(u -> collectExpressions(u, outExpressions));
                collectStatements(fs.body(), outStatements, outExpressions);
            }
            case ForOfStatement fos -> {
                collectExpressions(fos.iterable(), outExpressions);
                collectStatements(fos.body(), outStatements, outExpressions);
            }
            case ExpressionStatement es -> collectExpressions(es.expr(), outExpressions);
            case ExportDeclaration ed -> collectStatements(ed.declaration(), outStatements,
                outExpressions);
            case DeleteStatement ds -> collectExpressions(ds.target(), outExpressions);
            case TryStatement ts -> {
                collectStatements(ts.tryBlock(), outStatements, outExpressions);
                collectStatements(ts.catchBlock(), outStatements, outExpressions);
            }
            case ThrowStatement th -> collectExpressions(th.expr(), outExpressions);
            case Block b -> {
                for (StatementNode s : b.statements()) {
                    collectStatements(s, outStatements, outExpressions);
                }
            }
            case ClassDeclaration cd -> {
                for (ClassField f : cd.fields()) {
                    f.defaultExpr().ifPresent(e -> collectExpressions(e, outExpressions));
                }
            }
            default -> { /* Break/Continue/Import carry no sub-structure. */ }
        }
    }

    private static void collectExpressions(ExpressionNode node,
                                           List<ExpressionNode> outExpressions) {
        if (node == null) {
            return;
        }
        outExpressions.add(node);
        switch (node) {
            case BinaryExpr b -> {
                collectExpressions(b.left(), outExpressions);
                collectExpressions(b.right(), outExpressions);
            }
            case UnaryExpr u -> collectExpressions(u.expr(), outExpressions);
            case CallExpr c -> {
                collectExpressions(c.callee(), outExpressions);
                for (ExpressionNode arg : c.args()) {
                    collectExpressions(arg, outExpressions);
                }
            }
            case MemberAccessExpr m -> collectExpressions(m.object(), outExpressions);
            case IndexExpr i -> {
                collectExpressions(i.array(), outExpressions);
                collectExpressions(i.index(), outExpressions);
            }
            case ArrayLiteralExpr al -> {
                for (ExpressionNode e : al.elements()) {
                    collectExpressions(e, outExpressions);
                }
            }
            case ObjectLiteralExpr ol -> {
                for (Property p : ol.properties()) {
                    collectExpressions(p.value(), outExpressions);
                }
            }
            case FunctionExpr fe -> {
                List<StatementNode> body = new ArrayList<>();
                collectStatements(fe.body(), body, outExpressions);
            }
            case HasExpr h -> collectExpressions(h.object(), outExpressions);
            case AssignmentExpr as -> {
                collectExpressions(as.target(), outExpressions);
                collectExpressions(as.value(), outExpressions);
            }
            case TemplateLiteralExpr t -> {
                for (ExpressionNode part : t.parts()) {
                    collectExpressions(part, outExpressions);
                }
            }
            case AwaitExpression aw -> collectExpressions(aw.callee(), outExpressions);
            default -> { /* Literal/Identifier leaves. */ }
        }
    }

    private static <T> T first(ProgramNode program, Class<T> kind) {
        List<StatementNode> statements = new ArrayList<>();
        List<ExpressionNode> expressions = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            collectStatements(statement, statements, expressions);
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

    // =========================================================================
    // Shape assertion helpers
    // =========================================================================

    private static void checkSpan(String what, SourceOrigin origin, Span expected) {
        check(expected.file().equals(origin.span().file()),
            what + " span file " + origin.span().file() + " == " + expected.file());
        check(origin.span().startLine() == expected.startLine(),
            what + " span start line " + origin.span().startLine() + " == " + expected.startLine());
        check(origin.span().startColumn() == expected.startColumn(),
            what + " span start column " + origin.span().startColumn() + " == "
                + expected.startColumn());
        check(origin.span().endLine() == expected.endLine(),
            what + " span end line " + origin.span().endLine() + " == " + expected.endLine());
        check(origin.span().endColumn() == expected.endColumn(),
            what + " span end column " + origin.span().endColumn() + " == "
                + expected.endColumn());
        check(origin.span().startScalarOffset() == expected.startScalarOffset(),
            what + " span start scalar offset " + origin.span().startScalarOffset() + " == "
                + expected.startScalarOffset());
        check(origin.span().endScalarOffset() == expected.endScalarOffset(),
            what + " span end scalar offset " + origin.span().endScalarOffset() + " == "
                + expected.endScalarOffset());
    }

    private static void checkOrigin(String what, SemanticOp op, Span expected,
                                    SourceOriginKind kind, OpId parent) {
        check(SOURCE_ID.equals(op.origin().sourceId()),
            what + " origin sourceId is the module's stable source identity");
        checkSpan(what, op.origin(), expected);
        check(op.origin().kind() == kind,
            what + " origin kind " + op.origin().kind() + " == " + kind);
        check(java.util.Objects.equals(op.origin().parentOpId(), parent),
            what + " origin parentOpId " + op.origin().parentOpId() + " == " + parent);
    }

    private static void checkEmptyOperands(String what, SemanticOp op) {
        check(op.operands().isEmpty() && op.operandTypes().isEmpty(),
            what + " carries empty operand/operandTypes lists (payload-referenced prior steps)");
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

    private static void checkNoBinary(String what, List<SemanticOp> ops) {
        check(ofKind(ops, SemanticOpKind.BINARY).isEmpty(),
            what + " produces no BINARY op (string + never lowers to BINARY)");
    }

    // =========================================================================
    // 1. CONST arm — every closed scalar literal
    // =========================================================================

    static void testScalarLiteralConstArm() {
        System.out.println("-- CONST arm: every closed scalar literal --");

        CheckedSlice slice = checkSlice("""
            function f(): null {
              let n = null
              let b = true
              let i = 42
              let d = 4.5
              let s = "abc"
              return
            }
            """);
        if (slice == null) {
            return;
        }
        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        List<ExpressionNode> expressions = new ArrayList<>();
        for (StatementNode statement : slice.program().statements()) {
            collectStatements(statement, new ArrayList<>(), expressions);
        }
        List<LiteralExpr> literals = new ArrayList<>();
        for (ExpressionNode expression : expressions) {
            if (expression instanceof LiteralExpr literal) {
                literals.add(literal);
            }
        }
        check(literals.size() == 5,
            "the slice carries exactly the five closed scalar literals; got " + literals.size());
        if (literals.size() != 5) {
            return;
        }

        RuntimeDescriptor[] expectedTypes = {
            RuntimeDescriptor.Null.INSTANCE, RuntimeDescriptor.Boolean.INSTANCE,
            RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Number.INSTANCE,
            RuntimeDescriptor.String.INSTANCE
        };
        ScalarValue[] expectedScalars = {
            ScalarValue.Null.INSTANCE, new ScalarValue.Boolean(true),
            new ScalarValue.Int(42), new ScalarValue.Number(4.5),
            new ScalarValue.String("abc")
        };
        for (int i = 0; i < literals.size(); i++) {
            LiteralExpr literal = literals.get(i);
            ValueId value = lowerer.lowerExpression(literal);
            List<SemanticOp> ops = lowerer.ops();
            SemanticOp op = ops.get(ops.size() - 1);
            check(op.kind() == SemanticOpKind.CONST,
                "literal " + literal.value() + " lowers to one CONST; got " + op.kind());
            KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
            check(payload.value().equals(expectedScalars[i]),
                "literal " + literal.value() + " CONST payload value " + payload.value()
                    + " == " + expectedScalars[i]);
            check(op.result().equals(value),
                "literal " + literal.value() + " CONST publishes its result ValueId");
            check(op.resultType().equals(expectedTypes[i]),
                "literal " + literal.value() + " CONST resultType " + op.resultType()
                    + " == D(checked type) " + expectedTypes[i]);
            check(op.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                "literal " + literal.value() + " CONST policy NO_DEAL_FAILURE");
            checkOrigin("literal " + literal.value(), op, literal.span(), SourceOriginKind.USER,
                null);
            checkEmptyOperands("literal " + literal.value(), op);
        }
    }

    // =========================================================================
    // 1b. CONST arm — the signed32 int-literal range gate (fail closed,
    //     never truncate; the regression for the silent-narrowing finding)
    // =========================================================================

    static void checkIntLiteralRangeDetail(String what, RuntimeException defect) {
        check(defect instanceof SemanticLowerer.IntLiteralOutOfRange,
            what + " raises IntLiteralOutOfRange");
        if (!(defect instanceof SemanticLowerer.IntLiteralOutOfRange outOfRange)) {
            return;
        }
        check(outOfRange.getMessage().contains(Long.toString(outOfRange.value())),
            what + " defect message carries the literal value");
        LoweringFailureDetail detail = SemanticLowerer.loweringFailureDetail(MODULE, defect);
        check("main".equals(detail.module()), what + " detail module is main");
        check(detail.capability() == SemanticCapability.SIGNED_INT32,
            what + " detail capability SIGNED_INT32");
        check(SemanticLowerer.INT32_LITERAL_OUT_OF_RANGE.equals(detail.validatorRule()),
            what + " detail validatorRule INT32_LITERAL_OUT_OF_RANGE");
        check(detail.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
            what + " detail semanticProfile DEAL_V1_2_INT32");
        check(LoweredModuleUnit.FORMAT_VERSION.equals(detail.irVersion()),
            what + " detail irVersion deal.semantic-ir/1");
        check(("SemanticLowerer " + SemanticLowerer.INT32_LITERAL_OUT_OF_RANGE + " ("
                + outOfRange.getMessage() + ")").equals(detail.origin()),
            what + " detail origin is the pinned component description");
        CompilerDiagnostic diagnostic = FailureContractRegistry.e6005(detail);
        check("E6005".equals(diagnostic.code())
                && diagnostic.diagnosticCode() == DiagnosticCode.E6005
                && "error".equals(diagnostic.severity()),
            what + " converts to an error-severity E6005 diagnostic through the registry");
        check(diagnostic.message().contains(SemanticLowerer.INT32_LITERAL_OUT_OF_RANGE),
            what + " E6005 message carries the INT32_LITERAL_OUT_OF_RANGE rule");
    }

    static void testConstIntLiteralRangeGate() {
        System.out.println("-- CONST arm: the signed32 int-literal range gate --");

        // (a) The in-range extrema lower to the exact scalar — the cast is
        // exact at the boundary, never coerced.
        long[] inRange = {2147483647L, -2147483648L};
        for (long value : inRange) {
            Span span = new Span(SOURCE_ID, 1, 1, 1, 5);
            LiteralExpr literal = new LiteralExpr(span, new LiteralValue.IntLiteral(value));
            CheckResult checks = new CheckResult(Map.of(literal, Type.Int.INSTANCE),
                new SymbolTable(), List.of());
            SemanticLowerer.ModuleLowerer lowerer = lowerer(checks);
            ValueId result = lowerer.lowerExpression(literal);
            List<SemanticOp> ops = lowerer.ops();
            check(ops.size() == 1, "int literal " + value + " produced exactly one op");
            if (ops.size() != 1) {
                continue;
            }
            SemanticOp op = ops.get(0);
            check(op.kind() == SemanticOpKind.CONST,
                "int literal " + value + " (in-range extreme) lowers to CONST");
            KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
            check(payload.value().equals(new ScalarValue.Int((int) value)),
                "int literal " + value + " CONST payload is the exact ScalarValue.Int("
                    + value + "), never coerced");
            check(op.result().equals(result),
                "int literal " + value + " CONST publishes its result ValueId");
            check(op.resultType().equals(RuntimeDescriptor.Int.INSTANCE),
                "int literal " + value + " CONST resultType int");
            check(op.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                "int literal " + value + " CONST policy NO_DEAL_FAILURE");
        }

        // (b) The first out-of-range value on each side fails closed: the
        // exact defect, zero produced ops (never a truncated CONST), and
        // the exact LoweringFailureDetail + E6005 at the unit-production
        // seam.
        long[] outOfRange = {2147483648L, -2147483649L};
        for (long value : outOfRange) {
            Span span = new Span(SOURCE_ID, 1, 1, 1, 5);
            LiteralExpr literal = new LiteralExpr(span, new LiteralValue.IntLiteral(value));
            CheckResult checks = new CheckResult(Map.of(literal, Type.Int.INSTANCE),
                new SymbolTable(), List.of());
            SemanticLowerer.ModuleLowerer lowerer = lowerer(checks);
            RuntimeException defect = null;
            try {
                lowerer.lowerExpression(literal);
            } catch (SemanticLowerer.IntLiteralOutOfRange raised) {
                defect = raised;
            }
            check(defect != null,
                "int literal " + value + " (out of signed32) raises IntLiteralOutOfRange");
            check(lowerer.ops().isEmpty(),
                "int literal " + value + " produced no ops (never a truncated CONST)");
            checkIntLiteralRangeDetail("int literal " + value, defect);
        }

        // (c) The checker-valid end-to-end trigger: the frontend still
        // admits 2147483648 (the E1036 signed32 literal gate is
        // ISSUE-0111's not-yet-satisfied item), so the CONST arm is the
        // fail-closed gate — never a silently corrupted ScalarValue.Int.
        CheckedSlice slice = checkSlice("""
            function f(): null {
              let n = 2147483648
              return null
            }
            """);
        if (slice != null) {
            LiteralExpr literal = first(slice.program(), LiteralExpr.class);
            check(literal != null
                    && literal.value() instanceof LiteralValue.IntLiteral intLit
                    && intLit.value() == 2147483648L,
                "the checked slice carries the checker-valid IntLiteral 2147483648");
            if (literal != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
                RuntimeException defect = null;
                try {
                    lowerer.lowerExpression(literal);
                } catch (SemanticLowerer.IntLiteralOutOfRange raised) {
                    defect = raised;
                }
                check(defect != null,
                    "the checker-valid literal 2147483648 raises the range defect at the "
                        + "CONST arm (never ScalarValue.Int(-2147483648))");
                check(lowerer.ops().isEmpty(),
                    "the out-of-range literal produced no CONST op (no corrupted scalar "
                        + "enters the contract digest)");
                checkIntLiteralRangeDetail("checker-valid 2147483648", defect);
            }
        }

        // (d) The min-int spelling stays untouched: -2147483648 parses as
        // NEG(IntLiteral 2147483648) (the pinned in-tree frontend
        // contract). With the I3 value-operation slice landed the unary
        // negation routes through the UNARY(INT32_NEG) arm, and the
        // operand's CONST arm then fails closed on the out-of-range
        // literal — the defensive gate (E1036 rejects the literal under
        // DEAL_V1_2_INT32 before lowering; the legacy parse contract
        // still admits it) — so no ops are produced and the hard failure
        // stays.
        CheckedSlice negated = checkSlice("""
            function f(): null {
              let n = -2147483648
              return null
            }
            """);
        if (negated != null) {
            UnaryExpr negation = first(negated.program(), UnaryExpr.class);
            check(negation != null,
                "-2147483648 parses as a unary negation of the IntLiteral 2147483648");
            if (negation != null) {
                check(negation.expr() instanceof LiteralExpr operand
                        && operand.value() instanceof LiteralValue.IntLiteral intLit
                        && intLit.value() == 2147483648L,
                    "the negation operand is the IntLiteral 2147483648 (the pinned "
                        + "NEG(IntLiteral 2147483648) spelling)");
                SemanticLowerer.ModuleLowerer lowerer = lowerer(negated.checks());
                RuntimeException defect = null;
                try {
                    lowerer.lowerExpression(negation);
                } catch (SemanticLowerer.IntLiteralOutOfRange raised) {
                    defect = raised;
                }
                check(defect != null,
                    "the unary negation routes its operand through the I3 UNARY arm and "
                        + "the CONST arm fails closed on the out-of-range operand "
                        + "(IntLiteralOutOfRange — never a truncation)");
                check(lowerer.ops().isEmpty(),
                    "the negation produced no ops (no CONST for its out-of-range operand)");
                if (defect != null) {
                    check(((SemanticLowerer.IntLiteralOutOfRange) defect).value()
                            == 2147483648L,
                        "the defect carries the out-of-range literal value");
                }
            }
        }
    }

    // =========================================================================
    // 2. BINDING_LOAD arm — the loop-binding load-resolution rule
    // =========================================================================

    static void testIdentifierLoopBindingLoad() {
        System.out.println("-- BINDING_LOAD arm: the loop-binding load-resolution rule --");

        CheckedSlice slice = checkSlice("""
            for (let x: string of "ab") {
              for (let y: string of x) {}
            }
            """);
        if (slice == null) {
            return;
        }
        ForOfStatement outer = first(slice.program(), ForOfStatement.class);
        check(outer != null, "the slice carries the outer for-of");
        if (outer == null) {
            return;
        }
        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        OpId outerOpId = lowerer.lowerForOfStatement(outer);
        List<SemanticOp> ops = lowerer.ops();

        check(ops.size() == 4,
            "the nested-for-of corpus produces exactly four ops; got " + ops.size());
        if (ops.size() != 4) {
            return;
        }
        check(ops.get(0).kind() == SemanticOpKind.CONST, "op 0 is the iterable CONST");
        check(ops.get(1).kind() == SemanticOpKind.FOR_EACH, "op 1 is the outer FOR_EACH");
        check(ops.get(2).kind() == SemanticOpKind.BINDING_LOAD,
            "op 2 is the inner iterable's loop-binding load");
        check(ops.get(3).kind() == SemanticOpKind.FOR_EACH, "op 3 is the inner FOR_EACH");

        // The pinned id emission order: init block 0, then value/anchor/op per op.
        long[] expectedIds = {4, 7, 11, 14};
        for (int i = 0; i < ops.size(); i++) {
            check(ops.get(i).opId().id() == expectedIds[i],
                "op " + i + " carries the pinned allocation-order id " + expectedIds[i]
                    + "; got " + ops.get(i).opId().id());
        }

        SemanticOp constOp = ops.get(0);
        check(((KindPayload.ConstPayload) constOp.payload()).value()
                .equals(new ScalarValue.String("ab")),
            "the outer iterable CONST carries ScalarValue.String(\"ab\")");

        SemanticOp outerOp = ops.get(1);
        check(outerOp.opId().equals(outerOpId), "lowerForOfStatement returns the FOR_EACH op id");
        KindPayload.ForEachPayload outerPayload = (KindPayload.ForEachPayload) outerOp.payload();
        check(outerPayload.mode() == IterationMode.STRING_SCALARS,
            "outer FOR_EACH mode is STRING_SCALARS");
        check(outerPayload.iterable().equals(constOp.result()),
            "outer FOR_EACH iterable is the CONST prior step");
        check(outerPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
            "outer FOR_EACH generation is the pinned initial generation");
        check(outerOp.result() == null && outerOp.resultType() == null,
            "outer FOR_EACH result/resultType are none");
        check(outerOp.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "outer FOR_EACH policy TYPE_DESCRIPTOR");
        checkOrigin("outer FOR_EACH", outerOp, outer.span(), SourceOriginKind.USER, null);

        IdentifierExpr innerIterable = first(slice.program(), IdentifierExpr.class);
        check(innerIterable != null && "x".equals(innerIterable.name()),
            "the slice carries the inner iterable identifier 'x'");
        SemanticOp load = ops.get(2);
        check(load.kind() == SemanticOpKind.BINDING_LOAD, "op 2 is the BINDING_LOAD");
        KindPayload.BindingLoadPayload loadPayload = (KindPayload.BindingLoadPayload) load.payload();
        check(loadPayload.binding().equals(outerPayload.binding()),
            "the load carries the enclosing FOR_EACH payload's binding");
        check(loadPayload.generation() == outerPayload.generation()
                && loadPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
            "the load carries the enclosing FOR_EACH payload's initial generation "
                + "(the loop-binding load-resolution rule — the payload is never rewritten)");
        check(load.resultType().equals(RuntimeDescriptor.String.INSTANCE),
            "the load resultType is D(checked type) = string");
        check(load.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the load policy NO_DEAL_FAILURE");
        checkOrigin("loop-binding load", load, innerIterable.span(), SourceOriginKind.USER,
            outerOp.opId());

        SemanticOp innerOp = ops.get(3);
        KindPayload.ForEachPayload innerPayload = (KindPayload.ForEachPayload) innerOp.payload();
        check(innerPayload.mode() == IterationMode.STRING_SCALARS,
            "inner FOR_EACH mode is STRING_SCALARS");
        check(innerPayload.iterable().equals(load.result()),
            "inner FOR_EACH iterable is the load's value");
        check(!innerPayload.binding().equals(outerPayload.binding()),
            "the inner loop binding is a distinct producer-allocated BindingId");
        check(!innerPayload.body().equals(outerPayload.body()),
            "the inner body block is distinct from the outer body block");
        check(innerPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
            "inner FOR_EACH generation is the pinned initial generation");
        check(innerOp.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "inner FOR_EACH policy TYPE_DESCRIPTOR");
        check(ops.get(3).origin().span().startLine() > 1,
            "inner FOR_EACH origin is the inner for-of span");
    }

    // =========================================================================
    // 3. ARRAY_NEW arm — empty, nested, and the a, b, i, c, v source order
    // =========================================================================

    static void testArrayLiteralArm() {
        System.out.println("-- ARRAY_NEW arm: empty, nested, and the a, b, i, c, v shape --");

        // (a) The pinned source-order shape with five loop-binding loads.
        CheckedSlice orderSlice = checkSlice("""
            for (let a: string of "a") {
              for (let b: string of a) {
                for (let i: string of b) {
                  for (let c: string of i) {
                    for (let v: string of c) {
                      let xs: string[] = [a, b, i, c, v]
                    }
                  }
                }
              }
            }
            """);
        if (orderSlice != null) {
            ArrayLiteralExpr literal = first(orderSlice.program(), ArrayLiteralExpr.class);
            check(literal != null && literal.elements().size() == 5,
                "the order slice carries the five-element array literal");
            if (literal != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(orderSlice.checks());
                List<SemanticLowerer.ForEachFrame> frames = new ArrayList<>();
                for (String name : List.of("a", "b", "i", "c", "v")) {
                    frames.add(lowerer.openForEachScope(name));
                }
                ValueId arrayValue = lowerer.lowerExpression(literal);
                for (int i = 0; i < 5; i++) {
                    lowerer.closeForEachScope();
                }
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 11,
                    "[a,b,i,c,v] produces 5 loads + ARRAY_NEW + 5 boundary children = 11 ops; got "
                        + ops.size());
                if (ops.size() == 11) {
                    // Element loads in source order.
                    for (int i = 0; i < 5; i++) {
                        SemanticOp load = ops.get(i);
                        check(load.kind() == SemanticOpKind.BINDING_LOAD,
                            "op " + i + " is the element BINDING_LOAD");
                        KindPayload.BindingLoadPayload loadPayload =
                            (KindPayload.BindingLoadPayload) load.payload();
                        check(loadPayload.binding().equals(frames.get(i).binding()),
                            "op " + i + " loads the " + List.of("a", "b", "i", "c", "v").get(i)
                                + " binding in source order");
                        check(loadPayload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
                            "op " + i + " carries the pinned initial generation");
                    }
                    SemanticOp arrayNew = ops.get(5);
                    check(arrayNew.kind() == SemanticOpKind.ARRAY_NEW, "op 5 is ARRAY_NEW");
                    KindPayload.ArrayNewPayload payload =
                        (KindPayload.ArrayNewPayload) arrayNew.payload();
                    check(payload.elementDescriptor().equals(RuntimeDescriptor.String.INSTANCE),
                        "ARRAY_NEW elementDescriptor is D(T) = string");
                    check(payload.values().size() == 5
                            && payload.values().equals(
                                List.of(ops.get(0).result(), ops.get(1).result(),
                                    ops.get(2).result(), ops.get(3).result(),
                                    ops.get(4).result())),
                        "ARRAY_NEW values are the element ValueIds in source order");
                    check(arrayNew.result().equals(arrayValue),
                        "ARRAY_NEW publishes its result ValueId");
                    check(arrayNew.resultType()
                            .equals(new RuntimeDescriptor.Array(RuntimeDescriptor.String.INSTANCE)),
                        "ARRAY_NEW resultType is [D(T)] = [string]");
                    check(arrayNew.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                        "ARRAY_NEW policy NO_DEAL_FAILURE");
                    checkOrigin("ARRAY_NEW", arrayNew, literal.span(), SourceOriginKind.USER, null);
                    for (int i = 0; i < 5; i++) {
                        SemanticOp child = ops.get(6 + i);
                        check(child.kind() == SemanticOpKind.BOUNDARY,
                            "op " + (6 + i) + " is the element boundary child");
                        KindPayload.BoundaryPayload boundary =
                            (KindPayload.BoundaryPayload) child.payload();
                        check(boundary.kind() == BoundaryKind.ARRAY_LITERAL_ELEMENT,
                            "child " + i + " kind ARRAY_LITERAL_ELEMENT");
                        check(boundary.descriptor().equals(RuntimeDescriptor.String.INSTANCE),
                            "child " + i + " descriptor D(T) = string");
                        check(boundary.input().equals(ops.get(i).result()),
                            "child " + i + " input is the matching element ValueId");
                        check(boundary.realization().equals(new BoundaryRealization
                                .RuntimeValidation(SemanticLowerer
                                .CANONICAL_RUNTIME_VALIDATION_ID)),
                            "child " + i + " realization is the pinned RuntimeValidation("
                                + SemanticLowerer.CANONICAL_RUNTIME_VALIDATION_ID + ")");
                        check(child.failurePolicy() == FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
                            "child " + i + " policy ARRAY_ELEMENT_DESCRIPTOR");
                        checkOrigin("element boundary " + i, child,
                            literal.elements().get(i).span(), SourceOriginKind.SYNTHETIC,
                            arrayNew.opId());
                        check(payload.elementBoundaryOpIds().get(i).equals(child.opId()),
                            "ARRAY_NEW elementBoundaryOpIds entry " + i + " is the child op id "
                                + "in the same source order");
                    }
                }
            }
        }

        // (b) The empty literal: zero values and zero children.
        CheckedSlice emptySlice = checkSlice("""
            function f(): null {
              let e: int[] = []
              return null
            }
            """);
        if (emptySlice != null) {
            ArrayLiteralExpr empty = first(emptySlice.program(), ArrayLiteralExpr.class);
            check(empty != null && empty.elements().isEmpty(), "the empty slice carries []");
            if (empty != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(emptySlice.checks());
                lowerer.lowerExpression(empty);
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 1, "[] produces exactly one op; got " + ops.size());
                if (ops.size() == 1) {
                    KindPayload.ArrayNewPayload payload =
                        (KindPayload.ArrayNewPayload) ops.get(0).payload();
                    check(payload.values().isEmpty() && payload.elementBoundaryOpIds().isEmpty(),
                        "[] payload carries zero values and zero element boundaries");
                    check(payload.elementDescriptor().equals(RuntimeDescriptor.Int.INSTANCE),
                        "[] elementDescriptor is D(int) = int (the contextual element type)");
                }
            }
        }

        // (c) The nested literal: inner ARRAY_NEWs are element prior steps.
        CheckedSlice nestedSlice = checkSlice("""
            function f(): null {
              let n = [[1], [2]]
              return null
            }
            """);
        if (nestedSlice != null) {
            ArrayLiteralExpr outerLiteral = first(nestedSlice.program(), ArrayLiteralExpr.class);
            check(outerLiteral != null && outerLiteral.elements().size() == 2
                    && outerLiteral.elements().get(0) instanceof ArrayLiteralExpr,
                "the nested slice's first array literal is the outer [[1],[2]]");
            if (outerLiteral != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(nestedSlice.checks());
                ValueId outerValue = lowerer.lowerExpression(outerLiteral);
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 9,
                    "[[1],[2]] produces (CONST + inner ARRAY_NEW + inner boundary) per inner "
                        + "literal plus the outer ARRAY_NEW and its two boundaries = 9 ops; "
                        + "got " + ops.size());
                if (ops.size() == 9) {
                    List<SemanticOp> arrayNews = ofKind(ops, SemanticOpKind.ARRAY_NEW);
                    check(arrayNews.size() == 3, "three ARRAY_NEW ops (two inner, one outer)");
                    if (arrayNews.size() == 3) {
                        SemanticOp outerNew = arrayNews.get(2);
                        KindPayload.ArrayNewPayload outerPayload =
                            (KindPayload.ArrayNewPayload) outerNew.payload();
                        check(outerPayload.elementDescriptor().equals(
                                new RuntimeDescriptor.Array(RuntimeDescriptor.Int.INSTANCE)),
                            "outer ARRAY_NEW elementDescriptor is [int]");
                        check(outerPayload.values().equals(
                                List.of(arrayNews.get(0).result(), arrayNews.get(1).result())),
                            "outer ARRAY_NEW values are the inner results in source order");
                        check(outerNew.result().equals(outerValue),
                            "outer ARRAY_NEW publishes its result");
                        check(outerPayload.elementBoundaryOpIds().size() == 2,
                            "outer ARRAY_NEW carries exactly two boundary children");
                    }
                }
            }
        }
    }

    // =========================================================================
    // 4. TABLE_NEW arm — duplicate keys stay in source order
    // =========================================================================

    static void testTableLiteralArm() {
        System.out.println("-- TABLE_NEW arm: duplicate keys stay in source order --");

        CheckedSlice slice = checkSlice("""
            function f(): null {
              let t = {x: 1, y: "k", x: 2}
              return null
            }
            """);
        if (slice == null) {
            return;
        }
        ObjectLiteralExpr literal = first(slice.program(), ObjectLiteralExpr.class);
        check(literal != null && literal.properties().size() == 3,
            "the slice carries the three-property table literal");
        if (literal == null) {
            return;
        }
        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        ValueId tableValue = lowerer.lowerExpression(literal);
        List<SemanticOp> ops = lowerer.ops();

        check(ops.size() == 4,
            "{x: 1, y: \"k\", x: 2} produces three entry CONSTs + TABLE_NEW = 4 ops; got "
                + ops.size());
        if (ops.size() != 4) {
            return;
        }
        check(ops.get(0).kind() == SemanticOpKind.CONST
                && ops.get(1).kind() == SemanticOpKind.CONST
                && ops.get(2).kind() == SemanticOpKind.CONST,
            "the three entry values are CONST prior steps in source order");
        check(((KindPayload.ConstPayload) ops.get(0).payload()).value()
                .equals(new ScalarValue.Int(1)),
            "entry 1 value CONST is ScalarValue.Int(1)");
        check(((KindPayload.ConstPayload) ops.get(1).payload()).value()
                .equals(new ScalarValue.String("k")),
            "entry 2 value CONST is ScalarValue.String(\"k\")");
        check(((KindPayload.ConstPayload) ops.get(2).payload()).value()
                .equals(new ScalarValue.Int(2)),
            "entry 3 value CONST is ScalarValue.Int(2)");

        SemanticOp tableNew = ops.get(3);
        check(tableNew.kind() == SemanticOpKind.TABLE_NEW, "op 3 is TABLE_NEW");
        KindPayload.TableNewPayload payload = (KindPayload.TableNewPayload) tableNew.payload();
        check(payload.entries().size() == 3, "TABLE_NEW carries three entries");
        if (payload.entries().size() == 3) {
            check("x".equals(payload.entries().get(0).key())
                    && "y".equals(payload.entries().get(1).key())
                    && "x".equals(payload.entries().get(2).key()),
                "entry keys are the identifier property names in source order (x, y, x)");
            check(payload.entries().get(0).value().equals(ops.get(0).result())
                    && payload.entries().get(1).value().equals(ops.get(1).result())
                    && payload.entries().get(2).value().equals(ops.get(2).result()),
                "entry values are the prior steps in source order");
        }
        check(tableNew.result().equals(tableValue), "TABLE_NEW publishes its result ValueId");
        check(tableNew.resultType().equals(RuntimeDescriptor.Table.INSTANCE),
            "TABLE_NEW resultType is table");
        check(tableNew.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "TABLE_NEW policy NO_DEAL_FAILURE");
        checkOrigin("TABLE_NEW", tableNew, literal.span(), SourceOriginKind.USER, null);
        checkEmptyOperands("TABLE_NEW", tableNew);
    }

    // =========================================================================
    // 5. STRING_CONCAT arm — string +
    // =========================================================================

    static void testStringPlusArm() {
        System.out.println("-- STRING_CONCAT arm: string + --");

        CheckedSlice slice = checkSlice("""
            function f(a: string, b: string): null {
              let s = a + b
              return null
            }
            """);
        if (slice == null) {
            return;
        }
        BinaryExpr binary = first(slice.program(), BinaryExpr.class);
        check(binary != null, "the slice carries the string binary expression");
        if (binary == null) {
            return;
        }
        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        SemanticLowerer.ForEachFrame frameA = lowerer.openForEachScope("a");
        SemanticLowerer.ForEachFrame frameB = lowerer.openForEachScope("b");
        ValueId concatValue = lowerer.lowerExpression(binary);
        lowerer.closeForEachScope();
        lowerer.closeForEachScope();
        List<SemanticOp> ops = lowerer.ops();

        check(ops.size() == 3, "a + b produces two loads + STRING_CONCAT = 3 ops; got "
            + ops.size());
        if (ops.size() != 3) {
            return;
        }
        check(ops.get(0).kind() == SemanticOpKind.BINDING_LOAD
                && ops.get(1).kind() == SemanticOpKind.BINDING_LOAD,
            "the left and right operands are prior-step loads in source order");
        check(((KindPayload.BindingLoadPayload) ops.get(0).payload()).binding()
                .equals(frameA.binding())
                && ((KindPayload.BindingLoadPayload) ops.get(1).payload()).binding()
                .equals(frameB.binding()),
            "the operand loads resolve the left then right operands");

        SemanticOp concat = ops.get(2);
        check(concat.kind() == SemanticOpKind.STRING_CONCAT, "op 2 is STRING_CONCAT");
        KindPayload.StringConcatPayload payload =
            (KindPayload.StringConcatPayload) concat.payload();
        check(payload.fragments().equals(List.of(ops.get(0).result(), ops.get(1).result())),
            "fragments are [left ValueId, right ValueId] in source order");
        check(concat.result().equals(concatValue), "STRING_CONCAT publishes its result ValueId");
        check(concat.resultType().equals(RuntimeDescriptor.String.INSTANCE),
            "STRING_CONCAT resultType is string");
        check(concat.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "STRING_CONCAT policy NO_DEAL_FAILURE");
        checkOrigin("STRING_CONCAT", concat, binary.span(), SourceOriginKind.USER, null);
        checkEmptyOperands("STRING_CONCAT", concat);
        checkNoBinary("string +", ops);
    }

    // =========================================================================
    // 6. STRING_CONCAT arm — templates
    // =========================================================================

    static void testTemplateArms() {
        System.out.println("-- STRING_CONCAT arm: templates --");

        // (a) Multi-part with interpolation at both ends (the first fragment
        // is the empty literal string — never folded away).
        CheckedSlice multi = checkSlice("""
            function f(a: string, b: string): null {
              let s = `${a}mid${b}c`
              return null
            }
            """);
        if (multi != null) {
            TemplateLiteralExpr template = first(multi.program(), TemplateLiteralExpr.class);
            check(template != null && template.parts().size() == 5,
                "the multi-part template alternates 5 parts (literal, a, literal, b, literal)");
            if (template != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(multi.checks());
                lowerer.openForEachScope("a");
                lowerer.openForEachScope("b");
                ValueId templateValue = lowerer.lowerExpression(template);
                lowerer.closeForEachScope();
                lowerer.closeForEachScope();
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 6,
                    "the 5-part template produces 3 fragment CONSTs + 2 interpolation loads + "
                        + "STRING_CONCAT = 6 ops; got " + ops.size());
                if (ops.size() == 6) {
                    check(ops.get(0).kind() == SemanticOpKind.CONST
                            && ops.get(2).kind() == SemanticOpKind.CONST
                            && ops.get(4).kind() == SemanticOpKind.CONST,
                        "every literal part is a CONST step at its even source position");
                    check(((KindPayload.ConstPayload) ops.get(0).payload()).value()
                            .equals(new ScalarValue.String("")),
                        "the first fragment CONST is ScalarValue.String(\"\") — the empty "
                            + "leading literal part is a real fragment, never folded");
                    check(((KindPayload.ConstPayload) ops.get(2).payload()).value()
                            .equals(new ScalarValue.String("mid")),
                        "the middle fragment CONST carries \"mid\"");
                    check(((KindPayload.ConstPayload) ops.get(4).payload()).value()
                            .equals(new ScalarValue.String("c")),
                        "the trailing fragment CONST carries \"c\"");
                    check(ops.get(1).kind() == SemanticOpKind.BINDING_LOAD
                            && ops.get(3).kind() == SemanticOpKind.BINDING_LOAD,
                        "the interpolations are their producing op chains in source order");
                    SemanticOp concat = ops.get(5);
                    check(concat.kind() == SemanticOpKind.STRING_CONCAT,
                        "the template closes with one STRING_CONCAT");
                    KindPayload.StringConcatPayload payload =
                        (KindPayload.StringConcatPayload) concat.payload();
                    check(payload.fragments().size() == 5
                            && payload.fragments().equals(List.of(ops.get(0).result(),
                                ops.get(1).result(), ops.get(2).result(), ops.get(3).result(),
                                ops.get(4).result())),
                        "fragments are the part ValueIds in source order");
                    check(concat.result().equals(templateValue),
                        "template STRING_CONCAT publishes its result ValueId");
                    checkOrigin("template STRING_CONCAT", concat, template.span(),
                        SourceOriginKind.USER, null);
                    // The fragment CONST origins are the part spans (the literal
                    // parts carry line/column spans without scalar offsets).
                    checkSpan("first fragment CONST", ops.get(0).origin(),
                        template.parts().get(0).span());
                }
            }
        }

        // (b) The single-fragment template still produces STRING_CONCAT with
        // one fragment — no folding.
        CheckedSlice single = checkSlice("""
            function f(): null {
              let s = `hello`
              return null
            }
            """);
        if (single != null) {
            TemplateLiteralExpr template = first(single.program(), TemplateLiteralExpr.class);
            check(template != null && template.parts().size() == 1,
                "the single-fragment template carries one literal part");
            if (template != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(single.checks());
                lowerer.lowerExpression(template);
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 2,
                    "`hello` produces one fragment CONST + one STRING_CONCAT = 2 ops; got "
                        + ops.size());
                if (ops.size() == 2) {
                    check(ops.get(0).kind() == SemanticOpKind.CONST
                            && ((KindPayload.ConstPayload) ops.get(0).payload()).value()
                            .equals(new ScalarValue.String("hello")),
                        "the single fragment is one CONST ScalarValue.String(\"hello\")");
                    check(ops.get(1).kind() == SemanticOpKind.STRING_CONCAT,
                        "the single-fragment template still produces STRING_CONCAT");
                    KindPayload.StringConcatPayload payload =
                        (KindPayload.StringConcatPayload) ops.get(1).payload();
                    check(payload.fragments().equals(List.of(ops.get(0).result())),
                        "the STRING_CONCAT carries exactly one fragment (no folding)");
                }
            }
        }
    }

    // =========================================================================
    // 7. ARRAY_LENGTH arm
    // =========================================================================

    static void testArrayLengthArm() {
        System.out.println("-- ARRAY_LENGTH arm --");

        CheckedSlice slice = checkSlice("""
            function f(a: int[]): null {
              let n: int = a.length
              return null
            }
            """);
        if (slice == null) {
            return;
        }
        MemberAccessExpr access = first(slice.program(), MemberAccessExpr.class);
        check(access != null && "length".equals(access.field()),
            "the slice carries the array .length member access");
        if (access == null) {
            return;
        }
        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        SemanticLowerer.ForEachFrame frame = lowerer.openForEachScope("a");
        ValueId lengthValue = lowerer.lowerExpression(access);
        lowerer.closeForEachScope();
        List<SemanticOp> ops = lowerer.ops();

        check(ops.size() == 2,
            "a.length produces exactly the receiver load + ARRAY_LENGTH = 2 ops; got "
                + ops.size());
        if (ops.size() != 2) {
            return;
        }
        check(ops.get(0).kind() == SemanticOpKind.BINDING_LOAD
                && ((KindPayload.BindingLoadPayload) ops.get(0).payload()).binding()
                .equals(frame.binding()),
            "the receiver is one prior-step load (evaluated once, never re-evaluated)");
        SemanticOp length = ops.get(1);
        check(length.kind() == SemanticOpKind.ARRAY_LENGTH, "op 1 is ARRAY_LENGTH");
        KindPayload.ArrayLengthPayload payload =
            (KindPayload.ArrayLengthPayload) length.payload();
        check(payload.arrayValue().equals(ops.get(0).result()),
            "ARRAY_LENGTH payload arrayValue is the receiver ValueId");
        check(length.result().equals(lengthValue), "ARRAY_LENGTH publishes its result ValueId");
        check(length.resultType().equals(RuntimeDescriptor.Int.INSTANCE),
            "ARRAY_LENGTH resultType is int");
        check(length.failurePolicy() == FailurePolicyId.INT32_RESULT,
            "ARRAY_LENGTH policy INT32_RESULT (receiver then range policy)");
        checkOrigin("ARRAY_LENGTH", length, access.span(), SourceOriginKind.USER, null);
        checkEmptyOperands("ARRAY_LENGTH", length);
    }

    // =========================================================================
    // 8. MEMBER_READ arm — checked contextual positions
    // =========================================================================

    static void testMemberReadArm() {
        System.out.println("-- MEMBER_READ arm: checked contextual positions --");

        // (a) The if-condition read: contextual type boolean → TYPE_DESCRIPTOR.
        CheckedSlice boolSlice = checkSlice("""
            function f(t: table): null {
              if (t.k) {}
              return null
            }
            """);
        if (boolSlice != null) {
            MemberAccessExpr access = first(boolSlice.program(), MemberAccessExpr.class);
            check(access != null && "k".equals(access.field()),
                "the if-condition slice carries t.k");
            if (access != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(boolSlice.checks());
                lowerer.openForEachScope("t");
                ValueId readValue = lowerer.lowerExpression(access);
                lowerer.closeForEachScope();
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 3,
                    "t.k produces the receiver load + MEMBER_READ + its contextual child = 3 "
                        + "ops; got " + ops.size());
                if (ops.size() == 3) {
                    check(ops.get(0).kind() == SemanticOpKind.BINDING_LOAD,
                        "the receiver is one prior-step load");
                    SemanticOp read = ops.get(1);
                    check(read.kind() == SemanticOpKind.MEMBER_READ, "op 1 is MEMBER_READ");
                    KindPayload.MemberReadPayload payload =
                        (KindPayload.MemberReadPayload) read.payload();
                    check(payload.table().equals(ops.get(0).result()),
                        "MEMBER_READ payload table is the receiver ValueId (exactly once)");
                    check("k".equals(payload.key()),
                        "MEMBER_READ key is the constant identifier string (never evaluated)");
                    check(read.result().equals(readValue),
                        "MEMBER_READ publishes its result ValueId");
                    check(read.resultType().equals(RuntimeDescriptor.Boolean.INSTANCE),
                        "MEMBER_READ resultType is D(contextual type) = boolean");
                    check(read.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                        "MEMBER_READ policy NO_DEAL_FAILURE");
                    checkOrigin("MEMBER_READ", read, access.span(), SourceOriginKind.USER, null);
                    SemanticOp child = ops.get(2);
                    check(child.kind() == SemanticOpKind.BOUNDARY,
                        "op 2 is the single contextual child");
                    KindPayload.BoundaryPayload boundary =
                        (KindPayload.BoundaryPayload) child.payload();
                    check(boundary.kind() == BoundaryKind.CONTEXTUAL_TABLE_READ,
                        "child kind CONTEXTUAL_TABLE_READ");
                    check(boundary.descriptor().equals(RuntimeDescriptor.Boolean.INSTANCE),
                        "child descriptor D(contextual type) = boolean");
                    check(boundary.input().equals(read.result()),
                        "child input is the MEMBER_READ result ValueId");
                    check(boundary.realization().equals(new BoundaryRealization.RuntimeValidation(
                            SemanticLowerer.CANONICAL_RUNTIME_VALIDATION_ID)),
                        "child realization is the pinned RuntimeValidation("
                            + SemanticLowerer.CANONICAL_RUNTIME_VALIDATION_ID + ")");
                    check(child.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                        "child policy is the descriptor-kind rule: TYPE_DESCRIPTOR");
                    checkOrigin("contextual child", child, access.span(),
                        SourceOriginKind.SYNTHETIC, read.opId());
                }
            }
        }

        // (b) The function-descriptor read: contextual type () => int →
        // FUNCTION_SIGNATURE by the descriptor-kind rule.
        CheckedSlice funcSlice = checkSlice("""
            function f(t: table): null {
              let g: () => int = t.g
              return null
            }
            """);
        if (funcSlice != null) {
            MemberAccessExpr access = first(funcSlice.program(), MemberAccessExpr.class);
            check(access != null && "g".equals(access.field()),
                "the function-context slice carries t.g");
            if (access != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(funcSlice.checks());
                lowerer.openForEachScope("t");
                lowerer.lowerExpression(access);
                lowerer.closeForEachScope();
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 3, "t.g produces 3 ops; got " + ops.size());
                if (ops.size() == 3) {
                    SemanticOp read = ops.get(1);
                    SemanticOp child = ops.get(2);
                    check(read.resultType() instanceof RuntimeDescriptor.Func,
                        "MEMBER_READ resultType is the function descriptor");
                    check(((KindPayload.BoundaryPayload) child.payload()).descriptor()
                            .equals(read.resultType()),
                        "child descriptor equals the MEMBER_READ result descriptor");
                    check(child.failurePolicy() == FailurePolicyId.FUNCTION_SIGNATURE,
                        "child policy is the descriptor-kind rule: FUNCTION_SIGNATURE");
                }
            }
        }
    }

    // =========================================================================
    // 9. FOR_EACH arm — the exact shape, the nested body, the empty body
    // =========================================================================

    static void testForEachArm() {
        System.out.println("-- FOR_EACH arm: exact shape, nested body, empty body --");

        // (a) The nested corpus shape (also covered end-to-end above).
        CheckedSlice nested = checkSlice("""
            for (let x: string of "ab") {
              for (let y: string of x) {}
            }
            """);
        if (nested != null) {
            ForOfStatement outer = first(nested.program(), ForOfStatement.class);
            if (outer != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(nested.checks());
                lowerer.lowerForOfStatement(outer);
                List<SemanticOp> ops = lowerer.ops();
                check(ofKind(ops, SemanticOpKind.FOR_EACH).size() == 2,
                    "the nested corpus produces exactly two FOR_EACH ops");
                check(ops.size() == 4, "the nested corpus produces exactly 4 ops; got "
                    + ops.size());
                if (ops.size() == 4) {
                    check(((KindPayload.ForEachPayload) ops.get(1).payload()).iterable()
                            .equals(ops.get(0).result()),
                        "the outer iterable is one prior step");
                    check(((KindPayload.ForEachPayload) ops.get(3).payload()).iterable()
                            .equals(ops.get(2).result()),
                        "the inner iterable is one prior step");
                    for (SemanticOp op : ops) {
                        checkEmptyOperands("FOR_EACH corpus op", op);
                    }
                }
            }
        }

        // (b) The empty body: zero body ops, the binding and body block still
        // payload-carried.
        CheckedSlice emptyBody = checkSlice("""
            for (let x: string of "s") {}
            """);
        if (emptyBody != null) {
            ForOfStatement statement = first(emptyBody.program(), ForOfStatement.class);
            if (statement != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(emptyBody.checks());
                lowerer.lowerForOfStatement(statement);
                List<SemanticOp> ops = lowerer.ops();
                check(ops.size() == 2,
                    "the empty-body for-of produces exactly CONST + FOR_EACH = 2 ops; got "
                        + ops.size());
                if (ops.size() == 2) {
                    SemanticOp forEach = ops.get(1);
                    KindPayload.ForEachPayload payload =
                        (KindPayload.ForEachPayload) forEach.payload();
                    check(payload.body() != null && !payload.body().equals(
                            lowerer.moduleInitBlockId()),
                        "the empty body still carries its own body BlockId");
                    check(payload.binding() != null,
                        "the empty body still carries its producer-allocated BindingId");
                    check(forEach.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                        "FOR_EACH policy TYPE_DESCRIPTOR");
                    checkOrigin("FOR_EACH", forEach, statement.span(), SourceOriginKind.USER,
                        null);
                }
            }
        }
    }

    // =========================================================================
    // 10. Fail-closed arms — exactly one outcome each
    // =========================================================================

    static void checkConstructDetail(String what, RuntimeException defect,
                                     String expectedConstructText) {
        check(defect instanceof SemanticLowerer.ConstructUnlowered,
            what + " raises ConstructUnlowered");
        if (!(defect instanceof SemanticLowerer.ConstructUnlowered unlowered)) {
            return;
        }
        check(unlowered.construct().contains(expectedConstructText),
            what + " construct description carries \"" + expectedConstructText + "\": "
                + unlowered.construct());
        LoweringFailureDetail detail = SemanticLowerer.loweringFailureDetail(MODULE, defect);
        check("main".equals(detail.module()), what + " detail module is main");
        check(detail.capability() == SemanticCapability.CONTAINERS_AND_STRINGS,
            what + " detail capability CONTAINERS_AND_STRINGS");
        check(SemanticLowerer.CONSTRUCT_UNLOWERED.equals(detail.validatorRule()),
            what + " detail validatorRule CONSTRUCT_UNLOWERED");
        check(detail.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
            what + " detail semanticProfile DEAL_V1_2_INT32");
        check(LoweredModuleUnit.FORMAT_VERSION.equals(detail.irVersion()),
            what + " detail irVersion deal.semantic-ir/1");
        check(("SemanticLowerer " + SemanticLowerer.CONSTRUCT_UNLOWERED + " ("
                + unlowered.construct() + ")").equals(detail.origin()),
            what + " detail origin is the pinned component description");
        CompilerDiagnostic diagnostic = FailureContractRegistry.e6005(detail);
        check("E6005".equals(diagnostic.code())
                && diagnostic.diagnosticCode() == DiagnosticCode.E6005
                && "error".equals(diagnostic.severity()),
            what + " converts to an error-severity E6005 diagnostic through the registry");
    }

    static void testConstructUnloweredNegatives() {
        System.out.println("-- Fail-closed arms: CONSTRUCT_UNLOWERED --");

        // (a) Index read — the array index read arm is the
        // EVALUATION_ORDER carrier's (ISSUE-0410, INDEX_NORMALIZE/
        // INDEX_READ); this stage's window still fails hard on the seed's
        // parameter identifier (the E5 window resolves only enclosing
        // for-of/catch bindings), with no ops produced — never a partial
        // unit.
        CheckedSlice indexRead = checkSlice("""
            function f(xs: int[]): null {
              let n: int = xs[0]
              return null
            }
            """);
        if (indexRead != null) {
            IndexExpr expression = first(indexRead.program(), IndexExpr.class);
            if (expression != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(indexRead.checks());
                RuntimeException defect = null;
                try {
                    lowerer.lowerExpression(expression);
                } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                    defect = unlowered;
                }
                check(defect != null, "the index-read arm raises ConstructUnlowered");
                check(defect.getMessage() != null
                        && defect.getMessage().contains("identifier 'xs'"),
                    "the index-read failure names the unresolvable parameter identifier: "
                        + defect.getMessage());
                check(lowerer.ops().isEmpty(),
                    "the index-read arm produced no ops (hard failure, never a partial unit)");
            }
            // The module-level seam: exactly the pinned LoweringFailureDetail,
            // no unit, never a reroute.
            SemanticLowerer.LoweringResult result = SemanticLowerer.lowerModule(
                moduleOf(indexRead), SemanticProfile.DEAL_V1_2_INT32, Map.of(),
                INTERFACE_HASH, REGISTRY_HASH,
                SemanticIdAllocator.over(List.of(MODULE)));
            check(result != null && result.hasErrors() && result.unit() == null,
                "lowerModule fails hard with no unit (never a reroute)");
            if (result != null && result.hasErrors()) {
                check("E6005".equals(result.diagnostics().get(0).code())
                        && result.diagnostics().get(0).message()
                        .contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
                    "lowerModule returns the E6005 CONSTRUCT_UNLOWERED diagnostic");
            }
        }

        // (b) Class-typed object literal (CLASS_NEW is E9's).
        CheckedSlice classLiteral = checkSlice("""
            class Point { x: int; }
            function f(): null {
              let p: Point = {x: 1}
              return null
            }
            """);
        if (classLiteral != null) {
            ObjectLiteralExpr literal = first(classLiteral.program(), ObjectLiteralExpr.class);
            if (literal != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(classLiteral.checks());
                RuntimeException defect = null;
                try {
                    lowerer.lowerExpression(literal);
                } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                    defect = unlowered;
                }
                check(defect != null, "the class-typed literal arm raises ConstructUnlowered");
                checkConstructDetail("class-typed literal", defect, "CLASS_NEW");
            }
        }

        // (c) Class member access (FIELD_READ is E9's).
        CheckedSlice classAccess = checkSlice("""
            class Point { x: int; }
            function f(p: Point): null {
              let n: int = p.x
              return null
            }
            """);
        if (classAccess != null) {
            MemberAccessExpr access = first(classAccess.program(), MemberAccessExpr.class);
            if (access != null) {
                SemanticLowerer.ModuleLowerer lowerer = lowerer(classAccess.checks());
                RuntimeException defect = null;
                try {
                    lowerer.lowerExpression(access);
                } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                    defect = unlowered;
                }
                check(defect != null, "the class member access arm raises ConstructUnlowered");
                checkConstructDetail("class member access", defect, "FIELD_READ");
            }
        }

        // (d) Module member access — the value-position arm of the one
        // import-member read production (ISSUE-0659): with a declaration
        // matching the closed catalog row and the resolved import fact
        // installed, the arm produces the realized EXPORT_READ; keeping
        // the stub's diverging declaration, it fails closed with the
        // descriptor-equality guard.
        {
            StubModuleResolver resolver = new StubModuleResolver();
            CheckedSlice moduleAccess = checkSlice("""
                import * as console from "std/console"
                function f(): null {
                  let g: (x: string) => null = console.log
                  return null
                }
                """, resolver);
            if (moduleAccess != null) {
                MemberAccessExpr access = first(moduleAccess.program(),
                    MemberAccessExpr.class);
                if (access != null) {
                    SemanticLowerer.ModuleLowerer lowerer = lowerer(moduleAccess.checks());
                    lowerer.setModuleImports(List.of(new ResolvedImport("console",
                        "std/console", new ModuleId("std.console"),
                        ExternalModuleKind.STDLIB)));
                    RuntimeException defect = null;
                    try {
                        lowerer.lowerExpression(access);
                    } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                        defect = unlowered;
                    }
                    check(defect == null,
                        "the module member access arm produces the read with matching "
                            + "declared facts: " + (defect == null ? ""
                                : defect.getMessage()));
                    List<SemanticOp> reads = new ArrayList<>();
                    for (SemanticOp op : lowerer.ops()) {
                        if (op.kind() == SemanticOpKind.EXPORT_READ) {
                            reads.add(op);
                        }
                    }
                    check(reads.size() == 1,
                        "exactly one EXPORT_READ per source occurrence; got "
                            + reads.size());
                    if (reads.size() == 1) {
                        KindPayload.ExportReadPayload payload =
                            (KindPayload.ExportReadPayload) reads.get(0).payload();
                        check(payload.module().equals(new ModuleId("std.console"))
                                && payload.name().equals("log"),
                            "the read names std.console/log; got " + payload.module()
                                + "/" + payload.name());
                        RuntimeDescriptor.Func row = StdlibFunctionCatalog
                            .lookup("std.console", "log").orElseThrow()
                            .declaredDescriptor();
                        check(payload.descriptor().equals(row)
                                && reads.get(0).resultType().equals(row),
                            "the read carries the catalog row's declared descriptor "
                                + row.canonicalSpecText() + "; got "
                                + payload.descriptor().canonicalSpecText());
                        check(reads.get(0).origin().kind() == SourceOriginKind.USER,
                            "the read carries a USER origin at the access span");
                    }
                }
            }
        }
        {
            StubModuleResolver resolver = new StubModuleResolver();
            resolver.register("std/console",
                Map.of("log", new Type.Func(List.of(), Type.Null.INSTANCE)));
            CheckedSlice moduleAccess = checkSlice("""
                import * as console from "std/console"
                function f(): null {
                  let g: () => null = console.log
                  return null
                }
                """, resolver);
            if (moduleAccess != null) {
                MemberAccessExpr access = first(moduleAccess.program(),
                    MemberAccessExpr.class);
                if (access != null) {
                    SemanticLowerer.ModuleLowerer lowerer =
                        lowerer(moduleAccess.checks());
                    lowerer.setModuleImports(List.of(new ResolvedImport("console",
                        "std/console", new ModuleId("std.console"),
                        ExternalModuleKind.STDLIB)));
                    RuntimeException defect = null;
                    try {
                        lowerer.lowerExpression(access);
                    } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                        defect = unlowered;
                    }
                    check(defect != null,
                        "the diverging declared member raises ConstructUnlowered");
                    checkConstructDetail("module member access", defect, "EXPORT_READ");
                    if (defect != null) {
                        check(defect.getMessage().contains("()->null")
                                && defect.getMessage().contains("(string)->null"),
                            "the failure is the descriptor-equality guard naming the "
                                + "checked and the catalog row's declared descriptor: "
                                + defect.getMessage());
                    }
                }
            }
        }

        // (e) .length on bytes (ISSUE-0626 retargeted this pin): the bytes
        // .length arm is the landed ARRAY_LENGTH read over the byte receiver,
        // so the synthetic access no longer fails closed for bytes — its only
        // remaining defect is the synthetic receiver's own binding-load arm
        // (the fixture carries no binding fact), never a bytes-owned guard.
        {
            IdentifierExpr bytesObject = new IdentifierExpr(
                new Span(SOURCE_ID, 1, 1, 1, 2), "b");
            MemberAccessExpr access = new MemberAccessExpr(
                new Span(SOURCE_ID, 1, 1, 1, 9), bytesObject, "length");
            CheckResult checks = new CheckResult(
                Map.of(bytesObject, Type.Bytes.INSTANCE, access, Type.Error.INSTANCE),
                new SymbolTable(), List.of());
            SemanticLowerer.ModuleLowerer lowerer = lowerer(checks);
            RuntimeException defect = null;
            try {
                lowerer.lowerExpression(access);
            } catch (SemanticLowerer.ConstructUnlowered unlowered) {
                defect = unlowered;
            }
            check(defect == null
                    || !defect.getMessage().contains("bytes"),
                "the bytes .length arm is admitted (its receiver's binding-load arm is "
                    + "the synthetic fixture's only defect): "
                    + (defect == null ? "lowered" : defect.getMessage()));
            check(defect != null
                    && defect.getMessage().contains("identifier 'b' is not a load of an "
                        + "enclosing for-of loop binding"),
                "the bytes .length arm proceeds to the receiver's binding-load arm: "
                    + (defect == null ? "<lowered>" : defect.getMessage()));
        }
    }

    // =========================================================================
    // 11. Descriptor negatives — DESCRIPTOR_UNREPRESENTABLE
    // =========================================================================

    static void testDescriptorNegatives() {
        System.out.println("-- Descriptor negatives: DESCRIPTOR_UNREPRESENTABLE --");

        // (a) An array of bytes at the element-descriptor position (ISSUE-0626
        // retargeted this pin): the bytes element descriptor is representable
        // and the shared container pipeline emits the ARRAY_NEW with it — the
        // position is no longer excluded.
        {
            Span span = new Span(SOURCE_ID, 1, 1, 1, 5);
            ArrayLiteralExpr literal = new ArrayLiteralExpr(span, List.of());
            CheckResult checks = new CheckResult(
                Map.of(literal, new Type.Array(Type.Bytes.INSTANCE)),
                new SymbolTable(), List.of());
            SemanticLowerer.ModuleLowerer lowerer = lowerer(checks);
            SemanticLowerer.ConstructUnlowered defect = null;
            try {
                lowerer.lowerExpression(literal);
            } catch (SemanticLowerer.ConstructUnlowered raised) {
                defect = raised;
            }
            check(defect == null,
                "the bytes element position lowers through the shared container "
                    + "pipeline (the bytes descriptor is representable): "
                    + (defect == null ? "lowered" : defect.getMessage()));
        }

        // (b) Type.Error at the element-descriptor position (same projection).
        {
            Span span = new Span(SOURCE_ID, 1, 1, 1, 5);
            ArrayLiteralExpr literal = new ArrayLiteralExpr(span, List.of());
            CheckResult checks = new CheckResult(
                Map.of(literal, new Type.Array(Type.Error.INSTANCE)),
                new SymbolTable(), List.of());
            SemanticLowerer.ModuleLowerer lowerer = lowerer(checks);
            ContainerPayloadDescriptors.Defect defect = null;
            try {
                lowerer.lowerExpression(literal);
            } catch (ContainerPayloadDescriptors.Defect raised) {
                defect = raised;
            }
            check(defect != null,
                "the Type.Error element-descriptor position raises the bridge Defect");
            if (defect != null) {
                LoweringFailureDetail detail =
                    SemanticLowerer.loweringFailureDetail(MODULE, defect);
                check(ContainerPayloadDescriptors.DESCRIPTOR_UNREPRESENTABLE
                        .equals(detail.validatorRule()),
                    "Type.Error converts to DESCRIPTOR_UNREPRESENTABLE through the same seam");
            }
        }
    }

    // =========================================================================
    // 12. The combined dependency step — lower the slice to its validated unit
    //     and execute it through ContainerOpsExecutor (C3) with the fixture
    //     BoundaryCheckRunner
    // =========================================================================

    static void testCombinedDependencyStep() {
        System.out.println("-- Combined dependency step: slice → validated unit → C3 execution --");

        CheckedSlice slice = checkSlice("""
            function f(a: int, b: int, c: int, v: int, i: int): null {
              let xs: int[] = [a, b, i, c, v]
              let t = {x: 1, y: "k", x: 2}
              return null
            }
            """);
        if (slice == null) {
            return;
        }
        ArrayLiteralExpr arrayLiteral = first(slice.program(), ArrayLiteralExpr.class);
        ObjectLiteralExpr tableLiteral = first(slice.program(), ObjectLiteralExpr.class);
        check(arrayLiteral != null && tableLiteral != null,
            "the slice carries the side-effecting array literal and the duplicate-key table "
                + "literal");
        if (arrayLiteral == null || tableLiteral == null) {
            return;
        }

        SemanticLowerer.ModuleLowerer lowerer = lowerer(slice.checks());
        List<SemanticLowerer.ForEachFrame> frames = new ArrayList<>();
        for (String name : List.of("a", "b", "i", "c", "v")) {
            frames.add(lowerer.openForEachScope(name));
        }
        ValueId arrayValue = lowerer.lowerExpression(arrayLiteral);
        for (int i = 0; i < 5; i++) {
            lowerer.closeForEachScope();
        }
        ValueId tableValue = lowerer.lowerExpression(tableLiteral);

        Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(
            ConstructKind.IDENTIFIER, ConstructKind.IDENTIFIER.mappedOpKinds(),
            ConstructKind.ARRAY_OBJECT_LITERAL, ConstructKind.ARRAY_OBJECT_LITERAL.mappedOpKinds(),
            ConstructKind.SCALAR_LITERAL, ConstructKind.SCALAR_LITERAL.mappedOpKinds());
        LoweredModuleUnit unit = lowerer.buildUnit(coverage, List.of(), INTERFACE_HASH,
            REGISTRY_HASH);
        Optional<CompilerDiagnostic> validation = SemanticIrValidator.validate(unit, facts());
        check(validation.isEmpty(),
            "the slice's unit passes the closed validator (R-COVERAGE/R-CAPABILITY green): "
                + validation);
        if (validation.isPresent()) {
            return;
        }
        check(unit.requiredCapabilities().equals(Set.of(SemanticCapability.DESCRIPTORS,
                SemanticCapability.BOUNDARIES)),
            "the unit claims exactly {DESCRIPTORS, BOUNDARIES} at E5's gate (the five "
                + "ARRAY_LITERAL_ELEMENT boundary children fully evidence both "
                + "single-family rows; the other active rows are under-evidenced)");

        // The lowerer appends one detached module-level MODULE_INIT envelope
        // op per unit (ISSUE-0590 E3/E8); the slice's own ops are the 15
        // below.
        List<SemanticOp> ops = unit.ops().stream()
            .filter(op -> op.kind() != SemanticOpKind.MODULE_INIT)
            .toList();
        check(ops.size() == 15,
            "the combined slice produces 5 loads + ARRAY_NEW + 5 boundaries + 3 CONSTs + "
                + "TABLE_NEW = 15 ops; got " + ops.size());
        if (ops.size() != 15) {
            return;
        }
        List<SemanticOp> arrayNews = ofKind(ops, SemanticOpKind.ARRAY_NEW);
        List<SemanticOp> tableNews = ofKind(ops, SemanticOpKind.TABLE_NEW);
        List<SemanticOp> consts = ofKind(ops, SemanticOpKind.CONST);
        check(arrayNews.size() == 1 && tableNews.size() == 1 && consts.size() == 3,
            "the slice unit carries one ARRAY_NEW, one TABLE_NEW, and three CONSTs");
        if (arrayNews.size() != 1 || tableNews.size() != 1 || consts.size() != 3) {
            return;
        }
        SemanticOp arrayNew = arrayNews.get(0);
        check(arrayNew.result().equals(arrayValue)
                && tableNews.get(0).result().equals(tableValue),
            "the unit ops are the lowered slice ops (same value ids)");
        check(((KindPayload.ArrayNewPayload) arrayNew.payload()).elementDescriptor()
                .equals(RuntimeDescriptor.Int.INSTANCE),
            "the ARRAY_NEW elementDescriptor came from the C4 descriptor bridge (int)");

        // --- Execute ARRAY_NEW through C3 with the fixture runner. ---
        Map<ValueId, Value> arrayPrior = new LinkedHashMap<>();
        List<KindPayload.ArrayNewPayload> arrayPayload =
            List.of((KindPayload.ArrayNewPayload) arrayNew.payload());
        Value[] elementValues = {
            new Value.Int(1), new Value.Int(2), new Value.Int(3), new Value.Int(4),
            new Value.Int(5)
        };
        for (int i = 0; i < 5; i++) {
            arrayPrior.put(arrayPayload.get(0).values().get(i), elementValues[i]);
        }
        Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.BOUNDARY) {
                boundaryOps.put(op.opId(), op);
            }
        }

        final class RecordingRunner implements BoundaryCheckRunner {
            final List<KindPayload.BoundaryPayload> seen = new ArrayList<>();
            final List<Value> inputs = new ArrayList<>();
            int failAtIndex = -1;
            BoundaryFailure failure = null;

            @Override
            public BoundaryResult run(KindPayload.BoundaryPayload boundary, Value input) {
                seen.add(boundary);
                inputs.add(input);
                if (seen.size() - 1 == failAtIndex && failure != null) {
                    return new BoundaryResult.Fail(failure);
                }
                return new BoundaryResult.Pass(input);
            }
        }

        // All-pass run: allocation happens only after the last child passed.
        RecordingRunner allPass = new RecordingRunner();
        Outcome<SemanticArray<Value>> outcome = ContainerOpsExecutor.executeArrayNew(arrayNew,
            arrayPrior, boundaryOps, allPass);
        check(outcome instanceof Outcome.Success, "the all-pass run publishes the array");
        if (outcome instanceof Outcome.Success<SemanticArray<Value>> success) {
            SemanticArray<Value> array = success.value();
            check(array.size() == 5, "the published array carries five elements");
            for (int i = 0; i < 5; i++) {
                check(array.elementAt(i).equals(elementValues[i]),
                    "element " + i + " is the delegate-published checked value in source order");
            }
        }
        check(allPass.seen.size() == 5,
            "every element boundary child ran in payload order (5 checks)");
        for (int i = 0; i < 5; i++) {
            check(allPass.seen.get(i).input().equals(
                    arrayPayload.get(0).values().get(i)),
                "boundary " + i + " input is the matching element ValueId (element prior "
                    + "steps completed before the checks)");
            check(allPass.inputs.get(i).equals(elementValues[i]),
                "boundary " + i + " received the resolved element value "
                    + elementValues[i]);
        }

        // Fail-at-second-child run: the op fails with that child's failure, the
        // first child's pass stays observable, the later children never run,
        // and no array is published (allocate-after-checks).
        RecordingRunner failSecond = new RecordingRunner();
        failSecond.failAtIndex = 1;
        BoundaryFailure pinnedFailure =
            new BoundaryFailure(
                FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, DiagnosticCode.E8003,
                "array element 2 type mismatch", "int", "number", Map.of(), null);
        failSecond.failure = pinnedFailure;
        Outcome<SemanticArray<Value>> failedOutcome = ContainerOpsExecutor.executeArrayNew(
            arrayNew, arrayPrior, boundaryOps, failSecond);
        check(failedOutcome instanceof Outcome.Failure,
            "the failing second child fails the op (no array published)");
        if (failedOutcome instanceof Outcome.Failure<SemanticArray<Value>> failureOutcome) {
            check(failureOutcome.failure().failure().equals(pinnedFailure),
                "the published failure is the second child's own failure");
            check(failureOutcome.failure().origin().equals(arrayNew.origin()),
                "the published failure carries the parent op's origin");
        }
        check(failSecond.seen.size() == 2,
            "the second child's failure stops the run: exactly two children ran (the first "
                + "child's pass observable, the third child never ran)");
        check(failSecond.seen.get(0).input().equals(arrayPayload.get(0).values().get(0))
                && failSecond.seen.get(1).input().equals(arrayPayload.get(0).values().get(1)),
            "the run follows payload order until the failure");

        // --- Execute TABLE_NEW through C3: the pinned first-insertion order. ---
        Map<ValueId, Value> tablePrior = new LinkedHashMap<>();
        tablePrior.put((ValueId) consts.get(0).result(), new Value.Int(1));
        tablePrior.put((ValueId) consts.get(1).result(),
            new Value.String(deal.semantic.ir.UnicodeScalars.validate("k")));
        tablePrior.put((ValueId) consts.get(2).result(), new Value.Int(2));
        SemanticTable<Value> table = ContainerOpsExecutor.executeTableNew(tableNews.get(0),
            tablePrior);
        check(table.keys().equals(List.of("x", "y")),
            "the duplicate literal keys keep the first position: keys() == [x, y]; got "
                + table.keys());
        check(table.get("x") instanceof SemanticTable.Lookup.Present<Value> presentX
                && presentX.value().equals(new Value.Int(2)),
            "the later duplicate value wins: get(x) == Int(2)");
        check(table.get("y") instanceof SemanticTable.Lookup.Present<Value> presentY
                && presentY.value().equals(
                    new Value.String(deal.semantic.ir.UnicodeScalars.validate("k"))),
            "the middle entry keeps its value: get(y) == String(\"k\")");
    }

    // =========================================================================
    // 13. The module-level seam — the positionable string spine, ∅-claim
    //     validated units, byte-identical determinism, and the R-COVERAGE
    //     negative
    // =========================================================================

    static void testModuleCorpusDeterminism() {
        System.out.println("-- Module seam: positionable spine, determinism, R-COVERAGE --");

        CheckedSlice slice = checkSlice("""
            for (let x: string of "ab" + `c${"d"}e`) {
              for (let y: string of x) {}
            }
            """);
        if (slice == null) {
            return;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage = Map.of(
            ConstructKind.SCALAR_LITERAL, ConstructKind.SCALAR_LITERAL.mappedOpKinds(),
            ConstructKind.IDENTIFIER, ConstructKind.IDENTIFIER.mappedOpKinds(),
            ConstructKind.STRING_CONCAT_TEMPLATE,
            ConstructKind.STRING_CONCAT_TEMPLATE.mappedOpKinds(),
            ConstructKind.IF_WHILE_FOR_FOR_OF, ConstructKind.IF_WHILE_FOR_FOR_OF.mappedOpKinds());

        SemanticLowerer.LoweringResult first = SemanticLowerer.lowerModule(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, coverage, INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
        check(first != null && !first.hasErrors() && first.unit() != null,
            "the positionable spine lowers to a validated unit: " + (first == null ? "null"
                : first.diagnostics()));
        if (first == null || first.hasErrors()) {
            return;
        }
        LoweredModuleUnit unit = first.unit();
        check(unit.requiredCapabilities().isEmpty(),
            "the corpus unit claims ∅ at E5's gate (every active home row is "
                + "under-evidenced)");
        List<SemanticOpKind> kinds = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            kinds.add(op.kind());
        }
        check(kinds.contains(SemanticOpKind.CONST)
                && kinds.contains(SemanticOpKind.BINDING_LOAD)
                && kinds.contains(SemanticOpKind.STRING_CONCAT)
                && kinds.contains(SemanticOpKind.FOR_EACH),
            "the corpus produces every recorded row's mapped kind (R-COVERAGE green): " + kinds);
        checkNoBinary("module corpus", unit.ops());
        SemanticOp load = null;
        SemanticOp outerForEach = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_LOAD && load == null) {
                load = op;
            }
            if (op.kind() == SemanticOpKind.FOR_EACH && outerForEach == null) {
                outerForEach = op;
            }
        }
        if (load != null && outerForEach != null) {
            KindPayload.BindingLoadPayload loadPayload =
                (KindPayload.BindingLoadPayload) load.payload();
            KindPayload.ForEachPayload forEachPayload =
                (KindPayload.ForEachPayload) outerForEach.payload();
            check(loadPayload.binding().equals(forEachPayload.binding())
                    && loadPayload.generation() == forEachPayload.generation(),
                "the corpus's loop-binding load carries the enclosing FOR_EACH payload's "
                    + "initial generation");
        }

        // Determinism: a fresh lowering produces byte-identical dumps.
        SemanticLowerer.LoweringResult second = SemanticLowerer.lowerModule(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, coverage, INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
        check(second != null && !second.hasErrors(),
            "the repeated lowering validates again");
        if (second != null && !second.hasErrors()) {
            byte[] firstDump = SemanticIrDumper.dumpModule(unit);
            byte[] secondDump = SemanticIrDumper.dumpModule(second.unit());
            check(Arrays.equals(firstDump, secondDump),
                "two fresh lowerings produce byte-identical unit dumps (D8)");
        }

        // The R-COVERAGE negative: a recorded row without a produced op of its
        // mapped kind fails the validator (an uncovered construct is a hard
        // failure, never a silent skip).
        Map<ConstructKind, List<SemanticOpKind>> overCoverage =
            new LinkedHashMap<>(coverage);
        overCoverage.put(ConstructKind.CALL, ConstructKind.CALL.mappedOpKinds());
        SemanticLowerer.LoweringResult uncovered = SemanticLowerer.lowerModule(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, overCoverage, INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
        check(uncovered != null && uncovered.hasErrors() && uncovered.unit() == null,
            "a recorded CALL row without a produced op fails hard with no unit");
        if (uncovered != null && uncovered.hasErrors()) {
            check("E6005".equals(uncovered.diagnostics().get(0).code())
                    && uncovered.diagnostics().get(0).message()
                    .contains(SemanticIrValidator.R_COVERAGE),
                "the uncovered-row unit fails R-COVERAGE through the validator");
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Container Lowering Arms Test (ISSUE-0386) ===\n");

        testScalarLiteralConstArm();
        testConstIntLiteralRangeGate();
        testIdentifierLoopBindingLoad();
        testArrayLiteralArm();
        testTableLiteralArm();
        testStringPlusArm();
        testTemplateArms();
        testArrayLengthArm();
        testMemberReadArm();
        testForEachArm();
        testConstructUnloweredNegatives();
        testDescriptorNegatives();
        testCombinedDependencyStep();
        testModuleCorpusDeterminism();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
