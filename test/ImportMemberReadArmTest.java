package deal.test;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
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
import deal.ast.IfStatement;
import deal.ast.ImportDeclaration;
import deal.ast.IndexExpr;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.ProgramNode;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.ModuleRoute;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0659: the import-member read production — the value-position arm,
 * the STDLIB catalog branch, and the exactly-one registrations
 * (design source {@code import-member-read-arm-lowering-and-registration}
 * R1 (the one read production serving both positions; the returned read
 * value; the slot convention), R2 (the STDLIB branch and the catalog
 * row's declared descriptor), R3 (the registration set per kind and the
 * exactly-one discipline), R5 (the realized-lowering drive), the
 * import-read (lowering) contract, and guard-table rows G1/G2/G4/G5/G6;
 * {@code module-export-reads-and-in-project-class-construction} M1 and
 * the export-read (lowering) contract;
 * {@code semantic-ir-construct-coverage-cutover} K2/K9;
 * {@code luajit-jvm-single-lowering-production-cutover} C1).
 *
 * <ol>
 *   <li><b>The stub battery (per import kind, both positions).</b> A
 *       checked slice whose import alias resolves through the checker
 *       produces exactly one {@code EXPORT_READ} per source occurrence —
 *       the value-position arm and the landed callee arm call the same
 *       production — with the expected payload ({@code resolvedModule,
 *       exportName, descriptor}), a {@code USER} origin at the access
 *       span and {@code parentOpId} = the position's current parent; the
 *       unit's registration carries the expected shape and owner per
 *       kind ({@code HostFunction} for HOST and for a declared function
 *       export of a STDLIB kind, {@code ExternalFunction(SHARED_BODY)}
 *       for a COMPILED import resolved through the session's callee-route
 *       facts) keyed by the read's result identity; a non-function read
 *       produces the read with no registration.</li>
 *   <li><b>The guards of the arm.</b> An alias without a resolved import
 *       fact, a STDLIB member outside the closed catalog, a STDLIB
 *       descriptor mismatch, and a COMPILED read without a callee-route
 *       record each fail closed with the exact E6005
 *       {@code CONSTRUCT_UNLOWERED} and no unit.</li>
 *   <li><b>The focused project run.</b> A probe project whose entry module
 *       reads a compiled companion's declared function export into a
 *       function-typed binding with no invocation lowers through
 *       {@code lowerProject}, passes the composed project gate, and
 *       yields the unit with exactly one {@code EXPORT_READ} and exactly
 *       one {@code ExternalFunction(SHARED_BODY)} registration keyed by
 *       the read's result identity; the HOST and STDLIB kinds produce the
 *       same exactly-one shape in both positions through the project
 *       entry.</li>
 *   <li><b>The slot convention.</b> A read lowered in a slot-threaded
 *       position (a class default expression reading a module member)
 *       publishes the threaded cell and keys the registration by it.</li>
 *   <li><b>Registration and gate discipline.</b> A duplicate registration
 *       of the read's exact payload/facts shape is rejected at
 *       registration time (never overwritten); a doctored unit whose
 *       function-typed read result carries zero registrations fails the
 *       closed gate with {@code R-FUNCTION-BINDING}; the unmodified unit
 *       is admitted on the typed and the text surface.</li>
 * </ol>
 *
 * <p>This slice changes lowering only: the typed-binding invocation of a
 * read value lowers and validates through the landed call machine (the
 * stub battery's {@code CALL(INDIRECT)} with the host cell family) but is
 * neither emitted nor executed here, and no cross-module or dynamic
 * invocation is executed.</p>
 */
public class ImportMemberReadArmTest {

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

    private static final ModuleId MODULE = new ModuleId("main");
    private static final ModuleId CONSOLE = new ModuleId("std.console");
    private static final ModuleId HOST = new ModuleId("stub.host");
    private static final ModuleId LIB = new ModuleId("lib.util");
    private static final String SOURCE_ID = "read-arm.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = "b".repeat(64);

    private static SemanticIrValidator.ComparisonFacts facts() {
        return new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(SemanticProfile.DEAL_V1_2_INT32,
            deal.semantic.ir.ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    // =========================================================================
    // Checked slices and drives
    // =========================================================================

    private record Slice(ProgramNode program, CheckResult checks) {
    }

    private static Slice checkSlice(String source, ModuleId module, String sourceId,
                                    StubModuleResolver resolver) {
        LexResult lex = new Lexer(source, sourceId).tokenize();
        ParseResult parse = new Parser(lex.tokens(), sourceId, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(),
            "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver names = new NameResolver(module.path(), resolver);
        SymbolTable symbols = names.resolve(parse.program());
        check(names.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + names.diagnostics());
        if (!names.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(module.path(), symbols, names, parse.program());
        check(checks.diagnostics().isEmpty(),
            "the slice checks cleanly: " + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        return new Slice(parse.program(), checks);
    }

    /** The checked export facts of the slice (exported functions). */
    private static List<ExportInterface> exportsOf(ProgramNode program) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ExportDeclaration exported
                    && exported.declaration() instanceof FunctionDeclaration function) {
                exports.add(new ExportInterface(function.name(), "function"));
            }
        }
        return exports;
    }

    /**
     * The recorded coverage rows the slice's produced ops satisfy — a
     * conservative, slice-specific set (R-COVERAGE requires at least one
     * produced op per recorded row).
     */
    private static Map<ConstructKind, List<SemanticOpKind>> coverage(
            ConstructKind... kinds) {
        Map<ConstructKind, List<SemanticOpKind>> map = new EnumMap<>(ConstructKind.class);
        for (ConstructKind kind : kinds) {
            map.put(kind, kind.mappedOpKinds());
        }
        return map;
    }

    private static final ConstructKind[] SLICE_COVERAGE = {
        ConstructKind.IMPORT_EXPORT_ENTRY,
        ConstructKind.FUNCTION_DECLARATION_EXPRESSION,
        ConstructKind.IDENTIFIER,
        ConstructKind.CALL,
        ConstructKind.MEMBER_ACCESS,
        ConstructKind.VARIABLE_DECLARATION,
        ConstructKind.RETURN_EXPRESSION_STATEMENT,
        ConstructKind.SCALAR_LITERAL
    };

    private static final ConstructKind[] SLICE_COVERAGE_IF = {
        ConstructKind.IMPORT_EXPORT_ENTRY,
        ConstructKind.FUNCTION_DECLARATION_EXPRESSION,
        ConstructKind.IDENTIFIER,
        ConstructKind.CALL,
        ConstructKind.MEMBER_ACCESS,
        ConstructKind.VARIABLE_DECLARATION,
        ConstructKind.RETURN_EXPRESSION_STATEMENT,
        ConstructKind.IF_WHILE_FOR_FOR_OF,
        ConstructKind.SCALAR_LITERAL
    };

    /** One full-program E7 drive of one hand-built checked slice. */
    private static SemanticLowerer.FullProgramE7Result drive(String source,
            List<ResolvedImport> imports, Map<ModuleId, ModuleRoute> routes,
            StubModuleResolver resolver, ConstructKind... coverageKinds) {
        return drive(source, imports, routes, resolver, false, coverageKinds);
    }

    private static SemanticLowerer.FullProgramE7Result drive(String source,
            List<ResolvedImport> imports, Map<ModuleId, ModuleRoute> routes,
            StubModuleResolver resolver, boolean withoutImports,
            ConstructKind... coverageKinds) {
        Slice slice = checkSlice(source, MODULE, SOURCE_ID, resolver);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput input = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of(SOURCE_ID), slice.program(), slice.checks(),
            withoutImports ? List.of() : imports, exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        return SemanticLowerer.lowerModuleFullProgramE7(input,
            SemanticProfile.DEAL_V1_2_INT32, coverage(coverageKinds), INTERFACE_HASH,
            REGISTRY_HASH, deal.semantic.ir.SemanticIdAllocator.over(List.of(MODULE)),
            routes, Map.of(), Set.of());
    }

    private static LoweredModuleUnit unitOf(SemanticLowerer.FullProgramE7Result result,
                                            String what) {
        if (result == null || result.lowering() == null) {
            fail(what + ": the E7 drive returns a result");
            return null;
        }
        if (result.lowering().hasErrors() || result.lowering().unit() == null) {
            fail(what + " lowers to a validated unit: " + result.lowering().diagnostics());
            return null;
        }
        return result.lowering().unit();
    }

    private static void assertFailsClosed(SemanticLowerer.FullProgramE7Result result,
                                          String contains, String what) {
        if (result == null || result.lowering() == null) {
            fail(what + ": the E7 drive returns a result");
            return;
        }
        check(result.lowering().hasErrors() && result.lowering().unit() == null,
            what + " fails closed with no unit; got "
                + (result.lowering().hasErrors() ? "diagnostics" : "a unit"));
        if (!result.lowering().hasErrors()) {
            return;
        }
        CompilerDiagnostic diagnostic = result.lowering().diagnostics().get(0);
        check("E6005".equals(diagnostic.code())
                && diagnostic.message().contains(SemanticLowerer.CONSTRUCT_UNLOWERED),
            what + " converts to E6005 CONSTRUCT_UNLOWERED: " + diagnostic);
        check(diagnostic.message().contains(contains),
            what + " names \"" + contains + "\": " + diagnostic);
    }

    // =========================================================================
    // Op inspection helpers
    // =========================================================================

    private static List<SemanticOp> readsOf(LoweredModuleUnit unit) {
        List<SemanticOp> reads = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXPORT_READ) {
                reads.add(op);
            }
        }
        return reads;
    }

    private static KindPayload.ExportReadPayload payloadOf(SemanticOp read) {
        return (KindPayload.ExportReadPayload) read.payload();
    }

    private static SemanticOp opOfKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                return op;
            }
        }
        return null;
    }

    private static List<SemanticOp> opsOfKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    private static FunctionExecutionBinding bindingOf(LoweredModuleUnit unit, ValueId value) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(value.id()));
    }

    private static RuntimeDescriptor.Func funcDescriptor(Type... types) {
        List<RuntimeDescriptor> parameters = new ArrayList<>();
        for (int i = 0; i < types.length - 1; i++) {
            parameters.add(deal.semantic.DescriptorService.describe(types[i]));
        }
        return new RuntimeDescriptor.Func(parameters,
            deal.semantic.DescriptorService.describe(types[types.length - 1]));
    }

    private static int readsOfField(LoweredModuleUnit unit, String name) {
        int count = 0;
        for (SemanticOp read : readsOf(unit)) {
            if (payloadOf(read).name().equals(name)) {
                count++;
            }
        }
        return count;
    }

    private static StdlibFunctionCatalog.Entry rowOf(String modulePath, String exportName) {
        return StdlibFunctionCatalog.lookup(modulePath, exportName)
            .orElseThrow(() -> new IllegalStateException(
                "no catalog row for " + modulePath + "." + exportName));
    }

    private static RuntimeDescriptor.Func rowDescriptorOf(String modulePath, String exportName) {
        return rowOf(modulePath, exportName).declaredDescriptor();
    }

    // =========================================================================
    // AST finders (source-order walk over statements and expressions)
    // =========================================================================

    private static void collectStatements(StatementNode node,
                                          List<StatementNode> outStatements,
                                          List<ExpressionNode> outExpressions) {
        if (node == null) {
            return;
        }
        outStatements.add(node);
        switch (node) {
            case FunctionDeclaration fd ->
                collectStatements(fd.body(), outStatements, outExpressions);
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
            case ExportDeclaration ed ->
                collectStatements(ed.declaration(), outStatements, outExpressions);
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
            default -> {
                // Break/Continue/Import carry no sub-structure.
            }
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
            default -> {
                // Literal/Identifier leaves.
            }
        }
    }

    /** The first member access of the program carrying the given field. */
    private static MemberAccessExpr memberAccess(ProgramNode program, String field) {
        List<MemberAccessExpr> accesses = memberAccesses(program, field);
        return accesses.isEmpty() ? null : accesses.get(0);
    }

    /** Every member access of the program carrying the given field, in source order. */
    private static List<MemberAccessExpr> memberAccesses(ProgramNode program, String field) {
        List<StatementNode> statements = new ArrayList<>();
        List<ExpressionNode> expressions = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            collectStatements(statement, statements, expressions);
        }
        List<MemberAccessExpr> accesses = new ArrayList<>();
        for (ExpressionNode expression : expressions) {
            if (expression instanceof MemberAccessExpr access
                    && access.field().equals(field)) {
                accesses.add(access);
            }
        }
        return accesses;
    }

    /**
     * The {@code EXPORT_READ} produced at the given access's origin (the
     * access span's start line/column), or null — the read is identified
     * by the origin rule under test, never by op order.
     */
    private static SemanticOp readAt(LoweredModuleUnit unit, MemberAccessExpr access) {
        for (SemanticOp read : readsOf(unit)) {
            SourceSpan span = read.origin().span();
            if (span.startLine() == access.span().startLine()
                    && span.startColumn() == access.span().startColumn()) {
                return read;
            }
        }
        return null;
    }

    private static void checkOrigin(SemanticOp op, MemberAccessExpr access, String what) {
        SourceOrigin origin = op.origin();
        check(origin.kind() == SourceOriginKind.USER,
            what + " carries a USER origin; got " + origin.kind());
        SourceSpan span = origin.span();
        check(span.startLine() == access.span().startLine()
                && span.startColumn() == access.span().startColumn()
                && span.endLine() == access.span().endLine()
                && span.endColumn() == access.span().endColumn(),
            what + " carries the access span " + access.span().startLine() + ":"
                + access.span().startColumn() + "; got " + span.startLine() + ":"
                + span.startColumn());
    }

    // =========================================================================
    // 1. The stub battery — STDLIB, both positions
    // =========================================================================

    private static final String STDLIB_SLICE = """
        import * as console from "std/console"

        export function main(): null {
          if (true) {
            let g: (x: string) => null = console.log
            g("x")
          }
          console.log("y")
          return null
        }
        """;

    private static final List<ResolvedImport> STDLIB_IMPORTS = List.of(
        new ResolvedImport("console", "std/console", CONSOLE, ExternalModuleKind.STDLIB));

    private static SemanticLowerer.FullProgramE7Result driveStdlibSlice() {
        return drive(STDLIB_SLICE, STDLIB_IMPORTS, Map.of(), new StubModuleResolver(),
            SLICE_COVERAGE_IF);
    }

    static void testStdlibBothPositions() {
        System.out.println("-- stub battery: STDLIB value + callee positions --");

        Slice slice = checkSlice(STDLIB_SLICE, MODULE, SOURCE_ID, new StubModuleResolver());
        if (slice == null) {
            return;
        }
        LoweredModuleUnit unit = unitOf(driveStdlibSlice(), "the stdlib slice");
        if (unit == null) {
            return;
        }
        RuntimeDescriptor.Func row = rowDescriptorOf("std.console", "log");

        // Exactly one read per source occurrence: the value-position arm
        // and the landed stdlib call-callee arm both call the production.
        check(readsOf(unit).size() == 2,
            "exactly two EXPORT_READs (one per source occurrence); got "
                + readsOf(unit).size());
        check(opsOfKind(unit, SemanticOpKind.STDLIB_CALL).size() == 1,
            "the cataloged call-callee arm keeps its landed STDLIB_CALL");
        for (SemanticOp read : readsOf(unit)) {
            KindPayload.ExportReadPayload payload = payloadOf(read);
            check(payload.module().equals(CONSOLE) && payload.name().equals("log"),
                "the read names std.console/log; got " + payload.module() + "/"
                    + payload.name());
            check(payload.descriptor().equals(row),
                "the read carries the catalog row's declared descriptor "
                    + row.canonicalSpecText() + "; got "
                    + payload.descriptor().canonicalSpecText());
            check(read.resultType().equals(row),
                "the read publishes the row's declared descriptor");
            FunctionExecutionBinding binding = bindingOf(unit, payload.value());
            check(binding instanceof FunctionExecutionBinding.HostFunction host
                    && host.hostModuleId().equals(CONSOLE)
                    && host.exportName().equals("log")
                    && host.descriptor().equals(row),
                "exactly one HostFunction(std.console, log, row descriptor) registration "
                    + "keyed by the read's result identity; got " + binding);
        }

        // The value-position read's origin is the access span and its
        // parent is the position's current parent (the enclosing BRANCH).
        SemanticOp valueRead = null;
        SemanticOp calleeRead = null;
        for (SemanticOp read : readsOf(unit)) {
            if (read.origin().parentOpId() != null) {
                valueRead = read;
            } else {
                calleeRead = read;
            }
        }
        MemberAccessExpr valueAccess = memberAccess(slice.program(), "log");
        check(valueAccess != null, "the slice carries the console.log access");
        if (valueAccess != null && valueRead != null) {
            checkOrigin(valueRead, valueAccess,
                "the value-position read of console.log");
            SemanticOp branch = opOfKind(unit, SemanticOpKind.BRANCH);
            check(branch != null && branch.opId().equals(valueRead.origin().parentOpId()),
                "the value-position read's parentOpId is the position's current parent "
                    + "(the then-block's BRANCH); got " + valueRead.origin().parentOpId());
        }
        check(calleeRead != null && calleeRead.origin().parentOpId() == null,
            "the callee-position read's parentOpId is the position's current parent "
                + "(module top of the body: null)");

        // The typed-binding invocation of the read value lowers through the
        // landed call machine: CALL(INDIRECT) with the Static host binding
        // and the host cell family, admitted by the closed validator.
        SemanticOp indirect = genericCallWithStaticReading(unit);
        if (indirect != null) {
            KindPayload.CallPayload call = (KindPayload.CallPayload) indirect.payload();
            KindPayload.CallCallee.Static callee =
                (KindPayload.CallCallee.Static) call.callee();
            check(call.mode() == deal.semantic.ir.CallMode.INDIRECT,
                "the read value's invocation is CALL(INDIRECT); got " + call.mode());
            check(callee.binding() instanceof FunctionExecutionBinding.HostFunction,
                "the call's Static binding is the read's HostFunction registration; got "
                    + callee.binding());
            check(unit.ops().stream().anyMatch(op ->
                    op.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) op.payload()).kind()
                            == deal.semantic.ir.BoundaryKind.DEAL_TO_HOST
                        && op.failurePolicy() == deal.semantic.ir.FailurePolicyId.HOST_PARAMETER),
                "the invocation builds the DEAL_TO_HOST + HOST_PARAMETER parameter cell");
            check(unit.ops().stream().anyMatch(op ->
                    op.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) op.payload()).kind()
                            == deal.semantic.ir.BoundaryKind.HOST_TO_DEAL
                        && op.failurePolicy() == deal.semantic.ir.FailurePolicyId.HOST_SYNC_RETURN),
                "the invocation builds the HOST_TO_DEAL + HOST_SYNC_RETURN return cell");
        }
    }

    /** The first CALL(INDIRECT) carrying a Static binding, or null. */
    private static SemanticOp genericCallWithStaticReading(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.CALL) {
                continue;
            }
            KindPayload.CallPayload call = (KindPayload.CallPayload) op.payload();
            if (call.callee() instanceof KindPayload.CallCallee.Static) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // 2. The stub battery — HOST, both positions
    // =========================================================================

    private static final String HOST_SLICE = """
        import * as host from "stub/host"

        export function main(): null {
          let p: () => string = host.ping
          let s: string = p()
          host.ping()
          return null
        }
        """;

    private static StubModuleResolver hostResolver() {
        StubModuleResolver resolver = new StubModuleResolver();
        resolver.register("stub/host",
            Map.of("ping", new Type.Func(List.of(), Type.String.INSTANCE)));
        return resolver;
    }

    static void testHostBothPositions() {
        System.out.println("-- stub battery: HOST value + callee positions --");

        Slice slice = checkSlice(HOST_SLICE, MODULE, SOURCE_ID, hostResolver());
        if (slice == null) {
            return;
        }
        SemanticLowerer.FullProgramE7Result result = drive(HOST_SLICE,
            List.of(new ResolvedImport("host", "stub/host", HOST,
                ExternalModuleKind.HOST)),
            Map.of(), hostResolver(), SLICE_COVERAGE);
        LoweredModuleUnit unit = unitOf(result, "the host slice");
        if (unit == null) {
            return;
        }
        RuntimeDescriptor.Func expected = funcDescriptor(Type.String.INSTANCE);
        check(readsOf(unit).size() == 2,
            "the host slice produces exactly one read per position (2); got "
                + readsOf(unit).size());
        for (SemanticOp read : readsOf(unit)) {
            KindPayload.ExportReadPayload payload = payloadOf(read);
            check(payload.module().equals(HOST) && payload.name().equals("ping"),
                "the read names stub.host/ping; got " + payload.module() + "/"
                    + payload.name());
            check(payload.descriptor().equals(expected),
                "the read carries the checked descriptor ()->string; got "
                    + payload.descriptor().canonicalSpecText());
            FunctionExecutionBinding binding = bindingOf(unit, payload.value());
            check(binding instanceof FunctionExecutionBinding.HostFunction host
                    && host.hostModuleId().equals(HOST)
                    && host.exportName().equals("ping")
                    && host.descriptor().equals(expected),
                "exactly one HostFunction(host module, ping, declared descriptor) "
                    + "registration keyed by the read's result identity; got " + binding);
        }
        check(opsOfKind(unit, SemanticOpKind.CALL).stream().anyMatch(op ->
                ((KindPayload.CallPayload) op.payload()).mode()
                    == deal.semantic.ir.CallMode.HOST),
            "the callee-position read feeds the landed CALL(HOST) arm");

        List<MemberAccessExpr> accesses = memberAccesses(slice.program(), "ping");
        check(accesses.size() == 2,
            "the slice carries the value and the callee position accesses; got "
                + accesses.size());
        if (accesses.size() == 2) {
            SemanticOp valueRead = readAt(unit, accesses.get(0));
            SemanticOp calleeRead = readAt(unit, accesses.get(1));
            check(valueRead != null && calleeRead != null,
                "one read is produced at each access's origin");
            if (valueRead != null) {
                checkOrigin(valueRead, accesses.get(0), "the value-position read of ping");
            }
            if (calleeRead != null) {
                checkOrigin(calleeRead, accesses.get(1),
                    "the callee-position read of ping");
            }
            check(readsOf(unit).size() == 2,
                "the two positions produce two reads and no re-production; got "
                    + readsOf(unit).size());
        }
    }

    // =========================================================================
    // 3. The stub battery — COMPILED value read through the route facts
    // =========================================================================

    private static final String COMPILED_SLICE = """
        import * as lib from "./util"

        export function main(): null {
          let f: (v: int) => string = lib.tag
          return null
        }
        """;

    private static StubModuleResolver compiledResolver() {
        StubModuleResolver resolver = new StubModuleResolver();
        resolver.register("./util", Map.of("tag",
            new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE)));
        return resolver;
    }

    private static final List<ResolvedImport> COMPILED_IMPORTS = List.of(
        new ResolvedImport("lib", "./util", LIB, ExternalModuleKind.IMPLEMENTATION));

    static void testCompiledValueReadSharedRoute() {
        System.out.println("-- stub battery: COMPILED value read resolves the route facts --");

        LoweredModuleUnit unit = unitOf(drive(COMPILED_SLICE, COMPILED_IMPORTS,
            Map.of(LIB, ModuleRoute.SHARED), compiledResolver(), SLICE_COVERAGE),
            "the compiled slice");
        if (unit == null) {
            return;
        }
        RuntimeDescriptor.Func expected = funcDescriptor(Type.Int.INSTANCE,
            Type.String.INSTANCE);
        check(readsOf(unit).size() == 1,
            "the value-position read is produced once; got " + readsOf(unit).size());
        SemanticOp read = readsOf(unit).get(0);
        KindPayload.ExportReadPayload payload = payloadOf(read);
        check(payload.module().equals(LIB) && payload.name().equals("tag")
                && payload.descriptor().equals(expected),
            "the read names the compiled companion's declared export tag with the checked "
                + "descriptor (int)->string; got " + payload.module() + "/"
                + payload.name() + " " + payload.descriptor().canonicalSpecText());
        FunctionExecutionBinding binding = bindingOf(unit, payload.value());
        check(binding instanceof FunctionExecutionBinding.ExternalFunction external
                && external.moduleId().equals(LIB)
                && external.exportName().equals("tag")
                && external.descriptor().equals(expected)
                && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
            "exactly one ExternalFunction(compiled module, tag, descriptor, SHARED_BODY) "
                + "registration keyed by the read's result identity; got " + binding);
        check(unit.functionBindings().size() == 4,
            "the unit holds the read's registration, main's body binding, and the two "
                + "intrinsic seeds; got " + unit.functionBindings());
    }

    // =========================================================================
    // 4. The guards of the arm
    // =========================================================================

    static void testGuards() {
        System.out.println("-- the read arm's fail-closed guards --");

        // G2: an alias without a resolved import fact (a carrier session
        // installs no import facts) keeps failing closed with E6005.
        assertFailsClosed(drive(STDLIB_SLICE, STDLIB_IMPORTS, Map.of(),
                new StubModuleResolver(), true, SLICE_COVERAGE_IF),
            "without a resolved import fact",
            "the unresolved-alias read");

        // The COMPILED read without a callee-route record is the same
        // producer defect (the realized drive installs the route facts).
        assertFailsClosed(drive(COMPILED_SLICE, COMPILED_IMPORTS, Map.of(),
                compiledResolver(), SLICE_COVERAGE),
            "callee-route record", "the route-less compiled read");

        // G5: a STDLIB member outside the closed catalog.
        StubModuleResolver outOfCatalog = new StubModuleResolver();
        outOfCatalog.register("std/console",
            Map.of("localMarker", new Type.Func(List.of(), Type.String.INSTANCE)));
        assertFailsClosed(drive("""
            import * as console from "std/console"

            export function main(): null {
              let m: () => string = console.localMarker
              return null
            }
            """, STDLIB_IMPORTS, Map.of(), outOfCatalog, SLICE_COVERAGE),
            "outside the closed stdlib catalog", "the out-of-catalog stdlib read");

        // G6: a STDLIB read whose checked descriptor differs from the
        // catalog row's declared descriptor.
        StubModuleResolver drifted = new StubModuleResolver();
        drifted.register("std/console",
            Map.of("log", new Type.Func(List.of(Type.Int.INSTANCE), Type.Null.INSTANCE)));
        SemanticLowerer.FullProgramE7Result mismatch = drive("""
            import * as console from "std/console"

            export function main(): null {
              let g: (x: int) => null = console.log
              return null
            }
            """, STDLIB_IMPORTS, Map.of(), drifted, SLICE_COVERAGE);
        assertFailsClosed(mismatch, "descriptor", "the stdlib descriptor mismatch read");
        if (mismatch != null && mismatch.lowering() != null
                && mismatch.lowering().hasErrors()) {
            String message = mismatch.lowering().diagnostics().get(0).message();
            check(message.contains("(int)->null") && message.contains("(string)->null"),
                "the descriptor-mismatch failure names the checked descriptor and the "
                    + "catalog row's declared descriptor: " + message);
        }
    }

    // =========================================================================
    // 5. A non-function read produces the read with no registration
    // =========================================================================

    static void testNonFunctionReadRegistersNothing() {
        System.out.println("-- a non-function read registers nothing --");

        // An int export of a compiled companion (a checker-resolved
        // declaration through the stub resolver — the language grammar
        // exports functions and classes only, so the non-function
        // descriptor position is exercised through the checked facts).
        StubModuleResolver resolver = new StubModuleResolver();
        resolver.register("./util", Map.of("count", Type.Int.INSTANCE));
        LoweredModuleUnit unit = unitOf(drive("""
            import * as lib from "./util"

            export function main(): null {
              let n: int = lib.count
              return null
            }
            """, COMPILED_IMPORTS, Map.of(LIB, ModuleRoute.SHARED), resolver,
            SLICE_COVERAGE), "the non-function read slice");
        if (unit == null) {
            return;
        }
        check(readsOf(unit).size() == 1,
            "exactly one EXPORT_READ; got " + readsOf(unit).size());
        SemanticOp read = readsOf(unit).get(0);
        KindPayload.ExportReadPayload payload = payloadOf(read);
        check(payload.module().equals(LIB) && payload.name().equals("count"),
            "the read names the compiled companion's declared int export; got "
                + payload.module() + "/" + payload.name());
        check(payload.descriptor().equals(deal.semantic.DescriptorService.describe(
                Type.Int.INSTANCE)),
            "the read carries the checked int descriptor; got "
                + payload.descriptor().canonicalSpecText());
        check(bindingOf(unit, payload.value()) == null,
            "a non-function read registers nothing; got "
                + bindingOf(unit, payload.value()));
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            check(!(binding instanceof FunctionExecutionBinding.HostFunction)
                    && !(binding instanceof FunctionExecutionBinding.ExternalFunction),
                "no host/external registration exists for the non-function read; got "
                    + binding);
        }
    }

    // =========================================================================
    // 6. Determinism and one-read-per-occurrence
    // =========================================================================

    static void testDeterminism() {
        System.out.println("-- determinism: repeated lowering is byte-identical --");

        SemanticLowerer.FullProgramE7Result first = driveStdlibSlice();
        SemanticLowerer.FullProgramE7Result second = driveStdlibSlice();
        LoweredModuleUnit firstUnit = unitOf(first, "the first stdlib lowering");
        LoweredModuleUnit secondUnit = unitOf(second, "the second stdlib lowering");
        if (firstUnit == null || secondUnit == null) {
            return;
        }
        check(readsOf(firstUnit).size() == readsOf(secondUnit).size(),
            "repeated lowerings produce the same read count; got "
                + readsOf(firstUnit).size() + " and " + readsOf(secondUnit).size());
        check(SemanticIrDumper.dumpModuleText(firstUnit)
                .equals(SemanticIrDumper.dumpModuleText(secondUnit)),
            "repeated lowering produces byte-identical deal.semantic-ir/1 dumps");
    }

    // =========================================================================
    // 7. The focused project run — a compiled companion's function export
    // =========================================================================

    private static final String LIB_SOURCE = """
        export function tag(v: int): string {
          return "t"
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome) {
    }

    private static Fixture compileProject(Map<String, String> sources,
            Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("import-read-arm");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            resolvedExternals.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().toString());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, resolvedExternals,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the probe project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            String specifier = null;
            for (Map.Entry<String, String> external : externals.entrySet()) {
                if (external.getKey().replace('/', '.').equals(declarationModule.path())
                        || external.getKey().equals(declarationModule.path())) {
                    specifier = external.getKey();
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            surface, externCModules, identities,
            DistributionHome.forManifestDirectory(src.toString()));
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    private static LoweredModuleUnit entryUnit(SemanticLowerer.ProjectLoweringResult lowered,
                                               Fixture fixture, String what) {
        if (lowered == null || lowered.hasErrors() || lowered.project() == null) {
            fail(what + " yields the one validated project: "
                + (lowered == null ? "null" : lowered.diagnostics()));
            return null;
        }
        return lowered.project().modules().get(fixture.checkedProject().entryModule());
    }

    static void testProjectCompiledReadOnly() throws Exception {
        System.out.println("-- focused project run: a compiled companion's function export --");

        Fixture fixture = compileProject(Map.of(
            "src/lib.deal", LIB_SOURCE,
            "src/app.deal", """
                import * as lib from "./lib"

                export function main(): null {
                  let f: (v: int) => string = lib.tag
                  return null
                }
                """), Map.of());
        try {
            LoweredModuleUnit unit = entryUnit(lower(fixture), fixture,
                "the compiled-read probe");
            if (unit == null) {
                return;
            }
            check(readsOf(unit).size() == 1,
                "the entry unit carries exactly one EXPORT_READ; got "
                    + readsOf(unit).size());
            SemanticOp read = readsOf(unit).get(0);
            KindPayload.ExportReadPayload payload = payloadOf(read);
            RuntimeDescriptor.Func expected = funcDescriptor(Type.Int.INSTANCE,
                Type.String.INSTANCE);
            check(payload.name().equals("tag") && payload.descriptor().equals(expected),
                "the read names the companion's declared function export tag with the "
                    + "checked descriptor (int)->string; got " + payload.name() + " "
                    + payload.descriptor().canonicalSpecText());
            ModuleId companion = fixture.checkedProject().modules().get(0).moduleId();
            check(payload.module().equals(companion),
                "the read names the compiled companion's resolved module " + companion
                    + "; got " + payload.module());
            FunctionExecutionBinding binding = bindingOf(unit, payload.value());
            check(binding instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY
                    && external.moduleId().equals(payload.module())
                    && external.exportName().equals("tag")
                    && external.descriptor().equals(expected),
                "exactly one ExternalFunction(compiled module, tag, descriptor, "
                    + "SHARED_BODY) registration keyed by the read's result identity; got "
                    + binding);
            check(unit.functionBindings().size() == 4,
                "the registration set is the read's registration, main's body binding, "
                    + "and the two intrinsic seeds; got " + unit.functionBindings());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    static void testProjectHostAndStdlibBothPositions() throws Exception {
        System.out.println("-- project run: HOST and STDLIB in both positions --");

        Fixture fixture = compileProject(Map.of(
            "src/probe.d.deal", "export function ping(): string;\n",
            "src/app.deal", """
                import * as probe from "host/probe"
                import * as console from "std/console"

                export function main(): null {
                  let p: () => string = probe.ping
                  let s: string = p()
                  let g: (x: string) => null = console.log
                  g("x")
                  probe.ping()
                  console.log("y")
                  return null
                }
                """), Map.of("host/probe", "src/probe.d.deal"));
        try {
            LoweredModuleUnit unit = entryUnit(lower(fixture), fixture,
                "the host/stdlib probe");
            if (unit == null) {
                return;
            }
            RuntimeDescriptor.Func ping = funcDescriptor(Type.String.INSTANCE);
            RuntimeDescriptor.Func log = rowDescriptorOf("std.console", "log");
            check(readsOf(unit).size() == 4,
                "both positions of both kinds produce one read each (4); got "
                    + readsOf(unit).size());
            check(readsOfField(unit, "ping") == 2 && readsOfField(unit, "log") == 2,
                "one HOST read per position and one STDLIB read per position");
            for (SemanticOp read : readsOf(unit)) {
                KindPayload.ExportReadPayload payload = payloadOf(read);
                boolean host = payload.name().equals("ping");
                check(payload.descriptor().equals(host ? ping : log),
                    "the " + payload.name() + " read carries the declared descriptor "
                        + (host ? ping : log).canonicalSpecText() + "; got "
                        + payload.descriptor().canonicalSpecText());
                FunctionExecutionBinding binding = bindingOf(unit, payload.value());
                check(binding instanceof FunctionExecutionBinding.HostFunction bound
                        && bound.hostModuleId().equals(payload.module())
                        && bound.exportName().equals(payload.name())
                        && bound.descriptor().equals(payload.descriptor()),
                    "the " + payload.name() + " read registers exactly one HostFunction "
                        + "with the read's module, name, and descriptor; got " + binding);
            }
            check(opsOfKind(unit, SemanticOpKind.STDLIB_CALL).size() == 1,
                "the cataloged stdlib call-callee arm keeps its landed STDLIB_CALL");
            check(opsOfKind(unit, SemanticOpKind.CALL).stream().anyMatch(op ->
                    ((KindPayload.CallPayload) op.payload()).mode()
                        == deal.semantic.ir.CallMode.HOST),
                "the HOST callee position lowers CALL(HOST)");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    static void testProjectClassDefaultSlot() throws Exception {
        System.out.println("-- project run: the slot convention (a class default read) --");

        Fixture fixture = compileProject(Map.of(
            "src/lib.deal", LIB_SOURCE,
            "src/app.deal", """
                import * as lib from "./lib"

                class Holder {
                  f: (v: int) => string = lib.tag
                }

                export function main(): null {
                  return null
                }
                """), Map.of());
        try {
            LoweredModuleUnit unit = entryUnit(lower(fixture), fixture,
                "the class-default probe");
            if (unit == null) {
                return;
            }
            SemanticOp classDefault = opOfKind(unit, SemanticOpKind.CLASS_DEFAULT);
            check(classDefault != null, "the class default produces its CLASS_DEFAULT op");
            check(readsOf(unit).size() == 1,
                "the class default read is produced once; got " + readsOf(unit).size());
            if (classDefault == null || readsOf(unit).size() != 1) {
                return;
            }
            SemanticOp read = readsOf(unit).get(0);
            KindPayload.ExportReadPayload payload = payloadOf(read);
            check(read.result().equals(classDefault.result()),
                "the read publishes the class default's threaded slot; read result "
                    + read.result() + ", CLASS_DEFAULT result " + classDefault.result());
            check(read.origin().parentOpId() != null
                    && read.origin().parentOpId().equals(classDefault.opId()),
                "the read's parentOpId is the position's current parent (the "
                    + "CLASS_DEFAULT op); got " + read.origin().parentOpId());
            FunctionExecutionBinding binding = bindingOf(unit, payload.value());
            check(binding instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                "the registration keys the published cell (the threaded slot); got "
                    + binding);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 8. Registration and gate discipline seeds
    // =========================================================================

    static void testRegistrationDisciplineSeeds() {
        System.out.println("-- registration and gate discipline seeds --");

        // (a) A duplicate registration of the read's exact payload/facts
        // shape is rejected at registration time and never overwrites the
        // first binding.
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        RuntimeDescriptor.Func row = rowDescriptorOf("std.console", "log");
        ValueId value = new ValueId(9_001);
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(value.id());
        KindPayload.ExportReadPayload payload =
            new KindPayload.ExportReadPayload(CONSOLE, "log", row, value);
        FunctionBindingRegistry.FunctionValueImportFacts facts =
            new FunctionBindingRegistry.FunctionValueImportFacts(CONSOLE, null, "log", row);
        registry.registerHostOrExternalImportWithRoutes(identity, payload, facts, Map.of());
        boolean rejected = false;
        try {
            registry.registerHostOrExternalImportWithRoutes(identity, payload, facts,
                Map.of());
        } catch (IllegalStateException expected) {
            rejected = true;
        }
        check(rejected, "a duplicate registration is rejected at registration time");
        check(registry.size() == 1 && registry.bindings().get(identity)
                instanceof FunctionExecutionBinding.HostFunction host
                && host.exportName().equals("log"),
            "the first registration is never overwritten; got " + registry.bindings());

        // (b) A doctored unit whose function-typed read result carries zero
        // registrations fails the closed gate with R-FUNCTION-BINDING.
        LoweredModuleUnit unit = unitOf(driveStdlibSlice(), "the stdlib slice");
        if (unit == null) {
            return;
        }
        check(SemanticIrValidator.validate(unit, facts()).isEmpty(),
            "the unmodified unit passes the closed validator on the typed surface: "
                + SemanticIrValidator.validate(unit, facts()));
        check(SemanticIrValidator.validateText(SemanticIrValidator.toUnitText(unit),
                facts()).isEmpty(),
            "the unmodified unit passes the closed validator on the text surface");
        FunctionAllocationIdentity readKey = null;
        for (SemanticOp read : readsOf(unit)) {
            FunctionAllocationIdentity candidate = new FunctionAllocationIdentity(
                payloadOf(read).value().id());
            if (unit.functionBindings().containsKey(candidate)) {
                readKey = candidate;
                break;
            }
        }
        check(readKey != null, "the read's result identity is a registration key");
        if (readKey == null) {
            return;
        }
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> doctored =
            new LinkedHashMap<>(unit.functionBindings());
        doctored.remove(readKey);
        LoweredModuleUnit mutated = new LoweredModuleUnit(unit.formatVersion(),
            unit.semanticProfile(), unit.moduleId(), unit.interfaceHash(),
            unit.loweringContextHash(), unit.requiredCapabilities(),
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), doctored, unit.ops());
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validate(mutated, facts());
        check(failure.isPresent()
                && failure.get().message().contains("R-FUNCTION-BINDING"),
            "a function-typed read result with zero registrations fails the closed gate "
                + "with R-FUNCTION-BINDING; got "
                + (failure.isEmpty() ? "no diagnostic" : failure.get().message()));
    }

    // =========================================================================
    // Filesystem helpers
    // =========================================================================

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, java.nio.charset.StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path root) {
        if (root == null || !Files.exists(root)) {
            return;
        }
        try (var paths = Files.walk(root)) {
            paths.sorted(java.util.Comparator.reverseOrder()).forEach(path -> {
                try {
                    Files.deleteIfExists(path);
                } catch (java.io.IOException ignored) {
                    // best effort
                }
            });
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Driver
    // =========================================================================

    public static void main(String[] args) throws Exception {
        testStdlibBothPositions();
        testHostBothPositions();
        testCompiledValueReadSharedRoute();
        testGuards();
        testNonFunctionReadRegistersNothing();
        testDeterminism();
        testProjectCompiledReadOnly();
        testProjectHostAndStdlibBothPositions();
        testProjectClassDefaultSlot();
        testRegistrationDisciplineSeeds();
        System.out.println();
        System.out.println("ImportMemberReadArmTest: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
