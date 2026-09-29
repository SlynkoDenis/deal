package deal.module;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
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
import deal.ast.Parameter;
import deal.ast.ProgramNode;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.TypeNode;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.diagnostics.DiagnosticRange;
import deal.identity.CanonicalModuleIdentity;
import deal.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The shared typed-evaluator-IR recorder of the default planning epics
 * (ISSUE-0541; {@code provider-versioned-default-plans} D2/D3/D4):
 * records one default expression as a structured typed evaluator IR
 * ({@link DefaultIrNode}) over the checked facts — resolved types from
 * the checker's type map, resolved bindings from the declaration scope,
 * and complete scalar ranges — and walks that IR completely, publishing
 * ordered provisional {@link DefaultResourceOccurrence} records for
 * imported runtime resources and applying the E3020 sync gate to
 * evaluator-scope {@code await}.
 *
 * <p>The walk covers the complete checked expression: nested literals,
 * nested contextual class literals, call arguments, and the statement
 * grammar of function-expression and function-declaration bodies nested
 * inside the default. Occurrences are recorded in pre-order (the
 * consuming construct before its children), so a call whose callee is an
 * imported function records the call-site range before the callee's
 * member-access node would record the member range; deduplication by
 * semantic resource identity keeps the first (call-site) range.
 * References are published exactly for the two pinned forms:
 * a call whose callee resolves to a function declared in an imported
 * module (call-site range) or an imported function referenced as a
 * first-class value (member-access range), and a contextual class
 * literal typed as a plan-bearing class declared in an imported module
 * (literal range). Type-only references publish nothing. Class
 * declarations nested in walked function bodies are not descended into:
 * their defaults are planned separately as their own plan.</p>
 *
 * <p>The E3020 gate applies exactly at evaluator scope: any
 * {@code await} node outside a nested function-expression or
 * function-declaration body. Await inside a nested async function
 * expression body stays legal.</p>
 */
final class DefaultIrRecorder {

    /**
     * The scope-aware type-node resolution seam: the planner supplies
     * the module's {@code NameResolver} positioned at the given scope;
     * the declaration analyzer supplies its declaration-scope resolver.
     */
    @FunctionalInterface
    interface TypeNodeResolver {
        Type resolveTypeNode(TypeNode typeNode, SymbolTable scope);
    }

    // ---- Read-only inputs ----

    private final Map<ExpressionNode, Type> typeMap;
    private final Map<StatementNode, SymbolTable> scopeMap;
    private final Map<String, DefaultPlanImport> imports;
    private final Map<String, deal.identity.CanonicalModuleIdentity>
        classification;
    private final SourceModuleLocation location;
    private final String modulePath;
    private final ProgramNode program;
    private final TypeNodeResolver typeResolver;

    /**
     * Class name &rarr; the import alias the declaring field type
     * annotation names for that class (collected from the field's type
     * node): the importer-local alias a contextual class literal
     * occurrence is attributed to, in preference to the first alias
     * importing the provider.
     */
    private final Map<String, String> qualifiedClassAliases;

    // ---- Outputs ----

    private final LinkedHashMap<String, Symbol> bindings =
        new LinkedHashMap<>();
    private final LinkedHashMap<SemanticResourceIdentity,
        DefaultResourceOccurrence> occurrences = new LinkedHashMap<>();
    private final List<CompilerDiagnostic> awaitDiagnostics =
        new ArrayList<>();

    DefaultIrRecorder(
            Map<ExpressionNode, Type> typeMap,
            Map<StatementNode, SymbolTable> scopeMap,
            Map<String, DefaultPlanImport> imports,
            Map<String, deal.identity.CanonicalModuleIdentity> classification,
            SourceModuleLocation location,
            String modulePath,
            ProgramNode program,
            TypeNodeResolver typeResolver,
            Map<String, String> qualifiedClassAliases) {
        this.typeMap = Objects.requireNonNull(typeMap, "typeMap");
        this.scopeMap = Objects.requireNonNull(scopeMap, "scopeMap");
        this.imports = Objects.requireNonNull(imports, "imports");
        this.classification = Objects.requireNonNull(classification,
            "classification");
        this.location = Objects.requireNonNull(location, "location");
        this.modulePath = Objects.requireNonNull(modulePath, "modulePath");
        this.program = Objects.requireNonNull(program, "program");
        this.typeResolver = Objects.requireNonNull(typeResolver,
            "typeResolver");
        this.qualifiedClassAliases = Map.copyOf(Objects.requireNonNull(
            qualifiedClassAliases, "qualifiedClassAliases"));
    }

    /** The insertion-ordered resolved bindings (read-only view). */
    Map<String, Symbol> bindings() {
        return Collections.unmodifiableMap(bindings);
    }

    /**
     * The ordered, deduplicated provisional occurrence records
     * (first-IR-walk-occurrence order, deduplicated by semantic
     * resource identity).
     */
    List<DefaultResourceOccurrence> occurrences() {
        return List.copyOf(occurrences.values());
    }

    /** The E3020 evaluator-scope-await diagnostics. */
    List<CompilerDiagnostic> awaitDiagnostics() {
        return List.copyOf(awaitDiagnostics);
    }

    /**
     * Records the default expression: returns the IR root with the
     * field type as the root's expected-type context.
     */
    DefaultIrNode record(ExpressionNode root, SymbolTable scope,
                         Type fieldType) {
        return recordExpression(root, scope,
            fieldType == null ? List.of() : List.of(fieldType), true);
    }

    // =====================================================================
    // Expression walk
    // =====================================================================

    private DefaultIrNode recordExpression(ExpressionNode expr,
            SymbolTable scope, List<Type> contexts, boolean evaluatorScope) {
        switch (expr) {
            case LiteralExpr lit -> {
                return node(DefaultIrNode.NodeKind.LITERAL, null,
                    typeMap.get(lit), contexts, List.of(), lit.value(),
                    null, null, lit, lit.span());
            }
            case IdentifierExpr id -> {
                return recordIdentifier(id, scope, contexts);
            }
            case BinaryExpr bin -> {
                return node(DefaultIrNode.NodeKind.BINARY,
                    bin.op().name(), typeMap.get(bin), contexts,
                    List.of(
                        recordExpression(bin.left(), scope, List.of(),
                            evaluatorScope),
                        recordExpression(bin.right(), scope, List.of(),
                            evaluatorScope)),
                    null, null, null, bin, bin.span());
            }
            case UnaryExpr un -> {
                return node(DefaultIrNode.NodeKind.UNARY,
                    un.op().name(), typeMap.get(un), contexts,
                    List.of(recordExpression(un.expr(), scope, List.of(),
                        evaluatorScope)),
                    null, null, null, un, un.span());
            }
            case CallExpr call -> {
                return recordCall(call, scope, contexts, evaluatorScope);
            }
            case MemberAccessExpr mae -> {
                return recordMemberAccess(mae, scope, contexts,
                    evaluatorScope);
            }
            case IndexExpr idx -> {
                return node(DefaultIrNode.NodeKind.INDEX, null,
                    typeMap.get(idx), contexts,
                    List.of(
                        recordExpression(idx.array(), scope, List.of(),
                            evaluatorScope),
                        recordExpression(idx.index(), scope, List.of(),
                            evaluatorScope)),
                    null, null, null, idx, idx.span());
            }
            case ArrayLiteralExpr arr -> {
                List<DefaultIrNode> elements = new ArrayList<>();
                for (ExpressionNode element : arr.elements()) {
                    elements.add(recordExpression(element, scope,
                        List.of(), evaluatorScope));
                }
                return node(DefaultIrNode.NodeKind.ARRAY_LITERAL, null,
                    typeMap.get(arr), contexts, elements, null, null,
                    null, arr, arr.span());
            }
            case ObjectLiteralExpr obj -> {
                return recordObjectLiteral(obj, scope, contexts,
                    evaluatorScope);
            }
            case FunctionExpr fe -> {
                return recordFunctionExpression(fe, scope, contexts);
            }
            case HasExpr has -> {
                return node(DefaultIrNode.NodeKind.HAS, null,
                    typeMap.get(has), contexts,
                    List.of(recordExpression(has.object(), scope,
                        List.of(), evaluatorScope)),
                    null, null, null, has, has.span());
            }
            case AssignmentExpr assign -> {
                Type targetType = typeMap.get(assign.target());
                return node(DefaultIrNode.NodeKind.ASSIGNMENT, null,
                    typeMap.get(assign), contexts,
                    List.of(
                        recordExpression(assign.target(), scope,
                            List.of(), evaluatorScope),
                        recordExpression(assign.value(), scope,
                            targetType == null ? List.of()
                                : List.of(targetType),
                            evaluatorScope)),
                    null, null, null, assign, assign.span());
            }
            case AwaitExpression await -> {
                if (evaluatorScope) {
                    // D2 sync gate: every planned default is a sync
                    // evaluator; await at evaluator scope is E3020 at
                    // the await range.
                    awaitDiagnostics.add(CompilerDiagnostic.error(
                        DiagnosticCode.E3020, "'await' in class default",
                        await.span().range()));
                }
                return node(DefaultIrNode.NodeKind.AWAIT, null,
                    typeMap.get(await), contexts,
                    List.of(recordExpression(await.callee(), scope,
                        List.of(), evaluatorScope)),
                    null, null, null, await, await.span());
            }
            case TemplateLiteralExpr tl -> {
                List<DefaultIrNode> parts = new ArrayList<>();
                for (ExpressionNode part : tl.parts()) {
                    parts.add(recordExpression(part, scope, List.of(),
                        evaluatorScope));
                }
                return node(DefaultIrNode.NodeKind.TEMPLATE_LITERAL, null,
                    typeMap.get(tl), contexts, parts, null, null, null,
                    tl, tl.span());
            }
        }
    }

    private DefaultIrNode recordIdentifier(IdentifierExpr id,
            SymbolTable scope, List<Type> contexts) {
        DefaultIrNode.Target target = null;
        Symbol sym = scope.resolve(id.name());
        if (sym instanceof Symbol.VariableSymbol vs) {
            bindings.putIfAbsent(id.name(), vs);
            target = DefaultIrNode.Target.localBinding(id.name());
        } else if (sym instanceof Symbol.FunctionSymbol fs) {
            bindings.putIfAbsent(id.name(), fs);
            target = DefaultIrNode.Target.sameModuleResource(id.name(),
                sameModuleResource(
                    LexicalDeclarationIdentity.DeclarationKind.FUNCTION,
                    id.name()));
        } else if (sym instanceof Symbol.ClassSymbol cs) {
            bindings.putIfAbsent(id.name(), cs);
            target = DefaultIrNode.Target.sameModuleResource(id.name(),
                sameModuleResource(
                    LexicalDeclarationIdentity.DeclarationKind.CLASS,
                    id.name()));
        } else if (sym instanceof Symbol.IntrinsicSymbol is) {
            bindings.putIfAbsent(id.name(), is);
            target = DefaultIrNode.Target.intrinsic(id.name());
        } else if (sym instanceof Symbol.ModuleSymbol ms) {
            target = DefaultIrNode.Target.moduleAlias(id.name());
        }
        return node(DefaultIrNode.NodeKind.IDENTIFIER, null,
            typeMap.get(id), contexts, List.of(), null, target, null,
            id, id.span());
    }

    private DefaultIrNode recordCall(CallExpr call, SymbolTable scope,
            List<Type> contexts, boolean evaluatorScope) {
        DefaultIrNode.Target target = null;
        if (call.callee() instanceof MemberAccessExpr mae
                && mae.object() instanceof IdentifierExpr id) {
            Symbol sym = scope.resolve(id.name());
            if (sym instanceof Symbol.ModuleSymbol ms) {
                DefaultPlanImport provider = imports.get(id.name());
                Type exportType = provider == null ? null
                    : provider.exports().get(mae.field());
                if (exportType instanceof Type.Func) {
                    // D4: a call whose callee is a function declared in
                    // an imported module records the wrapper at the
                    // call-site range (pre-order: the callee's own
                    // member-access record is deduplicated away).
                    target = recordImportedFunctionWrapper(provider,
                        id.name(), ms.name() + "." + mae.field(),
                        mae.field(), call.span().range());
                }
            }
        } else if (call.callee() instanceof IdentifierExpr cid) {
            Symbol sym = scope.resolve(cid.name());
            if (sym instanceof Symbol.IntrinsicSymbol) {
                // The int/number conversion intrinsics serialize as
                // builtin-target calls.
                target = DefaultIrNode.Target.intrinsic(cid.name());
            }
        }

        List<Type> paramContexts = paramContextsOf(call);
        List<DefaultIrNode> children = new ArrayList<>();
        children.add(recordExpression(call.callee(), scope, List.of(),
            evaluatorScope));
        for (int i = 0; i < call.args().size(); i++) {
            children.add(recordExpression(call.args().get(i), scope,
                i < paramContexts.size()
                    ? List.of(paramContexts.get(i)) : List.of(),
                evaluatorScope));
        }
        return node(DefaultIrNode.NodeKind.CALL, null, typeMap.get(call),
            contexts, children, null, target, null, call, call.span());
    }

    private List<Type> paramContextsOf(CallExpr call) {
        Type calleeType = typeMap.get(call.callee());
        if (calleeType instanceof Type.Func func) {
            return func.paramTypes();
        }
        return List.of();
    }

    private DefaultIrNode recordMemberAccess(MemberAccessExpr mae,
            SymbolTable scope, List<Type> contexts,
            boolean evaluatorScope) {
        DefaultIrNode.Target target = null;
        if (mae.object() instanceof IdentifierExpr id) {
            Symbol sym = scope.resolve(id.name());
            if (sym instanceof Symbol.ModuleSymbol ms) {
                DefaultPlanImport provider = imports.get(id.name());
                Type exportType = provider == null ? null
                    : provider.exports().get(mae.field());
                if (exportType instanceof Type.Func) {
                    // An imported function referenced as a first-class
                    // value: the wrapper reference records at the member
                    // access range (a call site records first at the
                    // call range and deduplicates this).
                    target = recordImportedFunctionWrapper(provider,
                        id.name(), ms.name() + "." + mae.field(),
                        mae.field(), mae.span().range());
                } else if (exportType instanceof Type.Class clsType) {
                    // A class member in expression position cannot
                    // type-check; defensive target only, no occurrence
                    // (contextual class literals record their plan
                    // reference).
                    SemanticResourceIdentity resource = importedResource(
                        provider,
                        LexicalDeclarationIdentity.DeclarationKind.CLASS,
                        mae.field());
                    target = DefaultIrNode.Target.importedResource(
                        ms.name() + "." + mae.field(), resource);
                }
            }
        }
        // Table member reads carry their resolved type as the
        // contextual descriptor (the E3003 contextual-read semantics).
        List<Type> effectiveContexts = contexts;
        Type objectType = typeMap.get(mae.object());
        Type selfType = typeMap.get(mae);
        if (objectType instanceof Type.Table
                && selfType != null && !(selfType instanceof Type.Error)) {
            effectiveContexts = List.of(selfType);
        }
        return node(DefaultIrNode.NodeKind.MEMBER_ACCESS, null,
            typeMap.get(mae), effectiveContexts,
            List.of(recordExpression(mae.object(), scope, List.of(),
                evaluatorScope)),
            null, target, null, mae, mae.span());
    }

    private DefaultIrNode recordObjectLiteral(ObjectLiteralExpr obj,
            SymbolTable scope, List<Type> contexts,
            boolean evaluatorScope) {
        Type resolvedType = typeMap.get(obj);
        DefaultIrNode.Target target = null;
        if (resolvedType instanceof Type.Class cls) {
            Symbol sym = scope.resolve(cls.name());
            Symbol.ClassSymbol sameModule = null;
            if (sym instanceof Symbol.ClassSymbol cs
                    && cs.identity().equals(cls.identity())) {
                sameModule = cs;
            }
            if (sameModule != null) {
                bindings.putIfAbsent(cls.name(), sameModule);
                target = DefaultIrNode.Target.sameModuleResource(
                    cls.name(),
                    sameModuleResource(
                        LexicalDeclarationIdentity.DeclarationKind.CLASS,
                        cls.name()));
            } else if (cls.identity().moduleIdentity()
                    instanceof CanonicalModuleIdentity.BuiltinModule) {
                // The intrinsic Error class construction.
                target = DefaultIrNode.Target.intrinsic(cls.name());
            } else {
                DefaultPlanImport provider = providerForClass(cls);
                if (provider != null) {
                    SemanticResourceIdentity resource = importedResource(
                        provider,
                        LexicalDeclarationIdentity.DeclarationKind.CLASS,
                        cls.name());
                    target = DefaultIrNode.Target.importedResource(
                        cls.name(), resource);
                    if (provider.publishesClassPlans()) {
                        // D4: a contextual class literal typed as a
                        // plan-bearing class declared in an imported
                        // module records the class default plan at the
                        // literal range. Host-declared classes produce
                        // no plan (the host supplies defaults at load)
                        // and publish no occurrence.
                        String alias = aliasFor(provider, cls.name());
                        recordOccurrence(
                            RuntimeResourceReference.Kind
                                .IMPORTED_CLASS_DEFAULT_PLAN,
                            provider, alias, resource,
                            obj.span().range());
                    }
                }
            }
        }
        List<DefaultIrNode> children = new ArrayList<>();
        for (Property property : obj.properties()) {
            children.add(recordExpression(property.value(), scope,
                List.of(), evaluatorScope));
        }
        List<Type> effectiveContexts = contexts;
        if (resolvedType instanceof Type.Class) {
            effectiveContexts = List.of(resolvedType);
        }
        return node(DefaultIrNode.NodeKind.OBJECT_LITERAL, null,
            resolvedType, effectiveContexts, children, null, target,
            null, obj, obj.span());
    }

    /**
     * Records one function body as ordered statement IR nodes (the
     * serializer-owned provider-body entry, ISSUE-0542; design source
     * {@code provider-versioned-default-plans} D9): the body
     * statements walk at non-evaluator scope (await inside the body is
     * legal — the E3020 gate applies only at evaluator scope), and
     * imported-resource reference sites record as ordered occurrences
     * exactly like the default walk. Class declarations nested in the
     * body are not descended into: their defaults are planned
     * separately as their own plan.
     *
     * @param fd          the function declaration whose body to record
     * @param moduleScope the module root scope (the synthetic-fallback
     *                    parent when the pass-1 resolver recorded no
     *                    body scope)
     * @return the ordered body statement IR nodes
     */
    List<DefaultIrNode> recordFunctionBody(FunctionDeclaration fd,
            SymbolTable moduleScope) {
        SymbolTable bodyScope = scopeMap.get(fd.body());
        if (bodyScope == null) {
            bodyScope = moduleScope.enterScope();
            for (Parameter p : fd.params()) {
                Type paramType = typeResolver.resolveTypeNode(p.type(),
                    bodyScope);
                bodyScope.define(p.name(), new Symbol.VariableSymbol(
                    p.name(), paramType, true));
            }
        }
        List<DefaultIrNode> statements = new ArrayList<>();
        for (StatementNode stmt : fd.body().statements()) {
            statements.add(walkStatement(stmt, bodyScope, false));
        }
        return List.copyOf(statements);
    }

    private DefaultIrNode recordFunctionExpression(FunctionExpr fe,
            SymbolTable scope, List<Type> contexts) {
        List<DefaultIrNode> bodyChildren = new ArrayList<>();
        SymbolTable bodyScope = scopeMap.get(fe.body());
        if (bodyScope == null) {
            // The pass-1 resolver never walks class-default
            // subexpressions, so a function-expression body inside a
            // default has no recorded scope; mirror the checker's
            // fallback: a fresh child scope carrying the parameters.
            bodyScope = scope.enterScope();
            for (Parameter p : fe.params()) {
                Type paramType = typeResolver.resolveTypeNode(p.type(),
                    bodyScope);
                bodyScope.define(p.name(), new Symbol.VariableSymbol(
                    p.name(), paramType, true));
            }
        }
        // Await inside a nested function-expression body is not at
        // evaluator scope (D2).
        for (StatementNode stmt : fe.body().statements()) {
            bodyChildren.add(walkStatement(stmt, bodyScope, false));
        }
        return node(DefaultIrNode.NodeKind.FUNCTION_EXPRESSION, null,
            typeMap.get(fe), contexts, bodyChildren, null, null, null,
            fe, fe.span());
    }

    // =====================================================================
    // Statement walk (function bodies nested in a default)
    // =====================================================================

    private DefaultIrNode walkStatement(StatementNode stmt,
            SymbolTable scope, boolean evaluatorScope) {
        SymbolTable stmtScope = scopeMap.get(stmt);
        // The scope the construct itself was checked in (effectively
        // final for the Optional lambdas below).
        final SymbolTable effectiveScope =
            stmtScope != null ? stmtScope : scope;
        switch (stmt) {
            case Block b -> {
                List<DefaultIrNode> children = new ArrayList<>();
                for (StatementNode s : b.statements()) {
                    children.add(walkStatement(s, effectiveScope,
                        evaluatorScope));
                }
                return node(DefaultIrNode.NodeKind.BLOCK, null, null,
                    List.of(), children, null, null, null, b,
                    b.span().range());
            }
            case VariableDeclaration vd -> {
                List<DefaultIrNode> children = new ArrayList<>();
                if (vd.initializer() != null) {
                    children.add(recordExpression(vd.initializer(),
                        effectiveScope, List.of(), evaluatorScope));
                }
                return node(DefaultIrNode.NodeKind.VARIABLE_DECLARATION,
                    null, null, List.of(), children, null, null,
                    vd.name(), vd, vd.span().range());
            }
            case ExpressionStatement es -> {
                return node(DefaultIrNode.NodeKind.EXPRESSION_STATEMENT,
                    null, null, List.of(),
                    List.of(recordExpression(es.expr(), effectiveScope,
                        List.of(), evaluatorScope)),
                    null, null, null, es, es.span().range());
            }
            case ReturnStatement rs -> {
                List<DefaultIrNode> children = new ArrayList<>();
                rs.expr().ifPresent(expr -> children.add(
                    recordExpression(expr, effectiveScope, List.of(),
                        evaluatorScope)));
                return node(DefaultIrNode.NodeKind.RETURN, null, null,
                    List.of(), children, null, null, null, rs,
                    rs.span().range());
            }
            case ThrowStatement th -> {
                return node(DefaultIrNode.NodeKind.THROW, null, null,
                    List.of(),
                    List.of(recordExpression(th.expr(), effectiveScope,
                        List.of(), evaluatorScope)),
                    null, null, null, th, th.span().range());
            }
            case IfStatement is -> {
                List<DefaultIrNode> children = new ArrayList<>();
                children.add(recordExpression(is.condition(),
                    effectiveScope, List.of(), evaluatorScope));
                children.add(walkStatement(is.thenBlock(), effectiveScope,
                    evaluatorScope));
                is.elseBranch().ifPresent(branch -> {
                    switch (branch) {
                        case Either.Left<IfStatement, Block> left ->
                            children.add(walkStatement(left.value(),
                                effectiveScope, evaluatorScope));
                        case Either.Right<IfStatement, Block> right ->
                            children.add(walkStatement(right.value(),
                                effectiveScope, evaluatorScope));
                    }
                });
                return node(DefaultIrNode.NodeKind.IF, null, null,
                    List.of(), children, null, null, null, is,
                    is.span().range());
            }
            case WhileStatement ws -> {
                return node(DefaultIrNode.NodeKind.WHILE, null, null,
                    List.of(),
                    List.of(
                        recordExpression(ws.condition(), effectiveScope,
                            List.of(), evaluatorScope),
                        walkStatement(ws.body(), effectiveScope,
                            evaluatorScope)),
                    null, null, null, ws, ws.span().range());
            }
            case ForStatement fs -> {
                List<DefaultIrNode> children = new ArrayList<>();
                fs.init().ifPresent(init -> {
                    switch (init) {
                        case ForInit.VarDecl vd ->
                            children.add(walkStatement(vd.decl(),
                                effectiveScope, evaluatorScope));
                        case ForInit.AssignExpr ae ->
                            children.add(recordExpression(ae.expr(),
                                effectiveScope, List.of(),
                                evaluatorScope));
                    }
                });
                fs.condition().ifPresent(cond -> children.add(
                    recordExpression(cond, effectiveScope, List.of(),
                        evaluatorScope)));
                fs.update().ifPresent(update -> children.add(
                    recordExpression(update, effectiveScope, List.of(),
                        evaluatorScope)));
                children.add(walkStatement(fs.body(), effectiveScope,
                    evaluatorScope));
                return node(DefaultIrNode.NodeKind.FOR, null, null,
                    List.of(), children, null, null, null, fs,
                    fs.span().range());
            }
            case ForOfStatement fos -> {
                return node(DefaultIrNode.NodeKind.FOR_OF, null, null,
                    List.of(),
                    List.of(
                        recordExpression(fos.iterable(), effectiveScope,
                            List.of(), evaluatorScope),
                        walkStatement(fos.body(), effectiveScope,
                            evaluatorScope)),
                    null, null, fos.varName(), fos, fos.span().range());
            }
            case TryStatement ts -> {
                return node(DefaultIrNode.NodeKind.TRY, null, null,
                    List.of(),
                    List.of(
                        walkStatement(ts.tryBlock(), effectiveScope,
                            evaluatorScope),
                        walkStatement(ts.catchBlock(), effectiveScope,
                            evaluatorScope)),
                    null, null, null, ts, ts.span().range());
            }
            case DeleteStatement ds -> {
                return node(DefaultIrNode.NodeKind.DELETE, null, null,
                    List.of(),
                    List.of(recordExpression(ds.target(), effectiveScope,
                        List.of(), evaluatorScope)),
                    null, null, null, ds, ds.span().range());
            }
            case BreakStatement bs -> {
                return node(DefaultIrNode.NodeKind.BREAK, null, null,
                    List.of(), List.of(), null, null, null, bs,
                    bs.span().range());
            }
            case ContinueStatement cs -> {
                return node(DefaultIrNode.NodeKind.CONTINUE, null, null,
                    List.of(), List.of(), null, null, null, cs,
                    cs.span().range());
            }
            case FunctionDeclaration fd -> {
                // A nested function declaration inside a default: its
                // body is not at evaluator scope (it executes when the
                // nested function is called). Class declarations inside
                // are not descended into (their defaults are planned
                // separately).
                List<DefaultIrNode> children = new ArrayList<>();
                if (fd.body() != null) {
                    children.add(walkStatement(fd.body(), effectiveScope,
                        false));
                }
                DefaultIrNode.Target target = null;
                if (fd.body() != null) {
                    target = DefaultIrNode.Target.sameModuleResource(
                        fd.name(),
                        sameModuleResource(
                            LexicalDeclarationIdentity
                                .DeclarationKind.FUNCTION,
                            fd.name()));
                }
                return node(DefaultIrNode.NodeKind.FUNCTION_DECLARATION,
                    null, null, List.of(), children, null, target,
                    fd.name(), fd, fd.span().range());
            }
            case ClassDeclaration cd -> {
                // The nested class declaration's plan content and gates
                // are its own plan's domain; the IR node carries the
                // declaration and its same-module resource identity for
                // the serializer's inline canonical plan projection.
                DefaultIrNode.Target target =
                    DefaultIrNode.Target.sameModuleResource(cd.name(),
                        sameModuleResource(
                            LexicalDeclarationIdentity
                                .DeclarationKind.CLASS,
                            cd.name()));
                return node(DefaultIrNode.NodeKind.CLASS_DECLARATION,
                    null, null, List.of(), List.of(), null, target,
                    cd.name(), cd, cd.span().range());
            }
            case ImportDeclaration id -> {
                return node(DefaultIrNode.NodeKind.BLOCK, null, null,
                    List.of(), List.of(), null, null, null, id,
                    id.span().range());
            }
            case ExportDeclaration ed -> {
                return walkStatement(ed.declaration(), effectiveScope,
                    evaluatorScope);
            }
        }
    }

    // =====================================================================
    // Helpers
    // =====================================================================

    private static DefaultIrNode node(DefaultIrNode.NodeKind kind,
            String operatorKind, Type resultType, List<Type> contexts,
            List<DefaultIrNode> children, LiteralValue literalValue,
            DefaultIrNode.Target target, String declaredName,
            ExpressionNode expression, Span span) {
        return new DefaultIrNode(kind, operatorKind, resultType, contexts,
            children, literalValue, target, declaredName, null,
            expression, span.range());
    }

    private static DefaultIrNode node(DefaultIrNode.NodeKind kind,
            String operatorKind, Type resultType, List<Type> contexts,
            List<DefaultIrNode> children, LiteralValue literalValue,
            DefaultIrNode.Target target, String declaredName,
            StatementNode statement, DiagnosticRange range) {
        return new DefaultIrNode(kind, operatorKind, resultType, contexts,
            children, literalValue, target, declaredName, statement,
            null, range);
    }

    private void recordOccurrence(RuntimeResourceReference.Kind kind,
            DefaultPlanImport provider, String alias,
            SemanticResourceIdentity resource, DiagnosticRange range) {
        if (resource == null) {
            return;
        }
        occurrences.putIfAbsent(resource, new DefaultResourceOccurrence(
            kind, location.semanticModuleIdentity(),
            provider.location().semanticModuleIdentity(), alias, resource,
            range));
    }

    /**
     * The provider whose classification equals the class type's
     * declaring module identity, or null (an unknown or builtin
     * module).
     */
    private DefaultPlanImport providerForClass(Type.Class cls) {
        deal.identity.CanonicalModuleIdentity target =
            cls.identity().moduleIdentity();
        if (target instanceof CanonicalModuleIdentity.BuiltinModule) {
            return null;
        }
        for (DefaultPlanImport provider : imports.values()) {
            deal.identity.CanonicalModuleIdentity providerIdentity =
                classification.get(provider.modulePath());
            if (target.equals(providerIdentity)) {
                return provider;
            }
        }
        return null;
    }

    /**
     * The import alias to attribute an imported class-literal
     * occurrence to: the alias the declaring field type annotation
     * names for the class when present (the resolved spelling), else
     * the first alias importing the provider (deterministic).
     */
    private String aliasFor(DefaultPlanImport provider, String className) {
        String qualified = qualifiedClassAliases.get(className);
        if (qualified != null && imports.containsKey(qualified)
                && imports.get(qualified).sourcePath()
                    .equals(provider.sourcePath())) {
            return qualified;
        }
        for (Map.Entry<String, DefaultPlanImport> entry
                : imports.entrySet()) {
            if (entry.getValue().sourcePath()
                    .equals(provider.sourcePath())) {
                return entry.getKey();
            }
        }
        // Defensive: never null in a landed occurrence.
        return provider.modulePath();
    }

    /**
     * Records the imported-function wrapper reference of one imported
     * call or first-class member read, and returns its target: the
     * occurrence keys on the wrapper kind, the provider, the alias, and
     * the call-site or member-access range.
     */
    private DefaultIrNode.Target recordImportedFunctionWrapper(
            DefaultPlanImport provider, String alias, String qualifiedName,
            String field, DiagnosticRange range) {
        SemanticResourceIdentity resource = importedResource(provider,
            LexicalDeclarationIdentity.DeclarationKind.FUNCTION, field);
        recordOccurrence(
            RuntimeResourceReference.Kind.IMPORTED_FUNCTION_WRAPPER,
            provider, alias, resource, range);
        return DefaultIrNode.Target.importedResource(qualifiedName, resource);
    }

    private SemanticResourceIdentity sameModuleResource(
            LexicalDeclarationIdentity.DeclarationKind kind, String name) {
        return declarationResource(program, location.semanticModuleIdentity(),
            modulePath, kind, name);
    }

    private SemanticResourceIdentity importedResource(
            DefaultPlanImport provider,
            LexicalDeclarationIdentity.DeclarationKind kind, String name) {
        return declarationResource(provider.program(),
            provider.location().semanticModuleIdentity(),
            provider.modulePath(), kind, name);
    }

    /**
     * The semantic resource identity of one same-module or imported
     * declaration: the declaration's range when findable (a function's
     * synthetic JSON export anchors on its class), the program's range
     * otherwise.
     */
    private static SemanticResourceIdentity declarationResource(
            ProgramNode program, SemanticModuleIdentity moduleIdentity,
            String modulePath,
            LexicalDeclarationIdentity.DeclarationKind kind, String name) {
        StatementNode declaration = kind
                == LexicalDeclarationIdentity.DeclarationKind.FUNCTION
            ? AstDeclarations.findFunctionDeclaration(program, name)
            : AstDeclarations.findClassDeclaration(program, name);
        DiagnosticRange range;
        if (declaration != null) {
            range = declaration.span().range();
        } else if (kind
                == LexicalDeclarationIdentity.DeclarationKind.FUNCTION) {
            ClassDeclaration synthetic =
                AstDeclarations.jsonableClassForSynthetic(program, name);
            range = synthetic != null ? synthetic.span().range()
                : program.span().range();
        } else {
            range = program.span().range();
        }
        return new SemanticResourceIdentity(
            moduleIdentity, kind,
            new LexicalDeclarationIdentity(kind, name, modulePath, range));
    }

    /**
     * Collects className &rarr; alias pairs from a field type
     * annotation: every {@code Alias.ClassName} qualified type in the
     * annotation (recursively through array, nullable, and function
     * types), first occurrence wins.
     */
    static Map<String, String> qualifiedClassAliasesOf(TypeNode typeNode) {
        Map<String, String> aliases = new LinkedHashMap<>();
        collectQualifiedAliases(typeNode, aliases);
        return aliases;
    }

    private static void collectQualifiedAliases(TypeNode typeNode,
            Map<String, String> aliases) {
        switch (typeNode) {
            case deal.ast.QualifiedType q -> aliases.putIfAbsent(
                q.typeName(), q.moduleName());
            case deal.ast.ArrayType arr ->
                collectQualifiedAliases(arr.elementType(), aliases);
            case deal.ast.NullableType n ->
                collectQualifiedAliases(n.innerType(), aliases);
            case deal.ast.FunctionType ft -> {
                for (deal.ast.FunctionTypeParam p : ft.params()) {
                    collectQualifiedAliases(p.type(), aliases);
                }
                collectQualifiedAliases(ft.returnType(), aliases);
            }
            default -> {
                // Primitive/class named types carry no alias.
            }
        }
    }
}
