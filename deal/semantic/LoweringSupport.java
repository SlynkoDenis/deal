package deal.semantic;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
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
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.UnaryOp;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.CheckResult;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.StdlibFunctionId;
import deal.types.Type;
import deal.types.Types;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The requirement-manifest computation of the pre-lowering foundation
 * (F3, one component): one read-only classification over the checked
 * project, producing exactly one {@link SemanticRequirementManifest} per
 * implementation module in {@code CheckedProjectInput} dependency order.
 *
 * <p><b>Closed capability claims.</b> Every implementation module claims
 * {@code FOUNDATION_VALUES}. {@code STDLIB_TIME_CONFLICT} is never claimed
 * since K7: the superseded four-part line trigger
 * ({@code semantic-ir-construct-coverage-cutover} K7 item 6) is retired,
 * so a module referencing {@code std/time.nowMillis} claims through the
 * landed cataloged-call arm below like every other stdlib call, and the
 * closed capability set, the capability-requirement catalog's empty row,
 * the planner's time-conflict reroute, and the validator's
 * empty-evidence rule stay in the tree as inert surfaces. The I3
 * derivation rows (signed-int32 foundation,
 * ISSUE-0395) add exactly one further claim — {@code SIGNED_INT32} —
 * selected by the construct kind, never the magnitude:</p>
 *
 * <ul>
 *   <li>an {@code IntLiteral} of any magnitude → {@code CONST(Int)} → claims
 *       {@code SIGNED_INT32} — a small literal ({@code 1}) claims exactly
 *       like {@code 2147483647}, small literals waive nothing;</li>
 *   <li>a unary negation over an int-typed operand → {@code UNARY(INT32_NEG)}
 *       → claims {@code SIGNED_INT32};</li>
 *   <li>an arithmetic or comparison binary over int-typed operands →
 *       {@code BINARY(INT32_*)} → claims {@code SIGNED_INT32};</li>
 *   <li>an {@code int(...)} intrinsic call → {@code INTRINSIC_CALL(INT_CONVERT)}
 *       → claims {@code SIGNED_INT32}; an {@code number(...)} intrinsic
 *       call → {@code INTRINSIC_CALL(NUMBER_CONVERT)} → claims
 *       {@code FOUNDATION_VALUES} (the module-level row every manifest
 *       carries by construction — {@code NUMBER_CONVERT} never claims
 *       {@code SIGNED_INT32}).</li>
 * </ul>
 *
 * <p>Post-activation this makes every int-using module require target
 * capability {@code SIGNED_INT32} at plan time (F4 rule 4). The closed
 * {@code ConstructKind} set and the S4 capability catalog are untouched —
 * only the construct→capability derivation rows extend.</p>
 *
 * <p>The stdlib epic's plan-time arm ({@code stdlib-operations-and-time-lock}
 * D9): a module whose checked source contains a cataloged stdlib call
 * claims {@code STDLIB_SEMANTICS} — selected by the closed checked-fact
 * recognition predicate ({@link StdlibCallRecognition}: a
 * {@code ModuleSymbol} on a {@code STDLIB}-classified import plus the
 * closed {@link StdlibFunctionCatalog}, never a module/name pair) — so
 * F4 route rule 4's promotion gate covers stdlib-using modules before
 * lowering. A module without a cataloged call never claims it, and a
 * stdlib-export value read (a non-callee position) claims no stdlib
 * capability from the read and adds no route rule (D3). The claim is
 * derived from the checked source only — identical under every
 * invocation purpose.</p>
 *
 * <p><b>The remainder of the closed claims.</b></p>
 * <ul>
 *   <li><b>The stdlib claim:</b> a module whose checked source contains a
 *       cataloged stdlib call claims {@code STDLIB_SEMANTICS} — including
 *       the {@code std.time}/{@code nowMillis} call, whose catalog row is
 *       closed since K7 and whose produced {@code STDLIB_CALL} op is the
 *       claim's evidence. A stdlib-export value read (a non-callee
 *       position) claims no stdlib capability from the read.</li>
 * </ul>
 *
 * <p><b>{@code constructCoverage}.</b> One row per reachable construct
 * of the module's AST over the closed construct→op detector table (S4):
 * the row key is the {@link ConstructKind} the detector maps the AST
 * shape to and the row value is exactly
 * {@link ConstructKind#mappedOpKinds()} verbatim (enforced by the
 * manifest record). A recognized {@code std.time.nowMillis} call records
 * the {@code STDLIB_TIME_NOW_MILLIS} row besides the call row; at
 * lowering start the unit producer copies these rows onto the unit's own
 * enum-keyed {@code constructCoverage} (S1 — the validator's R-COVERAGE
 * fact). ISSUE-0231..0239 extend only the construct→op detector rows,
 * never the closed {@code ConstructKind} set.</p>
 *
 * <p><b>Errors.</b> E6005 through {@code FailureContractRegistry} (T5)
 * with {@code LoweringFailureDetail {module, capability:
 * FOUNDATION_VALUES, validatorRule:
 * MANIFEST_INTERNAL_ERROR_SENTINEL, semanticProfile, irVersion, origin}}
 * for internally inconsistent checked/interface facts only — an import
 * resolving outside the dependency-ordered index, an implementation input
 * entry without its {@code CheckResult} (producer-defect guard: present
 * by construction), an out-of-grammar checked fact the detector requires
 * (a missing or {@link Type.Error} typeMap entry for a
 * {@code nowMillis}-access object, an object literal, or a binary
 * expression; a module symbol without its import declaration). No other
 * new error exists and no SHARED-ineligibility condition is an error
 * here. The computation is strictly read-only — no AST, checker, or
 * symbol-table mutation — and deterministic: dependency-order iteration
 * and the canonical JSON facility make repeated computation
 * byte-identical.</p>
 */
public final class LoweringSupport {

    /**
     * The manifest fact-defect identifier carried as the E6005
     * {@code validatorRule} (foundation F3): a support fact-defect
     * identifier, not a {@code SemanticIrValidator} rule — the closed
     * 14-condition validator rule set is unchanged.
     */
    public static final String MANIFEST_INTERNAL_ERROR_SENTINEL =
        "MANIFEST_INTERNAL_ERROR_SENTINEL";

    private LoweringSupport() {
        // Static computation surface only; no instances.
    }

    /**
     * Computes exactly one {@link SemanticRequirementManifest} per
     * implementation module in {@code CheckedProjectInput} dependency
     * order (foundation F3): one deterministic read-only pass per module
     * over its checked facts, with the index-consistency facts checked
     * first (a resolution outside the dependency-ordered index fails
     * closed with E6005, never a silent under-claim).
     *
     * @param invocation the release-owned compiler invocation; non-null
     * @param input      the checked project input (implementation modules
     *                   in dependency order); non-null
     * @param index      the project interface index covering the full
     *                   dependency closure; non-null
     * @return the manifest result: the dependency-ordered manifests plus
     *         no diagnostics on success, {@code null} manifests plus one
     *         E6005 on an inconsistent-fact defect
     */
    public static RequirementManifestResult computeManifests(CompilerInvocation invocation,
                                                             CheckedProjectInput input,
                                                             ProjectInterfaceIndex index) {
        Objects.requireNonNull(invocation, "invocation must not be null");
        Objects.requireNonNull(input, "input must not be null");
        Objects.requireNonNull(index, "index must not be null");
        try {
            validateIndexFacts(input, index);

            // The ISSUE-0239 E10 imported-by arm's gate: the set of
            // implementation modules imported by another implementation
            // module (the reverse edge of the import graph, computed over
            // the index in one pass — a dependency module's artifact must
            // carry the retained-caller ABI surface while the emission
            // owned wrapper/init facts stay SHADOW).
            Set<ModuleId> implementationDependencies = new LinkedHashSet<>();
            for (ExternalModuleInterface entry : index.modules().values()) {
                if (entry.kind() != ExternalModuleKind.IMPLEMENTATION) {
                    continue;
                }
                for (ResolvedImport resolvedImport : entry.imports()) {
                    if (resolvedImport.kind() == ExternalModuleKind.IMPLEMENTATION) {
                        implementationDependencies.add(resolvedImport.resolvedModuleId());
                    }
                }
            }

            // One dependency-ordered pass over the input modules: each
            // module's claim set and coverage rows are computed from its
            // own checked facts (no cross-module claim propagation exists
            // since K7 — the superseded four-part line detector is
            // retired).
            List<SemanticRequirementManifest> manifests = new ArrayList<>();
            for (CheckedModuleInput module : input.modules()) {
                if (module.kind() != CheckedModuleKind.IMPLEMENTATION) {
                    throw new FactDefect(module.moduleId(),
                        "input entry has kind " + module.kind()
                            + "; the parent-pinned DECLARATION input kind has no producer "
                            + "and every input entry is IMPLEMENTATION (inconsistent input)");
                }
                CheckResult checks = module.checks();
                if (checks == null) {
                    throw new FactDefect(module.moduleId(),
                        "implementation module has no CheckResult (missing checked facts; "
                            + "every input entry is IMPLEMENTATION and typeCheckAll fills its "
                            + "CheckResult)");
                }
                manifests.add(manifestFor(module, implementationDependencies));
            }
            return new RequirementManifestResult(manifests, List.of());
        } catch (FactDefect defect) {
            return failedResult(invocation, defect.module(), defect.getMessage());
        }
    }

    /**
     * Validates the index/input consistency facts the computation needs:
     * every index entry's resolved imports must be index entries, and
     * every implementation input module must appear in the index. Both
     * are producer-defect guards, never silent under-claims (E6005).
     */
    private static void validateIndexFacts(CheckedProjectInput input,
                                           ProjectInterfaceIndex index) throws FactDefect {
        for (ExternalModuleInterface entry : index.modules().values()) {
            for (ResolvedImport resolvedImport : entry.imports()) {
                if (!index.modules().containsKey(resolvedImport.resolvedModuleId())) {
                    throw new FactDefect(entry.moduleId(),
                        "import '" + resolvedImport.modulePath() + "' of module '"
                            + entry.moduleId() + "' resolves to '"
                            + resolvedImport.resolvedModuleId()
                            + "' which is missing from the dependency-ordered index "
                            + "(inconsistent resolution facts)");
                }
            }
        }
        for (CheckedModuleInput module : input.modules()) {
            if (!index.modules().containsKey(module.moduleId())) {
                throw new FactDefect(module.moduleId(),
                    "implementation module is missing from the interface index (the "
                        + "index contradicts the checked project)");
            }
        }
    }

    /**
     * Computes one module's manifest from its own checked facts: the
     * closed capability claims (FOUNDATION_VALUES always; SIGNED_INT32,
     * STDLIB_SEMANTICS, MODULES, CLASSES, CALLS, and
     * CONTAINERS_AND_STRINGS by construct kind) plus the reachable
     * construct rows. One deterministic step per module, never a fixpoint
     * iteration.
     */
    private static SemanticRequirementManifest manifestFor(
            CheckedModuleInput module, Set<ModuleId> implementationDependencies)
            throws FactDefect {
        ModuleScan scan = scanModule(module);
        EnumSet<SemanticCapability> capabilities =
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES);
        // I3 derivation row: int constructs claim SIGNED_INT32 at
        // the construct kind, never the magnitude (a small literal
        // claims exactly like 2147483647) — post-activation F4 rule 4
        // requires SIGNED_INT32 at plan time for every int-using
        // module.
        if (scan.signedInt32) {
            capabilities.add(SemanticCapability.SIGNED_INT32);
        }
        // The plan-time STDLIB_SEMANTICS arm (stdlib epic T5, D9): a
        // module whose checked source contains a cataloged stdlib call
        // claims STDLIB_SEMANTICS before lowering; a module without a
        // cataloged call never claims it, and a stdlib-export value
        // read claims nothing from the read (D3 — no route rule).
        // Since K7 the arm covers the std.time/nowMillis call too.
        if (scan.stdlibCall) {
            capabilities.add(SemanticCapability.STDLIB_SEMANTICS);
        }
        // The modules epic's plan-time arms (ISSUE-0239, E10): a
        // module whose shared artifact cannot yet carry a fact
        // claims the owning capability so F4 rule 4 reroutes it
        // LEGACY at plan time post-activation (the reserved parent
        // verification-3 plan-time edge reroute conditions — an
        // over-claim only forces LEGACY, never E6005 and never a
        // within-run fallback).
        if (scan.importsModule
                || implementationDependencies.contains(module.moduleId())) {
            capabilities.add(SemanticCapability.MODULES);
        }
        // The canonical plan-time CLASSES arm (class epic,
        // ISSUE-0516) covers every class-construct claim: a class
        // declaration, a class-typed object literal (including the
        // builtin Error literal of a throw — the literal position,
        // never a declaration), a class member read/write/delete,
        // and has() — every construct the class epic's arms lower
        // to a class op.
        if (scan.classConstruct) {
            capabilities.add(SemanticCapability.CLASSES);
        }
        if (scan.exportedCalledFromSource
                || scan.awaitsAsync
                || scan.declaresAsyncFunction
                || scan.functionContainer
                || scan.dynamicCall
                || scan.nestedFunctionDeclaration
                || scan.adapterCreation
                || scan.uncalledDeclaredFunction
                || scan.storedFunctionExpression) {
            capabilities.add(SemanticCapability.CALLS);
        }
        if (scan.bytesInContainer || scan.bytesValue) {
            capabilities.add(SemanticCapability.CONTAINERS_AND_STRINGS);
        }
        // The step-1 bytes guard (ISSUE-0574, parent S1b): the
        // manifest's plan-time bytesBearing marker is set exactly
        // from the same triggers as the unchanged claim arm above —
        // the claim stays the construct-ownership fact, the marker
        // is the routing fact planner rule 2b consumes to keep
        // bytes-bearing modules on the retained route in every
        // purpose. A fixed per-module boolean, never a capability,
        // registry entry, registry hash, or schema member.
        boolean bytesBearing = scan.bytesInContainer || scan.bytesValue;
        return new SemanticRequirementManifest(module.moduleId(), capabilities,
            scan.coverage, bytesBearing);
    }

    // =========================================================================
    // Module scan: the closed construct→op detector
    // =========================================================================

    /**
     * The per-module scan state: the reachable-construct coverage rows
     * (enum-keyed, recorded over the closed construct→op detector table of
     * S4) and the claim triggers.
     */
    private static final class ModuleScan {
        /** The I3 {@code SIGNED_INT32} trigger: any int construct —
         * {@code CONST(Int)} (an int literal of any magnitude),
         * {@code UNARY(INT32_NEG)}, {@code BINARY(INT32_*)}, or
         * {@code INTRINSIC_CALL(INT_CONVERT)}. */
        boolean signedInt32;

        /** The plan-time {@code STDLIB_SEMANTICS} trigger: a call whose
         *  callee the closed checked-fact recognition predicate maps to a
         *  catalog entry (D1) — the only common stdlib form (D3); a
         *  stdlib-export value read never sets it. */
        boolean stdlibCall;

        /** The ISSUE-0239 {@code MODULES} trigger: any import
         *  declaration in the module's checked source (the reserved
         *  parent verification-3 plan-time edge reroute condition — the
         *  over-claim only forces LEGACY post-activation). */
        boolean importsModule;

        /** The ISSUE-0239 {@code CALLS} trigger: a direct call of one of
         *  the module's own exported functions from source (the
         *  single-invocation-shape guard's plan-time arm — an exported
         *  function called from source would carry two invocation shapes
         *  under the statically-resolved call machine; ISSUE-0531's
         *  runtime selection is the deferred closure). */
        boolean exportedCalledFromSource;

        /** The module's exported names (the export-fact arm's gate). */
        final Set<String> exportNames = new LinkedHashSet<>();

        /** The plan-time {@code CLASSES} trigger (ISSUE-0516): a class
         *  declaration, a class-typed object literal (including the
         *  builtin {@code Error} literal of a {@code throw} — the
         *  literal position, never a declaration), a member access or
         *  write/delete target on a class-typed receiver, or a
         *  {@code has()} expression — every checked construct the class
         *  epic's arms lower to a class op. Type-only references never
         *  set it. */
        boolean classConstruct;

        /** The ISSUE-0239 {@code CALLS} async trigger: any await
         *  expression in the module's checked source (ASYNC_START/AWAIT
         *  execution stays SHADOW in this slice). */
        boolean awaitsAsync;

        /** The ISSUE-0239 {@code CALLS} async-declaration trigger: any
         *  async function declaration or expression in the module's
         *  checked source (the retained async-export wrapper protocol
         *  and async body execution stay SHADOW in this slice). */
        boolean declaresAsyncFunction;

        /** The ISSUE-0239 container trigger: a for-of iterable whose
         *  checked type carries a function type (function elements are
         *  called through the iteration binding). */
        boolean functionContainer;
        /** The ISSUE-0239 container trigger: a for-of iterable whose
         *  checked type carries bytes. */
        boolean bytesInContainer;

        /** The ISSUE-0239 {@code CONTAINERS_AND_STRINGS} trigger: any
         *  walked expression whose checked type carries bytes —
         *  {@code bytes(...)} calls, bytes {@code .length}/index
         *  positions, and bytes-typed values anywhere in the checked
         *  source (the position claims the owning capability; the
         *  plan-time marker additionally drives the retained route's
         *  bytesBearing row, while the production path lowers the bytes
         *  construct through the shared bytes surface, K6). */
        boolean bytesValue;

        /** The ISSUE-0239 {@code CALLS} trigger: a call of a
         *  dynamically-resolved function value — a variable, parameter,
         *  catch binding, or iteration binding (the E7 call machine
         *  resolves only statically tracked function identities;
         *  ISSUE-0531's runtime selection is the deferred closure), or a
         *  callee shape outside the statically-resolved identifier and
         *  import-member set. */
        boolean dynamicCall;

        /** The ISSUE-0239 {@code CALLS} trigger: a function declaration
         *  nested inside a function body (nested local functions and
         *  nested recursion shapes carry no registered execution
         *  binding in this slice). */
        boolean nestedFunctionDeclaration;

        /** The ISSUE-0239 {@code CALLS} trigger: a function-typed
         *  variable-initializer or assignment position whose declared
         *  signature is assignable-but-not-exact (the closed D15
         *  {@code FUNCTION_ADAPT} creation rule — the produced adapter
         *  op has no shared emission in this slice). */
        boolean adapterCreation;

        /** The ISSUE-0239 {@code CALLS} trigger: a function expression
         *  (closure) in a stored/embedded value position — a binding
         *  initializer, an array/table literal element, a call
         *  argument, or a return value — whose body has no direct
         *  invocation. The closure body's RETURN boundary names no
         *  invocation shape and the closed validator rejects the unit
         *  (R-BOUNDARY-TRIPLE), so the position claims CALLS and F4
         *  rule 4 reroutes the module LEGACY at plan time (an
         *  over-claim only forces LEGACY, never E6005). The
         *  directly-invoked shape (an IIFE callee) is exempt: its
         *  body's RETURN names the enclosing CALL — and the
         *  dynamic-callee arm claims that call anyway. */
        boolean storedFunctionExpression;

        /** The ISSUE-0239 {@code CALLS} trigger: a non-exported declared
         *  function with zero source call sites (every non-exported
         *  declared function's single return boundary names an existing
         *  invocation; an uncalled one fails the closed validator). */
        boolean uncalledDeclaredFunction;

        /** The current function-body nesting depth (mutable walk state:
         *  incremented around every function body walk — a declaration
         *  seen at depth {@code > 0} is a nested local function). */
        int functionBodyDepth;

        /** Every declared function symbol in source order (identity-keyed
         *  call accounting; the never-called arm runs after the walk). */
        final List<Symbol.FunctionSymbol> declaredFunctions = new ArrayList<>();

        /** Every declared function symbol actually called from source,
         *  collected during the statement walk (identity-keyed:
         *  same-name declarations in different scopes are distinct
         *  symbols). The never-called arm runs after the walk, so the
         *  accounting is declaration-order-independent — a call site
         *  walked before the callee's declaration still counts. */
        final Set<Symbol.FunctionSymbol> calledFunctionSymbols =
            java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());

        final Map<ConstructKind, List<SemanticOpKind>> coverage =
            new EnumMap<>(ConstructKind.class);

        void cover(ConstructKind kind) {
            coverage.putIfAbsent(kind, kind.mappedOpKinds());
        }
    }

    private static ModuleScan scanModule(CheckedModuleInput module) throws FactDefect {
        ModuleScan scan = new ModuleScan();
        for (deal.semantic.ir.ExportInterface export : module.exports()) {
            scan.exportNames.add(export.name());
        }
        // The checker's module root table is the site scope at module
        // level; nested scopes are entered per walked statement below
        // (mirroring TypeChecker.walkStatement).
        walkStatements(module.ast().statements(), module, scan,
            module.checks().symbolTable());
        // The never-called arm (post-walk): a non-exported declared
        // function with zero source call sites cannot lower under the
        // statically-resolved call machine (its single return boundary
        // must name an existing invocation) — the module claims CALLS so
        // F4 rule 4 reroutes it LEGACY at plan time. The called-symbol
        // set is collected over the whole statement walk before this
        // check runs, so the result is declaration-order-independent:
        // a main-first module calling a later-declared helper counts the
        // call exactly like a callee-first layout.
        for (Symbol.FunctionSymbol declared : scan.declaredFunctions) {
            if (!scan.exportNames.contains(declared.name())
                    && !scan.calledFunctionSymbols.contains(declared)) {
                scan.uncalledDeclaredFunction = true;
            }
        }
        return scan;
    }

    private static void walkStatements(List<StatementNode> statements,
                                       CheckedModuleInput module, ModuleScan scan,
                                       SymbolTable checkerScope)
            throws FactDefect {
        for (StatementNode statement : statements) {
            walkStatement(statement, module, scan, checkerScope);
        }
    }

    /**
     * Walks one statement under the checker's site scope — exactly the
     * scope the checker resolved the statement's identifiers in, never
     * the module root table alone. Mirrors
     * {@code TypeChecker.walkStatement}: when pass-1 recorded a
     * per-scope symbol table for the statement
     * ({@code CheckResult.scopeMap()}), that table is the scope for the
     * statement's whole subtree ({@link SymbolTable#resolve} walks the
     * chain to the module root, so a nested binding shadows a
     * module-level import alias exactly like the checker resolves it).
     * The scope is threaded as a parameter, so sibling statements
     * automatically keep the enclosing scope.
     */
    private static void walkStatement(StatementNode statement, CheckedModuleInput module,
                                      ModuleScan scan, SymbolTable checkerScope)
            throws FactDefect {
        SymbolTable stmtScope = module.checks().scopeMap().get(statement);
        if (stmtScope != null) {
            checkerScope = stmtScope;
        }
        switch (statement) {
            case ImportDeclaration ignored -> {
                scan.cover(ConstructKind.IMPORT_EXPORT_ENTRY);
                scan.importsModule = true;
            }
            case ExportDeclaration exportDeclaration -> {
                scan.cover(ConstructKind.IMPORT_EXPORT_ENTRY);
                walkStatement(exportDeclaration.declaration(), module, scan, checkerScope);
            }
            case ClassDeclaration classDeclaration -> {
                scan.cover(ConstructKind.CLASS_DECLARATION);
                scan.classConstruct = true;
                for (ClassField field : classDeclaration.fields()) {
                    if (field.defaultExpr().isPresent()) {
                        walkExpression(field.defaultExpr().get(), module, scan,
                            checkerScope);
                    }
                }
            }
            case FunctionDeclaration functionDeclaration -> {
                scan.cover(ConstructKind.FUNCTION_DECLARATION_EXPRESSION);
                if (functionDeclaration.isAsync()) {
                    scan.declaresAsyncFunction = true;
                }
                // The ISSUE-0239 CALLS nested-declaration arm: a function
                // declaration inside a function body (nested local
                // functions and nested recursion shapes) carries no
                // registered execution binding in this slice.
                if (scan.functionBodyDepth > 0) {
                    scan.nestedFunctionDeclaration = true;
                }
                // The never-called arm's fact: record the declaration's
                // function symbol for the post-walk call-count check.
                Symbol declared = checkerScope.resolve(functionDeclaration.name());
                if (declared instanceof Symbol.FunctionSymbol functionSymbol) {
                    scan.declaredFunctions.add(functionSymbol);
                }
                if (functionDeclaration.body() != null) {
                    scan.functionBodyDepth++;
                    try {
                        walkStatement(functionDeclaration.body(), module, scan,
                            checkerScope);
                    } finally {
                        scan.functionBodyDepth--;
                    }
                }
            }
            case VariableDeclaration variableDeclaration -> {
                scan.cover(ConstructKind.VARIABLE_DECLARATION);
                walkExpression(variableDeclaration.initializer(), module, scan,
                    checkerScope);
                // The closed D15 FUNCTION_ADAPT creation-rule arm
                // (ISSUE-0239): a variable-initializer position whose
                // declared binding signature is a function type and whose
                // source value is a different (assignable-but-not-exact)
                // function type produces FUNCTION_ADAPT — an op without
                // a shared emission in this slice.
                noteAdapterCreation(module, scan, checkerScope,
                    variableDeclaration.name(), variableDeclaration.initializer());
            }
            case ReturnStatement returnStatement -> {
                scan.cover(ConstructKind.RETURN_EXPRESSION_STATEMENT);
                if (returnStatement.expr().isPresent()) {
                    walkExpression(returnStatement.expr().get(), module, scan,
                        checkerScope);
                }
            }
            case IfStatement ifStatement -> {
                scan.cover(ConstructKind.IF_WHILE_FOR_FOR_OF);
                walkExpression(ifStatement.condition(), module, scan, checkerScope);
                walkStatement(ifStatement.thenBlock(), module, scan, checkerScope);
                if (ifStatement.elseBranch().isPresent()) {
                    walkEither(ifStatement.elseBranch().get(), module, scan, checkerScope);
                }
            }
            case WhileStatement whileStatement -> {
                scan.cover(ConstructKind.IF_WHILE_FOR_FOR_OF);
                walkExpression(whileStatement.condition(), module, scan, checkerScope);
                walkStatement(whileStatement.body(), module, scan, checkerScope);
            }
            case ForStatement forStatement -> {
                scan.cover(ConstructKind.IF_WHILE_FOR_FOR_OF);
                if (forStatement.init().isPresent()) {
                    walkForInit(forStatement.init().get(), module, scan, checkerScope);
                }
                if (forStatement.condition().isPresent()) {
                    walkExpression(forStatement.condition().get(), module, scan,
                        checkerScope);
                }
                if (forStatement.update().isPresent()) {
                    walkExpression(forStatement.update().get(), module, scan,
                        checkerScope);
                }
                walkStatement(forStatement.body(), module, scan, checkerScope);
            }
            case ForOfStatement forOfStatement -> {
                scan.cover(ConstructKind.IF_WHILE_FOR_FOR_OF);
                Type iterableType = checkedType(module, forOfStatement.iterable());
                if (Types.containsBytes(iterableType)) {
                    scan.bytesInContainer = true;
                }
                if (containsFunction(iterableType)) {
                    scan.functionContainer = true;
                }
                walkExpression(forOfStatement.iterable(), module, scan, checkerScope);
                walkStatement(forOfStatement.body(), module, scan, checkerScope);
            }
            case BreakStatement ignored -> scan.cover(ConstructKind.BREAK_CONTINUE);
            case ContinueStatement ignored -> scan.cover(ConstructKind.BREAK_CONTINUE);
            case ExpressionStatement expressionStatement -> {
                scan.cover(ConstructKind.RETURN_EXPRESSION_STATEMENT);
                walkExpression(expressionStatement.expr(), module, scan, checkerScope);
            }
            case DeleteStatement deleteStatement -> {
                scan.cover(ConstructKind.DELETE);
                // The target's own member/index access is the write
                // position of the delete chain (D14) — the commit ops are
                // MEMBER_DELETE/INDEX_DELETE, named by the DELETE row,
                // never by the read rows; its receiver/key walk normally.
                walkWriteTarget(deleteStatement.target(), module, scan, checkerScope);
            }
            case TryStatement tryStatement -> {
                scan.cover(ConstructKind.TRY_CATCH_THROW);
                walkStatement(tryStatement.tryBlock(), module, scan, checkerScope);
                walkStatement(tryStatement.catchBlock(), module, scan, checkerScope);
            }
            case ThrowStatement throwStatement -> {
                scan.cover(ConstructKind.TRY_CATCH_THROW);
                walkExpression(throwStatement.expr(), module, scan, checkerScope);
            }
            case Block block ->
                walkStatements(block.statements(), module, scan, checkerScope);
        }
    }

    private static void walkEither(Either<IfStatement, Block> branch,
                                   CheckedModuleInput module, ModuleScan scan,
                                   SymbolTable checkerScope)
            throws FactDefect {
        switch (branch) {
            case Either.Left<IfStatement, Block> left ->
                walkStatement(left.value(), module, scan, checkerScope);
            case Either.Right<IfStatement, Block> right ->
                walkStatement(right.value(), module, scan, checkerScope);
        }
    }

    private static void walkForInit(ForInit init, CheckedModuleInput module,
                                    ModuleScan scan, SymbolTable checkerScope)
            throws FactDefect {
        switch (init) {
            case ForInit.VarDecl varDecl ->
                walkStatement(varDecl.decl(), module, scan, checkerScope);
            case ForInit.AssignExpr assignExpr ->
                walkExpression(assignExpr.expr(), module, scan, checkerScope);
        }
    }

    private static void walkExpression(ExpressionNode expression, CheckedModuleInput module,
                                       ModuleScan scan, SymbolTable checkerScope)
            throws FactDefect {
        // The ISSUE-0239 CONTAINERS_AND_STRINGS bytes arm: a walked
        // expression whose checked type carries bytes — bytes(...) calls,
        // bytes .length/index positions, and bytes-typed values anywhere in
        // the checked source — claims the owning capability at the value
        // position (the claim also sets the manifest's bytesBearing row the
        // retained route's rule 2b consumes; the production path lowers the
        // bytes construct through the shared bytes surface, K6).
        if (Types.containsBytes(checkedType(module, expression))) {
            scan.bytesValue = true;
        }
        switch (expression) {
            case LiteralExpr literalExpr -> {
                scan.cover(ConstructKind.SCALAR_LITERAL);
                // I3: CONST(Int) claims SIGNED_INT32 at the construct
                // kind, never the magnitude — a small literal claims
                // exactly like 2147483647.
                if (literalExpr.value() instanceof LiteralValue.IntLiteral) {
                    scan.signedInt32 = true;
                }
            }
            case IdentifierExpr ignored -> scan.cover(ConstructKind.IDENTIFIER);
            case BinaryExpr binaryExpr -> {
                Type type = checkedType(module, binaryExpr);
                // `string +` lowers to STRING_CONCAT (S4); every other
                // binary operator — arithmetic and comparison alike — is
                // the UNARY/BINARY row (logical operators use
                // selector-bearing BRANCH, named by the same row).
                if (binaryExpr.op() == BinaryOp.ADD && type == Type.String.INSTANCE) {
                    scan.cover(ConstructKind.STRING_CONCAT_TEMPLATE);
                } else {
                    scan.cover(ConstructKind.UNARY_ARITHMETIC_COMPARISON);
                    // I3: BINARY(INT32_*) claims SIGNED_INT32 — every
                    // arithmetic and comparison selector over int-typed
                    // operands (number/string/boolean/null/nullable/
                    // reference selectors do not).
                    if (checkedType(module, binaryExpr.left())
                            == Type.Int.INSTANCE) {
                        scan.signedInt32 = true;
                    }
                }
                walkExpression(binaryExpr.left(), module, scan, checkerScope);
                walkExpression(binaryExpr.right(), module, scan, checkerScope);
            }
            case UnaryExpr unaryExpr -> {
                scan.cover(ConstructKind.UNARY_ARITHMETIC_COMPARISON);
                // I3: UNARY(INT32_NEG) claims SIGNED_INT32 — a negation
                // over an int-typed operand; BOOL_NOT and NUMBER_NEG do not.
                if (unaryExpr.op() == UnaryOp.NEG
                        && checkedType(module, unaryExpr.expr())
                            == Type.Int.INSTANCE) {
                    scan.signedInt32 = true;
                }
                walkExpression(unaryExpr.expr(), module, scan, checkerScope);
            }
            case CallExpr callExpr -> {
                // A cataloged stdlib call is the closed CALL row's
                // STDLIB_CALL form — never CROSS_MODULE_CALL: the row's
                // mapped op kinds are {CALL, CALLBACK_INVOKE,
                // INTRINSIC_CALL, STDLIB_CALL, ASYNC_START, AWAIT}, the
                // exact production of the lowerer's stdlib branch. The
                // classification runs the closed checked-fact
                // recognition predicate (D1 — ModuleSymbol on a
                // STDLIB-classified import plus the catalog), never a
                // module/name pair — against the checker's site scope:
                // the innermost per-scope symbol table of the walk (the
                // module root only at module level), exactly the scope
                // the checker resolved the callee identifier in. A
                // nested-scope binding shadowing a stdlib import alias
                // therefore never claims (D1's shadowed-binding
                // negative: the checker resolved the call to the local
                // binding, not the import).
                Optional<StdlibFunctionCatalog.Entry> stdlibEntry =
                    StdlibCallRecognition.recognize(callExpr.callee(), checkerScope,
                        module.imports());
                boolean stdlibCall = stdlibEntry.isPresent();
                if (stdlibCall) {
                    // The plan-time STDLIB_SEMANTICS arm (D9): a cataloged
                    // stdlib call claims STDLIB_SEMANTICS before lowering,
                    // so route rule 4's promotion gate covers the module.
                    // Since K7 the arm covers the std.time/nowMillis call
                    // (the catalog row is closed; the claim's evidence is
                    // the produced STDLIB_CALL op), and the recognized
                    // time construct records its own coverage row besides
                    // the call row.
                    scan.stdlibCall = true;
                    if (stdlibEntry.get().function()
                            == StdlibFunctionId.TIME_NOW_MILLIS) {
                        scan.cover(ConstructKind.STDLIB_TIME_NOW_MILLIS);
                    }
                }
                // The callee classification (I3 + the ISSUE-0239 E10
                // CALLS arms): a declared function call counts the call
                // site (the never-called arm's fact) and pins the
                // exported-from-source dual shape; a call of a variable,
                // parameter, catch binding, or iteration binding is a
                // dynamically-resolved function value; a non-identifier,
                // non-import-member callee (call result, index, closure
                // expression) is runtime callee selection (ISSUE-0531's
                // deferred closure) — every shape the statically-resolved
                // call machine cannot lower claims CALLS so F4 rule 4
                // reroutes LEGACY at plan time.
                ExpressionNode callee = callExpr.callee();
                Symbol calleeSymbol = null;
                boolean importMemberCallee = false;
                if (callee instanceof IdentifierExpr identifier) {
                    calleeSymbol = checkerScope.resolve(identifier.name());
                    if (calleeSymbol instanceof Symbol.FunctionSymbol functionSymbol) {
                        // The never-called arm's fact: record the called
                        // symbol (the post-walk check runs after the whole
                        // statement walk, so declaration order never
                        // affects the count).
                        scan.calledFunctionSymbols.add(functionSymbol);
                        if (scan.exportNames.contains(identifier.name())) {
                            scan.exportedCalledFromSource = true;
                        }
                    } else if (calleeSymbol instanceof Symbol.VariableSymbol) {
                        scan.dynamicCall = true;
                    } else if (calleeSymbol instanceof Symbol.IntrinsicSymbol intrinsic
                            && "int".equals(intrinsic.name())) {
                        // I3: INTRINSIC_CALL(INT_CONVERT) claims
                        // SIGNED_INT32; NUMBER_CONVERT claims
                        // FOUNDATION_VALUES (the module-level row every
                        // manifest carries by construction) and never
                        // SIGNED_INT32.
                        scan.signedInt32 = true;
                    }
                } else if (callee instanceof MemberAccessExpr member
                        && member.object() instanceof IdentifierExpr objectIdentifier
                        && checkerScope.resolve(objectIdentifier.name())
                            instanceof Symbol.ModuleSymbol) {
                    importMemberCallee = true;
                } else {
                    scan.dynamicCall = true;
                }
                boolean crossModule = !stdlibCall && importMemberCallee;
                scan.cover(crossModule
                    ? ConstructKind.CROSS_MODULE_CALL
                    : ConstructKind.CALL);
                if (callee instanceof FunctionExpr functionExpr) {
                    // A directly-invoked closure: its body's RETURN names
                    // this call, so the stored-expression arm exempts it
                    // (the dynamic-callee arm above claims the call).
                    walkFunctionExpr(functionExpr, module, scan, checkerScope, true);
                } else {
                    walkExpression(callee, module, scan, checkerScope);
                }
                for (ExpressionNode argument : callExpr.args()) {
                    walkExpression(argument, module, scan, checkerScope);
                }
            }
            case MemberAccessExpr memberAccessExpr -> {
                scan.cover(ConstructKind.MEMBER_ACCESS);
                walkExpression(memberAccessExpr.object(), module, scan, checkerScope);
                // The plan-time CLASSES arm: a member read on a class-typed
                // (or cross-module nullable class) receiver lowers to
                // FIELD_READ.
                if (isClassReceiverType(checkedType(module, memberAccessExpr.object()))) {
                    scan.classConstruct = true;
                }
            }
            case IndexExpr indexExpr -> {
                scan.cover(ConstructKind.INDEX_ACCESS);
                walkExpression(indexExpr.array(), module, scan, checkerScope);
                walkExpression(indexExpr.index(), module, scan, checkerScope);
            }
            case ArrayLiteralExpr arrayLiteralExpr -> {
                scan.cover(ConstructKind.ARRAY_OBJECT_LITERAL);
                walkElements(arrayLiteralExpr.elements(), module, scan, checkerScope);
            }
            case ObjectLiteralExpr objectLiteralExpr -> {
                // A class-typed object literal constructs a class
                // (CLASS_NEW/CLASS_FACTORY); every other object literal
                // constructs an insertion-ordered table (TABLE_NEW).
                Type type = checkedType(module, objectLiteralExpr);
                scan.cover(type instanceof Type.Class
                    ? ConstructKind.CLASS_OBJECT_LITERAL
                    : ConstructKind.ARRAY_OBJECT_LITERAL);
                // The plan-time CLASSES arm: a class-typed literal is
                // CLASS_NEW construction — the builtin Error literal of a
                // throw statement has no declaring declaration in the
                // module, so the literal position claims CLASSES itself
                // (the declaration arm never sees it; an over-claim only
                // forces LEGACY, never E6005). The nullable wrapper is
                // included defensively (a nullable-class literal position).
                if (type instanceof Type.Class
                        || (type instanceof Type.Nullable nullable
                            && nullable.inner() instanceof Type.Class)) {
                    scan.classConstruct = true;
                }
                for (Property property : objectLiteralExpr.properties()) {
                    walkExpression(property.value(), module, scan, checkerScope);
                }
            }
            case FunctionExpr functionExpr ->
                walkFunctionExpr(functionExpr, module, scan, checkerScope, false);
            case HasExpr hasExpr -> {
                scan.cover(ConstructKind.HAS);
                // The plan-time CLASSES arm: has() is checker-pinned to a
                // class receiver with an optional field (E4005), so every
                // has() expression lowers to HAS_FIELD.
                scan.classConstruct = true;
                walkExpression(hasExpr.object(), module, scan, checkerScope);
            }
            case AssignmentExpr assignmentExpr -> {
                scan.cover(ConstructKind.ASSIGNMENT);
                // The target's own member/index access is the write
                // position of the address chain (D14: MEMBER_WRITE/
                // INDEX_WRITE commit ops — never MEMBER_READ/INDEX_READ),
                // so it records no MEMBER_ACCESS/INDEX_ACCESS row; its
                // receiver and key sub-expressions are ordinary reads and
                // walk normally.
                walkWriteTarget(assignmentExpr.target(), module, scan, checkerScope);
                walkExpression(assignmentExpr.value(), module, scan, checkerScope);
                // The closed D15 FUNCTION_ADAPT creation-rule arm
                // (ISSUE-0239): an assignment position whose target is a
                // function-typed binding and whose source value is a
                // different (assignable-but-not-exact) function type
                // produces FUNCTION_ADAPT — an op without a shared
                // emission in this slice. Exact-signature positions store
                // directly and claim nothing.
                if (assignmentExpr.target() instanceof IdentifierExpr identifier) {
                    noteAdapterCreation(module, scan, checkerScope, identifier.name(),
                        assignmentExpr.value());
                }
            }
            case TemplateLiteralExpr templateLiteralExpr -> {
                scan.cover(ConstructKind.STRING_CONCAT_TEMPLATE);
                walkElements(templateLiteralExpr.parts(), module, scan, checkerScope);
            }
            case AwaitExpression awaitExpression -> {
                scan.cover(ConstructKind.AWAIT_ASYNC_CALL);
                scan.awaitsAsync = true;
                walkExpression(awaitExpression.callee(), module, scan, checkerScope);
            }
        }
    }

    /**
     * Walks one function-expression body. The ISSUE-0239 {@code CALLS}
     * stored-expression arm: a function expression in a stored/embedded
     * value position — a binding initializer, an array/table literal
     * element, a call argument, or a return value — whose body has no
     * direct invocation carries a RETURN boundary naming no invocation
     * shape, and the closed validator rejects the unit
     * (R-BOUNDARY-TRIPLE). The position therefore claims {@code CALLS}
     * so F4 rule 4 reroutes the module LEGACY at plan time (an
     * over-claim only forces LEGACY, never E6005 and never a within-run
     * fallback). The directly-invoked shape (an IIFE callee) is exempt:
     * its body's RETURN names the enclosing CALL — the dynamic-callee
     * arm claims that call anyway.
     */
    private static void walkFunctionExpr(FunctionExpr functionExpr,
                                         CheckedModuleInput module, ModuleScan scan,
                                         SymbolTable checkerScope,
                                         boolean directlyInvoked) throws FactDefect {
        scan.cover(ConstructKind.FUNCTION_DECLARATION_EXPRESSION);
        if (functionExpr.isAsync()) {
            scan.declaresAsyncFunction = true;
        }
        if (!directlyInvoked) {
            scan.storedFunctionExpression = true;
        }
        scan.functionBodyDepth++;
        try {
            walkStatement(functionExpr.body(), module, scan, checkerScope);
        } finally {
            scan.functionBodyDepth--;
        }
    }

    private static void walkElements(List<ExpressionNode> elements, CheckedModuleInput module,
                                     ModuleScan scan, SymbolTable checkerScope)
            throws FactDefect {
        for (ExpressionNode element : elements) {
            walkExpression(element, module, scan, checkerScope);
        }
    }

    /** True iff the checked type carries a function type (arrays and
     *  nullables recurse). */
    private static boolean containsFunction(Type type) {
        if (type instanceof Type.Func) {
            return true;
        }
        if (type instanceof Type.Array array) {
            return containsFunction(array.element());
        }
        if (type instanceof Type.Nullable nullable) {
            return containsFunction(nullable.inner());
        }
        return false;
    }

    /**
     * The closed D15 {@code FUNCTION_ADAPT} creation-rule arm
     * (ISSUE-0239 E10): a variable-initializer or assignment position
     * whose declared binding signature is a function type and whose
     * source value's checked type is a different (assignable-but-not-
     * exact) function type produces {@code FUNCTION_ADAPT} — an op with
     * no shared emission in this slice — so the position claims
     * {@code CALLS} (an exact-signature position stores the value
     * directly and claims nothing). The declared binding signature is
     * the checker's {@link Symbol.VariableSymbol} fact of the position's
     * scope — never a target-built inference.
     */
    private static void noteAdapterCreation(CheckedModuleInput module, ModuleScan scan,
                                            SymbolTable checkerScope, String name,
                                            ExpressionNode source) throws FactDefect {
        Symbol symbol = checkerScope.resolve(name);
        if (!(symbol instanceof Symbol.VariableSymbol variable)
                || !(variable.type() instanceof Type.Func target)) {
            return;
        }
        Type sourceType = checkedType(module, source);
        if (sourceType instanceof Type.Func sourceFunc && !sourceFunc.equals(target)) {
            scan.adapterCreation = true;
        }
    }

    /**
     * Walks an assignment/delete target's sub-expressions without
     * recording a read row for the target's own member/index access: the
     * write position of the address chain (D14) produces the commit ops
     * ({@code MEMBER_WRITE}/{@code INDEX_WRITE},
     * {@code MEMBER_DELETE}/{@code INDEX_DELETE}), which are named by the
     * {@code ASSIGNMENT}/{@code DELETE} rows, never by the
     * {@code MEMBER_ACCESS}/{@code INDEX_ACCESS} read rows. The target's
     * receiver and key sub-expressions are ordinary reads and record
     * their own rows ({@code INDEX_ACCESS} for a chained receiver, etc.).
     * A non-member/index target (an identifier) walks normally.
     */
    private static void walkWriteTarget(ExpressionNode target, CheckedModuleInput module,
                                        ModuleScan scan, SymbolTable checkerScope)
            throws FactDefect {
        switch (target) {
            case MemberAccessExpr member -> {
                // The plan-time CLASSES arm: a class-field assignment or
                // delete lowers the FIELD_WRITE/FIELD_DELETE commit op.
                if (isClassReceiverType(checkedType(module, member.object()))) {
                    scan.classConstruct = true;
                }
                walkExpression(member.object(), module, scan, checkerScope);
            }
            case IndexExpr index -> {
                walkExpression(index.array(), module, scan, checkerScope);
                walkExpression(index.index(), module, scan, checkerScope);
            }
            default -> walkExpression(target, module, scan, checkerScope);
        }
    }

    /**
     * The closed class-receiver type predicate of the plan-time
     * {@code CLASSES} arm: a class type, or the cross-module nullable
     * class read shape the checker unwraps for member access
     * ({@code ?C} over a foreign identity). Every other type is not a
     * class receiver.
     */
    private static boolean isClassReceiverType(Type type) {
        return type instanceof Type.Class
            || (type instanceof Type.Nullable nullable
                && nullable.inner() instanceof Type.Class);
    }

    /**
     * The defensive checked-fact guard (F2/F3): a position the detector
     * classifies on must carry its checked type — a missing
     * {@code typeMap} entry or the internal checker sentinel
     * {@link Type.Error} is a producer defect (E6005), never a silent
     * under-claim and never a crash. Post-phase-3 success every checked
     * expression carries its type, so this guard never fires on valid
     * input.
     */
    private static Type checkedType(CheckedModuleInput module, ExpressionNode expression)
            throws FactDefect {
        Type type = module.checks().typeMap().get(expression);
        if (type == null || type == Type.Error.INSTANCE) {
            throw new FactDefect(module.moduleId(),
                "expression at " + expression.span().file() + ":"
                    + expression.span().startLine() + ":" + expression.span().startColumn()
                    + " has no usable checked type (missing checked facts / internal "
                    + "checker sentinel)");
        }
        return type;
    }

    // =========================================================================
    // E6005 through the failure contract registry
    // =========================================================================

    /** An internally inconsistent checked/interface fact (never a crash). */
    private static final class FactDefect extends Exception {
        private final ModuleId module;

        FactDefect(ModuleId module, String message) {
            super(message);
            this.module = Objects.requireNonNull(module, "module must not be null");
        }

        ModuleId module() {
            return module;
        }
    }

    private static RequirementManifestResult failedResult(CompilerInvocation invocation,
                                                          ModuleId module, String reason) {
        LoweringFailureDetail detail = new LoweringFailureDetail(module.path(),
            SemanticCapability.FOUNDATION_VALUES, MANIFEST_INTERNAL_ERROR_SENTINEL,
            invocation.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
            "LoweringSupport " + MANIFEST_INTERNAL_ERROR_SENTINEL + " (" + reason + ")");
        return new RequirementManifestResult(null,
            List.of(FailureContractRegistry.e6005(detail)));
    }
}
