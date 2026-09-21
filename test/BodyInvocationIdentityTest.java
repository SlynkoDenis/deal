package deal.test;

import deal.ast.ProgramNode;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.types.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0635: the body-invocation identity takeover and the never-called
 * guard removal
 * ({@code project-lowering-entry-and-registration-seeds} D9 and the
 * body-invocation identity contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C10;
 * {@code semantic-ir-construct-coverage-cutover} K12's lowering side).
 *
 * <ol>
 *   <li>five purpose-built minimal checked projects lower through
 *       {@link SemanticLowerer#lowerProject} with zero
 *       {@code CONSTRUCT_UNLOWERED}: a non-exported declaration with zero
 *       call sites whose identity is its {@code CLOSURE_NEW} result, a
 *       never-invoked stored function expression in its declaration form,
 *       its assigned form (the address chain's value child is the
 *       creation op), its slot-written forms (TABLE_SLOT, ARRAY_SLOT,
 *       CLASS_FIELD chains), and a never-invoked recursive-group member
 *       whose identity is the {@code RECURSIVE_GROUP_INIT}
 *       publication;</li>
 *   <li>each body's {@code RETURN} identity resolves in the project
 *       closure to exactly one emitted op, and each body carries exactly
 *       one body-local {@code FUNCTION_RETURN} cell — parented to the
 *       body's {@code RETURN}, on the allocated function's declared return
 *       descriptor under the descriptor-kind rule;</li>
 *   <li>the carrier-slice entry ({@code lowerModuleFullProgram}) carries
 *       the deleted uncalled-declaration guard's successor: the same
 *       finalization materializes a never-called body's identity there
 *       too, so the entry produces a validating unit;</li>
 *   <li>the producer-defect negatives: a body-local identity on a body
 *       with an assigned invocation shape and a body-local boundary
 *       outside its body's {@code RETURN} fail the closed gate with
 *       {@code R-BOUNDARY-TRIPLE}.</li>
 * </ol>
 */
public class BodyInvocationIdentityTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // Fixture 1: a non-exported declaration with zero call sites (size-1 SCC)
    // =========================================================================

    private static final String ZERO_CALL_SITE_SOURCE = """
        function helper(): int {
          return 7;
        }

        export function main(): null {
          // A value reference is not a call site: the declaration keeps zero
          // call sites and its value read publishes the closure identity.
          let ref: () => int = helper;
          return null;
        }
        """;

    private static void testZeroCallSiteDeclaration() throws Exception {
        System.out.println("-- a non-exported declaration with zero call sites: the "
            + "CLOSURE_NEW materializes the identity --");
        RealProject project = compileProject(ZERO_CALL_SITE_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(result.project() != null && result.diagnostics().isEmpty(),
                "the zero-call-site declaration lowers through the project entry with zero "
                    + "CONSTRUCT_UNLOWERED: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            checkEq(1, bodyLocal.size(),
                "exactly one body's RETURN names its function-value creation op (the "
                    + "zero-call-site declaration; main's identity is its entry CALL)");
            for (SemanticOp returned : bodyLocal) {
                KindPayload.ReturnPayload payload =
                    (KindPayload.ReturnPayload) returned.payload();
                SemanticOp creation = resolveOp(unit, payload.enclosingInvocationOpId());
                check(creation != null && creation.kind() == SemanticOpKind.CLOSURE_NEW,
                    "the zero-call-site declaration's identity is its CLOSURE_NEW; got "
                        + (creation == null ? "unresolved" : creation.kind().name()));
                if (creation != null) {
                    assertBodyLocalCell(result, unit, payload.function(), creation);
                }
            }
            // The other body (the entry main) keeps the landed discipline.
            check(bodyLocal.size() != 1 || moduleFunctionCount(unit) == 2,
                "the module lowers exactly the declaration and the entry body; got "
                    + moduleFunctionCount(unit));
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // Fixture 2: a never-invoked stored function expression
    // =========================================================================

    private static final String STORED_EXPRESSION_SOURCE = """
        export function main(): null {
          let f: () => null = function(): null {
            let y: int = 2;
          };
          return null;
        }
        """;

    private static void testNeverInvokedStoredFunctionExpression() throws Exception {
        System.out.println("-- a never-invoked stored function expression: the "
            + "CLOSURE_NEW materializes the identity --");
        RealProject project = compileProject(STORED_EXPRESSION_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(result.project() != null && result.diagnostics().isEmpty(),
                "the never-invoked stored function expression lowers with zero "
                    + "CONSTRUCT_UNLOWERED: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            checkEq(1, bodyLocal.size(),
                "exactly one body's RETURN names its function-value creation op (the "
                    + "stored function expression; main's identity is its entry CALL)");
            for (SemanticOp returned : bodyLocal) {
                KindPayload.ReturnPayload payload =
                    (KindPayload.ReturnPayload) returned.payload();
                SemanticOp creation = resolveOp(unit, payload.enclosingInvocationOpId());
                check(creation != null && creation.kind() == SemanticOpKind.CLOSURE_NEW,
                    "the stored function expression's identity is its CLOSURE_NEW; got "
                        + (creation == null ? "unresolved" : creation.kind().name()));
                if (creation != null) {
                    assertBodyLocalCell(result, unit, payload.function(), creation);
                    check(creation.payload()
                            instanceof KindPayload.ClosureNewPayload closure
                            && closure.function().equals(payload.function()),
                        "the CLOSURE_NEW allocates the returning function");
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // Fixture 2b: a never-invoked stored function expression — the assigned
    // storing form (the address chain's value child is the creation op)
    // =========================================================================

    private static final String ASSIGNED_EXPRESSION_SOURCE = """
        export function main(): null {
          let n: int = 1;
          let g: () => null = function(): null {
            return null;
          };
          n = n + 1;
          g = function(): null {
            return null;
          };
          return null;
        }
        """;

    private static void testAssignedNeverInvokedFunctionExpression() throws Exception {
        System.out.println("-- a never-invoked function expression stored by assignment: "
            + "the closed chain value child is the creation op --");
        RealProject project = compileProject(ASSIGNED_EXPRESSION_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(result.project() != null && result.diagnostics().isEmpty(),
                "the assigned never-invoked function expression lowers with zero "
                    + "diagnostics: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            assertChainChildrenResolve(unit);
            check(chainChildIsCreationOp(unit, AssignTargetKind.VARIABLE),
                "the VARIABLE assignment chain names the function expression's "
                    + "CLOSURE_NEW as its committed value child");
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            checkEq(2, bodyLocal.size(),
                "both never-invoked function expressions carry the body-local identity "
                    + "cell; got " + bodyLocal.size());
            for (SemanticOp returned : bodyLocal) {
                KindPayload.ReturnPayload payload =
                    (KindPayload.ReturnPayload) returned.payload();
                SemanticOp creation = resolveOp(unit, payload.enclosingInvocationOpId());
                check(creation != null && creation.kind() == SemanticOpKind.CLOSURE_NEW,
                    "the assigned expression's identity is its CLOSURE_NEW; got "
                        + (creation == null ? "unresolved" : creation.kind().name()));
                if (creation != null) {
                    assertBodyLocalCell(result, unit, payload.function(), creation);
                    check(creation.opId().equals(payload.enclosingInvocationOpId()),
                        "the body's RETURN names the creation op's own op id (every "
                            + "chain reference to it stays resolvable)");
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // Fixture 2c: a never-invoked stored function expression — the slot-written
    // storing forms (TABLE_SLOT, ARRAY_SLOT, CLASS_FIELD chains)
    // =========================================================================

    private static final String SLOT_WRITTEN_EXPRESSION_SOURCE = """
        class Box {
          run: () => null = function(): null {
            return null;
          };
        }

        export function main(): null {
          let t: table = { run: function(): null { return null; } };
          t.run = function(): null {
            return null;
          };
          let fs: (() => null)[] = [];
          fs[0] = function(): null {
            return null;
          };
          let b: Box = { run: function(): null { return null; } };
          b.run = function(): null {
            return null;
          };
          return null;
        }
        """;

    private static void testSlotWrittenNeverInvokedFunctionExpression() throws Exception {
        System.out.println("-- a never-invoked function expression stored by a slot "
            + "write: the closed chain value child is the creation op --");
        RealProject project = compileProject(SLOT_WRITTEN_EXPRESSION_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(result.project() != null && result.diagnostics().isEmpty(),
                "the slot-written never-invoked function expressions lower with zero "
                    + "diagnostics: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            assertChainChildrenResolve(unit);
            check(chainChildIsCreationOp(unit, AssignTargetKind.TABLE_SLOT),
                "the TABLE_SLOT assignment chain names the function expression's "
                    + "CLOSURE_NEW as its committed value child");
            check(chainChildIsCreationOp(unit, AssignTargetKind.ARRAY_SLOT),
                "the ARRAY_SLOT assignment chain names the function expression's "
                    + "CLOSURE_NEW as its committed value child");
            check(chainChildIsCreationOp(unit, AssignTargetKind.CLASS_FIELD),
                "the CLASS_FIELD assignment chain names the function expression's "
                    + "CLOSURE_NEW as its committed value child");
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            check(bodyLocal.size() >= 3,
                "the three slot-written never-invoked function expressions carry the "
                    + "body-local identity cell; got " + bodyLocal.size());
            for (SemanticOp returned : bodyLocal) {
                KindPayload.ReturnPayload payload =
                    (KindPayload.ReturnPayload) returned.payload();
                SemanticOp creation = resolveOp(unit, payload.enclosingInvocationOpId());
                check(creation != null && creation.kind() == SemanticOpKind.CLOSURE_NEW,
                    "each slot-written expression's identity is its CLOSURE_NEW");
                if (creation != null) {
                    assertBodyLocalCell(result, unit, payload.function(), creation);
                }
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // Fixture 3: a never-invoked recursive-group member
    // =========================================================================

    private static final String RECURSIVE_GROUP_SOURCE = """
        function left(): null {
          let rightRef: () => null = right;
        }

        function right(): null {
          let leftRef: () => null = left;
        }

        export function main(): null {
          return null;
        }
        """;

    private static void testNeverInvokedRecursiveGroupMember() throws Exception {
        System.out.println("-- a never-invoked recursive-group member: the "
            + "RECURSIVE_GROUP_INIT publication carries the member identities --");
        RealProject project = compileProject(RECURSIVE_GROUP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            check(result.project() != null && result.diagnostics().isEmpty(),
                "the never-invoked recursive-group member lowers with zero "
                    + "CONSTRUCT_UNLOWERED: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            List<SemanticOp> groups = opsOfKind(unit, SemanticOpKind.RECURSIVE_GROUP_INIT);
            checkEq(1, groups.size(),
                "exactly one RECURSIVE_GROUP_INIT publishes the pair; got " + groups.size());
            if (groups.size() != 1) {
                return;
            }
            SemanticOp group = groups.get(0);
            KindPayload.RecursiveGroupInitPayload groupPayload =
                (KindPayload.RecursiveGroupInitPayload) group.payload();
            checkEq(2, groupPayload.functions().size(),
                "the group publication names both members");
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            checkEq(2, bodyLocal.size(),
                "both group members carry the body-local return cell; got "
                    + bodyLocal.size());
            Set<FunctionId> members = new LinkedHashSet<>();
            for (SemanticOp returned : bodyLocal) {
                KindPayload.ReturnPayload payload =
                    (KindPayload.ReturnPayload) returned.payload();
                checkEq(group.opId(), payload.enclosingInvocationOpId(),
                    "the member's RETURN names the group publication");
                check(groupPayload.functions().contains(payload.function()),
                    "the group publication includes the returning member");
                members.add(payload.function());
            }
            checkEq(new LinkedHashSet<>(groupPayload.functions()), members,
                "every published member carries its body-local cell");
            for (FunctionId member : groupPayload.functions()) {
                assertBodyLocalCell(result, unit, member, group);
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // The carrier-slice entry: the deleted uncalled-declaration guard
    // =========================================================================

    /**
     * The carrier-slice entry carries no export arm (EXPORT_* is the E7
     * entry's), so its fixture keeps the entry body non-exported: a
     * never-called declaration plus the pinned {@code main(): null}.
     */
    private static final String CARRIER_SLICE_SOURCE = """
        function helper(): int {
          return 7;
        }

        function main(): null {
          let ref: () => int = helper;
          return null;
        }
        """;

    private static final ModuleId CARRIER_MODULE = new ModuleId("carrier");
    private static final String CARRIER_SOURCE_ID = "carrier.deal";

    /**
     * The carrier-slice fixture checked without the orchestrator: the
     * production orchestrator requires the entry module to export
     * {@code main}, and the carrier-slice entry carries no export arm
     * (EXPORT_* is the E7 entry's), so the checked module comes from the
     * real frontend chain directly (lexer, parser, name resolution, type
     * check, checked-project builder, requirement manifest) exactly like
     * the decomposition-tail carrier matrices.
     */
    private static void testCarrierSliceEntryAcceptsNeverCalledDeclaration()
            throws Exception {
        System.out.println("-- the carrier-slice entry: a never-called declaration "
            + "lowers through the deleted guard --");
        CheckedSlice slice = checkSlice(CARRIER_SLICE_SOURCE);
        if (slice == null) {
            return;
        }
        CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation(),
            CARRIER_MODULE, List.of(new ModuleFact(CARRIER_SOURCE_ID, CARRIER_MODULE,
                false, false, slice.program(), Map.of(), slice.symbols(),
                slice.checks(), List.of())));
        check(built != null && !built.hasErrors() && built.input() != null,
            "the carrier-slice checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null) {
            return;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation(),
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty(),
            "the carrier-slice manifests compute cleanly: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()) {
            return;
        }
        CheckedModuleInput module = built.input().modules().get(0);
        SemanticLowerer.LoweringResult result = SemanticLowerer.lowerModuleFullProgram(
            module, SemanticProfile.DEAL_V1_2_INT32,
            manifests.manifests().get(0).constructCoverage(),
            built.index().interfaceIndexDigest(),
            invocation().capabilityRegistryHash(),
            SemanticIdAllocator.over(List.of(module.moduleId())));
        check(!result.hasErrors() && result.unit() != null,
            "the carrier-slice entry lowers the never-called declaration (the "
                + "deleted guard): " + result.diagnostics());
        if (result.unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.unit();
        List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
        checkEq(1, bodyLocal.size(),
            "the carrier-slice entry materializes the never-called body's identity");
        for (SemanticOp returned : bodyLocal) {
            KindPayload.ReturnPayload payload =
                (KindPayload.ReturnPayload) returned.payload();
            check(resolveOp(unit, payload.enclosingInvocationOpId()) != null,
                "the never-called body's RETURN identity resolves to an emitted op");
        }
    }

    /** One carrier-slice fixture's checked frontend facts. */
    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    /** The frontend chain of one carrier-slice fixture, or {@code null}. */
    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, CARRIER_SOURCE_ID).tokenize();
        check(lex.diagnostics().isEmpty(),
            "the carrier-slice fixture lexes: " + lex.diagnostics());
        ParseResult parse = new Parser(lex.tokens(), CARRIER_SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(),
            "the carrier-slice fixture parses: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver resolver = new NameResolver(CARRIER_SOURCE_ID, new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath, String importingModule,
                    Set<String> modulesInProgress) throws ModuleNotFoundException {
                var exports = deal.module.StdlibModuleResolver.stdlibExports(
                    Path.of("std").toAbsolutePath().toString());
                if (!exports.containsKey(modulePath)) {
                    throw new ModuleNotFoundException("Module not found: " + modulePath);
                }
                return exports.get(modulePath);
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                    String importingModule) throws ModuleNotFoundException {
                return null;
            }
        });
        SymbolTable symbols = resolver.resolve(parse.program());
        check(resolver.diagnostics().isEmpty(),
            "the carrier-slice fixture resolves: " + resolver.diagnostics());
        if (!resolver.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(CARRIER_SOURCE_ID, symbols, resolver,
            parse.program());
        check(checks.diagnostics().isEmpty(),
            "the carrier-slice fixture checks: " + checks.diagnostics());
        if (!checks.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

    // =========================================================================
    // The body-local cell assertions (anti-hollow: read the produced unit)
    // =========================================================================

    /**
     * Asserts one body's complete body-invocation identity on the produced
     * unit and the produced project:
     *
     * <ol>
     *   <li>the creation op materializes the identity exactly once (the
     *       unit's op list carries its op id once);</li>
     *   <li>every {@code RETURN} of the body names that identity, and the
     *       identity resolves to an emitted op of the project closure;</li>
     *   <li>the body's {@code RETURN}s name exactly one
     *       {@code FUNCTION_RETURN} boundary, parented to a {@code RETURN}
     *       of the body, on the allocated function's declared return
     *       descriptor under the descriptor-kind rule.</li>
     * </ol>
     */
    private static void assertBodyLocalCell(SemanticLowerer.ProjectLoweringResult result,
            LoweredModuleUnit unit, FunctionId function, SemanticOp creation) {
        int occurrences = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(creation.opId())) {
                occurrences++;
            }
        }
        checkEq(1, occurrences,
            "the creation op materializes the body's invocation identity exactly once");
        check(creation.opId().module().equals(unit.moduleId()),
            "the identity op belongs to the body's module");
        List<SemanticOp> returns = returnOpsOf(unit, function);
        check(!returns.isEmpty(),
            "the body carries its RETURN (the implicit trailing return of a null-returning "
                + "body included)");
        Set<OpId> boundaries = new LinkedHashSet<>();
        for (SemanticOp returned : returns) {
            KindPayload.ReturnPayload payload =
                (KindPayload.ReturnPayload) returned.payload();
            checkEq(creation.opId(), payload.enclosingInvocationOpId(),
                "the body's RETURN names the materialized identity");
            check(resolvesInProject(result.project(), payload.enclosingInvocationOpId()),
                "the RETURN identity resolves in the project closure");
            boundaries.add(payload.returnBoundaryOpId());
        }
        checkEq(1, boundaries.size(), "the body has exactly one return boundary");
        if (boundaries.size() != 1) {
            return;
        }
        OpId boundaryId = boundaries.iterator().next();
        SemanticOp boundary = resolveOp(unit, boundaryId);
        check(boundary != null && boundary.kind() == SemanticOpKind.BOUNDARY,
            "the body's return boundary is an emitted BOUNDARY op");
        if (boundary == null || !(boundary.payload()
                instanceof KindPayload.BoundaryPayload boundaryPayload)) {
            return;
        }
        check(boundaryPayload.kind() == BoundaryKind.FUNCTION_RETURN,
            "the body-local cell is FUNCTION_RETURN; got " + boundaryPayload.kind());
        RuntimeDescriptor.Func signature = unit.functions().get(function) == null
            ? null : unit.functions().get(function).descriptor();
        if (signature == null) {
            fail("the body's LoweredFunction record is carried by the unit");
            return;
        }
        checkEq(signature.returnType(), boundaryPayload.descriptor(),
            "the body-local cell checks the allocated function's declared return "
                + "descriptor");
        checkEq(descriptorKindPolicy(signature.returnType()), boundary.failurePolicy(),
            "the body-local cell carries the descriptor-kind policy");
        boolean parented = false;
        for (SemanticOp returned : returns) {
            parented |= boundary.origin().parentOpId() != null
                && boundary.origin().parentOpId().equals(returned.opId());
        }
        check(parented,
            "the body-local boundary is parented to a RETURN of the body");
    }

    /**
     * The {@code RETURN} ops whose enclosing invocation resolves to a
     * function-value creation op ({@code CLOSURE_NEW} or
     * {@code RECURSIVE_GROUP_INIT}) — the bodies carrying the body-local
     * cell.
     */
    private static List<SemanticOp> bodyLocalReturnCells(LoweredModuleUnit unit) {
        List<SemanticOp> bodyLocal = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.RETURN
                    || !(op.payload() instanceof KindPayload.ReturnPayload payload)) {
                continue;
            }
            SemanticOp invocation = resolveOp(unit, payload.enclosingInvocationOpId());
            if (invocation != null
                    && (invocation.kind() == SemanticOpKind.CLOSURE_NEW
                        || invocation.kind() == SemanticOpKind.RECURSIVE_GROUP_INIT)) {
                bodyLocal.add(op);
            }
        }
        return bodyLocal;
    }

    /**
     * Asserts the closed address chains of the produced unit: every
     * {@code ASSIGN}/{@code DELETE} chain child named by the payload
     * resolves to an emitted op of the unit (the address-chain protocol's
     * child-resolution requirement — the regression's direct measure: a
     * chain referencing a body's creation op keeps resolving after the
     * identity takeover).
     */
    private static void assertChainChildrenResolve(LoweredModuleUnit unit) {
        int chains = 0;
        for (SemanticOp op : unit.ops()) {
            List<OpId> children = null;
            if (op.payload() instanceof KindPayload.AssignPayload assign) {
                children = assign.childOps();
            } else if (op.payload() instanceof KindPayload.DeletePayload delete) {
                children = delete.childOps();
            }
            if (children == null) {
                continue;
            }
            chains++;
            for (OpId child : children) {
                check(resolveOp(unit, child) != null,
                    "the " + op.kind() + " chain child " + child
                        + " resolves to an emitted op of the unit");
            }
        }
        check(chains > 0, "the unit carries closed address chains");
    }

    /**
     * Whether one target kind's {@code ASSIGN} chain names a body's
     * function-value creation op ({@code CLOSURE_NEW}) among its children.
     */
    private static boolean chainChildIsCreationOp(LoweredModuleUnit unit,
            AssignTargetKind targetKind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.ASSIGN
                    || !(op.payload() instanceof KindPayload.AssignPayload assign)
                    || assign.targetKind() != targetKind) {
                continue;
            }
            for (OpId child : assign.childOps()) {
                SemanticOp childOp = resolveOp(unit, child);
                if (childOp != null && childOp.kind() == SemanticOpKind.CLOSURE_NEW) {
                    return true;
                }
            }
        }
        return false;
    }

    // =========================================================================
    // The producer-defect negatives (R-BOUNDARY-TRIPLE)
    // =========================================================================

    private static void testBodyLocalIdentityWithAssignedShape() throws Exception {
        System.out.println("-- the negative: a body-local identity on a body with an "
            + "assigned invocation shape --");
        RealProject project = compileProject(ZERO_CALL_SITE_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            if (result.project() == null) {
                fail("the fixture lowers: " + result.diagnostics());
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            // main's identity is its entry CALL: rebinding main's RETURN to
            // main's own CLOSURE_NEW forges exactly the body-local identity
            // on a body with an assigned invocation shape.
            SemanticOp mainCreation = null;
            FunctionId mainFunction = null;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.ENTRY_INVOKE
                        && op.payload() instanceof KindPayload.EntryInvokePayload entry) {
                    mainFunction = entry.mainFunction();
                }
            }
            for (SemanticOp op : unit.ops()) {
                if (mainFunction != null
                        && op.kind() == SemanticOpKind.CLOSURE_NEW
                        && op.payload() instanceof KindPayload.ClosureNewPayload closure
                        && closure.function().equals(mainFunction)) {
                    mainCreation = op;
                }
            }
            check(mainCreation != null && mainFunction != null,
                "the entry body's CLOSURE_NEW is carried by the unit");
            if (mainCreation == null || mainFunction == null) {
                return;
            }
            LoweredModuleUnit corrupted = withReturnEnclosing(unit, mainFunction,
                mainCreation.opId());
            check(corrupted != null, "the corrupted unit is built");
            if (corrupted == null) {
                return;
            }
            Optional<CompilerDiagnostic> failure = validate(result, corrupted);
            check(failure.isPresent(), "the forged body-local identity fails the gate");
            if (failure.isPresent()) {
                check("E6005".equals(failure.get().code())
                        && failure.get().message().contains(
                            SemanticIrValidator.R_BOUNDARY_TRIPLE)
                        && failure.get().message().contains("assigned invocation shape"),
                    "the forged identity returns the first E6005 R-BOUNDARY-TRIPLE "
                        + "naming the assigned invocation shape; got "
                        + failure.get().message());
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static void testBodyLocalBoundaryOutsideReturn() throws Exception {
        System.out.println("-- the negative: a body-local boundary outside its body's "
            + "RETURN --");
        RealProject project = compileProject(STORED_EXPRESSION_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(project);
            if (result.project() == null) {
                fail("the fixture lowers: " + result.diagnostics());
                return;
            }
            LoweredModuleUnit unit = onlyModule(result.project());
            List<SemanticOp> bodyLocal = bodyLocalReturnCells(unit);
            checkEq(1, bodyLocal.size(), "the fixture carries the body-local cell");
            if (bodyLocal.size() != 1) {
                return;
            }
            KindPayload.ReturnPayload payload =
                (KindPayload.ReturnPayload) bodyLocal.get(0).payload();
            // Re-parenting the boundary to the creation op leaves the
            // boundary under the creation-op identity but outside any RETURN:
            // exactly the rejected body-local boundary.
            LoweredModuleUnit corrupted = withBoundaryParent(unit,
                payload.returnBoundaryOpId(), payload.enclosingInvocationOpId());
            check(corrupted != null, "the corrupted unit is built");
            if (corrupted == null) {
                return;
            }
            Optional<CompilerDiagnostic> failure = validate(result, corrupted);
            check(failure.isPresent(), "the re-parented boundary fails the gate");
            if (failure.isPresent()) {
                check("E6005".equals(failure.get().code())
                        && failure.get().message().contains(
                            SemanticIrValidator.R_BOUNDARY_TRIPLE)
                        && failure.get().message().contains(
                            "must be parented to the body's RETURN"),
                    "the re-parented boundary returns the first E6005 "
                        + "R-BOUNDARY-TRIPLE naming the parent defect; got "
                        + failure.get().message());
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    private static Optional<CompilerDiagnostic> validate(
            SemanticLowerer.ProjectLoweringResult result, LoweredModuleUnit unit) {
        ExecutableLoweredProject project = result.project();
        return SemanticLowerer.validateProjectUnit(unit, result.tableOf(unit.moduleId()),
            new SemanticIrValidator.ComparisonFacts(
                project.interfaceIndex().interfaceIndexDigest(),
                SemanticProfile.DEAL_V1_2_INT32,
                invocation().capabilityRegistryHash()),
            deal.semantic.BindingsProductionValidator.PinnedWriteFacts.empty(),
            result.registryOf(unit.moduleId()),
            new JsonDefaultChildTable(Map.of()),
            project.interfaceIndex().modules().get(unit.moduleId()),
            Map.of());
    }

    // =========================================================================
    // The fixture harness (the production frontend + the project entry)
    // =========================================================================

    private record RealProject(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface) {
    }

    private static RealProject compileProject(String source) throws Exception {
        Path proj = Files.createTempDirectory("body-invocation");
        writeFileIn(proj, "src/app.deal", source);
        Path entry = proj.resolve("src/app.deal").toAbsolutePath();
        Path output = proj.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(proj.resolve("src").toAbsolutePath()),
            Path.of(".").toAbsolutePath().normalize());
        boolean compiled = orchestrator.compile();
        check(compiled, "the fixture compiles through the production pipeline: "
            + orchestrator.diagnostics());
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.hasErrors() || built.input() == null
                || built.index() == null || manifests == null
                || manifests.manifests() == null) {
            deleteRecursively(proj);
            throw new IllegalStateException("the fixture project did not build");
        }
        return new RealProject(proj, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface());
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** One {@link SemanticLowerer#lowerProject} call over the real project. */
    private static SemanticLowerer.ProjectLoweringResult lower(RealProject project) {
        return SemanticLowerer.lowerProject(invocation(), project.checkedProject(),
            project.index(), project.manifests(), project.surface(), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    private static LoweredModuleUnit onlyModule(ExecutableLoweredProject project) {
        check(project.modules().size() == 1,
            "the fixture is one module; got " + project.modules().keySet());
        return project.modules().values().iterator().next();
    }

    private static int moduleFunctionCount(LoweredModuleUnit unit) {
        return unit.functions().size();
    }

    private static List<SemanticOp> opsOfKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                ops.add(op);
            }
        }
        return ops;
    }

    private static List<SemanticOp> returnOpsOf(LoweredModuleUnit unit, FunctionId function) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload payload
                    && payload.function().equals(function)) {
                ops.add(op);
            }
        }
        return ops;
    }

    private static SemanticOp resolveOp(LoweredModuleUnit unit, OpId opId) {
        if (opId == null) {
            return null;
        }
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    private static boolean resolvesInProject(ExecutableLoweredProject project, OpId opId) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            if (resolveOp(unit, opId) != null) {
                return true;
            }
        }
        return false;
    }

    /** The descriptor-kind policy (the closed table's rule). */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    // =========================================================================
    // Hand-built corruptions (the negative seeds)
    // =========================================================================

    /** The unit with one body's RETURNs re-keyed to a forged enclosing identity. */
    private static LoweredModuleUnit withReturnEnclosing(LoweredModuleUnit unit,
            FunctionId function, OpId enclosing) {
        List<SemanticOp> ops = new ArrayList<>();
        boolean rewritten = false;
        for (SemanticOp op : unit.ops()) {
            SemanticOp candidate = op;
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload returned
                    && returned.function().equals(function)) {
                candidate = rebuild(op, new KindPayload.ReturnPayload(returned.value(),
                    returned.function(), enclosing, returned.returnBoundaryOpId()));
                rewritten = true;
            }
            ops.add(candidate);
        }
        return rewritten ? withOps(unit, ops) : null;
    }

    /** The unit with one op re-parented to the given op id. */
    private static LoweredModuleUnit withBoundaryParent(LoweredModuleUnit unit,
            OpId boundaryId, OpId parent) {
        List<SemanticOp> ops = new ArrayList<>();
        boolean rewritten = false;
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(boundaryId)) {
                SourceOrigin origin = op.origin();
                SemanticOp candidate = new SemanticOp(op.opId(), op.kind(),
                    new SourceOrigin(origin.sourceId(), origin.span(), origin.kind(),
                        origin.anchorId(), parent),
                    op.result(), op.resultType(), op.operands(), op.operandTypes(),
                    op.payload(), op.failurePolicy(), op.contract());
                ops.add(candidate);
                rewritten = true;
                continue;
            }
            ops.add(op);
        }
        return rewritten ? withOps(unit, ops) : null;
    }

    /** One op with a replaced payload and its wired contract snapshot. */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        OperationContractSnapshot placeholder = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(),
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), null, payload, op.failurePolicy(), List.of(), digest);
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload,
            op.failurePolicy(), contract);
    }

    /** One lowered unit with the given op list (the corruption surface). */
    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
                                             List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
                        try {
                            Files.deleteIfExists(entry);
                        } catch (java.io.IOException ignored) {
                            // best effort
                        }
                    });
                }
            }
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    public static void main(String[] args) throws Exception {
        System.out.println("=== Body-Invocation Identity Tests (ISSUE-0635) ===\n");
        testZeroCallSiteDeclaration();
        testNeverInvokedStoredFunctionExpression();
        testAssignedNeverInvokedFunctionExpression();
        testSlotWrittenNeverInvokedFunctionExpression();
        testNeverInvokedRecursiveGroupMember();
        testCarrierSliceEntryAcceptsNeverCalledDeclaration();
        testBodyLocalIdentityWithAssignedShape();
        testBodyLocalBoundaryOutsideReturn();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Body-Invocation Identity Tests Passed ===");
    }
}
