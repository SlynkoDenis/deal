package deal.test;

import deal.ast.BinaryExpr;
import deal.ast.BinaryOp;
import deal.ast.ProgramNode;
import deal.ast.FunctionDeclaration;
import deal.ast.StatementNode;
import deal.ast.VariableDeclaration;
import deal.checker.CheckResult;
import deal.checker.Symbol;
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
import deal.semantic.ComparisonSelectorLowering;
import deal.semantic.ControlFlowValidator;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.ir.ReleaseState;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AddressChainProtocol;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ComparisonExecutor;
import deal.semantic.ir.ComparisonOperandView;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.NormalizedSlot;
import deal.semantic.ir.NullableSide;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
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
import deal.semantic.ir.UnicodeScalars;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The decomposition-tail integration verification of the
 * {@code EVALUATION_ORDER} epic (ISSUE-0410): the full three-domain
 * matrix — address chains, comparisons, control flow — runs through the
 * real production chain (lexer → parser → checker → checked project →
 * requirement manifest → lowerer → closed validator → address-chain
 * protocol → control-flow validator) over side-effecting seed programs,
 * with every constituent module's failure injection breaking the chain
 * with its pinned projection.
 *
 * <p>Verification scope of this tail (in-tree): the production chain and
 * the op-level executors ({@link BoundaryExecutor},
 * {@link ComparisonExecutor}, the {@link NormalizedSlot} computation)
 * over the validated op stream — op order and parentage prove
 * evaluation order and single evaluation, block membership proves
 * short-circuit/loop shapes, the lowered boundary payloads executed
 * through {@code BoundaryExecutor} prove the exact E8001/E8002/E8010
 * projections, and {@code ComparisonExecutor} proves the closed B-D2
 * selector rows. Every negative control remains executable, so a duplicated
 * evaluation, a wrong selector, a missing boundary, or a broken
 * constituent module fails the tail. The runtime comparison segment
 * itself — the identical validated unit executed on the semantic
 * oracle and BOTH shared emitters' real artifacts with per-consumer
 * event validation and three-way trace/effect/terminal comparison —
 * executes in {@code deal.test.RuntimeIntegrationMatrixTest}
 * ({@code deal.semantic.SemanticOracle},
 * {@code deal.codegen.lua.LuaSemanticEmitter},
 * {@code deal.codegen.jvm.JvmSemanticEmitter},
 * {@code deal.test.SemanticDifferentialHarness}); no stub
 * substitutes for the three-consumer run.</p>
 */
public class EvaluationOrderIntegrationTest {

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

    private record CheckedSlice(deal.ast.ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private static CheckedSlice checkSlice(String source) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, (ModuleResolver) null);
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the slice resolves cleanly: " + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), "the slice checks cleanly: " + result.diagnostics());
        if (!result.diagnostics().isEmpty()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    /** Checks a slice expecting a checker rejection; returns the diagnostics. */
    private static List<CompilerDiagnostic> checkSliceExpectingErrors(String source,
                                                                      String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return List.of();
        }
        NameResolver nr = new NameResolver(SOURCE_ID, (ModuleResolver) null);
        SymbolTable symTable = nr.resolve(parse.program());
        if (!nr.diagnostics().isEmpty()) {
            return nr.diagnostics();
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        return result.diagnostics();
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

    /** The E5 window (this epic's seam): full production chain + validators. */
    private static SemanticLowerer.LoweringResult lowerDetected(CheckedSlice slice) {
        return SemanticLowerer.lowerModule(moduleOf(slice), SemanticProfile.DEAL_V1_2_INT32,
            detectedCoverage(slice), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /** The binding-core window (comparisons + short circuit + lets). */
    private static SemanticLowerer.BindingCoreResult lowerBindingCoreDetected(
            CheckedSlice slice) {
        return SemanticLowerer.lowerModuleBindingCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, detectedCoverage(slice), INTERFACE_HASH,
            REGISTRY_HASH, SemanticIdAllocator.over(List.of(MODULE)));
    }

    // =========================================================================
    // Finders and rebuild helpers
    // =========================================================================

    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    private static SemanticOp opById(List<SemanticOp> ops, OpId id) {
        for (SemanticOp op : ops) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    private static void checkE6005(Optional<CompilerDiagnostic> diagnostic, String rule,
                                   String what) {
        check(diagnostic.isPresent(), what);
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()) && d.diagnosticCode() == DiagnosticCode.E6005,
            rule + " diagnostic code is E6005");
        check(d.message().contains(rule),
            rule + " message names the pinned rule: " + d.message());
        check(d.message().contains("module 'main'"), rule + " message names the module");
        check(d.message().contains("capability EVALUATION_ORDER")
                || d.message().contains("capability CONTAINERS_AND_STRINGS")
                || d.message().contains("capability FOUNDATION_VALUES"),
            rule + " message names the owning capability: " + d.message());
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit, List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    private static SemanticOp rebuildOp(SemanticOp original, KindPayload payload) {
        return rebuildOpWithPolicy(original, payload, original.failurePolicy());
    }

    private static SemanticOp rebuildOpWithPolicy(SemanticOp original, KindPayload payload,
                                                  FailurePolicyId policy) {
        OperationContractSnapshot placeholder = contractFor(original.kind(), payload,
            original.resultType(), original.operandTypes(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(placeholder);
        OperationContractSnapshot contract = contractFor(original.kind(), payload,
            original.resultType(), original.operandTypes(), policy, digest);
        return new SemanticOp(original.opId(), original.kind(), original.origin(),
            original.result(), original.resultType(), original.operands(),
            original.operandTypes(), payload, policy, contract);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType,
            List<RuntimeDescriptor> operandTypes, FailurePolicyId policy, String digest) {
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, null, payload, policy, List.of(), digest);
    }

    private static StructuredBodyTable rebuildTable(Map<BlockId, List<OpId>> blocks) {
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

    // =========================================================================
    // 1. The chain matrix — order per target kind through the production seam
    // =========================================================================

    static void testChainOrderMatrix() {
        System.out.println("-- Chain matrix: receiver -> key -> RHS -> normalize -> boundary "
            + "-> commit --");

        // (a) ARRAY_SLOT with a variable key: receiver load, key load, RHS
        // CONST, then the normalize-time ARRAY_LENGTH, normalize, boundary,
        // commit — the length read after key and RHS.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: int[] of [[1, 2]]) { for (let k: int of [5]) { xs[k] = 2 } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors() && result.unit() != null,
                "the ARRAY_SLOT variable-key seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors() || result.unit() == null) { return; }
            List<SemanticOp> ops = result.unit().ops();
            SemanticOp chain = ofKind(ops, SemanticOpKind.ASSIGN).get(0);
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) chain.payload();
            check(payload.targetKind() == AssignTargetKind.ARRAY_SLOT,
                "the chain is ARRAY_SLOT");
            check(payload.childOps().size() == 7,
                "the ARRAY_SLOT chain carries 7 children; got "
                    + payload.childOps().size());
            SemanticOp container = opById(ops, payload.childOps().get(0));
            SemanticOp key = opById(ops, payload.childOps().get(1));
            SemanticOp value = opById(ops, payload.childOps().get(2));
            SemanticOp length = opById(ops, payload.childOps().get(3));
            SemanticOp normalize = opById(ops, payload.childOps().get(4));
            SemanticOp boundary = opById(ops, payload.childOps().get(5));
            SemanticOp commit = opById(ops, payload.childOps().get(6));
            check(container.kind() == SemanticOpKind.BINDING_LOAD
                    && key.kind() == SemanticOpKind.BINDING_LOAD
                    && value.kind() == SemanticOpKind.CONST,
                "receiver/key/RHS children are load/load/CONST");
            check(length.kind() == SemanticOpKind.ARRAY_LENGTH,
                "the lengthOp is the ARRAY_LENGTH read");
            check(normalize.kind() == SemanticOpKind.INDEX_NORMALIZE
                    && ((KindPayload.IndexNormalizePayload) normalize.payload()).mode()
                        == IndexMode.ARRAY_WRITE,
                "the normalizeOp is INDEX_NORMALIZE with ARRAY_WRITE mode");
            check(boundary.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) boundary.payload()).kind()
                        == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                    && boundary.failurePolicy()
                        == FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
                "the boundary is ARRAY_ELEMENT_ASSIGNMENT with "
                    + "ARRAY_WRITE_BOUNDS_THEN_ELEMENT");
            check(commit.kind() == SemanticOpKind.INDEX_WRITE,
                "the commit is INDEX_WRITE, last");
            int containerAt = ops.indexOf(container);
            int keyAt = ops.indexOf(key);
            int valueAt = ops.indexOf(value);
            int lengthAt = ops.indexOf(length);
            int normalizeAt = ops.indexOf(normalize);
            int boundaryAt = ops.indexOf(boundary);
            int commitAt = ops.indexOf(commit);
            check(containerAt < keyAt && keyAt < valueAt && valueAt < lengthAt
                    && lengthAt < normalizeAt && normalizeAt < boundaryAt
                    && boundaryAt < commitAt,
                "op order pins receiver < key < RHS < length < normalize < boundary < "
                    + "commit (got " + containerAt + ", " + keyAt + ", " + valueAt + ", "
                    + lengthAt + ", " + normalizeAt + ", " + boundaryAt + ", " + commitAt
                    + ")");
            check(keyAt < lengthAt,
                "the length read occurs after the key (normalize-time read)");
            check(valueAt < lengthAt,
                "the length read occurs after the RHS (spec item 3: RHS before write check)");
            for (SemanticOp child : List.of(container, key, value, length, normalize,
                    boundary, commit)) {
                check(chain.opId().equals(child.origin().parentOpId()),
                    "child " + child.kind() + " records the chain op as parentOpId");
            }
            check(normalize.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                "INDEX_NORMALIZE carries NO_DEAL_FAILURE (purity)");
        }

        // (b) The length-mutating key seed: the inner chain (its own
        // ARRAY_LENGTH included) completes before the outer lengthOp.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: int[] of [[1, 2]]) { xs[xs[xs.length] = 1] = 2 }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the length-mutating key seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
            check(assigns.size() == 2, "two ASSIGN chains (inner key, outer write)");
            SemanticOp inner = assigns.get(0);
            SemanticOp outer = assigns.get(1);
            KindPayload.AssignPayload innerPayload =
                (KindPayload.AssignPayload) inner.payload();
            KindPayload.AssignPayload outerPayload =
                (KindPayload.AssignPayload) outer.payload();
            check(innerPayload.targetKind() == AssignTargetKind.ARRAY_SLOT
                    && outerPayload.targetKind() == AssignTargetKind.ARRAY_SLOT,
                "both chains are ARRAY_SLOT");
            check(outerPayload.childOps().get(1).equals(inner.opId()),
                "the inner chain is the outer chain's keyOp");
            SemanticOp innerLength = opById(ops, innerPayload.childOps().get(3));
            SemanticOp outerLength = opById(ops, outerPayload.childOps().get(3));
            check(innerLength.kind() == SemanticOpKind.ARRAY_LENGTH
                    && outerLength.kind() == SemanticOpKind.ARRAY_LENGTH,
                "both chains carry their own ARRAY_LENGTH lengthOp");
            check(ops.indexOf(innerLength) < ops.indexOf(outerLength),
                "the key's append runs (inner length read included) before the outer "
                    + "normalize-time length read — a length-mutating key proves the "
                    + "normalize-time read");
            Optional<CompilerDiagnostic> protocol = AddressChainProtocol.validate(
                result.unit());
            check(protocol.isEmpty(), "the nested-chain unit passes the protocol: "
                + protocol);
        }

        // (c) TABLE_SLOT index write with a nested VARIABLE key chain.
        {
            CheckedSlice slice = checkSlice(
                "for (let t: table of [{x: 1}]) { for (let k: string of [\"k\"]) "
                    + "{ t[(k = \"x\")] = 2 } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the TABLE_SLOT nested-key seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
            check(assigns.size() == 2, "the VARIABLE key chain and the TABLE_SLOT write");
            SemanticOp keyChain = assigns.get(0);
            SemanticOp tableChain = assigns.get(1);
            KindPayload.AssignPayload tablePayload =
                (KindPayload.AssignPayload) tableChain.payload();
            check(tablePayload.targetKind() == AssignTargetKind.TABLE_SLOT
                    && tablePayload.childOps().size() == 5,
                "the write is TABLE_SLOT with 5 children");
            check(tablePayload.childOps().get(1).equals(keyChain.opId()),
                "the VARIABLE chain is the table chain's keyOp");
            check(tableChain.opId().equals(keyChain.origin().parentOpId()),
                "the nested VARIABLE chain records the enclosing chain as parentOpId");
            SemanticOp receiver = opById(ops, tablePayload.childOps().get(0));
            SemanticOp value = opById(ops, tablePayload.childOps().get(2));
            SemanticOp normalize = opById(ops, tablePayload.childOps().get(3));
            SemanticOp commit = opById(ops, tablePayload.childOps().get(4));
            check(receiver.kind() == SemanticOpKind.BINDING_LOAD
                    && value.kind() == SemanticOpKind.CONST
                    && normalize.kind() == SemanticOpKind.INDEX_NORMALIZE
                    && ((KindPayload.IndexNormalizePayload) normalize.payload()).mode()
                        == IndexMode.TABLE_WRITE
                    && commit.kind() == SemanticOpKind.INDEX_WRITE,
                "the TABLE_SLOT children are load/CONST/TABLE_WRITE normalize/INDEX_WRITE");
            check(ops.indexOf(receiver) < ops.indexOf(keyChain)
                    && ops.indexOf(keyChain) < ops.indexOf(value)
                    && ops.indexOf(value) < ops.indexOf(normalize)
                    && ops.indexOf(normalize) < ops.indexOf(commit),
                "the TABLE_SLOT op order pins receiver < key chain < RHS < normalize < "
                    + "commit");
            check(ops.stream().noneMatch(op -> op.kind() == SemanticOpKind.ARRAY_LENGTH),
                "no length read occurs for table targets");
            NormalizedSlot.TableSlot slot = NormalizedSlot.tableSlot(IndexMode.TABLE_WRITE,
                "x");
            check(slot.key().equals("x"),
                "the table slot preserves the string key identity exactly (no coercion)");
        }

        // (d) Multi-op receiver (member read of a literal) + nested key +
        // nested RHS — the full receiver → key → RHS shape in one chain.
        {
            CheckedSlice slice = checkSlice(
                "for (let t: table of [{m: {x: 1}}]) { for (let k: string of [\"k\"]) "
                    + "{ ({wrap: t}).wrap[(k = \"x\")] = (k = \"y\") } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the multi-op receiver seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            SemanticOp chain = ofKind(ops, SemanticOpKind.ASSIGN).stream()
                .filter(op -> ((KindPayload.AssignPayload) op.payload()).targetKind()
                    == AssignTargetKind.TABLE_SLOT)
                .findFirst().orElse(null);
            check(chain != null, "the outer TABLE_SLOT chain exists");
            if (chain == null) { return; }
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) chain.payload();
            SemanticOp receiver = opById(ops, payload.childOps().get(0));
            SemanticOp key = opById(ops, payload.childOps().get(1));
            SemanticOp value = opById(ops, payload.childOps().get(2));
            SemanticOp normalize = opById(ops, payload.childOps().get(3));
            SemanticOp commit = opById(ops, payload.childOps().get(4));
            check(receiver.kind() == SemanticOpKind.MEMBER_READ,
                "the receiver is the MEMBER_READ of the literal");
            check(ops.indexOf(receiver) < ops.indexOf(key)
                    && ops.indexOf(key) < ops.indexOf(value)
                    && ops.indexOf(value) < ops.indexOf(normalize)
                    && ops.indexOf(normalize) < ops.indexOf(commit),
                "multi-op receiver ops complete before the key chain before the RHS "
                    + "chain before normalize before commit");
            boolean literalBeforeReceiver = false;
            for (SemanticOp op : ops) {
                if (ops.indexOf(op) < ops.indexOf(receiver)
                        && op.kind() == SemanticOpKind.TABLE_NEW) {
                    literalBeforeReceiver = true;
                }
            }
            check(literalBeforeReceiver,
                "the receiver's producing steps include the literal's TABLE_NEW before "
                    + "the MEMBER_READ");
            check(chain.opId().equals(key.origin().parentOpId()),
                "the nested key chain is the outer chain's child");
            Optional<CompilerDiagnostic> protocol = AddressChainProtocol.validate(
                result.unit());
            check(protocol.isEmpty(), "the combined-seed unit passes the protocol: "
                + protocol);
        }

        // (e) VARIABLE with a nested assignment RHS: the inner chain (value
        // effects) completes before the outer VARIABLE_ASSIGNMENT boundary
        // and the store.
        {
            CheckedSlice slice = checkSlice("for (let e: int of [1]) { e = (e = 2)\ne }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the nested VARIABLE seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
            check(assigns.size() == 2, "two VARIABLE chains (inner RHS, outer write)");
            SemanticOp inner = assigns.get(0);
            SemanticOp outer = assigns.get(1);
            KindPayload.AssignPayload innerPayload =
                (KindPayload.AssignPayload) inner.payload();
            KindPayload.AssignPayload outerPayload =
                (KindPayload.AssignPayload) outer.payload();
            check(innerPayload.targetKind() == AssignTargetKind.VARIABLE
                    && outerPayload.targetKind() == AssignTargetKind.VARIABLE,
                "both chains are VARIABLE");
            check(outerPayload.childOps().get(0).equals(inner.opId()),
                "the inner chain is the outer chain's valueOp");
            SemanticOp outerBoundary = opById(ops, outerPayload.childOps().get(1));
            SemanticOp outerStore = opById(ops, outerPayload.childOps().get(2));
            check(outerBoundary.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) outerBoundary.payload()).kind()
                        == BoundaryKind.VARIABLE_ASSIGNMENT,
                "the outer boundary is VARIABLE_ASSIGNMENT");
            check(outerStore.kind() == SemanticOpKind.BINDING_STORE,
                "the outer commit is BINDING_STORE");
            check(ops.indexOf(inner) < ops.indexOf(outerBoundary)
                    && ops.indexOf(outerBoundary) < ops.indexOf(outerStore),
                "the value's effects (inner chain) complete before the VARIABLE "
                    + "boundary before the store — the boundary runs after the value's "
                    + "effects and before the store is observable");
            check(((KindPayload.BoundaryPayload) outerBoundary.payload()).input()
                    .equals(inner.result()),
                "the VARIABLE boundary input is the committed value (the valueOp result)");
        }

        // (f) The append idiom lowers through the standard ARRAY_SLOT chain
        // and the normalize computes append at index == length.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: int[] of [[1]]) { xs[xs.length] = 2 }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the append idiom lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            SemanticOp chain = ofKind(result.unit().ops(), SemanticOpKind.ASSIGN).get(0);
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) chain.payload();
            check(payload.targetKind() == AssignTargetKind.ARRAY_SLOT,
                "the append idiom lowers through the standard ARRAY_SLOT chain");
            SemanticOp keyOp = opById(result.unit().ops(), payload.childOps().get(1));
            check(keyOp.kind() == SemanticOpKind.ARRAY_LENGTH,
                "the append idiom's keyOp is the .length ARRAY_LENGTH read");
            NormalizedSlot.ArraySlot append = NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE,
                2, 2);
            check(append.append() && !append.present(),
                "index == length normalizes to append=true (the commit appends)");
            NormalizedSlot.ArraySlot inRange = NormalizedSlot.arraySlot(IndexMode.ARRAY_WRITE,
                0, 2);
            check(inRange.present() && !inRange.append(),
                "0 <= index < length normalizes to present, never append");
            NormalizedSlot.ArraySlot outOfRange = NormalizedSlot.arraySlot(
                IndexMode.ARRAY_WRITE, 5, 2);
            check(!outOfRange.present() && !outOfRange.append(),
                "an out-of-range index normalizes exactly (never fails — the normalize is "
                    + "pure; enforcement belongs to the boundary)");
            NormalizedSlot.ArraySlot negative = NormalizedSlot.arraySlot(
                IndexMode.ARRAY_WRITE, -1, 2);
            check(negative.index() == -1 && negative.present(),
                "a negative index normalizes exactly with index -1 (present = "
                    + "index < length computes; never E8002 in the normalize — bounds "
                    + "enforcement belongs to the boundary)");
        }

        // (g) ASSIGN publishes the committed value; DELETE publishes none;
        // the delete rows carry the closed boundary structure.
        {
            CheckedSlice slice = checkSlice(
                "for (let y: int of [0]) { for (let xs: int[] of [[1]]) { y = (xs[0] = 2) } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the publish seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> assigns = ofKind(ops, SemanticOpKind.ASSIGN);
            SemanticOp inner = assigns.get(0);
            SemanticOp outer = assigns.get(1);
            KindPayload.AssignPayload outerPayload =
                (KindPayload.AssignPayload) outer.payload();
            SemanticOp outerBoundary = opById(ops, outerPayload.childOps().get(1));
            check(((KindPayload.BoundaryPayload) outerBoundary.payload()).input()
                    .equals(inner.result())
                    && outer.result().equals(inner.result()),
                "ASSIGN publishes the committed value — the outer boundary input and the "
                    + "outer chain result are the inner chain's result (expression "
                    + "positions covered)");

            CheckedSlice deleteSlice = checkSlice(
                "for (let xs: int[] of [[1, 2]]) { delete xs[0] }");
            if (deleteSlice == null) { return; }
            SemanticLowerer.LoweringResult deleteResult = lowerDetected(deleteSlice);
            check(deleteResult != null && !deleteResult.hasErrors(),
                "the array-delete seed lowers: "
                    + (deleteResult == null ? "null" : deleteResult.diagnostics()));
            if (deleteResult == null || deleteResult.hasErrors()) { return; }
            List<SemanticOp> deleteOps = deleteResult.unit().ops();
            SemanticOp deleteChain = ofKind(deleteOps, SemanticOpKind.DELETE).get(0);
            check(deleteChain.result() == null
                    && deleteChain.resultType() == null,
                "DELETE publishes no result");
            KindPayload.DeletePayload deletePayload =
                (KindPayload.DeletePayload) deleteChain.payload();
            check(deletePayload.targetKind() == DeleteTargetKind.ARRAY_SLOT
                    && deletePayload.childOps().size() == 6,
                "the array delete chain is [containerOp, keyOp, lengthOp, normalizeOp, "
                    + "boundaryOp, commitOp]");
            SemanticOp deleteBoundary = opById(deleteOps, deletePayload.childOps().get(4));
            check(deleteBoundary.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) deleteBoundary.payload()).kind()
                        == BoundaryKind.ARRAY_ELEMENT_DELETE
                    && deleteBoundary.failurePolicy() == FailurePolicyId.ARRAY_DELETE_BOUNDS,
                "the array delete runs exactly one ARRAY_ELEMENT_DELETE bounds boundary "
                    + "with ARRAY_DELETE_BOUNDS");
            SemanticOp deleteCommit = opById(deleteOps, deletePayload.childOps().get(5));
            check(deleteCommit.kind() == SemanticOpKind.INDEX_DELETE,
                "the delete commit is INDEX_DELETE, last");
            check(deleteOps.indexOf(deleteBoundary) < deleteOps.indexOf(deleteCommit),
                "the bounds boundary precedes the commit — a failed bounds check commits "
                    + "no nil write");

            CheckedSlice tableDeleteSlice = checkSlice(
                "for (let t: table of [{x: 1}]) { delete t[\"x\"] }");
            if (tableDeleteSlice == null) { return; }
            SemanticLowerer.LoweringResult tableDeleteResult =
                lowerDetected(tableDeleteSlice);
            check(tableDeleteResult != null && !tableDeleteResult.hasErrors(),
                "the table-delete seed lowers: "
                    + (tableDeleteResult == null ? "null" : tableDeleteResult.diagnostics()));
            if (tableDeleteResult == null || tableDeleteResult.hasErrors()) { return; }
            List<SemanticOp> tableDeleteOps = tableDeleteResult.unit().ops();
            SemanticOp tableDelete = ofKind(tableDeleteOps, SemanticOpKind.DELETE).get(0);
            KindPayload.DeletePayload tablePayload =
                (KindPayload.DeletePayload) tableDelete.payload();
            check(tablePayload.targetKind() == DeleteTargetKind.TABLE_SLOT
                    && tablePayload.childOps().size() == 4,
                "the table index delete chain is [containerOp, keyOp, normalizeOp, "
                    + "commitOp] — no bounds boundary");
            check(tableDeleteOps.stream().noneMatch(op ->
                    op.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) op.payload()).kind()
                            == BoundaryKind.ARRAY_ELEMENT_DELETE),
                "table deletes run no ARRAY_ELEMENT_DELETE bounds boundary");
        }
    }

    // =========================================================================
    // 3. Chain failure projections through BoundaryExecutor
    // =========================================================================

    private static BoundaryValueView intView(long value) {
        return BoundaryValueView.ofInt(value);
    }

    private static BoundaryValueView numberView(double value) {
        return BoundaryValueView.ofNumber(value);
    }

    private static BoundaryValueView funcView(RuntimeDescriptor.Func signature) {
        return BoundaryValueView.ofFunction(signature);
    }

    private static void checkE8002(BoundaryOutcome outcome, String messageText, String what) {
        check(outcome instanceof BoundaryOutcome.Fail,
            what + " fails; got " + outcome);
        if (outcome instanceof BoundaryOutcome.Fail failure) {
            BoundaryFailure f = failure.failure();
            check(f.code() == DiagnosticCode.E8002,
                what + " code is E8002; got " + f.code());
            check(f.message().equals(messageText),
                what + " message is '" + messageText + "'; got '" + f.message() + "'");
        }
    }

    private static void checkE8001(BoundaryOutcome outcome, String expected, String actual,
                                   String what) {
        check(outcome instanceof BoundaryOutcome.Fail,
            what + " fails; got " + outcome);
        if (outcome instanceof BoundaryOutcome.Fail failure) {
            BoundaryFailure f = failure.failure();
            check(f.code() == DiagnosticCode.E8001,
                what + " code is E8001; got " + f.code());
            check(f.expected().equals(expected) && f.actual().equals(actual),
                what + " expected/actual are " + expected + "/" + actual + "; got "
                    + f.expected() + "/" + f.actual());
        }
    }

    static void testChainFailureProjections() {
        System.out.println("-- Chain boundary projections: E8002/E8001/E8010, purity --");

        RuntimeDescriptor intDescriptor = RuntimeDescriptor.Int.INSTANCE;

        // (a) ARRAY_WRITE_BOUNDS_THEN_ELEMENT — bounds first, then the
        // element descriptor; the ==length append slot passes.
        {
            BoundaryOutcome negative = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, intDescriptor,
                intView(5), BoundaryContext.writeBounds(-1, 2));
            checkE8002(negative, "array index out of bounds",
                "write index -1 (length 2)");
            BoundaryOutcome gap = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, intDescriptor,
                intView(5), BoundaryContext.writeBounds(3, 2));
            checkE8002(gap, "array index out of bounds",
                "write index 3 > length 2");
            BoundaryOutcome append = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, intDescriptor,
                intView(5), BoundaryContext.writeBounds(2, 2));
            check(append instanceof BoundaryOutcome.Pass,
                "write index == length is the permitted append slot (pass)");
            BoundaryOutcome inRange = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, intDescriptor,
                intView(5), BoundaryContext.writeBounds(0, 2));
            check(inRange instanceof BoundaryOutcome.Pass,
                "an in-range int value passes the element descriptor");
            BoundaryOutcome wrongElement = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, intDescriptor,
                numberView(2.5), BoundaryContext.writeBounds(0, 2));
            checkE8001(wrongElement, "int", "non-integer number",
                "an in-range number value fails the int element descriptor");
            check(wrongElement instanceof BoundaryOutcome.Fail failure
                    && failure.failure().code() == DiagnosticCode.E8001
                    && failure.failure().metadata().isEmpty(),
                "the element failure carries no cause metadata");
        }

        // (b) ARRAY_DELETE_BOUNDS — index <0 or >length raises E8002 'array
        // index out of bounds'; index == length is the permitted no-op.
        {
            BoundaryOutcome negative = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_DELETE_BOUNDS, intDescriptor,
                intView(-1), BoundaryContext.writeBounds(-1, 2));
            checkE8002(negative, "array index out of bounds",
                "delete index -1");
            BoundaryOutcome pastEnd = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_DELETE_BOUNDS, intDescriptor,
                intView(3), BoundaryContext.writeBounds(3, 2));
            checkE8002(pastEnd, "array index out of bounds",
                "delete index 3 > length 2");
            BoundaryOutcome appendSlot = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_DELETE_BOUNDS, intDescriptor,
                intView(2), BoundaryContext.writeBounds(2, 2));
            check(appendSlot instanceof BoundaryOutcome.Pass,
                "delete index == length is the permitted no-op commit (pass)");
            BoundaryOutcome inRange = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_DELETE_BOUNDS, intDescriptor,
                intView(0), BoundaryContext.writeBounds(0, 2));
            check(inRange instanceof BoundaryOutcome.Pass,
                "an in-range delete index passes the bounds check");
        }

        // (c) VARIABLE_ASSIGNMENT descriptor-kind rule: non-function target
        // → TYPE_DESCRIPTOR (E8001 on a wrong value); function target →
        // FUNCTION_SIGNATURE (E8010).
        {
            BoundaryOutcome wrongValue = BoundaryExecutor.check(
                FailurePolicyId.TYPE_DESCRIPTOR, intDescriptor,
                numberView(1.5), BoundaryContext.none());
            checkE8001(wrongValue, "int", "non-integer number",
                "the VARIABLE boundary rejects a wrong dynamic value (E8001) and the "
                    + "commit runs nothing");
            BoundaryOutcome rightValue = BoundaryExecutor.check(
                FailurePolicyId.TYPE_DESCRIPTOR, intDescriptor,
                intView(7), BoundaryContext.none());
            check(rightValue instanceof BoundaryOutcome.Pass,
                "the VARIABLE boundary passes a matching dynamic value");

            RuntimeDescriptor.Func target = new RuntimeDescriptor.Func(
                List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Int.INSTANCE,
                false);
            RuntimeDescriptor.Func wrongSignature = new RuntimeDescriptor.Func(
                List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
                RuntimeDescriptor.Int.INSTANCE, false);
            BoundaryOutcome signatureMismatch = BoundaryExecutor.check(
                FailurePolicyId.FUNCTION_SIGNATURE, target,
                funcView(wrongSignature), BoundaryContext.none());
            check(signatureMismatch instanceof BoundaryOutcome.Fail failure
                    && failure.failure().code() == DiagnosticCode.E8010,
                "a function-typed VARIABLE boundary uses FUNCTION_SIGNATURE — a wrong "
                    + "signature is E8010 (got " + signatureMismatch + ")");
            BoundaryOutcome signaturePass = BoundaryExecutor.check(
                FailurePolicyId.FUNCTION_SIGNATURE, target,
                funcView(target), BoundaryContext.none());
            check(signaturePass instanceof BoundaryOutcome.Pass,
                "an exact function signature passes the VARIABLE boundary");
        }

        // (d) The negative read projection: E8002 'negative array index'
        // first — the contextual read decision runs after it.
        {
            BoundaryOutcome negativeRead = BoundaryExecutor.check(
                FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, intDescriptor,
                BoundaryValueView.of(ActualKind.MISSING),
                BoundaryContext.arrayIndex(-1));
            checkE8002(negativeRead, "negative array index",
                "a negative index read");
        }

        // (e) The lowered chain boundaries carry the exact policy and a
        // RuntimeValidation realization — connecting the production seam to
        // the executor.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: int[] of [[1, 2]]) { xs[0] = 2\nfor (let e: int of xs) "
                    + "{ e = 1 } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the boundary-production seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            for (SemanticOp op : result.unit().ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY) {
                    KindPayload.BoundaryPayload payload =
                        (KindPayload.BoundaryPayload) op.payload();
                    check(payload.realization()
                            instanceof BoundaryRealization.RuntimeValidation,
                        "every produced boundary records a RuntimeValidation realization");
                }
            }
            long variableBoundaries = result.unit().ops().stream()
                .filter(op -> op.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) op.payload()).kind()
                        == BoundaryKind.VARIABLE_ASSIGNMENT)
                .count();
            check(variableBoundaries == 1,
                "exactly one VARIABLE_ASSIGNMENT boundary for the variable chain; got "
                    + variableBoundaries);
            long elementBoundaries = result.unit().ops().stream()
                .filter(op -> op.kind() == SemanticOpKind.BOUNDARY
                    && ((KindPayload.BoundaryPayload) op.payload()).kind()
                        == BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT)
                .count();
            check(elementBoundaries == 1,
                "exactly one ARRAY_ELEMENT_ASSIGNMENT boundary for the array write; got "
                    + elementBoundaries);
        }
    }

    // =========================================================================
    // 4. Single evaluation and the retained double-evaluation detector
    // =========================================================================

    static void testChainSingleEvaluationAndRetainedShapeDetection() {
        System.out.println("-- Single evaluation: duplicated children/ops fail E6005 --");

        CheckedSlice slice = checkSlice(
            "for (let xs: int[] of [[1, 2]]) { delete xs[0] }");
        if (slice == null) { return; }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors() && result.unit() != null,
            "the negative-control seed lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors() || result.unit() == null) { return; }
        LoweredModuleUnit unit = result.unit();
        check(AddressChainProtocol.validate(unit).isEmpty(),
            "the produced unit passes the protocol (every producing child exactly once)");

        SemanticOp deleteChain = ofKind(unit.ops(), SemanticOpKind.DELETE).get(0);
        KindPayload.DeletePayload original =
            (KindPayload.DeletePayload) deleteChain.payload();

        // (a) The retained double-evaluation shape: the same producing op
        // appears twice in the unit's op list — a duplicated evaluation
        // would execute its source expression twice (the detector's
        // unit-level form of the duplicated effects the conformance
        // harness sees).
        {
            OpId duplicatedId = original.childOps().get(1);
            SemanticOp duplicatedOp = opById(unit.ops(), duplicatedId);
            List<SemanticOp> doubled = new ArrayList<>(unit.ops());
            doubled.add(doubled.indexOf(duplicatedOp), duplicatedOp);
            Optional<CompilerDiagnostic> rejected =
                AddressChainProtocol.validate(withOps(unit, doubled));
            checkE6005(rejected, "SINGLE_EVALUATION",
                "a duplicated op in the unit's op list — the retained "
                    + "double-evaluation shape (the receiver/index re-emitted) — fails "
                    + "E6005 SINGLE_EVALUATION");
            check(rejected.isPresent()
                    && rejected.get().message().contains("more than once"),
                "the duplicated-op rejection names the re-evaluation reason");
        }

        // (b) A producing child listed twice in one chain.
        {
            List<OpId> duplicated = new ArrayList<>(original.childOps());
            duplicated.add(1, original.childOps().get(1));
            LoweredModuleUnit corrupted = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(deleteChain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        duplicated))
                    : op).toList());
            Optional<CompilerDiagnostic> rejected =
                AddressChainProtocol.validate(corrupted);
            checkE6005(rejected, "SINGLE_EVALUATION",
                "a chain listing one producing child twice fails E6005 SINGLE_EVALUATION");
        }

        // (c) A child referenced by two chains (two chains sharing one
        // producing op) — the re-evaluation shape.
        {
            List<OpId> stolen = new ArrayList<>(original.childOps());
            stolen.set(0, original.childOps().get(1));
            LoweredModuleUnit corrupted = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(deleteChain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        stolen))
                    : op).toList());
            Optional<CompilerDiagnostic> rejected =
                AddressChainProtocol.validate(corrupted);
            checkE6005(rejected, "SINGLE_EVALUATION",
                "a producing child referenced by two chains fails E6005 SINGLE_EVALUATION");
        }

        // (d) Missing lengthOp, commit not last, and boundary-after-commit
        // shape defects.
        {
            List<OpId> missingLength = new ArrayList<>(original.childOps());
            missingLength.remove(2);
            LoweredModuleUnit corrupted = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(deleteChain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        missingLength))
                    : op).toList());
            checkE6005(AddressChainProtocol.validate(corrupted), "ADDRESS_CHAIN_SHAPE",
                "an array delete chain without its lengthOp fails E6005 "
                    + "ADDRESS_CHAIN_SHAPE");

            List<OpId> commitFirst = new ArrayList<>(original.childOps());
            OpId commit = commitFirst.remove(commitFirst.size() - 1);
            commitFirst.add(0, commit);
            LoweredModuleUnit corruptedCommit = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(deleteChain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        commitFirst))
                    : op).toList());
            checkE6005(AddressChainProtocol.validate(corruptedCommit), "ADDRESS_CHAIN_SHAPE",
                "a chain with the commit not last fails E6005 ADDRESS_CHAIN_SHAPE");

            List<OpId> boundaryAfterCommit = new ArrayList<>(original.childOps());
            OpId boundary = boundaryAfterCommit.remove(4);
            boundaryAfterCommit.add(boundary);
            LoweredModuleUnit corruptedBoundary = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(deleteChain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        boundaryAfterCommit))
                    : op).toList());
            checkE6005(AddressChainProtocol.validate(corruptedBoundary),
                "ADDRESS_CHAIN_SHAPE",
                "a chain with the boundary after the commit fails E6005 "
                    + "ADDRESS_CHAIN_SHAPE");
        }

        // (e) A wrong boundary policy on the delete cell.
        {
            OpId boundaryId = original.childOps().get(4);
            SemanticOp boundaryOp = opById(unit.ops(), boundaryId);
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) boundaryOp.payload();
            LoweredModuleUnit corrupted = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(boundaryId)
                    ? rebuildOpWithPolicy(op, new KindPayload.BoundaryPayload(
                        BoundaryKind.ARRAY_ELEMENT_DELETE,
                        boundaryPayload.descriptor(), boundaryPayload.input(),
                        boundaryPayload.realization()),
                        FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT)
                    : op).toList());
            Optional<CompilerDiagnostic> rejected =
                AddressChainProtocol.validate(corrupted);
            checkE6005(rejected, "ADDRESS_CHAIN_SHAPE",
                "a delete boundary with the write policy fails E6005 "
                    + "ADDRESS_CHAIN_SHAPE (the closed cell pins ARRAY_DELETE_BOUNDS)");
        }
    }

    // =========================================================================
    // 5. The frontend gates — E3017 and E3018 fire before lowering
    // =========================================================================

    static void testFrontendGates() {
        System.out.println("-- Frontend gates: E3017 (.length), E3018 (string table keys) --");

        List<CompilerDiagnostic> lengthAssign = checkSliceExpectingErrors(
            "for (let xs: int[] of [[1]]) { xs.length = 2 }",
            "the .length assignment seed");
        check(lengthAssign.stream().anyMatch(d -> "E3017".equals(d.code())),
            ".length assignment is rejected with E3017 before lowering: " + lengthAssign);
        List<CompilerDiagnostic> lengthDelete = checkSliceExpectingErrors(
            "for (let xs: int[] of [[1]]) { delete xs.length }",
            "the .length delete seed");
        check(lengthDelete.stream().anyMatch(d -> "E3017".equals(d.code())),
            ".length delete is rejected with E3017 before lowering: " + lengthDelete);

        List<CompilerDiagnostic> intKeyWrite = checkSliceExpectingErrors(
            "for (let t: table of [{x: 1}]) { t[0] = 1 }",
            "the int table key write seed");
        check(intKeyWrite.stream().anyMatch(d -> "E3018".equals(d.code())
                && d.message().contains("Table index key must have static type string")),
            "a non-string table index write key is rejected with E3018 before lowering: "
                + intKeyWrite);
        check(intKeyWrite.stream().filter(d -> "E3018".equals(d.code()))
                .allMatch(d -> d.line() == 1 && d.column() == 36),
            "E3018 is reported at the index expression's span: " + intKeyWrite);

        List<CompilerDiagnostic> intKeyDelete = checkSliceExpectingErrors(
            "for (let t: table of [{x: 1}]) { delete t[0] }",
            "the int table key delete seed");
        check(intKeyDelete.stream().anyMatch(d -> "E3018".equals(d.code())),
            "a non-string table index delete key is rejected with E3018 before lowering: "
                + intKeyDelete);

        List<CompilerDiagnostic> numberKey = checkSliceExpectingErrors(
            "for (let t: table of [{x: 1}]) { for (let n: number of [0.5]) { t[n] = 1 } }",
            "the number table key seed");
        check(numberKey.stream().anyMatch(d -> "E3018".equals(d.code())),
            "a number table index key is rejected with E3018: " + numberKey);

        // The string-key forms lower (the gate admits exactly string).
        CheckedSlice stringKey = checkSlice(
            "for (let t: table of [{x: 1}]) { for (let k: string of [\"k\"]) { t[k] = 1 } }");
        if (stringKey != null) {
            SemanticLowerer.LoweringResult result = lowerDetected(stringKey);
            check(result != null && !result.hasErrors(),
                "a string-typed table index key lowers through the total TableSlot path: "
                    + (result == null ? "null" : result.diagnostics()));
        }
    }

    // =========================================================================
    // 5b. Bytes equality admission (ISSUE-0158 gate lift) — frontend,
    // before lowering
    // =========================================================================

    /**
     * ISSUE-0158 lifted the E3019 gate: equal bytes-containing pairs and
     * nullable-bytes-vs-null (both directions) are admitted as
     * {@code Type.Boolean} in {@code checkBinary} (spec-v1.2
     * reference-identity equality), and {@code DiagnosticCode.E3019} was
     * deleted. The admission path is driven from real v1.2 source —
     * {@code bytes(2)} is now a production intrinsic — with no synthetic
     * parameter retyping. Mixed pairs keep E3006, bytes relationals keep
     * E3007, and the E6005 COMPARISON_SELECTOR producer guard now sits
     * behind the no-row relational pairs (section 7).
     */
    private record CheckedSource(CheckResult result, ProgramNode program) {}

    private static CheckedSource checkSource(String source) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID,
            lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "fixture program parses cleanly: "
            + parse.diagnostics());
        StubModuleResolver resolver = new StubModuleResolver();
        NameResolver nr = new NameResolver(SOURCE_ID, resolver);
        SymbolTable symTable = nr.resolve(parse.program());
        List<CompilerDiagnostic> diags = new ArrayList<>(nr.diagnostics());
        CheckResult result;
        if (diags.isEmpty()) {
            result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
            diags.addAll(result.diagnostics());
        } else {
            result = new CheckResult(Map.of(), symTable, diags);
        }
        return new CheckedSource(result, parse.program());
    }

    private static void assertNoDiagnostics(CheckedSource checked, String context) {
        check(checked.result().diagnostics().isEmpty(),
            context + " has zero diagnostics: " + checked.result().diagnostics());
    }

    private static void assertDiagnostic(CheckedSource checked, String code,
            String context) {
        check(checked.result().diagnostics().stream()
                .anyMatch(d -> code.equals(d.code())),
            context + " carries " + code + ": " + checked.result().diagnostics());
    }

    private static BinaryExpr firstBinaryExpr(ProgramNode program) {
        for (StatementNode stmt : program.statements()) {
            if (stmt instanceof FunctionDeclaration fd) {
                for (StatementNode bodyStmt : fd.body().statements()) {
                    if (bodyStmt instanceof VariableDeclaration vd
                            && vd.initializer() instanceof BinaryExpr bin) {
                        return bin;
                    }
                }
            }
        }
        fail("no binary expression found in the fixture program");
        return null;
    }

    static void testBytesComparisonAdmission() {
        System.out.println("-- Bytes equality admission (ISSUE-0158 gate lift): "
            + "frontend, before lowering --");

        // bytes === bytes / bytes !== bytes: boolean-typed, zero
        // diagnostics, and E3019 no longer exists.
        CheckedSource out = checkSource(
            "function f(): null {\n"
            + "  let a: bytes = bytes(2);\n"
            + "  let b: bytes = a;\n"
            + "  let c: boolean = a === b;\n"
            + "  let d: boolean = a !== bytes(2);\n"
            + "  return null;\n"
            + "}"
        );
        assertNoDiagnostics(out, "bytes ===/!== bytes admitted");
        BinaryExpr bin = firstBinaryExpr(out.program());
        Type comparisonType = out.result().typeMap().get(bin);
        check(comparisonType == Type.Boolean.INSTANCE,
            "bytes === bytes is typed boolean, got " + comparisonType);

        // bytes[] === bytes[] (equal reference shapes containing bytes).
        out = checkSource(
            "function f(): null {\n"
            + "  let xs: bytes[] = [bytes(1)];\n"
            + "  let ys: bytes[] = xs;\n"
            + "  let c: boolean = xs === ys;\n"
            + "  return null;\n"
            + "}"
        );
        assertNoDiagnostics(out, "bytes[] === bytes[] admitted");

        // bytes|null === bytes|null (equal nullable bytes pairs).
        out = checkSource(
            "function f(): null {\n"
            + "  let a: bytes | null = bytes(1);\n"
            + "  let b: bytes | null = a;\n"
            + "  let c: boolean = a === b;\n"
            + "  return null;\n"
            + "}"
        );
        assertNoDiagnostics(out, "bytes|null === bytes|null admitted");

        // bytes|null === null / null === bytes|null (both directions).
        out = checkSource(
            "function f(): null {\n"
            + "  let a: bytes | null = bytes(1);\n"
            + "  let c: boolean = a === null;\n"
            + "  let e: boolean = null === a;\n"
            + "  let g: boolean = a !== null;\n"
            + "  return null;\n"
            + "}"
        );
        assertNoDiagnostics(out, "bytes|null vs null admitted in both directions");

        // A non-admitted mixed pair keeps E3006 — admission did not widen.
        out = checkSource(
            "function f(): null {\n"
            + "  let b: bytes = bytes(1);\n"
            + "  let c: boolean = b === 1;\n"
            + "  return null;\n"
            + "}"
        );
        assertDiagnostic(out, "E3006", "bytes === number keeps E3006");
        check(out.result().diagnostics().stream()
                .noneMatch(d -> "E3019".equals(d.code())),
            "no E3019 diagnostic exists anymore: " + out.result().diagnostics());

        // Bytes relationals keep E3007 (relationals stay int/number/string).
        out = checkSource(
            "function f(): null {\n"
            + "  let b: bytes = bytes(1);\n"
            + "  let c: boolean = b < b;\n"
            + "  return null;\n"
            + "}"
        );
        assertDiagnostic(out, "E3007", "bytes relational keeps E3007");
    }

    // =========================================================================
    // 6. The comparison matrix — executor rows + production lowering map
    // =========================================================================

    private static ComparisonOperandView.String scalarString(String text) {
        return new ComparisonOperandView.String(
            (UnicodeScalars.Valid) UnicodeScalars.validate(text));
    }

    private static void checkCompare(String what, boolean expected, boolean actual) {
        check(expected == actual, what + " must be " + expected + "; got " + actual);
    }

    static void testComparisonExecutorMatrix() {
        System.out.println("-- ComparisonExecutor: the closed B-D2 rows incl. NaN/-0.0/"
            + "supplementary/nullable/missing/identity --");

        // INT32 rows.
        checkCompare("INT32_EQ(1,1)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_EQ, new ComparisonOperandView.Int(1),
            new ComparisonOperandView.Int(1), null, null));
        checkCompare("INT32_NE(1,2)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_NE, new ComparisonOperandView.Int(1),
            new ComparisonOperandView.Int(2), null, null));
        checkCompare("INT32_LT(1,2)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_LT, new ComparisonOperandView.Int(1),
            new ComparisonOperandView.Int(2), null, null));
        checkCompare("INT32_LE(2,2)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_LE, new ComparisonOperandView.Int(2),
            new ComparisonOperandView.Int(2), null, null));
        checkCompare("INT32_GT(2,1)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_GT, new ComparisonOperandView.Int(2),
            new ComparisonOperandView.Int(1), null, null));
        checkCompare("INT32_GE(2,2)", true, ComparisonExecutor.compare(
            BinarySelector.INT32_GE, new ComparisonOperandView.Int(2),
            new ComparisonOperandView.Int(2), null, null));
        checkCompare("INT32_LT(-2147483648, 0) signed", true, ComparisonExecutor.compare(
            BinarySelector.INT32_LT, new ComparisonOperandView.Int(-2147483648),
            new ComparisonOperandView.Int(0), null, null));

        // NUMBER rows — IEEE: NaN === NaN false, NaN !== NaN true,
        // -0.0 == 0.0, orderings with NaN all false, -0.0 < 0.0 false,
        // -0.0 <= 0.0 true. The NaN/-0.0 rows also prove the executor is
        // not Double.compare-based (Double.compare says NaN == NaN and
        // -0.0 < 0.0).
        double nan = Double.NaN;
        checkCompare("NUMBER_EQ(NaN,NaN) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_EQ, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(nan), null, null));
        checkCompare("NUMBER_NE(NaN,NaN) is true", true, ComparisonExecutor.compare(
            BinarySelector.NUMBER_NE, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(nan), null, null));
        checkCompare("NUMBER_EQ(-0.0,0.0) is true", true, ComparisonExecutor.compare(
            BinarySelector.NUMBER_EQ, new ComparisonOperandView.Number(-0.0),
            new ComparisonOperandView.Number(0.0), null, null));
        checkCompare("NUMBER_LT(-0.0,0.0) is false (never Double.compare)", false,
            ComparisonExecutor.compare(
                BinarySelector.NUMBER_LT, new ComparisonOperandView.Number(-0.0),
                new ComparisonOperandView.Number(0.0), null, null));
        checkCompare("NUMBER_LE(-0.0,0.0) is true", true, ComparisonExecutor.compare(
            BinarySelector.NUMBER_LE, new ComparisonOperandView.Number(-0.0),
            new ComparisonOperandView.Number(0.0), null, null));
        checkCompare("NUMBER_GE(-0.0,0.0) is true", true, ComparisonExecutor.compare(
            BinarySelector.NUMBER_GE, new ComparisonOperandView.Number(-0.0),
            new ComparisonOperandView.Number(0.0), null, null));
        checkCompare("NUMBER_LT(NaN,1) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_LT, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(1.0), null, null));
        checkCompare("NUMBER_LE(NaN,1) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_LE, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(1.0), null, null));
        checkCompare("NUMBER_GT(NaN,1) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_GT, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(1.0), null, null));
        checkCompare("NUMBER_GE(NaN,1) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_GE, new ComparisonOperandView.Number(nan),
            new ComparisonOperandView.Number(1.0), null, null));

        // STRING rows — code point order with supplementary characters.
        // U+E000 (BMP, UTF-16 unit 0xE000) vs U+10000 (surrogate pair
        // 0xD800 0xDC00): scalar order says U+E000 < U+10000; UTF-16
        // code-unit order (String.compareTo) says 0xD800 < 0xE000 — the
        // reversed verdict proves the executor is not String.compareTo.
        String bmpAbovePlane1 = "\uE000";
        String supplementary = new String(Character.toChars(0x10000));
        checkCompare("STRING_LT(U+E000, U+10000) scalar order", true,
            ComparisonExecutor.compare(
                BinarySelector.STRING_LT, scalarString(bmpAbovePlane1),
                scalarString(supplementary), null, null));
        checkCompare("STRING_GT(U+10000, U+E000) scalar order", true,
            ComparisonExecutor.compare(
                BinarySelector.STRING_GT, scalarString(supplementary),
                scalarString(bmpAbovePlane1), null, null));
        checkCompare("STRING_EQ('ab','ab')", true, ComparisonExecutor.compare(
            BinarySelector.STRING_EQ, scalarString("ab"), scalarString("ab"), null, null));
        checkCompare("STRING_NE('ab','ac')", true, ComparisonExecutor.compare(
            BinarySelector.STRING_NE, scalarString("ab"), scalarString("ac"), null, null));
        checkCompare("STRING_LT('a','b')", true, ComparisonExecutor.compare(
            BinarySelector.STRING_LT, scalarString("a"), scalarString("b"), null, null));
        checkCompare("STRING_LE('a','a')", true, ComparisonExecutor.compare(
            BinarySelector.STRING_LE, scalarString("a"), scalarString("a"), null, null));
        checkCompare("STRING_GE('b','a')", true, ComparisonExecutor.compare(
            BinarySelector.STRING_GE, scalarString("b"), scalarString("a"), null, null));

        // BOOLEAN and NULL rows.
        checkCompare("BOOLEAN_EQ(true,true)", true, ComparisonExecutor.compare(
            BinarySelector.BOOLEAN_EQ, new ComparisonOperandView.Boolean(true),
            new ComparisonOperandView.Boolean(true), null, null));
        checkCompare("BOOLEAN_NE(true,false)", true, ComparisonExecutor.compare(
            BinarySelector.BOOLEAN_NE, new ComparisonOperandView.Boolean(true),
            new ComparisonOperandView.Boolean(false), null, null));
        checkCompare("NULL_EQ", true, ComparisonExecutor.compare(
            BinarySelector.NULL_EQ, ComparisonOperandView.Null.INSTANCE,
            ComparisonOperandView.Null.INSTANCE, null, null));
        checkCompare("NULL_NE(null,null) is false", false, ComparisonExecutor.compare(
            BinarySelector.NULL_NE, ComparisonOperandView.Null.INSTANCE,
            ComparisonOperandView.Null.INSTANCE, null, null));

        // NULLABLE rows — sides LEFT/RIGHT/BOTH.
        RuntimeDescriptor nullableInt = RuntimeDescriptor.Int.INSTANCE;
        ComparisonOperandView nullOperand = ComparisonOperandView.Null.INSTANCE;
        ComparisonOperandView one = new ComparisonOperandView.Int(1);
        checkCompare("NULLABLE_EQ(null,null) BOTH", true, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_EQ, nullOperand, nullOperand, nullableInt,
            NullableSide.BOTH));
        checkCompare("NULLABLE_EQ(null,1) BOTH is false", false, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_EQ, nullOperand, one, nullableInt, NullableSide.BOTH));
        checkCompare("NULLABLE_EQ(1,1) BOTH", true, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_EQ, one, one, nullableInt, NullableSide.BOTH));
        checkCompare("NULLABLE_NE(1,2) BOTH", true, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_NE, one, new ComparisonOperandView.Int(2), nullableInt,
            NullableSide.BOTH));
        checkCompare("NULLABLE_EQ(null,null) LEFT side", true, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_EQ, nullOperand, nullOperand, nullableInt,
            NullableSide.LEFT));
        checkCompare("NULLABLE_EQ(1,null) RIGHT side is false", false,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_EQ, one, nullOperand, nullableInt,
                NullableSide.RIGHT));

        // NULLABLE_NULL rows — the named side consults only its operand.
        checkCompare("NULLABLE_NULL_EQ(null, null) LEFT", true, ComparisonExecutor.compare(
            BinarySelector.NULLABLE_NULL_EQ, nullOperand, nullOperand, nullableInt,
            NullableSide.LEFT));
        checkCompare("NULLABLE_NULL_EQ(1, null) LEFT is false", false,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_NULL_EQ, one, nullOperand, nullableInt,
                NullableSide.LEFT));
        checkCompare("NULLABLE_NULL_EQ(null, 1) RIGHT is false", false,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_NULL_EQ, nullOperand, one, nullableInt,
                NullableSide.RIGHT));
        checkCompare("NULLABLE_NULL_NE(null, null) LEFT is false", false,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_NULL_NE, nullOperand, nullOperand, nullableInt,
                NullableSide.LEFT));
        checkCompare("NULLABLE_NULL_NE(1, null) LEFT is true", true,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_NULL_NE, one, nullOperand, nullableInt,
                NullableSide.LEFT));

        // REFERENCE rows — allocation/function identity by token equality;
        // a null operand follows the null rules.
        RuntimeDescriptor tableDescriptor = RuntimeDescriptor.Table.INSTANCE;
        Object token = new Object();
        Object other = new Object();
        checkCompare("REFERENCE_EQ(same token)", true, ComparisonExecutor.compare(
            BinarySelector.REFERENCE_EQ, new ComparisonOperandView.Ref(token),
            new ComparisonOperandView.Ref(token), tableDescriptor, null));
        checkCompare("REFERENCE_NE(distinct tokens of equal shape)", true,
            ComparisonExecutor.compare(
                BinarySelector.REFERENCE_NE, new ComparisonOperandView.Ref(token),
                new ComparisonOperandView.Ref(other), tableDescriptor, null));
        checkCompare("REFERENCE_EQ(null,null)", true, ComparisonExecutor.compare(
            BinarySelector.REFERENCE_EQ, nullOperand, nullOperand, tableDescriptor, null));
        checkCompare("REFERENCE_EQ(null,token) is false", false, ComparisonExecutor.compare(
            BinarySelector.REFERENCE_EQ, nullOperand, new ComparisonOperandView.Ref(token),
            tableDescriptor, null));
        // Identity-vs-equals negative: two distinct allocation tokens of
        // equal shape compare NE (a structural equals() would say equal) —
        // identity by token, never by content.
        Object allocationA = new Object();
        Object allocationB = new Object();
        checkCompare("REFERENCE_EQ(distinct equal-shape allocations) is false", false,
            ComparisonExecutor.compare(
                BinarySelector.REFERENCE_EQ, new ComparisonOperandView.Ref(allocationA),
                new ComparisonOperandView.Ref(allocationB), tableDescriptor, null));
        checkCompare("REFERENCE_NE(distinct equal-shape allocations) is true", true,
            ComparisonExecutor.compare(
                BinarySelector.REFERENCE_NE, new ComparisonOperandView.Ref(allocationA),
                new ComparisonOperandView.Ref(allocationB), tableDescriptor, null));

        // Missing≡null (the jvm-arr-cmp-past-end-parity rows): a past-end
        // read at a comparison operand compares as language null at both
        // operand positions — no E8001 anywhere.
        ComparisonOperandView missing = ComparisonOperandView.Missing.INSTANCE;
        checkCompare("missing === missing is true", true, ComparisonExecutor.compare(
            BinarySelector.INT32_EQ, missing, missing, null, null));
        checkCompare("missing === 5 is false", false, ComparisonExecutor.compare(
            BinarySelector.INT32_EQ, missing, new ComparisonOperandView.Int(5), null, null));
        checkCompare("missing !== 5 is true", true, ComparisonExecutor.compare(
            BinarySelector.INT32_NE, missing, new ComparisonOperandView.Int(5), null, null));
        checkCompare("missing === null is true", true, ComparisonExecutor.compare(
            BinarySelector.INT32_EQ, missing, nullOperand, null, null));
        checkCompare("NUMBER_LT(missing, 1) is false", false, ComparisonExecutor.compare(
            BinarySelector.NUMBER_LT, missing, new ComparisonOperandView.Number(1.0),
            null, null));
        checkCompare("NULLABLE_EQ(missing, null) BOTH is true", true,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_EQ, missing, nullOperand, nullableInt,
                NullableSide.BOTH));
        checkCompare("NULLABLE_NULL_EQ(missing, null) LEFT is true", true,
            ComparisonExecutor.compare(
                BinarySelector.NULLABLE_NULL_EQ, missing, nullOperand, nullableInt,
                NullableSide.LEFT));
        checkCompare("STRING_EQ(missing, 'v') is false", false, ComparisonExecutor.compare(
            BinarySelector.STRING_EQ, missing, scalarString("v"), null, null));
    }

    static void testComparisonProductionMatrix() {
        System.out.println("-- Comparison lowering map + operand order + short circuit "
            + "(binding-core window) --");

        // Nested comparisons as operands: STRING_EQ/NE then BOOLEAN_EQ —
        // the operands complete left-to-right before each BINARY.
        {
            CheckedSlice slice = checkSlice(
                "let s: string = \"ab\"\nlet b: boolean = (s === s) === (s !== s)");
            if (slice == null) { return; }
            SemanticLowerer.BindingCoreResult result = lowerBindingCoreDetected(slice);
            check(result != null && result.lowering() != null
                    && !result.lowering().hasErrors(),
                "the string comparison seed lowers: "
                    + (result == null || result.lowering() == null ? "null"
                        : result.lowering().diagnostics()));
            if (result == null || result.lowering() == null
                    || result.lowering().hasErrors()) { return; }
            List<SemanticOp> ops = result.lowering().unit().ops();
            List<SemanticOp> binaries = ofKind(ops, SemanticOpKind.BINARY);
            check(binaries.size() == 3, "three BINARY ops (STRING_EQ, STRING_NE, BOOLEAN_EQ)");
            KindPayload.BinaryPayload first =
                (KindPayload.BinaryPayload) binaries.get(0).payload();
            KindPayload.BinaryPayload second =
                (KindPayload.BinaryPayload) binaries.get(1).payload();
            KindPayload.BinaryPayload third =
                (KindPayload.BinaryPayload) binaries.get(2).payload();
            check(first.selector() == BinarySelector.STRING_EQ
                    && first.innerDescriptor() == null && first.side() == null,
                "string === string lowers to STRING_EQ with no inner/side");
            check(second.selector() == BinarySelector.STRING_NE,
                "string !== string lowers to STRING_NE");
            check(third.selector() == BinarySelector.BOOLEAN_EQ,
                "boolean === boolean lowers to BOOLEAN_EQ");
            check(ops.indexOf(binaries.get(0)) < ops.indexOf(binaries.get(1))
                    && ops.indexOf(binaries.get(1)) < ops.indexOf(binaries.get(2)),
                "operands complete left-to-right: the first comparison's producing ops "
                    + "precede the second's, then the outer comparison");
            for (SemanticOp binary : binaries) {
                check(binary.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                    "every comparison BINARY carries NO_DEAL_FAILURE");
                check(binary.operands().size() == 2,
                    "the BINARY carries its two completed operands");
            }
            boolean boundaryUnderBinary = ops.stream().anyMatch(op ->
                op.kind() == SemanticOpKind.BOUNDARY
                    && op.origin().parentOpId() != null
                    && binaries.stream().anyMatch(b -> b.opId().equals(
                        op.origin().parentOpId())));
            check(!boundaryUnderBinary,
                "no BOUNDARY child appears under any comparison BINARY (B-D5)");
        }

        // Number relationals + nested operands.
        {
            CheckedSlice slice = checkSlice(
                "let n: number = 0.5\nlet b: boolean = (n < 1.0) === (n > 2.0)");
            if (slice == null) { return; }
            SemanticLowerer.BindingCoreResult result = lowerBindingCoreDetected(slice);
            check(result != null && result.lowering() != null
                    && !result.lowering().hasErrors(),
                "the number comparison seed lowers: "
                    + (result == null || result.lowering() == null ? "null"
                        : result.lowering().diagnostics()));
            if (result == null || result.lowering() == null
                    || result.lowering().hasErrors()) { return; }
            List<SemanticOp> binaries = ofKind(result.lowering().unit().ops(),
                SemanticOpKind.BINARY);
            check(binaries.size() == 3
                    && ((KindPayload.BinaryPayload) binaries.get(0).payload()).selector()
                        == BinarySelector.NUMBER_LT
                    && ((KindPayload.BinaryPayload) binaries.get(1).payload()).selector()
                        == BinarySelector.NUMBER_GT,
                "number relationals lower to NUMBER_LT/NUMBER_GT with the outer "
                    + "BOOLEAN_EQ");
        }

        // Reference equality + nullable-vs-null through the producer.
        {
            CheckedSlice slice = checkSlice(
                "let t = {a: 1}\nlet xs: int[] = [1]\nlet b1: boolean = (t === t)\n"
                    + "let b2: boolean = (xs === xs)\n"
                    + "let n: int | null = null\n"
                    + "let b3: boolean = (n === null)\n"
                    + "let b4: boolean = (null === n)");
            if (slice == null) { return; }
            SemanticLowerer.BindingCoreResult result = lowerBindingCoreDetected(slice);
            check(result != null && result.lowering() != null
                    && !result.lowering().hasErrors(),
                "the reference/nullable seed lowers: "
                    + (result == null || result.lowering() == null ? "null"
                        : result.lowering().diagnostics()));
            if (result == null || result.lowering() == null
                    || result.lowering().hasErrors()) { return; }
            List<SemanticOp> binaries = ofKind(result.lowering().unit().ops(),
                SemanticOpKind.BINARY);
            check(binaries.size() == 4, "four comparison BINARY ops; got " + binaries.size());
            KindPayload.BinaryPayload ref1 =
                (KindPayload.BinaryPayload) binaries.get(0).payload();
            check(ref1.selector() == BinarySelector.REFERENCE_EQ
                    && ref1.innerDescriptor().equals(RuntimeDescriptor.Table.INSTANCE),
                "table === table lowers to REFERENCE_EQ with the table descriptor; got "
                    + ref1.selector() + "/" + ref1.innerDescriptor());
            KindPayload.BinaryPayload ref2 =
                (KindPayload.BinaryPayload) binaries.get(1).payload();
            check(ref2.selector() == BinarySelector.REFERENCE_EQ
                    && ref2.innerDescriptor() instanceof RuntimeDescriptor.Array,
                "array === array lowers to REFERENCE_EQ with the array descriptor");
            KindPayload.BinaryPayload nullLeft =
                (KindPayload.BinaryPayload) binaries.get(2).payload();
            check(nullLeft.selector() == BinarySelector.NULLABLE_NULL_EQ
                    && nullLeft.side() == NullableSide.LEFT
                    && nullLeft.innerDescriptor() != null
                    && nullLeft.innerDescriptor().equals(RuntimeDescriptor.Int.INSTANCE),
                "nullable === null lowers to NULLABLE_NULL_EQ side LEFT with the inner "
                    + "int descriptor; got "
                    + nullLeft.selector() + "/" + nullLeft.side() + "/"
                    + nullLeft.innerDescriptor());
            KindPayload.BinaryPayload nullRight =
                (KindPayload.BinaryPayload) binaries.get(3).payload();
            check(nullRight.selector() == BinarySelector.NULLABLE_NULL_EQ
                    && nullRight.side() == NullableSide.RIGHT,
                "null === nullable lowers to NULLABLE_NULL_EQ side RIGHT; got "
                    + nullRight.side());
        }

        // Short circuit: BRANCH(LOGICAL_AND/OR) with the right operand's
        // ops in selectedBlock — never BINARY.
        {
            CheckedSlice slice = checkSlice(
                "let x: int = 1\nlet a: boolean = (x === 1) && (x === 2)\n"
                    + "let b: boolean = (x === 1) || (x === 2)");
            if (slice == null) { return; }
            SemanticLowerer.BindingCoreResult result = lowerBindingCoreDetected(slice);
            check(result != null && result.lowering() != null
                    && !result.lowering().hasErrors(),
                "the short-circuit seed lowers: "
                    + (result == null || result.lowering() == null ? "null"
                        : result.lowering().diagnostics()));
            if (result == null || result.lowering() == null
                    || result.lowering().hasErrors()) { return; }
            List<SemanticOp> ops = result.lowering().unit().ops();
            List<SemanticOp> branches = ofKind(ops, SemanticOpKind.BRANCH);
            check(branches.size() == 2, "two BRANCH ops (AND, OR); got " + branches.size());
            List<SemanticOp> binaries = ofKind(ops, SemanticOpKind.BINARY);
            check(binaries.size() == 4,
                "the four comparisons lower to four BINARY ops — &&/|| themselves never "
                    + "become BINARY");
            KindPayload.BranchPayload and =
                (KindPayload.BranchPayload) branches.get(0).payload();
            KindPayload.BranchPayload or =
                (KindPayload.BranchPayload) branches.get(1).payload();
            check(and.selector() == ControlSelector.LOGICAL_AND
                    && or.selector() == ControlSelector.LOGICAL_OR,
                "&&/|| lower to BRANCH(LOGICAL_AND/LOGICAL_OR), never BINARY");
            List<SemanticOp> rightOps = new ArrayList<>();
            for (OpId id : result.lowering().table().blockOps()
                    .get(and.selectedBlock())) {
                rightOps.add(opById(ops, id));
            }
            check(rightOps.size() == 3,
                "the AND's selectedBlock carries exactly the right operand's producing "
                    + "ops — the load of x, the CONST 2, and the BINARY(INT32_EQ) that "
                    + "consumes them and publishes the selected boolean (C-D3: the right "
                    + "operand's producing ops live in selectedBlock and execute only "
                    + "when the left value does not decide the result); got "
                    + rightOps.size() + " kinds="
                    + rightOps.stream().map(o -> o.kind().toString()).toList());
            check(rightOps.get(0).kind() == SemanticOpKind.BINDING_LOAD
                    && rightOps.get(1).kind() == SemanticOpKind.CONST
                    && rightOps.get(2).kind() == SemanticOpKind.BINARY,
                "the selectedBlock ops are load, CONST, then the consuming BINARY in "
                    + "source order; got "
                    + rightOps.stream().map(o -> o.kind().toString()).toList());
            KindPayload.BinaryPayload rightCmp =
                (KindPayload.BinaryPayload) rightOps.get(2).payload();
            check(rightCmp.selector() == BinarySelector.INT32_EQ
                    && rightOps.get(2).operands().size() == 2
                    && rightOps.get(2).operands().get(0).equals(rightOps.get(0).result())
                    && rightOps.get(2).operands().get(1).equals(rightOps.get(1).result()),
                "the right comparison's BINARY consumes exactly the block's load and "
                    + "CONST (never the left side's values)");
            check(branches.get(0).result().equals(rightOps.get(2).result()),
                "the BRANCH publishes the right comparison's boolean result identity");
            check(branches.get(0).opId().equals(rightOps.get(0).origin().parentOpId())
                    && branches.get(0).opId().equals(rightOps.get(1).origin().parentOpId()),
                "the right operand's producing loads/consts record the BRANCH as "
                    + "parentOpId (block ops nest under their structure op)");
            check(!and.selectedBlock().equals(
                    result.lowering().table().opBlocks().get(binaries.get(0).opId())),
                "the left operand's BINARY is the completed condition, not a member of "
                    + "the skipped block");
            check(ops.indexOf(branches.get(0)) < ops.indexOf(rightOps.get(2))
                    && ops.indexOf(binaries.get(0)) < ops.indexOf(branches.get(0)),
                "the unit list order is left operand's BINARY, the BRANCH, then the "
                    + "right operand's BINARY (the BRANCH precedes its child block ops)");
            check(ops.indexOf(rightOps.get(rightOps.size() - 1))
                    > ops.indexOf(binaries.get(0)),
                "the right side's producing ops follow the left operand's BINARY in the "
                    + "unit list (left-to-right, the skipped block never runs when the "
                    + "left side decides)");
        }
    }

    // =========================================================================
    // 7. The E6005 COMPARISON_SELECTOR producer-defect guard (no-row pairs)
    // =========================================================================

    static void testComparisonSelectorGuard() {
        System.out.println("-- COMPARISON_SELECTOR: the E6005 producer-defect guard --");

        // ISSUE-0158 lifted the E3019 gate and added the BYTES_EQ/NE row:
        // bytes === bytes is a closed row now — it lowers to BYTES_EQ and
        // never reaches the defect carrier.
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
        ValueId left = allocator.nextValueId(MODULE, 0, 0);
        ValueId right = allocator.nextValueId(MODULE, 1, 0);
        AnchorId anchor = allocator.nextAnchorId(MODULE, 2, 0);
        SourceOrigin origin = new SourceOrigin(SOURCE_ID,
            SourceSpan.synthetic(SOURCE_ID), SourceOriginKind.USER, anchor, null);
        boolean bytesEqDefective = false;
        SemanticOp bytesEqOp = null;
        try {
            bytesEqOp = ComparisonSelectorLowering.produce(MODULE, BinaryOp.EQ,
                Type.Bytes.INSTANCE, Type.Bytes.INSTANCE, left, right, origin,
                allocator, 3, 0);
        } catch (ComparisonSelectorLowering.Defect defect) {
            bytesEqDefective = true;
        }
        check(!bytesEqDefective && bytesEqOp != null
                && bytesEqOp.payload() instanceof KindPayload.BinaryPayload bp
                && bp.selector() == BinarySelector.BYTES_EQ,
            "bytes === bytes lowers to the closed BYTES_EQ row (ISSUE-0158), "
                + "never a COMPARISON_SELECTOR defect");

        // A bytes relational pair has no row (relationals stay
        // int/number/string only — E3007 in the checker) — the producer
        // guard is the defensive layer behind the gate.
        boolean defective = false;
        try {
            ComparisonSelectorLowering.produce(MODULE, BinaryOp.LT, Type.Bytes.INSTANCE,
                Type.Bytes.INSTANCE, left, right, origin, allocator, 3, 0);
        } catch (ComparisonSelectorLowering.Defect defect) {
            defective = true;
            CompilerDiagnostic diagnostic =
                ComparisonSelectorLowering.e6005(MODULE, defect);
            check("E6005".equals(diagnostic.code())
                    && diagnostic.diagnosticCode() == DiagnosticCode.E6005,
                "the bytes relational raises the E6005 carrier");
            check(diagnostic.message().contains("COMPARISON_SELECTOR"),
                "the E6005 message names COMPARISON_SELECTOR: " + diagnostic.message());
            check(diagnostic.message().contains("capability EVALUATION_ORDER"),
                "the E6005 message names capability EVALUATION_ORDER");
        }
        check(defective, "a no-row pair (bytes < bytes) is a producer defect "
            + "COMPARISON_SELECTOR — unreachable for user programs because the "
            + "E3007 checker gate rejects bytes relationals in phase 3 before "
            + "routing and lowering");

        // Mixed and non-orderable relational pairs are no-row pairs too.
        for (Type[] pair : new Type[][] {
            {Type.Bytes.INSTANCE, Type.Int.INSTANCE},
            {Type.Boolean.INSTANCE, Type.Boolean.INSTANCE}}) {
            BinaryOp op = pair[0] instanceof Type.Boolean ? BinaryOp.LT : BinaryOp.EQ;
            boolean raised = false;
            try {
                ComparisonSelectorLowering.produce(MODULE, op, pair[0], pair[1], left, right,
                    origin, allocator, 4, 0);
            } catch (ComparisonSelectorLowering.Defect defect) {
                raised = true;
                check(ComparisonSelectorLowering.e6005(MODULE, defect).message()
                    .contains("COMPARISON_SELECTOR"),
                    "the no-row pair raises E6005 COMPARISON_SELECTOR");
            }
            check(raised, "the no-row pair (" + pair[0] + " " + op + " " + pair[1]
                + ") raises the defect");
        }

        // The executor rejects an arithmetic selector (the guard's runtime
        // counterpart).
        boolean executorDefective = false;
        try {
            ComparisonExecutor.compare(BinarySelector.INT32_ADD,
                new ComparisonOperandView.Int(1), new ComparisonOperandView.Int(2), null,
                null);
        } catch (ComparisonExecutor.Defect defect) {
            executorDefective = true;
        }
        check(executorDefective,
            "an arithmetic selector reaching the comparison executor fails closed as a "
                + "producer defect");
    }

    // =========================================================================
    // 8. The control matrix through the production seam
    // =========================================================================

    static void testControlMatrix() {
        System.out.println("-- Control matrix: short circuit, loops, FOR_EACH, TRY_CATCH, "
            + "transfers, DISCARD --");

        // (a) Short circuit with a side-effecting (chain) condition: the
        // right side lives in selectedBlock behind the guard.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: boolean[] of [[true]]) { while ((xs[0] = false) || "
                    + "(xs[0] = true)) { break } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the chain-condition short-circuit seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> branches = ofKind(ops, SemanticOpKind.BRANCH);
            check(branches.size() == 1,
                "the || condition lowers to exactly one BRANCH; got " + branches.size());
            KindPayload.BranchPayload payload =
                (KindPayload.BranchPayload) branches.get(0).payload();
            check(payload.selector() == ControlSelector.LOGICAL_OR,
                "the BRANCH selector is LOGICAL_OR");
            SemanticOp leftChain = ofKind(ops, SemanticOpKind.ASSIGN).get(0);
            check(payload.condition().equals(leftChain.result()),
                "the condition is the left chain's committed value");
            List<SemanticOp> rightOps = new ArrayList<>();
            for (OpId id : result.table().blockOps().get(payload.selectedBlock())) {
                rightOps.add(opById(ops, id));
            }
            check(rightOps.size() == 8,
                "the selectedBlock carries the right chain's eight producing ops; got "
                    + rightOps.size());
            SemanticOp rightChain = rightOps.stream()
                .filter(op -> op.kind() == SemanticOpKind.ASSIGN)
                .findFirst().orElse(null);
            check(rightChain != null
                    && branches.get(0).opId().equals(rightChain.origin().parentOpId()),
                "the right chain op records the BRANCH as parentOpId");
            check(rightOps.stream().allMatch(op ->
                    op.kind() == SemanticOpKind.ASSIGN
                        || rightChain.opId().equals(op.origin().parentOpId())),
                "the right chain's children record the chain op as parentOpId — the "
                    + "short-circuited block never executes when the left value decides "
                    + "(false && e / true || e skip)");
            SemanticOp breakOp = ofKind(ops, SemanticOpKind.BREAK).get(0);
            check(ops.indexOf(breakOp) > ops.indexOf(rightOps.get(rightOps.size() - 1)),
                "the loop body follows the whole condition structure in the unit list");
        }

        // (b) WHILE with a per-iteration condition block: the condition's
        // producing ops are members of initBlock (re-evaluated per
        // iteration, never hoisted) and the body never runs speculatively.
        {
            CheckedSlice slice = checkSlice("while (({b: true}).b = false) {}");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the while seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            SemanticOp loop = ofKind(ops, SemanticOpKind.LOOP).get(0);
            KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
            check(payload.selector() == ControlSelector.WHILE,
                "the LOOP selector is WHILE");
            check(payload.updateBlock() == null,
                "WHILE carries no updateBlock");
            List<SemanticOp> conditionOps = new ArrayList<>();
            for (OpId id : result.table().blockOps().get(payload.initBlock())) {
                conditionOps.add(opById(ops, id));
            }
            check(conditionOps.size() == 5,
                "the per-iteration condition block (initBlock) carries the condition's "
                    + "five producing ops; got " + conditionOps.size());
            check(conditionOps.stream().anyMatch(op -> op.kind() == SemanticOpKind.ASSIGN),
                "the condition chain is an initBlock member — conditions re-evaluate per "
                    + "iteration, never hoisted");
            check(result.table().blockOps().get(payload.bodyBlock()).isEmpty(),
                "the body block is empty and never runs speculatively");
        }

        // (c) FOR: init once, test-first, update-then-re-test — with
        // break skipping the update and continue landing at the update.
        {
            CheckedSlice slice = checkSlice(
                "for (({i: 0}).i = 0; ({c: true}).c; ({u: 0}).u = 0) "
                    + "{ break }\n"
                    + "for (({i: 0}).i = 0; ({c: true}).c; ({u: 0}).u = 0) "
                    + "{ continue }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the for seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> loops = ofKind(ops, SemanticOpKind.LOOP);
            check(loops.size() == 2, "two LOOP(FOR) ops; got " + loops.size());
            SemanticOp breakLoop = loops.get(0);
            KindPayload.LoopPayload breakPayload =
                (KindPayload.LoopPayload) breakLoop.payload();
            List<OpId> initOps = result.table().blockOps().get(breakPayload.initBlock());
            List<OpId> updateOps = result.table().blockOps().get(breakPayload.updateBlock());
            check(initOps.size() == 9 && updateOps.size() == 9,
                "initBlock carries the init chain + first condition production; "
                    + "updateBlock carries the update chain + the re-test production");
            SemanticOp firstCondition = null;
            SemanticOp reTest = null;
            for (int i = initOps.size() - 4; i < initOps.size(); i++) {
                SemanticOp candidate = opById(ops, initOps.get(i));
                if (candidate.kind() == SemanticOpKind.MEMBER_READ) {
                    firstCondition = candidate;
                }
            }
            for (int i = updateOps.size() - 4; i < updateOps.size(); i++) {
                SemanticOp candidate = opById(ops, updateOps.get(i));
                if (candidate.kind() == SemanticOpKind.MEMBER_READ) {
                    reTest = candidate;
                }
            }
            check(firstCondition != null && reTest != null
                    && breakPayload.condition().equals(firstCondition.result())
                    && firstCondition.result().equals(reTest.result()),
                "the condition is one ValueId produced in initBlock and re-produced by "
                    + "the updateBlock production (update-then-re-test)");
            SemanticOp breakOp = ofKind(ops, SemanticOpKind.BREAK).get(0);
            check(breakLoop.opId().equals(
                    ((KindPayload.BreakPayload) breakOp.payload()).loopId()),
                "the BREAK targets its enclosing FOR");
            check(!updateOps.contains(breakOp.opId()),
                "break exits without running the update (the update ops live in "
                    + "updateBlock, never in the body)");
            SemanticOp continueLoop = loops.get(1);
            KindPayload.LoopPayload continuePayload =
                (KindPayload.LoopPayload) continueLoop.payload();
            SemanticOp continueOp = ofKind(ops, SemanticOpKind.CONTINUE).get(0);
            check(continueLoop.opId().equals(
                    ((KindPayload.ContinuePayload) continueOp.payload()).loopId()),
                "the CONTINUE targets its enclosing FOR");
            List<OpId> continueUpdateOps = result.table().blockOps()
                .get(continuePayload.updateBlock());
            boolean continueBeforeUpdate = true;
            for (OpId id : continueUpdateOps) {
                if (ops.indexOf(opById(ops, id)) < ops.indexOf(continueOp)) {
                    continueBeforeUpdate = false;
                }
            }
            check(continueBeforeUpdate,
                "continue lands before the update: every updateBlock op follows the "
                    + "CONTINUE in the unit list (the transfer proceeds to the "
                    + "updateBlock, then re-tests)");
        }

        // (d) Test-less FOR: exactly one CONST true in initBlock; the
        // updateBlock carries update ops only.
        {
            CheckedSlice slice = checkSlice("for (;;) { break; }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the test-less for lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            SemanticOp loop = ofKind(ops, SemanticOpKind.LOOP).get(0);
            KindPayload.LoopPayload payload = (KindPayload.LoopPayload) loop.payload();
            List<OpId> initOps = result.table().blockOps().get(payload.initBlock());
            check(initOps.size() == 1,
                "initBlock carries exactly one op — the CONST true condition production");
            SemanticOp constTrue = opById(ops, initOps.get(0));
            check(constTrue.kind() == SemanticOpKind.CONST
                    && constTrue.payload() instanceof KindPayload.ConstPayload constPayload
                    && constPayload.value().equals(new ScalarValue.Boolean(true)),
                "the single initBlock op is CONST true");
            check(payload.condition().equals(constTrue.result())
                    && constTrue.origin().kind() == SourceOriginKind.SYNTHETIC,
                "the payload condition is the CONST's result, produced once");
            check(result.table().blockOps().get(payload.updateBlock()).isEmpty(),
                "the test-less row's updateBlock carries only the update ops — zero here "
                    + "(no condition-producing op appears in updateBlock)");
        }

        // (e) FOR_EACH(ARRAY_VALUES): the iterable completes once as a
        // prior step, the op owns the TYPE_DESCRIPTOR terminal check, and
        // the per-iteration binding is fresh (binding + generation pinned).
        {
            CheckedSlice slice = checkSlice(
                "for (let e: int of [1, 2]) { e = (e + 1)\ne }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the FOR_EACH(ARRAY_VALUES) seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            List<SemanticOp> forEach = ofKind(ops, SemanticOpKind.FOR_EACH);
            check(forEach.size() == 1, "exactly one FOR_EACH op");
            KindPayload.ForEachPayload payload =
                (KindPayload.ForEachPayload) forEach.get(0).payload();
            check(payload.mode() == IterationMode.ARRAY_VALUES,
                "the mode is ARRAY_VALUES — the visitation runs slot index 0 through "
                    + "initialLength - 1 in increasing order (the 0-based shared slot "
                    + "space)");
            check(forEach.get(0).failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                "the FOR_EACH owns the TYPE_DESCRIPTOR element check (a missing element "
                    + "fails E8001 at the FOR_EACH origin before the body)");
            SemanticOp iterable = null;
            for (SemanticOp op : ops) {
                if (ops.indexOf(op) < ops.indexOf(forEach.get(0))
                        && op.kind() == SemanticOpKind.ARRAY_NEW) {
                    iterable = op;
                }
            }
            check(iterable != null
                    && payload.iterable().equals(iterable.result()),
                "the iterable's producing step (the ARRAY_NEW) completes exactly once "
                    + "before START as the payload's iterable operand — materialized into "
                    + "a local before the loop");
            check(payload.binding() != null
                    && payload.generation() == SemanticLowerer.INITIAL_LOOP_GENERATION,
                "the payload pins the fresh per-iteration binding with the initial "
                    + "generation");
            long stores = ops.stream()
                .filter(op -> op.kind() == SemanticOpKind.BINDING_STORE).count();
            check(stores == 1,
                "the loop-binding assignment commits through exactly one BINDING_STORE");
        }

        // (f) TRY_CATCH/THROW with a BREAK transfer across the try boundary
        // (the retained flag precedent) and the catch re-throw.
        {
            CheckedSlice slice = checkSlice(
                "for (;;) { try { break } catch (e) { throw e } }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the try/break/throw seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops();
            SemanticOp loop = ofKind(ops, SemanticOpKind.LOOP).get(0);
            SemanticOp tryCatch = ofKind(ops, SemanticOpKind.TRY_CATCH).get(0);
            KindPayload.TryCatchPayload payload =
                (KindPayload.TryCatchPayload) tryCatch.payload();
            check(payload.catchBinding() != null,
                "the TRY_CATCH carries the catch binding (the caught DEAL failure is "
                    + "reified as an Error value bound to it)");
            SemanticOp breakOp = ofKind(ops, SemanticOpKind.BREAK).get(0);
            check(loop.opId().equals(
                    ((KindPayload.BreakPayload) breakOp.payload()).loopId()),
                "the BREAK transfers across the enclosing TRY_CATCH boundary to the "
                    + "nearest loop");
            SemanticOp throwOp = ofKind(ops, SemanticOpKind.THROW).get(0);
            check(throwOp.failurePolicy() == FailurePolicyId.THROW_TRANSFER,
                "the THROW carries THROW_TRANSFER — code/message from the supplied Error "
                    + "value, origin = the THROW origin, and a catch-block failure links "
                    + "cause = the original caught failure");
            SemanticOp load = opById(ops,
                result.table().blockOps().get(payload.catchBlock()).get(1));
            check(load.kind() == SemanticOpKind.BINDING_LOAD
                    && ((KindPayload.ThrowPayload) throwOp.payload()).errorValue()
                        .equals(load.result()),
                "the catch re-throw operand is the catch binding's loaded Error value"
                    + " (the load follows the catch binding's producing ALLOC)");
        }

        // (g) DISCARD audits a completed value.
        {
            CheckedSlice slice = checkSlice("\"probe\";");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors(),
                "the discard seed lowers: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors()) { return; }
            List<SemanticOp> ops = result.unit().ops().stream()
                .filter(op -> op.kind() != SemanticOpKind.MODULE_INIT)
                .toList();
            check(ops.size() == 2 && ops.get(0).kind() == SemanticOpKind.CONST
                    && ops.get(1).kind() == SemanticOpKind.DISCARD,
                "the expression statement lowers to CONST + DISCARD");
            check(ops.get(0).result().equals(
                    ((KindPayload.DiscardPayload) ops.get(1).payload()).value()),
                "the DISCARD carries the completed value — the intentional discard is "
                    + "audited in the op stream, never inferred away");
            check(ops.get(1).result() == null && ops.get(1).resultType() == null,
                "the DISCARD publishes no result");
        }

        // (h) The combined three-domain corpus passes the full production
        // seam — every constituent validator accepts the shapes.
        {
            CheckedSlice slice = checkSlice("""
                for (let xs: int[] of [[1, 2]]) {
                  xs[(xs[xs.length] = 1)] = 2
                }
                while (({b: true}).b = false) {
                  for (;;) { break }
                }
                try {} catch (e) { throw e }
                for (let e: int of [1, 2]) { e }
                delete {x: 1}.y
                delete [1, 2][0]
                """);
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            check(result != null && !result.hasErrors() && result.unit() != null,
                "the combined three-domain corpus lowers through the full production "
                    + "chain: " + (result == null ? "null" : result.diagnostics()));
            if (result == null || result.hasErrors() || result.unit() == null) { return; }
            check(AddressChainProtocol.validate(result.unit()).isEmpty(),
                "the corpus passes the address-chain protocol");
            check(ControlFlowValidator.validate(result.unit(), result.table()).isEmpty(),
                "the corpus passes the control-flow validator");
            Map<OpId, BlockId> opBlocks = result.table().opBlocks();
            boolean everyOpInOneBlock = result.unit().ops().stream()
                .allMatch(op -> opBlocks.get(op.opId()) != null
                    || op.kind() == SemanticOpKind.MODULE_INIT);
            check(everyOpInOneBlock,
                "every op of the corpus is a member of exactly one block "
                    + "(StructuredBodyTable completeness; the module-level "
                    + "MODULE_INIT envelope op is the pinned exemption)");
        }
    }

    // =========================================================================
    // 9. Control-flow negatives — invalid loop target, block-tree defects
    // =========================================================================

    static void testControlNegatives() {
        System.out.println("-- Control negatives: invalid loop target E6005 CONTROL_EXIT, "
            + "orphan/dominance E6005 CONTROL_BLOCK_TREE --");

        CheckedSlice slice = checkSlice("for (;;) { break; }");
        if (slice == null) { return; }
        SemanticLowerer.LoweringResult result = lowerDetected(slice);
        check(result != null && !result.hasErrors() && result.unit() != null,
            "the negative-control seed lowers: "
                + (result == null ? "null" : result.diagnostics()));
        if (result == null || result.hasErrors() || result.unit() == null) { return; }
        LoweredModuleUnit unit = result.unit();
        StructuredBodyTable table = result.table();

        // (a) A BREAK targeting a non-loop op — an invalid recorded target
        // is E6005 CONTROL_EXIT, never a silent fallthrough.
        {
            SemanticOp breakOp = ofKind(unit.ops(), SemanticOpKind.BREAK).get(0);
            SemanticOp constOp = ofKind(unit.ops(), SemanticOpKind.CONST).get(0);
            SemanticOp retargeted = rebuildOp(breakOp,
                new KindPayload.BreakPayload(constOp.opId()));
            List<SemanticOp> corruptOps = new ArrayList<>(unit.ops());
            corruptOps.set(corruptOps.indexOf(breakOp), retargeted);
            checkE6005(ControlFlowValidator.validate(withOps(unit, corruptOps), table),
                ControlFlowValidator.CONTROL_EXIT,
                "a BREAK targeting a non-loop op fails E6005 CONTROL_EXIT");
        }

        // (b) A CONTINUE targeting a non-enclosing loop.
        {
            CheckedSlice continueSlice = checkSlice("for (;;) { continue; }");
            if (continueSlice != null) {
                SemanticLowerer.LoweringResult continueResult =
                    lowerDetected(continueSlice);
                if (continueResult != null && !continueResult.hasErrors()
                        && continueResult.unit() != null) {
                    LoweredModuleUnit continueUnit = continueResult.unit();
                    SemanticOp continueOp = ofKind(continueUnit.ops(),
                        SemanticOpKind.CONTINUE).get(0);
                    SemanticOp constOp = ofKind(continueUnit.ops(),
                        SemanticOpKind.CONST).get(0);
                    SemanticOp retargeted = rebuildOp(continueOp,
                        new KindPayload.ContinuePayload(constOp.opId()));
                    List<SemanticOp> corruptOps = new ArrayList<>(continueUnit.ops());
                    corruptOps.set(corruptOps.indexOf(continueOp), retargeted);
                    checkE6005(ControlFlowValidator.validate(
                            withOps(continueUnit, corruptOps), continueResult.table()),
                        ControlFlowValidator.CONTROL_EXIT,
                        "a CONTINUE targeting a non-loop op fails E6005 CONTROL_EXIT");
                }
            }
        }

        // (c) An orphan block — an extra table block referenced by no
        // payload position fails E6005 CONTROL_BLOCK_TREE.
        {
            Map<BlockId, List<OpId>> corruptBlocks = new LinkedHashMap<>(
                table.blockOps());
            corruptBlocks.put(new BlockId(7_777), List.of());
            checkE6005(ControlFlowValidator.validate(unit, rebuildTable(corruptBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "an orphan block fails E6005 CONTROL_BLOCK_TREE");
        }

        // (d) An op after a terminator in its block (bad dominance).
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
            checkE6005(ControlFlowValidator.validate(withOps(unit, corruptOps),
                    rebuildTable(corruptBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "an op after a terminator in its block fails E6005 CONTROL_BLOCK_TREE");
        }
    }

    // =========================================================================
    // 10. Failure injections per constituent module (T1–T7 outputs)
    // =========================================================================

    static void testConstituentFailureInjections() {
        System.out.println("-- Constituent failure injections: each broken module breaks "
            + "the chain --");

        // T1 — AddressChainProtocol: a corrupted chain shape breaks the
        // production seam with E6005 ADDRESS_CHAIN_SHAPE.
        {
            CheckedSlice slice = checkSlice(
                "for (let xs: int[] of [[1, 2]]) { delete xs[0] }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            if (result == null || result.hasErrors() || result.unit() == null) { return; }
            LoweredModuleUnit unit = result.unit();
            SemanticOp chain = ofKind(unit.ops(), SemanticOpKind.DELETE).get(0);
            KindPayload.DeletePayload original =
                (KindPayload.DeletePayload) chain.payload();
            List<OpId> missingLength = new ArrayList<>(original.childOps());
            missingLength.remove(2);
            LoweredModuleUnit corrupted = withOps(unit,
                unit.ops().stream().map(op -> op.opId().equals(chain.opId())
                    ? rebuildOp(op, new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                        missingLength))
                    : op).toList());
            checkE6005(AddressChainProtocol.validate(corrupted), "ADDRESS_CHAIN_SHAPE",
                "T1 broken (chain without its lengthOp) fails the seam with E6005 "
                    + "ADDRESS_CHAIN_SHAPE");
        }

        // T2 — ComparisonSelectorLowering + ComparisonExecutor: a no-row
        // pair and an arithmetic selector fail closed.
        {
            SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
            ValueId left = allocator.nextValueId(MODULE, 0, 0);
            ValueId right = allocator.nextValueId(MODULE, 1, 0);
            AnchorId anchor = allocator.nextAnchorId(MODULE, 2, 0);
            SourceOrigin origin = new SourceOrigin(SOURCE_ID,
                SourceSpan.synthetic(SOURCE_ID), SourceOriginKind.USER, anchor, null);
            boolean defective = false;
            try {
                ComparisonSelectorLowering.produce(MODULE, BinaryOp.LT,
                    Type.Boolean.INSTANCE, Type.Boolean.INSTANCE, left, right, origin,
                    allocator, 3, 0);
            } catch (ComparisonSelectorLowering.Defect defect) {
                defective = true;
                check(ComparisonSelectorLowering.e6005(MODULE, defect).message()
                    .contains("COMPARISON_SELECTOR"),
                    "T2 broken (relational over booleans) fails with E6005 "
                        + "COMPARISON_SELECTOR");
            }
            check(defective, "the T2 producer fails closed on a no-row pair");
            boolean executorDefective = false;
            try {
                ComparisonExecutor.compare(BinarySelector.NUMBER_ADD,
                    new ComparisonOperandView.Number(1.0),
                    new ComparisonOperandView.Number(2.0), null, null);
            } catch (ComparisonExecutor.Defect defect) {
                executorDefective = true;
            }
            check(executorDefective,
                "T2 broken (arithmetic selector in the executor) fails closed");
        }

        // T3 — ControlFlowValidator: a bad block table breaks the seam.
        {
            CheckedSlice slice = checkSlice("for (;;) { break; }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            if (result == null || result.hasErrors() || result.unit() == null) { return; }
            Map<BlockId, List<OpId>> corruptBlocks = new LinkedHashMap<>(
                result.table().blockOps());
            corruptBlocks.put(new BlockId(8_888), List.of());
            checkE6005(ControlFlowValidator.validate(result.unit(),
                    rebuildTable(corruptBlocks)),
                ControlFlowValidator.CONTROL_BLOCK_TREE,
                "T3 broken (orphan block) fails the seam with E6005 CONTROL_BLOCK_TREE");
        }

        // T4/E4 — BoundaryExecutor: a policy outside the closed 11-policy
        // subset fails closed as a producer defect.
        {
            boolean defective = false;
            try {
                BoundaryExecutor.check(FailurePolicyId.INT32_RESULT,
                    RuntimeDescriptor.Int.INSTANCE, intView(1), BoundaryContext.none());
            } catch (BoundaryExecutor.Defect defect) {
                defective = true;
            }
            check(defective,
                "T4 broken (a non-BOUNDARY policy reaching the boundary executor) fails "
                    + "closed as a producer defect");
        }

        // T5 — NormalizedSlot: a table mode through the array computation
        // fails closed (mode purity).
        {
            boolean defective = false;
            try {
                NormalizedSlot.arraySlot(IndexMode.TABLE_WRITE, 0, 1);
            } catch (IllegalArgumentException error) {
                defective = true;
            }
            check(defective,
                "T5 broken (a table mode through the array computation) fails closed");
        }

        // T6 — the frontend gates: E3018 must fire before any lowering op
        // exists.
        {
            List<CompilerDiagnostic> gate = checkSliceExpectingErrors(
                "for (let t: table of [{x: 1}]) { t[0] = 1 }",
                "the gate injection seed");
            check(gate.stream().anyMatch(d -> "E3018".equals(d.code())),
                "T6 broken (the E3018 gate missing) would admit the non-string key to "
                    + "lowering — the gate fires in the checker, before lowering");
        }

        // T7 — the foundation closed validator: a corrupted contract digest
        // fails the closed rule set with E6005 R-DIGEST.
        {
            CheckedSlice slice = checkSlice("for (;;) { break; }");
            if (slice == null) { return; }
            SemanticLowerer.LoweringResult result = lowerDetected(slice);
            if (result == null || result.hasErrors() || result.unit() == null) { return; }
            LoweredModuleUnit unit = result.unit();
            SemanticOp first = unit.ops().get(0);
            OperationContractSnapshot bad = new OperationContractSnapshot(
                first.contract().version(), first.kind(), first.resultType(),
                first.operandTypes(), first.contract().selector(), first.payload(),
                first.failurePolicy(), first.contract().referencedSemanticIds(),
                "corrupted-digest");
            SemanticOp corrupted = new SemanticOp(first.opId(), first.kind(),
                first.origin(), first.result(), first.resultType(), first.operands(),
                first.operandTypes(), first.payload(), first.failurePolicy(), bad);
            List<SemanticOp> corruptOps = new ArrayList<>(unit.ops());
            corruptOps.set(0, corrupted);
            Optional<CompilerDiagnostic> rejected = SemanticIrValidator.validate(
                withOps(unit, corruptOps),
                new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
                    SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
            check(rejected.isPresent() && "E6005".equals(rejected.get().code())
                    && rejected.get().message().contains("R-DIGEST"),
                "T7 broken (a corrupted contract digest) fails the foundation validator "
                    + "with E6005 R-DIGEST: " + rejected);
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Evaluation Order Integration Test (ISSUE-0410, "
            + "decomposition tail) ===\n");

        testChainOrderMatrix();
        testChainFailureProjections();
        testChainSingleEvaluationAndRetainedShapeDetection();
        testFrontendGates();
        testBytesComparisonAdmission();
        testComparisonExecutorMatrix();
        testComparisonProductionMatrix();
        testComparisonSelectorGuard();
        testControlMatrix();
        testControlNegatives();
        testConstituentFailureInjections();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
