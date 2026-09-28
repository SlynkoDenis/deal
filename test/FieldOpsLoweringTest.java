package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.lexer.Lexer;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ClassOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryResult;
import deal.semantic.ir.ClassOpsExecutor.FieldState;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.ValueId;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Verifies the ISSUE-0513 field-operation lowering arms of
 * {@link SemanticLowerer} (class-construction-jsonable-operations
 * K-D6/K-D7; parent D16 rows {@code FIELD_READ}/{@code FIELD_WRITE}/
 * {@code FIELD_DELETE}/{@code HAS_FIELD}): the class member-read arm,
 * the class-field assignment/delete chains with the pinned boundary
 * children, the {@code has} arm, the cross-module nullable read shape,
 * and the combined T1+T2+T3 executor drive over one instance.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>a class member read — exactly one {@code FIELD_READ} with the
 *       receiver lowered once, plus two {@code BOUNDARY} children in
 *       order ({@code UNTYPED_CLASS_INPUT} with descriptor
 *       {@code class:<ClassId>} and input = the receiver;
 *       {@code OPTIONAL_FIELD_READ} with the read's checked result
 *       descriptor and input = the {@code FIELD_READ} result) — the
 *       descriptor-kind policies, {@code RuntimeValidation},
 *       {@code parentOpId} = the {@code FIELD_READ} op;</li>
 *   <li>an optional-field read — the nullable-wrapped result
 *       descriptor;</li>
 *   <li>the cross-module nullable class read — the receiver lowers as
 *       checked (nullable) and the runtime null guard is the
 *       {@code UNTYPED_CLASS_INPUT} boundary;</li>
 *   <li>a class field assignment — the closed {@code CLASS_FIELD}
 *       {@code ASSIGN} chain {@code [containerOp, valueOp,
 *       FIELD_WRITE]} (zero chain boundary ops) with the
 *       {@code FIELD_WRITE} commit carrying two {@code BOUNDARY}
 *       children in order ({@code UNTYPED_CLASS_INPUT} +
 *       {@code CLASS_FIELD_ASSIGNMENT} with the field's declared
 *       descriptor and input = the stored value) and the chain passing
 *       {@code AddressChainProtocol} validation;</li>
 *   <li>a class field delete — the closed {@code CLASS_FIELD}
 *       {@code DELETE} chain {@code [containerOp, FIELD_DELETE]} with
 *       one {@code UNTYPED_CLASS_INPUT} child;</li>
 *   <li>{@code has(obj.field)} — exactly one {@code HAS_FIELD} with the
 *       static key, result {@code boolean}, policy
 *       {@code NO_DEAL_FAILURE}, no boundary children, the receiver
 *       lowered once;</li>
 *   <li>the combined T1+T2+T3 scenario — a checked source declaring a
 *       class (T1), constructing it (T2), then reading, writing,
 *       deleting, and {@code has}-checking fields (T3) lowers to a
 *       validated unit, and the executor drives construction plus field
 *       ops over the same instance end-to-end asserting the presence
 *       states (this scenario fails if T1's layout or T2's construction
 *       breaks);</li>
 *   <li>determinism — two repetitions produce byte-identical
 *       {@link SemanticIrDumper} dumps.</li>
 * </ol>
 */
public class FieldOpsLoweringTest {

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

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record PipelineSlice(CheckedSlice slice, String interfaceHash,
                                 ExternalModuleInterface ownInterface,
                                 Map<ConstructKind, List<SemanticOpKind>> coverage) {
    }

    // =========================================================================
    // Whole-pipeline helpers (lexer/parser/checker -> lowerModuleClassCore)
    // =========================================================================

    private static CheckedSlice checkSlice(String source) {
        return checkSlice(source, null);
    }

    private static CheckedSlice checkSlice(String source, ModuleResolver resolver) {
        Lexer lexer = new Lexer(source, SOURCE_ID);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), SOURCE_ID);
        deal.parser.ParseResult parse = parser.parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nameResolver = new NameResolver(MODULE.path(), resolver);
        SymbolTable symbols = nameResolver.resolve(parse.program());
        check(nameResolver.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + nameResolver.diagnostics());
        if (!nameResolver.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(MODULE.path(), symbols, nameResolver,
            parse.program());
        check(checks.diagnostics().isEmpty(), "the slice checks cleanly: " + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

    /** The foundation detector's project facts of the slice (index + coverage). */
    private static PipelineSlice pipeline(CheckedSlice slice) {
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
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests() != null && manifests.manifests().size() == 1,
            "the foundation detector produces exactly one requirement manifest: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests() == null || manifests.manifests().size() != 1) {
            return null;
        }
        Map<ConstructKind, List<SemanticOpKind>> coverage =
            new LinkedHashMap<>(manifests.manifests().get(0).constructCoverage());
        coverage.remove(ConstructKind.IMPORT_EXPORT_ENTRY);
        ExternalModuleInterface own = built.index().modules().get(MODULE);
        check(own != null, "the index carries the module's own interface entry");
        return new PipelineSlice(slice, built.index().interfaceIndexDigest(), own, coverage);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    /** The whole-pipeline driver: lexer/parser/checker &#8594; lowerModuleClassCore. */
    private static SemanticLowerer.ClassDeclarationCoreResult lowerModule(String source) {
        return lowerModule(source, null);
    }

    private static SemanticLowerer.ClassDeclarationCoreResult lowerModule(String source,
            ModuleResolver resolver) {
        CheckedSlice slice = checkSlice(source, resolver);
        if (slice == null) {
            return null;
        }
        PipelineSlice pipeline = pipeline(slice);
        if (pipeline == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleClassCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, pipeline.coverage(), pipeline.interfaceHash(),
            REGISTRY_HASH, pipeline.ownInterface(),
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    private static List<SemanticOp> ofKind(List<SemanticOp> ops, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : ops) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    private static SemanticOp opById(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    /** The boundary children of {@code owner} in emission order. */
    private static List<SemanticOp> childrenOf(LoweredModuleUnit unit, SemanticOp owner) {
        List<SemanticOp> children = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && owner.opId().equals(op.origin().parentOpId())) {
                children.add(op);
            }
        }
        return children;
    }

    /** The single op producing {@code result} (the lowered-once probe). */
    private static List<SemanticOp> producersOf(LoweredModuleUnit unit, ValueId result) {
        List<SemanticOp> producers = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (result.equals(op.result())) {
                producers.add(op);
            }
        }
        return producers;
    }

    // =========================================================================
    // (a) the class member-read arm
    // =========================================================================

    private static void testFieldReadArm() {
        System.out.println("-- class member read: FIELD_READ + UNTYPED_CLASS_INPUT + "
            + "OPTIONAL_FIELD_READ --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            class Point { x: int; tag?: string; }
            let p: Point = {x: 1}
            let a: int = p.x
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the read slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> reads = ofKind(unit.ops(), SemanticOpKind.FIELD_READ);
        check(reads.size() == 1, "exactly one FIELD_READ op; got " + reads.size());
        if (reads.size() != 1) {
            return;
        }
        SemanticOp read = reads.get(0);
        ClassId pointId = new ClassId("main", "Point");
        KindPayload.FieldReadPayload payload = (KindPayload.FieldReadPayload) read.payload();
        check(payload.classId().equals(pointId) && payload.field().equals("x"),
            "the payload carries the checker-resolved classId and the field name; got "
                + payload.classId() + "." + payload.field());
        check(read.result() instanceof ValueId,
            "the op publishes a ValueId result");
        check(read.resultType().equals(RuntimeDescriptor.Int.INSTANCE),
            "the result type is the read's checked result descriptor int; got "
                + read.resultType());
        check(read.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the FIELD_READ policy is NO_DEAL_FAILURE; got " + read.failurePolicy());

        // The receiver lowers exactly once.
        List<SemanticOp> receivers = producersOf(unit, payload.classValue());
        check(receivers.size() == 1,
            "the receiver ValueId has exactly one producing op (lowered once); got "
                + receivers.size());

        // The two boundary children in order.
        List<SemanticOp> children = childrenOf(unit, read);
        check(children.size() == 2,
            "exactly two boundary children under the FIELD_READ op; got " + children.size());
        if (children.size() == 2) {
            SemanticOp receiverBoundary = children.get(0);
            SemanticOp fieldBoundary = children.get(1);
            check(receiverBoundary.kind() == SemanticOpKind.BOUNDARY
                    && receiverBoundary.payload() instanceof KindPayload.BoundaryPayload
                        receiverPayload
                    && receiverPayload.kind() == BoundaryKind.UNTYPED_CLASS_INPUT,
                "child 1 is a BOUNDARY op of kind UNTYPED_CLASS_INPUT");
            if (receiverBoundary.payload() instanceof KindPayload.BoundaryPayload
                    receiverPayload) {
                check(receiverPayload.descriptor()
                            .equals(new RuntimeDescriptor.Class(pointId)),
                    "child 1 carries descriptor class:<ClassId>; got "
                        + receiverPayload.descriptor().canonicalSpecText());
                check(receiverPayload.input().equals(payload.classValue()),
                    "child 1 input is the receiver value op id");
                check(receiverBoundary.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                    "child 1 carries the descriptor-kind policy TYPE_DESCRIPTOR; got "
                        + receiverBoundary.failurePolicy());
                check(receiverPayload.realization()
                        instanceof BoundaryRealization.RuntimeValidation,
                    "child 1 realization is RuntimeValidation");
                check(receiverBoundary.origin().kind() == SourceOriginKind.SYNTHETIC,
                    "child 1 origin is SYNTHETIC");
            }
            check(fieldBoundary.kind() == SemanticOpKind.BOUNDARY
                    && fieldBoundary.payload() instanceof KindPayload.BoundaryPayload
                        fieldPayload
                    && fieldPayload.kind() == BoundaryKind.OPTIONAL_FIELD_READ,
                "child 2 is a BOUNDARY op of kind OPTIONAL_FIELD_READ");
            if (fieldBoundary.payload() instanceof KindPayload.BoundaryPayload fieldPayload) {
                check(fieldPayload.descriptor().equals(RuntimeDescriptor.Int.INSTANCE),
                    "child 2 carries the read's checked result descriptor int (a required "
                        + "field, no nullable wrap); got "
                        + fieldPayload.descriptor().canonicalSpecText());
                check(fieldPayload.input().equals(read.result()),
                    "child 2 input is the FIELD_READ result ValueId");
                check(fieldBoundary.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                    "child 2 carries the descriptor-kind policy TYPE_DESCRIPTOR; got "
                        + fieldBoundary.failurePolicy());
                check(fieldPayload.realization()
                        instanceof BoundaryRealization.RuntimeValidation,
                    "child 2 realization is RuntimeValidation");
            }
            check(read.opId().equals(receiverBoundary.origin().parentOpId())
                    && read.opId().equals(fieldBoundary.origin().parentOpId()),
                "both children record parentOpId = the FIELD_READ op");
        }
    }

    // =========================================================================
    // (b) the optional-field read: the nullable-wrapped result descriptor
    // =========================================================================

    private static void testOptionalFieldReadArm() {
        System.out.println("-- optional-field read: the checker's nullable-wrapped "
            + "result descriptor --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            class Point { x: int; tag?: string; }
            let p: Point = {x: 1}
            let t: string | null = p.tag
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the optional-read slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> reads = ofKind(unit.ops(), SemanticOpKind.FIELD_READ);
        check(reads.size() == 1, "exactly one FIELD_READ op; got " + reads.size());
        if (reads.size() != 1) {
            return;
        }
        SemanticOp read = reads.get(0);
        RuntimeDescriptor nullableString =
            new RuntimeDescriptor.Nullable(RuntimeDescriptor.String.INSTANCE);
        check(read.resultType().equals(nullableString),
            "the result type is the nullable-wrapped checked result descriptor ?string; got "
                + read.resultType());
        List<SemanticOp> children = childrenOf(unit, read);
        check(children.size() == 2,
            "exactly two boundary children; got " + children.size());
        if (children.size() == 2
                && children.get(1).payload() instanceof KindPayload.BoundaryPayload payload) {
            check(payload.kind() == BoundaryKind.OPTIONAL_FIELD_READ
                    && payload.descriptor().equals(nullableString),
                "child 2 carries descriptor ?string (the optional field's nullable-wrapped "
                    + "type); got " + payload.kind() + " "
                    + payload.descriptor().canonicalSpecText());
        }
    }

    // =========================================================================
    // (c) the cross-module nullable class read
    // =========================================================================

    private static void testCrossModuleNullableReadArm() {
        System.out.println("-- cross-module nullable class read: the receiver lowers as "
            + "checked (nullable), the UNTYPED_CLASS_INPUT boundary is the runtime null "
            + "guard --");

        final String lib = "./jsonable_batch2_lib";
        TypingResolver resolver = new TypingResolver(lib);
        deal.ast.Span span = new deal.ast.Span(lib, 1, 1, 1, 5);
        deal.checker.Symbol.ClassSymbol child = new deal.checker.Symbol.ClassSymbol("Child",
            List.of(new deal.ast.ClassField(span, "value", false, false,
                new deal.ast.NamedType(span, "int"), java.util.Optional.empty())),
            lib, IdentityTestFixtures.identityOf(lib, "Child"));
        deal.checker.Symbol.ClassSymbol parent = new deal.checker.Symbol.ClassSymbol("Parent",
            List.of(new deal.ast.ClassField(span, "children", false, false,
                new deal.ast.ArrayType(span, new deal.ast.NamedType(span, "Child")),
                java.util.Optional.empty())),
            lib, IdentityTestFixtures.identityOf(lib, "Parent"));
        resolver.registerClassSymbol(lib, child);
        resolver.registerClassSymbol(lib, parent);
        resolver.register(lib, Map.of("Parent", IdentityTestFixtures.classType("Parent", lib),
            "Child", IdentityTestFixtures.classType("Child", lib)));

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            import * as Lib from "./jsonable_batch2_lib"
            class Point { x: int; }
            let u: Lib.Parent | null = null;
            let children: Lib.Child[] = u.children;
            """, resolver);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the cross-module nullable-read slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> reads = ofKind(unit.ops(), SemanticOpKind.FIELD_READ);
        check(reads.size() == 1, "exactly one FIELD_READ op; got " + reads.size());
        if (reads.size() != 1) {
            return;
        }
        SemanticOp read = reads.get(0);
        ClassId parentId = new ClassId(lib, "Parent");
        KindPayload.FieldReadPayload payload = (KindPayload.FieldReadPayload) read.payload();
        check(payload.classId().equals(parentId) && payload.field().equals("children"),
            "the payload names the foreign class identity and the field; got "
                + payload.classId() + "." + payload.field());

        // The receiver lowers as checked: its single producing op
        // publishes the nullable class descriptor.
        List<SemanticOp> receivers = producersOf(unit, payload.classValue());
        check(receivers.size() == 1,
            "the receiver ValueId has exactly one producing op; got " + receivers.size());
        if (receivers.size() == 1) {
            SemanticOp receiverOp = receivers.get(0);
            check(receiverOp.resultType() instanceof RuntimeDescriptor.Nullable nullable
                    && nullable.inner() instanceof RuntimeDescriptor.Class inner
                    && inner.classId().equals(parentId),
                "the receiver's producing op publishes the checked nullable descriptor "
                    + "?@lib/Parent; got " + receiverOp.resultType());
        }
        List<SemanticOp> children = childrenOf(unit, read);
        check(children.size() == 2,
            "exactly two boundary children; got " + children.size());
        if (!children.isEmpty()
                && children.get(0).payload() instanceof KindPayload.BoundaryPayload
                    receiverPayload) {
            check(receiverPayload.kind() == BoundaryKind.UNTYPED_CLASS_INPUT
                    && receiverPayload.descriptor().equals(new RuntimeDescriptor.Class(parentId))
                    && receiverPayload.input().equals(payload.classValue()),
                "child 1 is the UNTYPED_CLASS_INPUT boundary on descriptor class:<Parent> "
                    + "with input = the receiver — the runtime null guard; got "
                    + receiverPayload.kind() + " "
                    + receiverPayload.descriptor().canonicalSpecText());
        }
        if (children.size() == 2
                && children.get(1).payload() instanceof KindPayload.BoundaryPayload
                    fieldPayload) {
            RuntimeDescriptor childArray = new RuntimeDescriptor.Array(
                new RuntimeDescriptor.Class(new ClassId(lib, "Child")));
            check(fieldPayload.kind() == BoundaryKind.OPTIONAL_FIELD_READ
                    && fieldPayload.descriptor().equals(childArray),
                "child 2 carries the read's checked result descriptor [@lib/Child]; got "
                    + fieldPayload.kind() + " "
                    + fieldPayload.descriptor().canonicalSpecText());
        }
    }

    // =========================================================================
    // (d) the class-field assignment arm
    // =========================================================================

    private static void testFieldWriteArm() {
        System.out.println("-- class field assignment: [containerOp, valueOp, FIELD_WRITE] "
            + "with UNTYPED_CLASS_INPUT + CLASS_FIELD_ASSIGNMENT children --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            class Point { x: int; y?: int = 0; }
            let p: Point = {x: 1}
            p.x = 9
            p.y = 3
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the write slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        ClassId pointId = new ClassId("main", "Point");

        check(deal.semantic.ir.AddressChainProtocol.validate(unit).isEmpty(),
            "the produced ASSIGN/DELETE class-field chains pass AddressChainProtocol "
                + "validation");

        List<SemanticOp> chains = ofKind(unit.ops(), SemanticOpKind.ASSIGN);
        check(chains.size() == 2, "exactly two ASSIGN chain ops; got " + chains.size());
        if (chains.size() != 2) {
            return;
        }
        for (SemanticOp chain : chains) {
            KindPayload.AssignPayload chainPayload = (KindPayload.AssignPayload) chain.payload();
            check(chainPayload.targetKind() == deal.semantic.ir.AssignTargetKind.CLASS_FIELD
                    && chainPayload.childOps().size() == 3,
                "the chain is CLASS_FIELD with three children; got " + chainPayload);
            if (chainPayload.childOps().size() != 3) {
                continue;
            }
            SemanticOp containerOp = opById(unit, chainPayload.childOps().get(0));
            SemanticOp valueOp = opById(unit, chainPayload.childOps().get(1));
            SemanticOp commitOp = opById(unit, chainPayload.childOps().get(2));
            check(containerOp != null && valueOp != null && commitOp != null,
                "the three chain children resolve in the unit's op list");
            check(commitOp != null && commitOp.kind() == SemanticOpKind.FIELD_WRITE,
                "the commit child is FIELD_WRITE");
            if (commitOp == null || commitOp.kind() != SemanticOpKind.FIELD_WRITE) {
                continue;
            }
            KindPayload.FieldWritePayload write =
                (KindPayload.FieldWritePayload) commitOp.payload();
            check(write.classId().equals(pointId)
                    && write.classValue().equals(containerOp.result())
                    && write.value().equals(valueOp.result()),
                "the FIELD_WRITE payload references the resolved receiver and stored "
                    + "value; got " + write);
            check(commitOp.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
                "the commit carries NO_DEAL_FAILURE");
            check(chain.opId().equals(commitOp.origin().parentOpId()),
                "the commit records the chain op as parentOpId");

            // The commit's two boundary children in order.
            List<SemanticOp> children = childrenOf(unit, commitOp);
            check(children.size() == 2,
                "exactly two boundary children under the FIELD_WRITE commit; got "
                    + children.size());
            if (children.size() != 2) {
                continue;
            }
            SemanticOp receiverBoundary = children.get(0);
            SemanticOp fieldBoundary = children.get(1);
            check(receiverBoundary.payload() instanceof KindPayload.BoundaryPayload
                        receiverPayload
                    && receiverPayload.kind() == BoundaryKind.UNTYPED_CLASS_INPUT
                    && receiverPayload.descriptor().equals(new RuntimeDescriptor.Class(pointId))
                    && receiverPayload.input().equals(write.classValue())
                    && receiverBoundary.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR
                    && receiverPayload.realization()
                        instanceof BoundaryRealization.RuntimeValidation,
                "child 1 is UNTYPED_CLASS_INPUT on class:<ClassId> with input = the "
                    + "receiver, TYPE_DESCRIPTOR, RuntimeValidation");
            check(fieldBoundary.payload() instanceof KindPayload.BoundaryPayload
                        fieldPayload
                    && fieldPayload.kind() == BoundaryKind.CLASS_FIELD_ASSIGNMENT
                    && fieldPayload.input().equals(write.value())
                    && fieldBoundary.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR
                    && fieldPayload.realization()
                        instanceof BoundaryRealization.RuntimeValidation,
                "child 2 is CLASS_FIELD_ASSIGNMENT with input = the stored value, "
                    + "TYPE_DESCRIPTOR, RuntimeValidation");
            if (fieldBoundary.payload() instanceof KindPayload.BoundaryPayload fieldPayload) {
                RuntimeDescriptor declared = fieldPayload.descriptor();
                check(write.field().equals("x")
                        ? declared.equals(RuntimeDescriptor.Int.INSTANCE)
                        : declared.equals(RuntimeDescriptor.Int.INSTANCE),
                    "child 2 carries the field's declared descriptor int (never the "
                        + "optional-read nullable wrap); got " + declared
                            .canonicalSpecText());
            }
            check(commitOp.opId().equals(receiverBoundary.origin().parentOpId())
                    && commitOp.opId().equals(fieldBoundary.origin().parentOpId()),
                "both children record parentOpId = the FIELD_WRITE commit op");
        }
        // Zero chain boundary ops: no boundary child of any chain op.
        for (SemanticOp chain : chains) {
            check(childrenOf(unit, chain).isEmpty(),
                "the ASSIGN chain carries zero boundary children (the write check lives "
                    + "in the commit op)");
        }
    }

    // =========================================================================
    // (e) the class-field delete arm
    // =========================================================================

    private static void testFieldDeleteArm() {
        System.out.println("-- class field delete: [containerOp, FIELD_DELETE] with one "
            + "UNTYPED_CLASS_INPUT child --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            class Point { x: int; y?: int = 0; }
            let p: Point = {x: 1}
            delete p.y
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the delete slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        ClassId pointId = new ClassId("main", "Point");
        check(deal.semantic.ir.AddressChainProtocol.validate(unit).isEmpty(),
            "the produced DELETE class-field chain passes AddressChainProtocol "
                + "validation");
        List<SemanticOp> chains = ofKind(unit.ops(), SemanticOpKind.DELETE);
        check(chains.size() == 1, "exactly one DELETE chain op; got " + chains.size());
        if (chains.size() != 1) {
            return;
        }
        SemanticOp chain = chains.get(0);
        KindPayload.DeletePayload chainPayload = (KindPayload.DeletePayload) chain.payload();
        check(chainPayload.targetKind() == deal.semantic.ir.DeleteTargetKind.CLASS_FIELD
                && chainPayload.childOps().size() == 2,
            "the chain is DELETE CLASS_FIELD with two children; got " + chainPayload);
        if (chainPayload.childOps().size() != 2) {
            return;
        }
        SemanticOp containerOp = opById(unit, chainPayload.childOps().get(0));
        SemanticOp commitOp = opById(unit, chainPayload.childOps().get(1));
        check(containerOp != null && commitOp != null && commitOp.kind()
                == SemanticOpKind.FIELD_DELETE,
            "the commit child is FIELD_DELETE");
        check(childrenOf(unit, chain).isEmpty(),
            "the DELETE chain carries zero boundary children");
        if (commitOp == null || commitOp.kind() != SemanticOpKind.FIELD_DELETE) {
            return;
        }
        KindPayload.FieldDeletePayload delete = (KindPayload.FieldDeletePayload) commitOp.payload();
        check(delete.classId().equals(pointId) && delete.field().equals("y")
                && delete.classValue().equals(containerOp.result()),
            "the FIELD_DELETE payload references the resolved receiver, class, and "
                + "field; got " + delete);
        check(commitOp.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the commit carries NO_DEAL_FAILURE");
        check(chain.opId().equals(commitOp.origin().parentOpId()),
            "the commit records the chain op as parentOpId");
        List<SemanticOp> children = childrenOf(unit, commitOp);
        check(children.size() == 1,
            "exactly one boundary child under the FIELD_DELETE commit; got " + children.size());
        if (children.size() == 1
                && children.get(0).payload() instanceof KindPayload.BoundaryPayload payload) {
            check(payload.kind() == BoundaryKind.UNTYPED_CLASS_INPUT
                    && payload.descriptor().equals(new RuntimeDescriptor.Class(pointId))
                    && payload.input().equals(delete.classValue()),
                "the child is UNTYPED_CLASS_INPUT on class:<ClassId> with input = the "
                    + "receiver; got " + payload.kind() + " "
                    + payload.descriptor().canonicalSpecText());
            check(children.get(0).failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR
                    && payload.realization() instanceof BoundaryRealization.RuntimeValidation
                    && commitOp.opId().equals(children.get(0).origin().parentOpId()),
                "the child carries TYPE_DESCRIPTOR, RuntimeValidation, and parentOpId = "
                    + "the FIELD_DELETE commit");
        }
    }

    // =========================================================================
    // (f) the has arm
    // =========================================================================

    private static void testHasFieldArm() {
        System.out.println("-- has(obj.field): HAS_FIELD with the static key, no "
            + "children, boolean result --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            class Point { x: int; y?: int = 0; }
            let p: Point = {x: 1}
            let b: boolean = has(p.y)
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the has slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> hasOps = ofKind(unit.ops(), SemanticOpKind.HAS_FIELD);
        check(hasOps.size() == 1, "exactly one HAS_FIELD op; got " + hasOps.size());
        if (hasOps.size() != 1) {
            return;
        }
        SemanticOp has = hasOps.get(0);
        KindPayload.HasFieldPayload payload = (KindPayload.HasFieldPayload) has.payload();
        check(payload.key().equals("y"),
            "the key is the static field name 'y' (never evaluated); got " + payload.key());
        check(has.result() instanceof ValueId && has.resultType()
                .equals(RuntimeDescriptor.Boolean.INSTANCE),
            "the result is boolean; got " + has.resultType());
        check(has.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the policy is NO_DEAL_FAILURE; got " + has.failurePolicy());
        check(childrenOf(unit, has).isEmpty(),
            "no boundary children nest under the HAS_FIELD op");
        List<SemanticOp> receivers = producersOf(unit, payload.receiver());
        check(receivers.size() == 1,
            "the receiver ValueId has exactly one producing op (lowered once); got "
                + receivers.size());
    }

    // =========================================================================
    // (g) the combined T1+T2+T3 executor drive
    // =========================================================================

    private static void testCombinedT1T2T3ExecutorDrive() {
        System.out.println("-- combined T1+T2+T3: construction plus field ops over the "
            + "same instance end-to-end --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            export class Point { x: int = 40 + 2; tag?: string; }
            let p: Point = {tag: "t"}
            let xv: int = p.x
            let hasTag: boolean = has(p.tag)
            delete p.tag
            let hasTag2: boolean = has(p.tag)
            p.x = 99
            let xv2: int = p.x
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the combined slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null
                || result.lowering().hasErrors() || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        ClassId pointId = new ClassId("main", "Point");

        List<SemanticOp> classNews = ofKind(unit.ops(), SemanticOpKind.CLASS_NEW);
        List<SemanticOp> reads = ofKind(unit.ops(), SemanticOpKind.FIELD_READ);
        List<SemanticOp> writes = ofKind(unit.ops(), SemanticOpKind.FIELD_WRITE);
        List<SemanticOp> deletes = ofKind(unit.ops(), SemanticOpKind.FIELD_DELETE);
        List<SemanticOp> hasOps = ofKind(unit.ops(), SemanticOpKind.HAS_FIELD);
        check(classNews.size() == 1 && reads.size() == 2 && writes.size() == 1
                && deletes.size() == 1 && hasOps.size() == 2,
            "the unit carries one CLASS_NEW, two FIELD_READs, one FIELD_WRITE, one "
                + "FIELD_DELETE, and two HAS_FIELD ops; got " + classNews.size() + "/"
                + reads.size() + "/" + writes.size() + "/" + deletes.size() + "/"
                + hasOps.size());
        if (classNews.size() != 1 || reads.size() != 2 || writes.size() != 1
                || deletes.size() != 1 || hasOps.size() != 2) {
            return;
        }

        // The T1 tie: the literal's default application names the same
        // CLASS_DEFAULT op as the exported factory (a broken T1 layout/
        // default emission fails here).
        KindPayload.ClassNewPayload classNewPayload =
            (KindPayload.ClassNewPayload) classNews.get(0).payload();
        List<SemanticOp> factories = ofKind(unit.ops(), SemanticOpKind.CLASS_FACTORY);
        check(factories.size() == 1
                && classNewPayload.classDefaultOpIds()
                    .equals(((KindPayload.ClassFactoryPayload) factories.get(0).payload())
                        .classDefaultOpIds()),
            "the CLASS_NEW's default op ids equal the factory's list (the T1 tie)");

        // The fixture interpreter over the unit's ops in order.
        Map<OpId, SemanticOp> opLookup = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            opLookup.put(op.opId(), op);
        }
        Map<ValueId, Value> heap = new LinkedHashMap<>();
        Map<deal.semantic.ir.BindingId, Value> bindings = new LinkedHashMap<>();
        List<String> log = new ArrayList<>();
        BoundaryCheckRunner real = realDelegate(log);
        ClassOpsExecutor.BodyRunner bodyRunner = defaultOp ->
            new Value.Int(42);
        Map<ClassId, deal.semantic.ir.ClassLayout> layouts = unit.classLayouts();

        for (SemanticOp op : unit.ops()) {
            switch (op.kind()) {
                case CONST -> {
                    heap.put((ValueId) op.result(), constValue(op));
                }
                case CLASS_NEW -> {
                    Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(op, heap,
                        resolveDefaultOps(opLookup, classNewPayload.classDefaultOpIds()),
                        resolveBoundaryOps(opLookup, classNewPayload.fieldBoundaries()),
                        layouts, real, bodyRunner);
                    check(outcome instanceof Outcome.Success<Value> success
                            && success.value() instanceof Value.Class,
                        "the CLASS_NEW drive constructs the instance; got " + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    }
                }
                case BINDING_INIT -> {
                    KindPayload.BindingInitPayload init =
                        (KindPayload.BindingInitPayload) op.payload();
                    Value value = heap.get(init.value());
                    if (value != null) {
                        bindings.put(init.binding(), value);
                    }
                }
                case BINDING_LOAD -> {
                    KindPayload.BindingLoadPayload load =
                        (KindPayload.BindingLoadPayload) op.payload();
                    Value value = bindings.get(load.binding());
                    if (value != null) {
                        heap.put((ValueId) op.result(), value);
                    }
                }
                case FIELD_READ -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 2) {
                        fail("the FIELD_READ op has " + children.size()
                            + " boundary children (expected 2)");
                        continue;
                    }
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldRead(op, heap,
                        children.get(0), children.get(1), layouts, real);
                    check(outcome instanceof Outcome.Success<Value>,
                        "the FIELD_READ drive succeeds; got " + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    }
                }
                case FIELD_WRITE -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 2) {
                        fail("the FIELD_WRITE op has " + children.size()
                            + " boundary children (expected 2)");
                        continue;
                    }
                    KindPayload.FieldWritePayload write =
                        (KindPayload.FieldWritePayload) op.payload();
                    Value oldInstance = heap.get(write.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldWrite(op, heap,
                        children.get(0), children.get(1), layouts, real);
                    check(outcome instanceof Outcome.Success<Value> success
                            && success.value() instanceof Value.Class,
                        "the FIELD_WRITE drive succeeds; got " + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        rebind(heap, bindings, oldInstance, success.value());
                    }
                }
                case FIELD_DELETE -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 1) {
                        fail("the FIELD_DELETE op has " + children.size()
                            + " boundary children (expected 1)");
                        continue;
                    }
                    KindPayload.FieldDeletePayload delete =
                        (KindPayload.FieldDeletePayload) op.payload();
                    Value oldInstance = heap.get(delete.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldDelete(op, heap,
                        children.get(0), layouts, real);
                    check(outcome instanceof Outcome.Success<Value> success
                            && success.value() instanceof Value.Class,
                        "the FIELD_DELETE drive succeeds; got " + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        rebind(heap, bindings, oldInstance, success.value());
                    }
                }
                case HAS_FIELD -> {
                    Outcome<Value> outcome = ClassOpsExecutor.executeHasField(op, heap,
                        layouts);
                    check(outcome instanceof Outcome.Success<Value>,
                        "the HAS_FIELD drive succeeds; got " + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    }
                }
                default -> {
                    // BINDING_ALLOC, detached CLASS_DEFAULT/CLASS_FACTORY,
                    // VARIABLE_DECLARATION boundaries, and the
                    // ASSIGN/DELETE chain ops carry no interpreter step
                    // in this drive (the field ops executed inline).
                }
            }
        }

        // The end-to-end presence assertions over the same instance.
        Value.Class instance = (Value.Class) heap.get((ValueId) classNews.get(0).result());
        check(instance != null && instance.classId().equals(pointId),
            "the published instance carries the classId tag");
        if (instance == null) {
            return;
        }
        check(instance.fields().size() == 2
                && instance.fields().get(0) instanceof FieldState.Present xPresent
                && xPresent.value().equals(new Value.Int(99)),
            "after the write the same instance carries x=99");
        check(instance.fields().get(1) == FieldState.Missing.INSTANCE,
            "after the delete the same instance carries tag missing");
        check(reads.size() == 2
                && heap.get((ValueId) reads.get(0).result()).equals(new Value.Int(42))
                && heap.get((ValueId) reads.get(1).result()).equals(new Value.Int(99)),
            "the first read observed the defaulted 42 and the later read observed the "
                + "committed 99 (the write landed)");
        check(hasOps.size() == 2
                && heap.get((ValueId) hasOps.get(0).result()).equals(new Value.Bool(true))
                && heap.get((ValueId) hasOps.get(1).result()).equals(new Value.Bool(false)),
            "has(tag) returned true before the delete and false after it (the presence "
                + "states over the same instance)");
        check(log.contains("child UNTYPED_CLASS_INPUT <- class:" + pointId.text())
                && log.contains("child OPTIONAL_FIELD_READ <- int")
                && log.contains("child CLASS_FIELD_ASSIGNMENT <- int"),
            "the real boundary delegate observed the pinned child kinds and the "
                + "canonical receiver kind; got " + log);
    }

    /** Resolves the CLASS_NEW default-op lookup from the unit's op list. */
    private static Map<OpId, SemanticOp> resolveDefaultOps(Map<OpId, SemanticOp> opLookup,
                                                           List<OpId> ids) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (OpId id : ids) {
            resolved.put(id, opLookup.get(id));
        }
        return resolved;
    }

    /** Resolves the CLASS_NEW boundary lookup from the unit's op list. */
    private static Map<OpId, SemanticOp> resolveBoundaryOps(Map<OpId, SemanticOp> opLookup,
            List<KindPayload.FieldBoundary> boundaries) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : boundaries) {
            resolved.put(entry.boundaryOpId(), opLookup.get(entry.boundaryOpId()));
        }
        return resolved;
    }

    /** Rebinds every reference to the pre-commit instance to the updated instance. */
    private static void rebind(Map<ValueId, Value> heap,
                               Map<deal.semantic.ir.BindingId, Value> bindings,
                               Value oldInstance, Value updated) {
        for (Map.Entry<ValueId, Value> entry : new ArrayList<>(heap.entrySet())) {
            if (oldInstance.equals(entry.getValue())) {
                heap.put(entry.getKey(), updated);
            }
        }
        for (Map.Entry<deal.semantic.ir.BindingId, Value> entry
                : new ArrayList<>(bindings.entrySet())) {
            if (oldInstance.equals(entry.getValue())) {
                bindings.put(entry.getKey(), updated);
            }
        }
    }

    /** The closed scalar of one CONST op as an executor value. */
    private static Value constValue(SemanticOp op) {
        KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
        return switch (payload.value()) {
            case ScalarValue.Boolean bool -> new Value.Bool(bool.value());
            case ScalarValue.Int intValue -> new Value.Int(intValue.value());
            case ScalarValue.Number number -> new Value.Number(number.value());
            case ScalarValue.String string -> Value.string(string.value());
            default -> Value.Null.INSTANCE;
        };
    }

    /** The real BoundaryExecutor delegate adapted to the executor view. */
    private static BoundaryCheckRunner realDelegate(List<String> log) {
        return (boundary, input) -> {
            if (log != null) {
                log.add("child " + boundary.kind() + " <- " + tokenOf(input));
            }
            FailurePolicyId policy = boundary.descriptor() instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
            BoundaryOutcome outcome = BoundaryExecutor.check(policy, boundary.descriptor(),
                valueView(input), BoundaryContext.none());
            return switch (outcome) {
                case BoundaryOutcome.Pass pass ->
                    new BoundaryResult.Pass(publishValue(pass.value(), input));
                case BoundaryOutcome.Fail fail -> new BoundaryResult.Fail(fail.failure());
            };
        };
    }

    private static String tokenOf(Value input) {
        return input.actualKind() == ActualKind.CLASS
            ? "class:" + ((Value.Class) input).classId().text()
            : input.actualKind().token();
    }

    private static BoundaryValueView valueView(Value value) {
        return switch (value) {
            case Value.Null ignored -> BoundaryValueView.of(ActualKind.NULL);
            case Value.Bool bool -> BoundaryValueView.of(ActualKind.BOOLEAN);
            case Value.Int intValue -> BoundaryValueView.ofInt(intValue.value());
            case Value.Number number -> BoundaryValueView.ofNumber(number.value());
            case Value.String string -> BoundaryValueView.of(string.scalar().actualKind());
            case Value.Bytes ignored -> BoundaryValueView.of(ActualKind.BYTES);
            case Value.Table ignored -> BoundaryValueView.of(ActualKind.TABLE);
            case Value.Array ignored -> BoundaryValueView.of(ActualKind.ARRAY);
            case Value.Class classValue -> BoundaryValueView.ofClass(classValue.classId().text());
            case Value.Function function -> BoundaryValueView.ofFunction(function.signature());
            case Value.Missing ignored -> BoundaryValueView.of(ActualKind.MISSING);
        };
    }

    private static Value publishValue(BoundaryValueView view, Value input) {
        return view.kind() == ActualKind.NULL ? Value.Null.INSTANCE : input;
    }

    // =========================================================================
    // (h) determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- determinism: two repetitions are byte-identical --");

        String source = """
            export class Line { a: int = 1; b?: string; }
            class Point { x: int = 2; y?: int = 0; }
            let p: Point = {x: 1}
            let xv: int = p.x
            p.y = 3
            let b: boolean = has(p.y)
            delete p.y
            let l: Line = {}
            """;
        SemanticLowerer.ClassDeclarationCoreResult first = lowerModule(source);
        SemanticLowerer.ClassDeclarationCoreResult second = lowerModule(source);
        check(first != null && first.lowering() != null && !first.lowering().hasErrors()
                && second != null && second.lowering() != null
                && !second.lowering().hasErrors(),
            "both repetitions lower");
        if (first == null || first.lowering() == null || first.lowering().hasErrors()
                || second == null || second.lowering() == null
                || second.lowering().hasErrors()) {
            return;
        }
        byte[] firstDump = SemanticIrDumper.dumpModule(first.lowering().unit());
        byte[] secondDump = SemanticIrDumper.dumpModule(second.lowering().unit());
        check(java.util.Arrays.equals(firstDump, secondDump),
            "the two repetitions produce byte-identical SemanticIrDumper dumps");
        check(SemanticIrValidator.validate(first.lowering().unit(),
                new SemanticIrValidator.ComparisonFacts(first.lowering().unit().interfaceHash(),
                    SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH)).isEmpty(),
            "the field-op-bearing unit passes the closed SemanticIrValidator");
    }

    /**
     * The identity-aware single-foreign-module resolver of the
     * cross-module nullable-read case (the CrossModuleTypingTest
     * discipline): exports, class symbols, the identity-keyed class
     * routing, and the foreign field-type resolution
     * ({@code resolveTypeNodeInModule}) all route to the one registered
     * companion module.
     */
    private static final class TypingResolver implements ModuleResolver {

        private final String lib;
        private final Map<String, Map<String, deal.types.Type>> modules = new java.util.HashMap<>();
        private final Map<String, deal.checker.Symbol.ClassSymbol> classSymbols =
            new java.util.HashMap<>();

        TypingResolver(String lib) {
            this.lib = lib;
        }

        void register(String path, Map<String, deal.types.Type> exports) {
            modules.put(path, exports);
        }

        void registerClassSymbol(String modulePath,
                                 deal.checker.Symbol.ClassSymbol classSymbol) {
            classSymbols.put(modulePath + ":" + classSymbol.name(), classSymbol);
        }

        @Override
        public Map<String, deal.types.Type> resolveModule(String modulePath,
                String importingModule, java.util.Set<String> modulesInProgress)
                throws ModuleNotFoundException {
            Map<String, deal.types.Type> exports = modules.get(modulePath);
            if (exports == null) {
                throw new ModuleNotFoundException("Module not found: " + modulePath);
            }
            return exports;
        }

        @Override
        public deal.checker.Symbol.ClassSymbol resolveClassSymbol(String className,
                String modulePath, String importingModule) throws ModuleNotFoundException {
            return classSymbols.get(modulePath + ":" + className);
        }

        @Override
        public deal.checker.Symbol.ClassSymbol resolveClassSymbol(String className,
                deal.identity.CanonicalModuleIdentity declaringModule,
                String importingModule) throws ModuleNotFoundException {
            deal.checker.Symbol.ClassSymbol sym = classSymbols.get(lib + ":" + className);
            if (sym != null && sym.identity().moduleIdentity().equals(declaringModule)) {
                return sym;
            }
            return null;
        }

        @Override
        public boolean isFunctionExportedFromModule(
                deal.identity.CanonicalModuleIdentity declaringModule,
                String functionName, String importingModule) throws ModuleNotFoundException {
            Map<String, deal.types.Type> exports = modules.get(lib);
            return exports != null && exports.containsKey(functionName);
        }

        @Override
        public deal.types.Type resolveTypeNodeInModule(deal.ast.TypeNode typeNode,
                String modulePath, String importingModule) throws ModuleNotFoundException {
            return switch (typeNode) {
                case deal.ast.NamedType nt -> switch (nt.name()) {
                    case "null" -> deal.types.Type.Null.INSTANCE;
                    case "boolean" -> deal.types.Type.Boolean.INSTANCE;
                    case "int" -> deal.types.Type.Int.INSTANCE;
                    case "number" -> deal.types.Type.Number.INSTANCE;
                    case "string" -> deal.types.Type.String.INSTANCE;
                    case "table" -> deal.types.Type.Table.INSTANCE;
                    default -> IdentityTestFixtures.classType(nt.name(), modulePath);
                };
                case deal.ast.ArrayType at -> {
                    deal.types.Type elem = resolveTypeNodeInModule(at.elementType(),
                        modulePath, importingModule);
                    yield elem == deal.types.Type.Error.INSTANCE
                        ? deal.types.Type.Error.INSTANCE : deal.types.Types.array(elem);
                }
                case deal.ast.NullableType nt -> {
                    deal.types.Type inner = resolveTypeNodeInModule(nt.innerType(),
                        modulePath, importingModule);
                    yield inner == deal.types.Type.Error.INSTANCE
                        ? deal.types.Type.Error.INSTANCE
                        : deal.types.Types.nullable(inner);
                }
                default -> null;
            };
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Field Ops Lowering Tests (ISSUE-0513 K-D6/K-D7) ===\n");

        testFieldReadArm();
        testOptionalFieldReadArm();
        testCrossModuleNullableReadArm();
        testFieldWriteArm();
        testFieldDeleteArm();
        testHasFieldArm();
        testCombinedT1T2T3ExecutorDrive();
        testDeterminism();

        System.out.println("\nFieldOpsLoweringTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
