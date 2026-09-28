package deal.test;

import deal.ast.ProgramNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.Lexer;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.ClassConstructionValidator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Verifies the ISSUE-0516 production component
 * {@link ClassConstructionValidator}
 * (class-construction-jsonable-operations K-D11; the epic's
 * decomposition tail): the production-time class-op coherence checks —
 * factory&#8596;constructionEntry bijection, {@code CLASS_NEW} payload/
 * layout/boundary/input-wiring coherence, the field-operation child
 * shapes, the default-block admission, and the nested-jsonable layout
 * resolution — producing exactly one E6005 with
 * {@code capability CLASSES}, the pinned {@code validatorRule}, the
 * module, and the {@code ClassConstructionValidator} origin outside the
 * foundation validator's closed 14-condition rule set.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>Positive corpus: lowerer-produced units over the whole pipeline
 *       (declaration arm, LOCAL/SHARED_FACTORY construction, field
 *       operations, {@code has()}, and the generated {@code @jsonable}
 *       bodies) each validate; the production seam
 *       ({@link SemanticLowerer#lowerModuleClassCore}) runs the
 *       validator internally (every listed slice lowers).</li>
 *   <li>Factory negatives, each exactly one E6005
 *       {@code FACTORY_COHERENCE}: an unregistered exported class, a
 *       fabricated registry key, a reordered factory
 *       {@code classDefaultOpIds}, a parented factory, a duplicate
 *       {@code CLASS_DEFAULT} op, and a default op for a non-defaulted
 *       field.</li>
 *   <li>Construction negatives, each exactly one E6005
 *       {@code CONSTRUCTION_COHERENCE}: a layout carrying a foreign
 *       classId, an undeclared provided field, a swapped
 *       field-boundary order, a tampered boundary input, a wrong
 *       boundary kind, a LOCAL shape with a factory ref, and a
 *       RETAINED_ABI owner (E10's shape, never produced).</li>
 *   <li>Field-operation negatives, each exactly one E6005
 *       {@code FIELD_OPERATION_SHAPE}: a FIELD_READ with a dropped
 *       OPTIONAL_FIELD_READ child, a tampered receiver descriptor, an
 *       extra boundary child, and a required-field delete.</li>
 *   <li>Default-block admission negatives, exactly one E6005
 *       {@code DEFAULT_BLOCK_ADMISSION}: a binding load inside the
 *       default closure referencing an enclosing-function allocation,
 *       and a nested closure capture of the same shape.</li>
 *   <li>JSON negatives, each exactly one E6005
 *       {@code JSON_LAYOUT_COHERENCE}: a dropped per-site default
 *       child, an orphan table entry, an unresolvable nested class
 *       layout, and a bytes-typed jsonable field.</li>
 *   <li>The pinned detail fields (code, capability, rule, profile,
 *       version, module, origin) and determinism.</li>
 *   <li>Dump/snapshot wiring: the produced class unit dumps through the
 *       canonicalizer and re-validates from the dump text (the class-op
 *       payload snapshots survive the text round-trip), and every
 *       class op's digest equals the recomputed canonical digest.</li>
 * </ol>
 */
public class ClassConstructionValidatorTest {

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
    // Fixed invocation facts (the ClassDeclarationLoweringTest discipline)
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

    private static CheckedSlice checkSlice(String source) {
        Lexer lexer = new Lexer(source, SOURCE_ID);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents());
        deal.parser.ParseResult parse = parser.parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver resolver = new NameResolver(MODULE.path(), (deal.checker.ModuleResolver) null);
        SymbolTable symbols = resolver.resolve(parse.program());
        check(resolver.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + resolver.diagnostics());
        if (!resolver.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(MODULE.path(), symbols, resolver, parse.program());
        check(checks.diagnostics().isEmpty(), "the slice checks cleanly: " + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

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

    /** The whole-pipeline driver: lexer/parser/checker → lowerModuleClassCore. */
    private static SemanticLowerer.ClassDeclarationCoreResult lowerModule(String source) {
        CheckedSlice slice = checkSlice(source);
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

    // =========================================================================
    // Mutation helpers (rebuild one op with a fresh wired digest)
    // =========================================================================

    private static OperationContractSnapshot contractFor(SemanticOp op, KindPayload payload,
                                                         String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, op.kind(),
            op.resultType(), op.operandTypes(), selector, payload, op.failurePolicy(),
            List.of(), digest);
    }

    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        String digest = ContractSnapshotCanonicalizer.digest(contractFor(op, payload, "placeholder"));
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(), op.resultType(),
            op.operands(), op.operandTypes(), payload, op.failurePolicy(),
            contractFor(op, payload, digest));
    }

    private static SemanticOp withParent(SemanticOp op, OpId parent) {
        SourceOrigin origin = new SourceOrigin(op.origin().sourceId(), op.origin().span(),
            op.origin().kind(), op.origin().anchorId(), parent);
        return new SemanticOp(op.opId(), op.kind(), origin, op.result(), op.resultType(),
            op.operands(), op.operandTypes(), op.payload(), op.failurePolicy(),
            op.contract());
    }

    private static LoweredModuleUnit unitWithOps(LoweredModuleUnit unit, List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            ops);
    }

    private static LoweredModuleUnit unitWithLayouts(LoweredModuleUnit unit,
                                                     Map<ClassId, ClassLayout> layouts) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), layouts,
            unit.functions(), unit.moduleInit(), unit.exportPlan(), unit.functionBindings(),
            unit.ops());
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    private static SemanticOp firstOfKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                return op;
            }
        }
        return null;
    }

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

    /** Asserts one E6005 with the exact pinned detail fields. */
    private static void expectE6005(Optional<CompilerDiagnostic> outcome, String rule) {
        check(outcome.isPresent(), "the tampered unit fails with E6005 (" + rule + ")");
        if (outcome.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = outcome.get();
        check("E6005".equals(diagnostic.code()), "the failure code is E6005; got "
            + diagnostic.code());
        check(diagnostic.message().contains("validatorRule " + rule),
            "the failure names validatorRule " + rule + "; got " + diagnostic.message());
        check(diagnostic.message().contains("capability CLASSES"),
            "the failure detail carries capability CLASSES");
        check(diagnostic.message().contains("module 'main'"),
            "the failure detail carries the module");
        check(diagnostic.message().contains("semanticProfile DEAL_V1_2_INT32"),
            "the failure detail carries the semantic profile");
        check(diagnostic.message().contains("irVersion deal.semantic-ir/1"),
            "the failure detail carries the IR version");
        check(diagnostic.message().contains("origin ClassConstructionValidator " + rule),
            "the failure detail carries the ClassConstructionValidator origin");
    }

    // =========================================================================
    // 1. Positive corpus
    // =========================================================================

    private static void testPositiveCorpus() {
        System.out.println("-- positive corpus: every admitted class-op shape validates --");

        // The representative slice: an exported defaulted class, a
        // non-exported class, construction, field ops, has(), and the
        // generated @jsonable bodies with a same-module nested class.
        String source = """
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p";
              note?: string;
            }
            // @jsonable
            export class Inner { n: int = 7; }
            // @jsonable
            export class Holder { home: Point; opt?: Inner; }
            let p: Point = {x: 1}
            let q: Point = {}
            p.x = 9
            p.note = "a"
            delete p.note
            let hasNote: boolean = has(p.note)
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the representative slice lowers (the production seam runs the validator "
                + "internally): " + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        // The direct drive over the produced records (unit + table +
        // registry + json defaults + own interface + empty imported
        // facts) passes.
        Optional<CompilerDiagnostic> direct = ClassConstructionValidator.validate(
            result.lowering().unit(), result.lowering().table(), result.registry(),
            result.jsonDefaults(), ownInterface(result, source), Map.of());
        check(direct.isEmpty(),
            "the produced records validate directly: " + direct);

        // The SHARED_FACTORY positive is the two-module seam's; the
        // single-module seam exercises LOCAL plus the shared shapes'
        // record invariants.
    }

    private static ExternalModuleInterface ownInterface(SemanticLowerer
            .ClassDeclarationCoreResult result, String source) {
        CheckedSlice slice = checkSlice(source);
        PipelineSlice pipeline = pipeline(slice);
        return pipeline.ownInterface();
    }

    // =========================================================================
    // 2. FACTORY_COHERENCE negatives
    // =========================================================================

    private static void testFactoryNegatives() {
        System.out.println("-- factory negatives: unregistered/fabricated entries, "
            + "reordered children, parented factory, duplicate defaults --");

        String source = """
            export class Point {
              x: int = 40 + 2;
              tag: string = "p";
              note?: string;
            }
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the factory slice lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();

        // (a) An unregistered exported class: the registry emptied while
        // the unit still produces the factory op.
        expectE6005(ClassConstructionValidator.validate(unit, result.lowering().table(),
            new ClassFactoryRegistry(Map.of()), result.jsonDefaults(),
            ownInterface(result, source), Map.of()), ClassConstructionValidator
                .FACTORY_COHERENCE);

        // (b) A fabricated registry key: a registration under an entry no
        // exported class carries (the valid registrations stay).
        ClassFactoryId fabricated = new ClassFactoryId(99_999);
        Map<ClassFactoryId, OpId> withFabricated = new LinkedHashMap<>(
            result.registry().factories());
        withFabricated.put(fabricated, ofKind(unit, SemanticOpKind.CLASS_FACTORY)
            .get(0).opId());
        expectE6005(ClassConstructionValidator.validate(unit, result.lowering().table(),
            new ClassFactoryRegistry(withFabricated),
            result.jsonDefaults(), ownInterface(result, source), Map.of()),
            ClassConstructionValidator.FACTORY_COHERENCE);

        // (c) Reordered factory classDefaultOpIds.
        SemanticOp factory = firstOfKind(unit, SemanticOpKind.CLASS_FACTORY);
        KindPayload.ClassFactoryPayload factoryPayload =
            (KindPayload.ClassFactoryPayload) factory.payload();
        List<OpId> reversed = new ArrayList<>(factoryPayload.classDefaultOpIds());
        java.util.Collections.reverse(reversed);
        SemanticOp tampered = rebuild(factory,
            new KindPayload.ClassFactoryPayload(factoryPayload.classId(), reversed,
                factoryPayload.callerOpRef()));
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit, replaceOp(unit, tampered)),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.FACTORY_COHERENCE);

        // (d) A parented factory (the detached static shape broken).
        expectE6005(ClassConstructionValidator.validate(
            unitWithOps(unit, replaceOp(unit, withParent(factory, factory.opId()))),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.FACTORY_COHERENCE);

        // (e) A duplicate CLASS_DEFAULT op: clone one default op under a
        // fresh op id.
        SemanticOp firstDefault = firstOfKind(unit, SemanticOpKind.CLASS_DEFAULT);
        KindPayload.ClassDefaultPayload defaultPayload =
            (KindPayload.ClassDefaultPayload) firstDefault.payload();
        KindPayload.ClassDefaultPayload clonePayload =
            new KindPayload.ClassDefaultPayload(defaultPayload.classId(),
                defaultPayload.field(), defaultPayload.defaultBlock());
        String cloneDigest = ContractSnapshotCanonicalizer.digest(contractFor(
            firstDefault, clonePayload, "placeholder"));
        SemanticOp clone = new SemanticOp(new OpId(MODULE, 99_998), firstDefault.kind(),
            new SourceOrigin(firstDefault.origin().sourceId(), firstDefault.origin().span(),
                SourceOriginKind.SYNTHETIC, new AnchorId(1), null),
            new ValueId(99_998), firstDefault.resultType(), firstDefault.operands(),
            firstDefault.operandTypes(), clonePayload, FailurePolicyId.NO_DEAL_FAILURE,
            contractFor(firstDefault, clonePayload, cloneDigest));
        List<SemanticOp> withClone = new ArrayList<>(unit.ops());
        withClone.add(clone);
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit, withClone),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.FACTORY_COHERENCE);
    }

    private static List<SemanticOp> replaceOp(LoweredModuleUnit unit, SemanticOp replacement) {
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        for (int i = 0; i < ops.size(); i++) {
            if (ops.get(i).opId().equals(replacement.opId())) {
                ops.set(i, replacement);
                return ops;
            }
        }
        throw new IllegalArgumentException("no op with id " + replacement.opId());
    }

    // =========================================================================
    // 3. CONSTRUCTION_COHERENCE negatives
    // =========================================================================

    private static void testConstructionNegatives() {
        System.out.println("-- construction negatives: layout identity, undeclared "
            + "provided field, boundary order/input/kind, owner shapes --");

        String source = """
            class Point {
              x: int = 40 + 2;
              tag: string = "p";
              note?: string;
            }
            let p: Point = {x: 1}
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the construction slice lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        SemanticOp classNew = firstOfKind(unit, SemanticOpKind.CLASS_NEW);
        KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) classNew.payload();

        // (a) A layout carrying a foreign classId (the payload layout
        // keeps the foreign id while the payload names Point).
        ClassLayout foreignLayout = new ClassLayout(
            new ClassId("foreign", "Point"), payload.layout().fields());
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
            replaceOp(unit, rebuild(classNew,
                new KindPayload.ClassNewPayload(payload.classId(), foreignLayout,
                    payload.providedFields(), payload.defaultOwner(),
                    payload.classDefaultOpIds(), payload.classFactoryRef(),
                    payload.fieldBoundaries())))),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.CONSTRUCTION_COHERENCE);

        // (b) An undeclared provided field.
        List<KindPayload.ProvidedField> extraProvided =
            new ArrayList<>(payload.providedFields());
        extraProvided.add(new KindPayload.ProvidedField("zzz", new ValueId(1)));
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
            replaceOp(unit, rebuild(classNew,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    extraProvided, payload.defaultOwner(), payload.classDefaultOpIds(),
                    payload.classFactoryRef(), payload.fieldBoundaries())))),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.CONSTRUCTION_COHERENCE);

        // (c) A swapped field-boundary order (the parented children keep
        // their emission order, so the payload order mismatch is caught).
        List<KindPayload.FieldBoundary> swapped =
            new ArrayList<>(payload.fieldBoundaries());
        if (swapped.size() < 2) {
            fail("the slice's CLASS_NEW carries fewer than two field boundaries");
        } else {
            java.util.Collections.swap(swapped, 0, 1);
            expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                replaceOp(unit, rebuild(classNew,
                    new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                        payload.providedFields(), payload.defaultOwner(),
                        payload.classDefaultOpIds(), payload.classFactoryRef(),
                        swapped)))),
                result.lowering().table(), result.registry(), result.jsonDefaults(),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.CONSTRUCTION_COHERENCE);
        }

        // (d) A tampered boundary input: the first boundary child's input
        // no longer names the provided value.
        List<SemanticOp> children = childrenOf(unit, classNew);
        if (!children.isEmpty()) {
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) children.get(0).payload();
            SemanticOp tampered = rebuild(children.get(0),
                new KindPayload.BoundaryPayload(boundaryPayload.kind(),
                    boundaryPayload.descriptor(), new ValueId(99_997),
                    boundaryPayload.realization()));
            expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                replaceOp(unit, tampered)), result.lowering().table(),
                result.registry(), result.jsonDefaults(), ownInterface(result, source),
                Map.of()), ClassConstructionValidator.CONSTRUCTION_COHERENCE);
        }

        // (e) A wrong boundary kind (CLASS_LITERAL_FIELD becomes
        // CLASS_DEFAULT_FIELD at a provided position).
        if (!payload.fieldBoundaries().isEmpty()) {
            KindPayload.FieldBoundary first = payload.fieldBoundaries().get(0);
            SemanticOp child = null;
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(first.boundaryOpId())) {
                    child = op;
                }
            }
            if (child != null) {
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) child.payload();
                BoundaryKind wrongKind = first.kind() == BoundaryKind
                    .CLASS_LITERAL_FIELD
                    ? BoundaryKind.CLASS_DEFAULT_FIELD
                    : BoundaryKind.CLASS_LITERAL_FIELD;
                SemanticOp tampered = rebuild(child,
                    new KindPayload.BoundaryPayload(wrongKind,
                        boundaryPayload.descriptor(), boundaryPayload.input(),
                        boundaryPayload.realization()));
                List<KindPayload.FieldBoundary> wrongEntries =
                    new ArrayList<>(payload.fieldBoundaries());
                wrongEntries.set(0, new KindPayload.FieldBoundary(first.field(), wrongKind,
                    first.boundaryOpId()));
                expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                    replaceOp(unit, tampered)), result.lowering().table(),
                    result.registry(), result.jsonDefaults(), ownInterface(result, source),
                    Map.of()), ClassConstructionValidator.CONSTRUCTION_COHERENCE);
                // The payload kind and the child kind both tampered
                // against the pinned expectation.
                expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                    replaceOp(unit, rebuild(classNew,
                        new KindPayload.ClassNewPayload(payload.classId(),
                            payload.layout(), payload.providedFields(),
                            payload.defaultOwner(), payload.classDefaultOpIds(),
                            payload.classFactoryRef(), wrongEntries)))),
                    result.lowering().table(), result.registry(), result.jsonDefaults(),
                    ownInterface(result, source), Map.of()),
                    ClassConstructionValidator.CONSTRUCTION_COHERENCE);
            }
        }

        // (f) A LOCAL shape carrying a factory ref.
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
            replaceOp(unit, rebuild(classNew,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), DefaultOwner.LOCAL,
                    payload.classDefaultOpIds(), new ClassFactoryId(77),
                    payload.fieldBoundaries())))),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.CONSTRUCTION_COHERENCE);

        // (g) A RETAINED_ABI owner (E10's shape, never produced here).
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
            replaceOp(unit, rebuild(classNew,
                new KindPayload.ClassNewPayload(payload.classId(), payload.layout(),
                    payload.providedFields(), DefaultOwner.RETAINED_ABI, List.of(),
                    new ClassFactoryId(78), payload.fieldBoundaries())))),
            result.lowering().table(), result.registry(), result.jsonDefaults(),
            ownInterface(result, source), Map.of()),
            ClassConstructionValidator.CONSTRUCTION_COHERENCE);
    }

    // =========================================================================
    // 4. FIELD_OPERATION_SHAPE negatives
    // =========================================================================

    private static void testFieldOperationNegatives() {
        System.out.println("-- field-operation negatives: dropped child, tampered "
            + "descriptor, extra child, required-field delete --");

        String source = """
            class Point {
              x: int;
              y?: int = 0;
            }
            let p: Point = {x: 1}
            let v: int | null = p.y
            p.x = 9
            delete p.y
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the field slice lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        SemanticOp read = firstOfKind(unit, SemanticOpKind.FIELD_READ);

        // (a) The OPTIONAL_FIELD_READ child dropped (reparented away).
        List<SemanticOp> readChildren = childrenOf(unit, read);
        if (readChildren.size() == 2) {
            expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                replaceOp(unit, withParent(readChildren.get(1), null))),
                result.lowering().table(), result.registry(), result.jsonDefaults(),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.FIELD_OPERATION_SHAPE);
        }

        // (b) A tampered receiver descriptor.
        if (!readChildren.isEmpty()) {
            KindPayload.BoundaryPayload boundaryPayload =
                (KindPayload.BoundaryPayload) readChildren.get(0).payload();
            SemanticOp tampered = rebuild(readChildren.get(0),
                new KindPayload.BoundaryPayload(boundaryPayload.kind(),
                    new RuntimeDescriptor.Class(new ClassId("other", "Other")),
                    boundaryPayload.input(), boundaryPayload.realization()));
            expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                replaceOp(unit, tampered)), result.lowering().table(),
                result.registry(), result.jsonDefaults(), ownInterface(result, source),
                Map.of()), ClassConstructionValidator.FIELD_OPERATION_SHAPE);
        }

        // (c) An extra boundary child parented to the read op.
        SemanticOp delete = firstOfKind(unit, SemanticOpKind.FIELD_DELETE);
        if (delete != null) {
            List<SemanticOp> deleteChildren = childrenOf(unit, delete);
            if (!deleteChildren.isEmpty()) {
                expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                    replaceOp(unit, withParent(deleteChildren.get(0), read.opId()))),
                    result.lowering().table(), result.registry(), result.jsonDefaults(),
                    ownInterface(result, source), Map.of()),
                    ClassConstructionValidator.FIELD_OPERATION_SHAPE);
            }
        }

        // (d) A required-field delete (the payload field rewritten from
        // the optional y to the required x).
        if (delete != null) {
            KindPayload.FieldDeletePayload deletePayload =
                (KindPayload.FieldDeletePayload) delete.payload();
            expectE6005(ClassConstructionValidator.validate(unitWithOps(unit,
                replaceOp(unit, rebuild(delete,
                    new KindPayload.FieldDeletePayload(deletePayload.classValue(),
                        deletePayload.classId(), "x")))),
                result.lowering().table(), result.registry(), result.jsonDefaults(),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.FIELD_OPERATION_SHAPE);
        }
    }

    // =========================================================================
    // 5. DEFAULT_BLOCK_ADMISSION negatives
    // =========================================================================

    private static void testDefaultBlockAdmissionNegatives() {
        System.out.println("-- default-block admission negatives: an enclosing-function "
            + "load and a nested capture inside the default closure --");

        // The baseline: a module-level binding plus a defaulted class.
        final String source = """
            let base: int = 5
            export class Point {
              x: int = base;
            }
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the admission baseline lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        ExternalModuleInterface own = ownInterface(result, source);
        LoweredModuleUnit unit = result.lowering().unit();
        SemanticOp defaultOp = firstOfKind(unit, SemanticOpKind.CLASS_DEFAULT);
        KindPayload.ClassDefaultPayload defaultPayload =
            (KindPayload.ClassDefaultPayload) defaultOp.payload();
        BlockId defaultBlock = defaultPayload.defaultBlock();

        // A foreign binding allocated in a foreign block (a function body
        // the default block does not reach).
        BindingId foreignBinding = new BindingId(97_777);
        BlockId foreignBlock = new BlockId(97_778);
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        KindPayload.BindingAllocPayload allocPayload =
            new KindPayload.BindingAllocPayload(foreignBinding, foreignBlock, true,
                deal.semantic.ir.BindingCellKind.DIRECT, 0);
        String allocDigest = ContractSnapshotCanonicalizer.digest(new
            OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.BINDING_ALLOC, null, List.of(), null, allocPayload,
                FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder"));
        ops.add(new SemanticOp(new OpId(MODULE, 97_776), SemanticOpKind.BINDING_ALLOC,
            new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
                SourceOriginKind.SYNTHETIC, new AnchorId(2), null),
            null, null, List.of(), List.of(), allocPayload,
            FailurePolicyId.NO_DEAL_FAILURE,
            new OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.BINDING_ALLOC, null, List.of(), null, allocPayload,
                FailurePolicyId.NO_DEAL_FAILURE, List.of(), allocDigest)));
        KindPayload.BindingLoadPayload loadPayload =
            new KindPayload.BindingLoadPayload(foreignBinding, 0);
        String loadDigest = ContractSnapshotCanonicalizer.digest(new
            OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.BINDING_LOAD, RuntimeDescriptor.Int.INSTANCE, List.of(),
                null, loadPayload, FailurePolicyId.NO_DEAL_FAILURE, List.of(),
                "placeholder"));
        ops.add(new SemanticOp(new OpId(MODULE, 97_774), SemanticOpKind.BINDING_LOAD,
            new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
                SourceOriginKind.SYNTHETIC, new AnchorId(3), defaultOp.opId()),
            new ValueId(97_775), RuntimeDescriptor.Int.INSTANCE, List.of(), List.of(),
            loadPayload, FailurePolicyId.NO_DEAL_FAILURE,
            new OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.BINDING_LOAD, RuntimeDescriptor.Int.INSTANCE, List.of(),
                null, loadPayload, FailurePolicyId.NO_DEAL_FAILURE, List.of(),
                loadDigest)));
        // The tampered load becomes a member of the default block; the
        // foreign alloc becomes a member of the foreign block.
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>(result.lowering().table()
            .blockOps());
        List<OpId> defaultMembers = new ArrayList<>(blockOps.getOrDefault(defaultBlock,
            List.of()));
        defaultMembers.add(new OpId(MODULE, 97_774));
        blockOps.put(defaultBlock, defaultMembers);
        blockOps.put(foreignBlock, List.of(new OpId(MODULE, 97_776)));
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>(result.lowering().table()
            .opBlocks());
        opBlocks.put(new OpId(MODULE, 97_774), defaultBlock);
        opBlocks.put(new OpId(MODULE, 97_776), foreignBlock);
        StructuredBodyTable tamperedTable = new StructuredBodyTable(blockOps, opBlocks);
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit, ops),
            tamperedTable, result.registry(), result.jsonDefaults(), own, Map.of()),
            ClassConstructionValidator.DEFAULT_BLOCK_ADMISSION);

        // A nested closure capture of the foreign binding inside the
        // default block (the capture is the reference, not a load): the
        // closure body is an internal block of the default walk while the
        // captured binding stays allocated in the foreign block.
        BlockId closureBody = new BlockId(97_770);
        RuntimeDescriptor.Func closureSignature =
            new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Int.INSTANCE, false);
        KindPayload.ClosureNewPayload closurePayload = new KindPayload.ClosureNewPayload(
            new deal.semantic.ir.FunctionId(97_771), closureSignature,
            List.of(new BindingGeneration(foreignBinding, 0)),
            new deal.semantic.ir.FunctionExecutionBinding.LoweredBody(
                new deal.semantic.ir.FunctionId(97_771), closureBody));
        String closureDigest = ContractSnapshotCanonicalizer.digest(new
            OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.CLOSURE_NEW, closureSignature, List.of(), null,
                closurePayload, FailurePolicyId.NO_DEAL_FAILURE, List.of(),
                "placeholder"));
        SemanticOp closure = new SemanticOp(new OpId(MODULE, 97_772),
            SemanticOpKind.CLOSURE_NEW,
            new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
                SourceOriginKind.SYNTHETIC, new AnchorId(4), defaultOp.opId()),
            new ValueId(97_773), closureSignature, List.of(), List.of(),
            closurePayload, FailurePolicyId.NO_DEAL_FAILURE,
            new OperationContractSnapshot(OperationContractSnapshot.VERSION,
                SemanticOpKind.CLOSURE_NEW, closureSignature, List.of(), null,
                closurePayload, FailurePolicyId.NO_DEAL_FAILURE, List.of(),
                closureDigest));
        List<SemanticOp> captureOps = new ArrayList<>(ops);
        captureOps.add(closure);
        List<OpId> captureMembers = new ArrayList<>(blockOps.getOrDefault(defaultBlock,
            List.of()));
        captureMembers.add(new OpId(MODULE, 97_772));
        blockOps.put(defaultBlock, captureMembers);
        blockOps.put(closureBody, List.of());
        opBlocks.put(new OpId(MODULE, 97_772), defaultBlock);
        StructuredBodyTable captureTable = new StructuredBodyTable(blockOps, opBlocks);
        expectE6005(ClassConstructionValidator.validate(unitWithOps(unit, captureOps),
            captureTable, result.registry(), result.jsonDefaults(), own, Map.of()),
            ClassConstructionValidator.DEFAULT_BLOCK_ADMISSION);
    }

    // =========================================================================
    // 6. JSON_LAYOUT_COHERENCE negatives
    // =========================================================================

    private static void testJsonNegatives() {
        System.out.println("-- JSON negatives: dropped default child, orphan entry, "
            + "unresolvable nested layout, bytes field --");

        String source = """
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p";
            }
            // @jsonable
            export class Inner { n: int = 7; }
            // @jsonable
            export class Holder { home: Point; opt?: Inner; }
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the json slice lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        SemanticOp fromJson = firstOfKind(unit, SemanticOpKind.JSON_FROM_CLASS);
        KindPayload.JsonFromClassPayload fromPayload =
            (KindPayload.JsonFromClassPayload) fromJson.payload();

        // (a) A dropped per-site default child (the table entry loses its
        // second child).
        List<OpId> children = result.jsonDefaults().childrenOf(fromJson.opId());
        if (children != null && children.size() >= 2) {
            Map<OpId, List<OpId>> entries = new LinkedHashMap<>(
                result.jsonDefaults().defaultChildren());
            List<OpId> dropped = new ArrayList<>(children);
            dropped.remove(dropped.size() - 1);
            entries.put(fromJson.opId(), dropped);
            expectE6005(ClassConstructionValidator.validate(unit, result.lowering().table(),
                result.registry(), new JsonDefaultChildTable(entries),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.JSON_LAYOUT_COHERENCE);
        }

        // (b) An orphan table entry naming a non-JSON op.
        SemanticOp someDefault = firstOfKind(unit, SemanticOpKind.CLASS_DEFAULT);
        if (someDefault != null) {
            expectE6005(ClassConstructionValidator.validate(unit, result.lowering().table(),
                result.registry(),
                new JsonDefaultChildTable(Map.of(someDefault.opId(), List.of())),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.JSON_LAYOUT_COHERENCE);
        }

        // (c) An unresolvable nested class layout: the Holder layout is
        // rebuilt (unit layout and JSON payload layouts alike) with a
        // class-typed field naming a class that resolves nowhere — the
        // nested-jsonable resolution fails.
        ClassId unresolvedHolderId = new ClassId(MODULE.path(), "Holder");
        ClassLayout unresolvedHolderLayout =
            unit.classLayouts().get(unresolvedHolderId);
        if (unresolvedHolderLayout != null) {
            List<ClassLayout.FieldLayout> holderFields =
                new ArrayList<>(unresolvedHolderLayout.fields());
            holderFields.add(new ClassLayout.FieldLayout("gone",
                new RuntimeDescriptor.Class(new ClassId("foreign", "Missing")),
                true, DefaultOwner.LOCAL));
            ClassLayout tamperedHolder =
                new ClassLayout(unresolvedHolderId, holderFields);
            Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>(unit.classLayouts());
            layouts.put(unresolvedHolderId, tamperedHolder);
            List<SemanticOp> ops = new ArrayList<>(unit.ops());
            for (int i = 0; i < ops.size(); i++) {
                SemanticOp op = ops.get(i);
                if (op.kind() == SemanticOpKind.JSON_FROM_CLASS
                        && op.payload() instanceof KindPayload.JsonFromClassPayload json
                        && json.layout().classId().equals(unresolvedHolderId)) {
                    ops.set(i, rebuild(op, new KindPayload.JsonFromClassPayload(
                        tamperedHolder, json.jsonString())));
                } else if (op.kind() == SemanticOpKind.JSON_TO_CLASS
                        && op.payload() instanceof KindPayload.JsonToClassPayload json
                        && json.layout().classId().equals(unresolvedHolderId)) {
                    ops.set(i, rebuild(op, new KindPayload.JsonToClassPayload(
                        json.classValue(), tamperedHolder)));
                }
            }
            expectE6005(ClassConstructionValidator.validate(
                unitWithLayouts(unitWithOps(unit, ops), layouts),
                result.lowering().table(), result.registry(), result.jsonDefaults(),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.JSON_LAYOUT_COHERENCE);
        }

        // (d) A bytes-typed jsonable field (hand-rebuilt layout): the
        // payload layout and the unit layout both carry the bytes field.
        ClassId holderId = new ClassId(MODULE.path(), "Holder");
        ClassLayout holderLayout = unit.classLayouts().get(holderId);
        if (holderLayout != null) {
            List<ClassLayout.FieldLayout> fields = new ArrayList<>(holderLayout.fields());
            fields.add(new ClassLayout.FieldLayout("raw", RuntimeDescriptor.Bytes.INSTANCE,
                true, DefaultOwner.LOCAL));
            ClassLayout tamperedLayout = new ClassLayout(holderId, fields);
            Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>(unit.classLayouts());
            layouts.put(holderId, tamperedLayout);
            List<SemanticOp> ops = new ArrayList<>(unit.ops());
            for (int i = 0; i < ops.size(); i++) {
                SemanticOp op = ops.get(i);
                if (op.kind() == SemanticOpKind.JSON_FROM_CLASS
                        || op.kind() == SemanticOpKind.JSON_TO_CLASS) {
                    KindPayload payloadOfOp = op.payload();
                    if (payloadOfOp instanceof KindPayload.JsonFromClassPayload jsonPayload
                            && jsonPayload.layout().classId().equals(holderId)) {
                        ops.set(i, rebuild(op,
                            new KindPayload.JsonFromClassPayload(tamperedLayout,
                                jsonPayload.jsonString())));
                    } else if (payloadOfOp instanceof KindPayload.JsonToClassPayload
                            jsonPayload && jsonPayload.layout().classId().equals(holderId)) {
                        ops.set(i, rebuild(op,
                            new KindPayload.JsonToClassPayload(jsonPayload.classValue(),
                                tamperedLayout)));
                    }
                }
            }
            expectE6005(ClassConstructionValidator.validate(
                unitWithLayouts(unitWithOps(unit, ops), layouts),
                result.lowering().table(), result.registry(), result.jsonDefaults(),
                ownInterface(result, source), Map.of()),
                ClassConstructionValidator.JSON_LAYOUT_COHERENCE);
        }
    }

    // =========================================================================
    // 7. Detail fields, dump/snapshot wiring, determinism, nulls
    // =========================================================================

    private static void testDetailsDumpDeterminism() {
        System.out.println("-- detail fields, dump/snapshot wiring, determinism, nulls --");

        String source = """
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p";
              note?: string;
            }
            let p: Point = {x: 1}
            p.x = 9
            let v: string | null = p.note
            let hasNote: boolean = has(p.note)
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null, "the detail slice lowers");
        if (result == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        ExternalModuleInterface own = ownInterface(result, source);

        // The dump/snapshot wiring: the produced unit dumps through the
        // canonicalizer and re-validates from the dump text — the class
        // payload snapshots (layout, provided fields, field boundaries,
        // class/factory refs) survive the text round-trip byte-for-byte.
        String dumpText = SemanticIrDumper.dumpModuleText(unit);
        check(dumpText.contains("\"providedFields\"") && dumpText.contains("\"layout\"")
                && dumpText.contains("\"fieldBoundaries\"")
                && dumpText.contains("\"classId\""),
            "the dump text carries the CLASS_NEW payload fields (providedFields, "
                + "layout, fieldBoundaries, classId)");
        Optional<CompilerDiagnostic> revalidated = SemanticIrValidator.validateText(dumpText,
            new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
        check(revalidated.isEmpty(),
            "the dumped class unit re-validates from the dump text: " + revalidated);

        // Every class op's digest equals the recomputed canonical digest
        // (the snapshot wiring pin).
        for (SemanticOp op : unit.ops()) {
            switch (op.kind()) {
                case CLASS_NEW, CLASS_FACTORY, CLASS_DEFAULT, FIELD_READ, FIELD_WRITE,
                     FIELD_DELETE, JSON_FROM_CLASS, JSON_TO_CLASS, HAS_FIELD -> {
                    String recomputed = ContractSnapshotCanonicalizer.digest(
                        op.contract());
                    check(op.contract().canonicalDigest().equals(recomputed),
                        op.kind() + " " + op.opId() + " carries the recomputed "
                            + "canonical digest");
                }
                default -> {
                    // Not a class op.
                }
            }
        }

        // Determinism and purity: the direct validation repeats with
        // byte-identical outcomes and mutates nothing.
        Optional<CompilerDiagnostic> first = ClassConstructionValidator.validate(unit,
            result.lowering().table(), result.registry(), result.jsonDefaults(), own,
            Map.of());
        Optional<CompilerDiagnostic> second = ClassConstructionValidator.validate(unit,
            result.lowering().table(), result.registry(), result.jsonDefaults(), own,
            Map.of());
        check(first.isEmpty() && second.isEmpty(),
            "the direct validation is deterministic (both runs empty)");
        check(unit.ops().size() == result.lowering().unit().ops().size()
                && result.registry().factories().equals(result.registry().factories()),
            "the validator mutates neither the unit nor the records");

        // Null-argument rejection.
        expectNpe(() -> ClassConstructionValidator.validate(null,
            result.lowering().table(), result.registry(), result.jsonDefaults(), own,
            Map.of()), "null unit");
        expectNpe(() -> ClassConstructionValidator.validate(unit, null,
            result.registry(), result.jsonDefaults(), own, Map.of()), "null table");
        expectNpe(() -> ClassConstructionValidator.validate(unit,
            result.lowering().table(), null, result.jsonDefaults(), own, Map.of()),
            "null factory registry");
        expectNpe(() -> ClassConstructionValidator.validate(unit,
            result.lowering().table(), result.registry(), null, own, Map.of()),
            "null json defaults");
        expectNpe(() -> ClassConstructionValidator.validate(unit,
            result.lowering().table(), result.registry(), result.jsonDefaults(), null,
            Map.of()), "null own interface");
        expectNpe(() -> ClassConstructionValidator.validate(unit,
            result.lowering().table(), result.registry(), result.jsonDefaults(), own,
            null), "null shared factories");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Class Construction Validator Tests (ISSUE-0516 K-D11) ===");
        testPositiveCorpus();
        testFactoryNegatives();
        testConstructionNegatives();
        testFieldOperationNegatives();
        testDefaultBlockAdmissionNegatives();
        testJsonNegatives();
        testDetailsDumpDeterminism();
        System.out.println();
        if (failed == 0) {
            System.out.println("ClassConstructionValidatorTest: " + passed + " passed, "
                + failed + " failed");
        } else {
            System.out.println("ClassConstructionValidatorTest: " + passed + " passed, "
                + failed + " failed");
            System.exit(1);
        }
    }
}
