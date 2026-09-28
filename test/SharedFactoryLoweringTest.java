package deal.test;

import deal.ast.ClassDeclaration;
import deal.ast.ExportDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
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
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ClassOpsExecutor.BodyRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryResult;
import deal.semantic.ir.ClassOpsExecutor.FieldState;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Verifies the ISSUE-0514 {@code CLASS_NEW(SHARED_FACTORY)} lowering arm
 * and the {@code CLASS_FACTORY} execution contract
 * (class-construction-jsonable-operations K-D2/K-D4/K-D5; parent D16):
 * the imported-construction slice — an object literal typed as a class
 * declared in another module lowers to exactly one {@code CLASS_NEW}
 * with {@code defaultOwner: SHARED_FACTORY}, {@code classFactoryRef} =
 * the imported class's {@code ClassInterface.constructionEntry} (the
 * pre-allocated route-independent {@link ClassFactoryId}), empty
 * {@code classDefaultOpIds}, {@code providedFields} in literal order,
 * and {@code fieldBoundaries} in declaration order —
 * {@code CLASS_LITERAL_FIELD} per provided field (input = the field's
 * {@code valueOpId}) plus {@code CLASS_DEFAULT_FIELD} per omitted
 * defaulted field with input = the owner {@code CLASS_FACTORY} op's
 * result {@code ValueId} (the K-D4 cross-unit D4-global reference) —
 * driven through the extended two-module seam
 * ({@link SemanticLowerer#lowerModuleClassCore} with the
 * {@link SharedFactoryFacts} context) and the executor's cross-unit
 * transfer.
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>the pinned SHARED_FACTORY payloads ({@code defaultOwner},
 *       {@code classFactoryRef} = the interface {@code constructionEntry},
 *       empty {@code classDefaultOpIds}, {@code fieldBoundaries} in
 *       declaration order with the factory-result input wiring);</li>
 *   <li>provided-field operand order equals literal order across the
 *       module boundary (the eval-order pin shape — the caller unit's
 *       producing ops precede the {@code CLASS_NEW} in literal order);</li>
 *   <li>the combined T1+T2+T3+T4 scenario — two checked modules (an
 *       owner exporting a defaulted class; a caller importing and
 *       constructing empty/partial/full literals plus field reads and
 *       {@code has()}) lowered through the extended seam to validated
 *       units, then the executor drives the cross-unit construction
 *       end-to-end: defaults filled by the owner's factory in the
 *       declaring module's scope, provided fields reordered to
 *       declaration order, both {@code jvm-xmod-class-construction-*}
 *       pin shapes reproduced at the unit level (this scenario fails if
 *       T1's factory/registry, T2's {@code CLASS_NEW}, or T3's
 *       field/presence model breaks);</li>
 *   <li>the RETAINED_ABI deferral negative (an owner-route mismatch
 *       defers to E10, never emits);</li>
 *   <li>same-module literals stay LOCAL (T2's arm) even when the
 *       shared-factory facts exist;</li>
 *   <li>determinism — two repetitions byte-identical.</li>
 * </ol>
 */
public class SharedFactoryLoweringTest {

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
    // Fixed invocation facts (two cross-unit modules)
    // =========================================================================

    private static final ModuleId OWNER = new ModuleId("owner");
    private static final ModuleId CALLER = new ModuleId("main");
    private static final String OWNER_SOURCE_ID = "owner.deal";
    private static final String CALLER_SOURCE_ID = "caller.deal";
    private static final String IMPORT_SPECIFIER = "owner";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record ProjectFacts(ProjectInterfaceIndex index, String interfaceHash,
                                Map<ModuleId, Map<ConstructKind, List<SemanticOpKind>>>
                                    coverages) {
    }

    private record LoweredPair(
        SemanticLowerer.ClassDeclarationCoreResult owner,
        SemanticLowerer.ClassDeclarationCoreResult caller,
        ProjectFacts project,
        Map<ClassId, SharedFactoryFacts> facts) {
    }

    // =========================================================================
    // Whole-pipeline helpers (two checked modules -> lowerModuleClassCore)
    // =========================================================================

    private static CheckedSlice checkSlice(String source, ModuleId moduleId,
                                           ModuleResolver resolver) {
        String sourceId = moduleId.path() + ".deal";
        Lexer lexer = new Lexer(source, sourceId);
        deal.lexer.LexResult lex = lexer.tokenize();
        Parser parser = new Parser(lex.tokens(), sourceId);
        deal.parser.ParseResult parse = parser.parse();
        check(parse.diagnostics().isEmpty(), "the slice parses cleanly: " + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver names = new NameResolver(moduleId.path(), resolver);
        SymbolTable symbols = names.resolve(parse.program());
        check(names.diagnostics().isEmpty(),
            "the slice resolves cleanly: " + names.diagnostics());
        if (!names.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(moduleId.path(), symbols, names,
            parse.program());
        check(checks.diagnostics().isEmpty(),
            "the slice checks cleanly: " + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symbols, checks);
    }

    /** The owner's Phase-3-corrected export map (the orchestrator's derivation). */
    private static Map<String, Type> ownerExports(CheckedSlice owner) {
        Map<String, Type> exports = new LinkedHashMap<>();
        for (StatementNode stmt : owner.program().statements()) {
            if (stmt instanceof ExportDeclaration exp
                    && exp.declaration() instanceof ClassDeclaration cd) {
                Symbol sym = owner.symbols().resolve(cd.name());
                if (sym instanceof Symbol.ClassSymbol cs) {
                    exports.put(cd.name(), Types.classType(cs.name(), cs.identity()));
                }
            }
        }
        return exports;
    }

    /** The owner's checked class symbols by simple name. */
    private static Map<String, Symbol.ClassSymbol> ownerClassSymbols(CheckedSlice owner) {
        Map<String, Symbol.ClassSymbol> symbols = new LinkedHashMap<>();
        for (StatementNode stmt : owner.program().statements()) {
            StatementNode declaration = stmt instanceof ExportDeclaration exp
                ? exp.declaration() : stmt;
            if (declaration instanceof ClassDeclaration cd) {
                Symbol sym = owner.symbols().resolve(cd.name());
                if (sym instanceof Symbol.ClassSymbol cs) {
                    symbols.put(cd.name(), cs);
                }
            }
        }
        return symbols;
    }

    /**
     * The caller's stub module resolver: the owner's exports and class
     * symbols routed by the module path and by the carried canonical
     * module identity (the identity-keyed seam the checker consults).
     */
    private static final class OwnerResolver implements ModuleResolver {

        private final Map<String, Type> exports;
        private final Map<String, Symbol.ClassSymbol> classSymbols;

        OwnerResolver(CheckedSlice owner) {
            this.exports = ownerExports(owner);
            this.classSymbols = ownerClassSymbols(owner);
        }

        @Override
        public Map<String, Type> resolveModule(String modulePath, String importingModule,
                                               Set<String> modulesInProgress)
                throws ModuleNotFoundException {
            if (IMPORT_SPECIFIER.equals(modulePath)) {
                return exports;
            }
            throw new ModuleNotFoundException("Module not found: " + modulePath);
        }

        @Override
        public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                                                      String importingModule)
                throws ModuleNotFoundException {
            if (OWNER.path().equals(modulePath)) {
                return classSymbols.get(className);
            }
            return null;
        }

        @Override
        public Symbol.ClassSymbol resolveClassSymbol(String className,
                deal.identity.CanonicalModuleIdentity declaringModule,
                String importingModule) throws ModuleNotFoundException {
            if (IdentityTestFixtures.moduleIdentityOf(OWNER.path())
                    .equals(declaringModule)) {
                return classSymbols.get(className);
            }
            return null;
        }
    }

    /** The two-module checked project: index digest + per-module coverage rows. */
    private static ProjectFacts buildProject(CheckedSlice owner, CheckedSlice caller) {
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
        ModuleFact ownerFact = new ModuleFact(OWNER_SOURCE_ID, OWNER, false, false,
            owner.program(), ownerExports(owner), owner.symbols(), owner.checks(), List.of());
        ModuleFact callerFact = new ModuleFact(CALLER_SOURCE_ID, CALLER, false, false,
            caller.program(), Map.of(), caller.symbols(), caller.checks(),
            List.of(new ModuleFact.ImportFact("Owner", IMPORT_SPECIFIER, OWNER_SOURCE_ID)));
        deal.semantic.CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation,
            CALLER, List.of(ownerFact, callerFact));
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            "the two-module checked project builds cleanly: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            built.input(), built.index());
        check(manifests != null && manifests.diagnostics().isEmpty()
                && manifests.manifests() != null && manifests.manifests().size() == 2,
            "the foundation detector produces exactly two requirement manifests (owner, "
                + "caller): "
                + (manifests == null ? "null" : manifests.diagnostics()));
        if (manifests == null || !manifests.diagnostics().isEmpty()
                || manifests.manifests() == null || manifests.manifests().size() != 2) {
            return null;
        }
        Map<ModuleId, Map<ConstructKind, List<SemanticOpKind>>> coverages =
            new LinkedHashMap<>();
        List<ModuleId> ordered = List.of(OWNER, CALLER);
        for (int i = 0; i < ordered.size(); i++) {
            Map<ConstructKind, List<SemanticOpKind>> coverage =
                new LinkedHashMap<>(manifests.manifests().get(i).constructCoverage());
            coverage.remove(ConstructKind.IMPORT_EXPORT_ENTRY);
            coverages.put(ordered.get(i), coverage);
        }
        return new ProjectFacts(built.index(), built.index().interfaceIndexDigest(),
            coverages);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice, ModuleId moduleId,
                                               List<ResolvedImport> imports) {
        return new CheckedModuleInput(moduleId, moduleId.path() + ".deal",
            Path.of(moduleId.path() + ".deal"), slice.program(), slice.checks(), imports,
            List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    /** Lowers the owner and the caller through the extended seam. */
    private static LoweredPair lowerPair(String ownerSource, String callerSource,
                                         boolean withFacts) {
        CheckedSlice owner = checkSlice(ownerSource, OWNER, null);
        if (owner == null) {
            return null;
        }
        CheckedSlice caller = checkSlice(callerSource, CALLER, new OwnerResolver(owner));
        if (caller == null) {
            return null;
        }
        ProjectFacts project = buildProject(owner, caller);
        if (project == null) {
            return null;
        }
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(OWNER, CALLER));
        SemanticLowerer.ClassDeclarationCoreResult ownerResult =
            SemanticLowerer.lowerModuleClassCore(moduleOf(owner, OWNER, List.of()),
                SemanticProfile.DEAL_V1_2_INT32, project.coverages().get(OWNER),
                project.interfaceHash(), REGISTRY_HASH,
                project.index().modules().get(OWNER), Map.of(), allocator);
        check(ownerResult != null && ownerResult.lowering() != null
                && !ownerResult.lowering().hasErrors()
                && ownerResult.lowering().unit() != null,
            "the owner module lowers to a validated unit: "
                + (ownerResult == null || ownerResult.lowering() == null ? "null"
                    : ownerResult.lowering().diagnostics()));
        if (ownerResult == null || ownerResult.lowering() == null
                || ownerResult.lowering().hasErrors()
                || ownerResult.lowering().unit() == null) {
            return null;
        }
        // The imported-construction facts: per exported owner class, the
        // interface entry, the owner unit's layout, the registry binding's
        // factory op id, and the factory op's result ValueId.
        Map<ClassId, SharedFactoryFacts> facts = new LinkedHashMap<>();
        ExternalModuleInterface ownerInterface = project.index().modules().get(OWNER);
        LoweredModuleUnit ownerUnit = ownerResult.lowering().unit();
        for (ClassInterface entry : ownerInterface.classes()) {
            ClassLayout ownerLayout = ownerUnit.classLayouts().get(entry.classId());
            OpId factoryOpId = ownerResult.registry().factoryFor(entry.constructionEntry());
            SemanticOp factoryOp = opById(ownerUnit, factoryOpId);
            check(ownerLayout != null && factoryOpId != null && factoryOp != null
                    && factoryOp.result() instanceof ValueId,
                "the owner facts resolve: layout, registry binding, factory op, and "
                    + "factory result of " + entry.classId());
            if (ownerLayout == null || factoryOpId == null || factoryOp == null
                    || !(factoryOp.result() instanceof ValueId factoryResult)) {
                return null;
            }
            facts.put(entry.classId(), new SharedFactoryFacts(entry.classId(), entry,
                ownerLayout, factoryOpId, factoryResult));
        }
        List<ResolvedImport> callerImports = List.of(new ResolvedImport("Owner",
            IMPORT_SPECIFIER, OWNER, ExternalModuleKind.IMPLEMENTATION));
        SemanticLowerer.ClassDeclarationCoreResult callerResult =
            SemanticLowerer.lowerModuleClassCore(moduleOf(caller, CALLER, callerImports),
                SemanticProfile.DEAL_V1_2_INT32, project.coverages().get(CALLER),
                project.interfaceHash(), REGISTRY_HASH,
                project.index().modules().get(CALLER), withFacts ? facts : Map.of(),
                allocator);
        return new LoweredPair(ownerResult, callerResult, project, facts);
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

    private static KindPayload.ClassNewPayload classNewPayload(SemanticOp op) {
        return (KindPayload.ClassNewPayload) op.payload();
    }

    private static KindPayload.ClassFactoryPayload factoryPayload(SemanticOp op) {
        return (KindPayload.ClassFactoryPayload) op.payload();
    }

    private static KindPayload.ClassDefaultPayload defaultPayload(SemanticOp op) {
        return (KindPayload.ClassDefaultPayload) op.payload();
    }

    private static ValueId providedIdOf(KindPayload.ClassNewPayload payload, String name) {
        for (KindPayload.ProvidedField field : payload.providedFields()) {
            if (field.name().equals(name)) {
                return field.valueOpId();
            }
        }
        return null;
    }

    private static Value constValue(SemanticOp op) {
        return op.payload() instanceof KindPayload.ConstPayload payload
            ? constValue(payload.value()) : null;
    }

    private static Value constValue(ScalarValue scalar) {
        return switch (scalar) {
            case ScalarValue.Int intValue -> new Value.Int(intValue.value());
            case ScalarValue.String string -> Value.string(string.value());
            case ScalarValue.Number number -> new Value.Number(number.value());
            case ScalarValue.Boolean bool -> new Value.Bool(bool.value());
            case ScalarValue.Null ignored -> Value.Null.INSTANCE;
        };
    }

    // =========================================================================
    // (a) the pinned SHARED_FACTORY payload shape
    // =========================================================================

    private static void testPinnedSharedFactoryPayloads() {
        System.out.println("-- imported literal: the pinned SHARED_FACTORY payload "
            + "(defaultOwner, classFactoryRef = the interface constructionEntry, empty "
            + "classDefaultOpIds, declaration-order boundaries with the factory-result "
            + "wiring) --");

        LoweredPair pair = lowerPair("""
            let base: int = 40;
            export class Point {
              x: int = base + 2;
              tag: string = "pt";
            }
            """, """
            import * as Owner from "owner"
            let p: Owner.Point = {tag: "t2"}
            """, true);
        check(pair != null && pair.caller() != null && pair.caller().lowering() != null
                && !pair.caller().lowering().hasErrors()
                && pair.caller().lowering().unit() != null,
            "the imported-literal caller lowers to a validated unit: "
                + (pair == null || pair.caller() == null || pair.caller().lowering() == null
                    ? "null" : pair.caller().lowering().diagnostics()));
        if (pair == null || pair.caller() == null || pair.caller().lowering() == null
                || pair.caller().lowering().hasErrors()
                || pair.caller().lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        ClassId pointId = new ClassId(OWNER.path(), "Point");

        List<SemanticOp> classNews = ofKind(callerUnit.ops(), SemanticOpKind.CLASS_NEW);
        check(classNews.size() == 1,
            "exactly one CLASS_NEW op in the caller unit; got " + classNews.size());
        if (classNews.size() != 1) {
            return;
        }
        SemanticOp op = classNews.get(0);
        KindPayload.ClassNewPayload payload = classNewPayload(op);

        // The mode and the factory ref: exactly one CLASS_NEW with
        // defaultOwner SHARED_FACTORY and classFactoryRef = the imported
        // class's ClassInterface.constructionEntry (the pre-allocated
        // route-independent ClassFactoryId).
        check(payload.defaultOwner() == DefaultOwner.SHARED_FACTORY,
            "defaultOwner is SHARED_FACTORY; got " + payload.defaultOwner());
        ClassInterface entry = null;
        for (ClassInterface candidate
                : pair.project().index().modules().get(OWNER).classes()) {
            if (candidate.classId().equals(pointId)) {
                entry = candidate;
            }
        }
        check(entry != null, "the interface index carries the imported class entry");
        if (entry == null) {
            return;
        }
        check(payload.classFactoryRef() != null
                && payload.classFactoryRef().equals(entry.constructionEntry()),
            "classFactoryRef equals the imported class's ClassInterface.constructionEntry "
                + "(the pre-allocated route-independent ClassFactoryId); got "
                + payload.classFactoryRef() + " vs " + entry.constructionEntry());
        check(payload.classDefaultOpIds().isEmpty(),
            "classDefaultOpIds is empty (the owner's CLASS_FACTORY carries the "
                + "CLASS_DEFAULT child list); got " + payload.classDefaultOpIds());

        // The layout is the owner unit's layout record (the
        // layout-resolution context fact), never a re-derived copy.
        ClassLayout ownerLayout = ownerUnit.classLayouts().get(pointId);
        check(ownerLayout != null && payload.layout().equals(ownerLayout),
            "the payload carries exactly the owner unit's classLayouts record");

        // Provided fields in literal order with the producing op results.
        check(payload.providedFields().size() == 1
                && payload.providedFields().get(0).name().equals("tag"),
            "providedFields records the literal source order (tag only); got "
                + payload.providedFields());
        if (payload.providedFields().size() == 1) {
            SemanticOp tagConst = constPublishing(callerUnit,
                payload.providedFields().get(0).valueOpId());
            check(tagConst != null
                    && tagConst.payload() instanceof KindPayload.ConstPayload tagPayload
                    && tagPayload.value() instanceof ScalarValue.String tagValue
                    && tagValue.value().equals("t2"),
                "the tag provided value op is the 't2' CONST producing op");
        }

        // Field boundaries in declaration order: x CLASS_DEFAULT_FIELD
        // (input = the owner factory result ValueId), tag
        // CLASS_LITERAL_FIELD (input = the provided value op id).
        check(payload.fieldBoundaries().size() == 2,
            "two field boundaries; got " + payload.fieldBoundaries().size());
        if (payload.fieldBoundaries().size() != 2) {
            return;
        }
        KindPayload.FieldBoundary x = payload.fieldBoundaries().get(0);
        KindPayload.FieldBoundary tag = payload.fieldBoundaries().get(1);
        check(x.field().equals("x") && x.kind() == BoundaryKind.CLASS_DEFAULT_FIELD
                && tag.field().equals("tag")
                && tag.kind() == BoundaryKind.CLASS_LITERAL_FIELD,
            "the boundaries are in declaration order (x defaulted, tag provided); got "
                + payload.fieldBoundaries());

        // The factory chain: classFactoryRef -> registry op id -> factory
        // op -> result ValueId, wired as the CLASS_DEFAULT_FIELD input
        // (the K-D4 cross-unit D4-global reference).
        OpId factoryOpId = pair.owner().registry().factoryFor(entry.constructionEntry());
        SemanticOp factoryOp = opById(ownerUnit, factoryOpId);
        check(factoryOpId != null && factoryOp != null
                && factoryOp.kind() == SemanticOpKind.CLASS_FACTORY
                && factoryOp.result() instanceof ValueId factoryResult,
            "the owner's registry binding resolves to the CLASS_FACTORY op with a "
                + "ValueId result");
        if (factoryOp == null || !(factoryOp.result() instanceof ValueId factoryResult)) {
            return;
        }
        SemanticOp xChild = opById(callerUnit, x.boundaryOpId());
        check(xChild != null && xChild.kind() == SemanticOpKind.BOUNDARY
                && op.opId().equals(xChild.origin().parentOpId())
                && xChild.payload() instanceof KindPayload.BoundaryPayload xBoundary
                && xBoundary.input().equals(factoryResult),
            "the CLASS_DEFAULT_FIELD boundary input is the owner CLASS_FACTORY op's "
                + "result ValueId (the K-D4 cross-unit D4-global reference)");
        if (xChild != null && xChild.payload() instanceof KindPayload.BoundaryPayload xBoundary) {
            check(xBoundary.kind() == BoundaryKind.CLASS_DEFAULT_FIELD
                    && xBoundary.descriptor().equals(RuntimeDescriptor.Int.INSTANCE)
                    && xChild.failurePolicy() == FailurePolicyId.TYPE_DESCRIPTOR,
                "the x boundary carries the pinned kind/descriptor/policy");
        }
        SemanticOp tagChild = opById(callerUnit, tag.boundaryOpId());
        check(tagChild != null && tagChild.kind() == SemanticOpKind.BOUNDARY
                && op.opId().equals(tagChild.origin().parentOpId())
                && tagChild.payload() instanceof KindPayload.BoundaryPayload tagBoundary
                && tagBoundary.input().equals(providedIdOf(payload, "tag")),
            "the CLASS_LITERAL_FIELD boundary input is the provided tag value op id");

        // The op header.
        check(op.failurePolicy() == FailurePolicyId.CLASS_CONSTRUCTION,
            "the CLASS_NEW policy is CLASS_CONSTRUCTION; got " + op.failurePolicy());
        check(op.result() instanceof ValueId
                && op.resultType() instanceof RuntimeDescriptor.Class classDescriptor
                && classDescriptor.classId().equals(pointId),
            "the op publishes a fresh-instance ValueId with the class:<ClassId> result "
                + "type; got " + op.resultType());
        check(op.operands().isEmpty(), "CLASS_NEW carries no pre-START operands");
        boolean returnBoundary = false;
        for (SemanticOp unitOp : callerUnit.ops()) {
            if (unitOp.kind() == SemanticOpKind.BOUNDARY
                    && op.opId().equals(unitOp.origin().parentOpId())
                    && unitOp.payload() instanceof KindPayload.BoundaryPayload boundary
                    && boundary.kind() == BoundaryKind.FUNCTION_RETURN) {
                returnBoundary = true;
            }
        }
        check(!returnBoundary, "zero return boundaries: no FUNCTION_RETURN child exists "
            + "under the CLASS_NEW op");

        // The caller unit passes the closed validator with the
        // two-module interface hash.
        check(SemanticIrValidator.validate(callerUnit,
                new SemanticIrValidator.ComparisonFacts(callerUnit.interfaceHash(),
                    SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH)).isEmpty(),
            "the imported-literal caller unit passes the closed SemanticIrValidator");
    }

    private static SemanticOp constPublishing(LoweredModuleUnit unit, ValueId result) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CONST && result.equals(op.result())) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // (b) the eval-order pin: provided-field operand order in literal order
    // =========================================================================

    private static void testProvidedFieldLiteralOrder() {
        System.out.println("-- provided-field operand order equals literal order across "
            + "the module boundary (the eval-order pin shape) --");

        LoweredPair pair = lowerPair("""
            export class Point {
              x: int = 1;
              tag: string = "pt";
            }
            """, """
            import * as Owner from "owner"
            let r: Owner.Point = {tag: "r", x: 7}
            """, true);
        check(pair != null && pair.caller() != null && pair.caller().lowering() != null
                && !pair.caller().lowering().hasErrors()
                && pair.caller().lowering().unit() != null,
            "the reordered-literal caller lowers: "
                + (pair == null || pair.caller() == null || pair.caller().lowering() == null
                    ? "null" : pair.caller().lowering().diagnostics()));
        if (pair == null || pair.caller() == null || pair.caller().lowering() == null
                || pair.caller().lowering().hasErrors()
                || pair.caller().lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        List<SemanticOp> classNews = ofKind(callerUnit.ops(), SemanticOpKind.CLASS_NEW);
        check(classNews.size() == 1, "exactly one CLASS_NEW op; got " + classNews.size());
        if (classNews.size() != 1) {
            return;
        }
        KindPayload.ClassNewPayload payload = classNewPayload(classNews.get(0));

        // Literal source order is tag, x (the reverse of declaration
        // order) — the providedFields record and the producing ops must
        // both keep the literal order.
        check(payload.providedFields().size() == 2
                && payload.providedFields().get(0).name().equals("tag")
                && payload.providedFields().get(1).name().equals("x"),
            "providedFields record the literal source order (tag, x); got "
                + payload.providedFields());
        check(payload.fieldBoundaries().size() == 2
                && payload.fieldBoundaries().get(0).field().equals("x")
                && payload.fieldBoundaries().get(0).kind() == BoundaryKind.CLASS_LITERAL_FIELD
                && payload.fieldBoundaries().get(1).field().equals("tag")
                && payload.fieldBoundaries().get(1).kind() == BoundaryKind.CLASS_LITERAL_FIELD,
            "the boundaries stay in declaration order (x, tag) — the reorder source of "
                + "the jvm-xmod-class-construction-defaults pin; got "
                + payload.fieldBoundaries());
        if (payload.providedFields().size() != 2) {
            return;
        }
        // The producing op order: the tag CONST precedes the x CONST and
        // both precede the CLASS_NEW in the caller's op list (the
        // eval-order pin — provided-field evaluation crosses the module
        // boundary in literal order).
        SemanticOp tagConst = constPublishing(callerUnit,
            payload.providedFields().get(0).valueOpId());
        SemanticOp xConst = constPublishing(callerUnit,
            payload.providedFields().get(1).valueOpId());
        int tagIndex = callerUnit.ops().indexOf(tagConst);
        int xIndex = callerUnit.ops().indexOf(xConst);
        int newIndex = callerUnit.ops().indexOf(classNews.get(0));
        check(tagIndex >= 0 && xIndex >= 0 && newIndex >= 0
                && tagIndex < xIndex && xIndex < newIndex,
            "the producing ops appear in the caller unit in literal order (tag CONST "
                + "before x CONST) and both precede the CLASS_NEW; got " + tagIndex + "/"
                + xIndex + "/" + newIndex);
        check(tagConst != null && xConst != null
                && tagConst.payload() instanceof KindPayload.ConstPayload tp
                && tp.value() instanceof ScalarValue.String tv
                && tv.value().equals("r")
                && xConst.payload() instanceof KindPayload.ConstPayload xp
                && xp.value() instanceof ScalarValue.Int xv && xv.value() == 7,
            "the producing ops carry the literal values (r and 7)");
    }

    // =========================================================================
    // (c) the combined T1+T2+T3+T4 scenario: end-to-end cross-unit drive
    // =========================================================================

    private static void testCombinedT1T2T3T4Scenario() {
        System.out.println("-- combined T1+T2+T3+T4: two checked modules lowered through "
            + "the extended seam, then the executor drives the cross-unit construction "
            + "end-to-end --");

        LoweredPair pair = lowerPair("""
            let base: int = 40;
            export class Point {
              x: int = base + 2;
              tag: string = "pt";
              note?: string;
            }
            """, """
            import * as Owner from "owner"
            let p: Owner.Point = {tag: "t2"}
            let q: Owner.Point = {}
            let r: Owner.Point = {tag: "r", x: 7}
            let px: int = p.x
            let hasNote: boolean = has(p.note)
            """, true);
        check(pair != null && pair.caller() != null && pair.caller().lowering() != null
                && !pair.caller().lowering().hasErrors()
                && pair.caller().lowering().unit() != null,
            "the combined caller lowers to a validated unit: "
                + (pair == null || pair.caller() == null || pair.caller().lowering() == null
                    ? "null" : pair.caller().lowering().diagnostics()));
        if (pair == null || pair.caller() == null || pair.caller().lowering() == null
                || pair.caller().lowering().hasErrors()
                || pair.caller().lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        StructuredBodyTable ownerTable = pair.owner().lowering().table();
        ClassId pointId = new ClassId(OWNER.path(), "Point");
        ClassLayout layout = ownerUnit.classLayouts().get(pointId);

        List<SemanticOp> classNews = ofKind(callerUnit.ops(), SemanticOpKind.CLASS_NEW);
        List<SemanticOp> reads = ofKind(callerUnit.ops(), SemanticOpKind.FIELD_READ);
        List<SemanticOp> hasOps = ofKind(callerUnit.ops(), SemanticOpKind.HAS_FIELD);
        check(classNews.size() == 3 && reads.size() == 1 && hasOps.size() == 1,
            "the caller unit carries three CLASS_NEW ops, one FIELD_READ, and one "
                + "HAS_FIELD; got " + classNews.size() + "/" + reads.size() + "/"
                + hasOps.size());
        if (classNews.size() != 3 || reads.size() != 1 || hasOps.size() != 1) {
            return;
        }

        // The T1 tie: the owner's exported class registered its factory
        // under the pre-allocated constructionEntry, and the caller's
        // CLASS_NEW ops reference that entry (a broken T1 registry fails
        // here).
        SharedFactoryFacts facts = pair.facts().get(pointId);
        check(facts != null, "the facts map carries the imported class entry");
        if (facts == null) {
            return;
        }
        List<SemanticOp> factories = ofKind(ownerUnit.ops(), SemanticOpKind.CLASS_FACTORY);
        check(factories.size() == 1 && facts.factoryOpId().equals(factories.get(0).opId()),
            "the owner unit carries exactly one CLASS_FACTORY op and the facts record "
                + "its registry binding");
        for (SemanticOp classNew : classNews) {
            check(classNewPayload(classNew).defaultOwner() == DefaultOwner.SHARED_FACTORY
                    && classNewPayload(classNew).classFactoryRef()
                        .equals(facts.interfaceEntry().constructionEntry())
                    && classNewPayload(classNew).classDefaultOpIds().isEmpty(),
                "each caller CLASS_NEW carries the pinned SHARED_FACTORY payload shape");
        }

        // The owner-scope default evidence: the x default block carries a
        // BINDING_LOAD of the owner's module-level binding `base` — the
        // declaring module's scope resolution surface (a broken T1
        // default-block emission fails here).
        Map<OpId, SemanticOp> ownerLookup = new LinkedHashMap<>();
        for (SemanticOp op : ownerUnit.ops()) {
            ownerLookup.put(op.opId(), op);
        }
        boolean ownerBindingLoad = false;
        KindPayload.ClassFactoryPayload ownerFactory = factoryPayload(factories.get(0));
        for (OpId defaultId : ownerFactory.classDefaultOpIds()) {
            SemanticOp def = ownerLookup.get(defaultId);
            if (def == null) {
                continue;
            }
            List<OpId> block = ownerTable.blockOps().get(defaultPayload(def).defaultBlock());
            if (block != null) {
                for (OpId listed : block) {
                    SemanticOp blockOp = ownerLookup.get(listed);
                    if (blockOp != null && blockOp.kind() == SemanticOpKind.BINDING_LOAD) {
                        ownerBindingLoad = true;
                    }
                }
            }
        }
        check(ownerBindingLoad,
            "the owner's default block carries the BINDING_LOAD of the module-level "
                + "binding (the declaring module's scope)");

        // The cross-unit drive: the caller unit's ops in source order with
        // the executor driving each CLASS_NEW through the owner's factory.
        Map<OpId, SemanticOp> callerLookup = new LinkedHashMap<>();
        for (SemanticOp op : callerUnit.ops()) {
            callerLookup.put(op.opId(), op);
        }
        Map<ValueId, Value> heap = new LinkedHashMap<>();
        Map<deal.semantic.ir.BindingId, Value> bindings = new LinkedHashMap<>();
        List<String> log = new ArrayList<>();
        BoundaryCheckRunner real = realDelegate(log);
        List<SemanticOp> invokedDefaults = new ArrayList<>();
        BodyRunner ownerScope = defaultOpArg -> {
            invokedDefaults.add(defaultOpArg);
            if ("x".equals(defaultPayload(defaultOpArg).field())) {
                return new Value.Int(42);
            }
            if ("tag".equals(defaultPayload(defaultOpArg).field())) {
                return Value.string("pt");
            }
            throw new IllegalStateException("unexpected default field "
                + defaultPayload(defaultOpArg).field());
        };
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>();
        layouts.putAll(ownerUnit.classLayouts());
        layouts.putAll(callerUnit.classLayouts());
        ClassFactoryRegistry registry = pair.owner().registry();

        for (SemanticOp op : callerUnit.ops()) {
            switch (op.kind()) {
                case CONST -> heap.put((ValueId) op.result(), constValue(op));
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
                case CLASS_NEW -> {
                    KindPayload.ClassNewPayload payload = classNewPayload(op);
                    Outcome<Value> outcome =
                        ClassOpsExecutor.executeClassNewSharedFactory(op, heap, registry,
                            ownerLookup,
                            resolveBoundaryOps(callerLookup, payload.fieldBoundaries()),
                            layouts, real, ownerScope);
                    check(outcome instanceof Outcome.Success<Value> success
                            && success.value() instanceof Value.Class,
                        "the cross-unit CLASS_NEW drive constructs the instance; got "
                            + outcome);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    }
                }
                case FIELD_READ -> {
                    List<SemanticOp> children = childrenOf(callerUnit, op);
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
                    // BINDING_ALLOC, VARIABLE_DECLARATION boundaries, and
                    // the detached CLASS_DEFAULT/CLASS_FACTORY ops carry
                    // no interpreter step in this drive.
                }
            }
        }

        // The jvm-xmod-class-construction-defaults pin at the unit level:
        // defaults applied by the owner's factory, provided fields
        // reordered to declaration order in the published instances.
        Value.Class p = (Value.Class) heap.get((ValueId) classNews.get(0).result());
        Value.Class q = (Value.Class) heap.get((ValueId) classNews.get(1).result());
        Value.Class r = (Value.Class) heap.get((ValueId) classNews.get(2).result());
        check(p != null && q != null && r != null && layout != null,
            "all three constructions published instances");
        if (p == null || q == null || r == null || layout == null) {
            return;
        }
        check(p.classId().equals(pointId) && p.fields().size() == 3
                && p.fields().get(0) instanceof FieldState.Present pxPresent
                && pxPresent.value().equals(new Value.Int(42))
                && p.fields().get(1) instanceof FieldState.Present tagPresent
                && tagPresent.value().equals(Value.string("t2"))
                && p.fields().get(2) == FieldState.Missing.INSTANCE,
            "the partial literal p: the omitted x defaulted by the owner's factory (42), "
                + "the provided tag overlaid in declaration order, the omitted optional "
                + "note missing");
        check(q.fields().get(0) instanceof FieldState.Present qx
                && qx.value().equals(new Value.Int(42))
                && q.fields().get(1) instanceof FieldState.Present qt
                && qt.value().equals(Value.string("pt"))
                && q.fields().get(2) == FieldState.Missing.INSTANCE,
            "the empty literal q: every required-present default filled by the owner's "
                + "factory (42 and pt), the omitted optional missing");
        check(r.fields().get(0) instanceof FieldState.Present rx
                && rx.value().equals(new Value.Int(7))
                && r.fields().get(1) instanceof FieldState.Present rt
                && rt.value().equals(Value.string("r")),
            "the full literal r: both provided fields overlaid in declaration order "
                + "(x=7, tag=r)");
        check(heap.get((ValueId) reads.get(0).result()).equals(new Value.Int(42)),
            "the FIELD_READ observed the factory-defaulted x (42) — the T3 presence "
                + "read over the imported instance");
        check(heap.get((ValueId) hasOps.get(0).result()).equals(new Value.Bool(false)),
            "has(note) returned false — the omitted optional stays missing (the T3 "
                + "presence model)");

        // The eval-order pin: every owner default invocation happened
        // after the caller-side provided values resolved; the provided
        // field's defaults never ran.
        for (SemanticOp invoked : invokedDefaults) {
            check(invoked.opId().module().equals(OWNER),
                "every default block ran in the owner unit (the declaring module's "
                    + "scope); got " + invoked.opId());
        }
        int pDefaults = 0;
        for (SemanticOp invoked : invokedDefaults) {
            if (defaultPayload(invoked).field().equals("x")) {
                pDefaults++;
            }
        }
        check(pDefaults == 2,
            "the x default ran exactly twice (p and q — the two omitted x fields); the "
                + "full literal r ran zero defaults (all provided); got " + pDefaults);
        check(log.contains("child CLASS_DEFAULT_FIELD <- int")
                && log.contains("child CLASS_LITERAL_FIELD <- string")
                && log.contains("child UNTYPED_CLASS_INPUT <- class:" + pointId.text())
                && log.contains("child OPTIONAL_FIELD_READ <- int"),
            "the real boundary delegate observed the pinned child kinds and the "
                + "canonical receiver kind; got " + log);
    }

    private static List<SemanticOp> childrenOf(LoweredModuleUnit unit, SemanticOp owner) {
        List<SemanticOp> children = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (owner.opId().equals(op.origin().parentOpId())) {
                children.add(op);
            }
        }
        return children;
    }

    private static Map<OpId, SemanticOp> resolveBoundaryOps(Map<OpId, SemanticOp> lookup,
            List<KindPayload.FieldBoundary> entries) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : entries) {
            SemanticOp child = lookup.get(entry.boundaryOpId());
            if (child != null) {
                resolved.put(entry.boundaryOpId(), child);
            }
        }
        return resolved;
    }

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
    // (d) the RETAINED_ABI deferral negative
    // =========================================================================

    private static void testRetainedAbiDeferralNegative() {
        System.out.println("-- RETAINED_ABI deferral negative: an owner-route mismatch "
            + "defers to E10 (E6005 RETAINED_ABI_DEFERRED), never emits --");

        LoweredPair pair = lowerPair("""
            export class Point {
              x: int = 1;
            }
            """, """
            import * as Owner from "owner"
            let p: Owner.Point = {}
            """, false);
        check(pair != null && pair.caller() != null && pair.caller().lowering() != null
                && pair.caller().lowering().hasErrors()
                && pair.caller().lowering().unit() == null,
            "the imported literal without shared-factory facts fails lowering with no "
                + "unit: "
                + (pair == null || pair.caller() == null || pair.caller().lowering() == null
                    ? "null" : pair.caller().lowering().diagnostics()));
        if (pair == null || pair.caller() == null || pair.caller().lowering() == null
                || !pair.caller().lowering().hasErrors()) {
            return;
        }
        CompilerDiagnostic diagnostic = pair.caller().lowering().diagnostics().get(0);
        check("E6005".equals(diagnostic.code()), "the failure is E6005; got "
            + diagnostic.code());
        check(diagnostic.message().contains(SemanticLowerer.RETAINED_ABI_DEFERRED),
            "the failure names the RETAINED_ABI_DEFERRED validator rule");
        check(diagnostic.message().contains("capability CLASSES"),
            "the failure detail carries capability CLASSES");
        check(diagnostic.message().contains("module 'main'"),
            "the failure detail carries the caller module");
        check(diagnostic.message().contains("the RETAINED_ABI derivation is E10's"),
            "the failure detail names the E10 deferral (ISSUE-0239)");
        check(pair.caller().registry().factories().isEmpty(),
            "the deferred caller produced an empty factory registry (never a "
                + "SHARED_FACTORY emission)");
        // Never silently emitted: no CLASS_NEW exists anywhere (the unit
        // is absent, so the unit-level check is vacuous and asserted by
        // construction — the deferral precedes any op emission).
        check(pair.caller().lowering().unit() == null,
            "no unit and therefore no CLASS_NEW op was emitted (the deferral never "
                + "emits SHARED_FACTORY or RETAINED_ABI)");
    }

    // =========================================================================
    // (e) same-module literals stay LOCAL
    // =========================================================================

    private static void testSameModuleStaysLocal() {
        System.out.println("-- same-module literals stay LOCAL (T2's arm) even when the "
            + "shared-factory facts exist --");

        LoweredPair pair = lowerPair("""
            export class Point {
              x: int = 1;
            }
            """, """
            import * as Owner from "owner"
            class Local { a: int = 1; }
            let l: Local = {}
            let p: Owner.Point = {}
            """, true);
        check(pair != null && pair.caller() != null && pair.caller().lowering() != null
                && !pair.caller().lowering().hasErrors()
                && pair.caller().lowering().unit() != null,
            "the mixed local+imported caller lowers: "
                + (pair == null || pair.caller() == null || pair.caller().lowering() == null
                    ? "null" : pair.caller().lowering().diagnostics()));
        if (pair == null || pair.caller() == null || pair.caller().lowering() == null
                || pair.caller().lowering().hasErrors()
                || pair.caller().lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        List<SemanticOp> classNews = ofKind(callerUnit.ops(), SemanticOpKind.CLASS_NEW);
        check(classNews.size() == 2, "two CLASS_NEW ops (Local and Point); got "
            + classNews.size());
        if (classNews.size() != 2) {
            return;
        }
        KindPayload.ClassNewPayload local = classNewPayload(classNews.get(0));
        KindPayload.ClassNewPayload imported = classNewPayload(classNews.get(1));
        check(local.classId().equals(new ClassId("main", "Local"))
                && local.defaultOwner() == DefaultOwner.LOCAL
                && local.classFactoryRef() == null,
            "the local literal keeps the LOCAL shape (defaultOwner LOCAL, null "
                + "classFactoryRef); got " + local.classId() + "/" + local.defaultOwner()
                + "/" + local.classFactoryRef());
        check(local.classDefaultOpIds().size() == 1,
            "the local literal wires its own CLASS_DEFAULT op id; got "
                + local.classDefaultOpIds());
        check(imported.classId().equals(new ClassId("owner", "Point"))
                && imported.defaultOwner() == DefaultOwner.SHARED_FACTORY
                && imported.classFactoryRef() != null
                && imported.classDefaultOpIds().isEmpty(),
            "the imported literal keeps the SHARED_FACTORY shape alongside the LOCAL "
                + "one; got " + imported.classId() + "/" + imported.defaultOwner()
                + "/" + imported.classFactoryRef());
        // The local default wiring differs from the imported wiring: the
        // local CLASS_DEFAULT_FIELD input is the local CLASS_DEFAULT op
        // result, the imported one is the owner factory result.
        if (local.fieldBoundaries().size() == 1 && local.classDefaultOpIds().size() == 1
                && imported.fieldBoundaries().size() == 1) {
            SemanticOp localBoundary = opById(callerUnit,
                local.fieldBoundaries().get(0).boundaryOpId());
            SemanticOp localDefault = opById(callerUnit, local.classDefaultOpIds().get(0));
            SemanticOp importedBoundary = opById(callerUnit,
                imported.fieldBoundaries().get(0).boundaryOpId());
            check(localBoundary != null && localDefault != null
                    && localBoundary.payload() instanceof KindPayload.BoundaryPayload lb
                    && lb.input().equals(localDefault.result()),
                "the local CLASS_DEFAULT_FIELD boundary wires the local CLASS_DEFAULT "
                    + "op result");
            check(importedBoundary != null
                    && importedBoundary.payload() instanceof KindPayload.BoundaryPayload ib
                    && ib.input().equals(pair.facts().get(imported.classId()).factoryResult()),
                "the imported CLASS_DEFAULT_FIELD boundary wires the owner factory "
                    + "result");
        }
    }

    // =========================================================================
    // (f) determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- determinism: two repetitions are byte-identical --");

        String ownerSource = """
            let base: int = 40;
            export class Point {
              x: int = base + 2;
              tag: string = "pt";
              note?: string;
            }
            """;
        String callerSource = """
            import * as Owner from "owner"
            let p: Owner.Point = {tag: "t2"}
            let q: Owner.Point = {}
            let r: Owner.Point = {tag: "r", x: 7}
            """;
        LoweredPair first = lowerPair(ownerSource, callerSource, true);
        LoweredPair second = lowerPair(ownerSource, callerSource, true);
        check(first != null && first.caller() != null && first.caller().lowering() != null
                && !first.caller().lowering().hasErrors()
                && second != null && second.caller() != null
                && second.caller().lowering() != null
                && !second.caller().lowering().hasErrors(),
            "both repetitions lower");
        if (first == null || first.caller() == null || first.caller().lowering() == null
                || first.caller().lowering().hasErrors()
                || second == null || second.caller() == null
                || second.caller().lowering() == null
                || second.caller().lowering().hasErrors()) {
            return;
        }
        byte[] firstOwner = SemanticIrDumper.dumpModule(first.owner().lowering().unit());
        byte[] secondOwner = SemanticIrDumper.dumpModule(second.owner().lowering().unit());
        byte[] firstCaller = SemanticIrDumper.dumpModule(first.caller().lowering().unit());
        byte[] secondCaller = SemanticIrDumper.dumpModule(second.caller().lowering().unit());
        check(java.util.Arrays.equals(firstOwner, secondOwner),
            "the two owner-unit repetitions produce byte-identical dumps");
        check(java.util.Arrays.equals(firstCaller, secondCaller),
            "the two caller-unit repetitions produce byte-identical dumps (the "
                + "cross-unit factory-result references are deterministic)");
        check(first.owner().registry().factories()
                .equals(second.owner().registry().factories()),
            "the two owner-registry repetitions are identical");
        check(first.facts().equals(second.facts()),
            "the two shared-factory fact maps are identical");
        check(SemanticIrValidator.validate(first.caller().lowering().unit(),
                new SemanticIrValidator.ComparisonFacts(
                    first.caller().lowering().unit().interfaceHash(),
                    SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH)).isEmpty(),
            "the first caller unit passes the closed SemanticIrValidator");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Shared Factory Lowering Tests (ISSUE-0514 "
            + "SHARED_FACTORY arm) ===\n");

        testPinnedSharedFactoryPayloads();
        testProvidedFieldLiteralOrder();
        testCombinedT1T2T3T4Scenario();
        testRetainedAbiDeferralNegative();
        testSameModuleStaysLocal();
        testDeterminism();

        System.out.println("\nSharedFactoryLoweringTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
