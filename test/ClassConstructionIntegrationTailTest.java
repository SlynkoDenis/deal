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
import deal.diagnostics.DiagnosticCode;
import deal.lexer.Lexer;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuilder;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.JsonClassAlgorithmAdapter;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ClassOpsExecutor.BodyRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryCheckRunner;
import deal.semantic.ir.ClassOpsExecutor.BoundaryResult;
import deal.semantic.ir.ClassOpsExecutor.FieldState;
import deal.semantic.ir.ClassOpsExecutor.NestedClassFactory;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SharedFactoryFacts;
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
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The ISSUE-0517 class-construction integration tail: the real
 * end-to-end semantic-IR pipeline suite driving local and imported
 * construction, provided/default order, mutable-default freshness,
 * E8007 extra-key rejection, field failures, presence states, nested
 * factory parenting, JSON round trips, null-on-input-failure, and
 * first serialization failure through the production lowerer
 * ({@code SemanticLowerer.lowerModuleClassCore} — the class arms plus
 * every production validator that runs inside it) and the assembled
 * production {@link ClassOpsExecutor} with the production
 * {@link BoundaryExecutor} boundary delegate and the production
 * {@link JsonClassAlgorithmAdapter} JSON algorithm delegate (the
 * {@code StdlibIntegrationTest} / {@code ClassIntegrationVerificationTest}
 * precedent).
 *
 * <p><b>Scenario.</b> Two checked modules — an owner exporting the
 * {@code @jsonable} Address (defaults: a literal city and a
 * module-level-binding zip) plus the mutable-defaulted Bag (array and
 * table defaults); a caller importing both and declaring the
 * {@code @jsonable} Person (defaulted name/age/ratio/home/meta plus an
 * optional note) and the no-default-required {@code @jsonable} Strict —
 * lowered through the extended two-module seam, then driven through the
 * executor with the owner's factories filling imported defaults in the
 * declaring module's scope and the pinned cross-module
 * construction/default/eval-order shapes reproduced at the unit level.</p>
 *
 * <p><b>Coverage map.</b> (a) local construction — provided values in
 * literal order, omitted defaults only, declaration-order field
 * validation, the complete tagged instance only, no partial instance on
 * failure; (b) the E8007 first-extra-key arm in provided-source order
 * after completed default application, LOCAL and SHARED_FACTORY;
 * (c) imported construction — the owner factory trigger, defaults in
 * the declaring module's scope, caller provided-field order preserved
 * with the overlay reorder; (d) mutable-default freshness — fresh
 * array/table identities per construction, imported and local;
 * (e) field read/write/delete/has — the three presence states
 * (missing/present null/present value), the exact nominal-receiver
 * identity failures, the required-field missing read, single
 * evaluation; (f) JSON decode — language null on syntax, unknown-key,
 * type-mismatch, nested, and absent-no-default failures with no
 * partial instance and no defaults on provided-value failure, the
 * {@code {}}/{@code []} collapse, the three-state roundtrip, the nested
 * factory parent pin; (g) JSON encode — deterministic declaration-order
 * text, the first declaration-order failure with the pinned
 * {@code value at {fieldPath} is not JSON serializable: {actual}}
 * template at the call origin, wrong identity at the root, nonfinite
 * numbers, cycles, and the missing-required arm.</p>
 *
 * <p><b>Determinism.</b> The suite is single-threaded and deterministic:
 * every phase reads the pinned fixtures and the landed production seams.</p>
 */
public class ClassConstructionIntegrationTailTest {

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

    private static final ClassId ADDRESS_ID = new ClassId("owner", "Address");
    private static final ClassId BAG_ID = new ClassId("owner", "Bag");
    private static final ClassId PERSON_ID = new ClassId("main", "Person");
    private static final ClassId STRICT_ID = new ClassId("main", "Strict");

    /** The call origin of the user's C$toJson call (never the generated anchor). */
    private static final SourceOrigin CALL_ORIGIN = new SourceOrigin(
        "call-site.deal", SourceSpan.synthetic("call-site.deal"),
        SourceOriginKind.USER, new AnchorId(500), null);

    /**
     * The owner: Address with a literal city default and a
     * module-level-binding zip default (the declaring-scope surface);
     * Bag with mutable array/table defaults.
     */
    private static final String OWNER_SOURCE = """
        let baseZip: int = 10115;

        // @jsonable
        export class Address {
          city: string = "berlin";
          zip: int = baseZip;
        }

        export class Bag {
          tags: int[] = [1, 2];
          meta: table = {seed: "s"};
        }
        """;

    /**
     * The caller: Person (@jsonable, defaulted fields plus an optional
     * note and a table meta), Strict (@jsonable, no-default required
     * tag — the K-D9 shape), imported literals (reordered and empty),
     * two Bag constructions, the field/presence operations, and the
     * cross-module nullable receiver read.
     */
    private static final String CALLER_SOURCE = """
        import * as Owner from "owner"

        // @jsonable
        export class Person {
          name: string = "anon";
          age: int = 0;
          ratio: number = 0.5;
          home: Owner.Address = {city: "seed"};
          note?: string | null;
          meta: table = {k: "v"};
        }

        // @jsonable
        export class Strict {
          tag: string;
        }

        let addr: Owner.Address = {zip: 9, city: "munich"}
        let emptyAddr: Owner.Address = {}
        let bag1: Owner.Bag = {}
        let bag2: Owner.Bag = {}
        let p: Person = {age: 7}
        let q: Person = {name: "bob", age: 3, home: {city: "x", zip: 5}}
        p.note = "x"
        let hasNote: boolean = has(p.note)
        let readNote: string | null = p.note
        p.note = null
        let hasNull: boolean = has(p.note)
        let readNull: string | null = p.note
        delete p.note
        let hasAfter: boolean = has(p.note)
        let maybe: Owner.Address | null = null
        let city: string | null = maybe.city
        let addrCity: string = addr.city
        """;

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record ProjectFacts(deal.semantic.ir.ProjectInterfaceIndex index,
                                String interfaceHash,
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
        Parser parser = new Parser(lex.tokens(), sourceId, lex.directiveEvents());
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

    /** The owner's export map (the orchestrator's derivation). */
    private static Map<String, Type> ownerExports(CheckedSlice owner) {
        Map<String, Type> exports = new LinkedHashMap<>();
        for (StatementNode stmt : owner.program().statements()) {
            if (stmt instanceof ExportDeclaration exp
                    && exp.declaration() instanceof ClassDeclaration cd) {
                Symbol sym = owner.symbols().resolve(cd.name());
                if (sym instanceof Symbol.ClassSymbol cs) {
                    exports.put(cd.name(), Types.classType(cs.name(), cs.identity()));
                    if (cd.isJsonable()) {
                        Symbol fromSym = owner.symbols().resolve(cd.name() + "$fromJson");
                        Symbol toSym = owner.symbols().resolve(cd.name() + "$toJson");
                        if (fromSym instanceof Symbol.FunctionSymbol from) {
                            exports.put(cd.name() + "$fromJson", from.funcType());
                        }
                        if (toSym instanceof Symbol.FunctionSymbol to) {
                            exports.put(cd.name() + "$toJson", to.funcType());
                        }
                    }
                }
            }
        }
        return exports;
    }

    /** The owner-symbol resolver for the caller's checking. */
    private static final class OwnerResolver implements ModuleResolver {
        private final Map<String, Type> exports;
        private final Map<String, Symbol.ClassSymbol> classSymbols = new LinkedHashMap<>();
        private final Set<String> syntheticFunctions;

        OwnerResolver(CheckedSlice owner) {
            this.exports = ownerExports(owner);
            this.syntheticFunctions = Set.of("Address$fromJson", "Address$toJson");
            for (StatementNode stmt : owner.program().statements()) {
                if (stmt instanceof ExportDeclaration exp
                        && exp.declaration() instanceof ClassDeclaration cd) {
                    Symbol sym = owner.symbols().resolve(cd.name());
                    if (sym instanceof Symbol.ClassSymbol cs) {
                        classSymbols.put(cd.name(), cs);
                    }
                }
            }
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
            if (IdentityTestFixtures.moduleIdentityOf(OWNER.path()).equals(declaringModule)) {
                return classSymbols.get(className);
            }
            return null;
        }

        @Override
        public boolean isFunctionExportedFromModule(
                deal.identity.CanonicalModuleIdentity declaringModule, String functionName,
                String importingModule) throws ModuleNotFoundException {
            if (IdentityTestFixtures.moduleIdentityOf(OWNER.path()).equals(declaringModule)) {
                return syntheticFunctions.contains(functionName);
            }
            return false;
        }
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice, ModuleId moduleId,
                                               List<ResolvedImport> imports) {
        return new CheckedModuleInput(moduleId, moduleId.path() + ".deal",
            Path.of(moduleId.path() + ".deal"), slice.program(), slice.checks(), imports,
            List.of(), CheckedModuleKind.IMPLEMENTATION);
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

    private static LoweredPair lowerPair() {
        CheckedSlice owner = checkSlice(OWNER_SOURCE, OWNER, null);
        if (owner == null) {
            return null;
        }
        CheckedSlice caller = checkSlice(CALLER_SOURCE, CALLER, new OwnerResolver(owner));
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
                project.index().modules().get(CALLER), facts, allocator);
        check(callerResult != null && callerResult.lowering() != null
                && !callerResult.lowering().hasErrors()
                && callerResult.lowering().unit() != null,
            "the caller module lowers to a validated unit: "
                + (callerResult == null || callerResult.lowering() == null ? "null"
                    : callerResult.lowering().diagnostics()));
        if (callerResult == null || callerResult.lowering() == null
                || callerResult.lowering().hasErrors()
                || callerResult.lowering().unit() == null) {
            return null;
        }
        return new LoweredPair(ownerResult, callerResult, project, facts);
    }

    // =========================================================================
    // Op helpers
    // =========================================================================

    private static SemanticOp opById(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
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

    private static Map<OpId, SemanticOp> resolveBoundaryOps(LoweredModuleUnit unit,
            KindPayload.ClassNewPayload payload) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
            SemanticOp child = opById(unit, entry.boundaryOpId());
            if (child != null) {
                resolved.put(entry.boundaryOpId(), child);
            }
        }
        return resolved;
    }

    private static Map<OpId, SemanticOp> resolveBoundaryOps(
            Map<OpId, SemanticOp> lookup, List<KindPayload.FieldBoundary> boundaries) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : boundaries) {
            resolved.put(entry.boundaryOpId(), lookup.get(entry.boundaryOpId()));
        }
        return resolved;
    }

    private static Map<OpId, SemanticOp> resolveDefaultOps(Map<OpId, SemanticOp> lookup,
                                                           List<OpId> ids) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (OpId id : ids) {
            resolved.put(id, lookup.get(id));
        }
        return resolved;
    }

    private static SemanticOp jsonOpOf(LoweredModuleUnit unit, SemanticOpKind kind,
                                       ClassId classId) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != kind) {
                continue;
            }
            ClassId carried = kind == SemanticOpKind.JSON_FROM_CLASS
                ? ((KindPayload.JsonFromClassPayload) op.payload()).layout().classId()
                : ((KindPayload.JsonToClassPayload) op.payload()).layout().classId();
            if (classId.equals(carried)) {
                return op;
            }
        }
        return null;
    }

    private static KindPayload.ClassNewPayload classNewPayload(SemanticOp op) {
        return (KindPayload.ClassNewPayload) op.payload();
    }

    private static KindPayload.ClassDefaultPayload defaultPayload(SemanticOp op) {
        return (KindPayload.ClassDefaultPayload) op.payload();
    }

    private static SemanticOp ageDefaultOf(LoweredModuleUnit callerUnit) {
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_DEFAULT)) {
            if (defaultPayload(op).classId().equals(PERSON_ID)
                    && "age".equals(defaultPayload(op).field())) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // The drive contexts
    // =========================================================================

    private record Drive(
        LoweredPair pair,
        LoweredModuleUnit ownerUnit,
        LoweredModuleUnit callerUnit,
        StructuredBodyTable ownerTable,
        StructuredBodyTable callerTable,
        Map<OpId, SemanticOp> ownerLookup,
        Map<OpId, SemanticOp> callerLookup,
        Map<ClassId, ClassLayout> layouts,
        Map<ValueId, Value> heap,
        Map<BindingId, Value> ownerBindings,
        Map<BindingId, Value> callerBindings,
        List<String> log,
        BodyRunner ownerRunner,
        BodyRunner callerRunner,
        Set<OpId> defaultBlockOps) {
    }

    private static Drive freshDrive(LoweredPair pair) {
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        StructuredBodyTable ownerTable = pair.owner().lowering().table();
        StructuredBodyTable callerTable = pair.caller().lowering().table();
        Map<OpId, SemanticOp> ownerLookup = new LinkedHashMap<>();
        for (SemanticOp op : ownerUnit.ops()) {
            ownerLookup.put(op.opId(), op);
        }
        Map<OpId, SemanticOp> callerLookup = new LinkedHashMap<>();
        for (SemanticOp op : callerUnit.ops()) {
            callerLookup.put(op.opId(), op);
        }
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>();
        layouts.putAll(ownerUnit.classLayouts());
        layouts.putAll(callerUnit.classLayouts());
        Map<ValueId, Value> heap = new LinkedHashMap<>();
        Map<BindingId, Value> ownerBindings = new LinkedHashMap<>();
        Map<BindingId, Value> callerBindings = new LinkedHashMap<>();
        List<String> log = new ArrayList<>();
        BoundaryCheckRunner real = realDelegate(log);

        // Seed the owner's module-level bindings (the declaring-scope
        // surface: the Address zip default resolves baseZip here, never
        // through the caller's bindings).
        for (SemanticOp op : ownerUnit.ops()) {
            switch (op.kind()) {
                case CONST -> heap.put((ValueId) op.result(), constValue(op));
                case BINDING_INIT -> {
                    KindPayload.BindingInitPayload init =
                        (KindPayload.BindingInitPayload) op.payload();
                    Value value = heap.get(init.value());
                    if (value != null) {
                        ownerBindings.put(init.binding(), value);
                    }
                }
                case BINDING_LOAD -> {
                    KindPayload.BindingLoadPayload load =
                        (KindPayload.BindingLoadPayload) op.payload();
                    Value value = ownerBindings.get(load.binding());
                    if (value != null) {
                        heap.put((ValueId) op.result(), value);
                    }
                }
                default -> {
                    // The owner's detached CLASS_DEFAULT/CLASS_FACTORY
                    // ops carry no seeding step.
                }
            }
        }

        // Seed the caller's CONST ops too (the provided literal values
        // every construction drive resolves from the heap).
        for (SemanticOp op : callerUnit.ops()) {
            if (op.kind() == SemanticOpKind.CONST) {
                Value constant = constValue(op);
                if (constant != null) {
                    heap.put((ValueId) op.result(), constant);
                }
            }
        }

        // The owner-side body runner (defaults evaluate in the declaring
        // module's scope); the holder breaks the self-reference.
        final BodyRunner[] ownerHolder = new BodyRunner[1];
        final BodyRunner[] callerHolder = new BodyRunner[1];
        ownerHolder[0] = defaultOpArg -> {
            log.add("owner-default " + defaultOpArg.opId());
            return runBlock(ownerUnit, ownerTable, defaultOpArg, heap, ownerBindings,
                layouts, pair.owner().registry(), ownerLookup, ownerLookup,
                ownerHolder[0], ownerHolder[0], real, log);
        };
        BodyRunner ownerRunner = ownerHolder[0];
        callerHolder[0] = defaultOpArg -> {
            log.add("caller-default " + defaultOpArg.opId());
            return runBlock(callerUnit, callerTable, defaultOpArg, heap, callerBindings,
                layouts, pair.owner().registry(), callerLookup, ownerLookup,
                callerHolder[0], ownerRunner, real, log);
        };
        BodyRunner callerRunner = callerHolder[0];

        // The CLASS_NEW ops nested inside default blocks (driven by the
        // block walker, never by the top-level loops).
        Set<OpId> defaultBlockOps = new LinkedHashSet<>();
        for (SemanticOp candidate : callerUnit.ops()) {
            if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                BlockId block = defaultPayload(candidate).defaultBlock();
                List<OpId> members = callerTable.blockOps().get(block);
                if (members != null) {
                    defaultBlockOps.addAll(members);
                }
            }
        }
        return new Drive(pair, ownerUnit, callerUnit, ownerTable, callerTable,
            ownerLookup, callerLookup, layouts, heap, ownerBindings, callerBindings, log,
            ownerRunner, callerRunner, defaultBlockOps);
    }

    // =========================================================================
    // The production delegates
    // =========================================================================

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
            case Value.Array array -> {
                List<BoundaryValueView> elementViews = new ArrayList<>();
                for (int i = 0; i < array.array().size(); i++) {
                    elementViews.add(valueView(array.array().elementAt(i)));
                }
                yield BoundaryValueView.ofArray(elementViews);
            }
            case Value.Class classValue -> BoundaryValueView.ofClass(classValue.classId().text());
            case Value.Function function -> BoundaryValueView.ofFunction(function.signature());
            case Value.Missing ignored -> BoundaryValueView.of(ActualKind.MISSING);
        };
    }

    private static Value publishValue(BoundaryValueView view, Value input) {
        return view.kind() == ActualKind.NULL ? Value.Null.INSTANCE : input;
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

    /**
     * The mini block interpreter of one detached default block: the
     * CONST, BINDING_LOAD, CLASS_NEW, ARRAY_NEW, and TABLE_NEW arms the
     * default blocks of this scenario carry (the E5 block machinery's
     * stand-in for the detached blocks; the production executor drives
     * every default block through the caller-supplied runner exactly
     * once per construction).
     */
    private static Value runBlock(LoweredModuleUnit unit, StructuredBodyTable table,
                                  SemanticOp defaultOp, Map<ValueId, Value> heap,
                                  Map<BindingId, Value> bindings,
                                  Map<ClassId, ClassLayout> layouts,
                                  ClassFactoryRegistry registry,
                                  Map<OpId, SemanticOp> ownLookup,
                                  Map<OpId, SemanticOp> ownerLookup,
                                  BodyRunner ownRunner, BodyRunner ownerRunner,
                                  BoundaryCheckRunner real, List<String> log) {
        KindPayload.ClassDefaultPayload payload = defaultPayload(defaultOp);
        List<OpId> block = table.blockOps().get(payload.defaultBlock());
        if (block == null) {
            throw new IllegalStateException("the default block of " + defaultOp.opId()
                + " is not in the produced table (producer defect)");
        }
        for (OpId listed : block) {
            SemanticOp op = opById(unit, listed);
            if (op == null) {
                continue;
            }
            switch (op.kind()) {
                case CONST -> {
                    Value value = constValue(op);
                    if (value != null) {
                        heap.put((ValueId) op.result(), value);
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
                    KindPayload.ClassNewPayload newPayload = classNewPayload(op);
                    Outcome<Value> outcome = newPayload.defaultOwner()
                        == DefaultOwner.SHARED_FACTORY
                            ? ClassOpsExecutor.executeClassNewSharedFactory(op, heap,
                                registry, ownerLookup,
                                resolveBoundaryOps(ownLookup, newPayload.fieldBoundaries()),
                                layouts, real, ownerRunner)
                            : ClassOpsExecutor.executeClassNewLocal(op, heap, ownLookup,
                                resolveBoundaryOps(ownLookup, newPayload.fieldBoundaries()),
                                layouts, real, ownRunner);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    } else {
                        throw new IllegalStateException("the default block's CLASS_NEW "
                            + "failed: " + outcome);
                    }
                }
                case ARRAY_NEW -> {
                    List<Value> elements = new ArrayList<>();
                    for (ValueId elementId
                            : ((KindPayload.ArrayNewPayload) op.payload()).values()) {
                        Value element = heap.get(elementId);
                        if (element == null) {
                            throw new IllegalStateException("the ARRAY_NEW operand "
                                + elementId + " is unresolvable (producer defect)");
                        }
                        elements.add(element);
                    }
                    heap.put((ValueId) op.result(),
                        new Value.Array(SemanticArray.of(elements)));
                }
                case TABLE_NEW -> {
                    KindPayload.TableNewPayload newPayload =
                        (KindPayload.TableNewPayload) op.payload();
                    SemanticTable<Value> built = new SemanticTable<>();
                    for (KindPayload.TableEntry entry : newPayload.entries()) {
                        Value entryValue = heap.get(entry.value());
                        if (entryValue == null) {
                            throw new IllegalStateException("the TABLE_NEW entry value "
                                + entry.value() + " is unresolvable (producer defect)");
                        }
                        built.put(entry.key(), entryValue);
                    }
                    heap.put((ValueId) op.result(), new Value.Table(built));
                }
                default -> {
                    // The CLASS_DEFAULT op itself and the BOUNDARY
                    // children (driven through the CLASS_NEW executor)
                    // carry no interpreter step here.
                }
            }
        }
        Value produced = heap.get((ValueId) defaultOp.result());
        if (produced == null) {
            throw new IllegalStateException("the default block of " + defaultOp.opId()
                + " produced no value for its result slot");
        }
        log.add("block-produced " + defaultOp.opId());
        return produced;
    }

    // =========================================================================
    // The construction drive (top-level CLASS_NEW ops only)
    // =========================================================================

    /**
     * Drives every top-level {@code CLASS_NEW} op of the caller in unit
     * order (the nested ones inside default blocks are the block
     * walker's), asserting success for each.
     */
    private static void driveConstructions(Drive drive) {
        for (SemanticOp op : drive.callerUnit().ops()) {
            if (op.kind() == SemanticOpKind.CONST) {
                Value constant = constValue(op);
                if (constant != null) {
                    drive.heap().put((ValueId) op.result(), constant);
                }
                continue;
            }
            if (op.kind() != SemanticOpKind.CLASS_NEW
                    || drive.defaultBlockOps().contains(op.opId())) {
                continue;
            }
            KindPayload.ClassNewPayload payload = classNewPayload(op);
            Outcome<Value> outcome = payload.defaultOwner() == DefaultOwner.SHARED_FACTORY
                ? ClassOpsExecutor.executeClassNewSharedFactory(op, drive.heap(),
                    drive.pair().owner().registry(), drive.ownerLookup(),
                    resolveBoundaryOps(drive.callerLookup(), payload.fieldBoundaries()),
                    drive.layouts(), realDelegate(drive.log()), drive.ownerRunner())
                : ClassOpsExecutor.executeClassNewLocal(op, drive.heap(),
                    resolveDefaultOps(drive.callerLookup(), payload.classDefaultOpIds()),
                    resolveBoundaryOps(drive.callerLookup(), payload.fieldBoundaries()),
                    drive.layouts(), realDelegate(drive.log()), drive.callerRunner());
            if (outcome instanceof Outcome.Success<Value> success) {
                drive.heap().put((ValueId) op.result(), success.value());
                continue;
            }
            fail("the top-level CLASS_NEW " + op.opId() + " failed: " + outcome);
        }
    }

    /** The "child ..." lines of one log in order. */
    private static List<String> childLines(List<String> log) {
        List<String> lines = new ArrayList<>();
        for (String line : log) {
            if (line.startsWith("child ")) {
                lines.add(line);
            }
        }
        return lines;
    }

    private static long countOf(List<String> log, String prefix) {
        long count = 0;
        for (String line : log) {
            if (line.startsWith(prefix)) {
                count++;
            }
        }
        return count;
    }

    // =========================================================================
    // The blanket field-op drive
    // =========================================================================

    /**
     * Drives the caller unit's field operations in unit order over the
     * constructed instances (the FieldOpsLoweringTest pattern with the
     * write/delete rebinding). Returns the {@code maybe.city} read
     * outcome — the cross-module nullable receiver read whose null
     * receiver must fail the nominal receiver boundary end-to-end.
     */
    private static Outcome<Value> driveFieldOps(Drive drive) {
        LoweredModuleUnit unit = drive.callerUnit();
        Outcome<Value> maybeCityRead = null;
        List<SemanticOp> reads = ofKind(unit, SemanticOpKind.FIELD_READ);
        SemanticOp maybeRead = reads.size() == 4 ? reads.get(2) : null;
        BoundaryCheckRunner real = realDelegate(drive.log());
        for (SemanticOp op : unit.ops()) {
            switch (op.kind()) {
                case CONST -> {
                    Value value = constValue(op);
                    if (value != null) {
                        drive.heap().put((ValueId) op.result(), value);
                    }
                }
                case BINDING_INIT -> {
                    KindPayload.BindingInitPayload init =
                        (KindPayload.BindingInitPayload) op.payload();
                    Value value = drive.heap().get(init.value());
                    if (value != null) {
                        drive.callerBindings().put(init.binding(), value);
                    }
                }
                case BINDING_LOAD -> {
                    KindPayload.BindingLoadPayload load =
                        (KindPayload.BindingLoadPayload) op.payload();
                    Value value = drive.callerBindings().get(load.binding());
                    if (value != null) {
                        drive.heap().put((ValueId) op.result(), value);
                    }
                }
                case CLASS_NEW -> {
                    if (drive.defaultBlockOps().contains(op.opId())) {
                        break;
                    }
                    KindPayload.ClassNewPayload payload = classNewPayload(op);
                    Outcome<Value> outcome = payload.defaultOwner()
                        == DefaultOwner.SHARED_FACTORY
                            ? ClassOpsExecutor.executeClassNewSharedFactory(op, drive.heap(),
                                drive.pair().owner().registry(), drive.ownerLookup(),
                                resolveBoundaryOps(drive.callerLookup(),
                                    payload.fieldBoundaries()),
                                drive.layouts(), real, drive.ownerRunner())
                            : ClassOpsExecutor.executeClassNewLocal(op, drive.heap(),
                                resolveDefaultOps(drive.callerLookup(),
                                    payload.classDefaultOpIds()),
                                resolveBoundaryOps(drive.callerLookup(),
                                    payload.fieldBoundaries()),
                                drive.layouts(), real, drive.callerRunner());
                    if (outcome instanceof Outcome.Success<Value> success) {
                        drive.heap().put((ValueId) op.result(), success.value());
                    } else {
                        fail("the blanket CLASS_NEW " + op.opId() + " failed: " + outcome);
                    }
                }
                case FIELD_WRITE -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 2) {
                        fail("the FIELD_WRITE op has " + children.size()
                            + " boundary children (expected 2)");
                        break;
                    }
                    KindPayload.FieldWritePayload write =
                        (KindPayload.FieldWritePayload) op.payload();
                    Value oldInstance = drive.heap().get(write.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldWrite(op,
                        drive.heap(), children.get(0), children.get(1), drive.layouts(),
                        real);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        rebind(drive.heap(), drive.callerBindings(), oldInstance,
                            success.value());
                    } else {
                        fail("the blanket FIELD_WRITE failed: " + outcome);
                    }
                }
                case FIELD_READ -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 2) {
                        fail("the FIELD_READ op has " + children.size()
                            + " boundary children (expected 2)");
                        break;
                    }
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldRead(op,
                        drive.heap(), children.get(0), children.get(1), drive.layouts(),
                        real);
                    if (op == maybeRead) {
                        maybeCityRead = outcome;
                    } else if (outcome instanceof Outcome.Success<Value> success) {
                        drive.heap().put((ValueId) op.result(), success.value());
                    } else {
                        fail("the blanket FIELD_READ failed: " + outcome);
                    }
                }
                case FIELD_DELETE -> {
                    List<SemanticOp> children = childrenOf(unit, op);
                    if (children.size() != 1) {
                        fail("the FIELD_DELETE op has " + children.size()
                            + " boundary children (expected 1)");
                        break;
                    }
                    KindPayload.FieldDeletePayload delete =
                        (KindPayload.FieldDeletePayload) op.payload();
                    Value oldInstance = drive.heap().get(delete.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldDelete(op,
                        drive.heap(), children.get(0), drive.layouts(), real);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        rebind(drive.heap(), drive.callerBindings(), oldInstance,
                            success.value());
                    } else {
                        fail("the blanket FIELD_DELETE failed: " + outcome);
                    }
                }
                case HAS_FIELD -> {
                    Outcome<Value> outcome = ClassOpsExecutor.executeHasField(op,
                        drive.heap(), drive.layouts());
                    if (outcome instanceof Outcome.Success<Value> success) {
                        drive.heap().put((ValueId) op.result(), success.value());
                    } else {
                        fail("the blanket HAS_FIELD failed: " + outcome);
                    }
                }
                default -> {
                    // BINDING_ALLOC, detached CLASS_DEFAULT/CLASS_FACTORY,
                    // JSON generated bodies, and the chain ops carry no
                    // interpreter step in this drive.
                }
            }
        }
        return maybeCityRead;
    }

    /** Rebinds every reference holding the old instance to the updated one. */
    private static void rebind(Map<ValueId, Value> heap,
                               Map<BindingId, Value> bindings,
                               Value oldInstance, Value updated) {
        for (Map.Entry<ValueId, Value> entry : new ArrayList<>(heap.entrySet())) {
            if (oldInstance.equals(entry.getValue())) {
                heap.put(entry.getKey(), updated);
            }
        }
        for (Map.Entry<BindingId, Value> entry : new ArrayList<>(bindings.entrySet())) {
            if (oldInstance.equals(entry.getValue())) {
                bindings.put(entry.getKey(), updated);
            }
        }
    }

    // =========================================================================
    // Op rebuild (payload tampering for the E8007/failure arms)
    // =========================================================================

    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, op.kind(), op.resultType(),
            op.operandTypes(), selector, payload, op.failurePolicy(), List.of(),
            "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = new OperationContractSnapshot(OperationContractSnapshot.VERSION,
            op.kind(), op.resultType(), op.operandTypes(), selector, payload,
            op.failurePolicy(), List.of(), digest);
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload, op.failurePolicy(),
            contract);
    }

    private static KindPayload.ClassNewPayload withProvided(
            KindPayload.ClassNewPayload original,
            List<KindPayload.ProvidedField> providedFields) {
        return new KindPayload.ClassNewPayload(original.classId(), original.layout(),
            providedFields, original.defaultOwner(), original.classDefaultOpIds(),
            original.classFactoryRef(), original.fieldBoundaries());
    }

    private static KindPayload.ClassNewPayload withDefaults(
            KindPayload.ClassNewPayload original, List<OpId> classDefaultOpIds) {
        return new KindPayload.ClassNewPayload(original.classId(), original.layout(),
            original.providedFields(), original.defaultOwner(), classDefaultOpIds,
            original.classFactoryRef(), original.fieldBoundaries());
    }

    // =========================================================================
    // Instance builders (the defective-instance failure arms)
    // =========================================================================

    private static Value.Class addressInstance(Value city, Value zip) {
        return new Value.Class(ADDRESS_ID, List.of(
            new FieldState.Present(city), new FieldState.Present(zip)));
    }

    private static Value.Class personInstance(ClassLayout layout, FieldState name,
                                              FieldState age, FieldState ratio,
                                              FieldState home, FieldState note,
                                              FieldState meta) {
        return new Value.Class(layout.classId(),
            List.of(name, age, ratio, home, note, meta));
    }

    private static Value validMeta() {
        SemanticTable<Value> table = new SemanticTable<>();
        table.put("k", Value.string("v"));
        return new Value.Table(table);
    }

    private static Value.Class validPerson(ClassLayout personLayout, Value home,
                                           Value meta, FieldState note) {
        return personInstance(personLayout,
            new FieldState.Present(Value.string("anon")),
            new FieldState.Present(new Value.Int(7)),
            new FieldState.Present(new Value.Number(0.5)),
            new FieldState.Present(home), note, new FieldState.Present(meta));
    }

    private static Value.Class validHome() {
        return addressInstance(Value.string("berlin"), new Value.Int(10115));
    }

    /** The present value of the declared field {@code name}, or null when absent. */
    private static Value fieldValue(Value.Class instance, ClassLayout layout, String name) {
        for (int i = 0; i < layout.fields().size(); i++) {
            if (layout.fields().get(i).name().equals(name)) {
                FieldState state = instance.fields().get(i);
                return state instanceof FieldState.Present present
                    ? present.value() : null;
            }
        }
        return null;
    }

    private static String carrier(Value.String string) {
        return ((UnicodeScalars.Valid) string.scalar()).carrier();
    }

    private static Value heapValue(Drive drive, ValueId id) {
        return drive.heap().get(id);
    }

    // =========================================================================
    // 1. Pipeline facts and determinism
    // =========================================================================

    private static void testPipelineFacts(LoweredPair pair) {
        System.out.println("-- pipeline facts: layouts, factories, defaults, JSON ops, "
            + "determinism --");
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        check(ownerUnit.classLayouts().containsKey(ADDRESS_ID)
                && ownerUnit.classLayouts().containsKey(BAG_ID),
            "the owner unit carries the Address and Bag layouts");
        check(callerUnit.classLayouts().containsKey(PERSON_ID)
                && callerUnit.classLayouts().containsKey(STRICT_ID),
            "the caller unit carries the Person and Strict layouts");
        check(pair.owner().registry().factories().size() == 2,
            "the owner registry registers exactly two exported-class factories; got "
                + pair.owner().registry().factories().size());
        check(ofKind(ownerUnit, SemanticOpKind.CLASS_DEFAULT).size() == 4,
            "the owner emits four CLASS_DEFAULT ops (city, zip, tags, meta); got "
                + ofKind(ownerUnit, SemanticOpKind.CLASS_DEFAULT).size());
        check(ofKind(callerUnit, SemanticOpKind.CLASS_DEFAULT).size() == 5,
            "the caller emits five CLASS_DEFAULT ops (name, age, ratio, home, meta); got "
                + ofKind(callerUnit, SemanticOpKind.CLASS_DEFAULT).size());
        check(ofKind(callerUnit, SemanticOpKind.CLASS_NEW).size() == 8,
            "the caller emits eight CLASS_NEW ops (six top-level literals, the "
                + "q-home provided literal, and the home default block's nested "
                + "literal); got " + ofKind(callerUnit, SemanticOpKind.CLASS_NEW).size());
        check(ofKind(callerUnit, SemanticOpKind.JSON_FROM_CLASS).size() == 2
                && ofKind(callerUnit, SemanticOpKind.JSON_TO_CLASS).size() == 2,
            "the caller emits two JSON_FROM_CLASS and two JSON_TO_CLASS ops (Person, "
                + "Strict)");
        check(ofKind(callerUnit, SemanticOpKind.CLASS_FACTORY).size() == 2,
            "the caller emits two CLASS_FACTORY ops for its exported classes");
        check(ofKind(callerUnit, SemanticOpKind.FIELD_READ).size() == 4
                && ofKind(callerUnit, SemanticOpKind.FIELD_WRITE).size() == 2
                && ofKind(callerUnit, SemanticOpKind.FIELD_DELETE).size() == 1
                && ofKind(callerUnit, SemanticOpKind.HAS_FIELD).size() == 3,
            "the caller emits the four reads, two writes, one delete, and three has "
                + "probes of the scenario");

        // The Address zip default's declaring-scope surface: its block
        // carries the BINDING_LOAD of the owner's module-level baseZip.
        boolean zipBindingLoad = false;
        for (SemanticOp op : ofKind(ownerUnit, SemanticOpKind.CLASS_DEFAULT)) {
            if (!"zip".equals(defaultPayload(op).field())) {
                continue;
            }
            for (OpId listed : pair.owner().lowering().table().blockOps()
                    .getOrDefault(defaultPayload(op).defaultBlock(), List.of())) {
                SemanticOp blockOp = opById(ownerUnit, listed);
                if (blockOp != null && blockOp.kind() == SemanticOpKind.BINDING_LOAD) {
                    zipBindingLoad = true;
                }
            }
        }
        check(zipBindingLoad,
            "the owner's zip default block carries the module-level BINDING_LOAD (the "
                + "declaring module's scope surface)");

        // Determinism: a second lowering of both modules is byte-identical.
        LoweredPair second = lowerPair();
        check(second != null, "the second repetition lowers");
        if (second != null) {
            check(Arrays.equals(
                    SemanticIrDumper.dumpModule(pair.owner().lowering().unit()),
                    SemanticIrDumper.dumpModule(second.owner().lowering().unit())),
                "the owner dump is byte-identical across repetitions");
            check(Arrays.equals(
                    SemanticIrDumper.dumpModule(pair.caller().lowering().unit()),
                    SemanticIrDumper.dumpModule(second.caller().lowering().unit())),
                "the caller dump is byte-identical across repetitions");
        }
    }

    // =========================================================================
    // 2. Local construction order + the complete-instance publication
    // =========================================================================

    private static void testLocalConstruction(LoweredPair pair) {
        System.out.println("-- local construction: literal order, omitted defaults, "
            + "declaration-order validation, complete tagged instances only --");
        Drive drive = freshDrive(pair);
        driveConstructions(drive);
        LoweredModuleUnit callerUnit = drive.callerUnit();

        List<SemanticOp> personNews = new ArrayList<>();
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            if (classNewPayload(op).classId().equals(PERSON_ID)
                    && !drive.defaultBlockOps().contains(op.opId())) {
                personNews.add(op);
            }
        }
        check(personNews.size() == 2, "two top-level Person CLASS_NEW ops (p, q); got "
            + personNews.size());
        if (personNews.size() != 2) {
            return;
        }
        SemanticOp p = personNews.get(0);
        SemanticOp q = personNews.get(1);
        SemanticOp qHome = null;
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            if (drive.defaultBlockOps().contains(op.opId())) {
                continue;
            }
            KindPayload.ClassNewPayload payload = classNewPayload(op);
            if (payload.classId().equals(ADDRESS_ID)
                    && payload.providedFields().size() == 2
                    && payload.providedFields().get(0).name().equals("city")
                    && payload.providedFields().get(1).name().equals("zip")) {
                qHome = op;
            }
        }
        check(qHome != null, "the q-home provided literal resolves (an Address "
            + "construction with the city,zip literal order)");
        KindPayload.ClassNewPayload pPayload = classNewPayload(p);
        KindPayload.ClassNewPayload qPayload = classNewPayload(q);

        check(pPayload.defaultOwner() == DefaultOwner.LOCAL
                && pPayload.providedFields().size() == 1
                && pPayload.providedFields().get(0).name().equals("age"),
            "p's payload carries the provided age in literal order, defaultOwner LOCAL");
        List<String> pDefaults = new ArrayList<>();
        for (OpId id : pPayload.classDefaultOpIds()) {
            pDefaults.add(defaultPayload(drive.callerLookup().get(id)).field());
        }
        check(pDefaults.equals(List.of("name", "ratio", "home", "meta")),
            "p's classDefaultOpIds name only the omitted required-present defaulted "
                + "fields in declaration order (name, ratio, home, meta); got " + pDefaults);
        List<String> pBoundaries = new ArrayList<>();
        for (KindPayload.FieldBoundary entry : pPayload.fieldBoundaries()) {
            pBoundaries.add(entry.field() + ":" + entry.kind());
        }
        check(pBoundaries.equals(List.of("name:CLASS_DEFAULT_FIELD",
                "age:CLASS_LITERAL_FIELD", "ratio:CLASS_DEFAULT_FIELD",
                "home:CLASS_DEFAULT_FIELD", "meta:CLASS_DEFAULT_FIELD")),
            "p's field boundaries run in declaration order with the pinned kinds; got "
                + pBoundaries);
        check(qPayload.providedFields().size() == 3
                && qPayload.providedFields().get(0).name().equals("name")
                && qPayload.providedFields().get(1).name().equals("age")
                && qPayload.providedFields().get(2).name().equals("home"),
            "q's payload records the provided fields in literal order (name, age, home)");
        List<String> qBoundaries = new ArrayList<>();
        for (KindPayload.FieldBoundary entry : qPayload.fieldBoundaries()) {
            qBoundaries.add(entry.field() + ":" + entry.kind());
        }
        check(qBoundaries.equals(List.of("name:CLASS_LITERAL_FIELD",
                "age:CLASS_LITERAL_FIELD", "ratio:CLASS_DEFAULT_FIELD",
                "home:CLASS_LITERAL_FIELD", "meta:CLASS_DEFAULT_FIELD")),
            "q's field boundaries run in declaration order with the pinned kinds; got "
                + qBoundaries);

        // The complete construction-order assertion: the global "child"
        // sequence reproduces the pinned per-construction declaration
        // order across all seven driven constructions.
        List<String> expected = List.of(
            "child CLASS_LITERAL_FIELD <- string",    // addr city
            "child CLASS_LITERAL_FIELD <- int",       // addr zip
            "child CLASS_DEFAULT_FIELD <- string",    // emptyAddr city
            "child CLASS_DEFAULT_FIELD <- int",       // emptyAddr zip
            "child CLASS_DEFAULT_FIELD <- array",     // bag1 tags
            "child CLASS_DEFAULT_FIELD <- table",     // bag1 meta
            "child CLASS_DEFAULT_FIELD <- array",     // bag2 tags
            "child CLASS_DEFAULT_FIELD <- table",     // bag2 meta
            "child CLASS_LITERAL_FIELD <- string",    // p home nested city (seed)
            "child CLASS_DEFAULT_FIELD <- int",       // p home nested zip (owner factory)
            "child CLASS_DEFAULT_FIELD <- string",    // p name
            "child CLASS_LITERAL_FIELD <- int",       // p age
            "child CLASS_DEFAULT_FIELD <- number",    // p ratio
            "child CLASS_DEFAULT_FIELD <- class:@owner/Address",  // p home
            "child CLASS_DEFAULT_FIELD <- table",     // p meta
            "child CLASS_LITERAL_FIELD <- string",    // qHome city
            "child CLASS_LITERAL_FIELD <- int",       // qHome zip
            "child CLASS_LITERAL_FIELD <- string",    // q name
            "child CLASS_LITERAL_FIELD <- int",       // q age
            "child CLASS_DEFAULT_FIELD <- number",    // q ratio
            "child CLASS_LITERAL_FIELD <- class:@owner/Address",  // q home
            "child CLASS_DEFAULT_FIELD <- table");    // q meta
        check(childLines(drive.log()).equals(expected),
            "the construction drives validate fields in declaration order end-to-end "
                + "(the exact boundary sequence); got " + childLines(drive.log()));
        check(countOf(drive.log(), "caller-default ") == 6,
            "the caller's default blocks ran exactly six times (p: name/ratio/home/"
                + "meta; q: ratio/meta — the provided age default never ran); got "
                + countOf(drive.log(), "caller-default "));
        check(countOf(drive.log(), "owner-default ") == 7,
            "the owner's default blocks ran exactly seven times (emptyAddr city/zip, "
                + "bag1 tags/meta, bag2 tags/meta, p-home-nested zip); got "
                + countOf(drive.log(), "owner-default "));

        // The published instances: p and q are distinct, tagged, complete.
        Value.Class pInstance = (Value.Class) heapValue(drive, (ValueId) p.result());
        Value.Class qInstance = (Value.Class) heapValue(drive, (ValueId) q.result());
        ClassLayout personLayout = drive.layouts().get(PERSON_ID);
        check(pInstance != null && qInstance != null && pInstance != qInstance,
            "p and q publish distinct fresh instances");
        check(pInstance != null && pInstance.classId().equals(PERSON_ID)
                && qInstance != null && qInstance.classId().equals(PERSON_ID),
            "both instances carry the canonical classId tag");
        check(pInstance != null && fieldValue(pInstance, personLayout, "name")
                instanceof Value.String name && carrier(name).equals("anon")
                && fieldValue(pInstance, personLayout, "age") instanceof Value.Int age
                    && age.value() == 7
                && fieldValue(pInstance, personLayout, "ratio") instanceof Value.Number ratio
                    && ratio.value() == 0.5,
            "p publishes the complete tagged instance (defaults + the provided age)");
        check(pInstance != null
                && fieldValue(pInstance, personLayout, "home") instanceof Value.Class home
                    && home.classId().equals(ADDRESS_ID),
            "p's home default published the nested Address instance");
        check(pInstance != null && fieldValue(pInstance, personLayout, "note") == null,
            "p's omitted optional note stays missing");
        check(qInstance != null && fieldValue(qInstance, personLayout, "name")
                instanceof Value.String qName && carrier(qName).equals("bob")
                && fieldValue(qInstance, personLayout, "home") instanceof Value.Class qHomeV
                    && fieldValue(qHomeV, drive.layouts().get(ADDRESS_ID), "city")
                        instanceof Value.String city && carrier(city).equals("x"),
            "q publishes the provided fields overlaid in declaration order");

        // The skip-provided arm: rebuild p with the age CLASS_DEFAULT child
        // also listed — the executor skips it because age is provided.
        final SemanticOp ageDefault = ageDefaultOf(callerUnit);
        check(ageDefault != null, "the age CLASS_DEFAULT op resolves");
        if (ageDefault != null) {
            List<OpId> expanded = new ArrayList<>(pPayload.classDefaultOpIds());
            expanded.add(1, ageDefault.opId());
            SemanticOp expandedOp = rebuild(p, withDefaults(pPayload, expanded));
            List<String> freshLog = new ArrayList<>();
            Drive skipDrive = freshDrive(pair);
            Outcome<Value> outcome = ClassOpsExecutor.executeClassNewLocal(expandedOp,
                skipDrive.heap(), resolveDefaultOps(skipDrive.callerLookup(), expanded),
                resolveBoundaryOps(skipDrive.callerLookup(), pPayload.fieldBoundaries()),
                skipDrive.layouts(), realDelegate(freshLog), skipDrive.callerRunner());
            check(outcome instanceof Outcome.Success<Value>,
                "the expanded-defaults construction still succeeds; got " + outcome);
            check(skipDrive.log().stream().noneMatch(line -> line.equals("caller-default "
                        + ageDefault.opId())),
                "the provided age's default block never ran (the skip-provided rule "
                    + "through the pipeline)");
            check(countOf(skipDrive.log(), "caller-default ") == 4,
                "the other four omitted defaults still ran exactly once each; got "
                    + countOf(skipDrive.log(), "caller-default "));
        }

        // The no-partial-instance arm: a failing field boundary publishes
        // nothing and stops validation at the first failing field.
        Map<ValueId, Value> tampered = new LinkedHashMap<>(drive.heap());
        tampered.put(pPayload.providedFields().get(0).valueOpId(),
            Value.string("wrong"));
        List<String> failureLog = new ArrayList<>();
        Outcome<Value> failing = ClassOpsExecutor.executeClassNewLocal(p, tampered,
            resolveDefaultOps(drive.callerLookup(), pPayload.classDefaultOpIds()),
            resolveBoundaryOps(drive.callerLookup(), pPayload.fieldBoundaries()),
            drive.layouts(), realDelegate(failureLog), drive.callerRunner());
        check(failing instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message().equals("expected int, got string")
                && failure.failure().origin().equals(p.origin()),
            "the tampered age fails the declaration-order boundary with the exact "
                + "E8001 at the op origin; got " + failing);
        List<String> boundaryOrder = childLines(failureLog);
        check(boundaryOrder.size() == 2
                && boundaryOrder.get(0).equals("child CLASS_DEFAULT_FIELD <- string")
                && boundaryOrder.get(1).equals("child CLASS_LITERAL_FIELD <- string"),
            "validation stopped at the first failing field (name passed, age failed, "
                + "ratio/home/meta never ran); got " + boundaryOrder);
    }

    // =========================================================================
    // 3. The E8007 extra-key arm (LOCAL and SHARED_FACTORY)
    // =========================================================================

    private static void testExtraKeyE8007(LoweredPair pair) {
        System.out.println("-- E8007: the first extra key in provided-source order, "
            + "after completed default application, before any provided application "
            + "or validation --");
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();

        // (a) the LOCAL arm: p with two injected extra provided fields.
        SemanticOp p = null;
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            KindPayload.ClassNewPayload payload = classNewPayload(op);
            if (payload.classId().equals(PERSON_ID) && payload.providedFields().size() == 1) {
                p = op;
            }
        }
        check(p != null, "the p CLASS_NEW op resolves");
        if (p == null) {
            return;
        }
        KindPayload.ClassNewPayload pPayload = classNewPayload(p);
        ValueId zzz = new ValueId(777_001);
        ValueId yyy = new ValueId(777_002);
        List<KindPayload.ProvidedField> injected = new ArrayList<>(
            pPayload.providedFields());
        injected.add(new KindPayload.ProvidedField("zzz", zzz));
        injected.add(new KindPayload.ProvidedField("yyy", yyy));
        SemanticOp injectedOp = rebuild(p, withProvided(pPayload, injected));
        Drive localDrive = freshDrive(pair);
        localDrive.heap().put(zzz, Value.string("zz"));
        localDrive.heap().put(yyy, Value.string("yy"));
        List<String> localLog = new ArrayList<>();
        Outcome<Value> localOutcome = ClassOpsExecutor.executeClassNewLocal(injectedOp,
            localDrive.heap(),
            resolveDefaultOps(localDrive.callerLookup(), pPayload.classDefaultOpIds()),
            resolveBoundaryOps(localDrive.callerLookup(), pPayload.fieldBoundaries()),
            localDrive.layouts(), realDelegate(localLog), localDrive.callerRunner());
        check(localOutcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8007
                && failure.failure().failure().message().equals(
                    "extra field 'zzz' in class '@main/Person'")
                && failure.failure().origin().equals(p.origin()),
            "the LOCAL construction fails E8007 with the exact template at the op "
                + "origin, reporting the first extra key in provided-source order; got "
                + localOutcome);
        check(countOf(localDrive.log(), "caller-default ") == 4,
            "default application completed before the scan (all four omitted defaults "
                + "ran); got " + countOf(localDrive.log(), "caller-default "));
        check(childLines(localLog).isEmpty(),
            "no provided application or field validation ran after the scan; got "
                + childLines(localLog));

        // (b) the SHARED_FACTORY arm: emptyAddr with an injected extra key —
        // the owner factory transfer completes first, then E8007.
        SemanticOp emptyAddr = null;
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            KindPayload.ClassNewPayload payload = classNewPayload(op);
            if (payload.classId().equals(ADDRESS_ID)
                    && payload.providedFields().isEmpty()) {
                emptyAddr = op;
            }
        }
        check(emptyAddr != null, "the emptyAddr CLASS_NEW op resolves");
        if (emptyAddr == null) {
            return;
        }
        KindPayload.ClassNewPayload emptyPayload = classNewPayload(emptyAddr);
        SemanticOp injectedEmpty = rebuild(emptyAddr, withProvided(emptyPayload,
            List.of(new KindPayload.ProvidedField("zzz", zzz))));
        Drive sharedDrive = freshDrive(pair);
        sharedDrive.heap().put(zzz, Value.string("zz"));
        List<String> sharedLog = new ArrayList<>();
        Outcome<Value> sharedOutcome = ClassOpsExecutor.executeClassNewSharedFactory(
            injectedEmpty, sharedDrive.heap(), pair.owner().registry(),
            sharedDrive.ownerLookup(),
            resolveBoundaryOps(sharedDrive.callerLookup(), emptyPayload.fieldBoundaries()),
            sharedDrive.layouts(), realDelegate(sharedLog), sharedDrive.ownerRunner());
        check(sharedOutcome instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8007
                && failure.failure().failure().message().equals(
                    "extra field 'zzz' in class '@owner/Address'")
                && failure.failure().origin().equals(emptyAddr.origin()),
            "the SHARED_FACTORY construction fails E8007 with the exact template at "
                + "the op origin; got " + sharedOutcome);
        check(countOf(sharedDrive.log(), "owner-default ") == 2,
            "the owner factory transfer completed before the scan (both omitted "
                + "defaults ran in the declaring module); got "
                + countOf(sharedDrive.log(), "owner-default "));
        check(childLines(sharedLog).isEmpty(),
            "no field validation ran after the scan; got " + childLines(sharedLog));
    }

    // =========================================================================
    // 4. Imported construction: the owner factory, the declaring scope,
    //    and the caller's provided-field order
    // =========================================================================

    private static void testImportedConstruction(LoweredPair pair) {
        System.out.println("-- imported construction: the owner factory trigger, "
            + "defaults in the declaring module's scope, caller provided order --");
        Drive drive = freshDrive(pair);
        driveConstructions(drive);
        LoweredModuleUnit callerUnit = drive.callerUnit();

        SemanticOp addr = null;
        SemanticOp emptyAddr = null;
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            KindPayload.ClassNewPayload payload = classNewPayload(op);
            if (!payload.classId().equals(ADDRESS_ID)
                    || drive.defaultBlockOps().contains(op.opId())) {
                continue;
            }
            if (payload.providedFields().size() == 2
                    && payload.providedFields().get(0).name().equals("zip")
                    && payload.providedFields().get(1).name().equals("city")) {
                addr = op;
            } else if (payload.providedFields().isEmpty()) {
                emptyAddr = op;
            }
        }
        check(addr != null && emptyAddr != null, "the addr and emptyAddr ops resolve");
        if (addr == null || emptyAddr == null) {
            return;
        }
        KindPayload.ClassNewPayload addrPayload = classNewPayload(addr);
        SharedFactoryFacts facts = pair.facts().get(ADDRESS_ID);
        check(facts != null
                && addrPayload.defaultOwner() == DefaultOwner.SHARED_FACTORY
                && addrPayload.classFactoryRef().equals(
                    facts.interfaceEntry().constructionEntry())
                && addrPayload.classDefaultOpIds().isEmpty(),
            "addr carries the pinned SHARED_FACTORY payload (the interface's "
                + "constructionEntry, empty default list)");
        check(addrPayload.providedFields().get(0).name().equals("zip")
                && addrPayload.providedFields().get(1).name().equals("city"),
            "addr's providedFields keep the literal order (zip, city — the reverse of "
                + "declaration order)");
        List<String> addrBoundaries = new ArrayList<>();
        for (KindPayload.FieldBoundary entry : addrPayload.fieldBoundaries()) {
            addrBoundaries.add(entry.field() + ":" + entry.kind());
        }
        check(addrBoundaries.equals(List.of("city:CLASS_LITERAL_FIELD",
                "zip:CLASS_LITERAL_FIELD")),
            "addr's boundaries run in declaration order (city, zip) — the overlay "
                + "reorder source of the jvm-xmod-class-construction-defaults pin; got "
                + addrBoundaries);

        ClassLayout addressLayout = drive.layouts().get(ADDRESS_ID);
        Value.Class addrInstance = (Value.Class) heapValue(drive, (ValueId) addr.result());
        Value.Class emptyInstance =
            (Value.Class) heapValue(drive, (ValueId) emptyAddr.result());
        check(addrInstance != null && addrInstance.classId().equals(ADDRESS_ID)
                && fieldValue(addrInstance, addressLayout, "city")
                    instanceof Value.String city && carrier(city).equals("munich")
                && fieldValue(addrInstance, addressLayout, "zip")
                    instanceof Value.Int zip && zip.value() == 9,
            "addr publishes the provided fields overlaid in declaration order");
        check(emptyInstance != null && emptyInstance.classId().equals(ADDRESS_ID)
                && fieldValue(emptyInstance, addressLayout, "city")
                    instanceof Value.String city && carrier(city).equals("berlin")
                && fieldValue(emptyInstance, addressLayout, "zip")
                    instanceof Value.Int zip && zip.value() == 10115,
            "emptyAddr's omitted defaults came from the owner's factory — including "
                + "zip = the owner's module-level baseZip (the declaring module's "
                + "scope: only the owner's bindings resolve it)");
        check(drive.log().stream().filter(line -> line.startsWith("owner-default "))
                .count() >= 4,
            "the owner factory ran for the imported constructions (city/zip per "
                + "construction)");
    }

    // =========================================================================
    // 5. Mutable-default freshness per construction
    // =========================================================================

    private static void testMutableDefaultFreshness(LoweredPair pair) {
        System.out.println("-- mutable-default freshness: fresh array/table identities "
            + "per construction, imported and local --");
        Drive drive = freshDrive(pair);
        driveConstructions(drive);
        LoweredModuleUnit callerUnit = drive.callerUnit();

        List<SemanticOp> bagNews = new ArrayList<>();
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            if (classNewPayload(op).classId().equals(BAG_ID)
                    && !drive.defaultBlockOps().contains(op.opId())) {
                bagNews.add(op);
            }
        }
        check(bagNews.size() == 2, "two top-level Bag constructions; got " + bagNews.size());
        if (bagNews.size() != 2) {
            return;
        }
        Value.Class bag1 = (Value.Class) heapValue(drive, (ValueId) bagNews.get(0).result());
        Value.Class bag2 = (Value.Class) heapValue(drive, (ValueId) bagNews.get(1).result());
        ClassLayout bagLayout = drive.layouts().get(BAG_ID);
        check(bag1 != null && bag2 != null, "both Bag constructions published instances");
        if (bag1 == null || bag2 == null) {
            return;
        }
        Value tags1 = fieldValue(bag1, bagLayout, "tags");
        Value tags2 = fieldValue(bag2, bagLayout, "tags");
        Value meta1 = fieldValue(bag1, bagLayout, "meta");
        Value meta2 = fieldValue(bag2, bagLayout, "meta");
        check(tags1 instanceof Value.Array a1 && tags2 instanceof Value.Array a2
                && tags1 != tags2,
            "the two constructions published distinct fresh array default identities");
        check(meta1 instanceof Value.Table t1 && meta2 instanceof Value.Table t2
                && meta1 != meta2,
            "the two constructions published distinct fresh table default identities");
        if (tags1 instanceof Value.Array a1) {
            check(a1.array().size() == 2
                    && a1.array().elementAt(0).equals(new Value.Int(1))
                    && a1.array().elementAt(1).equals(new Value.Int(2)),
                "the fresh array default carries the literal contents [1, 2]");
        }
        if (meta1 instanceof Value.Table t1 && meta2 instanceof Value.Table t2) {
            check(switch (t1.table().get("seed")) {
                    case SemanticTable.Lookup.Present<Value> present ->
                        present.value().equals(Value.string("s"));
                    case SemanticTable.Lookup.Missing<Value> ignored -> false;
                }
                && switch (t2.table().get("seed")) {
                    case SemanticTable.Lookup.Present<Value> present ->
                        present.value().equals(Value.string("s"));
                    case SemanticTable.Lookup.Missing<Value> ignored -> false;
                },
                "both fresh table defaults carry the equal literal contents");
        }

        // The local arm: Person.meta defaults are fresh per construction too.
        List<SemanticOp> personNews = new ArrayList<>();
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            if (classNewPayload(op).classId().equals(PERSON_ID)
                    && !drive.defaultBlockOps().contains(op.opId())
                    && classNewPayload(op).providedFields().size() == 3) {
                personNews.add(op);
            }
        }
        check(personNews.size() == 1, "exactly one top-level Person full literal (q); got "
            + personNews.size());
        if (personNews.size() != 1) {
            return;
        }
        Value.Class q = (Value.Class) heapValue(drive, (ValueId) personNews.get(0).result());
        ClassLayout personLayout = drive.layouts().get(PERSON_ID);
        List<SemanticOp> pTop = new ArrayList<>();
        for (SemanticOp op : ofKind(callerUnit, SemanticOpKind.CLASS_NEW)) {
            if (classNewPayload(op).classId().equals(PERSON_ID)
                    && !drive.defaultBlockOps().contains(op.opId())
                    && classNewPayload(op).providedFields().size() == 1) {
                pTop.add(op);
            }
        }
        Value.Class pInstance = pTop.isEmpty() ? null
            : (Value.Class) heapValue(drive, (ValueId) pTop.get(0).result());
        check(pInstance != null && q != null
                && fieldValue(pInstance, personLayout, "meta") instanceof Value.Table pm
                && fieldValue(q, personLayout, "meta") instanceof Value.Table qm
                && fieldValue(pInstance, personLayout, "meta") != fieldValue(q, personLayout,
                    "meta"),
            "p and q published distinct fresh local table-default identities");
    }

    // =========================================================================
    // 6. Field presence states and the exact identity/type failures
    // =========================================================================

    private static void testFieldPresenceAndFailures(LoweredPair pair) {
        System.out.println("-- field operations: the three presence states and the "
            + "exact identity/type failures without re-evaluation --");
        Drive drive = freshDrive(pair);
        Outcome<Value> maybeCityRead = driveFieldOps(drive);
        LoweredModuleUnit callerUnit = drive.callerUnit();
        List<SemanticOp> reads = ofKind(callerUnit, SemanticOpKind.FIELD_READ);
        List<SemanticOp> hasOps = ofKind(callerUnit, SemanticOpKind.HAS_FIELD);
        check(reads.size() == 4 && hasOps.size() == 3,
            "the four reads and three has probes resolve");

        // The presence matrix over p.note: write value -> present, write
        // null -> present null, delete -> missing; has distinguishes them.
        Value hasNote = heapValue(drive, (ValueId) hasOps.get(0).result());
        Value hasNull = heapValue(drive, (ValueId) hasOps.get(1).result());
        Value hasAfter = heapValue(drive, (ValueId) hasOps.get(2).result());
        Value readNote = heapValue(drive, (ValueId) reads.get(0).result());
        Value readNull = heapValue(drive, (ValueId) reads.get(1).result());
        check(hasNote.equals(new Value.Bool(true))
                && hasNull.equals(new Value.Bool(true))
                && hasAfter.equals(new Value.Bool(false)),
            "has(note) is true for the present value, true for present null, and false "
                + "after the delete — the three presence states stay distinct; got "
                + hasNote + "/" + hasNull + "/" + hasAfter);
        check(readNote instanceof Value.String string && carrier(string).equals("x"),
            "the read publishes the written present value");
        check(readNull == Value.Null.INSTANCE,
            "the read of present null publishes language null (present, not missing)");

        // The final instance state: the delete left note missing while the
        // other fields are untouched.
        Value addrCity = heapValue(drive, (ValueId) reads.get(3).result());
        check(addrCity instanceof Value.String city && carrier(city).equals("munich"),
            "the required-field read of addr.city publishes the provided value");

        // The nominal receiver null failure (the cross-module nullable
        // read's runtime guard) — executed end-to-end in the blanket drive.
        check(maybeCityRead instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message().equals(
                    "expected @owner/Address, got null")
                && failure.failure().origin().equals(reads.get(2).origin()),
            "the nullable receiver read fails the nominal receiver boundary with the "
                + "exact E8001 at the op origin; got " + maybeCityRead);
        check(maybeCityRead instanceof Outcome.Failure<Value> failure
                && !drive.heap().containsKey((ValueId) reads.get(2).result()),
            "the failed read published no value");

        // The single-evaluation pins: the receiver boundary consumes the
        // payload's resolved receiver and the field boundary consumes the
        // op's own result slot — the receiver/key are never re-evaluated.
        SemanticOp maybeRead = reads.get(2);
        List<SemanticOp> maybeChildren = childrenOf(callerUnit, maybeRead);
        KindPayload.FieldReadPayload maybePayload =
            (KindPayload.FieldReadPayload) maybeRead.payload();
        check(maybeChildren.size() == 2
                && maybeChildren.get(0).payload() instanceof KindPayload.BoundaryPayload
                    receiverBoundary
                && receiverBoundary.kind() == BoundaryKind.UNTYPED_CLASS_INPUT
                && receiverBoundary.input().equals(maybePayload.classValue())
                && maybeChildren.get(1).payload() instanceof KindPayload.BoundaryPayload
                    fieldBoundary
                && fieldBoundary.kind() == BoundaryKind.OPTIONAL_FIELD_READ
                && fieldBoundary.input().equals((ValueId) maybeRead.result()),
            "the read's boundaries consume the resolved receiver and the op's own "
                + "result slot exactly once (no re-evaluation wiring)");

        // The wrong-identity arm: the same lowered read driven with a
        // Person instance as the receiver fails with the canonical actual.
        Map<ValueId, Value> wrongHeap = new LinkedHashMap<>(drive.heap());
        ClassLayout personLayout = drive.layouts().get(PERSON_ID);
        wrongHeap.put(maybePayload.classValue(),
            validPerson(personLayout, validHome(), validMeta(), FieldState.Missing.INSTANCE));
        Outcome<Value> wrongIdentity = ClassOpsExecutor.executeFieldRead(maybeRead,
            wrongHeap, maybeChildren.get(0), maybeChildren.get(1), drive.layouts(),
            realDelegate(new ArrayList<>()));
        check(wrongIdentity instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message().equals(
                    "expected @owner/Address, got class:@main/Person")
                && failure.failure().origin().equals(maybeRead.origin()),
            "the wrong-identity receiver fails with the canonical actual "
                + "class:@main/Person at the op origin; got " + wrongIdentity);

        // The required-field missing read: a defective Address instance
        // (city missing) pre-maps to null and fails the declared string
        // descriptor.
        Value.Class defective = new Value.Class(ADDRESS_ID, List.of(
            FieldState.Missing.INSTANCE,
            new FieldState.Present(new Value.Int(10115))));
        Map<ValueId, Value> defectiveHeap = new LinkedHashMap<>(drive.heap());
        defectiveHeap.put(maybePayload.classValue(), defective);
        Outcome<Value> missingRequired = ClassOpsExecutor.executeFieldRead(maybeRead,
            defectiveHeap, maybeChildren.get(0), maybeChildren.get(1), drive.layouts(),
            realDelegate(new ArrayList<>()));
        check(missingRequired instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message().equals("expected string, got null")
                && failure.failure().origin().equals(maybeRead.origin()),
            "a required field of a defective instance fails the read with the exact "
                + "E8001 (expected string, got null); got " + missingRequired);
    }

    // =========================================================================
    // 7. JSON decode: language null on every listed failure
    // =========================================================================

    private static void testJsonFromFailures(LoweredPair pair) {
        System.out.println("-- JSON decode: null on syntax/unknown-key/type/nested/"
            + "no-default failures, no partial instance, no defaults on provided "
            + "failure, the {}/[] collapse, the three-state roundtrip, the nested "
            + "factory parent --");
        Drive drive = freshDrive(pair);
        LoweredModuleUnit callerUnit = drive.callerUnit();
        SemanticOp personFrom = jsonOpOf(callerUnit, SemanticOpKind.JSON_FROM_CLASS,
            PERSON_ID);
        SemanticOp strictFrom = jsonOpOf(callerUnit, SemanticOpKind.JSON_FROM_CLASS,
            STRICT_ID);
        check(personFrom != null && strictFrom != null, "the Person and Strict "
            + "JSON_FROM_CLASS ops resolve");
        if (personFrom == null || strictFrom == null) {
            return;
        }
        KindPayload.JsonFromClassPayload personPayload =
            (KindPayload.JsonFromClassPayload) personFrom.payload();

        // The nested factory seam (K-D5 trigger (b)) with the executed
        // parent = the triggering JSON_FROM_CLASS op.
        ClassInterface addressEntry = pair.project().index().modules().get(OWNER).classes()
            .stream().filter(entry -> entry.classId().equals(ADDRESS_ID)).findFirst()
            .orElseThrow();
        NestedClassFactory seam = (classId, providedFields) -> {
            OpId factoryOpId = pair.owner().registry().factoryFor(
                addressEntry.constructionEntry());
            SemanticOp factoryOp = drive.ownerLookup().get(factoryOpId);
            Outcome<Value> outcome = ClassOpsExecutor.executeClassFactory(factoryOp,
                personFrom, drive.ownerLookup(), drive.layouts(), providedFields,
                drive.ownerRunner());
            if (!(outcome instanceof Outcome.Success<Value> success)) {
                throw new IllegalStateException("the nested factory failed");
            }
            drive.log().add("nested-factory " + classId.text() + " parent "
                + personFrom.opId());
            return success.value();
        };

        // (a) a partial document with a nested {}: the walk plus the
        // nested factory trigger and the caller's own defaults.
        Value decoded = ClassOpsExecutor.executeJsonFromClass(personFrom,
            Map.of(personPayload.jsonString(),
                Value.string("{\"age\": 7, \"home\": {}}")),
            pair.caller().jsonDefaults().childrenOf(personFrom.opId()),
            drive.callerLookup(), drive.layouts(),
            JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
        ClassLayout personLayout = drive.layouts().get(PERSON_ID);
        check(decoded instanceof Value.Class decodedPerson
                && decodedPerson.classId().equals(PERSON_ID)
                && fieldValue(decodedPerson, personLayout, "name")
                    instanceof Value.String name && carrier(name).equals("anon")
                && fieldValue(decodedPerson, personLayout, "age")
                    instanceof Value.Int age && age.value() == 7
                && fieldValue(decodedPerson, personLayout, "ratio")
                    instanceof Value.Number ratio && ratio.value() == 0.5
                && fieldValue(decodedPerson, personLayout, "note") == null,
            "the partial document decodes with the omitted defaults and the provided "
                + "age; the omitted optional note stays missing");
        Value nestedHome = fieldValue((Value.Class) decoded, personLayout, "home");
        check(nestedHome instanceof Value.Class home
                && fieldValue(home, drive.layouts().get(ADDRESS_ID), "city")
                    instanceof Value.String city && carrier(city).equals("berlin")
                && fieldValue(home, drive.layouts().get(ADDRESS_ID), "zip")
                    instanceof Value.Int zip && zip.value() == 10115,
            "the nested {} home defaulted through the owner's factory in the "
                + "declaring module");
        check(drive.log().contains("nested-factory @owner/Address parent "
                + personFrom.opId()),
            "the nested factory executed with the JSON_FROM_CLASS op as the executed "
                + "parent (K-D5 trigger (b), cross-unit)");

        // (b) the {}/[] collapse: [] decodes as the defaulted instance.
        Value collapsed = ClassOpsExecutor.executeJsonFromClass(personFrom,
            Map.of(personPayload.jsonString(), Value.string("[]")),
            pair.caller().jsonDefaults().childrenOf(personFrom.opId()),
            drive.callerLookup(), drive.layouts(),
            JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
        check(collapsed instanceof Value.Class collapsedPerson
                && collapsedPerson.classId().equals(PERSON_ID)
                && fieldValue(collapsedPerson, personLayout, "age")
                    instanceof Value.Int age && age.value() == 0,
            "the empty-array document collapses to the defaulted instance (the "
                + "{}/[] pin)");

        // (c)-(f): every listed failure publishes language null and no
        // defaults run on a provided-value failure.
        List<String> failingDocs = List.of(
            "{\"nope\": 1}",            // unknown key, document order
            "{\"age\": \"x\"}",         // provided type mismatch
            "{\"home\": {\"city\": 5}}", // nested decode failure
            "{",                        // syntax defect
            "{\"age\": 7, \"nope\": 1}"); // unknown key after a provided field
        for (String document : failingDocs) {
            long before = drive.log().size();
            Value result = ClassOpsExecutor.executeJsonFromClass(personFrom,
                Map.of(personPayload.jsonString(), Value.string(document)),
                pair.caller().jsonDefaults().childrenOf(personFrom.opId()),
                drive.callerLookup(), drive.layouts(),
                JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
            check(result == Value.Null.INSTANCE,
                "the document " + document + " publishes language null (no partial "
                    + "instance)");
            check(drive.log().size() == before,
                "no defaults ran for the failing document " + document);
        }

        // (g) the three-state roundtrip input: present null decodes as
        // present null (distinct from missing).
        Value nullNote = ClassOpsExecutor.executeJsonFromClass(personFrom,
            Map.of(personPayload.jsonString(), Value.string("{\"note\": null}")),
            pair.caller().jsonDefaults().childrenOf(personFrom.opId()),
            drive.callerLookup(), drive.layouts(),
            JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
        check(nullNote instanceof Value.Class nullPerson
                && fieldValue(nullPerson, personLayout, "note") == Value.Null.INSTANCE,
            "a JSON null decodes to present null (distinct from the missing state)");

        // (h)-(i): the K-D9 absent-no-default arm and the clean Strict walk.
        KindPayload.JsonFromClassPayload strictPayload =
            (KindPayload.JsonFromClassPayload) strictFrom.payload();
        Value strictEmpty = ClassOpsExecutor.executeJsonFromClass(strictFrom,
            Map.of(strictPayload.jsonString(), Value.string("{}")),
            pair.caller().jsonDefaults().childrenOf(strictFrom.opId()),
            drive.callerLookup(), drive.layouts(),
            JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
        check(strictEmpty == Value.Null.INSTANCE,
            "the absent no-default required tag returns language null (K-D9)");
        Value strictOk = ClassOpsExecutor.executeJsonFromClass(strictFrom,
            Map.of(strictPayload.jsonString(), Value.string("{\"tag\": \"t\"}")),
            pair.caller().jsonDefaults().childrenOf(strictFrom.opId()),
            drive.callerLookup(), drive.layouts(),
            JsonClassAlgorithmAdapter.parser(), seam, drive.callerRunner());
        check(strictOk instanceof Value.Class strictInstance
                && strictInstance.classId().equals(STRICT_ID)
                && fieldValue(strictInstance, drive.layouts().get(STRICT_ID), "tag")
                    instanceof Value.String tag && carrier(tag).equals("t"),
            "the clean Strict document decodes the tagged instance");
    }

    // =========================================================================
    // 8. JSON encode: deterministic text and the first declaration-order
    //    failure at the call origin
    // =========================================================================

    private static void testJsonToDeterministicAndFailures(LoweredPair pair) {
        System.out.println("-- JSON encode: the deterministic roundtrip and the first "
            + "declaration-order failure at the call origin --");
        Drive drive = freshDrive(pair);
        LoweredModuleUnit callerUnit = drive.callerUnit();
        SemanticOp personTo = jsonOpOf(callerUnit, SemanticOpKind.JSON_TO_CLASS,
            PERSON_ID);
        check(personTo != null, "the Person JSON_TO_CLASS op resolves");
        if (personTo == null) {
            return;
        }
        KindPayload.JsonToClassPayload toPayload =
            (KindPayload.JsonToClassPayload) personTo.payload();
        ClassLayout personLayout = drive.layouts().get(PERSON_ID);

        // (a) the deterministic roundtrip over a decoded/defaulted instance.
        Value.Class decoded = validPerson(personLayout, validHome(), validMeta(),
            FieldState.Missing.INSTANCE);
        Outcome<Value> first = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), decoded), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        Outcome<Value> second = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), decoded), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(first instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.String text
                && carrier(text).equals("{\"name\":\"anon\",\"age\":7,\"ratio\":0.5,"
                    + "\"home\":{\"city\":\"berlin\",\"zip\":10115},"
                    + "\"meta\":{\"k\":\"v\"}}"),
            "the roundtrip emits the deterministic declared-order text; got " + first);
        check(first instanceof Outcome.Success<Value> f
                && second instanceof Outcome.Success<Value> s
                && f.value().equals(s.value()),
            "repeated encoding is deterministic");

        // (b) present null serializes as JSON null in declaration position.
        Value.Class nullNote = validPerson(personLayout, validHome(), validMeta(),
            new FieldState.Present(Value.Null.INSTANCE));
        Outcome<Value> nullNoteText = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), nullNote), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(nullNoteText instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.String text
                && carrier(text).equals("{\"name\":\"anon\",\"age\":7,"
                    + "\"ratio\":0.5,"
                    + "\"home\":{\"city\":\"berlin\",\"zip\":10115},"
                    + "\"note\":null,\"meta\":{\"k\":\"v\"}}"),
            "present null serializes as JSON null in declaration position (the "
                + "three-state roundtrip); got " + nullNoteText);

        // (c) the wrong identity at the root: actual class:@owner/Address
        // with the empty fieldPath, projected at the call origin.
        Outcome<Value> wrongRoot = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), validHome()), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(wrongRoot instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().code() == DiagnosticCode.E8001
                && failure.failure().failure().message().equals(
                    "value at  is not JSON serializable: class:@owner/Address")
                && failure.failure().origin().equals(CALL_ORIGIN)
                && !failure.failure().origin().equals(personTo.origin()),
            "a wrong root identity fails with the exact template, the empty fieldPath, "
                + "and the canonical actual at the call origin; got " + wrongRoot);

        // (d) the first declaration-order failure: name missing (declared
        // first) wins over a nonfinite ratio.
        Value.Class defective = personInstance(personLayout,
            FieldState.Missing.INSTANCE,
            new FieldState.Present(new Value.Int(7)),
            new FieldState.Present(new Value.Number(Double.NaN)),
            new FieldState.Present(validHome()),
            FieldState.Missing.INSTANCE,
            new FieldState.Present(validMeta()));
        Outcome<Value> firstFailure = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), defective), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(firstFailure instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().message().equals(
                    "value at name is not JSON serializable: missing")
                && failure.failure().origin().equals(CALL_ORIGIN),
            "the first declaration-order failure (the missing required name) wins over "
                + "the later nonfinite ratio; got " + firstFailure);

        // (e) the nonfinite number arm at its declared position.
        Value.Class nonfinite = personInstance(personLayout,
            new FieldState.Present(Value.string("anon")),
            new FieldState.Present(new Value.Int(7)),
            new FieldState.Present(new Value.Number(Double.NaN)),
            new FieldState.Present(validHome()),
            FieldState.Missing.INSTANCE,
            new FieldState.Present(validMeta()));
        Outcome<Value> nonfiniteFailure = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), nonfinite), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(nonfiniteFailure instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().message().equals(
                    "value at ratio is not JSON serializable: number")
                && failure.failure().origin().equals(CALL_ORIGIN),
            "a nonfinite number fails at its pinned fieldPath with the number actual; "
                + "got " + nonfiniteFailure);

        // (f) the cycle arm: a table field re-entering itself fails at the
        // re-entering position with the table actual.
        SemanticTable<Value> cyclic = new SemanticTable<>();
        Value.Table cyclicWrapper = new Value.Table(cyclic);
        cyclic.put("self", cyclicWrapper);
        Value.Class cycleInstance = personInstance(personLayout,
            new FieldState.Present(Value.string("anon")),
            new FieldState.Present(new Value.Int(7)),
            new FieldState.Present(new Value.Number(0.5)),
            new FieldState.Present(validHome()),
            FieldState.Missing.INSTANCE,
            new FieldState.Present(cyclicWrapper));
        Outcome<Value> cycleFailure = ClassOpsExecutor.executeJsonToClass(personTo,
            Map.of(toPayload.classValue(), cycleInstance), drive.layouts(),
            JsonClassAlgorithmAdapter.stringifier(), CALL_ORIGIN);
        check(cycleFailure instanceof Outcome.Failure<Value> failure
                && failure.failure().failure().message().equals(
                    "value at meta.self is not JSON serializable: table")
                && failure.failure().origin().equals(CALL_ORIGIN),
            "a cyclic table fails at the re-entering position with the table actual; "
                + "got " + cycleFailure);
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Class Construction Integration Tail (ISSUE-0517) ===\n");

        LoweredPair pair = lowerPair();
        check(pair != null, "the two-module pipeline lowers (the production validators "
            + "run inside lowerModuleClassCore)");
        if (pair == null) {
            System.out.println("\nClassConstructionIntegrationTailTest: " + passed
                + " passed, " + failed + " failed");
            System.exit(1);
        }

        testPipelineFacts(pair);
        testLocalConstruction(pair);
        testExtraKeyE8007(pair);
        testImportedConstruction(pair);
        testMutableDefaultFreshness(pair);
        testFieldPresenceAndFailures(pair);
        testJsonFromFailures(pair);
        testJsonToDeterministicAndFailures(pair);

        System.out.println("\nClassConstructionIntegrationTailTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
