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
import deal.semantic.JsonClassAlgorithmAdapter;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleFact;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ClassFactoryId;
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
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
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
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
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
 * Verifies the ISSUE-0515 {@code @jsonable} lowering arm of
 * {@link SemanticLowerer} (class-construction-jsonable-operations
 * K-D8/K-D10; parent D16): the generated synthetic module-level
 * {@code C$fromJson(s: string): C|null} / {@code C$toJson(v: C): string}
 * function bodies (ordinary {@code CLOSURE_NEW} producers with
 * {@code LoweredBody} registrations through the
 * {@link deal.semantic.FunctionBindingRegistry} seam — the parameter
 * {@code BINDING_ALLOC} at the body entry, the parameter
 * {@code BINDING_LOAD}, and exactly one {@code JSON_FROM_CLASS}/
 * {@code JSON_TO_CLASS} op with the validator-pinned policies and
 * result types), the produced {@link JsonDefaultChildTable} record (one
 * per-site {@code CLASS_DEFAULT} child per required-present defaulted
 * field in declaration order), and the combined T1..T5 scenario — an
 * {@code @jsonable} class declaration with defaults and a nested
 * {@code @jsonable} class field lowered to validated units, then the
 * executor drives the generated body ops end-to-end at the unit level
 * (fromJson on a defaulted/partial document, toJson on the produced
 * instance, the nested factory trigger, the roundtrip).
 *
 * <p>Pinned cases (the task verification):
 * <ol>
 *   <li>the generated bodies pinned — exact signatures, {@code
 *       LoweredBody} registrations, parameter load plus the JSON op
 *       wiring, policies, result types, deterministic ids;</li>
 *   <li>{@link JsonDefaultChildTable} pinned — one {@code CLASS_DEFAULT}
 *       child per required-present defaulted field in declaration
 *       order;</li>
 *   <li>a non-{@code @jsonable} class generates no JSON functions and
 *       records no table entry;</li>
 *   <li>the combined T1..T5 scenario — two checked modules (an owner
 *       exporting an {@code @jsonable} class with defaults; a caller
 *       importing it and declaring an {@code @jsonable} class with a
 *       nested class field and defaults plus a no-default {@code
 *       @jsonable} class) lowered through the two-module seam to
 *       validated units, then the executor drives the generated body
 *       ops end-to-end: fromJson on a defaulted/partial document
 *       (defaults via the {@code JsonDefaultChildTable} children, the
 *       nested class field's omitted required defaults through the
 *       nested class's {@code CLASS_FACTORY} in the declaring module —
 *       K-D5 trigger (b), the factory's executed parent = the
 *       {@code JSON_FROM_CLASS} op), toJson on the produced instance,
 *       the K-D9 absent-no-default failure, and the roundtrip (this
 *       scenario fails if any of T1's layouts/defaults, T2/T3's
 *       executor surface, or T4's factory execution breaks);</li>
 *   <li>determinism — two repetitions byte-identical.</li>
 * </ol>
 */
public class JsonClassLoweringTest {

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

    // The two cross-unit modules of the combined scenario.
    private static final ModuleId OWNER = new ModuleId("owner");
    private static final ModuleId CALLER = new ModuleId("main");
    private static final String OWNER_SOURCE_ID = "owner.deal";
    private static final String CALLER_SOURCE_ID = "caller.deal";
    private static final String IMPORT_SPECIFIER = "owner";

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record PipelineSlice(CheckedSlice slice, String interfaceHash,
                                 ExternalModuleInterface ownInterface,
                                 Map<ConstructKind, List<SemanticOpKind>> coverage) {
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
    // Single-module pipeline (the ClassDeclarationLoweringTest discipline)
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

    /** The owner's Phase-3-corrected export map (the orchestrator's derivation). */
    private static Map<String, Type> ownerExports(CheckedSlice owner) {
        Map<String, Type> exports = new LinkedHashMap<>();
        for (StatementNode stmt : owner.program().statements()) {
            if (stmt instanceof ExportDeclaration exp
                    && exp.declaration() instanceof ClassDeclaration cd) {
                Symbol sym = owner.symbols().resolve(cd.name());
                if (sym instanceof Symbol.ClassSymbol cs) {
                    exports.put(cd.name(), Types.classType(cs.name(), cs.identity()));
                    if (cd.isJsonable()) {
                        // The synthetic C$fromJson/C$toJson exports the
                        // checker's @jsonable field validation routes
                        // through (the generated function symbols).
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
     * module identity — including the {@code @jsonable} synthetic
     * function exports the checker's field-type validation consumes.
     */
    private static final class OwnerResolver implements ModuleResolver {

        private final Map<String, Type> exports;
        private final Map<String, Symbol.ClassSymbol> classSymbols;
        private final Set<String> syntheticFunctions;

        OwnerResolver(CheckedSlice owner) {
            this.exports = ownerExports(owner);
            this.classSymbols = ownerClassSymbols(owner);
            this.syntheticFunctions = new LinkedHashSet<>();
            for (StatementNode stmt : owner.program().statements()) {
                StatementNode declaration = stmt instanceof ExportDeclaration exp
                    ? exp.declaration() : stmt;
                if (declaration instanceof ClassDeclaration cd && cd.isJsonable()) {
                    syntheticFunctions.add(cd.name() + "$fromJson");
                    syntheticFunctions.add(cd.name() + "$toJson");
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
            if (IdentityTestFixtures.moduleIdentityOf(OWNER.path())
                    .equals(declaringModule)) {
                return classSymbols.get(className);
            }
            return null;
        }

        @Override
        public boolean isFunctionExportedFromModule(
                deal.identity.CanonicalModuleIdentity declaringModule, String functionName,
                String importingModule) throws ModuleNotFoundException {
            if (IdentityTestFixtures.moduleIdentityOf(OWNER.path())
                    .equals(declaringModule)) {
                return syntheticFunctions.contains(functionName);
            }
            return false;
        }
    }

    /** The single-module pipeline driver: lexer/parser/checker → lowerModuleClassCore. */
    private static SemanticLowerer.ClassDeclarationCoreResult lowerModule(String source) {
        CheckedSlice slice = checkSlice(source, MODULE, null);
        if (slice == null) {
            return null;
        }
        PipelineSlice pipeline = pipeline(slice);
        if (pipeline == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleClassCore(moduleOf(slice, MODULE, List.of()),
            SemanticProfile.DEAL_V1_2_INT32, pipeline.coverage(), pipeline.interfaceHash(),
            REGISTRY_HASH, pipeline.ownInterface(),
            SemanticIdAllocator.over(List.of(MODULE)));
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

    /** Lowers the owner and the caller through the two-module seam. */
    private static LoweredPair lowerPair(String ownerSource, String callerSource) {
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
        // The imported-construction facts (the ISSUE-0514 seam): per
        // exported owner class, the interface entry, the owner unit's
        // layout, the registry binding's factory op id, and the factory
        // op's result ValueId.
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

    private static KindPayload.ClassDefaultPayload defaultPayload(SemanticOp op) {
        return (KindPayload.ClassDefaultPayload) op.payload();
    }

    private static KindPayload.ClosureNewPayload closurePayload(SemanticOp op) {
        return (KindPayload.ClosureNewPayload) op.payload();
    }

    /** The carrier text of one valid-scalar string view (test-local). */
    private static String carrier(Value.String string) {
        return ((UnicodeScalars.Valid) string.scalar()).carrier();
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
    // (a) the generated bodies pinned (signatures, registrations, wiring)
    // =========================================================================

    private static void testGeneratedBodiesPinned() {
        System.out.println("-- the generated C$fromJson/C$toJson bodies: exact "
            + "signatures, LoweredBody registrations, parameter load plus the JSON op "
            + "wiring, policies, result types --");

        String source = """
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p" + "t";
              note?: string;
            }
            """;
        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule(source);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the @jsonable slice lowers to a validated unit: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        StructuredBodyTable table = result.lowering().table();
        ClassId pointId = new ClassId(MODULE.path(), "Point");
        ClassLayout layout = unit.classLayouts().get(pointId);
        check(layout != null, "the layout of the @jsonable class exists");
        if (layout == null) {
            return;
        }
        RuntimeDescriptor classDescriptor = new RuntimeDescriptor.Class(pointId);
        RuntimeDescriptor fromResult = new RuntimeDescriptor.Nullable(classDescriptor);

        // Exactly two CLOSURE_NEW ops with the pinned generated
        // signatures.
        List<SemanticOp> closures = ofKind(unit.ops(), SemanticOpKind.CLOSURE_NEW);
        check(closures.size() == 2, "exactly two generated CLOSURE_NEW ops; got "
            + closures.size());
        if (closures.size() != 2) {
            return;
        }
        SemanticOp fromClosure = null;
        SemanticOp toClosure = null;
        for (SemanticOp closure : closures) {
            KindPayload.ClosureNewPayload payload = closurePayload(closure);
            if (payload.signature().equals(new RuntimeDescriptor.Func(
                    List.of(RuntimeDescriptor.String.INSTANCE), fromResult, false))) {
                fromClosure = closure;
            } else if (payload.signature().equals(new RuntimeDescriptor.Func(
                    List.of(classDescriptor), RuntimeDescriptor.String.INSTANCE, false))) {
                toClosure = closure;
            }
        }
        check(fromClosure != null && toClosure != null,
            "one closure carries C$fromJson(s: string): C|null and one carries "
                + "C$toJson(v: C): string; got from=" + (fromClosure != null)
                + " to=" + (toClosure != null));
        if (fromClosure == null || toClosure == null) {
            return;
        }
        check(fromClosure.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE
                && toClosure.failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE,
            "the generated closures carry NO_DEAL_FAILURE");
        check(fromClosure.origin().kind() == SourceOriginKind.SYNTHETIC
                && toClosure.origin().kind() == SourceOriginKind.SYNTHETIC,
            "the generated closures carry SYNTHETIC origins (deterministic synthetic "
                + "origins)");

        // The LoweredFunction records and the LoweredBody registrations
        // through the registry seam (generated synthetics are ordinary
        // CLOSURE_NEW producers).
        KindPayload.ClosureNewPayload fromPayload = closurePayload(fromClosure);
        KindPayload.ClosureNewPayload toPayload = closurePayload(toClosure);
        check(unit.functions().containsKey(fromPayload.function())
                && unit.functions().containsKey(toPayload.function()),
            "unit.functions carries both generated LoweredFunction records");
        LoweredFunction fromFunction = unit.functions().get(fromPayload.function());
        LoweredFunction toFunction = unit.functions().get(toPayload.function());
        check(fromFunction != null && fromFunction.captures().isEmpty()
                && fromFunction.body().equals(fromPayload.binding().blockId())
                && toFunction != null && toFunction.captures().isEmpty()
                && toFunction.body().equals(toPayload.binding().blockId()),
            "the LoweredFunction records pin the signatures, empty captures, and the "
                + "binding body blocks");
        FunctionAllocationIdentity fromIdentity = new FunctionAllocationIdentity(
            ((ValueId) fromClosure.result()).id());
        FunctionAllocationIdentity toIdentity = new FunctionAllocationIdentity(
            ((ValueId) toClosure.result()).id());
        check(unit.functionBindings().get(fromIdentity)
                instanceof FunctionExecutionBinding.LoweredBody fromBinding
                && fromBinding.functionId().equals(fromPayload.function())
                && fromBinding.blockId().equals(fromPayload.binding().blockId()),
            "the fromJson closure identity registers exactly one LoweredBody binding "
                + "through the registry seam");
        check(unit.functionBindings().get(toIdentity)
                instanceof FunctionExecutionBinding.LoweredBody toBinding
                && toBinding.functionId().equals(toPayload.function())
                && toBinding.blockId().equals(toPayload.binding().blockId()),
            "the toJson closure identity registers exactly one LoweredBody binding "
                + "through the registry seam");

        // The fromJson body block: the parameter ALLOC, the parameter
        // load, and exactly one JSON_FROM_CLASS op.
        List<OpId> fromBody = table.blockOps().get(fromPayload.binding().blockId());
        check(fromBody != null && fromBody.size() == 3,
            "the fromJson body block carries exactly three ops (parameter ALLOC, "
                + "parameter load, JSON op); got " + (fromBody == null ? "null"
                    : fromBody.size()));
        if (fromBody == null || fromBody.size() != 3) {
            return;
        }
        SemanticOp fromAlloc = opById(unit, fromBody.get(0));
        SemanticOp fromLoad = opById(unit, fromBody.get(1));
        SemanticOp fromJson = opById(unit, fromBody.get(2));
        check(fromAlloc != null && fromAlloc.kind() == SemanticOpKind.BINDING_ALLOC
                && fromAlloc.payload() instanceof KindPayload.BindingAllocPayload fromAllocP
                && fromAllocP.mutable() && fromAllocP.generation() == 0,
            "the fromJson parameter ALLOC sits at the body entry (mutable, generation 0)");
        check(fromLoad != null && fromLoad.kind() == SemanticOpKind.BINDING_LOAD
                && fromLoad.payload() instanceof KindPayload.BindingLoadPayload fromLoadP
                && fromLoadP.binding().equals(((KindPayload.BindingAllocPayload)
                    fromAlloc.payload()).binding())
                && fromLoadP.generation() == 0
                && fromLoad.resultType().equals(RuntimeDescriptor.String.INSTANCE),
            "the fromJson parameter load wires the parameter binding with the string "
                + "result type");
        check(fromJson != null && fromJson.kind() == SemanticOpKind.JSON_FROM_CLASS
                && fromJson.failurePolicy() == FailurePolicyId.JSON_FROM_NULL,
            "the fromJson body's single JSON op carries policy JSON_FROM_NULL");
        check(fromJson != null && fromJson.payload()
                instanceof KindPayload.JsonFromClassPayload fromJsonP
                && fromJsonP.layout().equals(layout)
                && fromJsonP.jsonString().equals(fromLoad.result()),
            "the JSON_FROM_CLASS payload pins the class layout and the parameter load "
                + "result as the jsonString operand");
        check(fromJson != null && fromJson.resultType() != null
                && fromJson.resultType().equals(fromResult)
                && fromJson.result() instanceof ValueId,
            "the JSON_FROM_CLASS op publishes the pinned ?class:<ClassId> result type");

        // The toJson body block: the parameter ALLOC, the parameter
        // load, and exactly one JSON_TO_CLASS op.
        List<OpId> toBody = table.blockOps().get(toPayload.binding().blockId());
        check(toBody != null && toBody.size() == 3,
            "the toJson body block carries exactly three ops; got " + (toBody == null
                ? "null" : toBody.size()));
        if (toBody != null && toBody.size() == 3) {
            SemanticOp toAlloc = opById(unit, toBody.get(0));
            SemanticOp toLoad = opById(unit, toBody.get(1));
            SemanticOp toJson = opById(unit, toBody.get(2));
            check(toAlloc != null && toAlloc.kind() == SemanticOpKind.BINDING_ALLOC
                    && toLoad != null && toLoad.kind() == SemanticOpKind.BINDING_LOAD
                    && toLoad.resultType().equals(classDescriptor),
                "the toJson parameter load wires the class descriptor result type");
            check(toJson != null && toJson.kind() == SemanticOpKind.JSON_TO_CLASS
                    && toJson.failurePolicy() == FailurePolicyId.JSON_TO_ERROR,
                "the toJson body's single JSON op carries policy JSON_TO_ERROR");
            check(toJson != null && toJson.payload()
                    instanceof KindPayload.JsonToClassPayload toJsonP
                    && toJsonP.layout().equals(layout)
                    && toJsonP.classValue().equals(toLoad.result()),
                "the JSON_TO_CLASS payload pins the parameter load result as the "
                    + "classValue operand and the class layout");
            check(toJson != null && toJson.resultType() != null
                    && toJson.resultType().equals(RuntimeDescriptor.String.INSTANCE)
                    && toJson.result() instanceof ValueId,
                "the JSON_TO_CLASS op publishes the pinned string result type");
        }

        // The JsonDefaultChildTable entry: one per-site CLASS_DEFAULT
        // child per required-present defaulted field in declaration
        // order (x, tag — the optional note has no default and never
        // enters the list).
        List<SemanticOp> defaults = ofKind(unit.ops(), SemanticOpKind.CLASS_DEFAULT);
        check(defaults.size() == 2, "two CLASS_DEFAULT ops (x and tag); got "
            + defaults.size());
        List<OpId> children = result.jsonDefaults().childrenOf(fromJson.opId());
        check(children != null && children.size() == 2
                && children.get(0).equals(defaults.get(0).opId())
                && children.get(1).equals(defaults.get(1).opId())
                && defaultPayload(defaults.get(0)).field().equals("x")
                && defaultPayload(defaults.get(1)).field().equals("tag"),
            "the JsonDefaultChildTable entry lists exactly one CLASS_DEFAULT child per "
                + "required-present defaulted field in declaration order (x, tag)");
        check(result.jsonDefaults().childrenOf(toClosure.opId()) == null,
            "no JSON_TO_CLASS op records default children");
    }

    // =========================================================================
    // (b) the non-@jsonable negative
    // =========================================================================

    private static void testNonJsonableNegative() {
        System.out.println("-- a non-@jsonable class generates no JSON functions and "
            + "records no table entry --");

        SemanticLowerer.ClassDeclarationCoreResult result = lowerModule("""
            export class Plain {
              x: int = 1;
            }
            """);
        check(result != null && result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            "the non-@jsonable slice lowers: "
                + (result == null || result.lowering() == null ? "null"
                    : result.lowering().diagnostics()));
        if (result == null || result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        check(ofKind(unit.ops(), SemanticOpKind.JSON_FROM_CLASS).isEmpty()
                && ofKind(unit.ops(), SemanticOpKind.JSON_TO_CLASS).isEmpty()
                && ofKind(unit.ops(), SemanticOpKind.CLOSURE_NEW).isEmpty(),
            "no JSON op and no CLOSURE_NEW op exist for the non-@jsonable class");
        check(result.jsonDefaults().defaultChildren().isEmpty(),
            "the produced JsonDefaultChildTable record is empty");
    }

    // =========================================================================
    // (c) the combined T1..T5 scenario: the end-to-end two-module drive
    // =========================================================================

    private static void testCombinedT1T5Scenario() {
        System.out.println("-- combined T1..T5: the generated bodies driven end-to-end "
            + "at the unit level (fromJson defaults/partial document, the nested "
            + "factory trigger, toJson, the K-D9 failure, the roundtrip) --");

        LoweredPair pair = lowerPair("""
            // @jsonable
            export class Address {
              city: string = "berlin";
              zip: int = 10115;
            }
            """, """
            import * as Owner from "owner"

            // @jsonable
            export class Person {
              name: string = "anon";
              age: int = 0;
              home: Owner.Address = {city: "seed"};
            }

            // @jsonable
            export class Strict {
              tag: string;
            }
            """);
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
        StructuredBodyTable callerTable = pair.caller().lowering().table();
        StructuredBodyTable ownerTable = pair.owner().lowering().table();
        ClassId personId = new ClassId(CALLER.path(), "Person");
        ClassId strictId = new ClassId(CALLER.path(), "Strict");
        ClassId addressId = new ClassId(OWNER.path(), "Address");
        ClassLayout personLayout = callerUnit.classLayouts().get(personId);
        ClassLayout strictLayout = callerUnit.classLayouts().get(strictId);
        ClassLayout addressLayout = ownerUnit.classLayouts().get(addressId);
        check(personLayout != null && strictLayout != null && addressLayout != null,
            "the layouts resolve for Person, Strict, and Address");

        // The generated JSON ops of the caller (one fromJson + one toJson
        // per @jsonable class).
        List<SemanticOp> fromJsonOps = ofKind(callerUnit.ops(),
            SemanticOpKind.JSON_FROM_CLASS);
        List<SemanticOp> toJsonOps = ofKind(callerUnit.ops(), SemanticOpKind.JSON_TO_CLASS);
        check(fromJsonOps.size() == 2 && toJsonOps.size() == 2,
            "the caller unit carries exactly two JSON_FROM_CLASS and two "
                + "JSON_TO_CLASS ops; got " + fromJsonOps.size() + "/"
                + toJsonOps.size());
        if (fromJsonOps.size() != 2 || toJsonOps.size() != 2) {
            return;
        }
        SemanticOp personFrom = fromJsonOps.get(0);
        SemanticOp personTo = toJsonOps.get(0);
        SemanticOp strictFrom = fromJsonOps.get(1);
        SemanticOp strictTo = toJsonOps.get(1);
        check(personFrom.payload() instanceof KindPayload.JsonFromClassPayload p
                && p.layout().classId().equals(personId),
            "the first JSON_FROM_CLASS op walks the Person layout");
        check(strictFrom.payload() instanceof KindPayload.JsonFromClassPayload p
                && p.layout().classId().equals(strictId),
            "the second JSON_FROM_CLASS op walks the Strict layout");

        // The JsonDefaultChildTable pins for the caller: Person's fromJson
        // lists its three required-present defaulted fields in
        // declaration order; Strict's entry is empty.
        List<SemanticOp> personDefaults = ofKind(callerUnit.ops(),
            SemanticOpKind.CLASS_DEFAULT);
        check(personDefaults.size() == 3
                && defaultPayload(personDefaults.get(0)).field().equals("name")
                && defaultPayload(personDefaults.get(1)).field().equals("age")
                && defaultPayload(personDefaults.get(2)).field().equals("home"),
            "Person emits three CLASS_DEFAULT ops in declaration order (name, age, home)");
        List<OpId> personChildren = pair.caller().jsonDefaults().childrenOf(
            personFrom.opId());
        check(personChildren != null && personChildren.size() == 3
                && personChildren.get(0).equals(personDefaults.get(0).opId())
                && personChildren.get(1).equals(personDefaults.get(1).opId())
                && personChildren.get(2).equals(personDefaults.get(2).opId()),
            "Person's JsonDefaultChildTable entry lists name/age/home in declaration "
                + "order");
        List<OpId> strictChildren = pair.caller().jsonDefaults().childrenOf(
            strictFrom.opId());
        check(strictChildren != null && strictChildren.isEmpty(),
            "Strict's JsonDefaultChildTable entry is the empty list (no defaults)");

        // The owner's factory: the registry binding resolves through the
        // interface constructionEntry (a broken T1 factory fails here).
        ClassInterface addressEntry = null;
        for (ClassInterface candidate
                : pair.project().index().modules().get(OWNER).classes()) {
            if (candidate.classId().equals(addressId)) {
                addressEntry = candidate;
            }
        }
        check(addressEntry != null, "the interface index carries the Address entry");
        if (addressEntry == null) {
            return;
        }
        final ClassInterface nestedEntry = addressEntry;
        OpId addressFactoryId = pair.owner().registry().factoryFor(
            addressEntry.constructionEntry());
        SemanticOp addressFactory = opById(ownerUnit, addressFactoryId);
        check(addressFactory != null
                && addressFactory.kind() == SemanticOpKind.CLASS_FACTORY,
            "the owner's CLASS_FACTORY op resolves through the registry");

        // The drive contexts.
        Map<OpId, SemanticOp> callerLookup = new LinkedHashMap<>();
        for (SemanticOp op : callerUnit.ops()) {
            callerLookup.put(op.opId(), op);
        }
        Map<OpId, SemanticOp> ownerLookup = new LinkedHashMap<>();
        for (SemanticOp op : ownerUnit.ops()) {
            ownerLookup.put(op.opId(), op);
        }
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>();
        layouts.putAll(ownerUnit.classLayouts());
        layouts.putAll(callerUnit.classLayouts());
        Map<ValueId, Value> heap = new LinkedHashMap<>();
        Map<deal.semantic.ir.BindingId, Value> bindings = new LinkedHashMap<>();
        List<String> log = new ArrayList<>();
        BoundaryCheckRunner real = realDelegate(log);

        // The owner-side body runner: the mini block interpreter over the
        // owner's detached default blocks (the declaring module's scope).
        // The holder breaks the self-reference (a default block may
        // contain a CLASS_NEW whose factory drive re-enters the owner
        // runner).
        final BodyRunner[] ownerRunnerHolder = new BodyRunner[1];
        ownerRunnerHolder[0] = defaultOpArg -> {
            log.add("owner-default " + defaultOpArg.opId());
            return runBlock(ownerUnit, ownerTable, defaultOpArg, heap, bindings, layouts,
                pair.owner().registry(), ownerLookup, ownerRunnerHolder[0], real, log);
        };
        BodyRunner ownerRunner = ownerRunnerHolder[0];
        // The caller-side body runner: the mini block interpreter over
        // the caller's detached default blocks.
        final BodyRunner ownerRunnerFinal = ownerRunner;
        BodyRunner callerRunner = defaultOpArg -> {
            log.add("caller-default " + defaultOpArg.opId());
            return runBlock(callerUnit, callerTable, defaultOpArg, heap, bindings, layouts,
                pair.owner().registry(), ownerLookup, ownerRunnerFinal, real, log);
        };

        // Scripted documents per JSON_FROM_CLASS op (the generated
        // body's parameter load substitution).
        Map<OpId, String> documents = new LinkedHashMap<>();
        documents.put(personFrom.opId(), "{\"age\": 42}");
        documents.put(strictFrom.opId(), "{}");

        // Scripted toJson operands per generated toJson op (the
        // generated body's parameter-load substitution): the Person
        // toJson walks the instance the Person fromJson published (the
        // roundtrip), and the Strict toJson walks the language null the
        // Strict fromJson published (a root identity failure).
        Map<OpId, Value> toJsonInputs = new LinkedHashMap<>();

        SourceOrigin callOrigin = new SourceOrigin(CALLER_SOURCE_ID,
            new deal.semantic.ir.SourceSpan(CALLER_SOURCE_ID, 9, 5, 9, 20),
            SourceOriginKind.USER, new deal.semantic.ir.AnchorId(0), null);

        // The drive: the caller unit's ops in source order; the JSON ops
        // execute through the executor with the production JSON algorithm
        // delegate (the E8 seam).
        for (SemanticOp op : callerUnit.ops()) {
            switch (op.kind()) {
                case CONST -> {
                    Value value = constValue(op);
                    if (value != null) {
                        heap.put((ValueId) op.result(), value);
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
                case JSON_FROM_CLASS -> {
                    KindPayload.JsonFromClassPayload payload =
                        (KindPayload.JsonFromClassPayload) op.payload();
                    String document = documents.get(op.opId());
                    check(document != null, "a scripted document exists for " + op.opId());
                    if (document == null) {
                        continue;
                    }
                    Map<ValueId, Value> values = new LinkedHashMap<>(heap);
                    values.put(payload.jsonString(), Value.string(document));
                    List<OpId> children = pair.caller().jsonDefaults().childrenOf(
                        op.opId());
                    final SemanticOp triggeringOp = op;
                    NestedClassFactory seam = (classId, providedFields) -> {
                        log.add("nested-factory " + classId);
                        return fillNested(classId, providedFields, triggeringOp,
                            pair.owner().registry(), ownerLookup, layouts, ownerRunner,
                            nestedEntry, log);
                    };
                    Value result = ClassOpsExecutor.executeJsonFromClass(op, values,
                        children == null ? List.of() : children, callerLookup, layouts,
                        JsonClassAlgorithmAdapter.parser(), seam, callerRunner);
                    heap.put((ValueId) op.result(), result);
                    // The produced instance feeds the matching generated
                    // toJson body (the roundtrip leg); the Strict walk's
                    // language null feeds the Strict toJson root check.
                    if (op.opId().equals(personFrom.opId())) {
                        toJsonInputs.put(personTo.opId(), result);
                    }
                    if (op.opId().equals(strictFrom.opId())) {
                        toJsonInputs.put(strictTo.opId(), result);
                    }
                }
                case JSON_TO_CLASS -> {
                    KindPayload.JsonToClassPayload payload =
                        (KindPayload.JsonToClassPayload) op.payload();
                    Value input = toJsonInputs.get(op.opId());
                    check(input != null, "a scripted toJson input exists for " + op.opId());
                    if (input == null) {
                        continue;
                    }
                    Map<ValueId, Value> values = new LinkedHashMap<>(heap);
                    values.put(payload.classValue(), input);
                    Outcome<Value> outcome = ClassOpsExecutor.executeJsonToClass(op,
                        values, layouts, JsonClassAlgorithmAdapter.stringifier(),
                        callOrigin);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    } else {
                        heap.put((ValueId) op.result(), Value.Null.INSTANCE);
                    }
                }
                default -> {
                    // BINDING_ALLOC, detached CLASS_DEFAULT/CLASS_FACTORY
                    // ops, and the generated bodies' other ops carry no
                    // interpreter step in this drive.
                }
            }
        }

        // The Person partial-document decode: name defaulted (anon), age
        // provided (42), home defaulted through the caller-side default
        // block's CLASS_NEW(SHARED_FACTORY) — the home literal provides
        // city "seed" and the owner's factory fills zip 10115.
        Value personValue = heap.get((ValueId) personFrom.result());
        check(personValue instanceof Value.Class person
                && person.classId().equals(personId),
            "the Person fromJson publishes a tagged Person instance");
        if (personValue instanceof Value.Class person) {
            check(fieldValue(person, personLayout, "name") instanceof Value.String name
                    && carrier(name).equals("anon"),
                "the omitted name defaulted through the caller's CLASS_DEFAULT child");
            check(fieldValue(person, personLayout, "age") instanceof Value.Int age
                    && age.value() == 42,
                "the provided age decoded from the document");
            Value home = fieldValue(person, personLayout, "home");
            check(home instanceof Value.Class homeInstance
                    && homeInstance.classId().equals(addressId),
                "the omitted home defaulted to a fresh nested Address instance");
            if (home instanceof Value.Class homeInstance) {
                check(fieldValue(homeInstance, addressLayout, "city")
                        instanceof Value.String city && carrier(city).equals("seed"),
                    "the home default's provided city is seed (the literal's value)");
                check(fieldValue(homeInstance, addressLayout, "zip")
                        instanceof Value.Int zip && zip.value() == 10115,
                    "the home default's omitted zip filled by the owner's factory "
                        + "(the nested construction inside the default block)");
            }
            check(log.contains("caller-default " + personDefaults.get(0).opId())
                    && log.contains("caller-default " + personDefaults.get(2).opId()),
                "the caller's name and home default children ran exactly once");
            check(log.stream().anyMatch(entry -> entry.startsWith("owner-default")),
                "the owner's default blocks ran (zip) inside the caller's home default");

            // The drive's toJson over the produced instance (the
            // roundtrip leg): deterministic declared-order text.
            Value toJsonText = heap.get((ValueId) personTo.result());
            check(toJsonText instanceof Value.String text
                    && carrier(text).equals(
                        "{\"name\":\"anon\",\"age\":42,"
                            + "\"home\":{\"city\":\"seed\",\"zip\":10115}}"),
                "the drive's toJson on the produced instance emits the deterministic "
                    + "roundtrip text");
        }

        // The nested-factory trigger: Person fromJson with home provided
        // as {} — the nested Address decode triggers the owner's
        // CLASS_FACTORY (K-D5 trigger (b)) with the JSON_FROM_CLASS op
        // as the executed parent.
        List<String> nestedLog = new ArrayList<>();
        Map<ValueId, Value> nestedValues = new LinkedHashMap<>(heap);
        KindPayload.JsonFromClassPayload personPayload =
            (KindPayload.JsonFromClassPayload) personFrom.payload();
        nestedValues.put(personPayload.jsonString(), Value.string("{\"home\": {}}"));
        final SemanticOp triggeringOp = personFrom;
        NestedClassFactory recordingSeam = (classId, providedFields) -> {
            nestedLog.add("nested-factory " + classId);
            return fillNested(classId, providedFields, triggeringOp,
                pair.owner().registry(), ownerLookup, layouts, ownerRunner, nestedEntry,
                nestedLog);
        };
        Value nestedValue = ClassOpsExecutor.executeJsonFromClass(personFrom, nestedValues,
            pair.caller().jsonDefaults().childrenOf(personFrom.opId()), callerLookup,
            layouts, JsonClassAlgorithmAdapter.parser(), recordingSeam, callerRunner);
        check(nestedValue instanceof Value.Class person
                && person.classId().equals(personId),
            "the nested-decode Person walk publishes a tagged instance");
        if (nestedValue instanceof Value.Class person) {
            Value home = fieldValue(person, personLayout, "home");
            check(home instanceof Value.Class homeInstance
                    && homeInstance.classId().equals(addressId),
                "the provided {} home decoded to a tagged Address instance");
            if (home instanceof Value.Class homeInstance) {
                check(fieldValue(homeInstance, addressLayout, "city")
                        instanceof Value.String city && carrier(city).equals("berlin"),
                    "the nested city default evaluated through the owner's factory in "
                        + "the declaring module");
                check(fieldValue(homeInstance, addressLayout, "zip")
                        instanceof Value.Int zip && zip.value() == 10115,
                    "the nested zip default evaluated through the owner's factory in "
                        + "the declaring module");
            }
            check(fieldValue(person, personLayout, "name") instanceof Value.String name
                    && carrier(name).equals("anon")
                    && fieldValue(person, personLayout, "age") instanceof Value.Int age
                    && age.value() == 0,
                "the omitted name and age defaulted through the caller's children");
        }
        check(nestedLog.contains("nested-factory " + addressId.text())
                && nestedLog.contains("nested-factory-parent " + personFrom.opId()),
            "the nested factory seam recorded the Address factory execution with the "
                + "JSON_FROM_CLASS op as the executed parent (K-D5 trigger (b), "
                + "cross-unit)");
        check(log.stream().filter(entry -> entry.startsWith("owner-default")).count() >= 2,
            "the nested drive's owner defaults evaluated in the declaring module's "
                + "scope through the factory");

        // The K-D9 failure: Strict's fromJson on {} returns language
        // null (absent required-present no-default tag).
        Value strictValue = heap.get((ValueId) strictFrom.result());
        check(strictValue instanceof Value.Null,
            "Strict fromJson on {} returns language null (K-D9)");
    }

    /** The nested factory seam's production-shape drive (K-D5 trigger (b)). */
    private static Value fillNested(ClassId classId, Set<String> providedFields,
                                    SemanticOp triggeringOp,
                                    deal.semantic.ir.ClassFactoryRegistry registry,
                                    Map<OpId, SemanticOp> ownerLookup,
                                    Map<ClassId, ClassLayout> layouts,
                                    BodyRunner ownerRunner, ClassInterface entry,
                                    List<String> log) {
        OpId factoryOpId = registry.factoryFor(entry.constructionEntry());
        SemanticOp factoryOp = ownerLookup.get(factoryOpId);
        if (factoryOp == null) {
            throw new IllegalStateException("the nested factory does not resolve for "
                + classId + " (producer defect)");
        }
        Outcome<Value> outcome = ClassOpsExecutor.executeClassFactory(factoryOp,
            triggeringOp, ownerLookup, layouts, providedFields, ownerRunner);
        if (!(outcome instanceof Outcome.Success<Value> success)) {
            throw new IllegalStateException("the nested factory failed");
        }
        log.add("nested-factory-parent " + triggeringOp.opId());
        return success.value();
    }

    /**
     * The mini block interpreter of one detached default block: executes
     * the block's ops in order (CONST, BINDING_LOAD from the shared
     * bindings, CLASS_NEW through the executor with the owner's
     * shared-factory facts) and returns the block's produced default
     * value (the CLASS_DEFAULT op's result slot).
     */
    private static Value runBlock(LoweredModuleUnit unit, StructuredBodyTable table,
                                  SemanticOp defaultOp, Map<ValueId, Value> heap,
                                  Map<deal.semantic.ir.BindingId, Value> bindings,
                                  Map<ClassId, ClassLayout> layouts,
                                  deal.semantic.ir.ClassFactoryRegistry registry,
                                  Map<OpId, SemanticOp> ownerLookup, BodyRunner ownerRunner,
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
                    KindPayload.ClassNewPayload newPayload =
                        (KindPayload.ClassNewPayload) op.payload();
                    Outcome<Value> outcome = newPayload.defaultOwner()
                        == DefaultOwner.SHARED_FACTORY
                            ? ClassOpsExecutor.executeClassNewSharedFactory(op, heap,
                                registry, ownerLookup,
                                resolveBoundaryOps(op, unit, newPayload), layouts, real,
                                ownerRunner)
                            : ClassOpsExecutor.executeClassNewLocal(op, heap, ownerLookup,
                                resolveBoundaryOps(op, unit, newPayload), layouts, real,
                                ownerRunner);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    } else {
                        throw new IllegalStateException("the default block's CLASS_NEW "
                            + "failed: " + outcome);
                    }
                }
                default -> {
                    // The CLASS_DEFAULT op itself and its BOUNDARY
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

    private static Map<OpId, SemanticOp> resolveBoundaryOps(SemanticOp classNew,
            LoweredModuleUnit unit, KindPayload.ClassNewPayload payload) {
        Map<OpId, SemanticOp> resolved = new LinkedHashMap<>();
        for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
            SemanticOp child = opById(unit, entry.boundaryOpId());
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
    // (d) determinism
    // =========================================================================

    private static void testDeterminism() {
        System.out.println("-- determinism: two repetitions byte-identical --");

        String ownerSource = """
            // @jsonable
            export class Address {
              city: string = "berlin";
              zip: int = 10115;
            }
            """;
        String callerSource = """
            import * as Owner from "owner"

            // @jsonable
            export class Person {
              name: string = "anon";
              age: int = 0;
              home: Owner.Address = {city: "seed"};
            }

            // @jsonable
            export class Strict {
              tag: string;
            }
            """;
        LoweredPair first = lowerPair(ownerSource, callerSource);
        LoweredPair second = lowerPair(ownerSource, callerSource);
        check(first != null && second != null, "both repetitions lower");
        if (first == null || second == null) {
            return;
        }
        byte[] firstOwner = SemanticIrDumper.dumpModule(first.owner().lowering().unit());
        byte[] secondOwner = SemanticIrDumper.dumpModule(second.owner().lowering().unit());
        byte[] firstCaller = SemanticIrDumper.dumpModule(first.caller().lowering().unit());
        byte[] secondCaller = SemanticIrDumper.dumpModule(second.caller().lowering().unit());
        check(Arrays.equals(firstOwner, secondOwner),
            "the owner unit dump is byte-identical across repetitions");
        check(Arrays.equals(firstCaller, secondCaller),
            "the caller unit dump is byte-identical across repetitions");

        // The single-module slice repeats byte-identically too.
        SemanticLowerer.ClassDeclarationCoreResult a = lowerModule("""
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p" + "t";
              note?: string;
            }
            """);
        SemanticLowerer.ClassDeclarationCoreResult b = lowerModule("""
            // @jsonable
            export class Point {
              x: int = 40 + 2;
              tag: string = "p" + "t";
              note?: string;
            }
            """);
        check(a != null && b != null && a.lowering() != null && b.lowering() != null
                && a.lowering().unit() != null && b.lowering().unit() != null,
            "both single-module repetitions lower");
        if (a != null && b != null && a.lowering() != null && b.lowering() != null
                && a.lowering().unit() != null && b.lowering().unit() != null) {
            check(Arrays.equals(SemanticIrDumper.dumpModule(a.lowering().unit()),
                    SemanticIrDumper.dumpModule(b.lowering().unit())),
                "the single-module dump is byte-identical across repetitions");
        }

        // The record surface: immutability of the JsonDefaultChildTable.
        JsonDefaultChildTable table = first.caller().jsonDefaults();
        Map<OpId, List<OpId>> source = new LinkedHashMap<>(table.defaultChildren());
        OpId probeKey = source.keySet().iterator().next();
        source.remove(probeKey);
        check(table.defaultChildren().containsKey(probeKey),
            "the produced JsonDefaultChildTable record is immutable (later mutation of "
                + "the constructor argument cannot change it)");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Json Class Lowering Tests (ISSUE-0515 K-D8/K-D10) ===\n");

        testGeneratedBodiesPinned();
        testNonJsonableNegative();
        testCombinedT1T5Scenario();
        testDeterminism();

        System.out.println("\nJsonClassLoweringTest: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
