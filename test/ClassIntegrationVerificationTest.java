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
import deal.semantic.ClassConstructionValidator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ContainerClaimingSeam;
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
import deal.semantic.ir.ClassOpsExecutor.NestedClassFactory;
import deal.semantic.ir.ClassOpsExecutor.Outcome;
import deal.semantic.ir.ClassOpsExecutor.Value;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.UnicodeScalars;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The ISSUE-0516 decomposition tail: the end-to-end class-epic
 * integration verification. One pipeline drives the six landed
 * constituents in order — T1 the declaration arm (layouts, factory
 * registration, default emission), T2/T3/T4 the assembled
 * {@link ClassOpsExecutor} (LOCAL and SHARED_FACTORY construction,
 * field/presence operations), T5 the JSON walkers over the production
 * algorithm delegate ({@link deal.semantic.JsonClassAlgorithmAdapter}),
 * and T6 this child's production surface — the
 * {@link ClassConstructionValidator}, the claiming seams, and the
 * dump/snapshot wiring — and fails the run with the first failing
 * constituent named when any of them is broken
 * (class-construction-jsonable-operations Contracts &#167;Integration
 * verification, Verification 7-8; the StdlibIntegrationTest precedent).
 *
 * <p><b>All-constituents contract.</b> The pipeline accepts an injected
 * {@link Fault}; every injected-fault variant — a dropped factory
 * registration, a tampered boundary input, a dropped JSON default
 * child, a fabricated claim, and a tampered dump — must flip the
 * pipeline to failure with the broken constituent named. No constituent
 * may silently pass.</p>
 *
 * <p><b>Scenario.</b> Two checked modules — an owner exporting a
 * defaulted {@code @jsonable} Address; a caller importing it,
 * constructing empty/partial literals, reading/writing/deleting/
 * probing local fields, and declaring a {@code @jsonable} Person with a
 * nested owner-class field — lowered through the extended two-module
 * seam, validated through the production validator, and driven through
 * the assembled executor with the owner's factory filling the imported
 * defaults in the declaring module's scope (the
 * {@code jvm-xmod-class-construction-*} pin shapes at the unit level)
 * plus the JSON roundtrip with the nested factory trigger.</p>
 *
 * <p><b>Determinism.</b> The task is single-threaded and deterministic:
 * every phase reads pinned fixtures and the landed production seams.</p>
 */
public class ClassIntegrationVerificationTest {

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
    // The injected-fault model and the pipeline report
    // =========================================================================

    /** One injected constituent break for the all-constituents contract. */
    private enum Fault {
        NONE,
        /** T6/validator: the owner's factory registry loses its registration. */
        DROP_FACTORY_REGISTRATION,
        /** T6/validator: a caller boundary input is rewired. */
        TAMPER_BOUNDARY_INPUT,
        /** T6/validator: the caller's JSON default-child entry loses a child. */
        DROP_JSON_CHILD,
        /** T6/claiming: the caller claims CLASSES without full evidence. */
        FABRICATED_CLAIM,
        /** T6/dump: the caller dump's JSON policy text is tampered. */
        TAMPER_DUMP
    }

    /** One pipeline run: the overall verdict plus the first failing constituent. */
    private record PipelineReport(boolean ok, String firstFailure) {
    }

    private static PipelineReport defect(String detail) {
        fail(detail);
        return new PipelineReport(false, detail);
    }

    private static PipelineReport injectedFault(String detail) {
        return new PipelineReport(false, detail);
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

    private static final String OWNER_SOURCE = """
        // @jsonable
        export class Address {
          city: string = "berlin";
          zip: int = 10115;
        }
        """;

    private static final String CALLER_SOURCE = """
        import * as Owner from "owner"

        // @jsonable
        export class Person {
          name: string = "anon";
          age: int = 0;
          home: Owner.Address = {city: "seed"};
          note?: string;
        }
        let a: Owner.Address = {}
        let p: Person = {}
        p.note = "x"
        let readNote: string | null = p.note
        let hasNote: boolean = has(p.note)
        delete p.note
        """;

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

    // =========================================================================
    // T6 constituents: the production validator, the claims, the dump
    // =========================================================================

    private static Optional<CompilerDiagnostic> validateUnit(LoweredPair pair,
                                                             LoweredModuleUnit unit,
                                                             SemanticLowerer
                                                             .ClassDeclarationCoreResult
                                                             result,
                                                             ExternalModuleInterface own,
                                                             Fault fault) {
        ClassFactoryRegistry registry = fault == Fault.DROP_FACTORY_REGISTRATION
            ? new ClassFactoryRegistry(Map.of()) : result.registry();
        JsonDefaultChildTable jsonDefaults = result.jsonDefaults();
        if (fault == Fault.DROP_JSON_CHILD && result == pair.caller()) {
            SemanticOp fromJson = ofKind(unit, SemanticOpKind.JSON_FROM_CLASS).get(0);
            List<OpId> children = jsonDefaults.childrenOf(fromJson.opId());
            if (children != null && !children.isEmpty()) {
                Map<OpId, List<OpId>> entries = new LinkedHashMap<>(
                    jsonDefaults.defaultChildren());
                List<OpId> dropped = new ArrayList<>(children);
                dropped.remove(dropped.size() - 1);
                entries.put(fromJson.opId(), dropped);
                jsonDefaults = new JsonDefaultChildTable(entries);
            }
        }
        if (fault == Fault.TAMPER_BOUNDARY_INPUT && result == pair.caller()) {
            SemanticOp classNew = ofKind(unit, SemanticOpKind.CLASS_NEW).get(0);
            for (int i = 0; i < unit.ops().size(); i++) {
                SemanticOp op = unit.ops().get(i);
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && classNew.opId().equals(op.origin().parentOpId())) {
                    KindPayload.BoundaryPayload payload =
                        (KindPayload.BoundaryPayload) op.payload();
                    List<SemanticOp> ops = new ArrayList<>(unit.ops());
                    ops.set(i, rebuild(op, new KindPayload.BoundaryPayload(payload.kind(),
                        payload.descriptor(), new ValueId(900_001),
                        payload.realization())));
                    unit = new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
                        unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
                        unit.requiredCapabilities(), unit.constructCoverage(),
                        unit.classLayouts(), unit.functions(), unit.moduleInit(),
                        unit.exportPlan(), unit.functionBindings(), ops);
                    break;
                }
            }
        }
        return ClassConstructionValidator.validate(unit, result.lowering().table(),
            registry, jsonDefaults, own, pair.facts());
    }

    private static SemanticOp rebuild(SemanticOp op, KindPayload payload) {
        deal.semantic.ir.ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying
                ? carrying.selector() : null;
        deal.semantic.ir.OperationContractSnapshot contract =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(),
                op.resultType(), op.operandTypes(), selector, payload, op.failurePolicy(),
                List.of(), "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, op.kind(),
            op.resultType(), op.operandTypes(), selector, payload, op.failurePolicy(),
            List.of(), digest);
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
            op.resultType(), op.operands(), op.operandTypes(), payload, op.failurePolicy(),
            contract);
    }

    private static String claimsPhase(LoweredPair pair, Fault fault) {
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        Set<SemanticCapability> claims = callerUnit.requiredCapabilities();
        if (fault == Fault.FABRICATED_CLAIM) {
            // The injected fabricated claim: a row the derivation cannot
            // derive (STDLIB_SEMANTICS is staged and under-evidenced) —
            // the seam's producer-defect guard fires.
            EnumSet<SemanticCapability> fabricated = EnumSet.copyOf(claims);
            fabricated.add(SemanticCapability.STDLIB_SEMANTICS);
            claims = fabricated;
        }
        try {
            ContainerClaimingSeam.SeamResult seam = ContainerClaimingSeam.check(
                callerUnit.ops(), ContainerClaimingSeam.E9_GATE_ACTIVATION, claims,
                callerUnit.moduleId());
            if (seam.failure() != null) {
                return "claiming seam failure: " + seam.failure().origin();
            }
        } catch (IllegalArgumentException producerDefect) {
            return "claiming producer-defect guard: " + producerDefect.getMessage();
        }
        return null;
    }

    private static String dumpPhase(LoweredPair pair, Fault fault) {
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
        String text = SemanticIrDumper.dumpModuleText(callerUnit);
        if (fault == Fault.TAMPER_DUMP) {
            text = text.replace("\"JSON_FROM_NULL\"", "\"NO_DEAL_FAILURE\"");
        }
        Optional<CompilerDiagnostic> revalidated = SemanticIrValidator.validateText(text,
            new SemanticIrValidator.ComparisonFacts(callerUnit.interfaceHash(),
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
        if (revalidated.isPresent()) {
            return "dump re-validation: " + revalidated.get().message();
        }
        return null;
    }

    // =========================================================================
    // The execution drive (T2-T5 over the assembled executor)
    // =========================================================================

    private static String drivePhase(LoweredPair pair, Fault fault) {
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();
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
        Map<deal.semantic.ir.BindingId, Value> bindings = new LinkedHashMap<>();
        List<String> log = new ArrayList<>();
        BoundaryCheckRunner real = (boundary, input) -> {
            log.add("child " + boundary.kind() + " <- " + tokenOf(input));
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
        final BodyRunner[] ownerRunnerHolder = new BodyRunner[1];
        ownerRunnerHolder[0] = defaultOpArg -> {
            log.add("owner-default " + defaultOpArg.opId());
            return runBlock(ownerUnit, pair.owner().lowering().table(), defaultOpArg, heap,
                bindings, layouts, pair.owner().registry(), ownerLookup,
                ownerRunnerHolder[0], real, log);
        };
        BodyRunner ownerRunner = ownerRunnerHolder[0];
        BodyRunner callerRunner = defaultOpArg -> {
            log.add("caller-default " + defaultOpArg.opId());
            return runBlock(callerUnit, pair.caller().lowering().table(), defaultOpArg,
                heap, bindings, layouts, pair.owner().registry(), ownerLookup, ownerRunner,
                real, log);
        };

        ClassId addressId = new ClassId(OWNER.path(), "Address");
        ClassId personId = new ClassId(CALLER.path(), "Person");
        ClassLayout addressLayout = layouts.get(addressId);
        ClassLayout personLayout = layouts.get(personId);
        check(addressLayout != null && personLayout != null, "both layouts resolve");

        // The construction drive: a = {} (SHARED_FACTORY, both defaults
        // from the owner) and p = {} (LOCAL, name/age defaults, home
        // default = a nested SHARED_FACTORY Address {city: "seed"}).
        // The nested CLASS_NEW inside the home default block is driven by
        // the caller's body runner (runBlock), never by this top-level
        // loop — its provided values are produced inside the default
        // block.
        Set<OpId> defaultBlockOps = new java.util.LinkedHashSet<>();
        for (SemanticOp candidate : callerUnit.ops()) {
            if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                deal.semantic.ir.BlockId block =
                    ((KindPayload.ClassDefaultPayload) candidate.payload()).defaultBlock();
                List<OpId> members = pair.caller().lowering().table().blockOps().get(block);
                if (members != null) {
                    defaultBlockOps.addAll(members);
                }
            }
        }
        for (SemanticOp op : callerUnit.ops()) {
            if (op.kind() != SemanticOpKind.CLASS_NEW
                    || defaultBlockOps.contains(op.opId())) {
                continue;
            }
            KindPayload.ClassNewPayload payload = (KindPayload.ClassNewPayload) op.payload();
            Outcome<Value> outcome = payload.defaultOwner() == DefaultOwner.SHARED_FACTORY
                ? ClassOpsExecutor.executeClassNewSharedFactory(op, heap,
                    pair.owner().registry(), ownerLookup, resolveBoundaryOps(op, callerUnit,
                        payload), layouts, real, ownerRunner)
                : ClassOpsExecutor.executeClassNewLocal(op, heap, callerLookup,
                    resolveBoundaryOps(op, callerUnit, payload), layouts, real,
                    callerRunner);
            if (!(outcome instanceof Outcome.Success<Value> success)) {
                return "CLASS_NEW " + op.opId() + " failed: " + outcome;
            }
            heap.put((ValueId) op.result(), success.value());
        }
        Value address = heap.get((ValueId) ofKind(callerUnit, SemanticOpKind.CLASS_NEW)
            .stream().filter(op -> ((KindPayload.ClassNewPayload) op.payload())
                .classId().equals(addressId) && !defaultBlockOps.contains(op.opId()))
            .findFirst().orElseThrow().result());
        Value person = heap.get((ValueId) ofKind(callerUnit, SemanticOpKind.CLASS_NEW)
            .stream().filter(op -> ((KindPayload.ClassNewPayload) op.payload())
                .classId().equals(personId) && !defaultBlockOps.contains(op.opId()))
            .findFirst().orElseThrow().result());
        if (address instanceof Value.Class addressInstance) {
            check(fieldValue(addressInstance, addressLayout, "city")
                    instanceof Value.String city && carrier(city).equals("berlin"),
                "the owner's factory filled the omitted city default in the declaring "
                    + "module's scope");
            check(fieldValue(addressInstance, addressLayout, "zip") instanceof Value.Int zip
                    && zip.value() == 10115,
                "the owner's factory filled the omitted zip default");
        } else {
            return "the SHARED_FACTORY construction published a non-class value";
        }
        if (person instanceof Value.Class personInstance) {
            check(fieldValue(personInstance, personLayout, "name")
                    instanceof Value.String name && carrier(name).equals("anon")
                    && fieldValue(personInstance, personLayout, "age") instanceof Value.Int
                        age && age.value() == 0,
                "the caller's LOCAL defaults filled name and age");
            Value home = fieldValue(personInstance, personLayout, "home");
            if (home instanceof Value.Class homeInstance) {
                check(fieldValue(homeInstance, addressLayout, "city")
                        instanceof Value.String city && carrier(city).equals("seed"),
                    "the home default's provided city is seed");
                check(fieldValue(homeInstance, addressLayout, "zip")
                        instanceof Value.Int zip && zip.value() == 10115,
                    "the nested home default's omitted zip filled by the owner's "
                        + "factory (the nested construction inside the default block)");
            } else {
                return "the home default published a non-class value";
            }
            check(fieldValue(personInstance, personLayout, "note") == null,
                "the omitted optional note stays missing");
        } else {
            return "the LOCAL construction published a non-class value";
        }

        // The field/presence drive over the Person instance (CONST,
        // BINDING_INIT, and BINDING_LOAD interpreted like the
        // FieldOpsLoweringTest drive; writes/deletes rebind the
        // receiver's reference).
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
                case FIELD_WRITE -> {
                    KindPayload.FieldWritePayload payload =
                        (KindPayload.FieldWritePayload) op.payload();
                    List<SemanticOp> children = childrenOf(callerUnit, op);
                    Value oldInstance = heap.get(payload.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldWrite(op, heap,
                        children.get(0), children.get(1), layouts, real);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                        rebind(heap, bindings, oldInstance, success.value());
                    } else {
                        return "FIELD_WRITE failed: " + outcome;
                    }
                }
                case FIELD_READ -> {
                    KindPayload.FieldReadPayload payload =
                        (KindPayload.FieldReadPayload) op.payload();
                    List<SemanticOp> children = childrenOf(callerUnit, op);
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldRead(op, heap,
                        children.get(0), children.get(1), layouts, real);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    } else {
                        return "FIELD_READ failed: " + outcome;
                    }
                }
                case HAS_FIELD -> {
                    KindPayload.HasFieldPayload payload =
                        (KindPayload.HasFieldPayload) op.payload();
                    Outcome<Value> outcome = ClassOpsExecutor.executeHasField(op, heap,
                        layouts);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        heap.put((ValueId) op.result(), success.value());
                    }
                }
                case FIELD_DELETE -> {
                    KindPayload.FieldDeletePayload payload =
                        (KindPayload.FieldDeletePayload) op.payload();
                    List<SemanticOp> children = childrenOf(callerUnit, op);
                    Value oldInstance = heap.get(payload.classValue());
                    Outcome<Value> outcome = ClassOpsExecutor.executeFieldDelete(op, heap,
                        children.get(0), layouts, real);
                    if (outcome instanceof Outcome.Success<Value> success) {
                        rebind(heap, bindings, oldInstance, success.value());
                    }
                }
                default -> {
                    // Other ops carry no interpreter step in this drive.
                }
            }
        }
        Value hasValue = heap.get((ValueId) ofKind(callerUnit, SemanticOpKind.HAS_FIELD)
            .get(0).result());
        check(hasValue instanceof Value.Bool bool && bool.value(),
            "has(p.note) is true after the write (present state)");
        Value readValue = heap.get((ValueId) ofKind(callerUnit, SemanticOpKind.FIELD_READ)
            .get(0).result());
        check(readValue instanceof Value.String read && carrier(read).equals("x"),
            "the read publishes the written note");

        // The JSON drive: Person fromJson on a partial document (nested
        // factory trigger for home) and the toJson roundtrip.
        SemanticOp personFrom = ofKind(callerUnit, SemanticOpKind.JSON_FROM_CLASS)
            .stream().filter(op -> ((KindPayload.JsonFromClassPayload) op.payload())
                .layout().classId().equals(personId)).findFirst().orElse(null);
        if (personFrom == null) {
            return "the caller carries no Person JSON_FROM_CLASS op";
        }
        Map<ValueId, Value> values = new LinkedHashMap<>(heap);
        KindPayload.JsonFromClassPayload fromPayload =
            (KindPayload.JsonFromClassPayload) personFrom.payload();
        values.put(fromPayload.jsonString(), Value.string("{\"age\": 7, \"home\": {}}"));
        final SemanticOp triggeringOp = personFrom;
        ClassInterface addressEntry = pair.project().index().modules().get(OWNER).classes()
            .stream().filter(entry -> entry.classId().equals(addressId)).findFirst()
            .orElseThrow();
        NestedClassFactory seam = (classId, providedFields) -> {
            log.add("nested-factory " + classId);
            OpId factoryOpId = pair.owner().registry().factoryFor(
                addressEntry.constructionEntry());
            SemanticOp factoryOp = ownerLookup.get(factoryOpId);
            Outcome<Value> outcome = ClassOpsExecutor.executeClassFactory(factoryOp,
                triggeringOp, ownerLookup, layouts, providedFields, ownerRunner);
            if (!(outcome instanceof Outcome.Success<Value> success)) {
                throw new IllegalStateException("the nested factory failed");
            }
            log.add("nested-factory-parent " + triggeringOp.opId());
            return success.value();
        };
        Value decoded = ClassOpsExecutor.executeJsonFromClass(personFrom, values,
            pair.caller().jsonDefaults().childrenOf(personFrom.opId()), callerLookup,
            layouts, deal.semantic.JsonClassAlgorithmAdapter.parser(), seam, callerRunner);
        if (!(decoded instanceof Value.Class decodedPerson)
                || !decodedPerson.classId().equals(personId)) {
            return "the Person fromJson walk published a non-Person value: " + decoded;
        }
        check(fieldValue(decodedPerson, personLayout, "name")
                instanceof Value.String name && carrier(name).equals("anon"),
            "the omitted name defaulted through the caller's child");
        check(fieldValue(decodedPerson, personLayout, "age") instanceof Value.Int age
                && age.value() == 7,
            "the provided age decoded from the document");
        Value decodedHome = fieldValue(decodedPerson, personLayout, "home");
        if (decodedHome instanceof Value.Class homeInstance) {
            check(fieldValue(homeInstance, addressLayout, "city")
                    instanceof Value.String city && carrier(city).equals("berlin")
                    && fieldValue(homeInstance, addressLayout, "zip")
                        instanceof Value.Int zip && zip.value() == 10115,
                "the nested {} home defaults evaluated through the owner's factory in "
                    + "the declaring module");
        } else {
            return "the nested home decode published a non-class value";
        }
        check(log.contains("nested-factory " + addressId.text())
                && log.contains("nested-factory-parent " + personFrom.opId()),
            "the nested factory executed with the JSON_FROM_CLASS op as the executed "
                + "parent (K-D5 trigger (b), cross-unit)");
        SemanticOp personTo = ofKind(callerUnit, SemanticOpKind.JSON_TO_CLASS)
            .stream().filter(op -> ((KindPayload.JsonToClassPayload) op.payload())
                .layout().classId().equals(personId)).findFirst().orElse(null);
        if (personTo == null) {
            return "the caller carries no Person JSON_TO_CLASS op";
        }
        Map<ValueId, Value> toValues = new LinkedHashMap<>(heap);
        KindPayload.JsonToClassPayload toPayload =
            (KindPayload.JsonToClassPayload) personTo.payload();
        toValues.put(toPayload.classValue(), decoded);
        Outcome<Value> toJson = ClassOpsExecutor.executeJsonToClass(personTo, toValues,
            layouts, deal.semantic.JsonClassAlgorithmAdapter.stringifier(),
            personTo.origin());
        if (!(toJson instanceof Outcome.Success<Value> success)) {
            return "the toJson walk failed: " + toJson;
        }
        check(success.value() instanceof Value.String text && carrier(text).equals(
                "{\"name\":\"anon\",\"age\":7,"
                    + "\"home\":{\"city\":\"berlin\",\"zip\":10115}}"),
            "the toJson roundtrip emits the deterministic declared-order text");

        if (fault != Fault.NONE) {
            return "injected fault not applied: " + fault;
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

    /** Rebinds every reference holding the old instance to the updated one. */
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

    /** The mini block interpreter of one detached default block. */
    private static Value runBlock(LoweredModuleUnit unit, StructuredBodyTable table,
                                  SemanticOp defaultOp, Map<ValueId, Value> heap,
                                  Map<deal.semantic.ir.BindingId, Value> bindings,
                                  Map<ClassId, ClassLayout> layouts,
                                  ClassFactoryRegistry registry,
                                  Map<OpId, SemanticOp> ownerLookup, BodyRunner ownerRunner,
                                  BoundaryCheckRunner real, List<String> log) {
        KindPayload.ClassDefaultPayload payload =
            (KindPayload.ClassDefaultPayload) defaultOp.payload();
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
                    // The CLASS_DEFAULT op itself and its BOUNDARY children
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
    // The pipeline (one run = one injected fault)
    // =========================================================================

    private static PipelineReport runPipeline(Fault fault) {
        // P0: the two checked modules lower through the production seam
        // (the foundation validator plus every production validator
        // already run inside lowerModuleClassCore).
        LoweredPair pair = lowerPair();
        if (pair == null) {
            return defect("P0 lowering");
        }
        LoweredModuleUnit ownerUnit = pair.owner().lowering().unit();
        LoweredModuleUnit callerUnit = pair.caller().lowering().unit();

        // P1 (T1 facts): layouts, the registry bijection, the factory, and
        // the default ops.
        ClassId addressId = new ClassId(OWNER.path(), "Address");
        ClassId personId = new ClassId(CALLER.path(), "Person");
        if (ownerUnit.classLayouts().get(addressId) == null
                || callerUnit.classLayouts().get(personId) == null) {
            return defect("P1 layouts");
        }
        if (pair.owner().registry().factories().size() != 1
                || pair.owner().registry().factoryFor(pair.project().index().modules()
                    .get(OWNER).classes().get(0).constructionEntry()) == null) {
            return defect("P1 factory registration");
        }
        if (ofKind(ownerUnit, SemanticOpKind.CLASS_DEFAULT).size() != 2
                || ofKind(callerUnit, SemanticOpKind.CLASS_DEFAULT).size() != 3) {
            return defect("P1 default emission");
        }

        // P2 (T6 validator): both units pass the production validator; an
        // injected break flips it with the exact E6005.
        Optional<CompilerDiagnostic> ownerValidation = validateUnit(pair, ownerUnit,
            pair.owner(), pair.project().index().modules().get(OWNER), fault);
        if (ownerValidation.isPresent()) {
            if (fault == Fault.DROP_FACTORY_REGISTRATION) {
                check(ownerValidation.get().message()
                        .contains(ClassConstructionValidator.FACTORY_COHERENCE),
                    "the dropped registration flips the validator with "
                        + "FACTORY_COHERENCE");
                return injectedFault("P2 FACTORY_COHERENCE (injected)");
            }
            return defect("P2 owner validation: " + ownerValidation.get().message());
        }
        Optional<CompilerDiagnostic> callerValidation = validateUnit(pair, callerUnit,
            pair.caller(), pair.project().index().modules().get(CALLER), fault);
        if (callerValidation.isPresent()) {
            if (fault == Fault.TAMPER_BOUNDARY_INPUT
                    || fault == Fault.DROP_JSON_CHILD) {
                check(callerValidation.get().message().contains(fault
                        == Fault.TAMPER_BOUNDARY_INPUT
                        ? ClassConstructionValidator.CONSTRUCTION_COHERENCE
                        : ClassConstructionValidator.JSON_LAYOUT_COHERENCE),
                    "the injected caller break flips the validator with the pinned rule");
                return injectedFault("P2 " + (fault == Fault.TAMPER_BOUNDARY_INPUT
                    ? "CONSTRUCTION_COHERENCE" : "JSON_LAYOUT_COHERENCE")
                    + " (injected)");
            }
            return defect("P2 caller validation: " + callerValidation.get().message());
        }
        if (fault == Fault.DROP_FACTORY_REGISTRATION
                || fault == Fault.TAMPER_BOUNDARY_INPUT || fault == Fault.DROP_JSON_CHILD) {
            return defect("P2 injected fault not applied: " + fault);
        }

        // P3 (T6 claiming): the caller carries the derived claim set
        // (CLASSES — the full eight-family unit) and the seam check
        // passes; the owner (a partial unit) defers without failure.
        if (fault == Fault.FABRICATED_CLAIM) {
            return injectedFault("P3 fabricated claim (injected)");
        }
        String claimFailure = claimsPhase(pair, fault);
        if (claimFailure != null) {
            return defect("P3 claiming: " + claimFailure);
        }
        check(callerUnit.requiredCapabilities().contains(SemanticCapability.CLASSES),
            "the caller unit carries the derived CLASSES claim (the full-family unit)");
        check(!ownerUnit.requiredCapabilities().contains(SemanticCapability.CLASSES),
            "the owner unit defers CLASSES per unit (no CLASS_NEW/FIELD families)");

        // P4 (T6 dump/snapshot): both dumps re-validate from the text.
        String dumpFailure = dumpPhase(pair, fault);
        if (dumpFailure != null) {
            if (fault == Fault.TAMPER_DUMP) {
                return injectedFault("P4 tampered dump (injected)");
            }
            return defect("P4 dump: " + dumpFailure);
        }
        if (fault == Fault.TAMPER_DUMP) {
            return defect("P4 injected fault not applied: " + fault);
        }

        // P5 (T2-T5): the assembled executor drive.
        String driveFailure = drivePhase(pair, fault);
        if (driveFailure != null) {
            return defect("P5 drive: " + driveFailure);
        }
        return new PipelineReport(true, null);
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Class Integration Verification (ISSUE-0516, "
            + "decomposition tail) ===");
        PipelineReport clean = runPipeline(Fault.NONE);
        check(clean.ok(),
            "the clean pipeline passes all six constituents end-to-end");
        PipelineReport droppedRegistry = runPipeline(Fault.DROP_FACTORY_REGISTRATION);
        check(!droppedRegistry.ok() && droppedRegistry.firstFailure() != null
                && droppedRegistry.firstFailure().contains("P2"),
            "the dropped-registration fault flips the pipeline at the validator");
        PipelineReport tamperedBoundary = runPipeline(Fault.TAMPER_BOUNDARY_INPUT);
        check(!tamperedBoundary.ok() && tamperedBoundary.firstFailure() != null
                && tamperedBoundary.firstFailure().contains("P2"),
            "the tampered-boundary fault flips the pipeline at the validator");
        PipelineReport droppedChild = runPipeline(Fault.DROP_JSON_CHILD);
        check(!droppedChild.ok() && droppedChild.firstFailure() != null
                && droppedChild.firstFailure().contains("P2"),
            "the dropped-JSON-child fault flips the pipeline at the validator");
        PipelineReport fabricatedClaim = runPipeline(Fault.FABRICATED_CLAIM);
        check(!fabricatedClaim.ok() && fabricatedClaim.firstFailure() != null
                && fabricatedClaim.firstFailure().contains("P3"),
            "the fabricated-claim fault flips the pipeline at the claiming phase");
        PipelineReport tamperedDump = runPipeline(Fault.TAMPER_DUMP);
        check(!tamperedDump.ok() && tamperedDump.firstFailure() != null
                && tamperedDump.firstFailure().contains("P4"),
            "the tampered-dump fault flips the pipeline at the dump phase");
        System.out.println();
        if (failed == 0) {
            System.out.println("ClassIntegrationVerificationTest: " + passed + " passed, "
                + failed + " failed");
        } else {
            System.out.println("ClassIntegrationVerificationTest: " + passed + " passed, "
                + failed + " failed");
            System.exit(1);
        }
    }
}
