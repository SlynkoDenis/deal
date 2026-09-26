package deal.semantic;

import deal.ast.Block;
import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.VariableDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0676: the intrinsic value materialization — the identity-preserving
 * function-typed load and the real memoized conversion-intrinsic carrier on
 * both shared targets and in the semantic oracle (design sources
 * {@code conversion-intrinsic-function-values} J1/J2 and
 * {@code function-typed-value-materialization-and-dispatch} M2 item 1/M4).
 *
 * <ol>
 *   <li><b>The seeded identity's function-typed load (J1).</b> The seed
 *       incarnation carries the tracked function identity, so a typed load
 *       of the intrinsic binding publishes the producer-less seeded
 *       identity unchanged, every alias load republishes the same identity,
 *       no {@code DynamicFunctionValue} is registered for it, and the unit
 *       passes both closed gates. The identity-preserving exclusion is per
 *       publishing op and closed over the alias chain (the alias load
 *       names a cell whose {@code BINDING_INIT} carries the seeded
 *       identity), while a load naming a cell initialized with another
 *       identity stays a producing position.</li>
 *   <li><b>The memoized carrier on both targets (J2).</b> The LuaJIT
 *       accessor returns the real carrier — the conversion invoker, the
 *       declared descriptor text and canonical spec text, no function id,
 *       the intrinsic kind tag — one object per kind per program, so the
 *       seed's {@code BINDING_INIT} and the adapter's producer-less
 *       {@code AdaptSourceRef.Value} operand publish the identical object
 *       and the identity-preserving load never replaces it with a slot
 *       read; the residual export-read kind arm publishes the memoized
 *       carrier for a registered identity and a fresh real carrier surface
 *       otherwise (the landed per-read allocation); the JVM carrier is the
 *       landed {@code FunctionValue} subclass with the closed kind.</li>
 *   <li><b>The oracle value (J2).</b> The seeded value carries the closed
 *       kind, is keyed once in the value-keyed binding map to its
 *       {@code IntrinsicFunction} registration, a load republishes the
 *       same object, and the class-ops and boundary views project the
 *       kind's declared signature (the materialization-site function row
 *       admits the carrier and a differing declared signature keeps the
 *       pinned E8010 texts).</li>
 * </ol>
 *
 * <p>Every assertion reads the produced unit, the emitted artifacts, or a
 * real consumer run under the real toolchains; no parallel registration,
 * carrier, or behavior surface exists. The value-position program carries
 * the seed write and the alias declarations over one identity, so the
 * closed gate's seed-write counting admits the declaration's re-publication
 * of the seed write and its identity-preserving alias loads, while a
 * doctored unit whose seeded identity is also produced by another op (or by
 * a load naming a cell initialized with another identity) still fails the
 * seed clause.</p>
 */
public class IntrinsicValueMaterializationTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual), message + " (expected "
            + expected + ", got " + actual + ")");
    }

    private static final ModuleId MODULE = new ModuleId("app");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    // =========================================================================
    // Fixtures
    // =========================================================================

    /**
     * The value-position program: two bindings of the {@code int} intrinsic,
     * an alias chain, an identity comparison of the alias against the first
     * binding, and the {@code number} intrinsic bound and compared against
     * itself. Every function-typed result is the seeded identity or a load
     * republishing it.
     */
    private static final String VALUE_POSITION_SOURCE = """
        let f: (x: number) => int = int;
        let g: (x: number) => int = f;
        let h: (x: number) => int = g;
        let same: boolean = f === h;
        let numberValue: (x: int) => number = number;
        let sameNumber: boolean = numberValue === number;

        export function probe(): boolean {
          return same;
        }

        export function main(): null {
          return null;
        }
        """;

    /**
     * The adapted declaration over the intrinsic (the arity-extension
     * shape): the producer-less {@code AdaptSourceRef.Value} operand is the
     * seeded identity itself.
     */
    private static final String ADAPTER_SOURCE = """
        let wide: (x: number, y: number) => int = int;
        let x: int = 1;
        let r: int = x;

        export function main(): null {
          return null;
        }
        """;

    /**
     * The combined drive (J6 item 4): one unit carrying both a
     * value-position use of the {@code int} intrinsic (the typed binding
     * whose load republishes the seeded identity, its declaration's
     * re-publication of the seed write, and the reference-identity drives)
     * and the adapted declaration over the same intrinsic (the
     * producer-less {@code AdaptSourceRef.Value} operand naming the seeded
     * identity).
     */
    private static final String COMBINED_SOURCE = """
        let f: (x: number) => int = int;
        let wide: (x: number, y: number) => int = int;
        let same: boolean = f === f;

        export function main(): null {
          return null;
        }
        """;

    // =========================================================================
    // The checked-project and lowering helpers
    // =========================================================================

    private record CheckedSlice(ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private record Fixture(CheckedProjectInput input, ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           CheckedModuleInput module) {
    }

    private record RawLowering(LoweredModuleUnit unit, StructuredBodyTable table,
                               SemanticLowerer.ModuleLowerer lowerer) {
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath,
                    String importingModule, Set<String> modulesInProgress)
                    throws ModuleResolver.ModuleNotFoundException {
                Map<String, Map<String, Type>> exports =
                    deal.module.StdlibModuleResolver.stdlibExports(
                        Path.of("std").toAbsolutePath().toString());
                Map<String, Type> moduleExports = exports.get(modulePath);
                if (moduleExports == null) {
                    throw new ModuleResolver.ModuleNotFoundException(
                        "Module not found: " + modulePath);
                }
                return moduleExports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className,
                    String modulePath, String importingModule) {
                return null;
            }
        };
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": checks cleanly: "
            + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), symTable, result);
    }

    private static List<ExportInterface> exportsOf(ProgramNode program) {
        List<ExportInterface> exports = new ArrayList<>();
        for (StatementNode statement : program.statements()) {
            if (statement instanceof ExportDeclaration export
                    && export.declaration() instanceof FunctionDeclaration function) {
                exports.add(new ExportInterface(function.name(), "function"));
            }
        }
        return exports;
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static Fixture fixture(String source, String what) {
        CheckedSlice slice = checkSlice(source, what);
        if (slice == null) {
            return null;
        }
        CheckedModuleInput module = new CheckedModuleInput(MODULE, SOURCE_ID,
            Path.of("test.deal"), slice.program(), slice.checks(),
            List.<ResolvedImport>of(), exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        List<ModuleFact> facts = List.of(new ModuleFact(SOURCE_ID, MODULE, false, false,
            slice.program(), Map.of(), slice.symbols(), slice.checks(), List.of()));
        CompilerInvocation invocation = invocation();
        CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation, MODULE,
            facts);
        check(built != null && !built.hasErrors() && built.input() != null
                && built.index() != null,
            what + ": the checked project builds: "
                + (built == null ? "null" : built.diagnostics()));
        if (built == null || built.hasErrors() || built.input() == null
                || built.index() == null) {
            return null;
        }
        RequirementManifestResult manifestResult = LoweringSupport.computeManifests(
            invocation, built.input(), built.index());
        check(manifestResult != null && manifestResult.diagnostics().isEmpty(),
            what + ": the requirement manifests compute: "
                + (manifestResult == null ? "null" : manifestResult.diagnostics()));
        if (manifestResult == null || !manifestResult.diagnostics().isEmpty()) {
            return null;
        }
        return new Fixture(built.input(), built.index(), manifestResult.manifests(),
            module);
    }

    /** The direct per-module project walk (the produced, pre-gate unit). */
    private static RawLowering rawLower(Fixture fixture, String what) {
        SemanticIdAllocator allocator = SemanticIdAllocator.over(List.of(MODULE));
        ExternalModuleInterface ownInterface = fixture.index().modules().get(MODULE);
        SemanticLowerer.ModuleLowerer lowerer = new SemanticLowerer.ModuleLowerer(
            MODULE, SOURCE_ID, fixture.module().checks(), allocator,
            true, true, true, false, false, false, fixture.module().ast().span(),
            true, true, ownInterface, Map.of());
        lowerer.setModuleImports(fixture.module().imports());
        lowerer.setRegistrationSeeds(ClassRegistrationSeeds.builtinErrorOnly());
        lowerer.setDeclaredConversionIntrinsics(
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT));
        lowerer.setE7Facts(fixture.module().exports(), Map.of(), Map.of(), Set.of());
        try {
            lowerer.lowerProjectModule(fixture.module().ast().statements());
        } catch (RuntimeException defect) {
            check(false, what + ": the walk produces the unit: " + defect);
            return null;
        }
        LoweredModuleUnit unit = lowerer.buildUnit(
            fixture.manifests().get(0).constructCoverage(),
            fixture.module().imports().stream().map(ResolvedImport::resolvedModuleId)
                .toList(),
            fixture.index().interfaceIndexDigest(), REGISTRY_HASH,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        return new RawLowering(unit, lowerer.bodyTable(), lowerer);
    }

    private static ExecutableLoweredProject projectOf(LoweredModuleUnit unit) {
        return new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32,
            new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(MODULE, new ExternalModuleInterface(MODULE,
                    ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
                    InitializationMode.ONCE_AFTER_DEPENDENCIES))),
            Map.of(MODULE, unit), MODULE);
    }

    private static SemanticIrValidator.ComparisonFacts facts(LoweredModuleUnit unit) {
        return new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    // =========================================================================
    // Unit inspection helpers
    // =========================================================================

    /** The unit's registration of one identity, or null. */
    private static FunctionExecutionBinding registrationOf(LoweredModuleUnit unit,
                                                           long identity) {
        return unit.functionBindings().get(new FunctionAllocationIdentity(identity));
    }

    /** The seeded identity of one intrinsic kind (the unit's own registration). */
    private static long seedIdentity(LoweredModuleUnit unit, IntrinsicKind kind) {
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic && intrinsic.kind() == kind) {
                return entry.getKey().id();
            }
        }
        return -1;
    }

    /** The seed {@code BINDING_INIT} of one seeded identity, or null. */
    private static SemanticOp seedInit(LoweredModuleUnit unit, long seedIdentity) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() == seedIdentity) {
                return op;
            }
        }
        return null;
    }

    /** The function-typed builds whose result identity is the given one. */
    private static List<SemanticOp> producersOf(LoweredModuleUnit unit, long identity) {
        List<SemanticOp> producers = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId value && value.id() == identity) {
                producers.add(op);
            }
        }
        return producers;
    }

    private static String luaCell(long bindingId, long generation) {
        return "S.b" + bindingId + "g" + generation;
    }

    private static String jvmCell(long bindingId, long generation) {
        return "b" + bindingId + "g" + generation;
    }

    /** One binding cell (a binding plus its generation). */
    private record CellRef(BindingId binding, long generation) {
    }

    // =========================================================================
    // 1. The seeded identity's function-typed load (J1)
    // =========================================================================

    private static void testSeededIdentityPreservation() {
        System.out.println("-- J1: the seed incarnation's tracked identity, the "
            + "identity-preserving typed load, and the alias republishing --");
        Fixture fixture = fixture(VALUE_POSITION_SOURCE, "value position");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "value position");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();

        long intSeed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
        long numberSeed = seedIdentity(unit, IntrinsicKind.NUMBER_CONVERT);
        check(intSeed > 0 && numberSeed > 0,
            "the unit carries one IntrinsicFunction registration per conversion "
                + "intrinsic; got int=" + intSeed + " number=" + numberSeed);
        if (intSeed < 0 || numberSeed < 0) {
            return;
        }
        int intrinsicRegistrations = 0;
        int dynamicRegistrations = 0;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.IntrinsicFunction) {
                intrinsicRegistrations++;
            }
            if (binding instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                dynamicRegistrations++;
            }
        }
        checkEq(2, intrinsicRegistrations,
            "the unit carries exactly the two seed IntrinsicFunction registrations");
        checkEq(0, dynamicRegistrations,
            "no DynamicFunctionValue is registered for an intrinsic load");

        // Every function-typed result carries exactly one registration
        // (R-FUNCTION-BINDING): the loads publish a seeded identity and the
        // entry closures their LoweredBody.
        int functionTypedResults = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId value
                    && op.resultType() instanceof RuntimeDescriptor.Func) {
                functionTypedResults++;
                check(registrationOf(unit, value.id()) != null,
                    "every function-typed result is registered (op " + op.opId()
                        + " kind " + op.kind() + " result " + value.id() + ")");
            }
        }
        check(functionTypedResults >= 6,
            "the value-position program lowers its function-typed results; got "
                + functionTypedResults);

        SemanticOp intSeedInit = seedInit(unit, intSeed);
        check(intSeedInit != null, "the int seed BINDING_INIT exists");
        if (intSeedInit == null) {
            return;
        }
        KindPayload.BindingInitPayload intInit =
            (KindPayload.BindingInitPayload) intSeedInit.payload();

        // The identity-preserving loads of the int seed: the load of the
        // intrinsic binding's own cell and the alias loads of the bindings
        // holding the identity — every one a BINDING_LOAD whose result is
        // the seeded identity, and no other op produces it.
        int loads = 0;
        int aliasLoads = 0;
        boolean seedCellLoad = false;
        for (SemanticOp producer : producersOf(unit, intSeed)) {
            check(producer.kind() == SemanticOpKind.BINDING_LOAD,
                "the only producer of the seeded identity is an identity-preserving "
                    + "load (got " + producer.kind() + " at " + producer.opId() + ")");
            if (producer.kind() != SemanticOpKind.BINDING_LOAD) {
                continue;
            }
            KindPayload.BindingLoadPayload load =
                (KindPayload.BindingLoadPayload) producer.payload();
            loads++;
            if (load.binding().equals(intInit.binding())
                    && load.generation() == intInit.generation()) {
                seedCellLoad = true;
            } else {
                // The exclusion is per publishing op (ISSUE-0675) and closed
                // over the alias chain (J1's alias-load refinement): the
                // alias load preserves the seeded identity because the cell
                // it names was initialized with that identity (the alias
                // declaration's re-publication), so the identity stays out
                // of the producing positions. A load naming a cell whose
                // init carries another identity stays a producing position
                // (the foreign-load negative below).
                aliasLoads++;
                check(cellInitCarries(unit, load.binding(), load.generation(), intSeed),
                    "each alias load reads a cell whose BINDING_INIT carries the seeded "
                        + "identity (the alias declaration's re-publication); cell b"
                        + load.binding().id() + "g" + load.generation());
            }
        }
        check(loads >= 4,
            "the program carries the seed-cell load and the alias loads republishing "
                + "the seeded identity; got " + loads);
        check(seedCellLoad, "the typed load of the intrinsic binding reads the seed "
            + "BINDING_INIT's own cell");
        check(aliasLoads >= 3,
            "the identity-preserving alias loads republish the seeded identity; got "
                + aliasLoads);

        // The declarations over the identity: the seed write plus the alias
        // declarations storing the same identity (each a BINDING_INIT whose
        // operand is the seeded identity).
        int initsOverSeed = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() == intSeed) {
                initsOverSeed++;
            }
        }
        check(initsOverSeed >= 3,
            "every alias declaration republishes the seeded identity (the f/g/h "
                + "BINDING_INITs carry it); got " + initsOverSeed);

        // The produced unit passes both closed gates with the load present
        // (the T2 clause is load-bearing: the load itself is not a producing
        // position).
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), "the load-carrying unit passes the closed bindings "
            + "gate (REGISTRY_ONE_TO_ONE and ADAPTER_SOURCE_SHAPE): "
            + bindings.map(CompilerDiagnostic::message).orElse("admission"));
        Optional<CompilerDiagnostic> schema =
            SemanticIrValidator.validate(unit, facts(unit));
        check(schema.isEmpty(), "the load-carrying unit passes the closed schema gate "
            + "(R-FUNCTION-BINDING and the shape clauses): "
            + schema.map(CompilerDiagnostic::message).orElse("admission"));

        // The load-bearing T2 negative: another producing op over the seeded
        // identity still fails the seed clause.
        LoweredModuleUnit doctored = withOp(unit, exportReadOf(intSeed, unit));
        Optional<CompilerDiagnostic> doctoredFailure = BindingsProductionValidator
            .validate(doctored, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(doctoredFailure.isPresent()
                && "E6005".equals(doctoredFailure.get().code())
                && doctoredFailure.get().message().contains("REGISTRY_ONE_TO_ONE"),
            "a doctored unit whose seeded identity is also produced by an EXPORT_READ "
                + "still fails the seed clause: "
                + doctoredFailure.map(CompilerDiagnostic::message).orElse("admission"));

        // The merged rule's closed direction: an identity-preserving load is
        // one whose named cell carries the identity. A load naming a cell
        // whose BINDING_INIT carries another identity is a producing
        // position even when its result is the seeded identity, so the seed
        // clause stays load-bearing for the alias-flow spelling too.
        CellRef foreignCell = foreignFunctionCell(unit, intSeed);
        check(foreignCell != null, "the unit carries a function-typed cell initialized "
            + "with another identity (the foreign-load target)");
        if (foreignCell != null) {
            SemanticOp foreignLoad = foreignLoadOf(foreignCell, intSeed, unit);
            BlockId seedBlock = raw.table().opBlocks().get(intSeedInit.opId());
            LoweredModuleUnit foreignUnit = withOp(unit, foreignLoad);
            Optional<CompilerDiagnostic> foreignFailure = BindingsProductionValidator
                .validate(foreignUnit, withTableOp(raw.table(), foreignLoad, seedBlock),
                    raw.lowerer().pinnedWriteFacts());
            check(foreignFailure.isPresent()
                    && "E6005".equals(foreignFailure.get().code())
                    && foreignFailure.get().message().contains("REGISTRY_ONE_TO_ONE"),
                "a doctored load naming a cell whose init carries another identity over "
                    + "the seeded identity still fails the seed clause: "
                    + foreignFailure.map(CompilerDiagnostic::message).orElse("admission"));
        }

        // The emitted sites: the seed's BINDING_INIT publishes the memoized
        // carrier (never a slot read of the identity it has not filled), the
        // load reads the seed cell, and neither target emits the removed
        // marker.
        String lua = LuaSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()), Map.of(MODULE, new ClassFactoryRegistry(Map.of())));
        String jvm = JvmSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of()))).source();
        String seedCellLua = luaCell(intInit.binding().id(), intInit.generation());
        String seedCellJvm = jvmCell(intInit.binding().id(), intInit.generation());
        check(lua.contains(seedCellLua
                + " = __intrinsicFn(\"INT_CONVERT\", \"function(number;int)\", "
                + "\"(number)->int\")"),
            "the LuaJIT seed BINDING_INIT publishes the memoized declared-signature "
                + "carrier: " + seedCellLua);
        check(!lua.contains(seedCellLua + " = S.v" + intSeed),
            "the LuaJIT seed BINDING_INIT is never a slot read of the seeded identity");
        check(!lua.contains("__f = true"),
            "the LuaJIT artifact carries no marker placeholder");
        check(lua.contains("S.v" + intSeed + " = " + seedCellLua),
            "the LuaJIT typed load reads the seed cell (identity preservation)");
        check(jvm.contains(seedCellJvm
                + " = JvmRuntime.intrinsic(\"INT_CONVERT\", \"function(number;int)\", "
                + "\"(number)->int\")"),
            "the JVM seed BINDING_INIT publishes the memoized declared-signature "
                + "carrier: " + seedCellJvm);
        check(!jvm.contains(seedCellJvm + " = v" + intSeed),
            "the JVM seed BINDING_INIT is never a slot read of the seeded identity");
        check(!jvm.contains("new JvmRuntime.Intrinsic()"),
            "the JVM artifact carries no marker placeholder");
        check(jvm.contains("v" + intSeed + " = " + seedCellJvm + ";"),
            "the JVM typed load reads the seed cell (identity preservation)");

        // The alias declarations publish the identical memoized carrier (the
        // same object the seed and the load carry), so every materialization
        // of one intrinsic is one object.
        check(lua.split(java.util.regex.Pattern.quote(
                "__intrinsicFn(\"INT_CONVERT\", \"function(number;int)\", "
                    + "\"(number)->int\")"), -1).length - 1 >= 3,
            "every LuaJIT materialization of the int intrinsic publishes the "
                + "memoized carrier");
        check(jvm.split(java.util.regex.Pattern.quote(
                "JvmRuntime.intrinsic(\"INT_CONVERT\", \"function(number;int)\", "
                    + "\"(number)->int\")"), -1).length - 1 >= 3,
            "every JVM materialization of the int intrinsic publishes the memoized "
                + "carrier");

        // The value-position program's identity comparison ops (the drives).
        int comparisons = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINARY
                    && op.payload() instanceof KindPayload.BinaryPayload binary
                    && binary.selector() == deal.semantic.ir.BinarySelector.REFERENCE_EQ) {
                comparisons++;
            }
        }
        checkEq(2, comparisons, "the program carries the two reference comparisons");
    }

    /**
     * The combined value-position + adapted-declaration drive (J6 item 4):
     * the unit that carries the seed write, the identity-preserving load of
     * the seeded binding and the adapted declaration over the same seeded
     * identity still passes {@code ADAPTER_SOURCE_SHAPE} under the
     * VALUE-over-intrinsic exemption — the declaration's re-publication of
     * the seed write is not a second seed write — and the seed-write
     * predicate stays closed: a proof over the seeded operand naming
     * another intrinsic's seed binding refuses the exemption, and another
     * producing op over the seeded identity still fails the seed clause.
     * The landed mis-named-load negative (a unit carrying no
     * identity-preserving load of the seeded cell) is pinned by
     * {@code DynamicFunctionValueGateTest.testAdapterValueOverIntrinsicExemption}.
     */
    private static void testCombinedValueAndAdapterAdmission() {
        System.out.println("-- J6.4: the combined value-position + adapted-declaration "
            + "unit, and the closed seed-write predicate --");
        Fixture fixture = fixture(COMBINED_SOURCE, "combined value and adapter");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "combined value and adapter");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();

        long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
        check(seed > 0, "the combined unit carries the int seed registration");
        if (seed < 0) {
            return;
        }
        int intrinsicRegistrations = 0;
        int dynamicRegistrations = 0;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.IntrinsicFunction) {
                intrinsicRegistrations++;
            }
            if (binding instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                dynamicRegistrations++;
            }
        }
        checkEq(2, intrinsicRegistrations,
            "the combined unit carries exactly the two seed IntrinsicFunction "
                + "registrations (one per conversion intrinsic)");
        checkEq(0, dynamicRegistrations,
            "no DynamicFunctionValue is registered for the intrinsic load");

        // The trigger of the refined predicate: the seeded identity carries
        // two BINDING_INITs (the seed write and the value-position
        // declaration's re-publication) while exactly one of them lands on
        // the seeded cell the identity-preserving load reads.
        SemanticOp seedInit = seedInit(unit, seed);
        check(seedInit != null, "the combined unit carries the seed BINDING_INIT");
        if (seedInit == null) {
            return;
        }
        KindPayload.BindingInitPayload seedWrite =
            (KindPayload.BindingInitPayload) seedInit.payload();
        int initsOverSeed = 0;
        int initOnSeedCell = 0;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() == seed) {
                initsOverSeed++;
                if (init.binding().equals(seedWrite.binding())
                        && init.generation() == seedWrite.generation()) {
                    initOnSeedCell++;
                }
            }
        }
        checkEq(2, initsOverSeed, "the value-position declaration re-publishes the "
            + "seed write (the combined unit carries the seed BINDING_INIT plus the "
            + "declaration's BINDING_INIT over the seeded identity)");
        checkEq(1, initOnSeedCell, "exactly one of those writes lands on the seeded "
            + "cell the identity-preserving load reads (the seed write)");
        boolean seedCellLoad = false;
        for (SemanticOp producer : producersOf(unit, seed)) {
            check(producer.kind() == SemanticOpKind.BINDING_LOAD,
                "the only producer of the seeded identity is an identity-preserving "
                    + "load (got " + producer.kind() + " at " + producer.opId() + ")");
            KindPayload.BindingLoadPayload load =
                (KindPayload.BindingLoadPayload) producer.payload();
            if (load.binding().equals(seedWrite.binding())
                    && load.generation() == seedWrite.generation()) {
                seedCellLoad = true;
            }
        }
        check(seedCellLoad, "the value-position binding's typed load reads the seed "
            + "BINDING_INIT's own cell");

        // The adapted declaration's producer-less VALUE operand is the
        // seeded identity itself, with no proof (the B7/B8 creation shape).
        SemanticOp adaptOp = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adaptOp = op;
            }
        }
        check(adaptOp != null, "the combined unit produces its FUNCTION_ADAPT");
        if (adaptOp == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload adapt =
            (KindPayload.FunctionAdaptPayload) adaptOp.payload();
        check(adapt.source() instanceof deal.semantic.ir.AdaptSourceRef.Value value
                && value.value().id() == seed && adapt.proof() == null,
            "the adapter's operand is the seeded identity itself with no proof");

        // The combined unit passes both closed gates: REGISTRY_ONE_TO_ONE
        // (the seed write is counted on the seeded cell) and
        // ADAPTER_SOURCE_SHAPE (the VALUE-over-intrinsic exemption).
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), "the combined unit passes the closed bindings gate "
            + "(REGISTRY_ONE_TO_ONE and ADAPTER_SOURCE_SHAPE): "
            + bindings.map(CompilerDiagnostic::message).orElse("admission"));
        Optional<CompilerDiagnostic> schema =
            SemanticIrValidator.validate(unit, facts(unit));
        check(schema.isEmpty(), "the combined unit passes the closed schema gate: "
            + schema.map(CompilerDiagnostic::message).orElse("admission"));

        // Both targets publish the memoized carrier at the adapter's
        // producer-less VALUE operand (never a slot read of the seeded
        // identity, which the value-position load fills).
        String lua = LuaSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())));
        String jvm = JvmSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of()))).source();
        check(lua.contains("__value = __intrinsicFn(\"INT_CONVERT\", "
                + "\"function(number;int)\", \"(number)->int\")"),
            "the LuaJIT combined artifact's adapter VALUE operand publishes the "
                + "memoized carrier");
        check(!lua.contains("__value = S.v" + seed),
            "the LuaJIT combined artifact's adapter VALUE operand is never a slot "
                + "read of the seeded identity");
        check(jvm.contains("JvmRuntime.intrinsic(\"INT_CONVERT\", "
                + "\"function(number;int)\", \"(number)->int\"), null, null"),
            "the JVM combined artifact's adapter VALUE operand publishes the "
                + "memoized carrier");
        check(!jvm.contains("v" + seed + ", null, null"),
            "the JVM combined artifact's adapter VALUE operand is never a slot read "
                + "of the seeded identity");

        // The exemption's proof arm stays closed: a proof recorded over the
        // seeded intrinsic operand must name the seeded binding/generation.
        CellRef seedCell = seedCellOf(unit, seed);
        check(seedCell != null && seedCell.binding().equals(seedWrite.binding())
                && seedCell.generation() == seedWrite.generation(),
            "the seed write is the first BINDING_INIT over the seeded identity");
        long otherSeed = seedIdentity(unit, IntrinsicKind.NUMBER_CONVERT);
        CellRef otherSeedCell = otherSeed > 0 ? seedCellOf(unit, otherSeed) : null;
        check(otherSeedCell != null,
            "the combined unit carries the other intrinsic seed binding");
        if (seedCell == null || otherSeedCell == null) {
            return;
        }
        SemanticOp misProved = adaptWithProof(adaptOp, adapt,
            new BindingImmutabilityProof(otherSeedCell.binding(),
                otherSeedCell.generation()));
        LoweredModuleUnit misProvedUnit = replaceOp(unit, adaptOp, misProved);
        Optional<CompilerDiagnostic> misProvedFailure = BindingsProductionValidator
            .validate(misProvedUnit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(misProvedFailure.isPresent()
                && "E6005".equals(misProvedFailure.get().code())
                && misProvedFailure.get().message().contains("ADAPTER_SOURCE_SHAPE"),
            "a proof over the seeded intrinsic operand naming another intrinsic's "
                + "seed binding fails the exemption's proof arm: "
                + misProvedFailure.map(CompilerDiagnostic::message).orElse("admission"));

        // The seed clause is load-bearing for the combined unit: another op
        // producing the seeded identity still fails REGISTRY_ONE_TO_ONE.
        LoweredModuleUnit doctored = withOp(unit, exportReadOf(seed, unit));
        Optional<CompilerDiagnostic> doctoredFailure = BindingsProductionValidator
            .validate(doctored, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(doctoredFailure.isPresent()
                && "E6005".equals(doctoredFailure.get().code())
                && doctoredFailure.get().message().contains("REGISTRY_ONE_TO_ONE"),
            "the combined unit whose seeded identity is also produced by an "
                + "EXPORT_READ still fails the seed clause: "
                + doctoredFailure.map(CompilerDiagnostic::message).orElse("admission"));
    }

    /** True iff one BINDING_INIT of the cell carries the given identity. */
    private static boolean cellInitCarries(LoweredModuleUnit unit, BindingId binding,
                                           long generation, long identity) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.binding().equals(binding)
                    && init.generation() == generation
                    && init.value().id() == identity) {
                return true;
            }
        }
        return false;
    }

    /**
     * A cell whose {@code BINDING_INIT} carries a function-typed identity
     * other than the seed (the foreign-load target: the load naming it is a
     * producing position under the merged per-op rule).
     */
    private static CellRef foreignFunctionCell(LoweredModuleUnit unit, long seed) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() != seed) {
                for (SemanticOp producer : producersOf(unit, init.value().id())) {
                    if (producer.resultType() instanceof RuntimeDescriptor.Func) {
                        return new CellRef(init.binding(), init.generation());
                    }
                }
            }
        }
        return null;
    }

    /** The unit's table with one extra op placed in the given block. */
    private static StructuredBodyTable withTableOp(StructuredBodyTable table, SemanticOp op,
                                                   BlockId block) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
            blockOps.put(entry.getKey(), new ArrayList<>(entry.getValue()));
        }
        blockOps.computeIfAbsent(block, key -> new ArrayList<>()).add(op.opId());
        Map<OpId, BlockId> inverse = new LinkedHashMap<>(table.opBlocks());
        inverse.put(op.opId(), block);
        return new StructuredBodyTable(blockOps, inverse);
    }

    /**
     * A doctored {@code BINDING_LOAD} publishing the seeded identity from a
     * foreign cell (the merged rule's closed-direction negative).
     */
    private static SemanticOp foreignLoadOf(CellRef cell, long identity,
                                            LoweredModuleUnit unit) {
        SemanticOp template = unit.ops().get(0);
        OpId opId = new OpId(MODULE, nextOpIdOf(unit));
        RuntimeDescriptor.Func descriptor = IntrinsicKind.INT_CONVERT.declaredSignature();
        KindPayload.BindingLoadPayload payload = new KindPayload.BindingLoadPayload(
            cell.binding(), cell.generation());
        return new SemanticOp(opId, SemanticOpKind.BINDING_LOAD, template.origin(),
            new ValueId(identity), descriptor, List.of(), List.of(), payload,
            FailurePolicyId.NO_DEAL_FAILURE,
            contractFor(SemanticOpKind.BINDING_LOAD, payload, descriptor, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE));
    }

    /** A doctored EXPORT_READ op publishing the seeded identity (the T2 negative). */
    private static SemanticOp exportReadOf(long identity, LoweredModuleUnit unit) {
        SemanticOp template = unit.ops().get(0);
        OpId opId = new OpId(MODULE, nextOpIdOf(unit));
        RuntimeDescriptor.Func descriptor = IntrinsicKind.INT_CONVERT.declaredSignature();
        KindPayload.ExportReadPayload payload = new KindPayload.ExportReadPayload(MODULE,
            "f", descriptor, new ValueId(identity));
        return new SemanticOp(opId, SemanticOpKind.EXPORT_READ, template.origin(),
            new ValueId(identity), descriptor, List.of(), List.of(), payload,
            FailurePolicyId.NO_DEAL_FAILURE,
            contractFor(SemanticOpKind.EXPORT_READ, payload, descriptor, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE));
    }

    /** The contract snapshot of one doctored op (the digest recomputed). */
    private static OperationContractSnapshot contractFor(SemanticOpKind kind,
            KindPayload payload, OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        OperationContractSnapshot draft = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, operandTypes, selector,
            payload, policy, List.of(), "placeholder");
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(),
            ContractSnapshotCanonicalizer.digest(draft));
    }

    private static long nextOpIdOf(LoweredModuleUnit unit) {
        long max = 0;
        for (SemanticOp op : unit.ops()) {
            max = Math.max(max, op.opId().id());
        }
        return max + 1;
    }

    /**
     * The seed write's cell: the first {@code BINDING_INIT} over the seeded
     * identity.
     */
    private static CellRef seedCellOf(LoweredModuleUnit unit, long seed) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINDING_INIT
                    && op.payload() instanceof KindPayload.BindingInitPayload init
                    && init.value().id() == seed) {
                return new CellRef(init.binding(), init.generation());
            }
        }
        return null;
    }

    /** The adapter op with its recorded proof replaced (the doctor). */
    private static SemanticOp adaptWithProof(SemanticOp adaptOp,
            KindPayload.FunctionAdaptPayload adapt, BindingImmutabilityProof proof) {
        KindPayload.FunctionAdaptPayload replaced = new KindPayload.FunctionAdaptPayload(
            adapt.sourceSignature(), adapt.targetSignature(), adapt.mode(), adapt.source(),
            proof);
        return rebuild(adaptOp, replaced, adaptOp.resultType());
    }

    /** One op rebuilt over a new payload (the contract digest recomputed). */
    private static SemanticOp rebuild(SemanticOp op, KindPayload payload,
            OpResultType resultType) {
        OperationContractSnapshot contract = contractFor(op.kind(), payload, resultType,
            op.operandTypes(), op.failurePolicy());
        return new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(), resultType,
            op.operands(), op.operandTypes(), payload, op.failurePolicy(), contract);
    }

    /** The unit with one op replaced in place (the doctor). */
    private static LoweredModuleUnit replaceOp(LoweredModuleUnit unit, SemanticOp target,
            SemanticOp replacement) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op == target ? replacement : op);
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    /** The unit with one extra op appended (the doctor). */
    private static LoweredModuleUnit withOp(LoweredModuleUnit unit, SemanticOp extra) {
        List<SemanticOp> ops = new ArrayList<>(unit.ops());
        ops.add(extra);
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    // =========================================================================
    // 2. The carrier sites (J2)
    // =========================================================================

    private static void testCarrierSites() {
        System.out.println("-- J2: the memoized carrier at the adapter's "
            + "producer-less VALUE operand and at the residual export-read kind arm --");

        // The adapted declaration's producer-less VALUE operand.
        Fixture fixture = fixture(ADAPTER_SOURCE, "adapter operand");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "adapter operand");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
        check(seed > 0, "the adapter unit carries the int seed registration");
        if (seed < 0) {
            return;
        }
        SemanticOp adaptOp = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adaptOp = op;
            }
        }
        check(adaptOp != null, "the adapted declaration produces its FUNCTION_ADAPT");
        if (adaptOp == null) {
            return;
        }
        KindPayload.FunctionAdaptPayload adapt =
            (KindPayload.FunctionAdaptPayload) adaptOp.payload();
        check(adapt.source() instanceof deal.semantic.ir.AdaptSourceRef.Value value
                && value.value().id() == seed && adapt.proof() == null,
            "the adapter's operand is the seeded identity itself with no proof");
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(
            unit, raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), "the adapter unit passes the closed bindings gate "
            + "(the VALUE-over-intrinsic exemption): "
            + bindings.map(CompilerDiagnostic::message).orElse("admission"));

        String lua = LuaSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()), Map.of(MODULE, new ClassFactoryRegistry(Map.of())));
        String jvm = JvmSemanticEmitter.emitProject(projectOf(unit),
            Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of()))).source();
        check(lua.contains("__value = __intrinsicFn(\"INT_CONVERT\", "
                + "\"function(number;int)\", \"(number)->int\")"),
            "the LuaJIT adapter's producer-less VALUE operand publishes the memoized "
                + "carrier");
        check(!lua.contains("__value = S.v" + seed),
            "the LuaJIT adapter's VALUE operand is never a slot read of the seeded "
                + "identity");
        check(jvm.contains("JvmRuntime.intrinsic(\"INT_CONVERT\", \"function(number;int)\", "
                + "\"(number)->int\"), null, null"),
            "the JVM adapter's producer-less VALUE operand publishes the memoized "
                + "carrier");
        check(!jvm.contains("hasProducer") && !jvm.contains("v" + seed + ", null, null"),
            "the JVM adapter's VALUE operand is never a slot read of the seeded "
                + "identity");

        // The residual export-read kind arm (a session whose unit records no
        // import fact for the read's module) publishes a real, fresh
        // per-read carrier for an identity that resolves no intrinsic
        // registration (the landed per-read allocation), and the memoized
        // intrinsic carrier when the identity's own registration resolves
        // one.
        LoweredModuleUnit residualUnit = withOp(unit, residualReadOf(unit, seed));
        StructuredBodyTable residualTable = withBlockOp(raw.table(),
            unit.moduleInit().initBlock(), residualUnit.ops()
                .get(residualUnit.ops().size() - 1));
        String residualLua = LuaSemanticEmitter.emitModule(residualUnit, residualTable);
        String residualJvm = JvmSemanticEmitter.emitModule(residualUnit, residualTable)
            .source();
        check(residualLua.contains("= __intrinsicExport()"),
            "the LuaJIT residual export-read kind arm publishes a real carrier "
                + "surface");
        check(!residualLua.contains("__f = true"),
            "the LuaJIT residual arm carries no marker placeholder");
        check(residualJvm.contains("= JvmRuntime.intrinsicExport()"),
            "the JVM residual export-read kind arm publishes a real carrier "
                + "surface");
        check(!residualJvm.contains("new JvmRuntime.Intrinsic()"),
            "the JVM residual arm carries no marker placeholder");

        // The residual arm publishes the memoized intrinsic carrier when the
        // read's identity is a registered seeded identity (the kind's only
        // authority).
        LoweredModuleUnit seededReadUnit = withOp(unit, residualReadOf(unit, seed,
            new ValueId(seed)));
        StructuredBodyTable seededReadTable = withBlockOp(raw.table(),
            unit.moduleInit().initBlock(),
            seededReadUnit.ops().get(seededReadUnit.ops().size() - 1));
        check(LuaSemanticEmitter.emitModule(seededReadUnit, seededReadTable)
                .contains("= __intrinsicFn(\"INT_CONVERT\""),
            "the LuaJIT residual arm publishes the memoized carrier of a registered "
                + "seeded identity");
        check(JvmSemanticEmitter.emitModule(seededReadUnit, seededReadTable).source()
                .contains("= JvmRuntime.intrinsic(\"INT_CONVERT\""),
            "the JVM residual arm publishes the memoized carrier of a registered "
                + "seeded identity");
    }

    /** The table with one extra member appended to the given block. */
    private static StructuredBodyTable withBlockOp(StructuredBodyTable table, BlockId block,
            SemanticOp extra) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        for (Map.Entry<BlockId, List<OpId>> entry : table.blockOps().entrySet()) {
            List<OpId> members = new ArrayList<>(entry.getValue());
            if (entry.getKey().equals(block)) {
                members.add(extra.opId());
            }
            blockOps.put(entry.getKey(), members);
        }
        Map<OpId, BlockId> opBlocks = new LinkedHashMap<>(table.opBlocks());
        opBlocks.put(extra.opId(), block);
        return new StructuredBodyTable(blockOps, opBlocks);
    }

    /** A doctored EXPORT_READ of a module the session records no import fact for. */
    private static SemanticOp residualReadOf(LoweredModuleUnit unit, long identity) {
        return residualReadOf(unit, identity, new ValueId(identity + 100000));
    }

    /** The same residual read with the given published value identity. */
    private static SemanticOp residualReadOf(LoweredModuleUnit unit, long seed,
            ValueId result) {
        SemanticOp template = unit.ops().get(0);
        OpId opId = new OpId(MODULE, nextOpIdOf(unit));
        RuntimeDescriptor.Func descriptor = IntrinsicKind.INT_CONVERT.declaredSignature();
        KindPayload.ExportReadPayload payload = new KindPayload.ExportReadPayload(
            new ModuleId("std.console"), "log", descriptor, result);
        return new SemanticOp(opId, SemanticOpKind.EXPORT_READ, template.origin(),
            result, descriptor, List.of(), List.of(), payload,
            FailurePolicyId.NO_DEAL_FAILURE,
            contractFor(SemanticOpKind.EXPORT_READ, payload, descriptor, List.of(),
                FailurePolicyId.NO_DEAL_FAILURE));
    }

    // =========================================================================
    // 3. The oracle and the artifacts (J2)
    // =========================================================================

    private static void testConsumerDrives() throws Exception {
        System.out.println("-- J2: the oracle's keyed value and declared-signature "
            + "views, and the emitted artifacts' identity preservation --");
        Fixture fixture = fixture(VALUE_POSITION_SOURCE, "consumer drives");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "consumer drives");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        ExecutableLoweredProject project = projectOf(unit);
        Map<ModuleId, ClassFactoryRegistry> registries =
            Map.of(MODULE, new ClassFactoryRegistry(Map.of()));

        // The oracle: the declaration boundaries pass (the seeded value's
        // views carry the declared signature) and the identity comparisons
        // observe one object.
        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
            project, Map.of(MODULE, raw.table()), registries, null);
        check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the oracle run succeeds (the intrinsic declaration boundaries admit the "
                + "carrier with its declared signature): " + oracle.terminal());
        int comparisons = 0;
        for (SemanticRuntimeModel.TraceEvent event : oracle.trace()) {
            if (event.op().equals(comparisonOps(unit).get(0))
                    && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                comparisons++;
                checkEq("bool:true", event.output(),
                    "the oracle's identity comparison observes one object (the memoized "
                        + "carrier the seed published)");
            }
        }
        checkEq(1, comparisons, "the oracle runs the first identity comparison exactly "
            + "once");

        // The artifacts (trace mode, real toolchains): the same identity
        // comparison observes the identical object.
        Path luaWorkspace = Files.createTempDirectory("intrinsic-carrier-lua");
        Path jvmWorkspace = Files.createTempDirectory("intrinsic-carrier-jvm");
        try {
            ArtifactRun lua = runLuaTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), luaWorkspace);
            checkEq(0, lua.exitCode(), "the shared LuaJIT artifact executes: "
                + lua.protocol());
            assertComparisonTrue("shared-luajit", lua.protocol(), unit);
            ArtifactRun jvm = runJvmTrace(project, raw.table(),
                new ClassFactoryRegistry(Map.of()), jvmWorkspace);
            checkEq(0, jvm.exitCode(), "the shared JVM artifact executes: "
                + jvm.protocol());
            assertComparisonTrue("shared-jvm", jvm.protocol(), unit);
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
        }
    }

    /** The two reference-comparison ops of the value-position program, in op order. */
    private static List<OpId> comparisonOps(LoweredModuleUnit unit) {
        List<OpId> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BINARY
                    && op.payload() instanceof KindPayload.BinaryPayload binary
                    && binary.selector() == deal.semantic.ir.BinarySelector.REFERENCE_EQ) {
                ops.add(op.opId());
            }
        }
        return ops;
    }

    private static void assertComparisonTrue(String consumer, List<String> protocol,
                                             LoweredModuleUnit unit) {
        List<OpId> comparisons = comparisonOps(unit);
        checkEq(2, comparisons.size(), consumer + ": the unit carries two comparisons");
        for (OpId op : comparisons) {
            List<String> success = linesOf(protocol,
                MODULE.path() + "#" + op.id(), "SUCCESS");
            checkEq(1, success.size(), consumer + ": exactly one SUCCESS terminal for "
                + op);
            check(!success.isEmpty() && success.get(0).contains("=>bool:true"),
                consumer + ": the identical memoized carrier compares equal: " + success);
        }
    }

    private static void testCarriedSignatureIsDeclared() throws Exception {
        System.out.println("-- J2: the carried signature is the intrinsic's declared one "
            + "(a differing declared crossing projects E8010 over the intrinsic's own "
            + "signature text) --");
        Fixture fixture = fixture(VALUE_POSITION_SOURCE, "carried signature");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "carried signature");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        long seed = seedIdentity(unit, IntrinsicKind.INT_CONVERT);
        SourceSpan annotation = annotationSpan(fixture.module().ast(), "f");
        if (seed < 0 || annotation == null) {
            return;
        }
        String origin = SOURCE_ID + ":" + annotation.startLine() + ":"
            + annotation.startColumn();

        // The declaration boundary over the seeded identity (the annotated
        // `let f` crossing).
        SemanticOp boundary = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && op.payload() instanceof KindPayload.BoundaryPayload payload
                    && payload.kind() == BoundaryKind.VARIABLE_DECLARATION
                    && payload.input().id() == seed) {
                boundary = op;
                break;
            }
        }
        check(boundary != null, "the unit carries the declaration boundary over the "
            + "seeded identity");
        if (boundary == null) {
            return;
        }
        check(origin.equals(originText(boundary)),
            "the declaration boundary's origin is the declared annotation's span: "
                + originText(boundary));

        // The doctored crossing: the identical carried value against a
        // differing declared signature. The intrinsic's declared signature is
        // the actual side of the row — the carrier never carries a call site's
        // or an adapter target's signature.
        RuntimeDescriptor.Func mismatched = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Int.INSTANCE);
        LoweredModuleUnit doctored = withBoundaryDescriptor(unit, boundary, mismatched);
        Optional<CompilerDiagnostic> gate = SemanticIrValidator.validate(doctored,
            facts(doctored));
        check(gate.isEmpty(), "the closed schema gate accepts the doctored declaration "
            + "crossing: " + gate.map(CompilerDiagnostic::message).orElse("admission"));
        SemanticRuntimeModel.ConsumerRun oracle = SemanticOracle.executeProjectInits(
            projectOf(doctored), Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                && "E8010".equals(failure.error().code())
                && origin.equals(failure.error().origin())
                && "(int)->int".equals(failure.error().expected())
                && "(number)->int".equals(failure.error().actual()),
            "the oracle projects E8010 at the annotation span with the intrinsic's "
                + "declared signature as the actual text: " + oracle.terminal());

        String lua = luaProductionFailure(projectOf(doctored), raw.table(),
            new ClassFactoryRegistry(Map.of()), "carried signature");
        check(lua.startsWith("ERR:E8010|function signature mismatch:")
                && lua.contains("|" + origin + "|")
                && lua.contains("function(number;int)"),
            "the LuaJIT artifact projects E8010 at the annotation span over the "
                + "intrinsic's declared carrier signature: " + lua);
        String jvm = jvmProductionFailure(projectOf(doctored), raw.table(),
            new ClassFactoryRegistry(Map.of()), "carried signature");
        check(jvm.startsWith("ERR:E8010|function signature mismatch:")
                && jvm.contains("|" + origin + "|")
                && jvm.contains("function(number;int)"),
            "the JVM artifact projects E8010 at the annotation span over the intrinsic's "
                + "declared carrier signature: " + jvm);
    }

    /** The unit with one boundary op's descriptor replaced (the doctor). */
    private static LoweredModuleUnit withBoundaryDescriptor(LoweredModuleUnit unit,
            SemanticOp boundary, RuntimeDescriptor.Func descriptor) {
        KindPayload.BoundaryPayload payload =
            (KindPayload.BoundaryPayload) boundary.payload();
        KindPayload.BoundaryPayload replaced = new KindPayload.BoundaryPayload(
            payload.kind(), descriptor, payload.input(), payload.realization());
        SemanticOp replacement = new SemanticOp(boundary.opId(), SemanticOpKind.BOUNDARY,
            boundary.origin(), boundary.result(), boundary.resultType(), List.of(),
            List.of(), replaced, boundary.failurePolicy(),
            contractFor(SemanticOpKind.BOUNDARY, replaced, boundary.resultType(), List.of(),
                boundary.failurePolicy()));
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(op.opId().equals(boundary.opId()) ? replacement : op);
        }
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(),
            unit.functionBindings(), ops);
    }

    // =========================================================================
    // The trace-mode and production-artifact runners
    // =========================================================================

    private record ArtifactRun(int exitCode, List<String> stdout,
                               List<String> protocol) {
    }

    private static ArtifactRun runLuaTrace(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            Path workspace) throws Exception {
        Files.createDirectories(workspace);
        Path script = workspace.resolve("project.lua");
        Files.writeString(script,
            LuaSemanticEmitter.emitProject(project, Map.of(MODULE, table),
                Map.of(MODULE, registry)),
            StandardCharsets.UTF_8);
        Path stdout = workspace.resolve("lua-out.txt");
        Path stderr = workspace.resolve("lua-err.txt");
        ProcessBuilder builder = new ProcessBuilder("luajit",
            script.toAbsolutePath().toString());
        builder.redirectOutput(stdout.toFile());
        builder.redirectError(stderr.toFile());
        Process process = builder.start();
        int exit = process.waitFor();
        return new ArtifactRun(exit, Files.readAllLines(stdout, StandardCharsets.UTF_8),
            Files.readAllLines(stderr, StandardCharsets.UTF_8));
    }

    private static ArtifactRun runJvmTrace(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry,
            Path workspace) throws Exception {
        Files.createDirectories(workspace);
        JvmSemanticEmitter.EmissionResult emission =
            JvmSemanticEmitter.emitProject(project, Map.of(MODULE, table),
                Map.of(MODULE, registry));
        Path source = workspace.resolve(emission.className() + ".java");
        Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
        Path classes = workspace.resolve("classes");
        Files.createDirectories(classes);
        String classpath = absoluteClasspath();
        ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
            "-proc:none", "-cp", classpath, "-d", classes.toString(),
            source.toAbsolutePath().toString());
        javac.redirectErrorStream(true);
        Process compile = javac.start();
        String compileOut = new String(compile.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int compileExit = compile.waitFor();
        if (compileExit != 0) {
            check(false, "the JVM trace artifact compiles: " + compileOut);
            return new ArtifactRun(compileExit, List.of(), List.of());
        }
        Path stdout = workspace.resolve("jvm-out.txt");
        Path stderr = workspace.resolve("jvm-err.txt");
        ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
            classpath + File.pathSeparator + classes, emission.className());
        javaRun.redirectOutput(stdout.toFile());
        javaRun.redirectError(stderr.toFile());
        Process run = javaRun.start();
        int exit = run.waitFor();
        return new ArtifactRun(exit, Files.readAllLines(stdout, StandardCharsets.UTF_8),
            Files.readAllLines(stderr, StandardCharsets.UTF_8));
    }

    private static List<String> linesOf(List<String> protocol, String opKey,
                                        String phase) {
        List<String> found = new ArrayList<>();
        for (String line : protocol) {
            if (line.contains("|" + opKey + "|" + phase + "|")) {
                found.add(line);
            }
        }
        return found;
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static void deployRuntime(Path workspace) throws Exception {
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(Path.of("deal", "runtime.lua"), runtimeTarget);
        Path stdTarget = workspace.resolve("std");
        Files.createDirectories(stdTarget);
        try (var listing = Files.list(Path.of("std"))) {
            for (Path file : listing.sorted().toList()) {
                if (file.getFileName().toString().endsWith(".lua")) {
                    Files.copy(file, stdTarget.resolve(file.getFileName()));
                }
            }
        }
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(java.util.Comparator.reverseOrder()).forEach(entry -> {
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

    private static String luaProductionFailure(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry, String what)
            throws Exception {
        Path workspace = Files.createTempDirectory("intrinsic-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, Map.of(MODULE, table), Map.of(MODULE, registry),
                new HostDeclarationSurface(Map.of())), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                local chunk = dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                      .. tostring(err.o) .. "|" .. tostring(err.e) .. "|"
                      .. tostring(err.a))
                  else
                    print("ERR:" .. tostring(err))
                  end
                  os.exit(0)
                end
                print("OK")
                """.formatted(artifact.toAbsolutePath().toString()),
                StandardCharsets.UTF_8);
            ProcessBuilder builder = new ProcessBuilder("luajit",
                probe.toAbsolutePath().toString());
            builder.directory(workspace.toFile());
            builder.environment().put("DEAL_DEFER_MAIN", "1");
            Path stderrFile = Files.createTempFile(workspace, "stderr", ".txt");
            builder.redirectError(stderrFile.toFile());
            Process process = builder.start();
            String stdout = new String(process.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int exit = process.waitFor();
            String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
            checkEq(0, exit, what + " (luajit): the production chunk executes: "
                + stdout + stderr);
            return stdout.strip();
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static String jvmProductionFailure(ExecutableLoweredProject project,
            StructuredBodyTable table, ClassFactoryRegistry registry, String what)
            throws Exception {
        Path workspace = Files.createTempDirectory("intrinsic-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project,
                    Map.of(MODULE, table), Map.of(MODULE, registry), className,
                    new HostDeclarationSurface(Map.of()));
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("IntrinsicProbe.java"), """
                final class IntrinsicProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin + "|" + error.expected + "|" + error.actual);
                      return;
                    }
                    System.out.println("OK");
                  }
                }
                """.formatted(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessBuilder javac = new ProcessBuilder("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "IntrinsicProbe.java");
            javac.directory(workspace.toFile());
            javac.redirectErrorStream(true);
            Process compile = javac.start();
            String compileOut = new String(compile.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int compileExit = compile.waitFor();
            checkEq(0, compileExit, what + ": the JVM production artifact compiles: "
                + compileOut);
            if (compileExit != 0) {
                return "";
            }
            ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                classpath + File.pathSeparator + classes, "IntrinsicProbe");
            javaRun.directory(workspace.toFile());
            Process run = javaRun.start();
            String stdout = new String(run.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8);
            int exit = run.waitFor();
            checkEq(0, exit, what + " (java): the production artifact executes: "
                + stdout);
            return stdout.strip();
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // The declared type annotation's span (read from the checked AST)
    // =========================================================================

    private static SourceSpan annotationSpan(ProgramNode program, String bindingName) {
        for (StatementNode statement : program.statements()) {
            if (statement instanceof VariableDeclaration decl
                    && decl.name().equals(bindingName)
                    && decl.typeAnnotation().isPresent()) {
                return toSourceSpan(decl.typeAnnotation().get().span());
            }
        }
        check(false, "the checked AST carries the annotated declaration '"
            + bindingName + "'");
        return null;
    }

    private static SourceSpan toSourceSpan(Span span) {
        return new SourceSpan(span.file(), span.startLine(), span.startColumn(),
            span.endLine(), span.endColumn(), span.startScalarOffset(),
            span.endScalarOffset());
    }

    /** The origin text of one op ({@code source:line:column}). */
    private static String originText(SemanticOp op) {
        SourceSpan span = op.origin().span();
        if (span == null) {
            return "-";
        }
        return op.origin().sourceId() + ":" + span.startLine() + ":"
            + span.startColumn();
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        testSeededIdentityPreservation();
        testCarrierSites();
        testCombinedValueAndAdapterAdmission();
        testConsumerDrives();
        testCarriedSignatureIsDeclared();
        System.out.println();
        System.out.println("Intrinsic value materialization (ISSUE-0676): "
            + passed + " passed, " + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
