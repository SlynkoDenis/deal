package deal.semantic;

import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.BuiltinErrorDeclaration;
import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.ModuleResolver.ModuleNotFoundException;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.codegen.Backend;
import deal.module.CompilationOrchestrator;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0675 — the closed producer rule's lowering arms (wiki
 * {@code function-typed-value-materialization-and-dispatch} M2 items 1-3
 * and 5; wiki {@code semantic-ir-construct-coverage-cutover} K11/K12).
 *
 * <p>Every function-typed result registers exactly one
 * {@code FunctionExecutionBinding}: the static class where the class is
 * known and {@code DynamicFunctionValue} where it is not. This suite drives
 * the dynamic arms over the real production walk and asserts, per arm, that
 * exactly one {@code DynamicFunctionValue} is keyed by the arm's producing
 * op result identity, correlated to that op, and carrying that op's result
 * descriptor — and that the produced unit passes the schema rules (typed
 * and canonical text surfaces) and the bindings production rules in one
 * pass, so a broken gate clause fails the drive.</p>
 *
 * <ol>
 *   <li><b>The typed-load arm.</b> A value-position function-typed
 *       {@code BINDING_LOAD} whose cell value identity is not statically
 *       tracked (a parameter, a catch binding, an iteration binding, and a
 *       class-field or namespace-held value) registers exactly one dynamic
 *       record keyed by the load's result identity with the load's checked
 *       descriptor; the alias load of the resulting tracked cell republishes
 *       that identity and never registers again.</li>
 *   <li><b>The read arms.</b> A {@code MEMBER_READ}, an {@code INDEX_READ},
 *       and a {@code FIELD_READ} with a function-typed result register
 *       exactly one dynamic record each, keyed by the read's result
 *       identity; a module-namespace member read flows through the same
 *       member-read arm (the table-held namespace value's function-typed
 *       entry). The optional-read envelope publishes a nullable
 *       descriptor — not a function-typed result — so no record is keyed by
 *       it; the narrowed value-position load of the guarded cell registers
 *       the record the call dispatches on.</li>
 *   <li><b>The call arm.</b> A {@code CALL} result with a function-typed
 *       result registers exactly one dynamic record, whatever call arm
 *       allocated it (a direct call, a dynamically resolved call, an
 *       imported call, and the callee value of a call-of-call).</li>
 *   <li><b>The awaited-completion arm.</b> The {@code AWAIT} op — the op
 *       that allocates and publishes the completion value identity — with a
 *       function-typed completion registers exactly one dynamic record; the
 *       {@code ASYNC_START} result is the token under
 *       {@code INTERNAL_ASYNC} and registers nothing.</li>
 *   <li><b>Preserved static classes.</b> A tracked alias load and an
 *       imported function-typed export read (host/STDLIB
 *       {@code HostFunction}, compiled {@code ExternalFunction
 *       (SHARED_BODY)}) keep their landed static registration: no dynamic
 *       re-registration, no duplicate key.</li>
 *   <li><b>Negative seeds.</b> A dropped dynamic registration fails
 *       R-FUNCTION-BINDING; a dynamic registration keyed by a static
 *       position (a closure production) fails REGISTRY_ONE_TO_ONE; a
 *       duplicate key is rejected at the registry.</li>
 * </ol>
 *
 * <p><b>Boundary.</b> The seeded conversion intrinsic's
 * identity-preserving tracking (a function-typed load of the intrinsic
 * binding republishes the seeded identity) and the gate refinements its
 * alias declarations require are the conversion-intrinsic child's (wiki
 * {@code conversion-intrinsic-function-values} J1). Until that tracking
 * lands, the intrinsic binding's cell value identity is not statically
 * tracked, so a function-typed load of it takes this task's typed-load arm
 * — the same rule every other untracked cell follows; the seed's own
 * {@code IntrinsicFunction} registration is unchanged.</p>
 */
public class DynamicProducerRuleTest {

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

    private static final ModuleId MODULE = new ModuleId("app");
    private static final ModuleId LIB = new ModuleId("lib");
    private static final String SOURCE_ID = "app.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();

    // =========================================================================
    // Fixtures
    // =========================================================================

    /**
     * The typed-load arm: the parameter load registers the dynamic record;
     * the alias declaration republishes the load's identity into its own
     * cell (identity preservation — the alias load and the returned load
     * never register again), and the declared call's function-typed result
     * registers the call arm's record.
     */
    private static final String PARAMETER_ALIAS_SOURCE = """
        function apply(f: (x: int) => int): (x: int) => int {
          let g: (x: int) => int = f
          return g
        }

        function double(x: int): int {
          return x * 2
        }

        export function main(): null {
          let h: (x: int) => int = apply(double)
          let r: int = h(21)
          return null
        }
        """;

    /** The member-read arm: a function-typed table member read. */
    private static final String MEMBER_READ_SOURCE = """
        export function main(): null {
          let id: (x: int) => int = function(x: int): int { return x }
          let holder: table = { g: id }
          let g: (x: int) => int = holder.g
          let r: int = g(1)
          return null
        }
        """;

    /** The index-read arm: a function-typed array element read. */
    private static final String INDEX_READ_SOURCE = """
        export function main(): null {
          let id: (x: int) => int = function(x: int): int { return x }
          let fns: ((x: int) => int)[] = [id]
          let g: (x: int) => int = fns[0]
          let r: int = g(1)
          return null
        }
        """;

    /** The field-read arm: a function-typed class field read. */
    private static final String FIELD_READ_SOURCE = """
        class Holder {
          f: (x: int) => int = compute
        }

        function compute(x: int): int {
          return x
        }

        export function main(): null {
          let h: Holder = { f: compute }
          let g: (x: int) => int = h.f
          let r: int = g(1)
          return null
        }
        """;

    /**
     * The optional-read envelope: the declared type is a nullable function,
     * so the read lowers the {@code OPTIONAL_READ} envelope (a nullable
     * result descriptor) and the narrowed value-position load of the
     * guarded cell is the function-typed materialization.
     */
    private static final String OPTIONAL_READ_SOURCE = """
        export function main(): null {
          let id: (x: int) => int = function(x: int): int { return x }
          let holder: table = { g: id }
          let f: ((x: int) => int) | null = holder.g
          if (f !== null) {
            let r: int = f(1)
          }
          return null
        }
        """;

    /** The call-of-call arm: the callee value is a function-typed call result. */
    private static final String CALL_OF_CALL_SOURCE = """
        function pick(f: (x: int) => int): (x: int) => int {
          return f
        }

        function double(x: int): int {
          return x * 2
        }

        export function main(): null {
          let r: int = pick(double)(1)
          return null
        }
        """;

    /**
     * The awaited-completion arm: the declared arm's {@code AWAIT} publishes
     * a function-typed completion, and the dynamic arm's awaited parameter
     * callee publishes the same shape over a runtime-resolved callee.
     */
    private static final String AWAIT_SOURCE = """
        async function makeAsync(): (x: int) => int {
          return function(x: int): int { return x }
        }

        async function run(): int {
          let g: (x: int) => int = await makeAsync()
          return g(1)
        }

        async function apply(f: async () => ((x: int) => int)): int {
          let g: (x: int) => int = await f()
          return g(1)
        }

        export function main(): null {
          return null
        }
        """;

    /** The iteration-binding arm: a function-typed for-of binding load. */
    private static final String ITERATION_BINDING_SOURCE = """
        export function main(): null {
          let id: (x: int) => int = function(x: int): int { return x }
          let fns: ((x: int) => int)[] = [id]
          for (let f: (x: int) => int of fns) {
            let r: int = f(1)
          }
          return null
        }
        """;

    /** The tracked alias arm: a declared function's identity, republished twice. */
    private static final String TRACKED_ALIAS_SOURCE = """
        function make(x: int): int {
          return x
        }

        export function main(): null {
          let g: (x: int) => int = make
          let h: (x: int) => int = g
          let r: int = h(1)
          return null
        }
        """;

    // =========================================================================
    // The frontend + project harness (single module)
    // =========================================================================

    private record CheckedSlice(ProgramNode program, SymbolTable symbols, CheckResult checks) {
    }

    private record Fixture(CheckedProjectInput input, ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           CheckedModuleInput module) {
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath, String importingModule,
                    Set<String> modulesInProgress) throws ModuleNotFoundException {
                Map<String, Map<String, Type>> exports =
                    deal.module.StdlibModuleResolver.stdlibExports(
                        Path.of("std").toAbsolutePath().toString());
                Map<String, Type> moduleExports = exports.get(modulePath);
                if (moduleExports == null) {
                    throw new ModuleNotFoundException("Module not found: " + modulePath);
                }
                return moduleExports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                    String importingModule) {
                return null;
            }
        };
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID).parse();
        check(parse.diagnostics().isEmpty(), what + ": the fixture parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, stdlibResolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": the fixture resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": the fixture checks cleanly: "
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
            Path.of("app.deal"), slice.program(), slice.checks(),
            List.<ResolvedImport>of(), exportsOf(slice.program()),
            CheckedModuleKind.IMPLEMENTATION);
        List<ModuleFact> facts = List.of(new ModuleFact(SOURCE_ID, MODULE, false, false,
            slice.program(), Map.of(), slice.symbols(), slice.checks(), List.of()));
        CompilerInvocation invocation = invocation();
        CheckedProjectBuildResult built = CheckedProjectBuilder.build(invocation, MODULE, facts);
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
        return new Fixture(built.input(), built.index(), manifestResult.manifests(), module);
    }

    /** The one project lowering entry over the fixture. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(invocation(), fixture.input(), fixture.index(),
            fixture.manifests(), new HostDeclarationSurface(Map.of()), Map.of(), Map.of(),
            BuiltinErrorDeclaration.synthesized(fixture.module().ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    /** The direct per-module project walk (the produced, pre-gate unit). */
    private record RawLowering(LoweredModuleUnit unit, StructuredBodyTable table,
                               SemanticLowerer.ModuleLowerer lowerer) {
    }

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
            fail(what + ": the walk produces the unit: " + defect);
            return null;
        }
        LoweredModuleUnit unit = lowerer.buildUnit(
            fixture.manifests().get(0).constructCoverage(),
            fixture.module().imports().stream().map(ResolvedImport::resolvedModuleId).toList(),
            fixture.index().interfaceIndexDigest(), REGISTRY_HASH,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        return new RawLowering(unit, lowerer.bodyTable(), lowerer);
    }

    // =========================================================================
    // Assertions
    // =========================================================================

    private static SemanticIrValidator.ComparisonFacts facts(LoweredModuleUnit unit) {
        return new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    /** The closed schema rules and the bindings production rules in one pass. */
    private static void assertGatePasses(RawLowering raw, String what) {
        LoweredModuleUnit unit = raw.unit();
        Optional<CompilerDiagnostic> schema = SemanticIrValidator.validate(unit, facts(unit));
        check(schema.isEmpty(), what + ": the closed schema rules admit the produced unit: "
            + schema.map(CompilerDiagnostic::message).orElse(""));
        Optional<CompilerDiagnostic> text = SemanticIrValidator.validateText(
            SemanticIrValidator.toUnitText(unit), facts(unit));
        check(text.isEmpty(), what + ": the canonical text surface admits the produced "
            + "unit: " + text.map(CompilerDiagnostic::message).orElse(""));
        Optional<CompilerDiagnostic> bindings = BindingsProductionValidator.validate(unit,
            raw.table(), raw.lowerer().pinnedWriteFacts());
        check(bindings.isEmpty(), what + ": the bindings production rules admit the "
            + "produced unit: "
            + bindings.map(CompilerDiagnostic::message).orElse(""));
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit, SemanticOpKind kind) {
        List<SemanticOp> found = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                found.add(op);
            }
        }
        return found;
    }

    /** The dynamic records of the unit, keyed by their producing op. */
    private static Map<SemanticOp, FunctionExecutionBinding.DynamicFunctionValue>
            dynamicRecordsOf(LoweredModuleUnit unit) {
        Map<SemanticOp, FunctionExecutionBinding.DynamicFunctionValue> records =
            new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            if (!(op.result() instanceof ValueId value)) {
                continue;
            }
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new FunctionAllocationIdentity(value.id()));
            if (binding instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic) {
                records.put(op, dynamic);
            }
        }
        return records;
    }

    /** The distinct identities registered as {@code DynamicFunctionValue}. */
    private static Set<Long> dynamicIdentitiesOf(LoweredModuleUnit unit) {
        Set<Long> identities = new java.util.LinkedHashSet<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                identities.add(entry.getKey().id());
            }
        }
        return identities;
    }

    /** The first op of the given kind whose result identity carries a dynamic record. */
    private static SemanticOp opWithDynamicRecord(LoweredModuleUnit unit,
                                                  SemanticOpKind kind) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != kind || !(op.result() instanceof ValueId value)) {
                continue;
            }
            if (unit.functionBindings().get(new FunctionAllocationIdentity(value.id()))
                    instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                return op;
            }
        }
        return null;
    }

    /** Asserts exactly one dynamic record keyed by the op's result identity. */
    private static FunctionExecutionBinding.DynamicFunctionValue assertDynamicRecord(
            LoweredModuleUnit unit, SemanticOp op, String what) {
        check(op != null, what + ": the producing op exists");
        if (op == null || !(op.result() instanceof ValueId value)) {
            return null;
        }
        long matches = 0;
        FunctionExecutionBinding.DynamicFunctionValue record = null;
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getKey().id() == value.id()
                    && entry.getValue()
                        instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic) {
                matches++;
                record = dynamic;
            }
        }
        check(matches == 1, what + ": exactly one DynamicFunctionValue is keyed by the "
            + op.kind() + " " + op.opId() + " result identity; got " + matches);
        check(record != null && record.materializingOpId().equals(op.opId())
                && record.descriptor().equals(op.resultType()),
            what + ": the record names the producing op and the op's result descriptor; got "
                + record);
        return record;
    }

    private static void assertNoDynamicRecord(LoweredModuleUnit unit, ValueId identity,
                                              String what) {
        FunctionExecutionBinding binding = unit.functionBindings().get(
            new FunctionAllocationIdentity(identity.id()));
        check(!(binding instanceof FunctionExecutionBinding.DynamicFunctionValue),
            what + ": no DynamicFunctionValue is keyed by the identity " + identity
                + "; got " + binding);
    }

    private static SemanticOp onlyOp(LoweredModuleUnit unit, SemanticOpKind kind, String what) {
        List<SemanticOp> found = ofKind(unit, kind);
        check(found.size() == 1, what + ": the unit carries exactly one " + kind
            + "; got " + found.size());
        return found.isEmpty() ? null : found.get(0);
    }

    // =========================================================================
    // 1. The typed-load arm and the call arm (parameter load, alias, call result)
    // =========================================================================

    private static void testParameterAliasAndCallResult() {
        System.out.println("-- the typed-load arm: a parameter load, its alias, and the "
            + "declared call's function-typed result --");
        Fixture fixture = fixture(PARAMETER_ALIAS_SOURCE, "parameter alias");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "parameter alias");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();

        // The parameter load of `f` (the first function-typed load).
        SemanticOp parameterLoad = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.BINDING_LOAD)) {
            if (op.resultType() instanceof RuntimeDescriptor.Func) {
                parameterLoad = op;
                break;
            }
        }
        assertDynamicRecord(unit, parameterLoad, "the parameter load");

        // The declared call's function-typed result.
        Map<SemanticOp, FunctionExecutionBinding.DynamicFunctionValue> records =
            dynamicRecordsOf(unit);
        check(dynamicIdentitiesOf(unit).size() == 2,
            "the fixture carries exactly the two dynamic identities (the parameter "
                + "load and the declared call's result); got "
                + dynamicIdentitiesOf(unit).size());
        for (Map.Entry<SemanticOp, FunctionExecutionBinding.DynamicFunctionValue> entry
                : records.entrySet()) {
            check(entry.getKey().resultType() instanceof RuntimeDescriptor.Func
                    && entry.getValue().descriptor().equals(entry.getKey().resultType()),
                "the record of " + entry.getKey().kind() + " " + entry.getKey().opId()
                    + " carries the op's result descriptor");
        }
        SemanticOp callResult = opWithDynamicRecord(unit, SemanticOpKind.CALL);
        assertDynamicRecord(unit, callResult, "the declared call result");

        // Identity preservation: the alias load of `g` publishes the
        // parameter load's already-allocated identity and never registers
        // again.
        if (parameterLoad != null && parameterLoad.result() instanceof ValueId identity) {
            long publishers = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BINDING_LOAD
                        && op.result() instanceof ValueId value
                        && value.id() == identity.id()) {
                    publishers++;
                }
            }
            check(publishers >= 2, "the parameter load's identity is republished by the "
                + "alias cell's load without a second registration (identity "
                + "preservation); got " + publishers + " publishing loads");
        }

        assertGatePasses(raw, "the parameter-alias unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the parameter-alias fixture: "
                + result.diagnostics());
    }

    // =========================================================================
    // 2. The read arms
    // =========================================================================

    private static void testMemberReadArm() {
        System.out.println("-- the member-read arm: a function-typed table member read --");
        Fixture fixture = fixture(MEMBER_READ_SOURCE, "member read");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "member read");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp read = onlyOp(unit, SemanticOpKind.MEMBER_READ, "the member read");
        assertDynamicRecord(unit, read,
            "the function-typed member read");
        check(dynamicIdentitiesOf(unit).size() == 1, "the member-read fixture registers "
            + "exactly one dynamic identity; got " + dynamicIdentitiesOf(unit).size());
        assertGatePasses(raw, "the member-read unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the member-read fixture: "
                + result.diagnostics());
    }

    private static void testIndexReadArm() {
        System.out.println("-- the index-read arm: a function-typed array element read --");
        Fixture fixture = fixture(INDEX_READ_SOURCE, "index read");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "index read");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp read = onlyOp(unit, SemanticOpKind.INDEX_READ, "the index read");
        assertDynamicRecord(unit, read, "the function-typed index read");
        assertGatePasses(raw, "the index-read unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the index-read fixture: "
                + result.diagnostics());
    }

    private static void testFieldReadArm() {
        System.out.println("-- the field-read arm: a function-typed class field read --");
        Fixture fixture = fixture(FIELD_READ_SOURCE, "field read");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "field read");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp read = onlyOp(unit, SemanticOpKind.FIELD_READ, "the field read");
        assertDynamicRecord(unit, read, "the function-typed field read");
        assertGatePasses(raw, "the field-read unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the field-read fixture: "
                + result.diagnostics());
    }

    private static void testOptionalReadEnvelope() {
        System.out.println("-- the optional-read envelope: the nullable read and its "
            + "narrowed value-position load --");
        Fixture fixture = fixture(OPTIONAL_READ_SOURCE, "optional read");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "optional read");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp optional = onlyOp(unit, SemanticOpKind.OPTIONAL_READ,
            "the optional-read envelope");
        check(optional != null && optional.result() instanceof ValueId value
                && optional.resultType() instanceof RuntimeDescriptor.Nullable nullable
                && nullable.inner() instanceof RuntimeDescriptor.Func,
            "the envelope publishes the nullable function descriptor; got "
                + (optional == null ? "no envelope" : optional.resultType()));
        if (optional != null && optional.result() instanceof ValueId identity) {
            // The envelope's result is not a function-typed result: the
            // correlation clause resolves the named op's result descriptor
            // against the registered Func descriptor, so no dynamic record is
            // keyed by a nullable result.
            assertNoDynamicRecord(unit, identity,
                "the optional-read envelope");
        }

        // The narrowed value-position load of the guarded cell is the
        // function-typed materialization the call dispatches on.
        SemanticOp narrowed = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.BINDING_LOAD)) {
            if (op.resultType() instanceof RuntimeDescriptor.Func
                    && op.origin() != null && op.result() instanceof ValueId value
                    && unit.functionBindings().get(
                        new FunctionAllocationIdentity(value.id()))
                        instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                narrowed = op;
            }
        }
        assertDynamicRecord(unit, narrowed, "the narrowed value-position load");
        assertGatePasses(raw, "the optional-read unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the optional-read fixture: "
                + result.diagnostics());
    }

    // =========================================================================
    // 3. The call-of-call arm and the awaited-completion arm
    // =========================================================================

    private static void testCallOfCallArm() {
        System.out.println("-- the call arm: a dynamically resolved callee that is "
            + "itself a function-typed call result --");
        Fixture fixture = fixture(CALL_OF_CALL_SOURCE, "call of call");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "call of call");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp dynamicCall = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Dynamic) {
                dynamicCall = op;
            }
        }
        check(dynamicCall != null, "the call of the call result lowers a Dynamic callee");
        if (dynamicCall != null) {
            KindPayload.CallPayload payload =
                (KindPayload.CallPayload) dynamicCall.payload();
            ValueId callee = ((KindPayload.CallCallee.Dynamic) payload.callee()).callee();
            SemanticOp calleeProducer = null;
            for (SemanticOp op : unit.ops()) {
                if (op.result() instanceof ValueId value && value.equals(callee)) {
                    calleeProducer = op;
                }
            }
            check(calleeProducer != null
                    && calleeProducer.kind() == SemanticOpKind.CALL,
                "the dynamic callee value is the inner call's function-typed result; got "
                    + (calleeProducer == null ? "null" : calleeProducer.kind()));
            assertDynamicRecord(unit, calleeProducer, "the inner call result");
        }
        // The parameter load of `pick` is the second dynamic identity.
        check(dynamicIdentitiesOf(unit).size() == 2,
            "the fixture carries exactly the two dynamic identities (the parameter load "
                + "and the inner call result); got " + dynamicIdentitiesOf(unit).size());
        assertGatePasses(raw, "the call-of-call unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the call-of-call fixture: "
                + result.diagnostics());
    }

    private static void testAwaitCompletionArm() {
        System.out.println("-- the awaited-completion arm: the AWAIT op's function-typed "
            + "completion (the ASYNC_START result is the token) --");
        Fixture fixture = fixture(AWAIT_SOURCE, "await completion");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "await completion");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();

        // The ASYNC_START results are tokens under INTERNAL_ASYNC and register
        // nothing; the AWAITs publish the function-typed completions.
        List<SemanticOp> starts = ofKind(unit, SemanticOpKind.ASYNC_START);
        check(starts.size() == 2, "the fixture carries the declared and the dynamic "
            + "ASYNC_START; got " + starts.size());
        for (SemanticOp start : starts) {
            check(start.result() instanceof AsyncTokenId
                    && start.resultType() == InternalResultType.INTERNAL_ASYNC,
                "the ASYNC_START result is the token under INTERNAL_ASYNC; got "
                    + start.result() + " / " + start.resultType());
        }

        List<SemanticOp> awaits = ofKind(unit, SemanticOpKind.AWAIT);
        int functionTypedCompletions = 0;
        for (SemanticOp await : awaits) {
            if (await.resultType() instanceof RuntimeDescriptor.Func) {
                functionTypedCompletions++;
                assertDynamicRecord(unit, await, "the function-typed awaited completion");
            }
        }
        check(awaits.size() == 2 && functionTypedCompletions == 2,
            "both AWAITs publish a function-typed completion (the declared arm and the "
                + "dynamic arm); got " + awaits.size() + " awaits, "
                + functionTypedCompletions + " function-typed");
        assertGatePasses(raw, "the await-completion unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the await-completion fixture: "
                + result.diagnostics());
    }

    private static void testIterationBindingArm() {
        System.out.println("-- the iteration-binding arm: a function-typed for-of binding load "
            + "--");
        Fixture fixture = fixture(ITERATION_BINDING_SOURCE, "iteration binding");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "iteration binding");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp load = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.BINDING_LOAD)) {
            if (op.resultType() instanceof RuntimeDescriptor.Func
                    && op.result() instanceof ValueId value
                    && unit.functionBindings().get(
                        new FunctionAllocationIdentity(value.id()))
                        instanceof FunctionExecutionBinding.DynamicFunctionValue) {
                load = op;
                break;
            }
        }
        assertDynamicRecord(unit, load, "the function-typed for-of binding load");
        assertGatePasses(raw, "the iteration-binding unit");
        SemanticLowerer.ProjectLoweringResult result = lower(fixture);
        check(result.project() != null && result.diagnostics().isEmpty(),
            "the project entry produces a project for the iteration-binding fixture: "
                + result.diagnostics());
    }

    // =========================================================================
    // 4. Preserved static classes
    // =========================================================================

    private static void testTrackedAliasPreservation() {
        System.out.println("-- preserved static class: a tracked alias load republishes "
            + "the declared function's identity --");
        Fixture fixture = fixture(TRACKED_ALIAS_SOURCE, "tracked alias");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "tracked alias");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        check(dynamicRecordsOf(unit).isEmpty(), "the tracked-alias fixture registers no "
            + "dynamic record: " + dynamicRecordsOf(unit).keySet());
        // Every function-typed load publishes one identity, registered as the
        // declared function's LoweredBody.
        ValueId identity = null;
        int loads = 0;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.BINDING_LOAD)) {
            if (!(op.resultType() instanceof RuntimeDescriptor.Func)
                    || !(op.result() instanceof ValueId value)) {
                continue;
            }
            loads++;
            if (identity == null) {
                identity = value;
            } else {
                check(identity.equals(value), "every function-typed load of the tracked "
                    + "cells republishes the same identity; got " + identity + " and "
                    + value);
            }
        }
        check(loads >= 2 && identity != null, "the fixture carries the tracked cell's "
            + "loads; got " + loads);
        if (identity != null) {
            check(unit.functionBindings().get(new FunctionAllocationIdentity(identity.id()))
                    instanceof FunctionExecutionBinding.LoweredBody,
                "the tracked identity keeps its landed LoweredBody registration; got "
                    + unit.functionBindings().get(
                        new FunctionAllocationIdentity(identity.id())));
        }
        assertGatePasses(raw, "the tracked-alias unit");
    }

    // =========================================================================
    // 5. The imported read and the imported call result (two modules)
    // =========================================================================

    private static final String LIB_SOURCE = """
        export function double(x: int): int {
          return x * 2
        }

        export function make(): (x: int) => int {
          return function(x: int): int { return x }
        }
        """;

    private static final String IMPORT_SOURCE = """
        import * as lib from "./lib"

        function apply(f: (x: int) => int): int {
          return f(1)
        }

        export function main(): null {
          let f: (x: int) => int = lib.double
          let g: (x: int) => int = lib.make()
          let r: int = g(1)
          let s: int = apply(f)
          return null
        }
        """;

    private record ProjectFixture(SemanticLowerer.ProjectLoweringResult lowered) {
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
    }

    private static void deleteRecursively(Path root) {
        if (root == null || !Files.exists(root)) {
            return;
        }
        try (var walk = Files.walk(root)) {
            walk.sorted(java.util.Comparator.reverseOrder()).forEach(path -> {
                try {
                    Files.deleteIfExists(path);
                } catch (java.io.IOException ignored) {
                    // best effort
                }
            });
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    private static final String STDLIB_READ_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let f: (x: string) => null = console.log
          return null
        }
        """;

    /**
     * The module-namespace member read: the import alias's value position
     * holds the module's surface as a {@code table}, so its function-typed
     * member read takes the landed {@code MEMBER_READ} arm — the producer
     * rule's dynamic registration — never a second read production.
     */
    private static final String NAMESPACE_READ_SOURCE = """
        import * as console from "std/console"

        export function main(): null {
          let c: table = console
          let g: (x: string) => null = c.log
          return null
        }
        """;

    private static ProjectFixture compileProject(Map<String, String> sources)
            throws Exception {
        Path root = Files.createTempDirectory("dynamic-producer-rule");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(src.toAbsolutePath()), Path.of("std").toAbsolutePath().normalize(),
            null, invocation());
        orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the probe project did not build: "
                + detail + " / " + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        BuiltinErrorDeclaration builtinError = BuiltinErrorDeclaration.synthesized(
            built.input().modules().get(0).ast().span());
        SemanticLowerer.ProjectLoweringResult lowered = SemanticLowerer.lowerProject(
            invocation(), built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(),
            Map.<ModuleId, CanonicalModuleIdentity>of(), externCModules, builtinError,
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
        deleteRecursively(root);
        return new ProjectFixture(lowered);
    }

    private static void testImportedReadAndCallResult() throws Exception {
        System.out.println("-- the imported arm: the export read keeps its static class "
            + "and the imported call's function-typed result registers dynamically --");
        ProjectFixture fixture = compileProject(Map.of(
            "src/lib.deal", LIB_SOURCE, "src/app.deal", IMPORT_SOURCE));
        SemanticLowerer.ProjectLoweringResult lowered = fixture.lowered();
        check(lowered.project() != null && lowered.diagnostics().isEmpty(),
            "the two-module project lowers: " + lowered.diagnostics());
        if (lowered.project() == null) {
            return;
        }
        LoweredModuleUnit app = lowered.project().modules().get(MODULE);
        LoweredModuleUnit lib = lowered.project().modules().get(LIB);
        check(app != null && lib != null, "the project carries both units");
        if (app == null || lib == null) {
            return;
        }

        // The value-position export read keeps its landed static class.
        List<SemanticOp> reads = ofKind(app, SemanticOpKind.EXPORT_READ);
        check(reads.size() == 2, "the app unit carries the value read and the call "
            + "callee's read; got " + reads.size());
        ValueId readValue = null;
        for (SemanticOp read : reads) {
            FunctionExecutionBinding binding = app.functionBindings().get(
                new FunctionAllocationIdentity(
                    ((KindPayload.ExportReadPayload) read.payload()).value().id()));
            check(binding instanceof FunctionExecutionBinding.ExternalFunction external
                    && external.executionOwner() == ExternalExecutionOwner.SHARED_BODY,
                "the imported function-typed export read keeps its ExternalFunction "
                    + "(SHARED_BODY) registration; got " + binding);
            if (readValue == null) {
                readValue = ((KindPayload.ExportReadPayload) read.payload()).value();
            }
        }
        if (readValue != null) {
            assertNoDynamicRecord(app, readValue, "the value-position export read");
        }

        // The imported call's function-typed result registers the call arm's
        // record.
        SemanticOp importedCall = null;
        for (SemanticOp op : ofKind(app, SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.mode() == CallMode.EXTERNAL) {
                importedCall = op;
            }
        }
        check(importedCall != null, "the app unit carries the imported CALL(EXTERNAL)");
        assertDynamicRecord(app, importedCall, "the imported call's function-typed result");

        Optional<CompilerDiagnostic> schema = SemanticIrValidator.validate(lowered.project(),
            new SemanticIrValidator.ComparisonFacts(
                lowered.project().interfaceIndex().interfaceIndexDigest(),
                SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH));
        check(schema.isEmpty(), "the two-module project passes the closed schema rules: "
            + schema.map(CompilerDiagnostic::message).orElse(""));
    }

    private static void testStdlibReadPreservedClass() throws Exception {
        System.out.println("-- preserved static class: a STDLIB function-typed export "
            + "read keeps its HostFunction registration --");
        ProjectFixture fixture = compileProject(Map.of("src/app.deal", STDLIB_READ_SOURCE));
        SemanticLowerer.ProjectLoweringResult lowered = fixture.lowered();
        check(lowered.project() != null && lowered.diagnostics().isEmpty(),
            "the STDLIB-read project lowers: " + lowered.diagnostics());
        if (lowered.project() == null) {
            return;
        }
        LoweredModuleUnit app = lowered.project().modules().get(MODULE);
        check(app != null, "the project carries the app unit");
        if (app == null) {
            return;
        }
        List<SemanticOp> reads = ofKind(app, SemanticOpKind.EXPORT_READ);
        check(reads.size() == 1, "the app unit carries exactly the stdlib export read; "
            + "got " + reads.size());
        for (SemanticOp read : reads) {
            ValueId value = ((KindPayload.ExportReadPayload) read.payload()).value();
            FunctionExecutionBinding binding = app.functionBindings().get(
                new FunctionAllocationIdentity(value.id()));
            check(binding instanceof FunctionExecutionBinding.HostFunction host
                    && host.exportName().equals("log"),
                "the STDLIB function-typed export read keeps its HostFunction "
                    + "registration; got " + binding);
            assertNoDynamicRecord(app, value, "the STDLIB export read");
        }
    }

    /** The closed schema rules over a lowered project (typed and canonical text). */
    private static void assertProjectSchemaPasses(
            SemanticLowerer.ProjectLoweringResult lowered, String what) {
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            lowered.project().interfaceIndex().interfaceIndexDigest(),
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
        Optional<CompilerDiagnostic> typed = SemanticIrValidator.validate(
            lowered.project(), facts);
        check(typed.isEmpty(), what + ": the closed schema rules admit the lowered "
            + "project: " + typed.map(CompilerDiagnostic::message).orElse(""));
        for (LoweredModuleUnit unit : lowered.project().modules().values()) {
            Optional<CompilerDiagnostic> text = SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(unit), facts);
            check(text.isEmpty(), what + ": the canonical text surface admits the "
                + unit.moduleId() + " unit: "
                + text.map(CompilerDiagnostic::message).orElse(""));
        }
    }

    private static void testNamespaceMemberReadArm() throws Exception {
        System.out.println("-- the module-namespace member read: the table-held namespace "
            + "flows through the same member-read arm --");
        ProjectFixture fixture = compileProject(
            Map.of("src/app.deal", NAMESPACE_READ_SOURCE));
        SemanticLowerer.ProjectLoweringResult lowered = fixture.lowered();
        check(lowered.project() != null && lowered.diagnostics().isEmpty(),
            "the namespace-read project lowers: " + lowered.diagnostics());
        if (lowered.project() == null) {
            return;
        }
        LoweredModuleUnit app = lowered.project().modules().get(MODULE);
        check(app != null, "the project carries the app unit");
        if (app == null) {
            return;
        }
        SemanticOp read = null;
        long functionTypedReads = 0;
        for (SemanticOp op : ofKind(app, SemanticOpKind.MEMBER_READ)) {
            if (op.result() instanceof ValueId value
                    && op.resultType() instanceof RuntimeDescriptor.Func) {
                functionTypedReads++;
                read = op;
                FunctionExecutionBinding registration = app.functionBindings().get(
                    new FunctionAllocationIdentity(value.id()));
                check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
                    "the module-namespace member read's result identity carries the "
                        + "producer rule's dynamic record; got " + registration);
            }
        }
        check(functionTypedReads == 1, "the namespace-read fixture carries exactly one "
            + "function-typed member read; got " + functionTypedReads);
        assertDynamicRecord(app, read, "the module-namespace member read");
        assertProjectSchemaPasses(lowered, "the namespace-read project");
    }

    // =========================================================================
    // 6. Negative seeds
    // =========================================================================

    private static LoweredModuleUnit withoutRegistration(LoweredModuleUnit unit,
                                                         ValueId identity) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.remove(new FunctionAllocationIdentity(identity.id()));
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), bindings, unit.ops());
    }

    private static LoweredModuleUnit withRegistration(LoweredModuleUnit unit,
            ValueId identity, FunctionExecutionBinding binding) {
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.put(new FunctionAllocationIdentity(identity.id()), binding);
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(), unit.classLayouts(),
            unit.functions(), unit.moduleInit(), unit.exportPlan(), bindings, unit.ops());
    }

    private static void testNegativeSeeds() {
        System.out.println("-- negative seeds: the dropped registration, the static "
            + "producing position, and the duplicate key --");
        Fixture fixture = fixture(MEMBER_READ_SOURCE, "member read negative");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "member read negative");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp read = onlyOp(unit, SemanticOpKind.MEMBER_READ, "the member read");
        if (read != null && read.result() instanceof ValueId identity) {
            Optional<CompilerDiagnostic> dropped = SemanticIrValidator.validate(
                withoutRegistration(unit, identity), facts(unit));
            check(dropped.isPresent()
                    && dropped.get().message().contains("R-FUNCTION-BINDING"),
                "a function-typed read result with zero registrations fails the closed "
                    + "schema rules with R-FUNCTION-BINDING; got "
                    + dropped.map(CompilerDiagnostic::message).orElse("no diagnostic"));
        }

        // A dynamic registration keyed by a static producing position (a
        // closure's own identity) fails the producing-position clause.
        SemanticOp closure = null;
        for (SemanticOp op : ofKind(unit, SemanticOpKind.CLOSURE_NEW)) {
            if (op.result() instanceof ValueId value && read != null
                    && read.result() instanceof ValueId readIdentity
                    && value.id() != readIdentity.id()) {
                closure = op;
                break;
            }
        }
        if (closure != null && closure.result() instanceof ValueId closureIdentity
                && read != null && read.result() instanceof ValueId readIdentity) {
            LoweredModuleUnit doctored = withRegistration(unit, readIdentity,
                new FunctionExecutionBinding.DynamicFunctionValue(closure.opId(),
                    (RuntimeDescriptor.Func) read.resultType()));
            Optional<CompilerDiagnostic> staticPosition =
                BindingsProductionValidator.validate(doctored, raw.table(),
                    raw.lowerer().pinnedWriteFacts());
            check(staticPosition.isPresent()
                    && staticPosition.get().message().contains("REGISTRY_ONE_TO_ONE"),
                "a dynamic record naming a foreign op fails the producing-position "
                    + "clause; got "
                    + staticPosition.map(CompilerDiagnostic::message).orElse("admission"));
        }

        // The registry rejects a duplicate key at registration time.
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        ValueId identity = new ValueId(9_100);
        RuntimeDescriptor.Func descriptor = (RuntimeDescriptor.Func)
            RuntimeDescriptor.parseCanonicalText("(int)->int");
        registry.registerDynamicFunctionValue(new FunctionAllocationIdentity(identity.id()),
            new OpId(MODULE, 1), descriptor);
        boolean rejected = false;
        try {
            registry.registerDynamicFunctionValue(
                new FunctionAllocationIdentity(identity.id()), new OpId(MODULE, 2),
                descriptor);
        } catch (IllegalStateException expected) {
            rejected = true;
        }
        check(rejected, "a duplicate dynamic key is rejected at registration time");
        check(registry.size() == 1 && registry.bindings().get(
                new FunctionAllocationIdentity(identity.id()))
                instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the first dynamic registration is never overwritten");
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Dynamic Producer Rule / Materialization Arms Tests "
            + "(ISSUE-0675) ===\n");

        testParameterAliasAndCallResult();
        testMemberReadArm();
        testIndexReadArm();
        testFieldReadArm();
        testOptionalReadEnvelope();
        testCallOfCallArm();
        testAwaitCompletionArm();
        testIterationBindingArm();
        testTrackedAliasPreservation();
        testImportedReadAndCallResult();
        testStdlibReadPreservedClass();
        testNamespaceMemberReadArm();
        testNegativeSeeds();

        System.out.println("\nDynamic producer rule: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
