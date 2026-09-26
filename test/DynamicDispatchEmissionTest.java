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
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
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
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.test.SemanticDifferentialHarness;
import deal.types.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0658: the dynamic dispatch emission and the function-id to
 * owning-module resolution (design source
 * {@code dynamic-call-shape-production-and-emission} Y2, Y3, Y5, Y6, the
 * dynamic dispatch contract, the dynamic async start contract, and the
 * boundary with the function-typed-value child;
 * {@code semantic-ir-construct-coverage-cutover} K5/K12;
 * {@code luajit-jvm-single-lowering-production-cutover} C2).
 *
 * <ol>
 *   <li><b>The emitted dispatch surface (both targets).</b> The dynamic
 *       {@code CALL} arm of {@code LuaSemanticEmitter}/{@code
 *       JvmSemanticEmitter} dispatches on the carrier's own class tag: the
 *       DEAL-body path resolves the carrier's function id through the
 *       artifact's function-id to owning-module resolution (the LuaJIT
 *       chunk-global {@code __fnModules} table built by the walk that
 *       declares the function factories; the JVM generated {@code
 *       dealModuleOfFunction} lookup over the closure's function ids),
 *       pushes the callee frame, switches the module context, and invokes
 *       the carrier's own invoker; the adapter path runs the landed D15
 *       sequence; the HOST path invokes the loaded surface entry and runs
 *       the recorded {@code HOST_TO_DEAL}+{@code HOST_SYNC_RETURN} cell;
 *       every other carrier projects the pinned E8001 {@code expected
 *       function} text at the call origin. The JVM production factories
 *       carry the descriptor text, the canonical spec text, and the
 *       function identity (the four-argument {@code FunctionValue}
 *       construction) and the adapter value keeps {@code fid = null}.</li>
 *   <li><b>The closure-carrier drive.</b> A function-typed parameter
 *       whose runtime carrier is a DEAL closure executes the DEAL-body
 *       class path: the closed gate passes, the semantic oracle and both
 *       trace-mode emitters agree event-for-event over the same project
 *       (class path, selected return cell, frames, module context), and
 *       the production artifacts of both targets execute under real
 *       {@code luajit} and {@code javac --release 25 -proc:none} +
 *       {@code java} with the pinned result.</li>
 *   <li><b>The adapter-carrier drive.</b> The same parameter whose
 *       runtime carrier is a {@code FUNCTION_ADAPT} adapter executes the
 *       adapter path (the source value's own tag, the source-signature
 *       check, the leading-M projection) with the source class's cell.</li>
 *   <li><b>The dynamic async drive.</b> A dynamic {@code ASYNC_START}
 *       over a DEAL-body carrier starts the callee body task under the
 *       callee's module context and completes at the single {@code
 *       AWAIT} through the recorded task cell; the async-entry drive
 *       compares the oracle and both emitted dispatch entries
 *       event-for-event and executes under both real toolchains.</li>
 *   <li><b>The dynamic async adapter drive.</b> The awaited callee's
 *       runtime carrier is a {@code FUNCTION_ADAPT} value over an async
 *       DEAL body: the ADAPTER class runs the landed D15 sequence (the
 *       source value's own tag, the source-signature check, the
 *       leading-M argument projection) and starts the source body task
 *       under the source's module context with the recorded task cell
 *       and zero caller-side return boundaries beyond it, matching the
 *       oracle event-for-event and executing under both real
 *       toolchains.</li>
 *   <li><b>The closed DEAL-body cell forms and their executors
 *       (ISSUE-0677; design source
 *       {@code function-typed-value-materialization-and-dispatch} M6 and the
 *       dynamic DEAL-body cell contract).</b> A runtime-resolved callee
 *       (the producer rule's {@code DynamicFunctionValue} registration)
 *       records the landed call-owned cell, which the invocation site
 *       executes on the value the resolved body returned — sync after the
 *       body's own {@code RETURN} cell and before the {@code CALL}
 *       publishes, async in the caller-side task wrapper before the token
 *       completes; a statically identified same-walk body records its own
 *       RETURN-materialized cell, executed exactly once by that body's
 *       {@code RETURN}. Both forms are driven on the oracle and both real
 *       toolchains with the recorded cell's event position, its single
 *       execution, and the class path asserted.</li>
 *   <li><b>The oracle's value channel.</b> A dynamic callee whose value
 *       carries the producer rule's dynamic record (or none) resolves the
 *       runtime heap value's own producing registration through the
 *       value-keyed channel, so the dispatched class is the class of the
 *       materialized carrier; a heap value with no producing registration
 *       fails closed as a producer defect.</li>
 *   <li><b>The composed drive.</b> The host module's sync and async
 *       exports, the compiled module's sync and async exports, and the
 *       dynamic dispatch compose in one production project on both
 *       targets.</li>
 *   <li><b>Fault drives.</b> A carrier that is not a function value
 *       fails with the pinned E8001 {@code expected function} projection
 *       at the call origin on both targets and fails closed in the
 *       oracle; an adapter whose recorded source signature differs from
 *       its source's carried spec fails with E8010 under D15; a
 *       dynamically invoked DEAL body whose own {@code RETURN} cell
 *       check fails projects the cell's text with the callee's origin on
 *       both targets and in the oracle; an adapter whose D15 source
 *       value identifies no class the closed protocol resolves fails
 *       closed with the pinned E8001 (and the oracle's fail-closed
 *       guard).</li>
 *   <li><b>No extension, no regression.</b> The closed op-kind,
 *       boundary-kind, failure-policy, and payload-record sets are
 *       unchanged; the static call and async arms keep their landed
 *       shapes; no dynamic callee emitter gap exists to retarget.</li>
 * </ol>
 *
 * <p>The drives lower the fixture through the one project walk and
 * validate the produced unit as it stands: the callee value keeps the
 * producer rule's own registration (ISSUE-0675/ISSUE-0677 — the
 * {@code DynamicFunctionValue} record for a carrier read, the same-walk
 * body's {@code LoweredBody} for an in-place function expression), the
 * oracle resolves a runtime-resolved callee's class through the value
 * channel, and the emitted artifact reads the same class from the
 * carrier's own tag. No drive doctors a registration: a broken producer
 * arm, value channel, or form decision fails the drive. Nothing else in
 * the produced unit is changed — every op, cell, boundary, and origin is
 * the one lowering's own output.</p>
 */
public class DynamicDispatchEmissionTest {

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

    /** The closure-carrier parameter drive: a DEAL closure into a parameter. */
    private static final String CLOSURE_SOURCE = """
        function dbl(x: int): int {
          return x * 2
        }

        function apply(f: (x: int) => int, x: int): int {
          return f(x)
        }

        export function main(): null {
          let r: int = apply(dbl, 21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "closure dispatch" }
          }
          return null
        }
        """;

    /** The adapter-carrier parameter drive: an arity-extension adapter value. */
    private static final String ADAPTER_SOURCE = """
        function inc(x: int): int {
          return x + 1
        }

        function apply(f: (a: int, b: int) => int, x: int, y: int): int {
          return f(x, y)
        }

        export function main(): null {
          let adapted: (a: int, b: int) => int = inc
          let r: int = apply(adapted, 41, 9)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "adapter dispatch" }
          }
          return null
        }
        """;

    /** The dynamic async drive: an awaited function-typed parameter callee. */
    private static final String ASYNC_SOURCE = """
        async function value(): int {
          return 42
        }

        async function drive(f: async () => int): int {
          let v: int = await f()
          return v
        }

        export async function probe(): int {
          return await drive(value)
        }

        export function main(): null {
          return null
        }
        """;

    /**
     * The dynamic async adapter drive: an awaited function-typed parameter
     * whose runtime carrier is a {@code FUNCTION_ADAPT} value over an async
     * DEAL body (the reviewer's drive shape: the declared target takes two
     * parameters, the source takes one, so the leading-M projection drops
     * the second argument).
     */
    private static final String ASYNC_ADAPTER_SOURCE = """
        async function inc(x: int): int {
          return x + 1
        }

        async function drive(f: async (a: int, b: int) => int, x: int, y: int): int {
          let v: int = await f(x, y)
          return v
        }

        export async function probe(): int {
          let adapted: async (a: int, b: int) => int = inc
          return await drive(adapted, 41, 9)
        }

        export function main(): null {
          return null
        }
        """;

    private record CheckedSlice(ProgramNode program, SymbolTable symbols,
                                CheckResult checks) {
    }

    private record Fixture(CheckedProjectInput input, ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           CheckedModuleInput module) {
    }

    private static ModuleResolver stdlibResolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath,
                    String importingModule, Set<String> modulesInProgress)
                    throws ModuleNotFoundException {
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
        return new Fixture(built.input(), built.index(), manifestResult.manifests(),
            module);
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
            fixture.module().imports().stream().map(ResolvedImport::resolvedModuleId)
                .toList(),
            fixture.index().interfaceIndexDigest(), REGISTRY_HASH,
            ContainerClaimingSeam.E9_GATE_ACTIVATION);
        return new RawLowering(unit, lowerer.bodyTable(), lowerer);
    }

    // =========================================================================
    // The drive surface (the producer rule's own registrations)
    // =========================================================================

    /** One drive: the unit, its membership table, and the validated project. */
    private record Drive(LoweredModuleUnit unit, StructuredBodyTable table,
                         ExecutableLoweredProject project,
                         ClassFactoryRegistry registry) {
    }

    private static ExecutableLoweredProject projectOf(LoweredModuleUnit unit) {
        return new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32,
            new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
                Map.of(MODULE, new ExternalModuleInterface(MODULE,
                    ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
                    InitializationMode.ONCE_AFTER_DEPENDENCIES))),
            Map.of(MODULE, unit), MODULE);
    }

    /** The closed origin text of one op ({@code source:line:column}). */

    /** The dynamic CALL op of the unit. */
    private static SemanticOp dynamicCall(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload call
                    && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    /** The dynamic ASYNC_START op of the unit. */
    private static SemanticOp dynamicAsyncStart(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.AsyncStartPayload start
                    && start.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
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

    /**
     * The runtime carrier binding of the value flowing into one parameter
     * of the caller's call: the binding the argument's own materialization
     * registered, which is exactly the binding the runtime carrier carries
     * into the callee's parameter cell. Both the static {@code CALL} and
     * {@code ASYNC_START} arms carry their declared parameter cells.
     */
    private static FunctionExecutionBinding carrierBinding(LoweredModuleUnit unit,
            int parameterIndex) {
        for (SemanticOp op : unit.ops()) {
            KindPayload.CallCallee callee;
            List<OpId> parameterBoundaries;
            if (op.payload() instanceof KindPayload.CallPayload call) {
                callee = call.callee();
                parameterBoundaries = call.parameterBoundaryOpIds();
            } else if (op.payload() instanceof KindPayload.AsyncStartPayload start) {
                callee = start.callee();
                parameterBoundaries = start.parameterBoundaryOpIds();
            } else {
                continue;
            }
            if (!(callee instanceof KindPayload.CallCallee.Static)) {
                continue;
            }
            if (parameterIndex >= parameterBoundaries.size()) {
                continue;
            }
            SemanticOp boundary = opOf(unit, parameterBoundaries.get(parameterIndex));
            if (boundary == null
                    || !(boundary.payload() instanceof KindPayload.BoundaryPayload payload)
                    || payload.kind() != BoundaryKind.FUNCTION_PARAMETER) {
                continue;
            }
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new FunctionAllocationIdentity(payload.input().id()));
            if (binding != null) {
                return binding;
            }
        }
        return null;
    }

    /**
     * One prepared drive: the gate-validated project of one carrier class
     * over the producer rule's own registrations (ISSUE-0677). The callee
     * value keeps the {@code DynamicFunctionValue} record the producer rule
     * registered for its carrier read — the runtime class comes from the
     * value channel — and the runtime carrier binding of the argument is
     * resolved for the drive's class assertions only.
     */
    private static Drive drive(Fixture fixture, int parameterIndex, String what) {
        RawLowering raw = rawLower(fixture, what);
        if (raw == null) {
            return null;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        check(call != null, what + ": the unit carries the dynamic CALL shape");
        if (call == null) {
            return null;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            what + ": the callee value carries the producer rule's dynamic "
                + "materialization record: " + registration);
        FunctionExecutionBinding carrier = carrierBinding(unit, parameterIndex);
        check(carrier != null, what + ": the argument's runtime carrier binding "
            + "resolves: " + carrier);
        if (carrier == null) {
            return null;
        }
        return validateDrive(unit, raw, what);
    }

    /**
     * Runs the closed gate over the produced unit as it stands (no
     * registration doctoring: the producer rule's own records are the
     * drive's input).
     */
    private static Drive validateDrive(LoweredModuleUnit unit, RawLowering raw,
            String what) {
        ExecutableLoweredProject project = projectOf(unit);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    unit.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), what + ": the closed gate accepts the drive project: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return null;
        }
        return new Drive(unit, raw.table(), project,
            new ClassFactoryRegistry(Map.of()));
    }

    /**
     * The recorded DEAL-body cell of one drive's dynamic invocation and
     * whether it is the call-owned form: its parent {@code RETURN} names no
     * lowered body of the unit.
     */
    private record RecordedCell(SemanticOp cell, SemanticOp parent, boolean callOwned) {
    }

    private static RecordedCell recordedDealCell(LoweredModuleUnit unit, SemanticOp invocation) {
        OpId cellOpId = switch (invocation.payload()) {
            case KindPayload.CallPayload call -> call.dynamicReturnBoundary() == null
                ? null : call.dynamicReturnBoundary().dealBodyBoundaryOpId();
            case KindPayload.AsyncStartPayload start -> start.returnBoundaryOpId();
            default -> null;
        };
        if (cellOpId == null) {
            return null;
        }
        SemanticOp cell = opOf(unit, cellOpId);
        KindPayload.ReturnPayload returned = cell == null ? null : returnOf(unit, cell);
        boolean callOwned = returned == null
            || !unit.functions().containsKey(returned.function());
        return new RecordedCell(cell, returned == null ? null
            : opOf(unit, cell.origin().parentOpId()), callOwned);
    }

    /** The RETURN payload of one recorded cell's parent op, or null. */
    private static KindPayload.ReturnPayload returnOf(LoweredModuleUnit unit,
            SemanticOp cell) {
        if (cell.origin() == null || cell.origin().parentOpId() == null) {
            return null;
        }
        SemanticOp parent = opOf(unit, cell.origin().parentOpId());
        return parent != null && parent.kind() == SemanticOpKind.RETURN
                && parent.payload() instanceof KindPayload.ReturnPayload returned
            ? returned : null;
    }

    /** The trace index of the last event of one op in one phase, or -1. */
    private static int eventIndex(List<String> events, OpId op, String phase) {
        int found = -1;
        for (int i = 0; i < events.size(); i++) {
            if (events.get(i).contains("|" + op.module().path() + "#" + op.id()
                    + "|" + phase + "|")) {
                found = i;
            }
        }
        return found;
    }

    /**
     * The recorded call-owned cell executes at the invocation site
     * (ISSUE-0677): its boundary events appear after the resolved body's own
     * return-cell events and before the invocation's SUCCESS terminal, and
     * the cell runs exactly once.
     */
    private static void assertCallOwnedCellRun(String what, List<String> events,
            OpId invocation, OpId bodyReturnCell, RecordedCell recorded, int callSuccess) {
        check(recorded != null && recorded.callOwned(),
            what + ": the recorded DEAL-body cell is the call-owned form");
        if (recorded == null || !recorded.callOwned()) {
            return;
        }
        int bodyCell = eventIndex(events, bodyReturnCell, "SUCCESS");
        int cellStart = eventIndex(events, recorded.cell().opId(), "START");
        int cellSuccess = eventIndex(events, recorded.cell().opId(), "SUCCESS");
        int starts = 0;
        for (String event : events) {
            if (event.contains("|" + recorded.cell().opId().module().path() + "#"
                    + recorded.cell().opId().id() + "|START|BOUNDARY|")) {
                starts++;
            }
        }
        checkEq(1, starts, what + ": the recorded call-owned cell runs exactly once");
        check(bodyCell >= 0 && cellStart > bodyCell,
            what + ": the call-owned cell's START (" + cellStart + ") follows the "
                + "resolved body's own return cell (" + bodyCell + ")");
        check(cellSuccess > cellStart && callSuccess > cellSuccess,
            what + ": the call-owned cell's events (" + cellStart + ".." + cellSuccess
                + ") precede the invocation's SUCCESS terminal (" + callSuccess + ")");
    }

    /** The closed origin text of one op ({@code source:line:column}). */
    private static String originText(SemanticOp op) {
        deal.semantic.ir.SourceSpan span = op.origin().span();
        if (span == null) {
            return "-";
        }
        return op.origin().sourceId() + ":" + span.startLine() + ":"
            + span.startColumn();
    }

    // =========================================================================
    // 1. The trace-mode three-consumer drive
    // =========================================================================

    private static List<String> traceLines(SemanticRuntimeModel.ConsumerRun run) {
        List<String> lines = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            lines.add(event.text());
        }
        return lines;
    }

    private static void assertThreeConsumerTrace(String what, Drive drive,
            SemanticDifferentialHarness.Expectation expectation) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-dispatch-diff");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(drive.project(),
                    Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
                    expectation, workspace);
            checkEq(3, verdict.runs().size(), what
                + ": the harness produced the three consumers: " + verdict.failures());
            if (verdict.runs().size() != 3) {
                return;
            }
            List<String> oracleTrace = traceLines(verdict.runs().get(0));
            check(!oracleTrace.isEmpty(), what + ": the oracle produced events");
            for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                List<String> lines = traceLines(consumer);
                boolean equal = lines.equals(oracleTrace);
                if (!equal) {
                    for (int i = 0; i < Math.min(lines.size(), oracleTrace.size()); i++) {
                        if (!lines.get(i).equals(oracleTrace.get(i))) {
                            System.err.println("DIFF@" + i + " "
                                + consumer.consumer() + "\n  oracle: "
                                + oracleTrace.get(i) + "\n  other : " + lines.get(i));
                            break;
                        }
                    }
                }
                check(equal, what + ": the " + consumer.consumer()
                    + " trace equals the oracle's event-for-event (" + lines.size()
                    + " vs " + oracleTrace.size() + " events)");
            }
            check(verdict.pass(), what + ": the differential verdict passes: "
                + verdict.failures());
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 2. The production artifacts under the real toolchains
    // =========================================================================

    private record Outcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
    }

    private static String absoluteClasspath() {
        StringBuilder resolved = new StringBuilder();
        for (String entry : System.getProperty("java.class.path", "")
                .split(java.io.File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            if (resolved.length() > 0) {
                resolved.append(java.io.File.pathSeparator);
            }
            resolved.append(Path.of(entry).toAbsolutePath().normalize());
        }
        return resolved.toString();
    }

    private static Outcome runProcess(List<String> command, Path workDir)
            throws Exception {
        Path stderrFile = Files.createTempFile(workDir, "stderr", ".txt");
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new Outcome(exit, stdout, stderr);
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

    /** The LuaJIT production artifact of one drive, executed under real luajit. */
    private static void runLuaProduction(String what, Drive drive,
            String asyncEntryKey) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-dispatch-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                drive.project(), Map.of(MODULE, drive.table()),
                Map.of(MODULE, drive.registry()),
                new HostDeclarationSurface(Map.of())), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                local chunk = dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  if type(err) == "table" and err.__d then
                    print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                      .. tostring(err.o))
                  else
                    print("ERR:" .. tostring(err))
                  end
                  os.exit(0)
                end
                %s
                print("OK")
                """.formatted(artifact.toAbsolutePath().toString(),
                    asyncEntryKey == null ? ""
                        : "local v = __asyncEntries[\"" + asyncEntryKey
                            + "\"](\"-\", true)\nprint(\"VALUE:\" .. tostring(v))"),
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
            check(stdout.contains("OK"), what + " (luajit): the pinned drive "
                + "completes: " + stdout.replace("\n", "\\n"));
            check(!stdout.contains("ERR:"), what + " (luajit): no failure: "
                + stdout.replace("\n", "\\n"));
            if (asyncEntryKey != null) {
                check(stdout.contains("VALUE:42"), what + " (luajit): the dynamic "
                    + "async entry completes with the pinned value: "
                    + stdout.replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM production artifact of one drive, compiled and run by javac/java. */
    private static void runJvmProduction(String what, Drive drive, String exportName)
            throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-dispatch-jvm");
        try {
            String className = JvmBackend.classNameFor(drive.project().entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(drive.project(),
                    Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
                    className, new HostDeclarationSurface(Map.of()));
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            OpId asyncEntry = exportName == null ? null
                : asyncEntryOp(drive.unit(), exportName);
            String driveLine = asyncEntry == null ? ""
                : "      java.lang.Object value = " + className + ".ae"
                    + asyncEntry.id() + "(\"-\", true, new java.lang.Object[]{ });\n"
                    + "      System.out.println(\"VALUE:\" + value);\n";
            Files.writeString(workspace.resolve("DispatchProbe.java"), """
                final class DispatchProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin);
                      return;
                    }
                %s    System.out.println("OK");
                  }
                }
                """.formatted(className, driveLine), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                "DispatchProbe.java"), workspace);
            checkEq(0, javac.exitCode(), what + ": the JVM production artifact "
                + "compiles: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "DispatchProbe"),
                workspace);
            checkEq(0, run.exitCode(), what + " (java): the production artifact "
                + "executes: " + run.output());
            check(run.stdout().contains("OK"), what + " (java): the pinned drive "
                + "completes: " + run.stdout().replace("\n", "\\n"));
            check(!run.stdout().contains("ERR:"), what + " (java): no failure: "
                + run.stdout().replace("\n", "\\n"));
            if (asyncEntry != null) {
                check(run.stdout().contains("VALUE:42"), what + " (java): the dynamic "
                    + "async entry completes with the pinned value: "
                    + run.stdout().replace("\n", "\\n"));
            }
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The async EXTERNAL_ENTRY op of one export of the unit, or null. */
    private static OpId asyncEntryOp(LoweredModuleUnit unit, String exportName) {
        for (SemanticOp op : ofKind(unit, SemanticOpKind.EXTERNAL_ENTRY)) {
            KindPayload.ExternalEntryPayload payload =
                (KindPayload.ExternalEntryPayload) op.payload();
            if (payload.async() && payload.exportName().equals(exportName)) {
                return op.opId();
            }
        }
        return null;
    }

    // =========================================================================
    // 1. The closure-carrier drive
    // =========================================================================

    private static void testClosureCarrierDrive() throws Exception {
        System.out.println("-- the closure carrier: the parameter's DEAL closure "
            + "dispatches through the DEAL_BODY class on both targets --");
        Fixture fixture = fixture(CLOSURE_SOURCE, "closure drive");
        if (fixture == null) {
            return;
        }
        Drive drive = drive(fixture, 0, "closure drive");
        if (drive == null) {
            return;
        }
        // The runtime carrier's class is the closure's own identity: the
        // argument's registered LoweredBody binding. The callee value's
        // static registration stays the producer rule's dynamic record (the
        // value channel resolves the runtime class at execution).
        SemanticOp call = dynamicCall(drive.unit());
        FunctionExecutionBinding registration = carrierBinding(drive.unit(), 0);
        check(registration instanceof FunctionExecutionBinding.LoweredBody,
            "the argument's runtime carrier carries the closure's own "
                + "LoweredBody binding: " + registration);
        if (!(registration instanceof FunctionExecutionBinding.LoweredBody)) {
            return;
        }
        assertThreeConsumerTrace("closure carrier",
            drive, SemanticDifferentialHarness.Expectation.success(
                "closure carrier", List.of(), "null"));
        // The oracle's own trace: the callee body's FUNCTION_RETURN boundary runs
        // between the parameter cell and the caller's CALL terminal.
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
            drive.project(), Map.of(MODULE, drive.table()),
            Map.of(MODULE, drive.registry()), null);
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the closure drive completes in the oracle: " + run.comparisonReport());
        List<String> events = traceLines(run);
        // The callee body's own RETURN runs its single FUNCTION_RETURN cell
        // between the parameter cell and the caller's CALL terminal.
        FunctionId calleeFunction = ((FunctionExecutionBinding.LoweredBody) registration)
            .functionId();
        BlockId calleeBody = drive.unit().functions().get(calleeFunction).body();
        OpId calleeReturnCell = null;
        for (OpId member : drive.table().blockOps().get(calleeBody)) {
            SemanticOp op = opOf(drive.unit(), member);
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload returned) {
                calleeReturnCell = returned.returnBoundaryOpId();
            }
        }
        check(calleeReturnCell != null, "the callee body records its single "
            + "FUNCTION_RETURN cell: " + calleeReturnCell);
        int cellSuccess = -1;
        int callSuccess = -1;
        for (int i = 0; i < events.size(); i++) {
            if (calleeReturnCell != null && events.get(i).contains("|"
                    + calleeReturnCell.module().path() + "#" + calleeReturnCell.id()
                    + "|SUCCESS|BOUNDARY|")) {
                cellSuccess = i;
            }
            if (events.get(i).contains("|app#" + call.opId().id()
                    + "|SUCCESS|CALL|")) {
                callSuccess = i;
            }
        }
        check(cellSuccess >= 0 && callSuccess > cellSuccess,
            "the callee body's FUNCTION_RETURN cell SUCCESS (" + cellSuccess
                + ") precedes the caller's CALL SUCCESS (" + callSuccess + ")");
        // The recorded call-owned cell executes at the invocation site: the
        // runtime-resolved callee records the landed call-owned record, and
        // its events run after the body's own cell and before the CALL
        // terminal.
        assertCallOwnedCellRun("closure carrier", events, call.opId(), calleeReturnCell,
            recordedDealCell(drive.unit(), call), callSuccess);
        check(events.stream().anyMatch(event -> event.contains("|app#" + call.opId().id()
                + "|SUCCESS|CALL|") && event.endsWith("int:42")),
            "the dynamic CALL publishes the dispatched value");
        runLuaProduction("closure carrier", drive, null);
        runJvmProduction("closure carrier", drive, null);
    }

    // =========================================================================
    // 2. The adapter-carrier drive
    // =========================================================================

    private static void testAdapterCarrierDrive() throws Exception {
        System.out.println("-- the adapter carrier: the parameter's FUNCTION_ADAPT "
            + "value runs the D15 protocol on both targets --");
        Fixture fixture = fixture(ADAPTER_SOURCE, "adapter drive");
        if (fixture == null) {
            return;
        }
        Drive drive = drive(fixture, 0, "adapter drive");
        if (drive == null) {
            return;
        }
        SemanticOp call = dynamicCall(drive.unit());
        // The runtime carrier is the argument's FUNCTION_ADAPT value (the
        // callee value's static registration stays the producer rule's
        // dynamic record).
        FunctionExecutionBinding carrier = carrierBinding(drive.unit(), 0);
        check(carrier instanceof FunctionExecutionBinding.AdapterBinding,
            "the argument's runtime carrier carries the adapter's own "
                + "AdapterBinding: " + carrier);
        if (carrier instanceof FunctionExecutionBinding.AdapterBinding adapter) {
            checkEq(1, adapter.sourceSignature().paramTypes().size(),
                "the adapter's source arity is the leading-M projection width");
        }
        RecordedCell recorded = recordedDealCell(drive.unit(), call);
        check(recorded != null && recorded.callOwned(),
            "the runtime-resolved adapter callee records the call-owned DEAL-body "
                + "cell: " + recorded);
        assertThreeConsumerTrace("adapter carrier",
            drive, SemanticDifferentialHarness.Expectation.success(
                "adapter carrier", List.of(), "null"));
        // The recorded call-owned cell executes at the invocation site after
        // the adapter's DEAL-body source returned and before the CALL
        // terminal.
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
            drive.project(), Map.of(MODULE, drive.table()),
            Map.of(MODULE, drive.registry()), null);
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the adapter drive completes in the oracle: " + run.comparisonReport());
        List<String> events = traceLines(run);
        int callSuccessIndex = eventIndex(events, call.opId(), "SUCCESS");
        check(callSuccessIndex >= 0 && recorded != null && recorded.cell() != null
                && eventIndex(events, recorded.cell().opId(), "SUCCESS") > 0
                && eventIndex(events, recorded.cell().opId(), "SUCCESS")
                    < callSuccessIndex,
            "the recorded call-owned cell executes before the adapter call's "
                + "SUCCESS terminal");
        runLuaProduction("adapter carrier", drive, null);
        runJvmProduction("adapter carrier", drive, null);
    }

    // =========================================================================
    // 3. The dynamic async drive
    // =========================================================================

    private static void testDynamicAsyncDrive() throws Exception {
        System.out.println("-- the dynamic async start: the parameter's async callee "
            + "completes at the single AWAIT --");
        Fixture fixture = fixture(ASYNC_SOURCE, "dynamic async");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "dynamic async");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp start = dynamicAsyncStart(unit);
        check(start != null, "the awaited parameter callee lowers the dynamic "
            + "ASYNC_START shape");
        if (start == null) {
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.AsyncStartPayload) start.payload()).callee()).callee();
        // The callee value keeps the producer rule's dynamic record; the
        // runtime carrier of the awaited parameter is the `value` closure,
        // which the value channel resolves at execution.
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the awaited callee value carries the producer rule's dynamic "
                + "materialization record: " + registration);
        FunctionExecutionBinding carrier = null;
        for (FunctionExecutionBinding binding : unit.functionBindings().values()) {
            if (binding instanceof FunctionExecutionBinding.LoweredBody body
                    && unit.functions().get(body.functionId()) != null
                    && unit.functions().get(body.functionId()).descriptor().isAsync()) {
                carrier = binding;
                break;
            }
        }
        check(carrier != null, "the awaited argument's async body binding resolves: "
            + carrier);
        if (carrier == null) {
            return;
        }
        Drive drive = validateDrive(unit, raw, "dynamic async");
        if (drive == null) {
            return;
        }
        ExecutableLoweredProject project = drive.project();
        // The async-entry matrix: the oracle and both emitted dispatch entries.
        Path workspace = Files.createTempDirectory("dynamic-async-diff");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runAsyncEntry(project,
                    Map.of(MODULE, raw.table()), "probe", List.of(),
                    SemanticDifferentialHarness.Expectation.success(
                        "dynamic async", List.of(), "int:42"), workspace, null);
            checkEq(3, verdict.runs().size(), "the dynamic async drive produced the "
                + "three consumers: " + verdict.failures());
            if (verdict.runs().size() == 3) {
                List<String> oracleTrace = traceLines(verdict.runs().get(0));
                check(!oracleTrace.isEmpty(), "the oracle produced events for the "
                    + "dynamic async drive");
                for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                    checkEq(oracleTrace, traceLines(consumer),
                        "the " + consumer.consumer() + " async-entry trace equals "
                            + "the oracle's event-for-event");
                }
                check(verdict.pass(), "the dynamic async differential verdict "
                    + "passes: " + verdict.failures());
            }
        } finally {
            deleteRecursively(workspace);
        }
        OpId entry = asyncEntryOp(drive.unit(), "probe");
        check(entry != null, "the unit records the async EXTERNAL_ENTRY of the probe");
        runLuaProduction("dynamic async", drive, "app#probe");
        runJvmProduction("dynamic async", drive, "probe");
    }

    // =========================================================================
    // 3a. The dynamic async adapter drive
    // =========================================================================

    private static void testDynamicAsyncAdapterDrive() throws Exception {
        System.out.println("-- the dynamic async adapter: the awaited "
            + "FUNCTION_ADAPT value's D15 source class starts the source body task "
            + "on the oracle and both real toolchains --");
        Fixture fixture = fixture(ASYNC_ADAPTER_SOURCE, "dynamic async adapter");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "dynamic async adapter");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp start = dynamicAsyncStart(unit);
        check(start != null, "the awaited adapter callee lowers the dynamic "
            + "ASYNC_START shape");
        if (start == null) {
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.AsyncStartPayload) start.payload()).callee()).callee();
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the awaited callee value carries the producer rule's dynamic "
                + "materialization record: " + registration);
        FunctionExecutionBinding carrier = carrierBinding(unit, 0);
        check(carrier instanceof FunctionExecutionBinding.AdapterBinding,
            "the awaited argument's runtime carrier is the adapter's own "
                + "AdapterBinding: " + carrier);
        if (!(carrier instanceof FunctionExecutionBinding.AdapterBinding adapter)) {
            return;
        }
        checkEq(1, adapter.sourceSignature().paramTypes().size(),
            "the adapter's source arity is the leading-M projection width "
                + "(the dropped second argument proves the projection)");
        Drive drive = validateDrive(unit, raw, "dynamic async adapter");
        if (drive == null) {
            return;
        }
        // The async-entry matrix: the oracle and both emitted dispatch entries
        // agree event-for-event (the D15 source resolution, the source body
        // task under the source's module context, the source body's own
        // RETURN cell, and the single completion at the AWAIT).
        Path workspace = Files.createTempDirectory("dynamic-async-adapter-diff");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runAsyncEntry(drive.project(),
                    Map.of(MODULE, raw.table()), "probe", List.of(),
                    SemanticDifferentialHarness.Expectation.success(
                        "dynamic async adapter", List.of(), "int:42"), workspace, null);
            checkEq(3, verdict.runs().size(), "the dynamic async adapter drive "
                + "produced the three consumers: " + verdict.failures());
            if (verdict.runs().size() == 3) {
                List<String> oracleTrace = traceLines(verdict.runs().get(0));
                check(!oracleTrace.isEmpty(), "the oracle produced events for the "
                    + "dynamic async adapter drive");
                for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                    checkEq(oracleTrace, traceLines(consumer),
                        "the " + consumer.consumer() + " async-entry trace equals "
                            + "the oracle's event-for-event");
                }
                check(verdict.pass(), "the dynamic async adapter differential "
                    + "verdict passes: " + verdict.failures());
            }
        } finally {
            deleteRecursively(workspace);
        }
        runLuaProduction("dynamic async adapter", drive, "app#probe");
        runJvmProduction("dynamic async adapter", drive, "probe");
    }

    // =========================================================================
    // 3c. The callee-owned cell drive
    // =========================================================================

    /**
     * The callee-owned form fixture: an in-place function-expression callee
     * (a same-walk body) invoked immediately.
     */
    private static final String IIFE_SOURCE = """
        export function main(): null {
          let r: int = (function(x: int): int { return x * 2 })(21)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "iife" }
          }
          return null
        }
        """;

    /** The awaited in-place function-expression callee. */
    private static final String IIFE_ASYNC_SOURCE = """
        export async function probe(): int {
          return await (async function(): int { return 42 })()
        }

        export function main(): null {
          return null
        }
        """;

    /**
     * The callee-owned form drive (ISSUE-0677; design source M6): a
     * statically identified same-walk body records that body's own
     * RETURN-materialized cell, which the body's own {@code RETURN} executes
     * exactly once per invocation — sync and async — on the oracle and both
     * real toolchains.
     */
    private static void testCalleeOwnedCellDrive() throws Exception {
        System.out.println("-- the callee-owned cell: a same-walk body records its own "
            + "RETURN cell, executed exactly once by that RETURN --");
        Fixture fixture = fixture(IIFE_SOURCE, "iife drive");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "iife drive");
        if (raw == null) {
            return;
        }
        Drive drive = validateDrive(raw.unit(), raw, "iife drive");
        if (drive == null) {
            return;
        }
        SemanticOp call = dynamicCall(drive.unit());
        ValueId calleeValue = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        FunctionExecutionBinding registration = drive.unit().functionBindings().get(
            new FunctionAllocationIdentity(calleeValue.id()));
        check(registration instanceof FunctionExecutionBinding.LoweredBody,
            "the same-walk body callee keeps its LoweredBody registration: "
                + registration);
        RecordedCell recorded = recordedDealCell(drive.unit(), call);
        check(recorded != null && !recorded.callOwned(),
            "the same-walk body callee records the callee-owned cell: " + recorded);
        if (recorded == null || recorded.callOwned()) {
            return;
        }
        SemanticOp bodyReturn = recorded.parent();
        assertThreeConsumerTrace("iife drive", drive,
            SemanticDifferentialHarness.Expectation.success("iife drive", List.of(),
                "null"));
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
            drive.project(), Map.of(MODULE, drive.table()),
            Map.of(MODULE, drive.registry()), null);
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
            "the iife drive completes in the oracle: " + run.comparisonReport());
        List<String> events = traceLines(run);
        int starts = 0;
        for (String event : events) {
            if (event.contains("|" + recorded.cell().opId().module().path() + "#"
                    + recorded.cell().opId().id() + "|START|BOUNDARY|")) {
                starts++;
            }
        }
        checkEq(1, starts, "the callee-owned cell runs exactly once per invocation");
        int returnStart = eventIndex(events, bodyReturn.opId(), "START");
        int cellStart = eventIndex(events, recorded.cell().opId(), "START");
        int cellSuccess = eventIndex(events, recorded.cell().opId(), "SUCCESS");
        int callSuccess = eventIndex(events, call.opId(), "SUCCESS");
        check(returnStart >= 0 && cellStart > returnStart && cellSuccess > cellStart
                && callSuccess > cellSuccess,
            "the cell's single event pair runs inside the body's RETURN (" + returnStart
                + " < " + cellStart + " < " + cellSuccess + " < " + callSuccess + ")");
        runLuaProduction("iife drive", drive, null);
        runJvmProduction("iife drive", drive, null);

        // The async twin: the recorded task cell is the same-walk body's own
        // cell, executed by that body's RETURN inside the task.
        Fixture asyncFixture = fixture(IIFE_ASYNC_SOURCE, "iife async drive");
        if (asyncFixture == null) {
            return;
        }
        RawLowering asyncRaw = rawLower(asyncFixture, "iife async drive");
        if (asyncRaw == null) {
            return;
        }
        Drive asyncDrive = validateDrive(asyncRaw.unit(), asyncRaw, "iife async drive");
        if (asyncDrive == null) {
            return;
        }
        SemanticOp start = dynamicAsyncStart(asyncDrive.unit());
        RecordedCell taskCell = recordedDealCell(asyncDrive.unit(), start);
        check(taskCell != null && !taskCell.callOwned(),
            "the awaited same-walk body records the callee-owned task cell: " + taskCell);
        if (taskCell == null || taskCell.callOwned()) {
            return;
        }
        Path workspace = Files.createTempDirectory("dynamic-iife-diff");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runAsyncEntry(asyncDrive.project(),
                    Map.of(MODULE, asyncRaw.table()), "probe", List.of(),
                    SemanticDifferentialHarness.Expectation.success("iife async drive",
                        List.of(), "int:42"), workspace, null);
            checkEq(3, verdict.runs().size(), "the iife async drive produced the three "
                + "consumers: " + verdict.failures());
            if (verdict.runs().size() == 3) {
                List<String> oracleTrace = traceLines(verdict.runs().get(0));
                for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                    checkEq(oracleTrace, traceLines(consumer), "the "
                        + consumer.consumer() + " async-entry trace equals the "
                        + "oracle's event-for-event");
                    int asyncStarts = 0;
                    for (String event : traceLines(consumer)) {
                        if (event.contains("|" + taskCell.cell().opId().module().path()
                                + "#" + taskCell.cell().opId().id()
                                + "|START|BOUNDARY|")) {
                            asyncStarts++;
                        }
                    }
                    checkEq(1, asyncStarts, "the " + consumer.consumer()
                        + " runs the callee-owned task cell exactly once");
                }
                check(verdict.pass(), "the iife async differential verdict passes: "
                    + verdict.failures());
            }
        } finally {
            deleteRecursively(workspace);
        }
        runLuaProduction("iife async drive", asyncDrive, "app#probe");
        runJvmProduction("iife async drive", asyncDrive, "probe");
    }

    // =========================================================================
    // 3b. The composed drive (T2/T3/T5/T6/T8)
    // =========================================================================

    /** The composed host module's declaration (a sync and an async export). */
    private static final String COMPOSED_HOST_DECLARATION = """
        export function add(a: int, b: int): int;
        export async function fetchValue(): string;
        """;

    /** The composed compiled module (a sync and an async export). */
    private static final String COMPOSED_LIB_SOURCE = """
        export function mul(a: int, b: int): int {
          return a * b
        }

        export async function fetch(): int {
          return 40
        }
        """;

    /**
     * The composed entry module: the sync host call, the cross-module sync
     * call, the dynamic dispatch (the gate-clean closure-carrier callee
     * form), and (in the async export) the async host call and the
     * cross-module async call.
     */
    private static final String COMPOSED_APP_SOURCE = """
        import * as host from "host/composed_abi"
        import * as lib from "./lib"

        export async function probe(): int {
          let h: string = await host.fetchValue()
          let v: int = await lib.fetch()
          if (h !== "host" || v !== 40) {
            throw { code: "TEST_FAIL", message: "composed async" }
          }
          return 42
        }

        export function main(): null {
          let a: int = host.add(19, 23)
          let b: int = lib.mul(6, 7)
          let c: int = (function(x: int): int { return x * 2 })(21)
          if (a !== 42 || b !== 42 || c !== 42) {
            throw { code: "TEST_FAIL", message: "composed" }
          }
          return null
        }
        """;

    /** The composed host's LuaJIT implementation. */
    private static final String COMPOSED_HOST_LUA = """
        local rt = require("deal.runtime")

        return {
          add = function(a, b) return a + b end,
          fetchValue = function()
            return rt.async_start(function() return "host" end)
          end,
        }
        """;

    /** The composed host's JVM implementation (the deployed class name). */
    private static String composedHostJava(String hostClass) {
        return """
            import java.util.concurrent.CompletableFuture;

            public final class %s {
              public static Object add(int a, int b) {
                return Integer.valueOf(a + b);
              }

              public static Object fetchValue() {
                return CompletableFuture.completedFuture("host");
              }
            }
            """.formatted(hostClass);
    }

    /** One compiled composed project: its modules, surface, and compile facts. */
    private record ComposedFixture(Path root, Path src,
                                   CheckedProjectInput checkedProject,
                                   ProjectInterfaceIndex index,
                                   List<SemanticRequirementManifest> manifests,
                                   HostDeclarationSurface surface,
                                   Map<ModuleId, CanonicalModuleIdentity> identities) {
    }

    private static ComposedFixture compileComposed() throws Exception {
        Path root = Files.createTempDirectory("dynamic-composed");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(root.resolve("src/composed_abi.d.deal"),
            COMPOSED_HOST_DECLARATION, StandardCharsets.UTF_8);
        Files.writeString(root.resolve("src/lib.deal"), COMPOSED_LIB_SOURCE,
            StandardCharsets.UTF_8);
        Files.writeString(root.resolve("src/app.deal"), COMPOSED_APP_SOURCE,
            StandardCharsets.UTF_8);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put("host/composed_abi",
            root.resolve("src/composed_abi.d.deal").toAbsolutePath().toString());
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, deal.codegen.Backend.LUAJIT, externals,
            List.of(src.toAbsolutePath()), null, null,
            deal.test.ConformanceHarnessMetadata.invocation(
                SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        check(compiled && built != null && !built.hasErrors() && built.input() != null
                && built.index() != null && manifests != null
                && orchestrator.hostDeclarationSurface() != null,
            "the composed project compiles through the orchestrator: "
                + orchestrator.diagnostics());
        if (!compiled || built == null || built.input() == null || built.index() == null
                || manifests == null || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : orchestrator.hostDeclarationSurface()
                .moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule("host/composed_abi"));
        }
        return new ComposedFixture(root, src, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(), identities);
    }

    private static void testComposedDrive() throws Exception {
        System.out.println("-- the composed drive: the host load with its sync and async "
            + "exports, the compiled module's sync and async exports, and the dynamic "
            + "dispatch in one project on both targets --");
        ComposedFixture fixture = compileComposed();
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = SemanticLowerer.lowerProject(
                CompilerProfileProvider.resolve(
                    deal.semantic.ReleaseConfiguration.CURRENT_RELEASE_STATE,
                    deal.semantic.ReleaseConfiguration.releaseCapabilityRegistry()),
                fixture.checkedProject(), fixture.index(), fixture.manifests(),
                fixture.surface(), fixture.identities(), Map.of(),
                BuiltinErrorDeclaration.synthesized(
                    fixture.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                Set.of());
            check(result.project() != null, "the composed project lowers through the one "
                + "project entry: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId app = project.entryModule();
            ModuleId lib = new ModuleId("lib");
            check(project.modules().containsKey(lib),
                "the composed closure carries the compiled module");
            check(dynamicCall(project.modules().get(app)) != null,
                "the composed project carries the dynamic dispatch");
            // The oracle: the sync composition through the host seam, then the
            // async entry with the async host operation and the cross-module
            // async call.
            SemanticOracle.HostResponder responder = composedResponder();
            SemanticRuntimeModel.ConsumerRun mainRun =
                SemanticOracle.executeProjectInits(project, result.tables(),
                    result.registries(), responder);
            check(mainRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the composed sync drive completes in the oracle: "
                    + mainRun.comparisonReport());
            SemanticRuntimeModel.ConsumerRun asyncRun = SemanticOracle.invokeAsyncEntry(
                project, result.tables(), responder, app, "probe", List.of());
            check(asyncRun.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the composed async entry completes in the oracle: "
                    + asyncRun.comparisonReport());
            // The production artifacts: the deployed host implementation, the
            // real luajit and javac/java toolchains, and the pinned result.
            runComposedLua(fixture, project, result.tables(), result.registries());
            runComposedJvm(fixture, project, result.tables(), result.registries());
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The composed drive's scripted host seam (the oracle side). */
    private static SemanticOracle.HostResponder composedResponder() {
        return new SemanticOracle.HostResponder() {
            @Override
            public SyncOutcome call(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
                if ("host.composed_abi".equals(module.path()) && "add".equals(export)) {
                    return new SyncOutcome.Returned(
                        new SemanticOracle.Value.IntValue(42L));
                }
                throw new IllegalStateException("the composed responder scripts no sync "
                    + "host call for " + module.path() + "." + export);
            }

            @Override
            public String startAsync(ModuleId module, String export,
                    RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args, String operationLabel) {
                return "host.composed_abi.fetchValue".equals(module.path() + "." + export)
                    ? operationLabel : null;
            }

            @Override
            public SyncOutcome completeAsync(String operationLabel) {
                return new SyncOutcome.Returned(
                    new SemanticOracle.Value.StrValue("host"));
            }
        };
    }

    private static void runComposedLua(ComposedFixture fixture,
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-composed-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(project,
                tables, registries, fixture.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path host = workspace.resolve("host/composed_abi.lua");
            Files.createDirectories(host.getParent());
            Files.writeString(host, COMPOSED_HOST_LUA, StandardCharsets.UTF_8);
            Path probe = workspace.resolve("probe.lua");
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            check(entry != null, "the composed project records the async probe entry");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if not ok then
                  print("ERR:" .. tostring(err)) os.exit(0)
                end
                local v = __asyncEntries["%s#probe"]("-", true)
                print("OK VALUE:" .. tostring(v))
                """.formatted(artifact.toAbsolutePath().toString(),
                    project.entryModule().path()), StandardCharsets.UTF_8);
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
            checkEq(0, exit, "the composed production chunk executes under luajit: "
                + stdout + stderr);
            check(stdout.contains("OK VALUE:42"), "the composed luajit drive completes "
                + "with the pinned result (the host load, the sync/async host arms, "
                + "the cross-module sync/async realizations, and the dynamic "
                + "dispatch all execute): " + stdout.replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void runComposedJvm(ComposedFixture fixture,
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-composed-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            String hostClass = JvmBackend.classNameFor("host/composed_abi");
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                    className, fixture.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(hostClass + ".java"),
                composedHostJava(hostClass), StandardCharsets.UTF_8);
            OpId entry = asyncEntryOp(project.modules().get(project.entryModule()),
                "probe");
            check(entry != null, "the composed project records the async probe entry "
                + "for the JVM drive");
            Files.writeString(workspace.resolve("ComposedProbe.java"), """
                final class ComposedProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg);
                      return;
                    }
                    try {
                      java.lang.Object value = %s.ae%s("-", true,
                          new java.lang.Object[]{ });
                      System.out.println("OK VALUE:" + value);
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg);
                    }
                  }
                }
                """.formatted(className, className, entry.id()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                hostClass + ".java", "ComposedProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the composed production artifact compiles "
                + "with the deployed host implementation: " + javac.output());
            if (javac.exitCode() != 0) {
                return;
            }
            Outcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "ComposedProbe"),
                workspace);
            checkEq(0, run.exitCode(), "the composed production artifact executes "
                + "under java: " + run.output());
            check(run.stdout().contains("OK VALUE:42"), "the composed java drive "
                + "completes with the pinned result: "
                + run.stdout().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 4. The emitted dispatch surface
    // =========================================================================

    private static void testEmittedSurface() throws Exception {
        System.out.println("-- the emitted dispatch surface: the class tags, the "
            + "function-id to owning-module resolution, and the factory triple --");
        Fixture fixture = fixture(CLOSURE_SOURCE, "closure drive");
        if (fixture == null) {
            return;
        }
        Drive drive = drive(fixture, 0, "closure drive");
        if (drive == null) {
            return;
        }
        String lua = LuaSemanticEmitter.emitProductionProject(drive.project(),
            Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
            new HostDeclarationSurface(Map.of()));
        String jvm = JvmSemanticEmitter.emitProductionProject(drive.project(),
            Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
            JvmBackend.classNameFor(drive.project().entryModule().path()),
            new HostDeclarationSurface(Map.of())).source();
        // The function-id to owning-module resolution: one row per function,
        // built by the same walk that declares the function factories.
        check(lua.contains("__fnModules = __fnModules or {}\n"),
            "the LuaJIT chunk declares the chunk-global resolution table");
        check(jvm.contains("static String dealModuleOfFunction(String fid)"),
            "the JVM artifact carries the generated function-id lookup");
        for (Map.Entry<deal.semantic.ir.FunctionId, deal.semantic.ir.LoweredFunction> entry
                : drive.unit().functions().entrySet()) {
            long fid = entry.getKey().id();
            check(lua.contains("__fnModules[" + fid + "] = \"app\""),
                "the LuaJIT resolution table maps function " + fid + " to its module");
            check(jvm.contains("if (\"" + fid + "\".equals(fid)) return \"app\";"),
                "the JVM lookup maps function " + fid + " to its module");
        }
        // The class dispatch.
        check(lua.contains("__dynK = __dynClass(__dynC)"), "the LuaJIT arm reads the "
            + "carrier's own class tag");
        check(lua.contains("if __dynK == \"DEAL_BODY\" then")
                && lua.contains("elseif __dynK == \"ADAPTER\" then")
                && lua.contains("elseif __dynK == \"HOST\" then"),
            "the LuaJIT arm dispatches over the closed class set");
        check(lua.contains("__module = __dynM"), "the DEAL_BODY path switches the "
            + "module context to the resolved callee module");
        check(lua.contains("table.insert(__frames, 1, tostring(__dynC.__fid))"),
            "the DEAL_BODY path pushes the callee frame");
        check(lua.contains("__okT, __resT = pcall(__unfn(__dynC)"),
            "the DEAL_BODY path invokes the carrier's own invoker");
        check(lua.contains("__adaptSource(__dynC)")
                && lua.contains("pcall(__fncheck, __dynS, __dynC.__csrc,"),
            "the adapter path runs the landed D15 source resolution and check");
        check(lua.contains("unpack(__dynA, 1, __dynC.__m)"),
            "the adapter path projects the leading M arguments");
        check(lua.contains("__hostProjectArg(") && lua.contains("__hostReturnCell,"),
            "the HOST row invokes the loaded surface entry through the host calling "
                + "convention and runs the recorded HOST_TO_DEAL + HOST_SYNC_RETURN cell");
        check(lua.contains("expected function, got ")
                && lua.contains("__actualOf(\"function\", __dynC)"),
            "the residue projects the pinned E8001 expected/actual text");
        check(jvm.contains("instanceof JvmRuntime.AdapterValue")
                && jvm.contains("instanceof JvmRuntime.FunctionValue")
                && jvm.contains(".fid != null"),
            "the JVM arm reads the carrier's own class tag");
        check(jvm.contains("dealModuleOfFunction(") && jvm.contains("MODULE = __fm"),
            "the JVM DEAL_BODY path resolves the callee module through the lookup "
                + "and switches the module context");
        check(jvm.contains("JvmRuntime.pushFrame("), "the JVM DEAL_BODY path pushes "
            + "the callee frame");
        check(jvm.contains("JvmRuntime.fail(\"E8001\", \"expected function, got \""),
            "the JVM residue projects the pinned E8001 expected/actual text");
        check(jvm.contains("JvmRuntime.fnCheck(JvmRuntime.adapterSource(")
                && jvm.contains("java.util.Arrays.copyOfRange("),
            "the JVM adapter path runs the landed D15 sequence with the leading-M "
                + "projection");
        // The production factories carry the descriptor text, the canonical spec
        // text, and the function identity (the class tag the dispatch reads).
        // The drive's callee value keeps the producer rule's dynamic record, so
        // the runtime carrier's own registration names the dispatched body.
        SemanticOp call = dynamicCall(drive.unit());
        FunctionExecutionBinding closureRegistration = carrierBinding(drive.unit(), 0);
        if (closureRegistration instanceof FunctionExecutionBinding.LoweredBody body) {
            deal.semantic.ir.LoweredFunction function =
                drive.unit().functions().get(body.functionId());
            String triple = ", \"" + descriptorText(function.descriptor()) + "\", \""
                + function.descriptor().canonicalSpecText() + "\", \""
                + function.functionId().id() + "\");";
            check(jvm.contains(triple), "the JVM factory of function "
                + function.functionId().id() + " carries the descriptor text, the "
                + "canonical spec text, and the function identity: " + triple);
            check(lua.contains("__fid = " + function.functionId().id() + "}"),
                "the LuaJIT closure carrier of function " + function.functionId().id()
                    + " carries its function identity");
        }
        // The adapter value keeps fid = null (an adapter is not a DEAL body; its
        // D15 source resolution reads the source value's own tag).
        check(JvmRuntimeAdapterPinsNull(), "the landed AdapterValue pins fid = null: "
            + "an adapter is not a DEAL body");
    }

    /**
     * The dynamic async start's emitted dispatch surface (ISSUE-0658 review
     * cycle 1 finding 1): the DEAL_BODY class starts the callee body task and
     * the ADAPTER class runs the D15 sequence and starts the source class's
     * task with the leading-M projection; every other class residues.
     */
    private static void testEmittedAsyncDispatchSurface() throws Exception {
        System.out.println("-- the emitted async dispatch surface: the DEAL_BODY "
            + "and ADAPTER class branches and the fail-closed residue --");
        Fixture fixture = fixture(ASYNC_ADAPTER_SOURCE, "dynamic async adapter");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "dynamic async adapter");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp start = dynamicAsyncStart(unit);
        if (start == null) {
            fail("the async dispatch surface drive carries the dynamic ASYNC_START");
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.AsyncStartPayload) start.payload()).callee()).callee();
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the async dispatch surface drive's callee value carries the producer "
                + "rule's dynamic materialization record: " + registration);
        FunctionExecutionBinding carrier = carrierBinding(unit, 0);
        if (carrier == null) {
            fail("the async dispatch surface drive resolves the adapter carrier");
            return;
        }
        Drive drive = validateDrive(unit, raw, "dynamic async dispatch surface");
        if (drive == null) {
            return;
        }
        String lua = LuaSemanticEmitter.emitProductionProject(drive.project(),
            Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
            new HostDeclarationSurface(Map.of()));
        String jvm = JvmSemanticEmitter.emitProductionProject(drive.project(),
            Map.of(MODULE, drive.table()), Map.of(MODULE, drive.registry()),
            JvmBackend.classNameFor(drive.project().entryModule().path()),
            new HostDeclarationSurface(Map.of())).source();
        check(lua.contains("if __dynK == \"DEAL_BODY\" then")
                && lua.contains("elseif __dynK == \"ADAPTER\" then")
                && lua.contains("__adaptSource(__dynC)")
                && lua.contains("pcall(__fncheck, __dynS, __dynC.__csrc,"),
            "the LuaJIT async arm dispatches the DEAL_BODY and ADAPTER classes "
                + "through the landed D15 sequence");
        check(lua.contains("unpack(S.__sa")
                && lua.contains(", 1, __dynC.__m)"),
            "the LuaJIT async adapter path projects the leading-M recorded "
                + "arguments (zero caller-side return boundaries)");
        check(lua.contains("  end), S.__sa"),
            "the LuaJIT async arm starts the class task with the recorded argument "
                + "carrier");
        check(jvm.contains("if (__dc" + start.opId().id()
                + " instanceof JvmRuntime.AdapterValue)"),
            "the JVM async arm reads the carrier's own class tag");
        check(jvm.contains("JvmRuntime.fnCheck(JvmRuntime.adapterSource(")
                && jvm.contains(".sourceSpec, ")
                && jvm.contains("java.util.Arrays.copyOfRange(new Object[]{ ")
                && jvm.contains(".arity));"),
            "the JVM async adapter path runs the landed D15 sequence with the "
                + "leading-M projection");
        check(jvm.contains("dealModuleOfFunction(((JvmRuntime.FunctionValue) ")
                && jvm.contains("instanceof JvmRuntime.FunctionValue ")
                && jvm.contains(".fid != null"),
            "the JVM async arm resolves the source's owning module through the "
                + "emitted lookup");
        check(lua.contains("else\n") && lua.contains("__dynE = __failExpr(\"E8001\"")
                && jvm.contains("JvmRuntime.fail(\"E8001\", \"expected function, "
                    + "got \""),
            "every other carrier class residues with the pinned E8001 text");
    }

    /** Whether the runtime's adapter carrier pins the null function id. */
    private static boolean JvmRuntimeAdapterPinsNull() throws Exception {
        String source = Files.readString(
            Path.of("deal", "codegen", "jvm", "JvmRuntime.java"), StandardCharsets.UTF_8);
        return source.contains("super(fn, signature, spec, null);");
    }

    /**
     * The canonical contract snapshot of one hand-built op (the closed
     * digest the validator and the emitters recompute).
     */
    private static deal.semantic.ir.OperationContractSnapshot contractOf(
            SemanticOpKind kind, KindPayload payload,
            deal.semantic.ir.OpResultType resultType, FailurePolicyId policy) {
        deal.semantic.ir.ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying
                ? carrying.selector() : null;
        deal.semantic.ir.OperationContractSnapshot draft =
            new deal.semantic.ir.OperationContractSnapshot(
                deal.semantic.ir.OperationContractSnapshot.VERSION, kind, resultType,
                List.of(), selector, payload, policy, List.of(), "placeholder");
        String digest = deal.semantic.ir.ContractSnapshotCanonicalizer.digest(draft);
        return new deal.semantic.ir.OperationContractSnapshot(
            deal.semantic.ir.OperationContractSnapshot.VERSION, kind, resultType,
            List.of(), selector, payload, policy, List.of(), digest);
    }

    /** The JVM runtime descriptor text (the factory's carried signature text). */
    private static String descriptorText(RuntimeDescriptor descriptor) {
        if (descriptor instanceof RuntimeDescriptor.Null) {
            return "null";
        }
        if (descriptor instanceof RuntimeDescriptor.Boolean) {
            return "boolean";
        }
        if (descriptor instanceof RuntimeDescriptor.Int) {
            return "int";
        }
        if (descriptor instanceof RuntimeDescriptor.Number) {
            return "number";
        }
        if (descriptor instanceof RuntimeDescriptor.String) {
            return "string";
        }
        if (descriptor instanceof RuntimeDescriptor.Table) {
            return "table";
        }
        if (descriptor instanceof RuntimeDescriptor.Class cls) {
            return cls.classId().text();
        }
        if (descriptor instanceof RuntimeDescriptor.Array array) {
            return "array(" + descriptorText(array.element()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Nullable nullable) {
            return "nullable(" + descriptorText(nullable.inner()) + ")";
        }
        if (descriptor instanceof RuntimeDescriptor.Func func) {
            StringBuilder params = new StringBuilder();
            for (RuntimeDescriptor param : func.paramTypes()) {
                if (params.length() > 0) {
                    params.append(',');
                }
                params.append(descriptorText(param));
            }
            return "function(" + params + ";" + descriptorText(func.returnType())
                + ")";
        }
        return "unknown";
    }

    // =========================================================================
    // 5. The fail-closed drive
    // =========================================================================

    private static void testFailClosedResidue() throws Exception {
        System.out.println("-- the fail-closed residue: a carrier that is not a "
            + "function value projects the pinned E8001 at the call origin --");
        Fixture fixture = fixture(CLOSURE_SOURCE, "closure drive");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "residue drive");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        if (call == null) {
            fail("the residue drive unit carries the dynamic CALL");
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        // The carrier read is replaced by a CONST of a string result under the
        // same op identity: the produced unit carries the identical shape, and
        // the runtime value the dispatch reads is not a function carrier.
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId value && value.equals(callee)) {
                KindPayload payload = new KindPayload.ConstPayload(
                    new deal.semantic.ir.ScalarValue.String("carrier"));
                ops.add(new SemanticOp(op.opId(), SemanticOpKind.CONST, op.origin(),
                    op.result(), RuntimeDescriptor.String.INSTANCE, List.of(), List.of(),
                    payload, FailurePolicyId.NO_DEAL_FAILURE,
                    contractOf(SemanticOpKind.CONST, payload,
                        RuntimeDescriptor.String.INSTANCE,
                        FailurePolicyId.NO_DEAL_FAILURE)));
            } else {
                ops.add(op);
            }
        }
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.remove(new FunctionAllocationIdentity(callee.id()));
        LoweredModuleUnit doctored = new LoweredModuleUnit(unit.formatVersion(),
            unit.semanticProfile(), unit.moduleId(), unit.interfaceHash(),
            unit.loweringContextHash(), unit.requiredCapabilities(),
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), bindings, ops);
        ExecutableLoweredProject project = projectOf(doctored);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), "the closed gate accepts the residue drive: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return;
        }
        Drive drive = new Drive(doctored, raw.table(), project,
            new ClassFactoryRegistry(Map.of()));
        // The oracle fails closed: the carrier resolves no execution binding.
        String oracleFailure = null;
        try {
            SemanticOracle.executeProjectInits(project, Map.of(MODULE, raw.table()),
                Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        } catch (RuntimeException rejected) {
            oracleFailure = rejected.getClass().getSimpleName() + ": "
                + rejected.getMessage();
        }
        check(oracleFailure != null && oracleFailure.contains("FunctionExecutionBinding"),
            "the oracle fails closed on the unresolvable carrier: " + oracleFailure);
        // The artifacts project the pinned E8001 at the call origin.
        assertResidueRun("luajit", luaResidue(project, raw.table()), "E8001",
            "expected function, got string");
        assertResidueRun("java", jvmResidue(project, raw.table()), "E8001",
            "expected function, got string");
    }

    private static Outcome luaResidue(ExecutableLoweredProject project,
            StructuredBodyTable table) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-residue-lua");
        try {
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, Map.of(MODULE, table),
                Map.of(MODULE, new ClassFactoryRegistry(Map.of())),
                new HostDeclarationSurface(Map.of())), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, """
                dofile("%s")
                local ok, err = __dealMain()
                if ok then print("OK") os.exit(0) end
                if type(err) == "table" and err.__d then
                  print("ERR:" .. err.code .. "|" .. tostring(err.m) .. "|"
                    .. tostring(err.o) .. "|" .. tostring(err.e or "-") .. "|"
                    .. tostring(err.a or "-"))
                else
                  print("ERR:" .. tostring(err))
                end
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
            return new Outcome(exit, stdout, stderr);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static Outcome jvmResidue(ExecutableLoweredProject project,
            StructuredBodyTable table) throws Exception {
        Path workspace = Files.createTempDirectory("dynamic-residue-jvm");
        try {
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, Map.of(MODULE, table),
                    Map.of(MODULE, new ClassFactoryRegistry(Map.of())), className,
                    new HostDeclarationSurface(Map.of()));
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("ResidueProbe.java"), """
                final class ResidueProbe {
                  public static void main(String[] args) {
                    try {
                      %s.dealMain();
                      System.out.println("OK");
                    } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                      System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                          + error.origin + "|" + error.expected + "|" + error.actual);
                    }
                  }
                }
                """.formatted(className), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javac = runProcess(List.of("javac", "--release", "25", "-proc:none",
                "-cp", classpath, "-d", classes.toString(), className + ".java",
                "ResidueProbe.java"), workspace);
            checkEq(0, javac.exitCode(), "the residue JVM artifact compiles: "
                + javac.output());
            if (javac.exitCode() != 0) {
                return javac;
            }
            return runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "ResidueProbe"),
                workspace);
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static void assertResidueRun(String target, Outcome outcome, String code,
            String text) {
        checkEq(0, outcome.exitCode(), "the residue drive (" + target
            + ") exits cleanly: " + outcome.output());
        check(outcome.stdout().startsWith("ERR:" + code + "|") && outcome.stdout()
                .contains(text),
            "the residue drive (" + target + ") projects the pinned " + code + " "
                + "text at the call origin: " + outcome.stdout().replace("\n", "\\n"));
    }

    // =========================================================================
    // 5b. The adapter source-signature fault
    // =========================================================================

    private static void testAdapterSourceSignatureFault() throws Exception {
        System.out.println("-- the adapter source-signature fault: a carried source spec "
            + "that differs from the recorded source signature fails E8010 at the "
            + "call origin --");
        Fixture fixture = fixture(ADAPTER_SOURCE, "adapter fault");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "adapter fault");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp adapt = ofKind(unit, SemanticOpKind.FUNCTION_ADAPT).isEmpty()
            ? null : ofKind(unit, SemanticOpKind.FUNCTION_ADAPT).get(0);
        SemanticOp call = dynamicCall(unit);
        if (adapt == null || call == null) {
            fail("the adapter fault drive carries its FUNCTION_ADAPT and dynamic CALL");
            return;
        }
        KindPayload.FunctionAdaptPayload payload =
            (KindPayload.FunctionAdaptPayload) adapt.payload();
        // The recorded source signature is retargeted to the target signature: the
        // source value's own carried spec no longer equals it.
        KindPayload.FunctionAdaptPayload retargeted = new KindPayload.FunctionAdaptPayload(
            payload.targetSignature(), payload.targetSignature(), payload.mode(),
            payload.source(), payload.proof());
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(adapt.opId())) {
                ops.add(new SemanticOp(op.opId(), op.kind(), op.origin(), op.result(),
                    op.resultType(), op.operands(), op.operandTypes(), retargeted,
                    op.failurePolicy(), reContract(op, retargeted)));
            } else {
                ops.add(op);
            }
        }
        ValueId adaptValue = (ValueId) adapt.result();
        FunctionExecutionBinding.AdapterBinding original =
            (FunctionExecutionBinding.AdapterBinding) unit.functionBindings().get(
                new FunctionAllocationIdentity(adaptValue.id()));
        FunctionExecutionBinding.AdapterBinding rewired =
            new FunctionExecutionBinding.AdapterBinding(original.adaptOpId(),
                original.captureMode(), original.sourceRef(), payload.targetSignature(),
                original.targetSignature());
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the adapter fault drive's callee value carries the producer rule's "
                + "dynamic materialization record: " + registration);
        // The adapter's runtime carrier keeps the producer rule's dynamic
        // callee record: the doctored FUNCTION_ADAPT payload (and its own
        // AdapterBinding) carry the mismatched source signature the D15 check
        // reads from the runtime carrier.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        bindings.put(new FunctionAllocationIdentity(adaptValue.id()), rewired);
        LoweredModuleUnit doctored = new LoweredModuleUnit(unit.formatVersion(),
            unit.semanticProfile(), unit.moduleId(), unit.interfaceHash(),
            unit.loweringContextHash(), unit.requiredCapabilities(),
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), bindings, ops);
        ExecutableLoweredProject project = projectOf(doctored);
        java.util.Optional<deal.diagnostics.CompilerDiagnostic> gate =
            deal.semantic.ir.SemanticIrValidator.validate(project,
                new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                    doctored.interfaceHash(), SemanticProfile.DEAL_V1_2_INT32,
                    REGISTRY_HASH));
        check(gate.isEmpty(), "the closed gate accepts the adapter fault drive: "
            + gate.map(deal.diagnostics.CompilerDiagnostic::message).orElse(""));
        if (gate.isPresent()) {
            return;
        }
        // The oracle: E8010 at the dynamic call's origin (the D15 source check).
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.executeProjectInits(
            project, Map.of(MODULE, raw.table()),
            Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                && "E8010".equals(failure.error().code()),
            "the oracle projects E8010 for the mismatched carried source signature: "
                + run.comparisonReport());
        // The artifacts: the same pinned projection at the call origin.
        assertResidueRun("luajit", luaResidue(project, raw.table()), "E8010",
            "function signature mismatch");
        assertResidueRun("java", jvmResidue(project, raw.table()), "E8010",
            "function signature mismatch");
    }

    /** One op's contract snapshot over a replaced payload (the digest recomputed). */
    private static deal.semantic.ir.OperationContractSnapshot reContract(SemanticOp op,
            KindPayload payload) {
        deal.semantic.ir.OperationContractSnapshot original = op.contract();
        deal.semantic.ir.OperationContractSnapshot draft =
            new deal.semantic.ir.OperationContractSnapshot(original.version(), op.kind(),
                original.resultType(), original.operandTypes(), original.selector(),
                payload, original.failurePolicy(), original.referencedSemanticIds(),
                "placeholder");
        String digest = deal.semantic.ir.ContractSnapshotCanonicalizer.digest(draft);
        return new deal.semantic.ir.OperationContractSnapshot(original.version(),
            op.kind(), original.resultType(), original.operandTypes(),
            original.selector(), payload, original.failurePolicy(),
            original.referencedSemanticIds(), digest);
    }

    // =========================================================================
    // 5c. The DEAL-body return-cell fault
    // =========================================================================

    /**
     * A dynamically invoked DEAL body whose {@code RETURN} cell check fails:
     * the callee body's return-value producer is doctored to publish a value
     * of a runtime kind the body's own declared return descriptor rejects, so
     * the executed cell projects its pinned E8001 text at the cell's origin
     * and the CALL op's FAILURE terminal carries the callee's origin — in the
     * oracle and on both production artifacts.
     */
    private static void testDealBodyReturnCellFault() throws Exception {
        System.out.println("-- the DEAL-body return-cell fault: the dynamically "
            + "invoked body's own RETURN cell projects its pinned text with the "
            + "callee's origin on both targets and in the oracle --");
        Fixture fixture = fixture(CLOSURE_SOURCE, "closure drive");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "return-cell fault");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        if (call == null) {
            fail("the return-cell fault unit carries the dynamic CALL");
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        FunctionExecutionBinding carrier = carrierBinding(unit, 0);
        if (!(carrier instanceof FunctionExecutionBinding.LoweredBody body)) {
            fail("the return-cell fault drive resolves the closure carrier: " + carrier);
            return;
        }
        // The callee body's own RETURN and its single FUNCTION_RETURN cell.
        SemanticOp returnOp = null;
        OpId cell = null;
        for (OpId member : raw.table().blockOps().get(body.blockId())) {
            SemanticOp op = opOf(unit, member);
            if (op.kind() == SemanticOpKind.RETURN
                    && op.payload() instanceof KindPayload.ReturnPayload returned) {
                returnOp = op;
                cell = returned.returnBoundaryOpId();
            }
        }
        if (returnOp == null || cell == null) {
            fail("the callee body records its single RETURN and FUNCTION_RETURN cell");
            return;
        }
        SemanticOp cellOp = opOf(unit, cell);
        String cellOrigin = cellOp == null ? "-" : originText(cellOp);
        // The doctor: the body's return-value producer is replaced by a CONST
        // of a string under the identical op identity and result slot, so the
        // body's own descriptor-int cell runs its pinned E8001 projection on
        // the produced value (the op's contract digest is recomputed).
        ValueId returnedValue = ((KindPayload.ReturnPayload) returnOp.payload()).value();
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.result() instanceof ValueId value && value.equals(returnedValue)) {
                KindPayload payload = new KindPayload.ConstPayload(
                    new deal.semantic.ir.ScalarValue.String("carrier"));
                ops.add(new SemanticOp(op.opId(), SemanticOpKind.CONST, op.origin(),
                    op.result(), RuntimeDescriptor.String.INSTANCE, List.of(), List.of(),
                    payload, FailurePolicyId.NO_DEAL_FAILURE,
                    contractOf(SemanticOpKind.CONST, payload,
                        RuntimeDescriptor.String.INSTANCE,
                        FailurePolicyId.NO_DEAL_FAILURE)));
            } else {
                ops.add(op);
            }
        }
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings =
            new LinkedHashMap<>(unit.functionBindings());
        LoweredModuleUnit doctoredOps = new LoweredModuleUnit(unit.formatVersion(),
            unit.semanticProfile(), unit.moduleId(), unit.interfaceHash(),
            unit.loweringContextHash(), unit.requiredCapabilities(),
            unit.constructCoverage(), unit.classLayouts(), unit.functions(),
            unit.moduleInit(), unit.exportPlan(), bindings, ops);
        Drive drive = validateDrive(doctoredOps, raw, "return-cell fault");
        if (drive == null) {
            return;
        }
        // The trace-mode consumers and the oracle: the callee body's cell
        // FAILURE and the CALL op's FAILURE terminal, each carrying the
        // callee's origin (the START input atom of the doctored value is not
        // comparable — the doctor deliberately breaks the declared-descriptor
        // tie the atom agreement rests on, which no checker-valid program can
        // break).
        Path workspace = Files.createTempDirectory("dynamic-return-fault");
        try {
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(drive.project(),
                    Map.of(MODULE, raw.table()), Map.of(MODULE, drive.registry()),
                    SemanticDifferentialHarness.Expectation.failure("return-cell fault",
                        List.of(), "E8001", cellOrigin), workspace);
            checkEq(3, verdict.runs().size(), "the return-cell fault drive produced the "
                + "three consumers: " + verdict.failures());
            for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                check(consumer.terminal()
                        instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                        && "E8001".equals(failure.error().code())
                        && "expected int, got string".equals(failure.error().message())
                        && cellOrigin.equals(failure.error().origin()),
                    "the " + consumer.consumer() + " terminal projects the callee "
                        + "body's RETURN-cell projection with the callee's origin "
                        + cellOrigin + ": " + consumer.terminal());
                SemanticRuntimeModel.ErrorSnapshot cellFailure =
                    failureSnapshotOf(consumer, cell);
                check(cellFailure != null && cellOrigin.equals(cellFailure.origin()),
                    "the " + consumer.consumer() + " emits the cell's own FAILURE "
                        + "with the callee's origin " + cellOrigin + ": " + cellFailure);
                SemanticRuntimeModel.ErrorSnapshot callFailure =
                    failureSnapshotOf(consumer, call.opId());
                check(callFailure != null && cellOrigin.equals(callFailure.origin()),
                    "the " + consumer.consumer() + " emits the CALL op's FAILURE "
                        + "terminal with the callee's origin " + cellOrigin + ": "
                        + callFailure);
            }
        } finally {
            deleteRecursively(workspace);
        }
        assertFaultRun("luajit", luaResidue(drive.project(), raw.table()), "E8001",
            "expected int, got string", cellOrigin);
        assertFaultRun("java", jvmResidue(drive.project(), raw.table()), "E8001",
            "expected int, got string", cellOrigin);
    }

    /** The FAILURE snapshot of one op in one consumer's trace, or null. */
    private static SemanticRuntimeModel.ErrorSnapshot failureSnapshotOf(
            SemanticRuntimeModel.ConsumerRun run, OpId opId) {
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(opId)
                    && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                return event.error();
            }
        }
        return null;
    }

    // =========================================================================
    // 5d. The adapter source-class fault
    // =========================================================================

    /**
     * The adapter source-class fault fixture: an adapter over a second
     * adapter ({@code inc} adapted to two parameters, then to three). The
     * D15 source value of the dynamically dispatched adapter is itself an
     * adapter, so its class identifies no class the closed resolution
     * protocol realizes.
     */
    private static final String ADAPTER_SOURCE_CLASS_FAULT_SOURCE = """
        function inc(x: int): int {
          return x + 1
        }

        function apply(f: (a: int, b: int, c: int) => int, x: int, y: int, z: int): int {
          return f(x, y, z)
        }

        export function main(): null {
          let one: (a: int, b: int) => int = inc
          let two: (a: int, b: int, c: int) => int = one
          let r: int = apply(two, 41, 8, 1)
          if (r !== 42) {
            throw { code: "TEST_FAIL", message: "adapter source class" }
          }
          return null
        }
        """;

    /**
     * An adapter whose D15 source value identifies no resolvable class: the
     * oracle fails closed (the adapter-over-adapter source is outside the
     * statically resolved slice) and both production artifacts project the
     * pinned E8001 {@code expected function} residue at the call origin.
     */
    private static void testAdapterSourceClassFault() throws Exception {
        System.out.println("-- the adapter source-class fault: an adapter whose D15 "
            + "source value identifies no class fails closed with the pinned E8001 "
            + "at the call origin --");
        Fixture fixture = fixture(ADAPTER_SOURCE_CLASS_FAULT_SOURCE,
            "adapter source-class fault");
        if (fixture == null) {
            return;
        }
        RawLowering raw = rawLower(fixture, "adapter source-class fault");
        if (raw == null) {
            return;
        }
        LoweredModuleUnit unit = raw.unit();
        SemanticOp call = dynamicCall(unit);
        if (call == null) {
            fail("the source-class fault unit carries the dynamic CALL");
            return;
        }
        ValueId callee = ((KindPayload.CallCallee.Dynamic)
            ((KindPayload.CallPayload) call.payload()).callee()).callee();
        FunctionExecutionBinding carrier = carrierBinding(unit, 0);
        check(carrier instanceof FunctionExecutionBinding.AdapterBinding,
            "the drive registers the callee carrier read with the adapter's own "
                + "AdapterBinding: " + carrier);
        if (!(carrier instanceof FunctionExecutionBinding.AdapterBinding)) {
            return;
        }
        FunctionExecutionBinding registration = unit.functionBindings().get(
            new FunctionAllocationIdentity(callee.id()));
        check(registration instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the source-class fault drive's callee value carries the producer rule's "
                + "dynamic materialization record: " + registration);
        Drive drive = validateDrive(unit, raw, "adapter source-class fault");
        if (drive == null) {
            return;
        }
        // The oracle: the D15 source resolution classifies an adapter source,
        // which the closed resolution protocol does not realize — the drive
        // fails closed before any class path executes (the same fail-closed
        // shape testFailClosedResidue pins for an unresolvable carrier).
        String oracleFailure = null;
        try {
            SemanticOracle.executeProjectInits(drive.project(), Map.of(MODULE, raw.table()),
                Map.of(MODULE, new ClassFactoryRegistry(Map.of())), null);
        } catch (RuntimeException rejected) {
            oracleFailure = rejected.getClass().getSimpleName() + ": "
                + rejected.getMessage();
        }
        check(oracleFailure != null && oracleFailure.contains("adapter-of-adapter"),
            "the oracle fails closed on the adapter source that identifies no "
                + "class: " + oracleFailure);
        // The artifacts project the pinned E8001 residue at the call origin.
        String callOrigin = originText(call);
        assertFaultRun("luajit", luaResidue(drive.project(), raw.table()), "E8001",
            "expected function, got function", callOrigin);
        assertFaultRun("java", jvmResidue(drive.project(), raw.table()), "E8001",
            "expected function, got function", callOrigin);
    }

    /**
     * A residue/fault run: the artifact exits with the pinned projection and
     * the failure carries the failing cell's (or the call's) own origin.
     */
    private static void assertFaultRun(String target, Outcome outcome, String code,
            String text, String origin) {
        checkEq(0, outcome.exitCode(), "the fault drive (" + target
            + ") exits cleanly: " + outcome.output());
        check(outcome.stdout().startsWith("ERR:" + code + "|") && outcome.stdout()
                .contains(text),
            "the fault drive (" + target + ") projects the pinned " + code + " "
                + "text at the failure origin: " + outcome.stdout().replace("\n", "\\n"));
        check(outcome.stdout().contains("|" + origin + "|"), "the fault drive ("
            + target + ") carries the failing op's origin " + origin + ": "
            + outcome.stdout().replace("\n", "\\n"));
    }

    // =========================================================================
    // 6. No extension, no regression
    // =========================================================================

    private static void testNoExtension() {
        System.out.println("-- no extension: the closed op-kind, boundary-kind, "
            + "failure-policy, and payload sets are unchanged --");
        List<String> kinds = new ArrayList<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            kinds.add(kind.name());
        }
        checkEq(List.of("CONST", "UNARY", "BINARY", "STRING_CONCAT", "ARRAY_NEW",
                "TABLE_NEW", "ARRAY_LENGTH", "MEMBER_READ", "MEMBER_WRITE", "MEMBER_DELETE",
                "INDEX_NORMALIZE", "INDEX_READ", "INDEX_WRITE", "INDEX_DELETE",
                "OPTIONAL_READ", "HAS_FIELD", "BOUNDARY", "BINDING_ALLOC", "BINDING_INIT",
                "BINDING_LOAD", "BINDING_STORE", "RECURSIVE_GROUP_INIT", "CLOSURE_NEW",
                "FUNCTION_ADAPT", "ASSIGN", "DELETE", "CALL", "EXTERNAL_ENTRY",
                "CALLBACK_INVOKE", "INTRINSIC_CALL", "STDLIB_CALL", "ASYNC_START", "AWAIT",
                "BRANCH", "LOOP", "FOR_EACH", "TRY_CATCH", "THROW", "RETURN", "BREAK",
                "CONTINUE", "DISCARD", "CLASS_DEFAULT", "CLASS_NEW", "CLASS_FACTORY",
                "FIELD_READ", "FIELD_WRITE", "FIELD_DELETE", "JSON_FROM_CLASS",
                "JSON_TO_CLASS", "MODULE_INIT", "MODULE_IMPORT", "EXPORT_READ",
                "EXPORT_PUBLISH", "ENTRY_INVOKE"),
            kinds, "the closed op-kind set is unchanged");
        List<String> boundaries = new ArrayList<>();
        for (BoundaryKind kind : BoundaryKind.values()) {
            boundaries.add(kind.name());
        }
        checkEq(List.of("VARIABLE_DECLARATION", "VARIABLE_ASSIGNMENT",
                "CLASS_FIELD_ASSIGNMENT", "ARRAY_ELEMENT_ASSIGNMENT",
                "ARRAY_ELEMENT_READ", "ARRAY_ELEMENT_DELETE", "ARRAY_LITERAL_ELEMENT",
                "FUNCTION_PARAMETER", "FUNCTION_RETURN", "ASYNC_COMPLETION",
                "CLASS_LITERAL_FIELD", "CLASS_DEFAULT_FIELD", "UNTYPED_CLASS_INPUT",
                "OPTIONAL_FIELD_READ", "CONTEXTUAL_TABLE_READ", "IMPORTED_MEMBER_READ",
                "MODULE_EXPORT", "HOST_TO_DEAL", "DEAL_TO_HOST", "STDLIB_PARAMETER",
                "STDLIB_RETURN", "EXTERNAL_PARAMETER", "EXTERNAL_RETURN", "JSON_FROM_FIELD",
                "JSON_TO_FIELD"),
            boundaries, "the closed boundary-kind set is unchanged");
        List<String> policies = new ArrayList<>();
        for (FailurePolicyId policy : FailurePolicyId.values()) {
            policies.add(policy.name());
        }
        checkEq(List.of("NO_DEAL_FAILURE", "TYPE_DESCRIPTOR", "INT32_RESULT",
                "INT32_DIVISOR_THEN_RESULT", "INT32_EXPONENT_THEN_RESULT",
                "INT_CONVERSION", "NUMBER_CONVERSION", "ARRAY_ELEMENT_DESCRIPTOR",
                "ARRAY_READ_INDEX_THEN_DESCRIPTOR", "ARRAY_WRITE_BOUNDS_THEN_ELEMENT",
                "ARRAY_DELETE_BOUNDS", "FUNCTION_SIGNATURE", "HOST_PARAMETER",
                "HOST_SYNC_RETURN", "ASYNC_COMPLETION", "ASYNC_OPERATION_HANDLE",
                "HOST_LOAD", "CLASS_CONSTRUCTION", "JSON_PARSE_SYNTAX", "JSON_FROM_NULL",
                "JSON_TO_ERROR", "SQRT_NEGATIVE", "THROW_TRANSFER",
                "INFRASTRUCTURE_ONLY"),
            policies, "the closed failure-policy set is unchanged");
        List<String> payloads = new ArrayList<>();
        for (Class<?> permitted : KindPayload.class.getPermittedSubclasses()) {
            payloads.add(permitted.getSimpleName());
        }
        checkEq(List.of("ConstPayload", "UnaryPayload", "BinaryPayload",
                "StringConcatPayload", "ArrayNewPayload", "TableNewPayload",
                "ArrayLengthPayload", "MemberReadPayload", "MemberWritePayload",
                "MemberDeletePayload", "IndexNormalizePayload", "IndexReadPayload",
                "IndexWritePayload", "IndexDeletePayload", "OptionalReadPayload",
                "HasFieldPayload", "BoundaryPayload", "BindingAllocPayload",
                "BindingInitPayload", "BindingLoadPayload", "BindingStorePayload",
                "RecursiveGroupInitPayload", "ClosureNewPayload", "FunctionAdaptPayload",
                "AssignPayload", "DeletePayload", "CallPayload", "ExternalEntryPayload",
                "CallbackInvokePayload", "IntrinsicCallPayload", "StdlibCallPayload",
                "AsyncStartPayload", "AwaitPayload", "BranchPayload", "LoopPayload",
                "ForEachPayload", "TryCatchPayload", "ThrowPayload", "ReturnPayload",
                "BreakPayload", "ContinuePayload", "DiscardPayload", "ClassDefaultPayload",
                "ClassNewPayload", "ClassFactoryPayload", "FieldReadPayload",
                "FieldWritePayload", "FieldDeletePayload", "JsonFromClassPayload",
                "JsonToClassPayload", "ModuleInitPayload", "ModuleImportPayload",
                "ExportReadPayload", "ExportPublishPayload", "EntryInvokePayload"),
            payloads, "the payload-record set carries no new member");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Dynamic Dispatch Emission Tests (ISSUE-0658) ===\n");
        testClosureCarrierDrive();
        testAdapterCarrierDrive();
        testDynamicAsyncDrive();
        testDynamicAsyncAdapterDrive();
        testCalleeOwnedCellDrive();
        testComposedDrive();
        testEmittedSurface();
        testEmittedAsyncDispatchSurface();
        testFailClosedResidue();
        testAdapterSourceSignatureFault();
        testDealBodyReturnCellFault();
        testAdapterSourceClassFault();
        testNoExtension();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Dynamic Dispatch Emission Tests Passed ===");
    }
}
