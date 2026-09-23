package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StructuredBodyTable;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * ISSUE-0654: the cross-module sync call realization through the callee
 * unit's {@code EXTERNAL_ENTRY}
 * ({@code cross-module-call-realization} X1/X4/X5, the cross-module sync
 * call contract, and the entry record contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2/C7;
 * {@code semantic-ir-construct-coverage-cutover} K4).
 *
 * <ol>
 *   <li>the six named corpus fixtures
 *       ({@code modules/imported-recursive-export},
 *       {@code import-alias-member-access},
 *       {@code cross-module-class-factory},
 *       {@code exported-class-function-combo}, {@code imported-class-array},
 *       {@code modid-class-identity-control}) materialize in the lane
 *       layout, lower through {@link SemanticLowerer#lowerProject}, and
 *       emit one project artifact per target through the production arm;</li>
 *   <li>each fixture's exported zero-arity probe executes under real
 *       {@code luajit} and real {@code javac --release 25 -proc:none} +
 *       {@code java} through the artifact's published export surface, and
 *       the observed transcript (exit code, stdout, stderr) equals the
 *       fixture's pinned {@code .expect.json} sidecar;</li>
 *   <li>the caller-side cell shape: exactly one {@code EXTERNAL_PARAMETER}
 *       boundary child per argument in one-based order and no caller-side
 *       return boundary for the {@code SHARED_BODY} call; the callee unit
 *       records exactly one {@code EXTERNAL_ENTRY} whose single
 *       {@code EXTERNAL_RETURN} boundary is run by the callee body's
 *       {@code RETURN} under the declared return descriptor;</li>
 *   <li>the oracle and both conformance emitters agree event-for-event
 *       over the same projects (the differential harness), and the
 *       oracle's entry events parent to the caller's {@code CALL} op and
 *       carry the callee module while the caller's own terminal keeps the
 *       caller's module;</li>
 *   <li>the module context is restored after a successful and after a
 *       failing callee (the failure carries the callee's origin, the
 *       caller's {@code CALL} FAILURE carries the caller's module);</li>
 *   <li>the fail-closed seeds: an {@code externalEntryRef} naming a module
 *       outside the closure, an {@code externalEntryRef} resolving to a
 *       non-entry op, and a {@code RETAINED_ABI} external each fail closed
 *       with nothing emitted; the production arm's E6005
 *       {@code SHARED_EMITTER_COVERAGE} mapping of an emitter rejection and
 *       its staging-after-success order stay pinned.</li>
 * </ol>
 */
public class CrossModuleCallRealizationTest {

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
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    private static final Path CORPUS =
        Path.of("test", "conformance", "backend-runtime", "modules");

    /** One named corpus fixture: its entry, its compilation set, its sidecar. */
    private record CorpusFixture(String entryName, List<String> modulePaths,
                                 Path sidecar) {
    }

    private static final List<String> FIXTURE_NAMES = List.of(
        "imported-recursive-export",
        "import-alias-member-access",
        "cross-module-class-factory",
        "exported-class-function-combo",
        "imported-class-array",
        "modid-class-identity-control");

    /** The exported zero-arity probe each fixture's sidecar drives. */
    private static String probeOf(String fixtureName) {
        return switch (fixtureName) {
            case "imported-recursive-export" -> "test_imported_recursive_export";
            case "import-alias-member-access" -> "test_import_alias_member_access";
            case "cross-module-class-factory" ->
                "test_cross_module_class_factory";
            case "exported-class-function-combo" ->
                "test_exported_class_function_combo";
            case "imported-class-array" -> "test_imported_class_array";
            case "modid-class-identity-control" ->
                "test_same_module_class_identity_roundtrip";
            default -> throw new IllegalArgumentException(fixtureName);
        };
    }

    /** The companion module of each fixture's import, as a corpus path. */
    private static List<String> companionsOf(String source) {
        List<String> companions = new ArrayList<>();
        Matcher matcher = Pattern.compile("from \"(\\./[^\"]+)\"").matcher(source);
        while (matcher.find()) {
            String rel = matcher.group(1).substring(2);
            companions.add(rel);
        }
        return companions;
    }

    /** Reads one corpus source with its classification headers stripped. */
    private static String corpusSource(String relative) throws Exception {
        String text = Files.readString(CORPUS.resolve(relative),
            StandardCharsets.UTF_8);
        StringBuilder stripped = new StringBuilder();
        for (String line : text.split("\n", -1)) {
            if (line.startsWith("// @")) {
                continue;
            }
            stripped.append(line).append('\n');
        }
        return stripped.toString();
    }

    private record Fixture(
        Path root,
        Path moduleRoot,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome,
        String entryModule) {
    }

    /** The release-owned production invocation (the epic's production record). */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * Materializes one corpus fixture in the lane layout — the module root
     * is the temp {@code src} directory, the entry keeps its corpus stem,
     * and every imported companion keeps its corpus-relative path — so the
     * module identities and class descriptor namespaces match the
     * conformance lane's materialization.
     */
    private static Fixture materialize(String fixtureName) throws Exception {
        Path root = Files.createTempDirectory("cross-module-call-" + fixtureName);
        Path moduleRoot = root.resolve("src");
        Files.createDirectories(moduleRoot);
        String entrySource = corpusSource(fixtureName + ".deal");
        writeFileIn(root, "src/" + fixtureName + ".deal", entrySource);
        for (String companion : companionsOf(entrySource)) {
            writeFileIn(root, "src/" + companion + ".deal",
                corpusSource(companion + ".deal"));
        }
        Path entry = moduleRoot.resolve(fixtureName + ".deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(moduleRoot.toAbsolutePath()), null, null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: "
                + detail + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, moduleRoot, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            new LinkedHashMap<>(), new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(moduleRoot.toString()),
            fixtureName);
    }

    /** The probe project: a cross-module call, a same-module export call, recursion. */
    private record Probe(Fixture fixture, String lib, String app) {
    }

    private static final String PROBE_LIB = """
        export function add(a: int, b: int): int {
          return a + b;
        }

        export function fib(n: int): int {
          if (n < 2) { return n; }
          return fib(n - 1) + fib(n - 2);
        }
        """;

    private static final String PROBE_APP = """
        import * as lib from "./lib"

        function twice(x: int): int {
          return x * 2;
        }

        export function main(): null {
          let a: int = lib.add(1, 2);
          let b: int = lib.fib(6);
          let c: int = twice(a);
          if (a !== 3 || b !== 8 || c !== 6) {
            throw { code: "PROBE_FAIL", message: "cross-module probe" };
          }
          return null;
        }
        """;

    /** One probe project (two modules, a cross-module call and recursion). */
    private static Fixture probeProject() throws Exception {
        Path root = Files.createTempDirectory("cross-module-call-probe");
        Path moduleRoot = root.resolve("src");
        Files.createDirectories(moduleRoot);
        writeFileIn(root, "src/lib.deal", PROBE_LIB);
        writeFileIn(root, "src/app.deal", PROBE_APP);
        Path entry = moduleRoot.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(moduleRoot.toAbsolutePath()), null, null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null) {
            deleteRecursively(root);
            throw new IllegalStateException("the probe did not build: "
                + orchestrator.diagnostics());
        }
        return new Fixture(root, moduleRoot, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            new LinkedHashMap<>(), new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(moduleRoot.toString()), "app");
    }

    /** A failing-callee probe: the callee throws after a nested call. */
    private static Fixture failingProbeProject() throws Exception {
        Path root = Files.createTempDirectory("cross-module-call-failing");
        Path moduleRoot = root.resolve("src");
        Files.createDirectories(moduleRoot);
        writeFileIn(root, "src/lib.deal", """
            export function boom(n: int): int {
              let doubled: int = n * 2;
              throw { code: "BOOM", message: "callee failure" };
            }
            """);
        writeFileIn(root, "src/app.deal", """
            import * as lib from "./lib"

            export function main(): null {
              let r: int = lib.boom(1);
              return null;
            }
            """);
        Path entry = moduleRoot.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, output, false, false, false, false, Backend.LUAJIT, Map.of(),
            List.of(moduleRoot.toAbsolutePath()), null, null,
            ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null) {
            deleteRecursively(root);
            throw new IllegalStateException("the failing probe did not build: "
                + orchestrator.diagnostics());
        }
        return new Fixture(root, moduleRoot, built.input(), built.index(),
            manifests.manifests(), orchestrator.hostDeclarationSurface(),
            new LinkedHashMap<>(), new LinkedHashMap<>(),
            DistributionHome.forManifestDirectory(moduleRoot.toString()), "app");
    }

    /** The one project lowering over the real checked project. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            java.util.Set.of());
    }

    /** One production-arm drive of the fixture (the real production unit). */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager) throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            java.util.Set.of(), backend, false, fixture.distributionHome(), stager);
    }

    private static List<SemanticOp> ofKind(LoweredModuleUnit unit,
            SemanticOpKind kind) {
        List<SemanticOp> matches = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == kind) {
                matches.add(op);
            }
        }
        return matches;
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId opId) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(opId)) {
                return op;
            }
        }
        return null;
    }

    /** The external calls of one unit, in op order. */
    private static List<SemanticOp> externalCalls(LoweredModuleUnit unit) {
        List<SemanticOp> calls = new ArrayList<>();
        for (SemanticOp op : ofKind(unit, SemanticOpKind.CALL)) {
            if (op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Static callee
                    && callee.binding()
                        instanceof FunctionExecutionBinding.ExternalFunction) {
                calls.add(op);
            }
        }
        return calls;
    }

    // =========================================================================
    // 1. The lowering drive: the caller cells and the callee entry record
    // =========================================================================

    private static void testLoweringCellShapes() throws Exception {
        System.out.println("-- the caller-side EXTERNAL_PARAMETER cells, the absent "
            + "caller-side return boundary, and the callee's single "
            + "EXTERNAL_RETURN --");
        Fixture fixture = probeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null && !result.hasErrors(),
                "the probe lowers through the one project entry: "
                    + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ModuleId lib = new ModuleId("lib");
            ModuleId app = new ModuleId("app");
            LoweredModuleUnit libUnit = result.project().modules().get(lib);
            LoweredModuleUnit appUnit = result.project().modules().get(app);
            check(libUnit != null && appUnit != null,
                "the closure carries the callee and the caller module");
            if (libUnit == null || appUnit == null) {
                return;
            }

            // The callee unit: one EXTERNAL_ENTRY per exported function, each
            // naming the single EXTERNAL_RETURN boundary its body's RETURN
            // runs on the declared return descriptor.
            List<SemanticOp> entries = ofKind(libUnit, SemanticOpKind.EXTERNAL_ENTRY);
            checkEq(2, entries.size(),
                "the callee unit records one EXTERNAL_ENTRY per exported function");
            for (SemanticOp entry : entries) {
                KindPayload.ExternalEntryPayload payload =
                    (KindPayload.ExternalEntryPayload) entry.payload();
                check(!payload.async(), "the entry records the sync shape");
                SemanticOp boundary = opOf(libUnit, payload.returnBoundaryOpId());
                check(boundary != null
                        && boundary.kind() == SemanticOpKind.BOUNDARY
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp
                        && bp.kind() == BoundaryKind.EXTERNAL_RETURN,
                    "the sync entry names its single EXTERNAL_RETURN boundary: "
                        + payload.exportName());
                if (boundary != null
                        && boundary.payload() instanceof KindPayload.BoundaryPayload bp) {
                    checkEq(payload.signature().returnType(), bp.descriptor(),
                        "the EXTERNAL_RETURN boundary checks the declared return "
                            + "descriptor of " + payload.exportName());
                }
            }

            // The caller unit: each cross-module call carries exactly one
            // EXTERNAL_PARAMETER child per argument in one-based order, no
            // caller-side return boundary, and the callee entry ref.
            List<SemanticOp> calls = externalCalls(appUnit);
            checkEq(2, calls.size(),
                "the caller unit records one cross-module call per site: " + calls);
            for (SemanticOp call : calls) {
                KindPayload.CallPayload payload =
                    (KindPayload.CallPayload) call.payload();
                FunctionExecutionBinding.ExternalFunction external =
                    (FunctionExecutionBinding.ExternalFunction)
                        ((KindPayload.CallCallee.Static) payload.callee()).binding();
                checkEq(ExternalExecutionOwner.SHARED_BODY,
                    external.executionOwner(),
                    "the call resolves the SHARED_BODY execution owner");
                checkEq(null, payload.returnBoundaryOpId(),
                    "a SHARED_BODY external call carries no caller-side return "
                        + "boundary");
                check(payload.externalEntryRef() != null
                        && payload.externalEntryRef().module().equals(lib),
                    "the call records the callee unit's EXTERNAL_ENTRY ref: "
                        + payload.externalEntryRef());
                checkEq(external.descriptor().paramTypes().size(),
                    payload.parameterBoundaryOpIds().size(),
                    "one EXTERNAL_PARAMETER child per declared argument");
                for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                    SemanticOp boundary =
                        opOf(appUnit, payload.parameterBoundaryOpIds().get(i));
                    check(boundary != null
                            && boundary.payload()
                                instanceof KindPayload.BoundaryPayload bp
                            && bp.kind() == BoundaryKind.EXTERNAL_PARAMETER,
                        "argument " + (i + 1) + " carries its EXTERNAL_PARAMETER "
                            + "boundary child");
                    if (boundary != null
                            && boundary.payload()
                                instanceof KindPayload.BoundaryPayload bp) {
                        checkEq(external.descriptor().paramTypes().get(i),
                            bp.descriptor(),
                            "the EXTERNAL_PARAMETER boundary " + (i + 1)
                                + " checks the declared parameter descriptor");
                    }
                }
                SemanticOp entry = opOf(libUnit, payload.externalEntryRef());
                check(entry != null
                        && entry.kind() == SemanticOpKind.EXTERNAL_ENTRY
                        && ((KindPayload.ExternalEntryPayload) entry.payload())
                            .exportName().equals(external.exportName()),
                    "the recorded ref resolves to the callee entry of the same "
                        + "export");
            }

            // The callee module's own state: its exports are published by its
            // own init walk, and the caller's CALL names no callee cell (the
            // invocation reads the entry's function factory, not a module
            // cell) — the callee module's init state, cells, and exports are
            // untouched by the call.
            java.util.Set<Long> callerResults = new java.util.HashSet<>();
            for (SemanticOp op : appUnit.ops()) {
                if (op.result() instanceof deal.semantic.ir.ValueId value) {
                    callerResults.add(value.id());
                }
            }
            for (SemanticOp call : calls) {
                for (deal.semantic.ir.ValueId operand : call.operands()) {
                    check(callerResults.contains(operand.id()),
                        "the caller's call operand is produced in the caller "
                            + "unit: " + operand);
                }
            }
            for (SemanticOp publish : ofKind(appUnit, SemanticOpKind.EXPORT_PUBLISH)) {
                check(publish.payload() instanceof KindPayload.ExportPublishPayload p
                        && !p.name().equals("add") && !p.name().equals("fib"),
                    "the caller publishes no callee export: " + publish.payload());
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The oracle: entry events, module attribution, and the restored context
    // =========================================================================

    private static void testOracleEntryEvents() throws Exception {
        System.out.println("-- the oracle's entry events parent to the caller's CALL "
            + "under the callee module; the caller's terminal keeps the caller's "
            + "module --");
        Fixture fixture = probeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe lowers: " + result.diagnostics());
                return;
            }
            SemanticRuntimeModel.ConsumerRun run =
                SemanticOracle.executeProjectInits(result.project(),
                    result.tables(), result.registries(), null);
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle completes the probe: " + run.comparisonReport());

            ModuleId app = new ModuleId("app");
            LoweredModuleUnit appUnit = result.project().modules().get(app);
            List<SemanticOp> calls = externalCalls(appUnit);
            checkEq(2, calls.size(), "the probe carries two cross-module calls");
            if (calls.size() != 2) {
                return;
            }

            // Every entry invocation is one START/SUCCESS pair whose event
            // carries the callee module and whose parent is the triggering
            // CALL op (the caller's own op for the cross-module invocations,
            // the callee's op for the recursive invocations inside fib).
            List<SemanticRuntimeModel.TraceEvent> entryEvents = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.kind() == SemanticOpKind.EXTERNAL_ENTRY) {
                    entryEvents.add(event);
                }
            }
            check(!entryEvents.isEmpty() && entryEvents.size() % 2 == 0,
                "the oracle emits entry START/SUCCESS pairs: "
                    + entryEvents.size());
            java.util.Set<OpId> callOps = new java.util.HashSet<>();
            for (LoweredModuleUnit unit : result.project().modules().values()) {
                for (SemanticOp op : ofKind(unit, SemanticOpKind.CALL)) {
                    callOps.add(op.opId());
                }
            }
            int open = 0;
            for (SemanticRuntimeModel.TraceEvent event : entryEvents) {
                checkEq("lib", event.module(),
                    "the entry event carries the callee module: " + event.text());
                check(event.parentOp() != null && callOps.contains(event.parentOp()),
                    "the entry event parents to a CALL op: " + event.text());
                if (event.phase() == SemanticRuntimeModel.Phase.START) {
                    open++;
                } else {
                    checkEq(SemanticRuntimeModel.Phase.SUCCESS, event.phase(),
                        "the entry terminal is a SUCCESS: " + event.text());
                    open--;
                    check(open >= 0, "the entry events are properly nested: "
                        + event.text());
                }
            }
            checkEq(0, open, "every entry START closes with its SUCCESS");
            long callerParented = entryEvents.stream()
                .filter(event -> event.phase() == SemanticRuntimeModel.Phase.START)
                .filter(event -> event.parentOp() != null
                    && event.parentOp().module().equals(app))
                .count();
            check(callerParented >= 2,
                "the cross-module entry invocations parent to the caller's CALL "
                    + "ops: " + callerParented);

            // The callee's single EXTERNAL_RETURN boundary event runs, and
            // the caller's CALL SUCCESS publishes the checked value.
            List<SemanticRuntimeModel.TraceEvent> returns = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.kind() == SemanticOpKind.BOUNDARY
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS
                        && "lib".equals(event.module())) {
                    returns.add(event);
                }
            }
            check(!returns.isEmpty(),
                "the callee's boundary SUCCESS events run in the callee module");
            List<SemanticRuntimeModel.TraceEvent> callSuccesses = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.kind() == SemanticOpKind.CALL
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS) {
                    callSuccesses.add(event);
                }
            }
            check(callSuccesses.stream().anyMatch(event ->
                    "app".equals(event.module()) && "int:3".equals(event.output())),
                "the caller's CALL SUCCESS publishes the crossed add value: "
                    + callSuccesses);
            check(callSuccesses.stream().anyMatch(event ->
                    "app".equals(event.module()) && "int:8".equals(event.output())),
                "the caller's CALL SUCCESS publishes the crossed fib value: "
                    + callSuccesses);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testFailingCalleeRestoresContext() throws Exception {
        System.out.println("-- a failing callee: the failure carries the callee "
            + "origin and the caller's CALL FAILURE keeps the caller's module --");
        Fixture fixture = failingProbeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the failing probe lowers: " + result.diagnostics());
                return;
            }
            SemanticRuntimeModel.ConsumerRun run;
            try {
                run = SemanticOracle.executeProjectInits(result.project(),
                    result.tables(), result.registries(), null);
            } catch (RuntimeException rejected) {
                fail("the oracle rejects the failing probe instead of executing "
                    + "it: " + rejected);
                return;
            }
            check(run.terminal() instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the failing callee propagates to the terminal: "
                    + run.comparisonReport());
            for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                if (event.kind() == SemanticOpKind.EXTERNAL_ENTRY) {
                    checkEq("lib", event.module(),
                        "the entry event keeps the callee module on the failure "
                            + "path");
                }
                if (event.kind() == SemanticOpKind.CALL
                        && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                    checkEq("app", event.module(),
                        "the caller's CALL FAILURE keeps the caller's module: "
                            + event.text());
                }
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The three-consumer trace equality over the same projects
    // =========================================================================

    private static void testThreeConsumerTraceEquality() throws Exception {
        System.out.println("-- the oracle and both conformance emitters agree "
            + "event-for-event over the probe, the failing probe, and the six "
            + "fixtures --");
        Fixture probe = probeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(probe);
            if (result.project() == null) {
                fail("the probe lowers: " + result.diagnostics());
            } else {
                runDifferential("cross-module probe", result.project(),
                    result.tables(), result.registries());
            }
        } finally {
            deleteRecursively(probe.root());
        }

        Fixture failing = failingProbeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(failing);
            if (result.project() == null) {
                fail("the failing probe lowers: " + result.diagnostics());
            } else {
                runDifferential("failing cross-module probe", result.project(),
                    result.tables(), result.registries());
            }
        } finally {
            deleteRecursively(failing.root());
        }

        for (String name : FIXTURE_NAMES) {
            Fixture fixture = materialize(name);
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(fixture);
                if (result.project() == null) {
                    fail("fixture " + name + " lowers: " + result.diagnostics());
                    continue;
                }
                runDifferential("fixture " + name, result.project(),
                    result.tables(), result.registries());
            } finally {
                deleteRecursively(fixture.root());
            }
        }
    }

    private static List<String> traceLines(SemanticRuntimeModel.ConsumerRun run) {
        List<String> lines = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            lines.add(event.text());
        }
        return lines;
    }

    private static void runDifferential(String what, ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries) throws Exception {
        Path workspace = Files.createTempDirectory("cross-module-call-diff");
        try {
            SemanticDifferentialHarness.Expectation expectation;
            if (what.contains("failing")) {
                expectation = SemanticDifferentialHarness.Expectation.failure(what,
                    List.of(), "BOOM", null);
            } else {
                expectation = SemanticDifferentialHarness.Expectation.success(what,
                    List.of(), "null");
            }
            SemanticDifferentialHarness.Verdict verdict =
                SemanticDifferentialHarness.runProject(project, tables, registries,
                    expectation, workspace);
            // The three-consumer trace equality is the criterion here; the
            // harness's own per-op gate additionally assumes one START per
            // op per run, which a recursive body (fib) legitimately breaks,
            // so the traces are compared directly.
            checkEq(3, verdict.runs().size(), what
                + ": the harness produced the three consumers: "
                + verdict.failures());
            if (verdict.runs().size() == 3) {
                List<String> oracleTrace = traceLines(verdict.runs().get(0));
                check(!oracleTrace.isEmpty(), what + ": the oracle produced events");
                for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                    List<String> lines = traceLines(consumer);
                    checkEq(oracleTrace, lines, what + ": the " + consumer.consumer()
                        + " trace equals the oracle's event-for-event");
                }
            }
            if (!verdict.pass() && Boolean.getBoolean("deal.test.traceDebug")) {
                List<List<String>> traces = new ArrayList<>();
                for (SemanticRuntimeModel.ConsumerRun consumer : verdict.runs()) {
                    List<String> lines = new ArrayList<>();
                    for (SemanticRuntimeModel.TraceEvent event : consumer.trace()) {
                        lines.add(event.text());
                    }
                    traces.add(lines);
                    System.out.println("== " + consumer.consumer() + " ("
                        + lines.size() + " events)");
                }
                int min = traces.stream().mapToInt(List::size).min().orElse(0);
                for (int i = 0; i < min; i++) {
                    String first = traces.get(0).get(i);
                    for (int c = 1; c < traces.size(); c++) {
                        if (!traces.get(c).get(i).equals(first)) {
                            System.out.println("DIFF@" + i + " " + traces.get(c)
                                .get(0).split("\\|")[1] + "\n  oracle: " + first
                                + "\n  other : " + traces.get(c).get(i));
                            break;
                        }
                    }
                }
            }
        } finally {
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 4. The production artifacts and the pinned sidecars
    // =========================================================================

    private static void testProductionArtifactsAndSidecars() throws Exception {
        System.out.println("-- the six fixtures: one project artifact per target, "
            + "executed under luajit and java with the pinned sidecar transcript --");
        String classpath = absoluteClasspath();
        for (String name : FIXTURE_NAMES) {
            Fixture fixture = materialize(name);
            Path luaOut = fixture.root().resolve("out-luajit");
            Path jvmOut = fixture.root().resolve("out-jvm");
            Path classes = fixture.root().resolve("classes");
            try {
                // LuaJIT.
                PublicationStager luaStager = PublicationStager.forRoot(luaOut);
                ProductionProjectEmission.Result lua;
                try {
                    lua = emit(fixture, Backend.LUAJIT, luaStager);
                    check(lua.emitted(), name + ": the LuaJIT production run "
                        + "emits: " + lua.diagnostics());
                    if (lua.emitted()) {
                        checkEq(name + ".lua", lua.artifactRelativePath(),
                            name + ": the LuaJIT artifact is the entry module's "
                                + "chunk");
                        luaStager.publish();
                    }
                } finally {
                    luaStager.discard();
                }
                if (lua.emitted()) {
                    writeFileIn(luaOut, "probe.lua", luaDriver(
                        name, probeOf(name)));
                    ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"),
                        luaOut);
                    assertSidecar(name, "LuaJIT", fixture, run);
                }

                // JVM.
                PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
                ProductionProjectEmission.Result jvm;
                try {
                    jvm = emit(fixture, Backend.JVM, jvmStager);
                    check(jvm.emitted(), name + ": the JVM production run emits: "
                        + jvm.diagnostics());
                    if (jvm.emitted()) {
                        checkEq(JvmBackend.classNameFor(name) + ".java",
                            jvm.artifactRelativePath(),
                            name + ": the JVM artifact is the entry class");
                        jvmStager.publish();
                    }
                } finally {
                    jvmStager.discard();
                }
                if (jvm.emitted()) {
                    String className = JvmBackend.classNameFor(name);
                    Files.createDirectories(classes);
                    writeFileIn(jvmOut, "Probe.java",
                        jvmDriver(className, name, probeOf(name)));
                    ProcessOutcome javac = runProcess(List.of("javac",
                        "--release", "25", "-proc:none", "-cp", classpath,
                        "-d", classes.toString(),
                        jvmOut.resolve(className + ".java").toAbsolutePath()
                            .toString(),
                        jvmOut.resolve("Probe.java").toAbsolutePath().toString()),
                        jvmOut);
                    checkEq(0, javac.exitCode(), name
                        + ": the JVM production artifact compiles: "
                        + javac.output());
                    if (javac.exitCode() == 0) {
                        ProcessOutcome run = runProcess(List.of("java", "-cp",
                            classpath + java.io.File.pathSeparator + classes,
                            "Probe"), jvmOut);
                        assertSidecar(name, "JVM", fixture, run);
                    }
                }
            } finally {
                deleteRecursively(fixture.root());
            }
        }
    }

    /** The LuaJIT driver: the module walk, then the exported probe through the surface. */
    private static String luaDriver(String fixtureName, String exportName) {
        return """
            local surfaces = dofile("%s.lua")
            assert(type(surfaces) == "table",
              "the production chunk returns the entry surface")
            local probe = surfaces["%s"]
            assert(type(probe) == "table" and probe.__kind == "function"
              and type(probe.f) == "function",
              "the entry surface publishes the fixture probe")
            probe.f()
            """.formatted(fixtureName, exportName);
    }

    /** The JVM driver: the module walk, then the exported probe through the surface. */
    private static String jvmDriver(String className, String fixtureName,
            String exportName) {
        return """
            public final class Probe {
              public static void main(String[] args) {
                %s.main(new String[0]);
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.EXPORT_SURFACES.get("%s");
                Object probe = surface.read("%s");
                if (!(probe instanceof deal.codegen.jvm.JvmRuntime.FunctionValue fn)) {
                  throw new IllegalStateException(
                      "the entry surface publishes the fixture probe");
                }
                fn.fn.invoke(new Object[0]);
              }
            }
            """.formatted(className, className, fixtureName, exportName);
    }

    /** The pinned sidecar transcript of one fixture equals the observed run. */
    private static void assertSidecar(String name, String target, Fixture fixture,
            ProcessOutcome run) throws Exception {
        String sidecar = Files.readString(
            CORPUS.resolve(name + ".expect.json"), StandardCharsets.UTF_8);
        check(sidecar.contains("\"mode\": \"runtime-ok\""),
            name + ": the sidecar pins the runtime-ok mode");
        checkEq(0, sidecarExitCode(sidecar),
            name + ": the sidecar pins exit code 0");
        checkEq("", sidecarTranscript(sidecar, "stdout"),
            name + ": the sidecar pins an empty stdout");
        checkEq("", sidecarTranscript(sidecar, "stderr"),
            name + ": the sidecar pins an empty stderr");
        checkEq(0, run.exitCode(), name + " (" + target
            + "): the executed fixture exits 0: " + run.output());
        checkEq("", run.stdout(), name + " (" + target
            + "): the executed fixture writes nothing on stdout: " + run.output());
        checkEq("", run.stderr(), name + " (" + target
            + "): the executed fixture writes nothing on stderr: " + run.output());
    }

    private static int sidecarExitCode(String sidecar) {
        Matcher matcher = Pattern.compile("\"exitCode\":\\s*(-?\\d+)").matcher(sidecar);
        return matcher.find() ? Integer.parseInt(matcher.group(1)) : Integer.MIN_VALUE;
    }

    private static String sidecarTranscript(String sidecar, String channel) {
        Matcher matcher = Pattern.compile("\"" + channel
            + "\":\\s*\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(sidecar);
        if (!matcher.find()) {
            return null;
        }
        return matcher.group(1).replace("\\n", "\n").replace("\\\"", "\"");
    }

    // =========================================================================
    // 5. The fail-closed seeds
    // =========================================================================

    private static void testFailClosedSeeds() throws Exception {
        System.out.println("-- the fail-closed seeds: a ref outside the closure, a "
            + "non-entry ref, and a RETAINED_ABI external --");
        Fixture fixture = probeProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the probe lowers: " + result.diagnostics());
                return;
            }
            ModuleId app = new ModuleId("app");
            LoweredModuleUnit appUnit = result.project().modules().get(app);
            SemanticOp call = externalCalls(appUnit).get(0);

            // (a) The ref names a module outside the closure: retarget the
            // call at a foreign module's op identity.
            OpId foreign = new OpId(new ModuleId("outside"), 1);
            ExecutableLoweredProject outsideClosure = replaceProjectCall(
                result.project(), appUnit, call, foreign);
            assertEmitterRejects("the ref naming a module outside the closure",
                outsideClosure, result.tables(), result.registries(), fixture);

            // (b) The ref resolves to a non-entry op of the callee unit.
            ModuleId lib = new ModuleId("lib");
            LoweredModuleUnit libUnit = result.project().modules().get(lib);
            SemanticOp nonEntry = ofKind(libUnit, SemanticOpKind.EXPORT_PUBLISH).get(0);
            ExecutableLoweredProject nonEntryRef = replaceProjectCall(
                result.project(), appUnit, call, nonEntry.opId());
            assertEmitterRejects("the ref resolving to a non-entry op",
                nonEntryRef, result.tables(), result.registries(), fixture);

            // (c) A RETAINED_ABI external keeps its landed rejection: the one
            // project lowering records every module of the closure SHARED,
            // so this hand-built owner never arises from a checker-valid
            // program.
            KindPayload.CallPayload probePayload = (KindPayload.CallPayload) call.payload();
            FunctionExecutionBinding.ExternalFunction shared =
                (FunctionExecutionBinding.ExternalFunction)
                    ((KindPayload.CallCallee.Static) probePayload.callee()).binding();
            KindPayload.CallPayload retained = new KindPayload.CallPayload(
                probePayload.mode(),
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.ExternalFunction(
                        shared.moduleId(), shared.exportName(), shared.descriptor(),
                        ExternalExecutionOwner.RETAINED_ABI)),
                probePayload.signature(), probePayload.parameterBoundaryOpIds(),
                probePayload.returnBoundaryOpId(), probePayload.dynamicReturnBoundary(),
                probePayload.bodyBlock(), probePayload.externalEntryRef());
            assertRetainedOwnerRejected("the RETAINED_ABI external",
                replaceCallPayload(result.project(), appUnit, call, retained),
                result.tables(), result.registries(), fixture);
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /**
     * Replaces the externalEntryRef of one call in the project's caller unit
     * with the given op identity: the hand-built inconsistent fact the
     * fail-closed seeds need (no checker-valid program produces it).
     */
    private static ExecutableLoweredProject replaceProjectCall(
            ExecutableLoweredProject project, LoweredModuleUnit caller,
            SemanticOp call, OpId newRef) {
        KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
        KindPayload.CallPayload replaced = new KindPayload.CallPayload(
            payload.mode(), payload.callee(), payload.signature(),
            payload.parameterBoundaryOpIds(), payload.returnBoundaryOpId(),
            payload.dynamicReturnBoundary(), payload.bodyBlock(), newRef);
        return replaceCallPayload(project, caller, call, replaced);
    }

    /**
     * Replaces one call op's payload (the caller unit rebuilt with the
     * replaced payload and its rewired contract snapshot): the hand-built
     * inconsistent fact every fail-closed seed needs (no checker-valid
     * program produces one).
     */
    private static ExecutableLoweredProject replaceCallPayload(
            ExecutableLoweredProject project, LoweredModuleUnit caller,
            SemanticOp call, KindPayload.CallPayload replaced) {
        // The contract snapshot is rewired to the replaced payload instance
        // (the op constructor pins the identity): the hand-built seed stays
        // a structurally valid op carrying the inconsistent fact.
        deal.semantic.ir.OperationContractSnapshot old = call.contract();
        deal.semantic.ir.OperationContractSnapshot rewired =
            new deal.semantic.ir.OperationContractSnapshot(old.version(),
                old.opKind(), old.resultType(), old.operandTypes(), old.selector(),
                replaced, old.failurePolicy(), old.referencedSemanticIds(),
                old.canonicalDigest());
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : caller.ops()) {
            if (op.opId().equals(call.opId())) {
                ops.add(new SemanticOp(op.opId(), op.kind(), op.origin(),
                    op.result(), op.resultType(), op.operands(), op.operandTypes(),
                    replaced, op.failurePolicy(), rewired));
            } else {
                ops.add(op);
            }
        }
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        for (Map.Entry<ModuleId, LoweredModuleUnit> entry
                : project.modules().entrySet()) {
            if (entry.getKey().equals(caller.moduleId())) {
                modules.put(entry.getKey(), withOps(caller, ops));
            } else {
                modules.put(entry.getKey(), entry.getValue());
            }
        }
        return new ExecutableLoweredProject(project.semanticProfile(),
            project.interfaceIndex(), modules, project.entryModule());
    }

    private static LoweredModuleUnit withOps(LoweredModuleUnit unit,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(unit.formatVersion(), unit.semanticProfile(),
            unit.moduleId(), unit.interfaceHash(), unit.loweringContextHash(),
            unit.requiredCapabilities(), unit.constructCoverage(),
            unit.classLayouts(), unit.functions(), unit.moduleInit(),
            unit.exportPlan(), unit.functionBindings(), ops);
    }

    /**
     * Both emitters and the oracle reject the hand-built inconsistent fact
     * with a fail-closed producer defect naming the unresolved entry; the
     * production arm maps such an emitter rejection to E6005
     * {@code SHARED_EMITTER_COVERAGE} and stages nothing (the mapping is
     * pinned by the production-mapping test).
     */
    private static void assertEmitterRejects(String what,
            ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, Fixture fixture) {
        try {
            LuaSemanticEmitter.emitProductionProject(project, tables, registries,
                fixture.surface());
            fail(what + ": the LuaJIT emitter rejects the inconsistent fact");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && (rejection.getMessage().contains("externalEntryRef")
                        || rejection.getMessage().contains("outside the")
                        || rejection.getMessage().contains("does not resolve")),
                what + ": the LuaJIT rejection names the unresolved entry: "
                    + rejection.getMessage());
        }
        try {
            JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                "Probe", fixture.surface());
            fail(what + ": the JVM emitter rejects the inconsistent fact");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && (rejection.getMessage().contains("externalEntryRef")
                        || rejection.getMessage().contains("outside the")
                        || rejection.getMessage().contains("does not resolve")),
                what + ": the JVM rejection names the unresolved entry: "
                    + rejection.getMessage());
        }
        try {
            SemanticOracle.executeProjectInits(project, tables, registries, null);
            fail(what + ": the oracle rejects the inconsistent fact");
        } catch (RuntimeException rejection) {
            check(rejection.getMessage() != null
                    && (rejection.getMessage().contains("externalEntryRef")
                        || rejection.getMessage().contains("outside the closure")
                        || rejection.getMessage().contains("producer defect")),
                what + ": the oracle rejection names the unresolved entry: "
                    + rejection.getMessage());
        }
    }

    /**
     * The landed rejection of a {@code RETAINED_ABI} external: both
     * production emitters refuse to emit a call arm for it (the retained
     * per-module ABI surface has no place in the one project artifact).
     * The oracle's host request seam is outside this seed's subject.
     */
    private static void assertRetainedOwnerRejected(String what,
            ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, Fixture fixture) {
        try {
            LuaSemanticEmitter.emitProductionProject(project, tables, registries,
                fixture.surface());
            fail(what + ": the LuaJIT emitter rejects the retained-ABI external");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && rejection.getMessage().contains("RETAINED_ABI"),
                what + ": the LuaJIT rejection names the retained execution owner: "
                    + rejection.getMessage());
        }
        try {
            JvmSemanticEmitter.emitProductionProject(project, tables, registries,
                "Probe", fixture.surface());
            fail(what + ": the JVM emitter rejects the retained-ABI external");
        } catch (IllegalStateException rejection) {
            check(rejection.getMessage() != null
                    && rejection.getMessage().contains("RETAINED_ABI"),
                what + ": the JVM rejection names the retained execution owner: "
                    + rejection.getMessage());
        }
    }

    /**
     * The production arm's fail-closed E6005 {@code SHARED_EMITTER_COVERAGE}
     * mapping: both target arms wrap the emitter call, a rejection becomes
     * the registered E6005 diagnostic carrying no artifact, and the staging
     * surface is reached only after a successful emission — so the
     * hand-built inconsistent facts above fail closed with E6005
     * {@code SHARED_EMITTER_COVERAGE} and stage nothing. The mapping is
     * structural in the production unit (the emitters' own rejections are
     * asserted above); this pin keeps it load-bearing.
     */
    private static void testProductionMapping() throws Exception {
        System.out.println("-- the production arm's E6005 SHARED_EMITTER_COVERAGE "
            + "mapping of an emitter rejection --");
        String source = Files.readString(
            Path.of("deal", "module", "ProductionProjectEmission.java"),
            StandardCharsets.UTF_8);
        check(countOccurrences(source, "catch (IllegalStateException emitterGap)") == 2,
            "both target arms catch the emitter rejection");
        check(countOccurrences(source,
                "sharedEmitterCoverage(project.entryModule().path(),") == 2,
            "both target arms map the rejection through the E6005 helper");
        check(countOccurrences(source, "emitterGap, invocation)), null);") == 2,
            "the mapped failure carries no artifact (nothing stages)");
        check(source.contains("FailureContractRegistry.e6005")
                && source.contains(
                    "\"ProductionProjectEmission \" + SHARED_EMITTER_COVERAGE"),
            "the mapping is the registered E6005 SHARED_EMITTER_COVERAGE rule");
        int lastCatch = source.lastIndexOf("catch (IllegalStateException emitterGap)");
        int staging = source.indexOf("stager.stage(");
        check(lastCatch >= 0 && staging > lastCatch,
            "the staging surface is reached only after a successful emission");
    }

    private static int countOccurrences(String haystack, String needle) {
        int count = 0;
        int index = haystack.indexOf(needle);
        while (index >= 0) {
            count++;
            index = haystack.indexOf(needle, index + needle.length());
        }
        return count;
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n")
                + " stderr=" + stderr.replace("\n", "\\n");
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

    private static ProcessOutcome runProcess(List<String> command, Path workDir)
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
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
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

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Cross-Module Call Realization Tests "
            + "(ISSUE-0654) ===\n");
        testLoweringCellShapes();
        testOracleEntryEvents();
        testFailingCalleeRestoresContext();
        testThreeConsumerTraceEquality();
        testProductionArtifactsAndSidecars();
        testFailClosedSeeds();
        testProductionMapping();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Cross-Module Call Realization Tests Passed ===");
    }
}
