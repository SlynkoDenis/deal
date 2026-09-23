package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.ValueId;

import java.lang.reflect.Method;
import java.lang.reflect.Parameter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0640: {@code LuaSemanticEmitter.emitProductionProject} — the
 * production project entry
 * ({@code production-project-emission-and-atomic-cutover} P1/P3 and the
 * production LuaJIT emission contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2 and the
 * production LuaJIT emission contract).
 *
 * <ol>
 *   <li>the entry consumes only the validated {@link ExecutableLoweredProject},
 *       the per-module block-membership tables, the per-module class-factory
 *       registries, and the compile's host declaration surface (the
 *       declared-map source of the {@code MODULE_IMPORT(HOST)} load) — no
 *       AST, no checker result, no route input, no extern-C
 *       generated-module map, and no identity index;</li>
 *   <li>the artifact is exactly one Lua chunk carrying the whole closure
 *       (the prelude once, every module's function factories, adapter
 *       thunks, and detached class-default functions, then each module's
 *       init walk in dependency order) with the trace protocol suppressed
 *       (no event output, no {@code R|} terminal) and the production
 *       terminal applying;</li>
 *   <li>the entry module's {@code ENTRY_INVOKE} delegation runs exactly
 *       once per chunk execution while every non-entry module's
 *       {@code ENTRY_INVOKE} and its delegated {@code CALL} stay skipped,
 *       observable through a
 *       {@code std/console.log} effect;</li>
 *   <li>the artifact carries the module export-surface registry (one
 *       surface per module keyed by module identity, written by
 *       {@code EXPORT_PUBLISH}) and the production chunk returns the entry
 *       module's surface; the executed chunk's surfaces hold each module's
 *       exports (the T1 dependency);</li>
 *   <li>the chunk is deployed with the runtime ({@code deal/runtime.lua},
 *       {@code std/*.lua}) and executes under {@code luajit}: a
 *       covered-construct fixture exits 0 with empty output, a
 *       conversion-overflow fixture exits 1 with
 *       {@code DEAL_ERROR_CODE: E8004} on stdout;</li>
 *   <li>repeated emission over identical inputs is byte-identical, and
 *       {@code emitProject}/{@code emitProductionModule} keep their
 *       signatures and behavior.</li>
 * </ol>
 */
public class LuaProductionProjectEmissionTest {

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
    // Fixtures: two-module projects (the implementation import makes the
    // closure carry two modules without any cross-module call)
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId APP = new ModuleId("app");

    private static final String LIB_SOURCE = """
        export class Counter {
          n: int = 0;
        }

        export function add(a: int, b: int): int {
          return a + b;
        }

        export function twice(x: int): int {
          return x * 2;
        }
        """;

    /**
     * The observable one-main probe: {@code main} publishes one
     * {@code std/console.log} effect byte line per execution, and the
     * entry module also exports {@code label} so its surface carries more
     * than the delegated entry.
     */
    private static final String CONSOLE_APP_SOURCE = """
        import * as lib from "./lib"
        import * as console from "std/console"

        export function main(): null {
          console.log("PROBE|MAIN-ONCE");
          return null;
        }

        export function label(): string {
          return "app";
        }
        """;

    /**
     * The non-entry-main probe fixture: {@code lib} exports its own
     * {@code main} with an observable effect, so the fixture proves the
     * production chunk delegates the entry module's {@code ENTRY_INVOKE}
     * only (lib's delegation op and its delegated CALL stay skipped).
     */
    private static final String LIB_WITH_MAIN_SOURCE = """
        import * as console from "std/console"

        export function add(a: int, b: int): int {
          return a + b;
        }

        export function main(): null {
          console.log("PROBE|LIB-MAIN");
          return null;
        }
        """;

    /** The covered-construct fixture: runs clean with no output. */
    private static final String QUIET_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          return null;
        }

        export function label(): string {
          return "app";
        }
        """;

    /** The conversion-overflow fixture: E8004 at execution. */
    private static final String OVERFLOW_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let x: int = 2147483647 + 1;
          return null;
        }

        export function label(): string {
          return "app";
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    /** The release-owned production invocation (the epic's production record). */
    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(String appSource) throws Exception {
        return compileProject(LIB_SOURCE, appSource);
    }

    private static Fixture compileProject(String libSource, String appSource)
            throws Exception {
        Path root = Files.createTempDirectory("lua-production-project");
        writeFileIn(root, "src/lib.deal", libSource);
        writeFileIn(root, "src/app.deal", appSource);
        Path entry = root.resolve("src/app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, null, List.of(root.resolve("src").toAbsolutePath()), null);
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: " + detail
                + " / " + orchestrator.diagnostics());
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), new LinkedHashMap<>(),
            new LinkedHashMap<>());
    }

    /** The one project lowering over the real checked project. */
    private static SemanticLowerer.ProjectLoweringResult lower(Fixture project) {
        return SemanticLowerer.lowerProject(invocation(), project.checkedProject(),
            project.index(), project.manifests(), project.surface(),
            project.declarationIdentities(), project.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                project.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** One module's declared exports in declaration order (the op order). */
    private record ExportEntry(String name, String spec, long valueId) {
    }

    private static List<ExportEntry> exportsOf(LoweredModuleUnit unit) {
        List<ExportEntry> entries = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.EXPORT_PUBLISH) {
                continue;
            }
            KindPayload.ExportPublishPayload payload =
                (KindPayload.ExportPublishPayload) op.payload();
            entries.add(new ExportEntry(payload.name(),
                payload.descriptor().canonicalSpecText(),
                ((ValueId) payload.value()).id()));
        }
        return entries;
    }

    // =========================================================================
    // 1. The entry's signature: project + tables + registries, nothing else
    // =========================================================================

    private static void testEntrySignatureAndInputs() throws Exception {
        System.out.println("-- the production project entry consumes only the "
            + "validated project, the tables, and the registries --");

        Method entry = LuaSemanticEmitter.class.getDeclaredMethod("emitProductionProject",
            ExecutableLoweredProject.class, Map.class, Map.class,
            HostDeclarationSurface.class);
        check(java.lang.reflect.Modifier.isStatic(entry.getModifiers())
                && java.lang.reflect.Modifier.isPublic(entry.getModifiers()),
            "emitProductionProject is a public static entry");
        checkEq(String.class, entry.getReturnType(),
            "the entry returns the one project artifact source text");

        Class<?>[] parameters = entry.getParameterTypes();
        checkEq(List.of(ExecutableLoweredProject.class, Map.class, Map.class,
                HostDeclarationSurface.class),
            List.of(parameters),
            "the entry takes exactly the validated project, the tables, the "
                + "registries, and the host declaration surface");
        for (Parameter parameter : entry.getParameters()) {
            if (parameter.getType() == Map.class) {
                checkEq("java.util.Map", parameter.getType().getTypeName(),
                    "the tables/registries parameters are the per-module maps");
            }
        }
        List<String> genericTypes = new ArrayList<>();
        for (java.lang.reflect.Type type : entry.getGenericParameterTypes()) {
            genericTypes.add(type.getTypeName());
        }
        checkEq(List.of(
                "deal.semantic.ir.ExecutableLoweredProject",
                "java.util.Map<deal.semantic.ir.ModuleId, "
                    + "deal.semantic.ir.StructuredBodyTable>",
                "java.util.Map<deal.semantic.ir.ModuleId, "
                    + "deal.semantic.ir.ClassFactoryRegistry>",
                "deal.semantic.HostDeclarationSurface"),
            genericTypes,
            "the entry's declared inputs are exactly the project lowering result's "
                + "tables and registries plus the host declaration surface");

        for (Parameter parameter : entry.getParameters()) {
            String typeName = parameter.getType().getName();
            for (String forbidden : List.of("deal.ast.", "deal.checker.",
                    "deal.parser.", "Route", "MigrationPlanner", "CapabilityRegistry",
                    "HostModuleDeclarations", "FfiGenerated",
                    "CanonicalModuleIdentity", "CheckResult", "ProgramNode")) {
                check(!typeName.contains(forbidden),
                    "emitProductionProject takes no " + forbidden + " input: "
                        + typeName);
            }
        }

        // The pre-existing entries keep their signatures.
        Method trace = LuaSemanticEmitter.class.getDeclaredMethod("emitProject",
            ExecutableLoweredProject.class, Map.class, Map.class);
        checkEq(String.class, trace.getReturnType(),
            "emitProject keeps its signature and return type");
        Method module = LuaSemanticEmitter.class.getDeclaredMethod("emitProductionModule",
            deal.semantic.ir.LoweredModuleUnit.class,
            deal.semantic.ir.StructuredBodyTable.class, boolean.class);
        checkEq(String.class, module.getReturnType(),
            "emitProductionModule keeps its signature and return type");

        // The entry's null guards: the four declared inputs are required.
        try {
            LuaSemanticEmitter.emitProductionProject(null, Map.of(), Map.of(),
                new HostDeclarationSurface(Map.of()));
            fail("a null project is rejected");
        } catch (NullPointerException expected) {
            passed++;
        } catch (Exception unexpected) {
            fail("a null project fails with "
                + unexpected.getClass().getSimpleName() + ", not NullPointerException");
        }
    }

    // =========================================================================
    // 2. The emitted chunk: one artifact, trace suppressed, the terminal
    // =========================================================================

    private static void testEmittedChunkText() throws Exception {
        System.out.println("-- the emitted production chunk: one artifact, the trace "
            + "protocol suppressed, the DEAL_ERROR_CODE terminal --");
        Fixture fixture = compileProject(CONSOLE_APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(List.of(LIB, APP), List.copyOf(project.modules().keySet()),
                "the closure carries the two modules in dependency order");
            checkEq(APP, project.entryModule(), "the entry module is app");

            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());

            // Exactly one chunk: one header, one prelude, one deferred main,
            // one entry-surface return.
            checkEq(1, countOccurrences(lua,
                    "-- deal.semantic-ir/1 shared LuaJIT artifact"),
                "the artifact carries exactly one chunk header");
            checkEq(1, countOccurrences(lua, "-- ==== shared runtime prelude ===="),
                "the artifact carries the shared runtime prelude exactly once");
            checkEq(1, countOccurrences(lua, "__dealMain = function()"),
                "the artifact declares exactly one deferred main");
            checkEq(1, countOccurrences(lua,
                    "local __mainOk, __mainErr = __dealMain()"),
                "the deferred main is driven exactly once at load");
            checkEq(1, countOccurrences(lua, "return __exportSurfaces[\"app\"]\n"),
                "the production chunk returns the entry module's surface once");

            // The trace protocol is suppressed: no event helper output and no
            // protocol terminal.
            check(lua.contains("__ev = function() end"),
                "the trace event helper is the production no-op");
            check(!lua.contains("io.stderr:write(\"R|"),
                "the artifact carries no R| terminal writer");
            check(!lua.contains("io.stderr:write(\"F|"),
                "the artifact carries no F| event writer");
            check(!lua.contains("\"R|success|null\""),
                "the artifact carries no success terminal text");
            String trace = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            check(trace.contains("io.stderr:write(\"R|success|null\\n\")"),
                "emitProject keeps its trace terminal (the entry differs only by mode)");

            // The production terminal: code line + exit 1 on a DEAL failure,
            // rethrow of a non-DEAL failure, silence on success.
            check(lua.contains("if type(__mainErr) == \"table\" and __mainErr.__d then"),
                "the terminal discriminates the DEAL failure carrier");
            check(lua.contains("print(\"DEAL_ERROR_CODE: \"..__mainErr.code)"),
                "the terminal publishes the retained DEAL_ERROR_CODE line on stdout");
            check(lua.contains("error(__mainErr, 0)"),
                "the terminal rethrows a non-DEAL failure");
            check(lua.contains("os.exit(1)"),
                "the terminal exits 1 after the failure line");

            // The module surface registry: one surface per module keyed by the
            // module identity, created before the walks, written by
            // EXPORT_PUBLISH in declaration order.
            checkEq(1, countOccurrences(lua,
                    "__exportSurfaces = __exportSurfaces or {}\n"),
                "the chunk declares the chunk-global registry exactly once");
            checkEq(List.of(
                    "__exportSurfaces[\"lib\"] = __exportSurfaces[\"lib\"] or {}",
                    "__exportSurfaces[\"app\"] = __exportSurfaces[\"app\"] or {}"),
                luaSurfaceCreations(lua),
                "one surface per closure module keyed by the dotted module path, in "
                    + "closure order");
            List<String> expectedWrites = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                for (ExportEntry entry : exportsOf(project.modules().get(moduleId))) {
                    expectedWrites.add("__exportSurfaces[\"" + moduleId.path() + "\"][\""
                        + entry.name() + "\"] = {__kind = \"function\", sig = \""
                        + entry.spec() + "\", f = __unfn(S.v" + entry.valueId() + ")}");
                }
            }
            checkEq(4, expectedWrites.size(),
                "the fixture declares four exports (lib: add, twice; app: main, label)");
            int previous = lua.indexOf("__exportSurfaces = __exportSurfaces or {}");
            for (String write : expectedWrites) {
                checkEq(1, countOccurrences(lua, write),
                    "the artifact publishes " + write);
                int at = lua.indexOf(write);
                check(at > previous, "the publications run in declaration order: " + write);
                previous = at;
            }
            int walksAt = lua.indexOf("__dealMain = function()");
            check(previous > walksAt,
                "every publication is inside the module walks, after the registry");

            // The init walks run in dependency order, each under its own tag.
            int libWalk = lua.indexOf("__module = \"lib\"", walksAt);
            int appWalk = lua.indexOf("__module = \"app\"", walksAt);
            check(libWalk > walksAt && appWalk > libWalk,
                "the module walks run in dependency order under their own __module tag");

            // The whole closure is present: every module's factories before the
            // walks, and every detached class-default function of the closure —
            // a pre-declared chunk-level local assigned in the preamble (the
            // pre-declaration precedes the factories, so a construction inside a
            // function body resolves the local instead of a nil global).
            List<String> defaultNames = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                for (SemanticOp op : project.modules().get(moduleId).ops()) {
                    if (op.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        defaultNames.add("D" + op.opId().id());
                    }
                }
            }
            String predeclaration = "local " + String.join(", ", defaultNames)
                + "\n";
            int predeclarationAt = defaultNames.isEmpty() ? -1
                : lua.indexOf(predeclaration);
            if (!defaultNames.isEmpty()) {
                check(predeclarationAt >= 0 && predeclarationAt < walksAt,
                    "the chunk pre-declares the detached class-default locals before "
                        + "the walks: " + predeclaration.trim());
            }
            int classDefaults = 0;
            for (ModuleId moduleId : project.modules().keySet()) {
                LoweredModuleUnit unit = project.modules().get(moduleId);
                for (deal.semantic.ir.LoweredFunction function
                        : unit.functions().values()) {
                    String factory = "F" + function.functionId().id() + " = function(";
                    int factoryAt = lua.indexOf(factory);
                    check(factoryAt >= 0 && factoryAt < walksAt,
                        "the closure carries the factory of " + moduleId.path() + "#"
                            + function.functionId());
                }
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() != SemanticOpKind.CLASS_DEFAULT) {
                        continue;
                    }
                    classDefaults++;
                    String defaultFn = "D" + op.opId().id() + " = function()";
                    int defaultAt = lua.indexOf(defaultFn);
                    check(defaultAt > predeclarationAt && defaultAt < walksAt,
                        "the closure carries the detached class-default function "
                            + defaultFn + " assigned after its pre-declaration and "
                            + "before the walks");
                }
            }
            check(classDefaults > 0,
                "the fixture exercises the detached class-default surface (Counter.n)");

            // Determinism: byte-identical repeated emission.
            checkEq(lua, LuaSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), fixture.surface()),
                "the repeated production project emission is byte-identical");

            // The tables/registries inputs are required.
            try {
                LuaSemanticEmitter.emitProductionProject(project, null,
                    result.registries(), fixture.surface());
                fail("a null tables map is rejected");
            } catch (NullPointerException expected) {
                passed++;
            }
            try {
                LuaSemanticEmitter.emitProductionProject(project, result.tables(), null,
                    fixture.surface());
                fail("a null registries map is rejected");
            } catch (NullPointerException expected) {
                passed++;
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. Real luajit: the observable one-main probe, the clean run, and the
    //    conversion-overflow terminal
    // =========================================================================

    private static void testUnderLuaJit() throws Exception {
        System.out.println("-- the production chunk under real luajit: the one-main "
            + "observable, the clean run, and the E8004 terminal --");

        // (a) The observable one-main probe: main's console.log effect appears
        //     exactly once, and the trace protocol publishes nothing on stderr.
        Fixture fixture = compileProject(CONSOLE_APP_SOURCE);
        Path workspace = Files.createTempDirectory("lua-production-project-run");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the console fixture lowers: " + result.diagnostics());
                return;
            }
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                fixture.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            ProcessOutcome run = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), workspace);
            checkEq(0, run.exitCode(),
                "the console fixture exits 0: stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
            checkEq("PROBE|MAIN-ONCE\n", run.stdout(),
                "the entry main runs exactly once (one observable effect byte line)");
            checkEq("", run.stderr(),
                "the production chunk publishes no trace protocol on stderr");
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }

        // (b) The covered-construct fixture: exit 0 with empty output.
        Fixture quiet = compileProject(QUIET_APP_SOURCE);
        Path quietWorkspace = Files.createTempDirectory("lua-production-project-quiet");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(quiet);
            if (result.project() == null) {
                fail("the quiet fixture lowers: " + result.diagnostics());
                return;
            }
            Path artifact = quietWorkspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                quiet.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(quietWorkspace);
            ProcessOutcome run = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), quietWorkspace);
            checkEq(0, run.exitCode(),
                "the covered-construct fixture exits 0: stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
            checkEq("", run.stdout(), "the covered-construct fixture is silent on stdout");
            checkEq("", run.stderr(), "the covered-construct fixture is silent on stderr");
        } finally {
            deleteRecursively(quietWorkspace);
            deleteRecursively(quiet.root());
        }

        // (c) The conversion-overflow fixture: exit 1, DEAL_ERROR_CODE: E8004
        //     on stdout (never a trace terminal).
        Fixture overflow = compileProject(OVERFLOW_APP_SOURCE);
        Path overflowWorkspace = Files.createTempDirectory("lua-production-project-ovf");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(overflow);
            if (result.project() == null) {
                fail("the overflow fixture lowers: " + result.diagnostics());
                return;
            }
            Path artifact = overflowWorkspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                overflow.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(overflowWorkspace);
            ProcessOutcome run = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), overflowWorkspace);
            checkEq(1, run.exitCode(),
                "the conversion-overflow fixture exits 1: stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
            check(run.stdout().contains("DEAL_ERROR_CODE: E8004\n"),
                "the overflow publishes the retained DEAL_ERROR_CODE: E8004 line on "
                    + "stdout: " + escaped(run.stdout()));
            checkEq("", run.stderr(),
                "the overflow publishes no trace protocol on stderr");
        } finally {
            deleteRecursively(overflowWorkspace);
            deleteRecursively(overflow.root());
        }
    }

    // =========================================================================
    // 4. The T1 dependency: the executed chunk's per-module surfaces hold
    //    each module's exports
    // =========================================================================

    private static void testExecutedSurfaces() throws Exception {
        System.out.println("-- the executed chunk's per-module surfaces hold each "
            + "module's exports (the T1 dependency) --");
        Fixture fixture = compileProject(QUIET_APP_SOURCE);
        Path workspace = Files.createTempDirectory("lua-production-project-surface");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), fixture.surface()),
                StandardCharsets.UTF_8);

            List<String> modules = new ArrayList<>();
            List<List<ExportEntry>> entries = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                modules.add(moduleId.path());
                entries.add(exportsOf(project.modules().get(moduleId)));
            }
            Path probe = workspace.resolve("surface-probe.lua");
            Files.writeString(probe, luaSurfaceProbe(artifact, modules, entries),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            ProcessOutcome run = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the executed chunk's registry carries one surface per module keyed by "
                    + "the dotted module path with the declared entries in declaration "
                    + "order and the published callable: exit=" + run.exitCode()
                    + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 5. Every non-entry module's ENTRY_INVOKE delegation stays skipped
    // =========================================================================

    private static void testNonEntryMainStaysSkipped() throws Exception {
        System.out.println("-- every non-entry module's ENTRY_INVOKE delegation stays "
            + "skipped (the lib main never runs) --");
        Fixture fixture = compileProject(LIB_WITH_MAIN_SOURCE, CONSOLE_APP_SOURCE);
        Path workspace = Files.createTempDirectory("lua-production-project-nonentry");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            // The non-vacuity check: both units carry their own lowered
            // ENTRY_INVOKE delegation op, so the skip is exercised.
            int libEntryOps = 0;
            int appEntryOps = 0;
            for (SemanticOp op : project.modules().get(LIB).ops()) {
                if (op.kind() == SemanticOpKind.ENTRY_INVOKE) {
                    libEntryOps++;
                }
            }
            for (SemanticOp op : project.modules().get(APP).ops()) {
                if (op.kind() == SemanticOpKind.ENTRY_INVOKE) {
                    appEntryOps++;
                }
            }
            checkEq(1, libEntryOps,
                "the fixture's lib unit carries its own ENTRY_INVOKE delegation op");
            checkEq(1, appEntryOps,
                "the fixture's entry unit carries its ENTRY_INVOKE delegation op");

            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());
            checkEq(1, countOccurrences(lua, "\"START\", \"ENTRY_INVOKE\""),
                "the production chunk emits exactly one ENTRY_INVOKE delegation "
                    + "(the entry module's)");

            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, lua, StandardCharsets.UTF_8);
            deployRuntime(workspace);
            ProcessOutcome run = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), workspace);
            checkEq(0, run.exitCode(),
                "the non-entry-main fixture exits 0: stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
            checkEq("PROBE|MAIN-ONCE\n", run.stdout(),
                "the entry main runs exactly once and the non-entry main runs not "
                    + "at all");
            checkEq("", run.stderr(),
                "the non-entry-main fixture publishes no trace protocol on stderr");
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Driver sources
    // =========================================================================

    /**
     * The Lua surface probe: the chunk's returned value is the entry
     * module's surface, the registry carries exactly one surface per
     * closure module keyed by the dotted module path, each surface holds
     * its declared exports with the landed entry shape in declaration
     * order, and the published callable runs.
     */
    private static String luaSurfaceProbe(Path artifact, List<String> modules,
            List<List<ExportEntry>> entries) {
        StringBuilder lua = new StringBuilder();
        lua.append("local __expected = {\n");
        for (int i = 0; i < modules.size(); i++) {
            lua.append("  {module = ").append(luaString(modules.get(i)))
                .append(", entries = {\n");
            for (ExportEntry entry : entries.get(i)) {
                lua.append("    {name = ").append(luaString(entry.name()))
                    .append(", sig = ").append(luaString(entry.spec())).append("},\n");
            }
            lua.append("  }},\n");
        }
        lua.append("}\n");
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __returned = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("local __count = 0\n");
        lua.append("for __ in pairs(__exportSurfaces) do __count = __count + 1 end\n");
        lua.append("if __count ~= ").append(modules.size())
            .append(" then __fail(\"the registry carries \"..__count..\" surfaces\") end\n");
        lua.append("if __returned ~= __exportSurfaces[")
            .append(luaString(modules.get(modules.size() - 1)))
            .append("] then __fail(\"the chunk returned no entry-module surface\") end\n");
        lua.append("for _, __m in ipairs(__expected) do\n");
        lua.append("  local __surface = __exportSurfaces[__m.module]\n");
        lua.append("  if type(__surface) ~= \"table\" then __fail(\"no surface for \"..__m.module) end\n");
        lua.append("  local __held = 0\n");
        lua.append("  for __ in pairs(__surface) do __held = __held + 1 end\n");
        lua.append("  if __held ~= #__m.entries then __fail(__m.module..\" holds \"..__held..\" entries\") end\n");
        lua.append("  local __order = {}\n");
        lua.append("  for _, __e in ipairs(__m.entries) do\n");
        lua.append("    local __entry = __surface[__e.name]\n");
        lua.append("    if type(__entry) ~= \"table\" then __fail(\"no entry \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("    if __entry.__kind ~= \"function\" then __fail(\"entry kind \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("    if __entry.sig ~= __e.sig then __fail(\"entry sig \"..__m.module..\"#\"..__e.name..\": \"..tostring(__entry.sig)) end\n");
        lua.append("    if type(__entry.f) ~= \"function\" then __fail(\"entry callable \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("  end\n");
        lua.append("end\n");
        lua.append("local __okCall, __value = pcall(__exportSurfaces[\"lib\"][\"add\"].f, 2, 3)\n");
        lua.append("if not __okCall then __fail(\"the published callable failed: \"..tostring(__value)) end\n");
        lua.append("if __value ~= 5 then __fail(\"the published callable returned \"..tostring(__value)) end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /** The emitted Lua surface-creation statements, in text order. */
    private static List<String> luaSurfaceCreations(String text) {
        List<String> lines = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            if (line.startsWith("__exportSurfaces[\"")
                    && line.contains("\"] = __exportSurfaces[\"")) {
                lines.add(line);
            }
        }
        return lines;
    }

    private static String escaped(String text) {
        return text.replace("\n", "\\n");
    }

    private static String luaString(String value) {
        StringBuilder text = new StringBuilder("\"");
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '"' -> text.append("\\\"");
                case '\\' -> text.append("\\\\");
                case '\n' -> text.append("\\n");
                default -> text.append(c);
            }
        }
        return text.append('"').toString();
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + 1);
        }
        return count;
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    /**
     * Deploys the unchanged runtime/stdlib copies next to the emitted chunk
     * (the production artifact set the compile publishes): the executed
     * workspace carries {@code deal/runtime.lua} and every {@code std/*.lua}.
     */
    private static void deployRuntime(Path workspace) throws Exception {
        Path runtime = Path.of("deal", "runtime.lua");
        check(Files.isRegularFile(runtime),
            "the checkout runtime deal/runtime.lua is available for deployment");
        Path std = Path.of("std");
        check(Files.isDirectory(std),
            "the checkout stdlib surface std/ is available for deployment");
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(runtime, runtimeTarget);
        Path stdTarget = workspace.resolve("std");
        Files.createDirectories(stdTarget);
        try (var listing = Files.list(std)) {
            for (Path file : listing.sorted().toList()) {
                if (file.getFileName().toString().endsWith(".lua")) {
                    Files.copy(file, stdTarget.resolve(file.getFileName()));
                }
            }
        }
        check(Files.isRegularFile(runtimeTarget)
                && Files.isRegularFile(stdTarget.resolve("console.lua")),
            "the workspace carries the runtime and stdlib deployment copies");
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
        System.out.println("=== Lua Production Project Emission Tests (ISSUE-0640) ===\n");
        testEntrySignatureAndInputs();
        testEmittedChunkText();
        testUnderLuaJit();
        testExecutedSurfaces();
        testNonEntryMainStaysSkipped();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Lua Production Project Emission Tests Passed ===");
    }
}
