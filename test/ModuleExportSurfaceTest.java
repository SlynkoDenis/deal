package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.jvm.JvmSemanticEmitter;
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
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

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
 * ISSUE-0639: the module export-surface registry in both project-mode
 * sessions (the module-identity key)
 * ({@code production-project-emission-and-atomic-cutover} P2 and the
 * module export-surface contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2 and the
 * production LuaJIT/JVM emission contracts;
 * {@code semantic-ir-construct-coverage-cutover} K15 item 1).
 *
 * <ol>
 *   <li>the LuaJIT project session emits one chunk-global registry keyed by
 *       the module identity (the dotted module path), exactly one surface
 *       per module of the closure created idempotently before the module
 *       walks, and one {@code EXPORT_PUBLISH} write per declared export
 *       into the emitting module's surface with the landed entry shape
 *       ({@code __kind}/{@code sig}/{@code f}) in declaration order;</li>
 *   <li>{@code emitModule}, {@code emitProductionModule}, {@code emitProject}
 *       and the project session share the one registry shape; the
 *       production-mode chunk returns its own module's surface (the
 *       entry module's surface in project mode) and a trace-mode chunk
 *       keeps its protocol and returns no registry;</li>
 *   <li>the emitted Lua project chunk runs under {@code luajit}: the
 *       registry carries one surface per closure module keyed by the
 *       dotted module path, each surface holds its declared exports in
 *       declaration order with the landed entry shape, and a repeated or
 *       cross-chunk drive never wipes a published surface;</li>
 *   <li>the emitted JVM project class carries the same registry as one
 *       {@code JvmRuntime.Table} per module, created idempotently before
 *       the module walks, and {@code EXPORT_PUBLISH} writes the published
 *       {@code JvmRuntime.FunctionValue} carrier into the emitting
 *       module's table; the class compiles with
 *       {@code javac --release 25 -proc:none} against the compiler's
 *       runtime classes and runs under {@code java}, where the probe
 *       asserts the module keys, the declaration-order entries, the
 *       carrier type, and that a repeated {@code dealMain()} drive leaves
 *       every published surface intact;</li>
 *   <li>emission is deterministic: byte-identical repeated emission for
 *       identical input.</li>
 * </ol>
 */
public class ModuleExportSurfaceTest {

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
    // Fixture: a real two-module project without a cross-module call
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId APP = new ModuleId("app");

    private static final String LIB_SOURCE = """
        export function add(a: int, b: int): int {
          return a + b;
        }

        export function twice(x: int): int {
          return x * 2;
        }
        """;

    /**
     * The entry module imports the implementation module (so the closure
     * carries two modules) without any cross-module call: the module walk,
     * the two export surfaces, and the entry delegation are covered at
     * this boundary.
     */
    private static final String APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
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

    private static Fixture compileProject() throws Exception {
        Path root = Files.createTempDirectory("module-export-surface");
        writeFileIn(root, "src/lib.deal", LIB_SOURCE);
        writeFileIn(root, "src/app.deal", APP_SOURCE);
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
    // 1. The LuaJIT project session: the registry and the publication
    // =========================================================================

    private static void testLuaProjectSurfaceText() throws Exception {
        System.out.println("-- the LuaJIT project session: one surface per module "
            + "keyed by the module identity --");
        Fixture fixture = compileProject();
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

            String lua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());

            // The registry declaration, once.
            checkEq(1, countOccurrences(lua, "__exportSurfaces = __exportSurfaces or {}\n"),
                "the chunk declares the chunk-global registry exactly once");

            // Exactly one surface per module of the closure, keyed by the
            // module identity, created idempotently, in closure order.
            checkEq(List.of(
                    "__exportSurfaces[\"lib\"] = __exportSurfaces[\"lib\"] or {}",
                    "__exportSurfaces[\"app\"] = __exportSurfaces[\"app\"] or {}"),
                luaSurfaceCreations(lua),
                "the registry creates one surface per closure module keyed by the dotted "
                    + "module path with the idempotence guard, in closure order");
            int registryAt = lua.indexOf("__exportSurfaces = __exportSurfaces or {}");
            int walksAt = lua.indexOf("__dealMain = function()");
            check(registryAt >= 0 && walksAt > registryAt,
                "the registry and every surface are created before the module walks");

            // The publication writes: the landed entry shape, addressed to
            // the emitting module's surface, in declaration order.
            List<String> expectedWrites = new ArrayList<>();
            List<String> expectedOrder = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                LoweredModuleUnit unit = project.modules().get(moduleId);
                for (ExportEntry entry : exportsOf(unit)) {
                    expectedOrder.add(moduleId.path() + "#" + entry.name());
                    expectedWrites.add("__exportSurfaces[\"" + moduleId.path() + "\"][\""
                        + entry.name() + "\"] = {__kind = \"function\", sig = \""
                        + entry.spec() + "\", f = __unfn(S.v" + entry.valueId() + ")}");
                }
            }
            checkEq(List.of("lib#add", "lib#twice", "app#main", "app#label"),
                expectedOrder,
                "the fixture's declared exports are covered in declaration order "
                    + "(lib: add, twice; app: main, label)");
            for (String write : expectedWrites) {
                checkEq(1, countOccurrences(lua, write),
                    "the artifact publishes " + write);
            }
            int previous = -1;
            for (String write : expectedWrites) {
                int at = lua.indexOf(write);
                check(at > previous, "the publications run in declaration order: " + write);
                previous = at;
            }

            // No name-keyed chunk-global remains, and trace mode returns no
            // registry (the trace protocol is unchanged).
            check(!lua.contains("local __exports"), "the name-keyed chunk-global export "
                + "table is gone");
            check(!lua.contains("__exports["), "no publication targets the name-keyed "
                + "chunk-global table");
            check(!lua.contains("return __exportSurfaces"), "a trace-mode chunk keeps its "
                + "protocol and returns no registry");

            // Determinism: byte-identical repeated emission.
            checkEq(lua, LuaSemanticEmitter.emitProject(project, result.tables(),
                    result.registries()),
                "the repeated project emission is byte-identical");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The single-unit entries share the one registry shape
    // =========================================================================

    private static void testLuaModeRegistryShapes() throws Exception {
        System.out.println("-- emitModule / emitProductionModule / emitProject share "
            + "the one registry shape --");
        Fixture fixture = compileProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            StructuredBodyTable appTable = result.tables().get(APP);
            StructuredBodyTable libTable = result.tables().get(LIB);

            // The trace single-unit entries: one surface for their module.
            String traceApp = LuaSemanticEmitter.emitModule(appUnit, appTable);
            checkEq(List.of("__exportSurfaces[\"app\"] = __exportSurfaces[\"app\"] or {}"),
                luaSurfaceCreations(traceApp),
                "emitModule declares its one module's surface");
            check(traceApp.contains("__exportSurfaces[\"app\"][\"main\"] = "
                    + "{__kind = \"function\", sig = \"" + exportsOf(appUnit).get(0).spec()
                    + "\", f = __unfn("),
                "emitModule publishes through the registry surface");
            check(!traceApp.contains("return __exportSurfaces"),
                "emitModule is trace mode: it returns no registry");

            String traceLib = LuaSemanticEmitter.emitModule(libUnit, libTable);
            checkEq(List.of("__exportSurfaces[\"lib\"] = __exportSurfaces[\"lib\"] or {}"),
                luaSurfaceCreations(traceLib),
                "emitModule of another module keys its surface by that module's identity");

            // The production single-unit entries: the same registry shape
            // plus the one module's surface return.
            String productionApp = LuaSemanticEmitter.emitProductionModule(appUnit,
                appTable, true);
            checkEq(List.of("__exportSurfaces[\"app\"] = __exportSurfaces[\"app\"] or {}"),
                luaSurfaceCreations(productionApp),
                "emitProductionModule declares its one module's surface");
            check(productionApp.endsWith("return __exportSurfaces[\"app\"]\n"),
                "the production chunk returns its one module's surface (the "
                    + "retained-caller ABI)");
            checkEq(productionApp, LuaSemanticEmitter.emitProductionModule(appUnit,
                    appTable, true),
                "the repeated production emission is byte-identical");

            String productionLib = LuaSemanticEmitter.emitProductionModule(libUnit,
                libTable, false);
            checkEq(List.of("__exportSurfaces[\"lib\"] = __exportSurfaces[\"lib\"] or {}"),
                luaSurfaceCreations(productionLib),
                "a non-entry production module keys its surface by its own module identity");
            check(productionLib.endsWith("return __exportSurfaces[\"lib\"]\n"),
                "a non-entry production chunk returns its own module's surface");
            check(!productionLib.contains("ENTRY_INVOKE"),
                "a non-entry production module runs no entry delegation");

            checkEq(traceApp, LuaSemanticEmitter.emitModule(appUnit, appTable),
                "the repeated trace emission is byte-identical");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The LuaJIT project chunk under real luajit
    // =========================================================================

    private static void testLuaProjectArtifactExecution() throws Exception {
        System.out.println("-- the emitted LuaJIT project chunk runs under luajit --");
        Fixture fixture = compileProject();
        Path workspace = Files.createTempDirectory("module-export-surface-lua");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String lua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, lua, StandardCharsets.UTF_8);

            List<String> modules = new ArrayList<>();
            List<List<ExportEntry>> entries = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                modules.add(moduleId.path());
                entries.add(exportsOf(project.modules().get(moduleId)));
            }

            // (a) The execution probe: one surface per module, the landed
            //     entry shape, the published callable, and the cross-chunk
            //     idempotence guard.
            Path probe = workspace.resolve("surface-probe.lua");
            Files.writeString(probe, luaSurfaceProbe(artifact, modules, entries, "lib",
                "add", "2, 3", "5"), StandardCharsets.UTF_8);
            ProcessOutcome probeRun = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace);
            check(probeRun.exitCode() == 0 && probeRun.stdout().contains("PROBE-OK"),
                "the LuaJIT project chunk publishes one surface per module with the "
                    + "landed entry shapes and survives a repeated drive: exit="
                    + probeRun.exitCode() + " stdout="
                    + probeRun.stdout().replace("\n", "\\n") + " stderr="
                    + probeRun.stderr().replace("\n", "\\n"));

            // (b) The declaration-order write probe: an instrumented registry
            //     records every publication in execution order.
            Path orderProbe = workspace.resolve("order-probe.lua");
            Files.writeString(orderProbe, luaOrderProbe(artifact), StandardCharsets.UTF_8);
            ProcessOutcome orderRun = runProcess(List.of("luajit",
                orderProbe.toAbsolutePath().toString()), workspace);
            List<String> expectedOrder = new ArrayList<>();
            for (int i = 0; i < modules.size(); i++) {
                for (ExportEntry entry : entries.get(i)) {
                    expectedOrder.add(modules.get(i) + "#" + entry.name());
                }
            }
            check(orderRun.exitCode() == 0,
                "the order probe runs: exit=" + orderRun.exitCode() + " stdout="
                    + orderRun.stdout().replace("\n", "\\n") + " stderr="
                    + orderRun.stderr().replace("\n", "\\n"));
            checkEq(String.join(",", expectedOrder),
                orderRun.stdout().trim(),
                "each module's entries are published in declaration order into the "
                    + "registry keyed by the module identity");
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The production-mode chunk returns the entry module's surface
    // =========================================================================

    private static void testLuaProductionChunkReturn() throws Exception {
        System.out.println("-- the production-mode chunk returns the entry module's "
            + "surface (the retained-caller ABI) --");
        Fixture fixture = compileProject();
        Path workspace = Files.createTempDirectory("module-export-surface-return");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String production = LuaSemanticEmitter.emitProductionModule(
                project.modules().get(APP), result.tables().get(APP), true);
            Path artifact = workspace.resolve("app.lua");
            Files.writeString(artifact, production, StandardCharsets.UTF_8);

            Path probe = workspace.resolve("return-probe.lua");
            Files.writeString(probe, luaReturnProbe(artifact, APP.path(),
                exportsOf(project.modules().get(APP))),
                StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the production chunk's returned value is the entry module's surface "
                    + "with its declared exports: exit=" + run.exitCode() + " stdout="
                    + run.stdout().replace("\n", "\\n") + " stderr="
                    + run.stderr().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 5. The JVM project session: one JvmRuntime.Table per module
    // =========================================================================

    private static void testJvmSurfaceText() throws Exception {
        System.out.println("-- the JVM project session: one JvmRuntime.Table per "
            + "module, created idempotently before the walks --");
        Fixture fixture = compileProject();
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            JvmSemanticEmitter.EmissionResult emission = JvmSemanticEmitter.emitProject(
                project, result.tables(), result.registries());
            String source = emission.source();

            check(source.contains("static final java.util.LinkedHashMap<String, "
                    + "JvmRuntime.Table> EXPORT_SURFACES = new "
                    + "java.util.LinkedHashMap<>();"),
                "the emitted class carries the module surface registry");
            check(source.contains("static JvmRuntime.Table exportSurface(String module) {")
                    && source.contains("JvmRuntime.Table surface = "
                        + "EXPORT_SURFACES.get(module);")
                    && source.contains("EXPORT_SURFACES.put(module, surface);"),
                "the registry's surface lookup is the idempotent get-or-create");

            checkEq(List.of("    exportSurface(\"lib\");", "    exportSurface(\"app\");"),
                jvmSurfaceCreations(source),
                "every closure module's surface is created before the module walks");
            int creationsAt = source.indexOf("    exportSurface(\"");
            int walkAt = source.indexOf("    MODULE = \"lib\";");
            check(creationsAt >= 0 && walkAt > creationsAt,
                "the surface creation precedes the first module walk");

            int previous = -1;
            for (ModuleId moduleId : project.modules().keySet()) {
                for (ExportEntry entry : exportsOf(project.modules().get(moduleId))) {
                    String write = "exportSurface(\"" + moduleId.path() + "\").write(\""
                        + entry.name() + "\", v" + entry.valueId() + ");";
                    checkEq(1, countOccurrences(source, write),
                        "the artifact publishes " + write);
                    int at = source.indexOf(write);
                    check(at > previous, "the JVM publications run in declaration "
                        + "order: " + write);
                    previous = at;
                }
            }

            checkEq(emission.source(), JvmSemanticEmitter.emitProject(project,
                    result.tables(), result.registries()).source(),
                "the repeated project emission is byte-identical");

            // The production single-unit entry shares the one registry shape.
            JvmSemanticEmitter.EmissionResult production =
                JvmSemanticEmitter.emitProductionModule(project.modules().get(APP),
                    result.tables().get(APP), true, "Main");
            checkEq(List.of("    exportSurface(\"app\");"),
                jvmSurfaceCreations(production.source()),
                "the production single-unit emission keys its surface by its module "
                    + "identity");
            checkEq(production.source(), JvmSemanticEmitter.emitProductionModule(
                    project.modules().get(APP), result.tables().get(APP), true, "Main")
                    .source(),
                "the repeated production emission is byte-identical");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 6. The JVM project class under javac and java
    // =========================================================================

    private static void testJvmProjectArtifactExecution() throws Exception {
        System.out.println("-- the emitted JVM project class compiles and runs --");
        Fixture fixture = compileProject();
        Path workspace = Files.createTempDirectory("module-export-surface-jvm");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            JvmSemanticEmitter.EmissionResult emission = JvmSemanticEmitter.emitProject(
                project, result.tables(), result.registries());
            Path source = workspace.resolve(emission.className() + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);

            List<String> modules = new ArrayList<>();
            List<List<ExportEntry>> entries = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                modules.add(moduleId.path());
                entries.add(exportsOf(project.modules().get(moduleId)));
            }
            String driverName = "ModuleExportSurfaceProbe";
            Path driver = workspace.resolve(driverName + ".java");
            Files.writeString(driver, jvmProbeSource(emission.className(), driverName,
                modules, entries), StandardCharsets.UTF_8);

            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString(), driver.toAbsolutePath().toString()),
                workspace);
            check(javacRun.exitCode() == 0,
                "the emitted JVM project class compiles with javac --release 25 "
                    + "-proc:none: " + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome javaRun = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, driverName), workspace);
            check(javaRun.exitCode() == 0 && javaRun.stdout().contains("PROBE-OK"),
                "the executed artifact publishes one surface per module in declaration "
                    + "order with the FunctionValue carrier and survives a repeated "
                    + "dealMain() drive: exit=" + javaRun.exitCode() + " stdout="
                    + javaRun.stdout().replace("\n", "\\n") + " stderr="
                    + javaRun.stderr().replace("\n", "\\n"));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Driver sources
    // =========================================================================

    /**
     * The Lua execution probe: after the chunk runs, the registry carries
     * exactly one surface per closure module keyed by the dotted module
     * path, each surface holds its declared exports in the landed entry
     * shape, the published callable runs, and a second load of the same
     * chunk keeps the published surfaces (the idempotence guard).
     */
    private static String luaSurfaceProbe(Path artifact, List<String> modules,
            List<List<ExportEntry>> entries, String callModule, String callExport,
            String callArgs, String callResult) {
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
        lua.append("local __ok, __err = pcall(dofile, ")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if not __ok then __fail(\"the project chunk failed: \"..tostring(__err)) end\n");
        lua.append("local __count = 0\n");
        lua.append("for __ in pairs(__exportSurfaces) do __count = __count + 1 end\n");
        lua.append("if __count ~= ").append(modules.size())
            .append(" then __fail(\"the registry carries \"..__count..\" surfaces\") end\n");
        lua.append("for _, __m in ipairs(__expected) do\n");
        lua.append("  local __surface = __exportSurfaces[__m.module]\n");
        lua.append("  if type(__surface) ~= \"table\" then __fail(\"no surface for \"..__m.module) end\n");
        lua.append("  local __held = 0\n");
        lua.append("  for __ in pairs(__surface) do __held = __held + 1 end\n");
        lua.append("  if __held ~= #__m.entries then __fail(__m.module..\" holds \"..__held..\" entries\") end\n");
        lua.append("  for _, __e in ipairs(__m.entries) do\n");
        lua.append("    local __entry = __surface[__e.name]\n");
        lua.append("    if type(__entry) ~= \"table\" then __fail(\"no entry \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("    if __entry.__kind ~= \"function\" then __fail(\"entry kind \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("    if __entry.sig ~= __e.sig then __fail(\"entry sig \"..__m.module..\"#\"..__e.name..\": \"..tostring(__entry.sig)) end\n");
        lua.append("    if type(__entry.f) ~= \"function\" then __fail(\"entry callable \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("  end\n");
        lua.append("end\n");
        lua.append("local __okCall, __value = pcall(__exportSurfaces[")
            .append(luaString(callModule)).append("][").append(luaString(callExport))
            .append("].f, ").append(callArgs).append(")\n");
        lua.append("if not __okCall then __fail(\"the published callable failed: \"..tostring(__value)) end\n");
        lua.append("if __value ~= ").append(callResult)
            .append(" then __fail(\"the published callable returned \"..tostring(__value)) end\n");
        lua.append("local __before = {}\n");
        lua.append("for _, __m in ipairs(__expected) do __before[__m.module] = __exportSurfaces[__m.module] end\n");
        lua.append("local __ok2, __err2 = pcall(dofile, ")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if not __ok2 then __fail(\"the second load failed: \"..tostring(__err2)) end\n");
        lua.append("for _, __m in ipairs(__expected) do\n");
        lua.append("  if __exportSurfaces[__m.module] ~= __before[__m.module] then __fail(\"the second load replaced the surface \"..__m.module) end\n");
        lua.append("  for _, __e in ipairs(__m.entries) do\n");
        lua.append("    if __before[__m.module][__e.name] == nil then __fail(\"the second load wiped \"..__m.module..\"#\"..__e.name) end\n");
        lua.append("  end\n");
        lua.append("end\n");
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /**
     * The Lua declaration-order probe: an instrumented registry and
     * instrumented surfaces record every publication in execution order,
     * so the assertion is over the writes that really happen, not over the
     * emitted text.
     */
    private static String luaOrderProbe(Path artifact) {
        StringBuilder lua = new StringBuilder();
        lua.append("local __order = {}\n");
        lua.append("local function __surface(module)\n");
        lua.append("  return setmetatable({}, {__newindex = function(self, name, value)\n");
        lua.append("    __order[#__order + 1] = module..\"#\"..name\n");
        lua.append("    rawset(self, name, value)\n");
        lua.append("  end})\n");
        lua.append("end\n");
        lua.append("__exportSurfaces = setmetatable({}, {__newindex = function(self, module, surface)\n");
        lua.append("  rawset(self, module, __surface(module))\n");
        lua.append("end})\n");
        lua.append("local __ok, __err = pcall(dofile, ")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if not __ok then print(\"PROBE-FAIL: \"..tostring(__err)) os.exit(1) end\n");
        lua.append("print(table.concat(__order, \",\"))\n");
        return lua.toString();
    }

    /**
     * The Lua return probe (the production single-unit entry): the chunk's
     * return value is its one module's surface, reachable through the
     * registry under the module identity and carrying the declared
     * exports.
     */
    private static String luaReturnProbe(Path artifact, String module,
            List<ExportEntry> entries) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function __fail(message)\n");
        lua.append("  print(\"PROBE-FAIL: \"..message)\n");
        lua.append("  os.exit(1)\n");
        lua.append("end\n");
        lua.append("local __surface = dofile(")
            .append(luaString(artifact.toAbsolutePath().toString())).append(")\n");
        lua.append("if type(__surface) ~= \"table\" then __fail(\"the production chunk "
            + "returned \"..type(__surface)) end\n");
        lua.append("if __surface ~= __exportSurfaces[")
            .append(luaString(module)).append("] then __fail(\"the returned table is not "
            + "the module's registry surface\") end\n");
        lua.append("local __held = 0\n");
        lua.append("for __ in pairs(__surface) do __held = __held + 1 end\n");
        lua.append("if __held ~= ").append(entries.size())
            .append(" then __fail(\"the surface holds \"..__held..\" entries\") end\n");
        for (ExportEntry entry : entries) {
            lua.append("if type(__surface[").append(luaString(entry.name()))
                .append("]) ~= \"table\" or __surface[").append(luaString(entry.name()))
                .append("].__kind ~= \"function\" or __surface[")
                .append(luaString(entry.name())).append("].sig ~= \"")
                .append(entry.spec()).append("\" then __fail(\"the entry ")
                .append(entry.name()).append(" is not the landed shape\") end\n");
        }
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    /**
     * The generated Java probe (the default package, so it reaches the
     * emitted class's registry): the class's own {@code main} runs once,
     * the registry carries one surface per module keyed by the dotted
     * module path, each surface holds its declared exports in declaration
     * order with the {@code JvmRuntime.FunctionValue} carrier, and a
     * repeated {@code dealMain()} drive leaves every published surface
     * intact.
     */
    private static String jvmProbeSource(String className, String driverName,
            List<String> modules, List<List<ExportEntry>> entries) {
        StringBuilder source = new StringBuilder();
        source.append("public class ").append(driverName).append(" {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
        source.append("  }\n");
        source.append("  static void checkEntry(Object value, String spec, String what) {\n");
        source.append("    check(value instanceof deal.codegen.jvm.JvmRuntime.FunctionValue, "
            + "what + \" is a JvmRuntime.FunctionValue carrier; got \" + value);\n");
        source.append("    if (value instanceof deal.codegen.jvm.JvmRuntime.FunctionValue "
            + "carrier) {\n");
        source.append("      check(spec.equals(carrier.spec), what + \" carries its "
            + "canonical spec text; got \" + carrier.spec);\n");
        source.append("    } else {\n");
        source.append("      check(false, what + \" carries its canonical spec text; got "
            + "no carrier\");\n");
        source.append("    }\n");
        source.append("  }\n");
        source.append("  public static void main(String[] args) {\n");
        source.append("    ").append(className).append(".main(new String[0]);\n");
        source.append("    java.util.LinkedHashMap<String, deal.codegen.jvm.JvmRuntime.Table>"
            + " surfaces = ").append(className).append(".EXPORT_SURFACES;\n");
        source.append("    check(surfaces.size() == ").append(modules.size())
            .append(", \"one surface per module of the closure; got \" + surfaces.size());\n");
        source.append("    check(new java.util.ArrayList<>(surfaces.keySet())"
            + ".equals(java.util.List.of(").append(javaStringList(modules))
            .append(")), \"the registry is keyed by the dotted module path in closure "
            + "order; got \" + surfaces.keySet());\n");
        for (int i = 0; i < modules.size(); i++) {
            String module = modules.get(i);
            List<ExportEntry> moduleEntries = entries.get(i);
            List<String> names = new ArrayList<>();
            for (ExportEntry entry : moduleEntries) {
                names.add(entry.name());
            }
            source.append("    { deal.codegen.jvm.JvmRuntime.Table surface = surfaces.get(")
                .append(javaString(module)).append(");\n");
            source.append("      check(surface != null, ")
                .append(javaString("the surface of " + module + " exists")).append(");\n");
            source.append("      if (surface != null) {\n");
            source.append("        check(new java.util.ArrayList<>(surface.entries.keySet())"
                + ".equals(java.util.List.of(").append(javaStringList(names))
                .append(")), ").append(javaString("the module " + module
                    + " surface holds its declared exports in declaration order; got "))
                .append(" + surface.entries.keySet());\n");
            for (ExportEntry entry : moduleEntries) {
                source.append("        { Object value = surface.entries.get(")
                    .append(javaString(entry.name())).append(");\n");
                source.append("          checkEntry(value, ")
                    .append(javaString(entry.spec())).append(", ")
                    .append(javaString("the published " + module + "#" + entry.name()))
                    .append("); }\n");
            }
            source.append("      }\n    }\n");
        }
        source.append("    ").append(className).append(".dealMain();\n");
        source.append("    check(surfaces == ").append(className)
            .append(".EXPORT_SURFACES, \"the repeated dealMain() drive keeps the "
                + "registry instance\");\n");
        source.append("    check(surfaces.size() == ").append(modules.size())
            .append(", \"the repeated dealMain() drive keeps every surface; got \" + "
                + "surfaces.size());\n");
        for (int i = 0; i < modules.size(); i++) {
            String module = modules.get(i);
            source.append("    { deal.codegen.jvm.JvmRuntime.Table surface = surfaces.get(")
                .append(javaString(module)).append(");\n");
            source.append("      check(surface != null && surface.keys.contains(")
                .append(javaString(entries.get(i).get(0).name()))
                .append("), ").append(javaString("the repeated drive left the published "
                    + module + "#" + entries.get(i).get(0).name() + " intact")).append("); }\n");
        }
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" "
            + "+ failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
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

    /** The emitted JVM surface-creation statements, in text order. */
    private static List<String> jvmSurfaceCreations(String text) {
        List<String> lines = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            if (line.startsWith("    exportSurface(\"") && line.endsWith(");")
                    && !line.contains(").write(")) {
                lines.add(line);
            }
        }
        return lines;
    }

    private static String javaStringList(List<String> values) {
        StringBuilder text = new StringBuilder();
        for (int i = 0; i < values.size(); i++) {
            if (i > 0) {
                text.append(", ");
            }
            text.append(javaString(values.get(i)));
        }
        return text.toString();
    }

    private static String javaString(String value) {
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

        /** The combined output for diagnostics. */
        String output() {
            return "stdout=" + stdout.replace("\n", "\\n")
                + " stderr=" + stderr.replace("\n", "\\n");
        }
    }

    /**
     * The test's classpath entries resolved against the test process's
     * working directory: the emitted-artifact toolchain runs in an
     * isolated workspace directory, so a relative {@code build} entry
     * would not resolve there.
     */
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
        System.out.println("=== Module Export Surface Tests (ISSUE-0639) ===\n");
        testLuaProjectSurfaceText();
        testLuaModeRegistryShapes();
        testLuaProjectArtifactExecution();
        testLuaProductionChunkReturn();
        testJvmSurfaceText();
        testJvmProjectArtifactExecution();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Module Export Surface Tests Passed ===");
    }
}
