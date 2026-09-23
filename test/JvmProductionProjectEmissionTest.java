package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
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

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
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
 * ISSUE-0641: the JVM production project entry
 * {@code JvmSemanticEmitter.emitProductionProject(project, tables,
 * registries, className, declarationSurface)}
 * ({@code production-project-emission-and-atomic-cutover} P1/P2/P3 and the
 * production JVM emission contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2 and the
 * production JVM emission contract).
 *
 * <ol>
 *   <li>The entry consumes only the validated project, the per-module body
 *       tables and class-factory registries, the entry class name, and the
 *       host declaration surface; the artifact is one {@code public final
 *       class <className>} with {@code public static void main(String[])}
 *       and the {@code dealMain()} drive carrying the whole closure.</li>
 *   <li>The trace protocol is suppressed (the class enables no trace and
 *       carries no {@code R|} line), {@code main} drives {@code dealMain()}
 *       exactly once, and the production {@code DEAL_ERROR_CODE: <code>}
 *       terminal is the uncaught-DEAL-failure outcome.</li>
 *   <li>The class carries the module export-surface registry keyed by the
 *       module identity (one {@code JvmRuntime.Table} per module), written
 *       by {@code EXPORT_PUBLISH} in declaration order.</li>
 *   <li>The class name is used verbatim; the artifact compiles with
 *       {@code javac --release 25 -proc:none} against the compiler's
 *       runtime classes and runs under {@code java}.</li>
 *   <li>{@code emitProject} and {@code emitProductionModule} keep their
 *       signatures and behavior; repeated production emission is
 *       byte-identical.</li>
 * </ol>
 */
public class JvmProductionProjectEmissionTest {

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
     * The entry module imports the implementation module (the closure
     * carries two modules) without any cross-module call — that shape
     * belongs to the calls child — and the module walk order plus the one
     * {@code ENTRY_INVOKE} delegation of the entry module are observable
     * through the runtime's module-init state.
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

    /** The conversion/arithmetic overflow terminal fixture (E8004). */
    private static final String OVERFLOW_SOURCE = """
        export function main(): null {
          let x: int = 2147483647 + 1
          return null
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

    /** A real two-module checked project (lib plus the importing app entry). */
    private static Fixture compileProject() throws Exception {
        return compileProject(APP_SOURCE, "src/app.deal");
    }

    /** A real checked project with the given entry source and entry file. */
    private static Fixture compileProject(String entrySource, String entryRelative)
            throws Exception {
        Path root = Files.createTempDirectory("jvm-production-project");
        writeFileIn(root, "src/lib.deal", LIB_SOURCE);
        writeFileIn(root, entryRelative, entrySource);
        Path entry = root.resolve(entryRelative).toAbsolutePath();
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
    // 1. The one entry signature and the class-name use
    // =========================================================================

    private static void testEntrySignature() {
        System.out.println("-- the production project entry signature --");
        Method entry = null;
        for (Method method : JvmSemanticEmitter.class.getDeclaredMethods()) {
            if (method.getName().equals("emitProductionProject")) {
                entry = method;
            }
        }
        check(entry != null, "JvmSemanticEmitter publishes emitProductionProject");
        if (entry == null) {
            return;
        }
        check(Modifier.isPublic(entry.getModifiers()) && Modifier.isStatic(entry.getModifiers()),
            "emitProductionProject is public static");
        checkEq(JvmSemanticEmitter.EmissionResult.class, entry.getReturnType(),
            "emitProductionProject returns the emitted artifact");
        Class<?>[] parameters = entry.getParameterTypes();
        checkEq(List.of(
                ExecutableLoweredProject.class,
                Map.class,
                Map.class,
                String.class,
                HostDeclarationSurface.class),
            List.of(parameters),
            "emitProductionProject consumes exactly the validated project, the tables, "
                + "the registries, the entry class name, and the host declaration "
                + "surface");
        for (Class<?> parameter : parameters) {
            String name = parameter.getName();
            check(!name.startsWith("deal.ast.") && !name.startsWith("deal.checker.")
                    && !name.equals("deal.codegen.HostModuleDeclarations")
                    && !name.equals("deal.ffi.FfiGeneratedModule")
                    && !name.equals("deal.semantic.RoutePlanResult")
                    && !name.equals("deal.semantic.ModuleRoutePlan")
                    && !name.equals("deal.semantic.CapabilityRegistry"),
                "emitProductionProject takes no AST/checker/route/host/extern-C input: "
                    + name);
        }

        // The two landed entries keep their signatures.
        Method projectEntry = null;
        Method moduleEntry = null;
        for (Method method : JvmSemanticEmitter.class.getDeclaredMethods()) {
            if (method.getName().equals("emitProject")) {
                projectEntry = method;
            }
            if (method.getName().equals("emitProductionModule")) {
                moduleEntry = method;
            }
        }
        check(projectEntry != null && projectEntry.getParameterCount() == 3,
            "emitProject keeps its three-input signature");
        check(moduleEntry != null && moduleEntry.getParameterCount() == 4
                && moduleEntry.getParameterTypes()[2] == boolean.class
                && moduleEntry.getParameterTypes()[3] == String.class,
            "emitProductionModule keeps its four-input signature");
    }

    // =========================================================================
    // 2. The emitted production artifact text
    // =========================================================================

    private static void testEmittedTextShapes() throws Exception {
        System.out.println("-- the production artifact: one class, trace suppressed, "
            + "the whole closure, the surface registry --");
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
            String className = JvmBackend.classNameFor(project.entryModule().path());
            checkEq("App", className, "the entry class name derives from the entry path");

            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            String source = emission.source();
            checkEq(className, emission.className(), "the emission reports its class name");

            // One public final class with main and the dealMain drive.
            checkEq(1, countOccurrences(source, "public final class " + className + " {"),
                "the artifact is one public final class named for the className argument");
            List<String> imports = new ArrayList<>();
            for (String line : source.split("\n", -1)) {
                if (line.startsWith("import ")) {
                    imports.add(line);
                }
            }
            checkEq(List.of("import deal.codegen.jvm.JvmRuntime;",
                    "import deal.codegen.jvm.JvmJson;", "import java.util.List;"),
                imports,
                "the artifact imports only the compiler's runtime classes");
            check(source.contains("  public static void dealMain() {"),
                "the class carries the dealMain() drive");
            check(source.contains("  public static void main(String[] args) {"),
                "the class declares public static void main(String[])");
            checkEq(1, countOccurrences(source, "dealMain();"),
                "main drives dealMain() exactly once");
            check(!source.contains("SharedM"),
                "the production artifact does not use the shared conformance class name");

            // The trace protocol is suppressed.
            check(source.contains("JvmRuntime.setTraceEnabled(false);"),
                "the class disables the runtime trace protocol");
            check(!source.contains("setTraceEnabled(true)"),
                "the class enables no trace protocol");
            check(!source.contains("R|"),
                "the artifact carries no R| trace line");

            // The production terminal.
            check(source.contains("System.out.println(\"DEAL_ERROR_CODE: \" + e.code);"),
                "an uncaught DEAL failure publishes the DEAL_ERROR_CODE terminal");
            check(source.contains("System.exit(1);"),
                "an uncaught DEAL failure exits 1");
            check(!source.contains("DEAL_ERROR_SNAPSHOT"),
                "the artifact publishes no snapshot line (the lane composes it)");

            // The whole closure in dependency order: the two module walks,
            // and each module's function factories.
            int libWalk = source.indexOf("    MODULE = \"lib\";");
            int appWalk = source.indexOf("    MODULE = \"app\";");
            check(libWalk >= 0 && appWalk > libWalk,
                "the artifact walks every closure module in dependency order");
            LoweredModuleUnit appUnit = project.modules().get(APP);
            LoweredModuleUnit libUnit = project.modules().get(LIB);
            for (LoweredModuleUnit unit : List.of(libUnit, appUnit)) {
                for (var function : unit.functions().values()) {
                    check(source.contains("  static JvmRuntime.FunctionValue F"
                            + function.functionId().id() + "("),
                        "the artifact carries the factory of " + unit.moduleId().path()
                            + "#" + function.functionId().id());
                }
            }

            // The one entry delegation: the entry module's valid unit
            // carries exactly one ENTRY_INVOKE op delegating exactly one
            // CALL to its main, and the emitted walk drives that call once.
            int entryInvokes = 0;
            for (SemanticOp op : appUnit.ops()) {
                if (op.kind() != SemanticOpKind.ENTRY_INVOKE) {
                    continue;
                }
                entryInvokes++;
                int delegated = 0;
                for (SemanticOp candidate : appUnit.ops()) {
                    if (candidate.kind() == SemanticOpKind.CALL
                            && op.opId().equals(candidate.origin().parentOpId())) {
                        delegated++;
                    }
                }
                checkEq(1, delegated,
                    "the entry ENTRY_INVOKE delegates exactly one CALL to main");
            }
            checkEq(1, entryInvokes,
                "the entry module carries exactly one ENTRY_INVOKE delegation");
            checkEq(1, countOccurrences(source, ".fn.invoke(new Object[]{});"),
                "the emitted entry walk invokes the main delegate exactly once");
            check(source.indexOf(".fn.invoke(new Object[]{});") > appWalk,
                "the one main delegation runs inside the entry module's walk");
            int libInvokes = 0;
            for (SemanticOp op : libUnit.ops()) {
                if (op.kind() == SemanticOpKind.ENTRY_INVOKE) {
                    libInvokes++;
                }
            }
            checkEq(0, libInvokes,
                "the implementation module carries no ENTRY_INVOKE delegation");

            // The module export-surface registry (T1): one surface per
            // closure module keyed by the dotted module path, created before
            // the walks, and one EXPORT_PUBLISH write per declared export in
            // declaration order. The registry is hosted by the runtime
            // (M2: the program-scoped registry) and the class-level field is
            // the compatible per-class view of it.
            check(source.contains("static final java.util.LinkedHashMap<String, "
                    + "JvmRuntime.Table> EXPORT_SURFACES = "
                    + "JvmRuntime.EXPORT_SURFACES;"),
                "the class carries the class-level view of the runtime-hosted "
                    + "program-scoped export-surface registry");
            checkEq(List.of("    exportSurface(\"lib\");", "    exportSurface(\"app\");"),
                jvmSurfaceCreations(source),
                "one surface is created per closure module keyed by the module identity, "
                    + "before the module walks");
            int creationsAt = source.indexOf("    exportSurface(\"");
            check(creationsAt >= 0 && creationsAt < libWalk,
                "the surface creation precedes the first module walk");
            int previous = -1;
            List<String> writes = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                for (ExportEntry entry : exportsOf(project.modules().get(moduleId))) {
                    String spec = entry.spec();
                    check(spec != null && !spec.isEmpty(),
                        "the export " + moduleId.path() + "#" + entry.name()
                            + " carries a canonical spec text");
                }
            }
            checkEq(List.of("lib#add", "lib#twice", "app#main", "app#label"),
                exportOrder(project, writes),
                "the fixture's declared exports are covered in declaration order");
            for (String write : writes) {
                checkEq(1, countOccurrences(source, write),
                    "the artifact publishes " + write);
                int at = source.indexOf(write);
                check(at > previous, "the publications run in declaration order: " + write);
                previous = at;
            }

            // Determinism and the className passthrough.
            checkEq(source, JvmSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), className,
                    fixture.surface()).source(),
                "the repeated production emission is byte-identical");
            checkEq("CustomApp",
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), "CustomApp", fixture.surface()).className(),
                "the className argument is used verbatim");
            checkEq(1, countOccurrences(JvmSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), "CustomApp",
                    fixture.surface()).source(),
                    "public final class CustomApp {"),
                "a verbatim className lands in the class head");

            // The landed entries keep their behavior.
            JvmSemanticEmitter.EmissionResult trace = JvmSemanticEmitter.emitProject(
                project, result.tables(), result.registries());
            check(trace.className().startsWith("SharedM") && trace.source().contains("R|"),
                "emitProject keeps its shared conformance class and trace protocol");
            JvmSemanticEmitter.EmissionResult module =
                JvmSemanticEmitter.emitProductionModule(appUnit, result.tables().get(APP),
                    true, "AppModule");
            checkEq("AppModule", module.className(),
                "emitProductionModule keeps using its className argument");
            check(module.source().contains("JvmRuntime.setTraceEnabled(false);"),
                "emitProductionModule keeps the suppressed trace protocol");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** The EXPORT_PUBLISH writes the artifact must carry, in declaration order. */
    private static List<String> exportOrder(ExecutableLoweredProject project,
            List<String> writes) {
        List<String> order = new ArrayList<>();
        for (ModuleId moduleId : project.modules().keySet()) {
            for (ExportEntry entry : exportsOf(project.modules().get(moduleId))) {
                order.add(moduleId.path() + "#" + entry.name());
                writes.add("exportSurface(\"" + moduleId.path() + "\").write(\""
                    + entry.name() + "\", v" + entry.valueId() + ");");
            }
        }
        return order;
    }

    // =========================================================================
    // 3. The artifact under javac --release 25 -proc:none and java
    // =========================================================================

    private static void testCompileAndRun() throws Exception {
        System.out.println("-- the production artifact compiles and runs under the "
            + "real toolchain --");
        Fixture fixture = compileProject();
        Path workspace = Files.createTempDirectory("jvm-production-project-run");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Path source = workspace.resolve(className + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);

            List<String> modules = new ArrayList<>();
            List<List<ExportEntry>> entries = new ArrayList<>();
            for (ModuleId moduleId : project.modules().keySet()) {
                modules.add(moduleId.path());
                entries.add(exportsOf(project.modules().get(moduleId)));
            }

            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString()), workspace);
            check(javacRun.exitCode() == 0,
                "the production artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }

            // The artifact's own main: exit 0, empty output, no trace line.
            ProcessOutcome direct = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, className), workspace);
            check(direct.exitCode() == 0,
                "the executed artifact exits 0: exit=" + direct.exitCode() + " "
                    + direct.output());
            checkEq("", direct.stdout(),
                "the successful production run prints nothing on stdout");
            checkEq("", direct.stderr(),
                "the successful production run prints nothing on stderr");
            check(!direct.stdout().contains("R|") && !direct.stderr().contains("R|"),
                "the executed artifact emits no R| trace line");

            // The surface probe: the entry module's main drive runs once,
            // both per-module surfaces hold their declaration-order exports,
            // and a repeated dealMain() drive re-runs no initialized module.
            String driverName = "JvmProductionProjectProbe";
            Path driver = workspace.resolve(driverName + ".java");
            Files.writeString(driver, probeSource(className, driverName, modules, entries),
                StandardCharsets.UTF_8);
            ProcessOutcome probeJavac = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath + java.io.File.pathSeparator + classes.toString(),
                "-d", classes.toString(), driver.toAbsolutePath().toString()), workspace);
            check(probeJavac.exitCode() == 0,
                "the surface probe compiles: " + probeJavac.output());
            if (probeJavac.exitCode() != 0) {
                return;
            }
            ProcessOutcome probe = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, driverName), workspace);
            check(probe.exitCode() == 0 && probe.stdout().contains("PROBE-OK"),
                "the two per-module surfaces hold their declaration-order exports after "
                    + "the run, the entry main ran exactly once, and a repeated "
                    + "dealMain() drive re-runs no initialized module: exit="
                    + probe.exitCode() + " " + probe.output());
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The DEAL_ERROR_CODE terminal (E8004)
    // =========================================================================

    private static void testOverflowTerminal() throws Exception {
        System.out.println("-- the conversion-overflow fixture: exit 1 and the "
            + "DEAL_ERROR_CODE terminal --");
        Fixture fixture = compileProject(OVERFLOW_SOURCE, "src/main.deal");
        Path workspace = Files.createTempDirectory("jvm-production-project-overflow");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the overflow fixture project lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            checkEq(List.of(new ModuleId("main")), List.copyOf(project.modules().keySet()),
                "the overflow fixture is the single entry module");
            String className = JvmBackend.classNameFor(project.entryModule().path());
            checkEq("Main", className, "the overflow entry class name is Main");
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());

            Path source = workspace.resolve(className + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString()), workspace);
            check(javacRun.exitCode() == 0,
                "the overflow artifact compiles with javac --release 25 -proc:none: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, className), workspace);
            check(run.exitCode() == 1,
                "the overflow run exits 1: exit=" + run.exitCode() + " " + run.output());
            check(run.stdout().contains("DEAL_ERROR_CODE: E8004"),
                "the overflow run prints DEAL_ERROR_CODE: E8004 on stdout: "
                    + run.output());
            check(!run.stdout().contains("DEAL_ERROR_SNAPSHOT"),
                "the production artifact prints no snapshot line");
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Driver sources
    // =========================================================================

    /**
     * The surface probe: the artifact's own {@code main} runs, the registry
     * carries one surface per module keyed by the dotted module path, each
     * surface holds its declared exports in declaration order with the
     * published {@code JvmRuntime.FunctionValue} carrier, the entry drive
     * initialized every module once, and a repeated {@code dealMain()}
     * drive re-runs no initialized module and keeps every surface.
     */
    private static String probeSource(String className, String driverName,
            List<String> modules, List<List<ExportEntry>> entries) {
        StringBuilder source = new StringBuilder();
        source.append("public class ").append(driverName).append(" {\n");
        source.append("  static int failures = 0;\n");
        source.append("  static void check(boolean condition, String what) {\n");
        source.append("    if (!condition) { failures++; "
            + "System.out.println(\"PROBE-FAIL: \" + what); }\n");
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
                source.append("          check(value instanceof "
                    + "deal.codegen.jvm.JvmRuntime.FunctionValue, ")
                    .append(javaString("the published " + module + "#" + entry.name()
                        + " is a JvmRuntime.FunctionValue carrier; got "))
                    .append(" + value);\n");
                source.append("          if (value instanceof "
                    + "deal.codegen.jvm.JvmRuntime.FunctionValue carrier) {\n");
                source.append("            check(").append(javaString(entry.spec()))
                    .append(".equals(carrier.spec), ")
                    .append(javaString("the published " + module + "#" + entry.name()
                        + " carries its canonical spec text; got "))
                    .append(" + carrier.spec);\n");
                source.append("          }\n        }\n");
            }
            source.append("      }\n    }\n");
        }
        // The entry drive completed every module's init walk exactly once:
        // the runtime's module-init state proves the guarded walks will not
        // run again (the ENTRY_INVOKE delegation lives inside the entry
        // module's single walk).
        source.append("    check(!deal.codegen.jvm.JvmRuntime.moduleInitNeeded(\"lib\"), "
            + "\"the entry drive initialized lib exactly once\");\n");
        source.append("    check(!deal.codegen.jvm.JvmRuntime.moduleInitNeeded(\"app\"), "
            + "\"the entry drive initialized app exactly once (the one "
            + "ENTRY_INVOKE delegation)\");\n");
        // A repeated dealMain() drive re-runs no initialized module and
        // keeps every published surface.
        source.append("    ").append(className).append(".dealMain();\n");
        source.append("    check(surfaces == ").append(className)
            .append(".EXPORT_SURFACES, \"the repeated dealMain() drive keeps the "
                + "registry instance\");\n");
        source.append("    check(surfaces.size() == ").append(modules.size())
            .append(", \"the repeated dealMain() drive keeps every surface; got \" + "
                + "surfaces.size());\n");
        source.append("    check(!deal.codegen.jvm.JvmRuntime.moduleInitNeeded(\"lib\"), "
            + "\"the repeated drive re-runs no initialized module (lib)\");\n");
        source.append("    check(!deal.codegen.jvm.JvmRuntime.moduleInitNeeded(\"app\"), "
            + "\"the repeated drive re-runs no initialized module (app)\");\n");
        for (String module : modules) {
            source.append("    check(surfaces.containsKey(").append(javaString(module))
                .append("), ").append(javaString("the repeated drive left the " + module
                    + " surface intact")).append(");\n");
        }
        source.append("    if (failures > 0) { System.out.println(\"PROBE-FAIL: \" + "
            + "failures + \" checks failed\"); System.exit(1); }\n");
        source.append("    System.out.println(\"PROBE-OK\");\n");
        source.append("  }\n}\n");
        return source.toString();
    }

    // =========================================================================
    // Helpers
    // =========================================================================

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
        System.out.println("=== JVM Production Project Emission Tests (ISSUE-0641) ===\n");
        testEntrySignature();
        testEmittedTextShapes();
        testCompileAndRun();
        testOverflowTerminal();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== JVM Production Project Emission Tests Passed ===");
    }
}
