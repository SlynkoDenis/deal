package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.distribution.DistributionHome;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.publication.PublicationStager;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticProfile;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

/**
 * ISSUE-0656: the guard replacement, the pin retargeting, and the
 * production-arm drives (design source
 * {@code host-module-load-and-host-call-realization} H6 and the extern-C
 * remnant contract; {@code cross-module-call-realization} X3;
 * {@code luajit-jvm-single-lowering-production-cutover} C2/C4; read-only
 * {@code production-project-emission-and-atomic-cutover} P9/P10).
 *
 * <ol>
 *   <li><b>The narrowed guard.</b> A HOST-kind import whose
 *       declaration-surface kind is {@code EXTERN_C} keeps the landed
 *       E6005 {@code SHARED_EMITTER_COVERAGE} outcome with the stable
 *       {@code HOST_MODULE_IMPORT} token, the raw specifier, and the
 *       resolved module, and stages nothing (the FFI child replaces the
 *       remnant when it realizes the {@code load_ffi} table). The
 *       superseded {@code EXTERNAL_ASYNC_CALL} token has no producer in
 *       the production source set and appears in no production
 *       outcome.</li>
 *   <li><b>The composed host closure.</b> One closure imports two host
 *       declaration modules and runs the host load, the sync host call,
 *       the async host call, the sync host value-position read (invoked),
 *       and the async host value-position read (awaited) through this
 *       epic's static arms ({@code CALL(INDIRECT)} and
 *       {@code ASYNC_START(HOST)} on the reads child's exactly-one
 *       {@code HostFunction} registration); it compiles through the
 *       release-owned production arm ({@code ProductionProjectEmission.run}:
 *       one staged project artifact, {@code semanticEmissionCount() == 1},
 *       {@code retainedEmissionCount() == 0}) and executes under
 *       {@code luajit} and {@code java} with the pinned transcript.</li>
 *   <li><b>The composed cross-module closure.</b> One closure runs the
 *       sync external call and the async external call through the callee
 *       module's own async entry and the caller's alias token; it compiles
 *       through the same production arm with one staged project artifact
 *       and no retained emission, and executes under both real toolchains
 *       with the pinned transcript. No guard blocks the realized
 *       closure.</li>
 * </ol>
 *
 * <p>No operation kind, boundary kind, policy, or payload record is
 * added; the extern-C E6006 path on the JVM, the lanes, and the JS
 * pipeline are untouched.</p>
 */
public class GuardReplacementTest {

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
        check(java.util.Objects.equals(expected, actual),
            message + " (expected " + expected + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Fixtures
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");

    /** The cross-module library: one sync and one async export. */
    private static final String LIB_SOURCE = """
        export function bump(v: int): int {
          return v + 1;
        }

        export async function plus(a: int, b: int): int {
          return a + b;
        }
        """;

    /** The composed cross-module closure: the sync and async external calls. */
    private static final String CROSS_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          return null;
        }

        export async function run(): int {
          let a: int = lib.bump(4);
          let b: int = await lib.plus(1, 2);
          return a * 10 + b;
        }
        """;

    /**
     * The composed host closure: the sync host call, the async host call,
     * the sync value-position read (invoked), and the async
     * value-position read (awaited) over two host declaration modules.
     */
    private static final String HOST_APP_SOURCE = """
        import * as hostAsync from "host/async_ok"
        import * as hostBoundary from "host/boundary"

        export function main(): null {
          return null;
        }

        export async function run(): int {
          let direct: int = hostBoundary.echoInt(7);
          let fetched: string = await hostAsync.fetchValue();
          let f: (v: int) => int = hostBoundary.echoInt;
          let read: int = f(4);
          let op: async () => string = hostAsync.fetchValue;
          let readAsync: string = await op();
          if (fetched === "fetched" && readAsync === "fetched") {
            return direct + read + 100;
          }
          return direct + read;
        }
        """;

    /** The extern-C declaration of the narrowed-guard probe. */
    private static final String EXTERN_C_DECLARATION = """
        // @extern-c
        export function nativeAdd(a: int, b: int): int;
        """;

    /** The extern-C import fixture: the import is never called. */
    private static final String EXTERN_C_APP_SOURCE = """
        import * as native from "native/math"

        export function main(): null {
          return null;
        }
        """;

    /**
     * The failing composed host closure: the host async operation
     * completes with 42, which violates the declared {@code string}
     * return, so the single {@code ASYNC_COMPLETION} boundary fails at the
     * await site (line 8 column 25, the pinned origin of the corpus's
     * {@code host-async-bad} projection).
     */
    private static final String HOST_FAILURE_APP_SOURCE = """
        import * as hostAsync from "host/async_bad"

        export function main(): null {
          return null;
        }

        export async function run(): string {
          let fetched: string = await hostAsync.fetchValue();
          return fetched;
        }
        """;

    private static final String HOST_ASYNC_SPECIFIER = "host/async_ok";
    private static final String HOST_ASYNC_BAD_SPECIFIER = "host/async_bad";
    private static final String HOST_BOUNDARY_SPECIFIER = "host/boundary";
    private static final String EXTERN_C_SPECIFIER = "native/math";

    /** The corpus host implementations this drive deploys unchanged. */
    private static final Path HOST_FIXTURES =
        Path.of("test", "conformance", "host-fixtures");

    /** One temp project: its root, src dir, entry, and externals wiring. */
    private record Project(
        Path root,
        Path src,
        Path entry,
        Map<String, String> externals) {
    }

    /** The harness-invocation build facts {@code ProductionProjectEmission.run} needs. */
    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    private record ArmCompile(CompilationOrchestrator orchestrator, boolean success) {
    }

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n") + " stderr="
                + stderr.replace("\n", "\\n");
        }
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    // =========================================================================
    // The compile harness
    // =========================================================================

    /**
     * Materializes one temp project: every source under its map key plus
     * the externals wiring. An externals value of the form
     * {@code corpus:<stem>} copies the corpus host declaration
     * companion ({@code test/conformance/host-fixtures/<stem>.d.deal})
     * into the project with its classification headers stripped (the
     * harness's own seam); every other value is a root-relative
     * declaration path.
     */
    private static Project project(Map<String, String> sources,
            Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("guard-replacement-fixture");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            if (external.getValue().startsWith("corpus:")) {
                String stem = external.getValue().substring("corpus:".length());
                String declaration = Files.readString(
                    HOST_FIXTURES.resolve(stem + ".d.deal"), StandardCharsets.UTF_8);
                writeFileIn(root, "src/" + stem + ".d.deal",
                    ConformanceHarnessMetadata.stripClassificationHeaders(declaration));
                resolvedExternals.put(external.getKey(),
                    root.resolve("src/" + stem + ".d.deal").toAbsolutePath().toString());
            } else {
                resolvedExternals.put(external.getKey(),
                    root.resolve(external.getValue()).toAbsolutePath().toString());
            }
        }
        return new Project(root, src.toAbsolutePath(),
            src.resolve("app.deal").toAbsolutePath(), resolvedExternals);
    }

    /**
     * The harness-invocation compile of one project (the P10 item-3
     * pattern): the fixture facts stay arm-independent of the production
     * dispatch this test drives.
     */
    private static Fixture gather(Project project, Backend backend) throws Exception {
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            project.entry(), project.root().resolve("gather-out"), false, false,
            false, false, backend, project.externals(), List.of(project.src()),
            null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            throw new IllegalStateException("the fixture project did not build: "
                + detail + " / " + orchestrator.diagnostics());
        }
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            String specifier = null;
            for (String key : project.externals().keySet()) {
                if (key.replace('/', '.').equals(declarationModule.path())
                        || key.equals(declarationModule.path())) {
                    specifier = key;
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(project.root(), built.input(), built.index(),
            manifests.manifests(), surface, externCModules, identities);
    }

    /** The release-owned production compile of one project (the dispatch seam). */
    private static ArmCompile productionCompile(Project project, Backend backend,
            Path output) throws Exception {
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            project.entry(), output, false, false, false, false, backend,
            project.externals(), List.of(project.src()), null, null,
            productionInvocation());
        return new ArmCompile(orchestrator, orchestrator.compile());
    }

    /** The direct unit drive of the production arm over the gathered facts. */
    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager) throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(), BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, false,
            DistributionHome.forManifestDirectory(fixture.root().resolve("src")
                .toString()), stager);
    }

    // =========================================================================
    // 1. The narrowed guard and the removed shape
    // =========================================================================

    private static void testNarrowedGuardAndRemovedShape() throws Exception {
        System.out.println("-- the narrowed guard: the extern-C declaration import "
            + "keeps the HOST_MODULE_IMPORT outcome and stages nothing --");

        Project externC = project(
            Map.of("src/app.deal", EXTERN_C_APP_SOURCE, "src/native.d.deal",
                EXTERN_C_DECLARATION),
            Map.of(EXTERN_C_SPECIFIER, "src/native.d.deal"));
        try {
            Fixture fixture = gather(externC, Backend.LUAJIT);
            checkEq(HostDeclarationSurface.DeclarationKind.EXTERN_C,
                fixture.surface().require(new ModuleId("native.math")).kind(),
                "the probe's declaration module is EXTERN_C-kind");

            Path out = externC.root().resolve("unit-out");
            writeFileIn(out, "app.lua", "-- previous artifact\n");
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(fixture, Backend.LUAJIT, stager);
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the narrowed guard stages nothing");
            } finally {
                stager.discard();
            }
            check(!result.emitted(), "the extern-C declaration import fails closed");
            checkEq(1, result.diagnostics().size(),
                "the guard returns exactly the first diagnostic");
            check(result.firstDiagnostic() != null
                    && "E6005".equals(result.firstDiagnostic().code()),
                "the guard diagnostic is E6005: " + result.diagnostics());
            String message = result.firstDiagnostic() == null
                ? "" : result.firstDiagnostic().message();
            check(message.contains(ProductionProjectEmission.SHARED_EMITTER_COVERAGE),
                "the guard names SHARED_EMITTER_COVERAGE: " + message);
            check(message.contains(ProductionProjectEmission.HOST_MODULE_IMPORT),
                "the guard names the stable HOST_MODULE_IMPORT token: " + message);
            check(message.contains("'" + EXTERN_C_SPECIFIER + "'"),
                "the guard names the import's raw specifier: " + message);
            check(message.contains("'native.math'"),
                "the guard names the import's resolved module: " + message);
            check(Files.exists(out.resolve("app.lua"))
                    && Files.readString(out.resolve("app.lua"),
                        StandardCharsets.UTF_8).equals("-- previous artifact\n"),
                "the guarded compile leaves the previous artifact set untouched");
        } finally {
            deleteRecursively(externC.root());
        }

        // The release-owned production CLI of the same extern-C closure:
        // the narrowed guard's outcome with nothing published.
        Project cli = project(
            Map.of("src/app.deal", EXTERN_C_APP_SOURCE, "src/native.d.deal",
                EXTERN_C_DECLARATION),
            Map.of(EXTERN_C_SPECIFIER, "src/native.d.deal"));
        try {
            Path cliOut = cli.root().resolve("cli-out");
            ArmCompile compile = productionCompile(cli, Backend.LUAJIT, cliOut);
            check(!compile.success(),
                "the release-owned production compile of the extern-C closure "
                    + "fails closed");
            check(compile.orchestrator().diagnostics().stream().anyMatch(d ->
                    "E6005".equals(d.code())
                        && d.message().contains(
                            ProductionProjectEmission.SHARED_EMITTER_COVERAGE)
                        && d.message().contains(
                            ProductionProjectEmission.HOST_MODULE_IMPORT)),
                "the production compile names E6005 SHARED_EMITTER_COVERAGE "
                    + "HOST_MODULE_IMPORT: "
                    + compile.orchestrator().diagnostics());
            check(!Files.exists(cliOut),
                "the production compile publishes nothing under " + cliOut);
        } finally {
            deleteRecursively(cli.root());
        }

        // The superseded shape has no producer: the constant is gone from
        // the production unit, and the JVM extern-C path keeps its
        // pre-artifact E6006 rejection.
        String productionUnit = Files.readString(
            Path.of("deal", "module", "ProductionProjectEmission.java"),
            StandardCharsets.UTF_8);
        check(!productionUnit.contains("EXTERNAL_ASYNC_CALL"),
            "the production unit carries no EXTERNAL_ASYNC_CALL token");
        check(!productionUnit.contains("closureGuard"),
            "the production unit carries no cross-module async closure guard");
    }

    // =========================================================================
    // 2. The composed host closure
    // =========================================================================

    private static void testComposedHostClosure() throws Exception {
        System.out.println("-- the composed host closure: the host load, the sync and "
            + "async host calls, and both value-position read forms through the "
            + "production arm under luajit and java --");

        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(HOST_ASYNC_SPECIFIER, "corpus:async_ok");
        externals.put(HOST_BOUNDARY_SPECIFIER, "corpus:boundary");
        Project project = project(Map.of("src/app.deal", HOST_APP_SOURCE), externals);
        try {
            // (a) LuaJIT: the release-owned production compile (one project
            // emission, no retained emission, one staged project artifact)
            // then the executed transcript with the deployed host
            // implementations.
            Path luaOut = project.root().resolve("out-luajit");
            ArmCompile luaArm = productionCompile(project, Backend.LUAJIT, luaOut);
            check(luaArm.success(),
                "the composed host closure compiles through the release-owned "
                    + "production arm: " + luaArm.orchestrator().diagnostics());
            if (!luaArm.success()) {
                return;
            }
            checkEq(1, luaArm.orchestrator().semanticEmissionCount(),
                "the composed host closure records one project emission");
            checkEq(0, luaArm.orchestrator().retainedEmissionCount(),
                "the composed host closure increments no retained counter");
            List<String> luaArtifacts = artifactFiles(luaOut);
            check(luaArtifacts.contains("app.lua") && !luaArtifacts.contains("lib.lua"),
                "the composed host closure publishes the one project artifact and "
                    + "no per-module sibling: " + luaArtifacts);
            String chunk = Files.readString(luaOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            checkEq(1, countOccurrences(chunk,
                    "__rt.load_host(\"host/async_ok\""),
                "the host module host/async_ok loads exactly once");
            checkEq(1, countOccurrences(chunk,
                    "__rt.load_host(\"host/boundary\""),
                "the host module host/boundary loads exactly once");
            check(hasDeclaredExport(chunk),
                "the emitted declared map carries the host function descriptors");
            check(!chunk.contains("__callbacks.__hostStartAsync("),
                "the production chunk's async host site never calls the "
                    + "deterministic start seam");
            check(chunk.contains("pcall(__rt.async_step, __tA.handle)"),
                "the AWAIT drives a handle-carrying record through __rt.async_step");
            check(chunk.contains("if __tA.handle ~= nil then")
                    && chunk.indexOf("pcall(__rt.async_step, __tA.handle)")
                        < chunk.indexOf("__callbacks.__hostCompleteAsync(__tA.label)"),
                "the seam completion is reachable only by a record without an "
                    + "operation handle (the production path never reaches it)");

            deployHostLua(luaOut, "async_ok");
            deployHostLua(luaOut, "boundary");
            writeFileIn(luaOut, "probe.lua", """
                local surfaces = dofile("app.lua")
                local run = surfaces.run
                assert(type(run) == "table" and run.__kind == "function",
                  "the entry surface publishes the composed async export")
                local completed = run.f()
                print("PROBE|HOST-COMPOSED|" .. tostring(completed))
                """);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "probe.lua"), luaOut);
            checkEq(0, luaRun.exitCode(),
                "the composed host closure executes under luajit: "
                    + luaRun.output());
            check(luaRun.stdout().contains("PROBE|HOST-COMPOSED|111"),
                "the composed host closure completes with 111 under luajit: "
                    + luaRun.stdout());

            // (b) JVM: the same production arm, the artifact compiled
            // together with the deployed host implementations, and the
            // identical transcript under java.
            Path jvmOut = project.root().resolve("out-jvm");
            ArmCompile jvmArm = productionCompile(project, Backend.JVM, jvmOut);
            check(jvmArm.success(),
                "the composed host closure compiles through the release-owned "
                    + "JVM production arm: " + jvmArm.orchestrator().diagnostics());
            if (!jvmArm.success()) {
                return;
            }
            checkEq(1, jvmArm.orchestrator().semanticEmissionCount(),
                "the composed host JVM closure records one project emission");
            checkEq(0, jvmArm.orchestrator().retainedEmissionCount(),
                "the composed host JVM closure increments no retained counter");
            checkEq(List.of("App.java"), artifactFiles(jvmOut),
                "the composed host JVM closure publishes the one project class");
            String source = Files.readString(jvmOut.resolve("App.java"),
                StandardCharsets.UTF_8);
            check(source.contains(JvmBackend.classNameFor(HOST_ASYNC_SPECIFIER))
                    && source.contains(JvmBackend.classNameFor(HOST_BOUNDARY_SPECIFIER)),
                "the JVM artifact carries both host imports' ABI surface");
            check(!source.contains("HOST_ASYNC"),
                "the JVM artifact never references the deterministic host-async "
                    + "seam");

            deployHostJava(jvmOut, "async_ok", "HostAsync_ok");
            deployHostJava(jvmOut, "boundary", "HostBoundary");
            writeFileIn(jvmOut, "HostComposedProbe.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class HostComposedProbe {
                  public static void main(String[] args) {
                    App.main(new String[0]);
                    JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
                    JvmRuntime.FunctionValue run =
                        (JvmRuntime.FunctionValue) surface.read("run");
                    Object completed = run.fn.invoke(new Object[0]);
                    System.out.println("PROBE|HOST-COMPOSED|" + completed);
                  }
                }
                """);
            Path classes = project.root().resolve("host-classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmOut.resolve("App.java").toString(),
                jvmOut.resolve("HostAsync_ok.java").toString(),
                jvmOut.resolve("HostBoundary.java").toString(),
                jvmOut.resolve("HostComposedProbe.java").toString()), jvmOut);
            checkEq(0, javacRun.exitCode(),
                "the composed host JVM artifact compiles with the deployed host "
                    + "implementations: " + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, "HostComposedProbe"),
                jvmOut);
            checkEq(0, jvmRun.exitCode(),
                "the composed host closure executes under java: "
                    + jvmRun.output());
            check(jvmRun.stdout().contains("PROBE|HOST-COMPOSED|111"),
                "the composed host closure completes with 111 under java: "
                    + jvmRun.stdout());
        } finally {
            deleteRecursively(project.root());
        }
    }

    /**
     * True when the emitted chunk carries the declared-map entries of both
     * host modules (the declared export names in declaration order).
     */
    private static boolean hasDeclaredExport(String chunk) {
        return chunk.contains("[\"fetchValue\"] = ")
            && chunk.contains("[\"echoInt\"] = ")
            && chunk.contains("[\"nextValue\"] = ");
    }

    // =========================================================================
    // 3. The composed cross-module closure
    // =========================================================================

    private static void testComposedCrossModuleClosure() throws Exception {
        System.out.println("-- the composed cross-module closure: the sync and async "
            + "external calls through the production arm under luajit and java --");

        Project project = project(new LinkedHashMap<>(Map.of(
                "src/lib.deal", LIB_SOURCE,
                "src/app.deal", CROSS_APP_SOURCE)), Map.of());
        try {
            // (a) LuaJIT.
            Path luaOut = project.root().resolve("out-luajit");
            ArmCompile luaArm = productionCompile(project, Backend.LUAJIT, luaOut);
            check(luaArm.success(),
                "the composed cross-module closure compiles through the "
                    + "release-owned production arm: "
                    + luaArm.orchestrator().diagnostics());
            if (!luaArm.success()) {
                return;
            }
            checkEq(1, luaArm.orchestrator().semanticEmissionCount(),
                "the composed cross-module closure records one project emission");
            checkEq(0, luaArm.orchestrator().retainedEmissionCount(),
                "the composed cross-module closure increments no retained counter");
            List<String> luaArtifacts = artifactFiles(luaOut);
            check(luaArtifacts.contains("app.lua")
                    && !luaArtifacts.contains("lib.lua"),
                "the composed cross-module closure publishes the one project "
                    + "artifact and no per-module sibling: " + luaArtifacts);
            String chunk = Files.readString(luaOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            check(chunk.contains("__asyncEntries[\"lib#plus\"]"),
                "the chunk carries the callee module's async entry");
            check(!chunk.contains("EXTERNAL_ASYNC_CALL")
                    && !chunk.contains("SharedM"),
                "the chunk carries no superseded guard token and no per-module "
                    + "async-entry reference");
            writeFileIn(luaOut, "probe.lua", """
                local surfaces = dofile("app.lua")
                local run = surfaces.run
                assert(type(run) == "table" and run.__kind == "function",
                  "the entry surface publishes the composed async export")
                local completed = run.f()
                print("PROBE|CROSS-COMPOSED|" .. tostring(completed))
                """);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "probe.lua"), luaOut);
            checkEq(0, luaRun.exitCode(),
                "the composed cross-module closure executes under luajit: "
                    + luaRun.output());
            check(luaRun.stdout().contains("PROBE|CROSS-COMPOSED|53"),
                "the composed cross-module closure completes with 53 under "
                    + "luajit: " + luaRun.stdout());

            // (b) JVM.
            Path jvmOut = project.root().resolve("out-jvm");
            ArmCompile jvmArm = productionCompile(project, Backend.JVM, jvmOut);
            check(jvmArm.success(),
                "the composed cross-module closure compiles through the "
                    + "release-owned JVM production arm: "
                    + jvmArm.orchestrator().diagnostics());
            if (!jvmArm.success()) {
                return;
            }
            checkEq(1, jvmArm.orchestrator().semanticEmissionCount(),
                "the composed cross-module JVM closure records one project emission");
            checkEq(0, jvmArm.orchestrator().retainedEmissionCount(),
                "the composed cross-module JVM closure increments no retained "
                    + "counter");
            checkEq(List.of("App.java"), artifactFiles(jvmOut),
                "the composed cross-module JVM closure publishes the one project "
                    + "class");
            String source = Files.readString(jvmOut.resolve("App.java"),
                StandardCharsets.UTF_8);
            check(!source.contains("SharedM"),
                "the JVM class references no per-module async-entry class");
            writeFileIn(jvmOut, "CrossComposedProbe.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class CrossComposedProbe {
                  public static void main(String[] args) {
                    App.main(new String[0]);
                    JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
                    JvmRuntime.FunctionValue run =
                        (JvmRuntime.FunctionValue) surface.read("run");
                    Object completed = run.fn.invoke(new Object[0]);
                    System.out.println("PROBE|CROSS-COMPOSED|" + completed);
                  }
                }
                """);
            Path classes = project.root().resolve("cross-classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmOut.resolve("App.java").toString(),
                jvmOut.resolve("CrossComposedProbe.java").toString()), jvmOut);
            checkEq(0, javacRun.exitCode(),
                "the composed cross-module JVM artifact compiles: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, "CrossComposedProbe"),
                jvmOut);
            checkEq(0, jvmRun.exitCode(),
                "the composed cross-module closure executes under java: "
                    + jvmRun.output());
            check(jvmRun.stdout().contains("PROBE|CROSS-COMPOSED|53"),
                "the composed cross-module closure completes with 53 under java: "
                    + jvmRun.stdout());
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 4. The failing composed closure's pinned origin
    // =========================================================================

    private static void testComposedFailureOrigin() throws Exception {
        System.out.println("-- the failing composed host closure: the single "
            + "ASYNC_COMPLETION boundary fails at the pinned await-site origin "
            + "under both targets --");
        Project project = project(Map.of("src/app.deal", HOST_FAILURE_APP_SOURCE),
            Map.of(HOST_ASYNC_BAD_SPECIFIER, "corpus:async_bad"));
        try {
            // LuaJIT: the deployed host operation completes with 42, so the
            // AWAIT's completion cell fails; the probe reports the boundary
            // error's own fields.
            Path luaOut = project.root().resolve("out-luajit");
            ArmCompile luaArm = productionCompile(project, Backend.LUAJIT, luaOut);
            check(luaArm.success(),
                "the failing composed closure compiles through the production "
                    + "arm: " + luaArm.orchestrator().diagnostics());
            if (!luaArm.success()) {
                return;
            }
            deployHostLua(luaOut, "async_bad");
            writeFileIn(luaOut, "probe.lua", """
                local surfaces = dofile("app.lua")
                local run = surfaces.run
                local ok, err = pcall(run.f)
                assert(not ok, "the failing composed closure raises")
                print("PROBE|HOST-FAILURE|" .. tostring(err.code) .. "|"
                  .. tostring(err.m) .. "|" .. tostring(err.o) .. "|"
                  .. tostring(err.e) .. "|" .. tostring(err.a))
                """);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "probe.lua"), luaOut);
            checkEq(0, luaRun.exitCode(),
                "the failing composed closure probe runs: " + luaRun.output());
            String luaLine = lineStartingWith(luaRun.stdout(), "PROBE|HOST-FAILURE|");
            check(luaLine != null, "the failing composed closure reports its "
                + "completion-cell error: " + luaRun.stdout());
            if (luaLine != null) {
                check(luaLine.contains("E8001"),
                    "the completion-cell failure is E8001: " + luaLine);
                check(luaLine.contains("expected string"),
                    "the completion-cell failure names the declared type: "
                        + luaLine);
                check(luaLine.contains(":8:25"),
                    "the completion-cell failure carries the pinned await-site "
                        + "origin (line 8 column 25): " + luaLine);
            }

            // JVM: the same closure, the returned future completing with 42
            // joined by the production host task and the completion cell
            // failing at the await site.
            Path jvmOut = project.root().resolve("out-jvm");
            ArmCompile jvmArm = productionCompile(project, Backend.JVM, jvmOut);
            check(jvmArm.success(),
                "the failing composed closure compiles through the JVM "
                    + "production arm: " + jvmArm.orchestrator().diagnostics());
            if (!jvmArm.success()) {
                return;
            }
            deployHostJava(jvmOut, "async_bad", "HostAsync_bad");
            writeFileIn(jvmOut, "HostFailureProbe.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class HostFailureProbe {
                  public static void main(String[] args) {
                    App.main(new String[0]);
                    JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
                    JvmRuntime.FunctionValue run =
                        (JvmRuntime.FunctionValue) surface.read("run");
                    try {
                      run.fn.invoke(new Object[0]);
                      System.out.println("PROBE|HOST-FAILURE|no-error");
                    } catch (JvmRuntime.DealError error) {
                      System.out.println("PROBE|HOST-FAILURE|" + error.code + "|"
                          + error.msg + "|" + error.origin + "|"
                          + error.expected + "|" + error.actual);
                    }
                  }
                }
                """);
            Path classes = project.root().resolve("failure-classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                jvmOut.resolve("App.java").toString(),
                jvmOut.resolve("HostAsync_bad.java").toString(),
                jvmOut.resolve("HostFailureProbe.java").toString()), jvmOut);
            checkEq(0, javacRun.exitCode(),
                "the failing composed JVM artifact compiles: " + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                classpath + File.pathSeparator + classes, "HostFailureProbe"),
                jvmOut);
            checkEq(0, jvmRun.exitCode(),
                "the failing composed JVM closure probe runs: " + jvmRun.output());
            String jvmLine = lineStartingWith(jvmRun.stdout(), "PROBE|HOST-FAILURE|");
            check(jvmLine != null, "the failing composed JVM closure reports its "
                + "completion-cell error: " + jvmRun.stdout());
            if (jvmLine != null) {
                check(jvmLine.contains("E8001"),
                    "the JVM completion-cell failure is E8001: " + jvmLine);
                check(jvmLine.contains("expected string"),
                    "the JVM completion-cell failure names the declared type: "
                        + jvmLine);
                check(jvmLine.contains(":8:25"),
                    "the JVM completion-cell failure carries the pinned await-site "
                        + "origin (line 8 column 25): " + jvmLine);
            }
        } finally {
            deleteRecursively(project.root());
        }
    }

    /** The first stdout line starting with the given prefix, or null. */
    private static String lineStartingWith(String stdout, String prefix) {
        for (String line : stdout.split("\n", -1)) {
            if (line.startsWith(prefix)) {
                return line;
            }
        }
        return null;
    }

    // =========================================================================
    // Deployment and process helpers
    // =========================================================================

    /** Deploys one corpus host Lua implementation where the raw specifier resolves it. */
    private static void deployHostLua(Path output, String stem) throws Exception {
        Path target = output.resolve("host").resolve(stem + ".lua");
        Files.createDirectories(target.getParent());
        Files.copy(HOST_FIXTURES.resolve(stem + ".lua"), target);
    }

    /** Deploys one corpus host Java implementation under its derived class name. */
    private static void deployHostJava(Path output, String stem, String className)
            throws Exception {
        Files.writeString(output.resolve(className + ".java"),
            Files.readString(HOST_FIXTURES.resolve(stem + ".java"),
                StandardCharsets.UTF_8), StandardCharsets.UTF_8);
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

    private static List<String> artifactFiles(Path root) throws Exception {
        if (!Files.isDirectory(root)) {
            return List.of();
        }
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(Files::isRegularFile)
                .map(path -> root.relativize(path).toString()
                    .replace(File.separatorChar, '/'))
                .sorted().toList();
        }
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int at = text.indexOf(needle);
        while (at >= 0) {
            count++;
            at = text.indexOf(needle, at + needle.length());
        }
        return count;
    }

    private static String absoluteClasspath() {
        List<String> entries = new ArrayList<>();
        for (String entry : System.getProperty("java.class.path", "build")
                .split(File.pathSeparator)) {
            if (!entry.isEmpty()) {
                entries.add(Path.of(entry).toAbsolutePath().normalize().toString());
            }
        }
        return String.join(File.pathSeparator, entries);
    }

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path file = root.resolve(relative);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content, StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path path) {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (var walk = Files.walk(path)) {
            walk.sorted(Comparator.reverseOrder()).forEach(entry -> {
                try {
                    Files.deleteIfExists(entry);
                } catch (java.io.IOException ignored) {
                    // best effort
                }
            });
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Guard Replacement Tests (ISSUE-0656) ===\n");
        testNarrowedGuardAndRemovedShape();
        testComposedHostClosure();
        testComposedCrossModuleClosure();
        testComposedFailureOrigin();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Guard Replacement Tests Passed ===");
    }
}
