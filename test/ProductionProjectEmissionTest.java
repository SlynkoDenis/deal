package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
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

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
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
 * ISSUE-0642: the production project emission unit
 * {@code deal.module.ProductionProjectEmission}
 * ({@code production-project-emission-and-atomic-cutover} P5/P6/P7/P9/P11
 * and the production-arm, source-map, and fail-closed producer-guard
 * contracts; {@code luajit-jvm-single-lowering-production-cutover}
 * C3/C4/C5/C7/C8/C9).
 *
 * <ol>
 *   <li>the unit is one production-source unit with one public static
 *       entry, consuming exactly the compile's declared inputs, the
 *       target, the explicit source-map flag, the deployment-copy
 *       resolver, and the staging surface;</li>
 *   <li>one lowering, one emission, one staged project artifact per
 *       target ({@code app.lua} on LuaJIT, {@code App.java} on the JVM),
 *       the unchanged LuaJIT runtime/stdlib deployment copies, no
 *       sidecar, and byte-identical repeated staging;</li>
 *   <li>the C9 warning fires once for an explicit {@code --source-map}
 *       request and never for a {@code --dump-ir}-derived flag;</li>
 *   <li>the pre-emission closure guard carries no HOST-kind shape after
 *       the calls child's realization (ISSUE-0656) and this slice's
 *       extern-C admission (ISSUE-0662): a HOST-declaration-kind import
 *       emits its declared-map host load and an extern-C declaration
 *       import emits its {@code load_ffi} prelude, each staging its one
 *       project artifact, while the guard's stable
 *       {@code HOST_MODULE_IMPORT} token and its E6005 producer stay
 *       landed; the cross-module sync and async calls emit and execute
 *       (ISSUE-0654/ISSUE-0655) with the {@code EXTERNAL_ASYNC_CALL}
 *       shape removed (ISSUE-0656);</li>
 *   <li>a failing lowering (bytes) stages nothing and leaves the previous
 *       artifact set byte-identical, while a cross-module sync call emits
 *       through the realized {@code CALL(EXTERNAL)} {@code SHARED_BODY}
 *       arm and stages its one project artifact (ISSUE-0654);</li>
 *   <li>the staged LuaJIT artifact executes under {@code luajit} and the
 *       staged JVM artifact compiles with {@code javac --release 25
 *       -proc:none} plus {@code java}.</li>
 * </ol>
 *
 * <p>The fixture inputs are gathered through a harness-invocation compile
 * (the P10 item-3 pattern), so the fixtures stay valid after the dispatch
 * leaf activates the production arm for the release-owned invocation; the
 * unit itself is driven with the release-owned production invocation.</p>
 */
public class ProductionProjectEmissionTest {

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
    // Fixtures (compiled through a harness invocation: P10 item 3)
    // =========================================================================

    private static final ModuleId LIB = new ModuleId("lib");
    private static final ModuleId HOST_CFG = new ModuleId("host.cfg");
    private static final String HOST_CFG_SPECIFIER = "host/cfg";

    /** The extern-C declaration module of the admission probe. */
    private static final ModuleId NATIVE_MATH = new ModuleId("native.math");
    private static final String EXTERN_C_SPECIFIER = "native/math";

    private static final String LIB_SOURCE = """
        export function add(a: int, b: int): int {
          return a + b;
        }

        export function twice(x: int): int {
          return x * 2;
        }
        """;

    /** The covered two-module fixture: a COMPILED import, no call. */
    private static final String APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          return null;
        }

        export function label(): string {
          return "app";
        }
        """;

    /** The one-main probe: the entry main publishes one effect byte line. */
    private static final String PROBE_APP_SOURCE = """
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

    /** The bytes-bearing fixture: the lowering fails CONSTRUCT_UNLOWERED. */
    private static final String BYTES_APP_SOURCE = """
        export function main(): null {
          let n: int = 3;
          let b: bytes = bytes(n);
          return null;
        }
        """;

    /** The cross-module sync call: the realized external-call arm. */
    private static final String SYNC_CALL_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          let x: int = lib.add(1, 2);
          return null;
        }
        """;

    /** The HOST declaration: two function exports in declaration order. */
    private static final String HOST_DECLARATION = """
        export function version(): int;
        export function describe(s: string): string;
        """;

    /** The host-import fixture: the import is never called or constructed. */
    private static final String HOST_APP_SOURCE = """
        import * as cfg from "host/cfg"

        export function main(): null {
          return null;
        }
        """;

    /** The extern-C declaration: the narrowed guard's remaining shape. */
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

    /** The async library of the cross-module async fixture. */
    private static final String ASYNC_LIB_SOURCE = """
        export async function getValue(): int {
          return 42;
        }
        """;

    /**
     * The cross-module async call: the exported worker really executes the
     * caller's alias-token linkage (the callee is a non-entry module).
     */
    private static final String CROSS_ASYNC_APP_SOURCE = """
        import * as lib from "./lib"

        export function main(): null {
          return null;
        }

        export async function worker(): int {
          return await lib.getValue();
        }
        """;

    /**
     * The same-module async call: accepted, emitted, and executable. The
     * awaiting call sits in an exported zero-arity async function so the
     * runner can invoke it through the artifact's published surface and
     * really execute the ASYNC_START(DEAL_BODY)/AWAIT path.
     */
    private static final String SAME_ASYNC_APP_SOURCE = """
        export function main(): null {
          return null;
        }

        async function compute(): int {
          return 1;
        }

        export async function worker(): int {
          return await compute();
        }
        """;

    private record Fixture(
        Path root,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
        DistributionHome distributionHome) {
    }

    /**
     * The harness invocation of the fixture compile (P10 item 3): the
     * fixtures keep building after the dispatch leaf activates the
     * production arm for the release-owned invocation.
     */
    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());
    }

    /** The release-owned production invocation this unit is driven with. */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources,
            Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("production-arm-fixture");
        Path src = root.resolve("src");
        for (Map.Entry<String, String> source : sources.entrySet()) {
            writeFileIn(root, source.getKey(), source.getValue());
        }
        Map<String, String> resolvedExternals = new LinkedHashMap<>();
        for (Map.Entry<String, String> external : externals.entrySet()) {
            resolvedExternals.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().toString());
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, resolvedExternals,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the fixture project did not build: " + detail
                + " / " + orchestrator.diagnostics());
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
            for (Map.Entry<String, String> external : externals.entrySet()) {
                if (external.getKey().replace('/', '.').equals(declarationModule.path())) {
                    specifier = external.getKey();
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            surface, externCModules, identities,
            DistributionHome.forManifestDirectory(src.toString()));
    }

    private static Fixture twoModuleFixture(String appSource) throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of(
                "src/lib.deal", LIB_SOURCE,
                "src/app.deal", appSource)), Map.of());
    }

    private static Fixture bytesFixture() throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of(
                "src/app.deal", BYTES_APP_SOURCE)), Map.of());
    }

    /** The fail-closed source: a nested function declaration (CALLS family). */
    private static final String NESTED_DECLARATION_APP_SOURCE = """
        export function main(): null {
          function inner(): int { return 1; }
          let x: int = inner();
          return null
        }
        """;

    /**
     * The still-fail-closed source: an arity-extended adapter call whose
     * source identity is not statically fixed (a call-result
     * REEVALUATE_THUNK source — the function-typed-value child's
     * ISSUE-0531 residue), so the production lowering fails the module
     * with the named E6005 CONSTRUCT_UNLOWERED rule before any emission.
     */
    private static final String ADAPTER_SOURCE_APP_SOURCE = """
        export function main(): null {
          let f: (a: int, b: int) => int = one
          f(1, 2)
          return null
        }

        function one(x: int): int {
          return x
        }
        """;

    private static Fixture adapterSourceFixture() throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of(
                "src/app.deal", ADAPTER_SOURCE_APP_SOURCE)), Map.of());
    }

    private static Fixture nestedDeclarationFixture() throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of(
                "src/app.deal", NESTED_DECLARATION_APP_SOURCE)), Map.of());
    }

    private static Fixture asyncFixture(String libSource, String appSource)
            throws Exception {
        return compileProject(new LinkedHashMap<>(Map.of(
                "src/lib.deal", libSource,
                "src/app.deal", appSource)), Map.of());
    }

    private static Fixture hostFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/cfg.d.deal", HOST_DECLARATION);
        sources.put("src/app.deal", HOST_APP_SOURCE);
        return compileProject(sources,
            Map.of(HOST_CFG_SPECIFIER, "src/cfg.d.deal"));
    }

    private static Fixture externCFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/native.d.deal", EXTERN_C_DECLARATION);
        sources.put("src/app.deal", EXTERN_C_APP_SOURCE);
        return compileProject(sources,
            Map.of(EXTERN_C_SPECIFIER, "src/native.d.deal"));
    }

    /** The emitted declared-map literal of one host import (declaration order). */
    private static String declaredMapLiteral(HostDeclarationSurface surface,
            ModuleId module) {
        HostDeclarationSurface.DeclarationFacts facts = surface.require(module);
        StringBuilder map = new StringBuilder("{");
        boolean first = true;
        for (Map.Entry<String, deal.types.Type> export : facts.exports().entrySet()) {
            if (!first) {
                map.append(", ");
            }
            first = false;
            map.append("[\"").append(export.getKey()).append("\"] = \"")
                .append(deal.semantic.DescriptorService.describe(export.getValue())
                    .canonicalSpecText())
                .append("\"");
        }
        return map.append("}").toString();
    }

    // =========================================================================
    // The unit driver
    // =========================================================================

    private static ProductionProjectEmission.Result emit(Fixture fixture,
            Backend backend, PublicationStager stager, boolean sourceMapExplicit)
            throws Exception {
        return ProductionProjectEmission.run(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            fixture.distributionHome().manifestDirectoryText(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of(), backend, sourceMapExplicit, fixture.distributionHome(), stager);
    }

    /** Runs the unit with stderr captured (the C9 warning observable). */
    private static String emitCapturingStderr(Fixture fixture, Backend backend,
            PublicationStager stager, boolean sourceMapExplicit) throws Exception {
        PrintStream originalErr = System.err;
        ByteArrayOutputStream buffer = new ByteArrayOutputStream();
        System.setErr(new PrintStream(buffer, true, StandardCharsets.UTF_8));
        try {
            emit(fixture, backend, stager, sourceMapExplicit);
        } finally {
            System.setErr(originalErr);
        }
        return buffer.toString(StandardCharsets.UTF_8);
    }

    // =========================================================================
    // 1. The unit: one production source unit, one public static entry
    // =========================================================================

    private static void testUnitShapeAndConstants() throws Exception {
        System.out.println("-- the unit is one production source unit with one "
            + "public static entry --");

        Class<?> unit = ProductionProjectEmission.class;
        check(Modifier.isPublic(unit.getModifiers())
                && Modifier.isFinal(unit.getModifiers()),
            "ProductionProjectEmission is a public final production unit");
        checkEq("deal.module", unit.getPackageName(),
            "the unit sits in the production module package");

        List<String> publicStatic = new ArrayList<>();
        for (Method method : unit.getDeclaredMethods()) {
            if (Modifier.isPublic(method.getModifiers())
                    && Modifier.isStatic(method.getModifiers())) {
                publicStatic.add(method.getName());
            }
        }
        checkEq(List.of("run"), publicStatic,
            "the unit publishes exactly one public static entry");

        Method entry = unit.getMethod("run", CompilerInvocation.class,
            CheckedProjectInput.class, ProjectInterfaceIndex.class, List.class,
            HostDeclarationSurface.class, Map.class, Map.class, String.class,
            BuiltinErrorDeclaration.class, List.class, Set.class, Backend.class,
            boolean.class, DistributionHome.class, PublicationStager.class);
        checkEq(ProductionProjectEmission.Result.class, entry.getReturnType(),
            "the entry returns the run outcome");
        List<String> parameterTypes = new ArrayList<>();
        for (Class<?> parameter : entry.getParameterTypes()) {
            parameterTypes.add(parameter.getSimpleName());
        }
        checkEq(List.of("CompilerInvocation", "CheckedProjectInput",
                "ProjectInterfaceIndex", "List", "HostDeclarationSurface", "Map",
                "Map", "String", "BuiltinErrorDeclaration", "List", "Set", "Backend",
                "boolean", "DistributionHome", "PublicationStager"),
            parameterTypes,
            "the entry consumes the compile's declared inputs (the extern-C"
                + " generated modules and the manifest-directory text feeding"
                + " the Lua session's FFI emission input), the backend, the"
                + " explicit source-map flag, the deployment-copy resolver, and the"
                + " staging surface");
        for (Class<?> parameter : entry.getParameterTypes()) {
            String name = parameter.getName();
            for (String forbidden : List.of("deal.ast.", "deal.parser.",
                    "Route", "MigrationPlanner", "CapabilityRegistry",
                    "HostModuleDeclarations", "CheckResult", "ProgramNode")) {
                check(!name.contains(forbidden),
                    "the entry takes no " + forbidden + " input: " + name);
            }
        }

        checkEq("Warning: --source-map produces no source-map sidecars with the "
                + "LuaJIT project emission (source maps are LuaJIT/JVM-unavailable in "
                + "this release)",
            ProductionProjectEmission.WARNING_LUAJIT,
            "the pinned LuaJIT C9 warning text");
        checkEq("Warning: --source-map produces no source-map sidecars with the "
                + "JVM project emission (source maps are LuaJIT/JVM-unavailable in "
                + "this release)",
            ProductionProjectEmission.WARNING_JVM,
            "the pinned JVM C9 warning text");
        checkEq("SHARED_EMITTER_COVERAGE",
            ProductionProjectEmission.SHARED_EMITTER_COVERAGE,
            "the registered emitter-coverage rule id");
        checkEq("HOST_MODULE_IMPORT", ProductionProjectEmission.HOST_MODULE_IMPORT,
            "the stable extern-C declaration-import guard token");

        // The JS target is not a production arm.
        Fixture fixture = twoModuleFixture(APP_SOURCE);
        try {
            PublicationStager stager =
                PublicationStager.forRoot(fixture.root().resolve("js-out"));
            try {
                boolean rejected = false;
                try {
                    emit(fixture, Backend.JS, stager, false);
                } catch (IllegalArgumentException expected) {
                    rejected = true;
                }
                check(rejected, "the JS target is rejected by the production unit");
                check(stager.stagedSet().relativePaths().isEmpty(),
                    "the rejected JS run stages nothing");
            } finally {
                stager.discard();
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. One lowering, one emission, one staged project artifact per target
    // =========================================================================

    private static void testOneArtifactPerTarget() throws Exception {
        System.out.println("-- one staged project artifact per target, the LuaJIT "
            + "deployment copies, no sidecar, byte-identical repeats --");
        Fixture fixture = twoModuleFixture(APP_SOURCE);
        Path luaOut = fixture.root().resolve("lua-out");
        Path jvmOut = fixture.root().resolve("jvm-out");
        Path luaOutRepeat = fixture.root().resolve("lua-out-repeat");
        try {
            // LuaJIT: the chunk named for the entry module plus the unchanged
            // runtime/stdlib deployment copies.
            PublicationStager luaStager = PublicationStager.forRoot(luaOut);
            ProductionProjectEmission.Result luaResult;
            String firstChunk;
            try {
                luaResult = emit(fixture, Backend.LUAJIT, luaStager, false);
                check(luaResult.emitted(),
                    "the LuaJIT production run emits: " + luaResult.diagnostics());
                checkEq("app.lua", luaResult.artifactRelativePath(),
                    "the LuaJIT artifact is the entry module's chunk");
                check(luaStager.stagedSet().artifact("app.lua").isPresent(),
                    "exactly one staged artifact at the pinned entry path");
                check(luaStager.stagedSet().artifact("lib.lua").isEmpty(),
                    "no per-module sibling artifact stages");
                check(luaStager.stagedSet().artifact("deal/runtime.lua").isPresent(),
                    "the unchanged LuaJIT runtime deployment copy stages");
                check(luaStager.stagedSet().artifact("std/console.lua").isPresent(),
                    "the unchanged stdlib deployment copies stage");
                for (String path : luaStager.stagedSet().relativePaths()) {
                    check(!path.endsWith(".deal.map.json"),
                        "no source-map sidecar stages: " + path);
                }
                checkEq(luaStager.stagedSet().size(),
                    1 + luaStager.stagedSet().relativePaths().stream()
                        .filter(path -> path.startsWith("std/")
                            || path.equals("deal/runtime.lua")).toList().size(),
                    "the LuaJIT staged set is the project artifact plus the "
                        + "deployment copies");
                firstChunk = new String(luaStager.stagedSet()
                    .artifact("app.lua").orElseThrow().content(),
                    StandardCharsets.UTF_8);
            } finally {
                luaStager.discard();
            }

            // JVM: one class source, no deployment copy and no sidecar.
            PublicationStager jvmStager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result jvmResult;
            try {
                jvmResult = emit(fixture, Backend.JVM, jvmStager, false);
                check(jvmResult.emitted(),
                    "the JVM production run emits: " + jvmResult.diagnostics());
                checkEq("App.java", jvmResult.artifactRelativePath(),
                    "the JVM artifact is the entry class named by classNameFor");
                checkEq(Set.of("App.java"), jvmStager.stagedSet().relativePaths(),
                    "exactly one staged artifact and nothing else on the JVM");
            } finally {
                jvmStager.discard();
            }

            // Byte-identical repeated staging.
            PublicationStager repeatStager =
                PublicationStager.forRoot(luaOutRepeat);
            try {
                ProductionProjectEmission.Result repeat =
                    emit(fixture, Backend.LUAJIT, repeatStager, false);
                check(repeat.emitted(),
                    "the repeated LuaJIT run emits: " + repeat.diagnostics());
                String secondChunk = new String(repeatStager.stagedSet()
                    .artifact("app.lua").orElseThrow().content(),
                    StandardCharsets.UTF_8);
                checkEq(firstChunk, secondChunk,
                    "repeated compiles are byte-identical");
            } finally {
                repeatStager.discard();
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testOneMainProbe() throws Exception {
        System.out.println("-- the staged chunk delegates the entry main exactly "
            + "once --");
        Fixture fixture = twoModuleFixture(PROBE_APP_SOURCE);
        Path out = fixture.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(out);
            try {
                ProductionProjectEmission.Result result =
                    emit(fixture, Backend.LUAJIT, stager, false);
                check(result.emitted(),
                    "the probe fixture emits: " + result.diagnostics());
                stager.publish();
            } finally {
                stager.discard();
            }
            check(Files.isRegularFile(out.resolve("app.lua")),
                "the published chunk exists at the pinned path");
            ProcessOutcome run = runProcess(List.of("luajit", "app.lua"), out);
            checkEq(0, run.exitCode(), "the published chunk exits 0: " + run.output());
            checkEq("PROBE|MAIN-ONCE\n", run.stdout(),
                "the entry main ran exactly once");
            checkEq("", run.stderr(),
                "the production chunk publishes no trace protocol on stderr");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 3. The real toolchains
    // =========================================================================

    private static void testJvmToolchain() throws Exception {
        System.out.println("-- the staged JVM artifact compiles with javac --release "
            + "25 -proc:none and runs under java --");
        Fixture fixture = twoModuleFixture(APP_SOURCE);
        Path out = fixture.root().resolve("out-arm");
        Path classes = fixture.root().resolve("classes");
        try {
            PublicationStager stager = PublicationStager.forRoot(out);
            try {
                ProductionProjectEmission.Result result =
                    emit(fixture, Backend.JVM, stager, false);
                check(result.emitted(),
                    "the JVM fixture emits: " + result.diagnostics());
                stager.publish();
            } finally {
                stager.discard();
            }
            Path source = out.resolve("App.java");
            check(Files.isRegularFile(source),
                "the published JVM artifact exists at the pinned path");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString()), fixture.root());
            checkEq(0, javacRun.exitCode(),
                "the published JVM artifact compiles: " + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "App"),
                fixture.root());
            checkEq(0, run.exitCode(), "the published JVM artifact runs: "
                + run.output());
            checkEq("", run.stdout(),
                "the successful JVM production run prints nothing on stdout");
            check(!run.stderr().contains("R|"),
                "the executed JVM artifact emits no trace line");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. Atomic failure: a failing lowering; the realized cross-module sync
    //    call emits and stages
    // =========================================================================

    private static void testAtomicFailures() throws Exception {
        System.out.println("-- a failing lowering stages nothing and preserves the "
            + "previous artifact set; the cross-module sync call emits and "
            + "stages --");

        // ISSUE-0626: the bytes allocation now lowers and emits through
        // the one production pipeline (the bytes coverage slice), so the
        // bytes-bearing run stages its one project artifact.
        Fixture bytes = bytesFixture();
        Path bytesOut = bytes.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(bytesOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(bytes, Backend.LUAJIT, stager, false);
                check(result.emitted(), "the bytes-bearing run emits: "
                    + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the bytes allocation carries no diagnostic: "
                        + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the bytes-bearing run stages the entry module's chunk");
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the bytes-bearing run stages its one project artifact");
            } finally {
                stager.discard();
            }
        } finally {
            deleteRecursively(bytes.root());
        }

        // ISSUE-0626: the nested-declaration arm is production-covered (a
        // declaration inside a function body owns its lowering context), so
        // the nested-declaration fixture emits its one project artifact
        // instead of failing closed.
        Fixture nested = nestedDeclarationFixture();
        Path nestedOut = nested.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(nestedOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(nested, Backend.LUAJIT, stager, false);
                check(result.emitted(), "the nested-declaration run emits: "
                    + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the nested declaration carries no diagnostic: "
                        + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the nested-declaration run stages the entry module's chunk");
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the nested-declaration run stages its one project artifact");
            } finally {
                stager.discard();
            }
        } finally {
            deleteRecursively(nested.root());
        }

        // The failing lowering: an arity-extended adapter call whose source
        // identity is not statically fixed (the function-typed-value
        // child's ISSUE-0531 residue) fails CONSTRUCT_UNLOWERED. The live
        // root is pre-populated with a previous artifact set.
        Fixture failing = adapterSourceFixture();
        Path out = failing.root().resolve("out-arm");
        try {
            writeFileIn(out, "app.lua", "-- previous artifact\n");
            writeFileIn(out, "lib.lua", "-- previous sibling\n");
            writeFileIn(out, "deal/runtime.lua", "-- previous runtime\n");
            Map<String, String> before = snapshotTree(out);
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            try {
                result = emit(failing, Backend.LUAJIT, stager, false);
            } finally {
                stager.discard();
            }
            check(!result.emitted(), "the fail-closed run emits nothing");
            check(result.firstDiagnostic() != null
                    && "E6005".equals(result.firstDiagnostic().code()),
                "the failing lowering merges the first E6005: "
                    + result.diagnostics());
            check(result.firstDiagnostic() != null
                    && result.firstDiagnostic().message().contains("CONSTRUCT_UNLOWERED"),
                "the adapter-source construct is the named fail-closed rule: "
                    + result.diagnostics());
            checkEq(before, snapshotTree(out),
                "the failing lowering leaves the previous artifact set byte-identical");
        } finally {
            deleteRecursively(failing.root());
        }

        // ISSUE-0654: a cross-module sync call now emits through the
        // realized CALL(EXTERNAL) SHARED_BODY arm — the callee unit's
        // EXTERNAL_ENTRY runs inside the one project artifact — so the
        // production run stages its one artifact over the previous set
        // (the atomic staging property stays covered by the adapter-source
        // case above, whose lowering fails before any emission).
        Fixture sync = twoModuleFixture(SYNC_CALL_APP_SOURCE);
        Path syncOut = sync.root().resolve("out-arm");
        try {
            writeFileIn(syncOut, "app.lua", "-- previous artifact\n");
            writeFileIn(syncOut, "deal/runtime.lua", "-- previous runtime\n");
            PublicationStager stager = PublicationStager.forRoot(syncOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(sync, Backend.LUAJIT, stager, false);
                check(result.emitted(),
                    "the cross-module sync call emits: " + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the emitted cross-module sync call carries no diagnostic: "
                        + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the cross-module sync call stages the entry module's chunk");
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the cross-module sync call stages its one project artifact");
                String chunk = new String(stager.stagedSet().artifact("app.lua")
                    .orElseThrow().content(), StandardCharsets.UTF_8);
                check(chunk.contains("__module = \"lib\"")
                        && chunk.contains("__modStack[#__modStack + 1] = __module")
                        && chunk.contains("pcall(F")
                        && !chunk.contains("SharedM"),
                    "the staged chunk runs the callee unit's entry under the "
                        + "callee module context and references no per-module "
                        + "artifact");
                check(chunk.contains("__svStack"),
                    "the staged chunk preserves the callee body's private "
                        + "state across the invocation");
            } finally {
                stager.discard();
            }
        } finally {
            deleteRecursively(sync.root());
        }
    }

    // =========================================================================
    // 5. The pre-emission closure guard
    // =========================================================================

    private static void testHostImportGuard() throws Exception {
        System.out.println("-- the HOST-declaration import emits its declared-map "
            + "load and stages; the extern-C declaration import emits its "
            + "load_ffi prelude --");

        // The HOST-declaration-kind import: realized by the host load of
        // the module init walk (H1), so the production run stages its one
        // project artifact and no guard fires.
        Fixture fixture = hostFixture();
        Path out = fixture.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(out);
            ProductionProjectEmission.Result result;
            String chunk;
            try {
                result = emit(fixture, Backend.LUAJIT, stager, false);
                check(result.emitted(),
                    "the HOST-declaration import emits: " + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the HOST-declaration import carries no diagnostic: "
                        + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the HOST-declaration import stages the entry module's chunk");
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the HOST-declaration import stages its one project artifact");
                chunk = new String(stager.stagedSet().artifact("app.lua")
                    .orElseThrow().content(), StandardCharsets.UTF_8);
            } finally {
                stager.discard();
            }
            HostDeclarationSurface.DeclarationFacts facts =
                fixture.surface().require(HOST_CFG);
            checkEq(HostDeclarationSurface.DeclarationKind.HOST, facts.kind(),
                "the fixture's declaration module is HOST-kind");
            String loadPrefix = "__exportSurfaces[\"" + HOST_CFG.path()
                + "\"] = __exportSurfaces[\"" + HOST_CFG.path()
                + "\"] or __rt.load_host(\"" + HOST_CFG_SPECIFIER + "\", ";
            check(chunk.contains(loadPrefix
                    + declaredMapLiteral(fixture.surface(), HOST_CFG) + ", "),
                "the emitted artifact carries the load of " + HOST_CFG_SPECIFIER
                    + " with the declared map in declaration order");
            checkEq(1, countOccurrences(chunk,
                    "__rt.load_host(\"" + HOST_CFG_SPECIFIER + "\""),
                "the host module loads exactly once for the one import op");
            check(chunk.indexOf("__dealMain = function()")
                    < chunk.indexOf("__rt.load_host(\"" + HOST_CFG_SPECIFIER),
                "the load runs inline in the module init walk");
            check(!chunk.contains(ProductionProjectEmission.HOST_MODULE_IMPORT),
                "the emitted chunk carries no guard token");
        } finally {
            deleteRecursively(fixture.root());
        }

        // The extern-C admission (ISSUE-0662): a HOST-kind import whose
        // declaration-surface kind is EXTERN_C (the @extern-c declaration
        // module) is realized by the emitted load_ffi prelude selected from
        // the compile's FFI emission input, so the arm stages its one
        // project artifact and no guard outcome fires. The guard step and
        // its stable HOST_MODULE_IMPORT token stay landed (a superseded
        // shape is replaced, never deleted); the fail-closed seeds of the
        // FFI emission family are the focused suite's.
        Fixture externC = externCFixture();
        Path externCOut = externC.root().resolve("out-arm");
        try {
            checkEq(HostDeclarationSurface.DeclarationKind.EXTERN_C,
                externC.surface().require(NATIVE_MATH).kind(),
                "the probe's declaration module is EXTERN_C-kind");
            PublicationStager stager = PublicationStager.forRoot(externCOut);
            ProductionProjectEmission.Result result;
            String chunk;
            try {
                result = emit(externC, Backend.LUAJIT, stager, false);
                check(result.emitted(),
                    "the extern-C declaration import emits: "
                        + result.diagnostics());
                check(result.diagnostics().isEmpty(),
                    "the extern-C declaration import carries no guard "
                        + "diagnostic: " + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the extern-C declaration import stages the entry "
                        + "module's chunk");
                check(stager.stagedSet().artifact("app.lua").isPresent(),
                    "the extern-C declaration import stages its one project "
                        + "artifact");
                chunk = new String(stager.stagedSet().artifact("app.lua")
                    .orElseThrow().content(), StandardCharsets.UTF_8);
            } finally {
                stager.discard();
            }
            check(chunk.contains("__exportSurfaces[\"" + NATIVE_MATH.path()
                    + "\"] = __exportSurfaces[\"" + NATIVE_MATH.path()
                    + "\"] or __rt.load_ffi(\"ffi:@$external/"
                    + EXTERN_C_SPECIFIER + "\", "),
                "the emitted artifact carries the load_ffi prelude with the "
                    + "metadata-provided module key: " + chunk);
            check(chunk.contains(", \""
                    + externC.root().resolve("src/app.deal").toAbsolutePath()
                    + "\", 1, 1)"),
                "the load carries the import statement's span triplet: "
                    + chunk);
            check(!chunk.contains(ProductionProjectEmission.HOST_MODULE_IMPORT),
                "the emitted chunk carries no guard token");
            check(!chunk.contains("ffi.C") && !chunk.contains("cdef("),
                "the emitted chunk carries no ffi.C/cdef text");
        } finally {
            deleteRecursively(externC.root());
        }
    }

    private static void testCrossModuleAsyncEmission() throws Exception {
        System.out.println("-- the cross-module async call emits through the "
            + "entity-local async entry and executes; a same-module async call "
            + "emits --");

        // The cross-module async call: one project artifact stages, no
        // guard shape fires, and the exported async worker executes the
        // caller's alias-token linkage end-to-end (ISSUE-0655/ISSUE-0656).
        Fixture cross = asyncFixture(ASYNC_LIB_SOURCE, CROSS_ASYNC_APP_SOURCE);
        Path crossOut = cross.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(crossOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(cross, Backend.LUAJIT, stager, false);
                check(result.emitted(),
                    "the cross-module async closure emits: "
                        + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the cross-module async artifact is the entry chunk");
                checkEq(1L, stager.stagedSet().relativePaths().stream()
                        .filter(path -> path.endsWith(".lua")
                            && !path.startsWith("std/")
                            && !path.equals("deal/runtime.lua")).count(),
                    "exactly one staged project artifact");
                stager.publish();
            } finally {
                stager.discard();
            }
            String chunk = Files.readString(crossOut.resolve("app.lua"),
                StandardCharsets.UTF_8);
            check(!chunk.contains("EXTERNAL_ASYNC_CALL"),
                "the emitted chunk carries no superseded guard token");
            check(!chunk.contains("SharedM"),
                "the emitted chunk references no per-module async-entry surface");
            check(chunk.contains("__asyncEntries[\"" + LIB.path()
                    + "#getValue\"]"),
                "the chunk carries one async entry per async export of the "
                    + "callee closure module");
            writeFileIn(cross.root(), "probe.lua", """
                local surfaces = dofile("out-arm/app.lua")
                local worker = surfaces.worker
                assert(type(worker) == "table" and worker.__kind == "function",
                  "the entry surface publishes the cross-module async export")
                local completion = worker.f()
                assert(completion == 42,
                  "the cross-module await completes with 42, got "
                    .. tostring(completion))
                print("PROBE|ASYNC-RESULT|" .. tostring(completion))
                """);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "probe.lua"),
                cross.root());
            checkEq(0, luaRun.exitCode(),
                "the cross-module await path executes under luajit: "
                    + luaRun.output());
            check(luaRun.stdout().contains("PROBE|ASYNC-RESULT|42"),
                "the cross-module await completes with 42 under luajit: "
                    + luaRun.stdout());
        } finally {
            deleteRecursively(cross.root());
        }

        // The JVM target of the same closure: the class source compiles
        // with javac --release 25 -proc:none and the runner executes the
        // exported async function through the artifact's published
        // surface.
        Fixture crossJvm = asyncFixture(ASYNC_LIB_SOURCE, CROSS_ASYNC_APP_SOURCE);
        Path crossJvmOut = crossJvm.root().resolve("out-arm");
        Path crossJvmClasses = crossJvm.root().resolve("cross-classes");
        try {
            PublicationStager stager = PublicationStager.forRoot(crossJvmOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(crossJvm, Backend.JVM, stager, false);
                check(result.emitted(),
                    "the cross-module async JVM closure emits: "
                        + result.diagnostics());
                stager.publish();
            } finally {
                stager.discard();
            }
            String source = Files.readString(crossJvmOut.resolve("App.java"),
                StandardCharsets.UTF_8);
            check(!source.contains("EXTERNAL_ASYNC_CALL"),
                "the emitted JVM class carries no superseded guard token");
            check(!source.contains("SharedM"),
                "the emitted JVM class references no per-module class");
            writeFileIn(crossJvmOut, "AsyncCrossRunner.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class AsyncCrossRunner {
                  public static void main(String[] args) {
                    App.main(new String[0]);
                    JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
                    JvmRuntime.FunctionValue worker =
                        (JvmRuntime.FunctionValue) surface.read("worker");
                    Object completion = worker.fn.invoke(new Object[0]);
                    System.out.println("PROBE|ASYNC-RESULT|" + completion);
                  }
                }
                """);
            Files.createDirectories(crossJvmClasses);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", crossJvmClasses.toString(),
                crossJvmOut.resolve("App.java").toAbsolutePath().toString(),
                crossJvmOut.resolve("AsyncCrossRunner.java").toAbsolutePath().toString()),
                crossJvm.root());
            checkEq(0, javacRun.exitCode(),
                "the cross-module async JVM artifact compiles: "
                    + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + crossJvmClasses,
                    "AsyncCrossRunner"), crossJvm.root());
                checkEq(0, jvmRun.exitCode(),
                    "the cross-module await path executes under java: "
                        + jvmRun.output());
                check(jvmRun.stdout().contains("PROBE|ASYNC-RESULT|42"),
                    "the cross-module await completes with 42 under java: "
                        + jvmRun.stdout());
            }
        } finally {
            deleteRecursively(crossJvm.root());
        }

        // The same-module async call: accepted, emitted, and executed on
        // both targets. The awaiting call is reachable through the
        // exported zero-arity async function's published surface, so the
        // runner's invocation really runs the ASYNC_START(DEAL_BODY)/
        // AWAIT path (never merely compiling a never-invoked body).
        Fixture same = asyncFixture(ASYNC_LIB_SOURCE, SAME_ASYNC_APP_SOURCE);
        Path sameOut = same.root().resolve("out-arm");
        try {
            PublicationStager stager = PublicationStager.forRoot(sameOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(same, Backend.LUAJIT, stager, false);
                check(result.emitted(), "the same-module async closure emits: "
                    + result.diagnostics());
                checkEq("app.lua", result.artifactRelativePath(),
                    "the same-module async artifact is the entry chunk");
                stager.publish();
            } finally {
                stager.discard();
            }
            check(Files.isRegularFile(sameOut.resolve("app.lua")),
                "the published same-module async chunk exists");
            writeFileIn(same.root(), "probe.lua", """
                local surfaces = dofile("out-arm/app.lua")
                assert(type(surfaces) == "table",
                  "the chunk returns the entry surface")
                local worker = surfaces.worker
                assert(type(worker) == "table" and worker.__kind == "function",
                  "the entry surface publishes the same-module async export")
                local completion = worker.f()
                assert(completion == 1,
                  "the awaiting call completes with 1, got "
                    .. tostring(completion))
                print("PROBE|ASYNC-RESULT|" .. tostring(completion))
                """);
            ProcessOutcome luaRun = runProcess(List.of("luajit", "probe.lua"),
                same.root());
            checkEq(0, luaRun.exitCode(),
                "the same-module await path executes under luajit: "
                    + luaRun.output());
            check(luaRun.stdout().contains("PROBE|ASYNC-RESULT|1"),
                "the awaiting call completes with 1 under luajit: "
                    + luaRun.stdout());
        } finally {
            deleteRecursively(same.root());
        }

        // The JVM target of the same fixture: the class source compiles
        // with javac --release 25 -proc:none and the runner executes the
        // exported async function through the artifact's published
        // surface.
        Fixture sameJvm = asyncFixture(ASYNC_LIB_SOURCE, SAME_ASYNC_APP_SOURCE);
        Path jvmOut = sameJvm.root().resolve("out-arm");
        Path jvmClasses = sameJvm.root().resolve("same-classes");
        try {
            PublicationStager stager = PublicationStager.forRoot(jvmOut);
            ProductionProjectEmission.Result result;
            try {
                result = emit(sameJvm, Backend.JVM, stager, false);
                check(result.emitted(),
                    "the same-module async JVM closure emits: "
                        + result.diagnostics());
                stager.publish();
            } finally {
                stager.discard();
            }
            check(Files.isRegularFile(jvmOut.resolve("App.java")),
                "the published same-module async JVM artifact exists");
            writeFileIn(jvmOut, "AsyncWorkerRunner.java", """
                import deal.codegen.jvm.JvmRuntime;

                public final class AsyncWorkerRunner {
                  public static void main(String[] args) {
                    App.main(new String[0]);
                    JvmRuntime.Table surface = App.EXPORT_SURFACES.get("app");
                    JvmRuntime.FunctionValue worker =
                        (JvmRuntime.FunctionValue) surface.read("worker");
                    Object completion = worker.fn.invoke(new Object[0]);
                    System.out.println("PROBE|ASYNC-RESULT|" + completion);
                  }
                }
                """);
            Files.createDirectories(jvmClasses);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", jvmClasses.toString(),
                jvmOut.resolve("App.java").toAbsolutePath().toString(),
                jvmOut.resolve("AsyncWorkerRunner.java").toAbsolutePath().toString()),
                sameJvm.root());
            checkEq(0, javacRun.exitCode(),
                "the same-module async JVM artifact compiles: "
                    + javacRun.output());
            if (javacRun.exitCode() == 0) {
                ProcessOutcome jvmRun = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + jvmClasses,
                    "AsyncWorkerRunner"), sameJvm.root());
                checkEq(0, jvmRun.exitCode(),
                    "the same-module await path executes under java: "
                        + jvmRun.output());
                check(jvmRun.stdout().contains("PROBE|ASYNC-RESULT|1"),
                    "the awaiting call completes with 1 under java: "
                        + jvmRun.stdout());
            }
        } finally {
            deleteRecursively(sameJvm.root());
        }
    }

    // =========================================================================
    // 6. The C9 source-map disposition
    // =========================================================================

    private static void testSourceMapDisposition() throws Exception {
        System.out.println("-- an explicit --source-map prints the pinned warning "
            + "once and stages no sidecar; a --dump-ir-derived flag prints none --");
        Fixture fixture = twoModuleFixture(APP_SOURCE);
        Path out = fixture.root().resolve("out-arm");
        try {
            PublicationStager explicitStager = PublicationStager.forRoot(out);
            String explicitStderr;
            try {
                explicitStderr = emitCapturingStderr(fixture, Backend.LUAJIT,
                    explicitStager, true);
                for (String path : explicitStager.stagedSet().relativePaths()) {
                    check(!path.endsWith(".deal.map.json"),
                        "the explicit --source-map compile stages no sidecar: " + path);
                }
            } finally {
                explicitStager.discard();
            }
            checkEq(ProductionProjectEmission.WARNING_LUAJIT + "\n", explicitStderr,
                "the explicit LuaJIT --source-map warning is the pinned text, once");
            checkEq(1, countOccurrences(explicitStderr, "Warning:"),
                "the pinned warning prints exactly once");

            PublicationStager derivedStager =
                PublicationStager.forRoot(fixture.root().resolve("derived-out"));
            String derivedStderr;
            try {
                derivedStderr = emitCapturingStderr(fixture, Backend.LUAJIT,
                    derivedStager, false);
            } finally {
                derivedStager.discard();
            }
            checkEq("", derivedStderr,
                "a --dump-ir-derived source-map flag prints no warning");

            PublicationStager jvmStager =
                PublicationStager.forRoot(fixture.root().resolve("jvm-map-out"));
            String jvmStderr;
            try {
                jvmStderr = emitCapturingStderr(fixture, Backend.JVM, jvmStager, true);
            } finally {
                jvmStager.discard();
            }
            checkEq(ProductionProjectEmission.WARNING_JVM + "\n", jvmStderr,
                "the explicit JVM --source-map warning is the pinned text, once");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /** The published/previous artifact set of one tree: path → bytes. */
    private static Map<String, String> snapshotTree(Path root) throws Exception {
        Map<String, String> snapshot = new java.util.TreeMap<>();
        if (!Files.exists(root)) {
            return snapshot;
        }
        try (var walk = Files.walk(root)) {
            for (Path file : walk.sorted().toList()) {
                if (Files.isRegularFile(file)) {
                    snapshot.put(root.relativize(file).toString().replace('\\', '/'),
                        java.util.Arrays.toString(Files.readAllBytes(file)));
                }
            }
        }
        return snapshot;
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
        System.out.println("=== Production Project Emission Tests (ISSUE-0642) ===\n");
        testUnitShapeAndConstants();
        testOneArtifactPerTarget();
        testOneMainProbe();
        testJvmToolchain();
        testAtomicFailures();
        testHostImportGuard();
        testCrossModuleAsyncEmission();
        testSourceMapDisposition();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Production Project Emission Tests Passed ===");
    }
}
