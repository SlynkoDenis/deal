package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmBackend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.types.Type;

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
 * ISSUE-0650: the host module load and the JVM host ABI emission surface
 * (design source {@code host-module-load-and-host-call-realization} H1,
 * H2 items 1-2, H7's carrier set, and the host-load contract;
 * {@code luajit-jvm-single-lowering-production-cutover} C2).
 *
 * <ol>
 *   <li><b>LuaJIT load.</b> The {@code MODULE_IMPORT(HOST)} op emits the
 *       load inline at its position in the module init walk
 *       ({@code __exportSurfaces[<resolved module>] = ... or
 *       __rt.load_host(<rawSpecifier>, { <declared map> }, file, line,
 *       column)}), with the declared map in declaration order and the
 *       import statement's span as the origin; the loaded table is
 *       published in the same registry {@code EXPORT_PUBLISH}/
 *       {@code EXPORT_READ} use; exactly one load happens per imported
 *       module per program (a two-alias import produces one load and one
 *       shared surface value).</li>
 *   <li><b>LuaJIT defects.</b> The pinned E8011 failures (missing
 *       declared export at the import origin, class identity mismatch,
 *       missing {@code <C>_defaults}) fail the importing module's init
 *       with the host-module-abi texts.</li>
 *   <li><b>JVM surface.</b> The artifact carries the module-keyed load
 *       entry (idempotent per module; {@code Class.forName} of the
 *       {@code classNameFor(rawSpecifier)} derivation), the declared
 *       function bindings with the declared parameter-class projection,
 *       the {@code <C>_defaults} captures, the per-export wrappers with
 *       the declared parameter/return cells and the pinned E8010 texts,
 *       and the synthesized {@code $DealRt} host-record and host-carrier
 *       scope the deployed host fixtures compile against.</li>
 *   <li><b>Real toolchains.</b> The chunk executes under {@code luajit}
 *       (the host module loads once, both aliases observe one surface);
 *       the class compiles with {@code javac --release 25 -proc:none}
 *       together with the deployed {@code test/conformance/host-fixtures}
 *       sources, and the emitted wrappers run under {@code java} with the
 *       pinned E8010 parameter/return texts.</li>
 *   <li><b>Signature extension.</b> The production emitter entries take
 *       the host declaration surface (the single declared-map source) and
 *       {@code ProductionProjectEmission.run} passes its received surface
 *       through to both.</li>
 * </ol>
 */
public class HostModuleLoadEmissionTest {

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

    private static final String PROBE_SPECIFIER = "host/abi_probe";
    private static final String CFG_SPECIFIER = "host/cfg";
    private static final String MISSING_SPECIFIER = "host/missing_export";

    /** The host ABI declaration: scalar, array, function, bytes, and async positions. */
    private static final String ABI_DECLARATION_SOURCE = """
        export function ping(): string;
        export function echoInt(v: int): int;
        export function badReturn(): int;
        export function join(sep: string, parts: string[]): string;
        export function apply(f: (x: int) => int, v: int): int;
        export async function fetchValue(): string;
        export function echoBytes(b: bytes): bytes;
        export function nullable(v: string | null): string | null;
        """;

    /** The declared-class declaration (the synthesized record and array carriers). */
    private static final String CFG_DECLARATION_SOURCE = """
        export class Endpoint {
          path: string;
        }

        export class ServerConfig {
          port: int;
          endpoint: Endpoint;
          tags?: string[];
          note?: string | null;
        }

        export function describe(s: ServerConfig): string;
        """;

    /**
     * The missing-export declaration: the raw implementation omits the
     * declared {@code missing} export, so the load raises the pinned E8011
     * at the import origin. The import sits on line 6 column 1 exactly like
     * the corpus fixture {@code host-abi/host-missing-export.deal}.
     */
    private static final String MISSING_DECLARATION_SOURCE = """
        export function missing(): string;
        export function ping(): string;
        """;

    private static final String MISSING_APP_SOURCE = """
        // spec: Modules, declarations, standard library, and host ABI
        // description: A declared host export missing from the raw implementation is a load-time error (E8011).
        // expected: runtime-error E8011
        // features: modules, host-abi, runtime-errors

        import * as host from "host/missing_export"

        export function test_host_missing_export(): string {
          return "unreachable";
        }

        export function main(): null {
          return null;
        }
        """;

    /** The ABI-importing application (no host call: the call arms are a later slice). */
    private static final String ABI_APP_SOURCE = """
        import * as probe from "host/abi_probe"
        import * as cfg from "host/cfg"

        export function main(): null {
          return null;
        }
        """;

    /** The two-alias import of one host module (one load, one surface value). */
    private static final String TWO_ALIAS_APP_SOURCE = """
        import * as first from "host/abi_probe"
        import * as second from "host/abi_probe"
        import * as cfg from "host/cfg"

        export function main(): null {
          return null;
        }
        """;

    private static final String MISSING_DECLARATION_APP_SOURCE = MISSING_APP_SOURCE;

    /** The deployed LuaJIT host implementation of host/abi_probe. */
    private static final String PROBE_LUA = """
        _HOST_PROBE_LOADS = (_HOST_PROBE_LOADS or 0) + 1
        return {
          ping = function() return "pong" end,
          echoInt = function(v) return v end,
          badReturn = function() return "junk" end,
          join = function(sep, parts) return table.concat(parts, sep) end,
          apply = function(f, v) return f(v) + 100 end,
          fetchValue = function()
            local rt = require("deal.runtime")
            return rt.async_start(function() return "fetched" end)
          end,
          echoBytes = function(b) return b end,
          nullable = function(v) return v end,
        }
        """;

    /**
     * The deployed LuaJIT host implementation of host/cfg (valid shapes). The
     * class identities equal the declared descriptors the emitted declared map
     * carries for this fixture's externals classification (the corpus lane's
     * dotted typing name is a lane-classification concern).
     */
    private static final String CFG_LUA = """
        _HOST_CFG_LOADS = (_HOST_CFG_LOADS or 0) + 1
        local rt = require("deal.runtime")
        return {
          Endpoint = { __kind = "class", __classname = "@$external/host/cfg/Endpoint" },
          Endpoint_defaults = { path = "/" },
          ServerConfig = { __kind = "class", __classname = "@$external/host/cfg/ServerConfig" },
          ServerConfig_defaults = { port = 8080, endpoint = rt.__MISSING, tags = rt.__MISSING, note = rt.__MISSING },
          describe = function(s) return s.endpoint.path .. ":" .. tostring(s.port) end,
        }
        """;

    /** The raw implementation of host/missing_export (omits the declared export). */
    private static final String MISSING_LUA = """
        return {
          ping = function() return "pong" end,
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
        Map<String, String> externals) {
    }

    /**
     * The harness invocation of the fixture compile: the orchestrator builds
     * the checked project and the declaration surface through its harness
     * arm, while this test drives the one project lowering and the
     * production emitter entries directly (the ISSUE-0656 guard replacement
     * lets a host import reach the production arm).
     */
    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32,
            deal.semantic.ir.ReleaseState.V1_2_ACTIVE,
            deal.semantic.CapabilityRegistry.releaseRegistry());
    }

    /** The release-owned production invocation (the lowering profile). */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            deal.semantic.ReleaseConfiguration.CURRENT_RELEASE_STATE,
            deal.semantic.ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources,
            Map<String, String> externals) throws Exception {
        Path root = Files.createTempDirectory("host-load-fixture");
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
            for (Map.Entry<String, String> external : externals.entrySet()) {
                if (external.getKey().replace('/', '.').equals(declarationModule.path())
                        || external.getKey().equals(declarationModule.path())) {
                    specifier = external.getKey();
                    break;
                }
            }
            identities.put(declarationModule, specifier == null
                ? IdentityTestFixtures.moduleIdentityOf(declarationModule.path())
                : new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            surface, externCModules, identities, externals);
    }

    private static Fixture abiFixture(String appSource) throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/abi_probe.d.deal", ABI_DECLARATION_SOURCE);
        sources.put("src/cfg.d.deal", CFG_DECLARATION_SOURCE);
        sources.put("src/app.deal", appSource);
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(PROBE_SPECIFIER, "src/abi_probe.d.deal");
        externals.put(CFG_SPECIFIER, "src/cfg.d.deal");
        return compileProject(sources, externals);
    }

    private static Fixture missingFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/missing_export.d.deal", MISSING_DECLARATION_SOURCE);
        sources.put("src/app.deal", MISSING_DECLARATION_APP_SOURCE);
        return compileProject(sources,
            Map.of(MISSING_SPECIFIER, "src/missing_export.d.deal"));
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.declarationIdentities(),
            fixture.externCModules(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
            Set.of());
    }

    /** The resolved module identity of one host import of the lowered project. */
    private static ModuleId hostImportModule(ExecutableLoweredProject project,
            String rawSpecifier) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.MODULE_IMPORT) {
                    continue;
                }
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                if (payload.kind() == ModuleImportKind.HOST
                        && payload.rawSpecifier().equals(rawSpecifier)) {
                    return payload.resolvedModule();
                }
            }
        }
        throw new IllegalStateException("no host import of '" + rawSpecifier + "'");
    }

    private static SemanticOp hostImportOp(ExecutableLoweredProject project,
            String rawSpecifier) {
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.MODULE_IMPORT) {
                    continue;
                }
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) op.payload();
                if (payload.kind() == ModuleImportKind.HOST
                        && payload.rawSpecifier().equals(rawSpecifier)) {
                    return op;
                }
            }
        }
        throw new IllegalStateException("no host import of '" + rawSpecifier + "'");
    }

    /** The emitted declared-map literal of one host import (declaration order). */
    private static String declaredMapLiteral(HostDeclarationSurface surface,
            ModuleId module) {
        HostDeclarationSurface.DeclarationFacts facts = surface.require(module);
        StringBuilder map = new StringBuilder("{");
        boolean first = true;
        for (Map.Entry<String, Type> export : facts.exports().entrySet()) {
            if (!first) {
                map.append(", ");
            }
            first = false;
            map.append("[\"").append(export.getKey()).append("\"] = \"")
                .append(DescriptorService.describe(export.getValue())
                    .canonicalSpecText())
                .append("\"");
        }
        return map.append("}").toString();
    }

    // =========================================================================
    // 1. The LuaJIT load: the artifact text
    // =========================================================================

    private static void testLuaArtifactText() throws Exception {
        System.out.println("-- the LuaJIT load: the inline load with the declared map "
            + "and the import origin --");
        Fixture fixture = abiFixture(ABI_APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null,
                "the host-importing fixture lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            String lua = LuaSemanticEmitter.emitProductionProject(project,
                result.tables(), result.registries(), fixture.surface());

            ModuleId probeModule = hostImportModule(project, PROBE_SPECIFIER);
            SemanticOp probeImport = hostImportOp(project, PROBE_SPECIFIER);
            ModuleId cfgModule = hostImportModule(project, CFG_SPECIFIER);
            String probeKey = "\"" + probeModule.path() + "\"";
            String probeLoad = "__exportSurfaces[" + probeKey + "] = "
                + "__exportSurfaces[" + probeKey + "] or __rt.load_host("
                + "\"" + PROBE_SPECIFIER + "\", "
                + declaredMapLiteral(fixture.surface(), probeModule) + ", "
                + probeImport.origin().sourceId() + "\", "
                + probeImport.origin().span().startLine() + ", "
                + probeImport.origin().span().startColumn() + ")";
            // The emitted origin atom is a Lua string literal: rebuild the
            // expected line with the quoted source id.
            String expectedProbe = "__exportSurfaces[" + probeKey + "] = "
                + "__exportSurfaces[" + probeKey + "] or __rt.load_host("
                + "\"" + PROBE_SPECIFIER + "\", "
                + declaredMapLiteral(fixture.surface(), probeModule) + ", \""
                + probeImport.origin().sourceId() + "\", "
                + probeImport.origin().span().startLine() + ", "
                + probeImport.origin().span().startColumn() + ")";
            check(lua.contains(expectedProbe),
                "the artifact carries the inline load of " + PROBE_SPECIFIER
                    + " with the declared map in declaration order: " + expectedProbe);
            check(!lua.contains(probeLoad),
                "the origin is the import statement's quoted source id");

            String expectedCfg = "__exportSurfaces[\"" + cfgModule.path() + "\"] = "
                + "__exportSurfaces[\"" + cfgModule.path() + "\"] or __rt.load_host("
                + "\"" + CFG_SPECIFIER + "\", "
                + declaredMapLiteral(fixture.surface(), cfgModule) + ", \""
                + hostImportOp(project, CFG_SPECIFIER).origin().sourceId() + "\", "
                + hostImportOp(project, CFG_SPECIFIER).origin().span().startLine()
                + ", "
                + hostImportOp(project, CFG_SPECIFIER).origin().span().startColumn()
                + ")";
            check(lua.contains(expectedCfg),
                "the artifact carries the inline load of " + CFG_SPECIFIER
                    + " with its declared map: " + expectedCfg);

            // The class export carries the canonical class descriptor text and
            // the function exports their canonical function descriptor texts.
            HostDeclarationSurface.DeclarationFacts cfgFacts =
                fixture.surface().require(cfgModule);
            String classDescriptor = DescriptorService.describe(
                cfgFacts.exports().get("ServerConfig")).canonicalSpecText();
            check(classDescriptor.startsWith("@"),
                "the declared class export carries a canonical class descriptor: "
                    + classDescriptor);
            check(lua.contains("[\"ServerConfig\"] = \"" + classDescriptor + "\""),
                "the declared map carries the class export's canonical descriptor");

            // The load is inside the module init walk (after __dealMain).
            int walk = lua.indexOf("__dealMain = function()");
            int loadAt = lua.indexOf("__rt.load_host(\"" + PROBE_SPECIFIER + "\"");
            check(walk >= 0 && loadAt > walk,
                "the load runs inline in the module init walk");

            // Exactly one load statement per import op; two aliases of one
            // module share the registry key and the `or` guard.
            Fixture aliases = abiFixture(TWO_ALIAS_APP_SOURCE);
            try {
                SemanticLowerer.ProjectLoweringResult aliasResult = lower(aliases);
                if (aliasResult.project() == null) {
                    fail("the two-alias fixture lowers: " + aliasResult.diagnostics());
                    return;
                }
                ExecutableLoweredProject aliasProject = aliasResult.project();
                String aliasLua = LuaSemanticEmitter.emitProductionProject(aliasProject,
                    aliasResult.tables(), aliasResult.registries(), aliases.surface());
                ModuleId aliasModule = hostImportModule(aliasProject, PROBE_SPECIFIER);
                checkEq(2, countOccurrences(aliasLua,
                        "__rt.load_host(\"" + PROBE_SPECIFIER + "\""),
                    "one guarded load statement per import op");
                checkEq(2, countOccurrences(aliasLua,
                        "__exportSurfaces[\"" + aliasModule.path() + "\"] = "
                            + "__exportSurfaces[\"" + aliasModule.path() + "\"] or"),
                    "both aliases write the one module-keyed registry entry through "
                        + "the identity guard");
            } finally {
                deleteRecursively(aliases.root());
            }

            checkEq(lua, LuaSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), fixture.surface()),
                "the repeated production emission is byte-identical");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The LuaJIT load under real luajit
    // =========================================================================

    private static void testLuaExecution() throws Exception {
        System.out.println("-- the LuaJIT load under real luajit: one load per "
            + "module, one shared surface value, the pinned E8011 --");
        Fixture fixture = abiFixture(TWO_ALIAS_APP_SOURCE);
        Path workspace = Files.createTempDirectory("host-load-lua");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the two-alias fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId probeModule = hostImportModule(project, PROBE_SPECIFIER);
            ModuleId cfgModule = hostImportModule(project, CFG_SPECIFIER);
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), fixture.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            writeFileIn(workspace, "host/abi_probe.lua", PROBE_LUA);
            writeFileIn(workspace, "host/cfg.lua", CFG_LUA);

            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaLoadProbe(artifact, probeModule, cfgModule),
                StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace, true);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the loaded surface is the import's namespace value, one load "
                    + "happens per module, and the second drive keeps the surface "
                    + "identity: exit=" + run.exitCode() + " stdout="
                    + escaped(run.stdout()) + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }

        // The pinned E8011 at the import origin (6:1, the corpus pin).
        Fixture missing = missingFixture();
        checkLuaSeed(missing, "host/missing_export.lua", MISSING_LUA,
            "missing host export 'missing' in module 'host/missing_export'", 6, 1,
            "missing-export-at-6:1");
        // The declared-map defects of the host-module-abi loader contract:
        // a pre-wrapped export whose .f is not a function, a pre-wrapped
        // signature mismatch, and a non-table module result.
        checkLuaSeed(missing, "host/missing_export.lua",
            "return { ping = function() return \"pong\" end,\n"
                + "  missing = { __kind = \"function\", sig = \"()->string\", f = 42 } }\n",
            "host export 'missing' in module 'host/missing_export' has non-function .f",
            -1, -1, "prewrapped-non-function-f");
        checkLuaSeed(missing, "host/missing_export.lua",
            "return { ping = function() return \"pong\" end,\n"
                + "  missing = { __kind = \"function\", sig = \"(int)->string\", "
                + "f = function() end } }\n",
            "host export 'missing' in module 'host/missing_export' has signature "
                + "mismatch: expected ()->string, got (int)->string",
            -1, -1, "prewrapped-signature-mismatch");
        checkLuaSeed(missing, "host/missing_export.lua", "return 42\n",
            "host module 'host/missing_export' did not return a table",
            -1, -1, "non-table-module-result");
        checkLuaSeed(missing, "host/missing_export.lua",
            "return { ping = function() return \"pong\" end, missing = 42 }\n",
            "host export 'missing' in module 'host/missing_export' is not a function",
            -1, -1, "non-function-export-shape");
        deleteRecursively(missing.root());

        // The declared-class seeds: a class identity mismatch, a missing
        // <C>_defaults, and a present-but-non-table <C>_fields all fail the
        // init with their pinned E8011.
        Fixture cfgFixture = cfgOnlyFixture();
        checkLuaSeed(cfgFixture, "host/cfg.lua",
            CFG_LUA.replace("@$external/host/cfg/ServerConfig",
                "@$external/host/cfg/Other"),
            "host class export 'ServerConfig' in module 'host/cfg' has identity "
                + "mismatch: expected @$external/host/cfg/ServerConfig, got "
                + "@$external/host/cfg/Other",
            -1, -1, "cfg-identity-mismatch");
        checkLuaSeed(cfgFixture, "host/cfg.lua",
            CFG_LUA.replace("ServerConfig_defaults", "ServerConfig_other"),
            "host class 'ServerConfig' in module 'host/cfg' is missing its "
                + "defaults table",
            -1, -1, "cfg-missing-defaults");
        checkLuaSeed(cfgFixture, "host/cfg.lua",
            CFG_LUA.replace("ServerConfig_defaults = { port = 8080,",
                "ServerConfig_defaults = 42, ServerConfig_ignored = {"),
            "host class 'ServerConfig' in module 'host/cfg' is missing its "
                + "defaults table",
            -1, -1, "cfg-non-table-defaults");
        checkLuaSeed(cfgFixture, "host/cfg.lua",
            CFG_LUA.replace(
                "ServerConfig = { __kind = \"class\", __classname = "
                    + "\"@$external/host/cfg/ServerConfig\" }",
                "ServerConfig = 42"),
            "host export 'ServerConfig' in module 'host/cfg' is not a class meta "
                + "table",
            -1, -1, "cfg-invalid-class-shape");
        checkLuaSeed(cfgFixture, "host/cfg.lua",
            CFG_LUA.replace("describe = function(s)",
                "Endpoint_fields = 42, describe = function(s)"),
            "host class 'Endpoint' in module 'host/cfg' supplies a non-table _fields "
                + "value",
            -1, -1, "cfg-non-table-fields");
        deleteRecursively(cfgFixture.root());
    }

    /**
     * One LuaJIT seed drive: the fixture's artifact runs under real luajit
     * with the given raw host implementation and the importing module's init
     * must fail with the pinned E8011 (and, when the seed pins it, the
     * import origin).
     */
    private static void checkLuaSeed(Fixture fixture, String hostFile,
            String rawLua, String expectedMessage, int line, int column,
            String label) throws Exception {
        Path workspace = Files.createTempDirectory("host-load-lua-seed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the seed fixture '" + label + "' lowers: " + result.diagnostics());
                return;
            }
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                fixture.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            writeFileIn(workspace, hostFile, rawLua);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe, luaFailureProbe(artifact, expectedMessage,
                line, column), StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace, true);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the negative seed '" + label + "' fails with the pinned E8011: "
                    + "exit=" + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(workspace);
        }
    }

    private static Fixture cfgOnlyFixture() throws Exception {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/cfg.d.deal", CFG_DECLARATION_SOURCE);
        sources.put("src/app.deal", """
            import * as cfg from "host/cfg"

            export function main(): null {
              return null;
            }
            """);
        return compileProject(sources, Map.of(CFG_SPECIFIER, "src/cfg.d.deal"));
    }

    /** The LuaJIT probe: one load per module, one surface value, its entries. */
    private static String luaLoadProbe(Path artifact, ModuleId probeModule,
            ModuleId cfgModule) {
        return """
            local function fail(message)
              print("PROBE-FAIL: " .. message)
              os.exit(1)
            end
            local rt = require("deal.runtime")
            local loads = {}
            local total = 0
            local realLoad = rt.load_host
            rt.load_host = function(module_path, ...)
              total = total + 1
              loads[module_path] = (loads[module_path] or 0) + 1
              return realLoad(module_path, ...)
            end
            local entry = dofile("%s")
            local ok, err = __dealMain()
            if not ok then
              fail("init failed: type=" .. type(err) .. " value=" .. tostring(err)
                .. " message=" .. tostring(type(err) == "table" and err.message)
                .. " file=" .. tostring(type(err) == "table" and err.file)
                .. " line=" .. tostring(type(err) == "table" and err.line))
            end
            if total ~= 2 then fail("load_host calls: " .. total) end
            if loads["host/abi_probe"] ~= 1 then
              fail("host/abi_probe loads: " .. tostring(loads["host/abi_probe"]))
            end
            if loads["host/cfg"] ~= 1 then
              fail("host/cfg loads: " .. tostring(loads["host/cfg"]))
            end
            if (_HOST_PROBE_LOADS or 0) ~= 1 then
              fail("host module side effects: " .. tostring(_HOST_PROBE_LOADS))
            end
            if (_HOST_CFG_LOADS or 0) ~= 1 then
              fail("host cfg side effects: " .. tostring(_HOST_CFG_LOADS))
            end
            local surface = __exportSurfaces["%s"]
            if type(surface) ~= "table" then fail("no probe surface") end
            local ping = surface["ping"]
            if type(ping) ~= "table" or ping.__kind ~= "function" then
              fail("the loaded entry is not the wrapped function table")
            end
            if type(ping.f) ~= "function" then fail("the loaded entry has no callable") end
            if ping.sig ~= "()->string" then fail("the loaded wrapper sig: " .. tostring(ping.sig)) end
            if ping.f() ~= "pong" then fail("the loaded wrapper call") end
            local cfgSurface = __exportSurfaces["%s"]
            if type(cfgSurface) ~= "table" then fail("no cfg surface") end
            if type(cfgSurface["ServerConfig_defaults"]) ~= "table" then
              fail("the loaded <C>_defaults copy-through")
            end
            local before = surface
            __moduleStates = {}
            local ok2 = __dealMain()
            if not ok2 then fail("the second drive failed") end
            if total ~= 2 then
              fail("second-drive load_host calls: " .. total)
            end
            if loads["host/abi_probe"] ~= 1 then
              fail("second-drive host/abi_probe loads")
            end
            if __exportSurfaces["%s"] ~= before then fail("surface identity changed") end
            if entry ~= __exportSurfaces["app"] then fail("the chunk return surface") end
            print("PROBE-OK")
            """.formatted(artifact.toAbsolutePath().toString(),
                probeModule.path(), cfgModule.path(), probeModule.path());
    }

    /** The LuaJIT failure probe: the init fails with the pinned E8011. */
    private static String luaFailureProbe(Path artifact, String message,
            int line, int column) {
        StringBuilder lua = new StringBuilder();
        lua.append("local function fail(m) print(\"PROBE-FAIL: \" .. m) os.exit(1) end\n");
        lua.append("dofile(\"").append(artifact.toAbsolutePath().toString())
            .append("\")\n");
        lua.append("local ok, err = __dealMain()\n");
        lua.append("if ok then fail(\"the init succeeded\") end\n");
        lua.append("if type(err) ~= \"table\" or err.code ~= \"E8011\" then fail(\"code: \" .. tostring(err and err.code)) end\n");
        lua.append("if err.message ~= ").append(luaString(message))
            .append(" then fail(\"message: \" .. tostring(err.message)) end\n");
        if (line > 0) {
            lua.append("if err.line ~= ").append(line)
                .append(" then fail(\"line: \" .. tostring(err.line)) end\n");
            lua.append("if err.column ~= ").append(column)
                .append(" then fail(\"column: \" .. tostring(err.column)) end\n");
        }
        lua.append("print(\"PROBE-OK\")\n");
        return lua.toString();
    }

    // =========================================================================
    // 3. The JVM host ABI emission surface: the artifact text
    // =========================================================================

    private static void testJvmArtifactText() throws Exception {
        System.out.println("-- the JVM artifact: the module-keyed load entry, the "
            + "declared parameter classes, the defaults capture, the wrapper cells, "
            + "and the $DealRt scope --");
        Fixture fixture = abiFixture(ABI_APP_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the host-importing fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            String source = emission.source();

            ModuleId probeModule = hostImportModule(project, PROBE_SPECIFIER);
            ModuleId cfgModule = hostImportModule(project, CFG_SPECIFIER);
            String probeKey = JvmBackend.escapedIdentifier(probeModule.path());
            String cfgKey = JvmBackend.escapedIdentifier(cfgModule.path());

            check(source.contains("static boolean __hostLoaded$" + probeKey + ";"),
                "the load entry is module-keyed and idempotent (the loaded flag)");
            checkEq(1, countOccurrences(source,
                    "static void __hostLoad$" + probeKey
                        + "(java.lang.String oFile, int oLine, int oCol) {"),
                "exactly one load entry per host module");
            check(source.contains("__h = java.lang.Class.forName(\"HostAbi_probe\");"),
                "the implementation class resolves through the classNameFor(rawSpecifier) "
                    + "derivation");
            check(source.contains("__h = java.lang.Class.forName(\"HostCfg\");"),
                "the second host module resolves its own implementation class");

            // The declared function bindings with the declared parameter-class
            // projection in declaration order.
            check(source.contains("__hostM$" + probeKey + "$ping = __hostMethod(__h, "
                    + "\"host/abi_probe\", \"ping\", \"()->string\", "
                    + "new java.lang.Class[]{  }, oFile, oLine, oCol);"),
                "the string export binds through the landed __hostMethod shape");
            check(source.contains("__hostM$" + probeKey + "$echoInt = __hostMethod(__h, "
                    + "\"host/abi_probe\", \"echoInt\", \"(int)->int\", "
                    + "new java.lang.Class[]{ int.class }, oFile, oLine, oCol);"),
                "a declared int parameter resolves to its primitive carrier class");
            check(source.contains("\"join\", \"(string,[string])->string\", "
                    + "new java.lang.Class[]{ java.lang.String.class, "
                    + "$DealRt.__StringArray.class }"),
                "a declared string[] parameter resolves to its element-shape carrier");
            check(source.contains("\"apply\", \"((int)->int,int)->int\", "
                    + "new java.lang.Class[]{ $DealRt.Fn1_I_R_I.class, int.class }"),
                "a declared function position resolves to its per-signature wrapper class");
            check(source.contains("\"echoBytes\", \"(bytes)->bytes\", "
                    + "new java.lang.Class[]{ $DealRt.Bytes.class }"),
                "a declared bytes position resolves to the Bytes carrier");
            check(source.contains("\"nullable\", \"(?string)->?string\", "
                    + "new java.lang.Class[]{ java.lang.String.class }"),
                "a nullable declared position resolves to its boxed carrier");
            String classDescriptor = DescriptorService.describe(
                fixture.surface().require(cfgModule).exports().get("ServerConfig"))
                .canonicalSpecText();
            check(source.contains("\"describe\", \"(" + classDescriptor
                    + ")->string\", new java.lang.Class[]{ "
                    + "$DealRt.$Host$host$scfg$ServerConfig.class }"),
                "a declared class position resolves to the synthesized record: "
                    + classDescriptor);

            // The <C>_defaults capture.
            check(source.contains("__hostD$" + cfgKey + "$ServerConfig = __hostDefaults("
                    + "__h, \"host/cfg\", \"ServerConfig\", oFile, oLine, oCol);"),
                "the declared class export captures its mandatory <C>_defaults map");
            check(source.contains("\"host class '\" + name + \"' in module '\" + module "
                    + "+ \"' is missing its defaults field (\" + name + \"_defaults)\""),
                "the pinned missing-defaults E8011 text is emitted");
            check(source.contains("throw JvmRuntime.fail(\"E8011\", \"missing host "
                    + "export '\" + name + \"' in module '\" + module + \"'\""),
                "the pinned missing-export E8011 text is emitted");

            // The per-export wrappers: the declared parameter cells in one-based
            // order and the declared return cell.
            check(source.contains("static int __host$" + probeKey + "$echoInt("
                    + "java.lang.Object __a0, java.lang.String oFile, int oLine, int oCol) {"),
                "the wrapper carries the declared return carrier");
            check(source.contains("__a0 = __hostParamCheck(1, \"bytes\", __a0, "
                    + "oFile, oLine, oCol);"),
                "the parameter cell runs the declared descriptor in one-based order");
            check(source.contains("__hostParamCheck(2, \"[string]\", __a1, "
                    + "oFile, oLine, oCol);"),
                "the second parameter cell carries its declared descriptor");
            check(source.contains("return ((java.lang.Integer) __hostCheck(\"int\", "
                    + "__r, false, oFile, oLine, oCol)).intValue();"),
                "the sync return cell runs the declared descriptor");
            check(source.contains("throw JvmRuntime.fail(\"E8010\", \"return value 1 "
                    + "type mismatch: expected int, got nothing\""),
                "the presence rule emits the pinned 'got nothing' return text");
            check(source.contains("throw JvmRuntime.fail(\"E8010\", \"parameter \" + i "
                    + "+ \" type mismatch: \" + __hostInnerMessage(desc, v, __inner)"),
                "the parameter cell emits the pinned E8010 parameter text");
            check(source.contains("throw JvmRuntime.fail(\"E8010\", \"return value 1 "
                    + "type mismatch: \" + __hostInnerMessage(desc, v, __inner)"),
                "the return cell emits the pinned E8010 return text");
            check(source.contains("host async function must return an async operation, "
                    + "got \" + __hostKind(__r)"),
                "the declared async export runs the operation-shape check");

            // The synthesized host-record and host-carrier scope.
            check(source.contains("class $DealRt {"),
                "the artifact carries the top-level $DealRt scope");
            check(source.contains("interface FnValue { java.lang.String descriptor(); }"),
                "the scope carries the FnValue interface");
            check(source.contains("static abstract class Fn1_I_R_I implements FnValue {"),
                "the scope carries the per-signature wrapper class of the declared "
                    + "function position");
            check(source.contains("static final class __StringArray {"),
                "the scope carries the declared element-shape array carriers");
            check(source.contains("static final class Bytes {"),
                "the scope carries the declared bytes descriptor's carrier type");
            check(source.contains("static final class $Host$host$scfg$ServerConfig {")
                    && source.contains("$Host$host$scfg$ServerConfig(int port,"),
                "the scope carries one synthesized record per declared host class with "
                    + "its declared fields in declaration order");
            check(source.contains("static final class $HostArr$host$scfg$ServerConfig "
                    + "extends __RefArray {"),
                "the scope carries the per-class array carrier of a declared class element");

            checkEq(source, JvmSemanticEmitter.emitProductionProject(project,
                    result.tables(), result.registries(), className,
                    fixture.surface()).source(),
                "the repeated production emission is byte-identical");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The JVM artifact under javac and java: the deployed host fixtures
    //    compile, the wrappers run the pinned cells
    // =========================================================================

    private static void testJvmToolchain() throws Exception {
        System.out.println("-- the JVM artifact under javac + java: the deployed host "
            + "fixtures compile and the wrapper cells run --");
        Fixture fixture = abiFixture(ABI_APP_SOURCE);
        Path workspace = Files.createTempDirectory("host-load-jvm");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the host-importing fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Path source = workspace.resolve(className + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);

            ModuleId probeModule = hostImportModule(project, PROBE_SPECIFIER);
            ModuleId cfgModule = hostImportModule(project, CFG_SPECIFIER);
            String probeKey = JvmBackend.escapedIdentifier(probeModule.path());
            String cfgKey = JvmBackend.escapedIdentifier(cfgModule.path());

            // The deployed host implementations of the fixture declarations.
            Files.writeString(workspace.resolve("HostAbi_probe.java"), HOST_ABI_JAVA,
                StandardCharsets.UTF_8);
            // The deployed corpus host implementations: they must compile
            // unchanged against the synthesized scope. The JVM lane deploys
            // each <name>.java under its classNameFor("host/<name>") name
            // (the public classes' file-name rule).
            List<String> corpusHostSources = new ArrayList<>();
            Path corpusHost = Path.of("test", "conformance", "host-fixtures");
            try (var listing = Files.list(corpusHost)) {
                for (Path file : listing.sorted().toList()) {
                    String fileName = file.getFileName().toString();
                    if (!fileName.endsWith(".java")) {
                        continue;
                    }
                    String stem = fileName.substring(0, fileName.length() - ".java".length());
                    String deployed = JvmBackend.classNameFor("host/" + stem) + ".java";
                    Files.copy(file, workspace.resolve(deployed));
                    corpusHostSources.add(deployed);
                }
            }

            // The probe: the load entry's bindings, its idempotence, and the
            // wrapper cells.
            Files.writeString(workspace.resolve("HostModuleLoadProbe.java"),
                jvmProbe(probeKey, cfgKey), StandardCharsets.UTF_8);

            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            List<String> sources = new ArrayList<>();
            sources.add(source.toAbsolutePath().toString());
            sources.add("HostAbi_probe.java");
            sources.addAll(corpusHostSources);
            sources.add("HostModuleLoadProbe.java");
            List<String> command = new ArrayList<>(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString()));
            command.addAll(sources);
            ProcessOutcome javacRun = runProcess(command, workspace, false);
            check(javacRun.exitCode() == 0,
                "the artifact compiles with the deployed host fixtures: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }

            ProcessOutcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes,
                "HostModuleLoadProbe"), workspace, false);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the emitted host wrappers run the declared cells under java: exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(fixture.root());
        }
    }

    /** The deployed JVM host implementation of the ABI declaration. */
    private static final String HOST_ABI_JAVA = """
        import java.util.concurrent.CompletableFuture;

        final class HostAbi_probe {
          public static Object ping() { return "pong"; }
          public static Object echoInt(int v) { return Integer.valueOf(v); }
          public static Object badReturn() { return "junk"; }
          public static Object join(String sep, $DealRt.__StringArray parts) {
            return String.join(sep, parts.data);
          }
          public static Object apply($DealRt.Fn1_I_R_I f, int v) {
            return Integer.valueOf(f.invoke(v) + 100);
          }
          public static Object fetchValue() {
            return CompletableFuture.completedFuture("fetched");
          }
          public static Object echoBytes($DealRt.Bytes b) { return b; }
          public static Object nullable(String v) { return v; }
        }
        """;

    /** The JVM probe: the load entry's bindings, its idempotence, the cells. */
    private static String jvmProbe(String probeKey, String cfgKey) {
        return PROBE_JAVA.replace("$PROBE$", probeKey).replace("$CFG$", cfgKey);
    }

    private static final String PROBE_JAVA = """
            final class HostModuleLoadProbe {
              private static int passed = 0;

              private static void check(boolean condition, String message) {
                if (!condition) { throw new IllegalStateException("FAIL: " + message); }
                passed++;
              }

              private static void expect(String code, String message,
                  Runnable action) {
                try {
                  action.run();
                  throw new IllegalStateException("FAIL: no error for " + message);
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  check(code.equals(error.code),
                      "code " + error.code + " for " + message);
                  check(message.equals(error.msg),
                      "message '" + error.msg + "' for " + message);
                }
              }

              public static void main(String[] args) {
                App.dealMain();
                check(App.__hostLoaded$$PROBE$, "the load entry ran in the walk");
                check(App.__hostM$$PROBE$$ping != null, "the ping binding exists");
                check(App.__hostM$$PROBE$$echoInt != null, "the echoInt binding exists");
                check(App.__hostM$$PROBE$$join != null, "the join binding exists");
                check(App.__hostM$$PROBE$$apply != null, "the apply binding exists");
                check(App.__hostM$$PROBE$$fetchValue != null, "the async binding exists");
                check(App.__hostM$$PROBE$$echoBytes != null, "the bytes binding exists");
                check(App.__hostD$$CFG$$ServerConfig != null,
                    "the defaults capture exists");
                java.lang.reflect.Method before = App.__hostM$$PROBE$$ping;
                App.__hostLoad$$PROBE$("probe.deal", 6, 1);
                check(App.__hostM$$PROBE$$ping == before,
                    "the second load entry call binds nothing new");

                // The declared parameter and return cells.
                // The call arms project the production carrier onto the
                // declared host carrier at the boundary cell (a later slice);
                // this drive passes the declared carrier directly.
                Object echo = App.__host$$PROBE$$echoInt(Integer.valueOf(7),
                    "probe.deal", 3, 1);
                check(Integer.valueOf(7).equals(echo), "the int roundtrip: " + echo);
                Object joined = App.__host$$PROBE$$join("-",
                    new $DealRt.__StringArray(new String[] {"a", "b"}),
                    "probe.deal", 4, 1);
                check("a-b".equals(joined), "the array carrier roundtrip: " + joined);
                Object applied = App.__host$$PROBE$$apply(new $DealRt.Fn1_I_R_I() {
                    int invoke(int p0) { return p0 + 1; }
                  }, Integer.valueOf(7), "probe.deal", 5, 1);
                check(Integer.valueOf(108).equals(applied),
                    "the function carrier reaches the host bridge: " + applied);

                // The pinned E8010 parameter cells.
                expect("E8010", "parameter 1 type mismatch: expected bytes",
                    () -> App.__host$$PROBE$$echoBytes(Double.valueOf(1.0),
                        "probe.deal", 6, 1));
                expect("E8010", "parameter 2 type mismatch: expected array",
                    () -> App.__host$$PROBE$$join("x", Double.valueOf(1.0),
                        "probe.deal", 7, 1));
                expect("E8010", "parameter 1 type mismatch: expected function",
                    () -> App.__host$$PROBE$$apply(Double.valueOf(1.0),
                        Integer.valueOf(1), "probe.deal", 8, 1));

                // The pinned E8010 return cell (the host returns junk for int).
                expect("E8010", "return value 1 type mismatch: expected int",
                    () -> App.__host$$PROBE$$badReturn("probe.deal", 9, 1));

                System.out.println("PROBE-OK " + passed);
              }
            }
            """;

    // =========================================================================
    // 5. The JVM pinned E8011 at the import origin
    // =========================================================================

    private static void testJvmMissingExport() throws Exception {
        System.out.println("-- the JVM load entry raises the pinned E8011 at the "
            + "import origin --");
        Fixture fixture = missingFixture();
        try {
            checkJvmLoadFailure(fixture, "HostMissing_export.java", """
                final class HostMissing_export {
                  public static Object ping() { return "pong"; }
                }
                """, "E8011",
                "missing host export 'missing' in module 'host/missing_export'",
                ":6:1", "missing-export-at-6:1");
        } finally {
            deleteRecursively(fixture.root());
        }

        // The declared-class seed: a host class without its mandatory
        // <C>_defaults field fails the load entry with the pinned E8011.
        Fixture cfgFixture = cfgOnlyFixture();
        try {
            checkJvmLoadFailure(cfgFixture, "HostCfg.java", """
                final class HostCfg {
                  public static final java.util.Map<String, Object> Endpoint_defaults =
                      java.util.Map.of("path", "/");
                  public static Object describe(Object s) { return "cfg"; }
                }
                """, "E8011",
                "host class 'ServerConfig' in module 'host/cfg' is missing its "
                    + "defaults field (ServerConfig_defaults)",
                null, "missing-defaults");
        } finally {
            deleteRecursively(cfgFixture.root());
        }
    }

    /**
     * One JVM load-failure drive: the artifact compiles and runs with the
     * given host implementation, and the module init must fail with the
     * pinned E8011 (and, when pinned, the origin suffix).
     */
    private static void checkJvmLoadFailure(Fixture fixture, String hostFileName,
            String hostSource, String expectedCode, String expectedMessage,
            String originSuffix, String label) throws Exception {
        Path workspace = Files.createTempDirectory("host-load-jvm-seed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            if (result.project() == null) {
                fail("the seed fixture '" + label + "' lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, fixture.surface());
            Path source = workspace.resolve(className + ".java");
            Files.writeString(source, emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve(hostFileName), hostSource,
                StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostLoadFailureProbe.java"),
                jvmFailureProbe(expectedCode, expectedMessage, originSuffix),
                StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            ProcessOutcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                source.toAbsolutePath().toString(), hostFileName,
                "HostLoadFailureProbe.java"), workspace, false);
            check(javacRun.exitCode() == 0,
                "the load-failure artifact ('" + label + "') compiles: "
                    + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            ProcessOutcome run = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes,
                "HostLoadFailureProbe"), workspace, false);
            check(run.exitCode() == 0 && run.stdout().contains("PROBE-OK"),
                "the load seed '" + label + "' raises the pinned E8011: exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
        } finally {
            deleteRecursively(workspace);
        }
    }

    /** The JVM load-failure probe of one pinned E8011. */
    private static String jvmFailureProbe(String expectedCode,
            String expectedMessage, String originSuffix) {
        String originCheck = originSuffix == null ? ""
            : "      if (!error.origin.endsWith(" + quoted(originSuffix)
                + ")) { throw new IllegalStateException(\"FAIL: origin \" + error.origin); }\n";
        return """
            final class HostLoadFailureProbe {
              public static void main(String[] args) {
                try {
                  App.dealMain();
                  throw new IllegalStateException("FAIL: the init succeeded");
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  if (!$CODE$.equals(error.code)) {
                    throw new IllegalStateException("FAIL: code " + error.code);
                  }
                  if (!$MESSAGE$.equals(error.msg)) {
                    throw new IllegalStateException("FAIL: message " + error.msg);
                  }
            $ORIGIN$      System.out.println("PROBE-OK " + error.origin);
                }
              }
            }
            """.replace("$CODE$", quoted(expectedCode))
            .replace("$MESSAGE$", quoted(expectedMessage))
            .replace("$ORIGIN$", originCheck);
    }

    /** One Java string literal of the given text. */
    private static String quoted(String text) {
        StringBuilder literal = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> literal.append("\\\"");
                case '\\' -> literal.append("\\\\");
                default -> literal.append(c);
            }
        }
        return literal.append('"').toString();
    }

    // =========================================================================
    // 6. The signature extension: the production unit passes the surface
    // =========================================================================

    private static void testSignatureExtension() throws Exception {
        System.out.println("-- the production unit passes its received declaration "
            + "surface to both production emitter entries --");
        String unit = Files.readString(
            Path.of("deal", "module", "ProductionProjectEmission.java"),
            StandardCharsets.UTF_8);
        check(unit.contains("JvmSemanticEmitter.emitProductionProject(project,"),
            "the JVM call site is present");
        check(unit.contains("LuaSemanticEmitter.emitProductionProject(project,"),
            "the LuaJIT call site is present");
        checkEq(2, countOccurrences(unit, "declarationSurface);"),
            "both call sites pass the declaration surface through");
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static void deployRuntime(Path workspace) throws Exception {
        Path runtime = Path.of("deal", "runtime.lua");
        Path runtimeTarget = workspace.resolve("deal").resolve("runtime.lua");
        Files.createDirectories(runtimeTarget.getParent());
        Files.copy(runtime, runtimeTarget);
        Path stdTarget = workspace.resolve("std");
        Files.createDirectories(stdTarget);
        try (var listing = Files.list(Path.of("std"))) {
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

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n")
                + " stderr=" + stderr.replace("\n", "\\n");
        }
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir,
            boolean deferMain) throws Exception {
        Path stderrFile = Files.createTempFile(workDir, "stderr", ".txt");
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        if (deferMain) {
            builder.environment().put("DEAL_DEFER_MAIN", "1");
        }
        builder.redirectError(stderrFile.toFile());
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        String stderr = Files.readString(stderrFile, StandardCharsets.UTF_8);
        Files.deleteIfExists(stderrFile);
        return new ProcessOutcome(exit, stdout, stderr);
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

    private static String escaped(String text) {
        return text.replace("\n", "\\n");
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
        System.out.println("=== Host Module Load / JVM Host ABI Surface Tests "
            + "(ISSUE-0650) ===\n");
        testLuaArtifactText();
        testLuaExecution();
        testJvmArtifactText();
        testJvmToolchain();
        testJvmMissingExport();
        testSignatureExtension();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Host Module Load / JVM Host ABI Surface Tests Passed ===");
    }
}
