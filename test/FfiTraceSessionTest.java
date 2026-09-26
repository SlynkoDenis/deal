package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.lua.FfiEmissionInput;
import deal.codegen.lua.LuaFfiBindingGenerator;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.ffi.FfiClassDescriptor;
import deal.ffi.FfiCompilerClassDefaultPlan;
import deal.ffi.FfiGeneratedModule;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.DescriptorService;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SemanticTraceProtocol;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.test.conformance.CorpusFfi;
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
import java.util.function.Supplier;
import java.util.stream.Stream;

/**
 * ISSUE-0668: the trace-mode FFI session and the both-mode runtime
 * binding ({@code luajit-ffi-load-emission-and-typed-crossings} F6;
 * {@code luajit-ffi-shared-emission-and-jvm-rejection} F2;
 * {@code luajit-ffi-struct-plan-construction-and-oracle-projection} F4;
 * sequencing step 7).
 *
 * <ol>
 *   <li><b>The both-mode runtime binding and the host-free prelude.</b> A
 *       session over an extern-C closure binds
 *       {@code local __rt = require("deal.runtime")} and the host-boundary
 *       prelude in both modes and both trace entries (with and without the
 *       compile's declaration surface), independent of the FFI emission
 *       input; a host-free chunk keeps its self-contained prelude.</li>
 *   <li><b>The three-input trace entry over the crossings (ffi/020).</b>
 *       The landed trace entry keeps its signature and emits the extern-C
 *       {@code MODULE_IMPORT} op's events with a no-op load (no
 *       {@code load_ffi}, no {@code load_host}); the drive pre-publishes
 *       the scenario surface, runs the chunk under {@code luajit}, and
 *       compares the stream with the oracle event-for-event, asserting
 *       that the pre-published surface survived the chunk's {@code or}
 *       guards.</li>
 *   <li><b>The four-input trace entry over the crossings and the
 *       construction (ffi/019).</b> The drive pre-publishes one function
 *       wrapper per declared function and the real generated
 *       {@code Pair_plan} entry, runs the crossings and the construction,
 *       and matches the oracle event-for-event with one heap value per
 *       class-typed crossing.</li>
 *   <li><b>The construction runs the real generated evaluators.</b> A
 *       focused declaration whose struct fields carry observable defaults
 *       constructs with omitted fields in the trace session; the
 *       pre-published plan's evaluator closures run against the scenario
 *       bindings, and the counter sequence matches the production
 *       artifact's real native evaluators and the oracle's projection
 *       suppliers.</li>
 *   <li><b>The absence negative.</b> An absent surface or entry stays the
 *       fail-visible {@code missing} projection on the value-position
 *       read, and the invocation fails visibly — never a silent value;
 *       the same drive with the entry published succeeds.</li>
 *   <li><b>Literal determinism.</b> The generated literals and both mode
 *       emissions are byte-identical across runs.</li>
 * </ol>
 */
public class FfiTraceSessionTest {

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

    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String CORPUS_FFI_DIR =
        "test/conformance/backend-runtime/ffi";
    private static final String NATIVE = "candidate/native";
    private static final String NATIVE_DOTTED = "candidate.native";
    private static final String PAIR_DESC = "@$external/candidate/native/Pair";
    private static final String HANDLE_DESC = "@$external/candidate/native/Handle";
    private static final String POINTER_CASE = "020-ffi-pointer-token";
    private static final String STRUCT_CASE = "019-ffi-struct-copy-isolation";

    private static final String FOCUSED_SPECIFIER = "ffi/valid";
    private static final String FOCUSED_DOTTED = "ffi.valid";

    /** The runtime binding the chunk carries whenever it has a HOST import. */
    private static final String RUNTIME_BINDING =
        "local __rt = require(\"deal.runtime\")";

    /** One marker of the host-boundary prelude (the FFI construction helper). */
    private static final String PRELUDE_MARK = "local function __ffiClassPlan(";

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private record Fixture(
        Path root,
        Path sourceRoot,
        String specifier,
        String dotted,
        String appFileName,
        String app,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    /**
     * Compiles one synthetic app against the corpus extern-C declaration of
     * {@code candidate/native} (the corpus generated module is the
     * production FFI metadata, exactly like the sibling FFI drives).
     */
    private static Fixture compileCorpus(String caseName, String appOverride)
            throws Exception {
        String rawFixture = Files.readString(Path.of(CORPUS_FFI_DIR + "/"
            + caseName + ".deal"), StandardCharsets.UTF_8);
        CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT, NATIVE);
        if (wiring == null) {
            throw new IllegalStateException("the corpus wiring carries no entry '"
                + NATIVE + "'");
        }
        String declaration = Files.readString(CONFORMANCE_ROOT
            .resolve(CorpusFfi.FFI_DIR).resolve(wiring.declarationCorpusPath()),
            StandardCharsets.UTF_8);
        CorpusFfi.Module module = CorpusFfi.module(CONFORMANCE_ROOT, NATIVE,
            SemanticProfile.DEAL_V1_2_INT32);
        if (module.validationDiagnostics().stream()
                .anyMatch(d -> "error".equals(d.severity()))
                || module.generatedModule() == null) {
            throw new IllegalStateException(
                "the corpus declaration of '" + NATIVE + "' does not validate: "
                    + module.validationDiagnostics());
        }
        String app = appOverride != null ? appOverride
            : ConformanceHarnessMetadata.stripClassificationHeaders(rawFixture);
        return compile(NATIVE, declaration, caseName + ".deal", app,
            module.generatedModule());
    }

    /**
     * Compiles one fixture: {@code declaration} is the extern-C declaration
     * source of {@code specifier} (or {@code null} for a declaration-free
     * import such as a stdlib module) and {@code appSource} the
     * application.
     */
    private static Fixture compile(String specifier, String declaration,
            String appName, String appSource, FfiGeneratedModule generated)
            throws Exception {
        Path root = Files.createTempDirectory("ffi-trace-session");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve(appName),
            ConformanceHarnessMetadata.stripClassificationHeaders(appSource),
            StandardCharsets.UTF_8);
        Map<String, String> externals = new LinkedHashMap<>();
        if (declaration != null) {
            Files.writeString(src.resolve("native.d.deal"),
                ConformanceHarnessMetadata.stripClassificationHeaders(declaration),
                StandardCharsets.UTF_8);
            externals.put(specifier,
                src.resolve("native.d.deal").toAbsolutePath().toString());
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(appName).toAbsolutePath(), root.resolve("out"),
            false, false, false, false, Backend.LUAJIT, externals,
            List.of(src.toAbsolutePath()), null, null, productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null
                || built.index() == null || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the FFI trace fixture '" + appName
                + "' did not build: " + detail + " / "
                + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        if (generated != null) {
            externCModules.put(new ModuleId(specifier.replace('/', '.')), generated);
        } else {
            for (Map.Entry<String, FfiGeneratedModule> entry
                    : orchestrator.ffiGenerations().entrySet()) {
                externCModules.put(new ModuleId(entry.getKey()), entry.getValue());
            }
        }
        String dotted = specifier.replace('/', '.');
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(specifier));
        }
        return new Fixture(root, src, specifier, dotted, appName, appSource,
            built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
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

    /** The registered declaration-class layouts of the lowering's seeds. */
    private static Map<ClassId, ClassLayout> declarationLayouts(
            SemanticLowerer.ProjectLoweringResult result) {
        Map<ClassId, ClassLayout> layouts = new LinkedHashMap<>();
        for (Map.Entry<ClassId, deal.semantic.ClassRegistrationSeeds.ClassRegistration>
                entry : result.seeds().registrations().entrySet()) {
            layouts.put(entry.getKey(), entry.getValue().layout());
        }
        return layouts;
    }

    // =========================================================================
    // The trace entries of the one session family
    // =========================================================================

    /** The trace entry with the compile's declaration surface (four inputs). */
    private static String traceWithSurface(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult lowered) {
        return LuaSemanticEmitter.emitProject(lowered.project(),
            lowered.tables(), lowered.registries(), fixture.surface());
    }

    /** The landed three-input trace entry (no declaration surface). */
    private static String traceWithoutSurface(
            SemanticLowerer.ProjectLoweringResult lowered) {
        return LuaSemanticEmitter.emitProject(lowered.project(),
            lowered.tables(), lowered.registries());
    }

    /**
     * The FFI-capable production session of the same closure (the FFI
     * emission input selects the realized load).
     */
    private static String production(Fixture fixture,
            SemanticLowerer.ProjectLoweringResult lowered) {
        return LuaSemanticEmitter.emitProductionProject(lowered.project(),
            lowered.tables(), lowered.registries(), fixture.surface(),
            new FfiEmissionInput(fixture.externCModules(),
                fixture.sourceRoot().toString()));
    }

    // =========================================================================
    // The scenario-published surface
    // =========================================================================

    /**
     * The scenario-published surface of one trace-mode FFI session
     * (load-emission F6): one {@code { __kind = "function", sig = ...,
     * f = ... }} wrapper per declared function of the declaration module
     * (the declaration surface's own export list) and one
     * {@code <name>_plan} entry per {@code C_STRUCT} class, taken from the
     * generated plan literal — so the construction runs the real generated
     * plan closures and their evaluators.
     *
     * @param fixture      the compiled fixture (the declaration facts name
     *                     the declared functions)
     * @param module       the compile's generated extern-C module (the plan
     *                     literal's authority)
     * @param terminals    the scripted terminal bodies by export name (a
     *                     Lua statement list, e.g. {@code return 31});
     *                     every declared function gets a wrapper and an
     *                     unscripted one fails visibly
     * @param excluded     the declared exports served no wrapper (the
     *                     absent-entry negative)
     * @param bindingsLocal the generated module's bindings local name (the
     *                     plan literal's same-module forward-cell handle);
     *                     {@code null} for the default
     * @param bindingsTable the extra prelude defining that bindings table,
     *                     or {@code null}
     * @return the Lua prelude publishing the surface; non-null
     */
    private static String seamPrelude(Fixture fixture, FfiGeneratedModule module,
            Map<String, String> terminals, Set<String> excluded,
            String bindingsLocal, String bindingsTable) {
        String bindings = bindingsLocal == null ? "__seam_bindings" : bindingsLocal;
        LuaFfiBindingGenerator.Generation generation =
            LuaFfiBindingGenerator.generate(module, "", bindings,
                "__seam_import_");
        if (generation.failure() != null) {
            throw new IllegalStateException("the generated plan literal does not"
                + " serialize: " + generation.failure().message());
        }
        HostDeclarationSurface.DeclarationFacts facts =
            fixture.surface().require(new ModuleId(fixture.dotted()));
        StringBuilder sb = new StringBuilder();
        sb.append("local __seamPlans = ")
            .append(generation.parts().plansLiteral()).append("\n");
        sb.append("local __seamRt = require(\"deal.runtime\")\n");
        sb.append("__seamCalls = {}\n");
        sb.append("local function __seamCalled(name)\n");
        sb.append("  __seamCalls[name] = (__seamCalls[name] or 0) + 1\n");
        sb.append("end\n");
        if (bindingsTable != null) {
            sb.append(bindings).append(" = ").append(bindingsTable).append("\n");
        }
        sb.append("__exportSurfaces = {\n");
        sb.append("  [").append(luaString(fixture.dotted())).append("] = {\n");
        List<String> entries = new ArrayList<>();
        for (Map.Entry<String, Type> export : facts.exports().entrySet()) {
            if (!(export.getValue() instanceof Type.Func)
                    || excluded.contains(export.getKey())) {
                continue;
            }
            String body = terminals.get(export.getKey());
            entries.add("    [" + luaString(export.getKey())
                + "] = {__kind = \"function\", sig = "
                + luaString(descriptorText(export.getValue()))
                + ", f = function(...) __seamCalled("
                + luaString(export.getKey()) + ") "
                + (body != null ? body
                    : "error(\"the trace drive scripts no terminal for "
                        + export.getKey() + "\", 0)")
                + " end}");
        }
        for (FfiClassDescriptor declared : module.descriptor().classes()) {
            if (declared.kind() == FfiClassDescriptor.ClassKind.C_STRUCT) {
                entries.add("    [" + luaString(declared.name() + "_plan")
                    + "] = __seamPlans["
                    + luaString(planIdentity(module, declared)) + "].plan");
            }
        }
        sb.append(String.join(",\n", entries)).append("\n");
        sb.append("  },\n");
        sb.append("}\n");
        return sb.toString();
    }

    /** The plan-map key of one declared C_STRUCT class. */
    private static String planIdentity(FfiGeneratedModule module,
            FfiClassDescriptor declared) {
        for (String key : module.plans().keySet()) {
            if (key.equals(declared.canonicalClassIdentity())) {
                return key;
            }
        }
        throw new IllegalStateException("the generated plan map carries no entry"
            + " for the class identity " + declared.canonicalClassIdentity()
            + ": " + module.plans().keySet());
    }

    /**
     * The trace drive: pre-publishes the scenario surface, loads the chunk
     * with the deferred entry walk, runs the walk, and publishes the
     * terminal and the seam-usage report.
     */
    private static String traceProbe(String artifactName, String moduleKey,
            String seamPrelude) {
        return "package.path = \"./?.lua;./std/?.lua;\" .. package.path\n"
            + seamPrelude
            + "local __seamBefore = __exportSurfaces\n"
            + "local __seamOk, __seamErr = pcall(dofile, "
            + luaString(artifactName) + ")\n"
            + "if not __seamOk then\n"
            + "  local __text = type(__callbacks) == \"table\""
            + " and __callbacks.__errtext(__seamErr) or tostring(__seamErr)\n"
            + "  io.stderr:write(\"R|failure|\" .. __text .. \"\\n\")\n"
            + "  print(\"PROBE-LOAD-FAIL|\" .. tostring(__seamErr))\n"
            + "  os.exit(1)\n"
            + "end\n"
            + "local ok, err = __dealMain()\n"
            + "if ok then\n"
            + "  io.stderr:write(\"R|success|null\\n\")\n"
            + "else\n"
            + "  io.stderr:write(\"R|failure|\" .. __callbacks.__errtext(err)"
            + " .. \"\\n\")\n"
            + "end\n"
            + "io.stderr:flush()\n"
            + "local __survived = (__exportSurfaces == __seamBefore)\n"
            + "  and (type(__exportSurfaces[" + luaString(moduleKey)
            + "]) == \"table\")\n"
            + "print(\"SEAM-SURVIVED|\" .. tostring(__survived))\n"
            + "local __names = {}\n"
            + "for __name, __count in pairs(__seamCalls) do\n"
            + "  __names[#__names + 1] = __name .. \"=\" .. __count\n"
            + "end\n"
            + "table.sort(__names)\n"
            + "print(\"SEAM-CALLS|\" .. table.concat(__names, \",\"))\n"
            + "if not ok then os.exit(1) end\n";
    }

    /** Whether the pre-published surface survived one drive's or-guards. */
    private static boolean seamSurvived(String stdout) {
        for (String line : stdout.split("\n")) {
            if (line.startsWith("SEAM-SURVIVED|")) {
                return line.endsWith("true");
            }
        }
        throw new IllegalStateException("the probe published no seam report: "
            + escaped(stdout));
    }

    /** The seam-usage counts of one probe report, by export name. */
    private static Map<String, Integer> seamCalls(String stdout) {
        for (String line : stdout.split("\n")) {
            if (line.startsWith("SEAM-CALLS|")) {
                Map<String, Integer> counts = new LinkedHashMap<>();
                String rest = line.substring("SEAM-CALLS|".length());
                if (rest.isEmpty()) {
                    return counts;
                }
                for (String part : rest.split(",")) {
                    int at = part.indexOf('=');
                    counts.put(part.substring(0, at),
                        Integer.parseInt(part.substring(at + 1)));
                }
                return counts;
            }
        }
        throw new IllegalStateException("the probe published no seam usage: "
            + escaped(stdout));
    }

    /** Deploys the runtime and the probe, then runs the chunk under luajit. */
    private static ProcessOutcome runTrace(Path workspace, String chunk,
            String moduleKey, String seamPrefix) throws Exception {
        Files.createDirectories(workspace.resolve("deal"));
        Files.copy(Path.of("deal", "runtime.lua"),
            workspace.resolve("deal/runtime.lua"));
        Files.writeString(workspace.resolve("trace.lua"), chunk,
            StandardCharsets.UTF_8);
        Files.writeString(workspace.resolve("trace-probe.lua"),
            traceProbe("trace.lua", moduleKey, seamPrefix),
            StandardCharsets.UTF_8);
        return runProcess(List.of("luajit", "trace-probe.lua"), workspace,
            Map.of("DEAL_DEFER_MAIN", "1"));
    }

    // =========================================================================
    // The oracle seam
    // =========================================================================

    /** One scripted host terminal of a seam responder. */
    @FunctionalInterface
    private interface Terminal {
        SemanticOracle.HostResponder.SyncOutcome f(List<SemanticOracle.Value> args);
    }

    /**
     * The oracle's closed seam for one drive: the plan projection built from
     * the compile's generated plan (the real entries; the deferred defaults
     * are the supplied proxies), and the scripted call terminals — the
     * oracle-side twin of the scenario-published surface.
     */
    private static final class SeamResponder implements SemanticOracle.HostResponder {

        final String dotted;
        final FfiGeneratedModule module;
        final Map<String, Terminal> terminals = new LinkedHashMap<>();
        final Map<String, Supplier<SemanticOracle.Value>> defaults =
            new LinkedHashMap<>();
        final List<String> projectionRequests = new ArrayList<>();
        final List<String> evaluatorInvocations = new ArrayList<>();
        final List<String> calls = new ArrayList<>();
        final Map<String, SemanticOracle.Value> loaded = new LinkedHashMap<>();
        /** Whether the seamed load published the surface (the negative drives). */
        boolean surfacePublished = true;

        SeamResponder(String dotted, FfiGeneratedModule module) {
            this.dotted = dotted;
            this.module = module;
        }

        @Override
        public SemanticOracle.Value loadedExport(ModuleId requested, String export,
                RuntimeDescriptor descriptor) {
            if (!surfacePublished || !requested.path().equals(dotted)) {
                return null;
            }
            if (descriptor instanceof RuntimeDescriptor.Func signature) {
                return loaded.computeIfAbsent(export,
                    key -> new SemanticOracle.Value.HostEntryValue(signature));
            }
            return null;
        }

        @Override
        public List<PlanEntry> planProjection(ModuleId requested, String className,
                RuntimeDescriptor.Class declaredClass) {
            projectionRequests.add(requested.path() + "." + className + " "
                + declaredClass.classId().text());
            String identity = declaredClass.classId().text();
            FfiCompilerClassDefaultPlan plan = module.plans().get(identity);
            if (plan == null) {
                throw new IllegalStateException("the seam scripts no plan for "
                    + identity + ": " + module.plans().keySet());
            }
            List<PlanEntry> entries = new ArrayList<>();
            for (FfiCompilerClassDefaultPlan.Entry entry : plan.entries()) {
                Supplier<SemanticOracle.Value> supplier = () -> {
                    evaluatorInvocations.add(entry.name());
                    Supplier<SemanticOracle.Value> scripted =
                        defaults.get(entry.name());
                    if (scripted == null) {
                        throw new IllegalStateException("the drive scripts no"
                            + " deferred default for field '" + entry.name() + "'");
                    }
                    return scripted.get();
                };
                entries.add(new PlanEntry(entry.name(),
                    descriptorOf(entry.canonicalDescriptor()), entry.optional(),
                    entry.hasDefaultEvaluator() ? supplier : null));
            }
            return entries;
        }

        @Override
        public SyncOutcome call(ModuleId requested, String export,
                RuntimeDescriptor.Func descriptor, List<SemanticOracle.Value> args) {
            calls.add(export);
            Terminal terminal = terminals.get(export);
            if (terminal == null) {
                throw new IllegalStateException("the drive scripts no terminal for "
                    + requested.path() + "." + export);
            }
            return terminal.f(args);
        }
    }

    /** The closed descriptor of one canonical descriptor text. */
    private static RuntimeDescriptor descriptorOf(String text) {
        return switch (text) {
            case "int" -> RuntimeDescriptor.Int.INSTANCE;
            case "number" -> RuntimeDescriptor.Number.INSTANCE;
            case "boolean" -> RuntimeDescriptor.Boolean.INSTANCE;
            case "string" -> RuntimeDescriptor.String.INSTANCE;
            default -> throw new IllegalStateException("the drive scripts no"
                + " descriptor projection for '" + text + "'");
        };
    }

    // =========================================================================
    // 1. The both-mode runtime binding and the host-free prelude
    // =========================================================================

    private static void testBothModeRuntimeBinding() throws Exception {
        System.out.println("-- the runtime binding and the host-boundary prelude"
            + " in both modes whenever the closure carries a HOST-kind import;"
            + " a host-free chunk keeps its self-contained prelude --");
        Fixture fixture = compileCorpus(POINTER_CASE, null);
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            Map<String, String> chunks = new LinkedHashMap<>();
            chunks.put("the trace entry with the declaration surface",
                traceWithSurface(fixture, lowered));
            chunks.put("the three-input trace entry",
                traceWithoutSurface(lowered));
            chunks.put("the FFI-capable production entry",
                production(fixture, lowered));
            String noInputProduction = LuaSemanticEmitter.emitProductionProject(
                lowered.project(), lowered.tables(), lowered.registries(),
                fixture.surface());
            chunks.put("the production entry without the FFI emission input",
                noInputProduction);
            for (Map.Entry<String, String> entry : chunks.entrySet()) {
                check(entry.getValue().contains(RUNTIME_BINDING),
                    entry.getKey() + " binds the runtime");
                check(entry.getValue().contains(PRELUDE_MARK),
                    entry.getKey() + " carries the host-boundary prelude");
                checkEq(1, countOccurrences(entry.getValue(), RUNTIME_BINDING),
                    entry.getKey() + " binds the runtime exactly once");
            }
            check(!chunks.get("the trace entry with the declaration surface")
                    .contains("__rt.load_ffi(")
                    && !chunks.get("the trace entry with the declaration surface")
                        .contains("__rt.load_host("),
                "the four-input trace entry emits no FFI load");
            check(!chunks.get("the three-input trace entry")
                    .contains("__rt.load_ffi(")
                    && !chunks.get("the three-input trace entry")
                        .contains("__rt.load_host("),
                "the three-input trace entry emits no FFI load");
            check(!noInputProduction.contains("__rt.load_ffi(")
                    && !noInputProduction.contains("__rt.load_host("),
                "a production session without the FFI emission input emits the"
                    + " extern-C import's no-op load");
            check(chunks.get("the FFI-capable production entry")
                    .contains("__rt.load_ffi("),
                "the production entry emits the FFI load");

            // The host-free chunk: no runtime binding and no host prelude in
            // either mode (its prelude is self-contained).
            Fixture hostFree = compileHostFree();
            try {
                SemanticLowerer.ProjectLoweringResult freeLowered =
                    lower(hostFree);
                if (freeLowered.project() == null) {
                    fail("the host-free fixture lowers: "
                        + freeLowered.diagnostics());
                    return;
                }
                String freeTrace = traceWithoutSurface(freeLowered);
                String freeProduction = LuaSemanticEmitter.emitProductionProject(
                    freeLowered.project(), freeLowered.tables(),
                    freeLowered.registries(), hostFree.surface());
                check(!freeTrace.contains(RUNTIME_BINDING)
                        && !freeTrace.contains(PRELUDE_MARK),
                    "a host-free trace chunk keeps its self-contained prelude");
                check(!freeProduction.contains(RUNTIME_BINDING)
                        && !freeProduction.contains(PRELUDE_MARK),
                    "a host-free production chunk keeps its self-contained"
                        + " prelude");
            } finally {
                deleteRecursively(hostFree.root());
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    /** One host-free project (no host and no extern-C declaration import). */
    private static Fixture compileHostFree() throws Exception {
        String app = """
            import * as str from "std/string";

            export function main(): null {
              let value: string = str.trim("  abc  ");
              if (value !== "abc") {
                throw { code: "TEST_FAIL", message: "the host-free stdlib call" };
              }
              return null;
            }
            """;
        return compile("std/string", null, "host-free.deal", app, null);
    }

    // =========================================================================
    // 2. The three-input trace entry over the crossings (ffi/020)
    // =========================================================================

    private static void testTraceEntryWithoutSurface() throws Exception {
        System.out.println("-- the three-input trace entry over the pointer"
            + " crossings: no FFI load, the import op's events, the"
            + " pre-published surface surviving the or-guards, and"
            + " event-for-event oracle parity --");
        Fixture fixture = compileCorpus(POINTER_CASE, null);
        Path workspace = Files.createTempDirectory("ffi-trace-pointer");
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the pointer fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            String chunk = traceWithoutSurface(lowered);
            check(!chunk.contains("__rt.load_ffi(")
                    && !chunk.contains("__rt.load_host("),
                "the extern-C MODULE_IMPORT emits a no-op load in the"
                    + " three-input trace entry");
            check(chunk.contains(RUNTIME_BINDING) && chunk.contains(PRELUDE_MARK),
                "the three-input trace entry binds the runtime for its FFI arms");
            check(chunk.contains("__exportSurfaces = __exportSurfaces or {}"),
                "the chunk-global registry keeps a pre-published surface"
                    + " through its or-guard");

            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(NATIVE_DOTTED));
            Map<String, String> terminals = new LinkedHashMap<>();
            terminals.put("ffi_handle_new", "return {__kind = \"class\","
                + " __classname = " + luaString(HANDLE_DESC)
                + ", __ptr = __seamToken()}");
            terminals.put("ffi_handle_value", "return 31");
            terminals.put("ffi_handle_free", "return __seamRt.__NULL");
            String seam = "local __seamTokenV = {}\n"
                + "local function __seamToken() return __seamTokenV end\n"
                + seamPrelude(fixture, module, terminals, Set.of(), null, null);
            ProcessOutcome run = runTrace(workspace, chunk, NATIVE_DOTTED, seam);
            check(run.exitCode() == 0,
                "the three-input trace drive exits 0: exit=" + run.exitCode()
                    + " stdout=" + escaped(run.stdout()) + " stderr="
                    + escaped(run.stderr()));
            check(seamSurvived(run.stdout()),
                "the pre-published surface survives the chunk's or-guards");
            checkEq(1, seamCalls(run.stdout()).get("ffi_handle_new"),
                "the drive's own wrapper served the load-path call");
            checkEq(1, seamCalls(run.stdout()).get("ffi_handle_value"),
                "the drive's own wrapper served the value crossing");
            TraceRun artifact = decodeTrace(run.stderr());
            check(hasEvent(artifact, SemanticOpKind.MODULE_IMPORT, "START")
                    && hasEvent(artifact, SemanticOpKind.MODULE_IMPORT, "SUCCESS"),
                "the extern-C MODULE_IMPORT emits its op events with the no-op"
                    + " load");

            SeamResponder responder = new SeamResponder(NATIVE_DOTTED, module);
            responder.terminals.put("ffi_handle_new", args ->
                new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    new SemanticOracle.Value.ClassValue(
                        new ClassId("$external/" + NATIVE, "Handle"), List.of())));
            responder.terminals.put("ffi_handle_value", args ->
                new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    new SemanticOracle.Value.IntValue(31)));
            responder.terminals.put("ffi_handle_free", args ->
                new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    SemanticOracle.Value.NullValue.INSTANCE));
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), responder, declarationLayouts(lowered));
            TraceRun oracle = oracleRun(oracleRun);
            checkTraceParity("ffi/020", "luajit", oracle, artifact);
            checkEq(terminalText(oracle.terminal()),
                terminalText(artifact.terminal()),
                "ffi/020 (luajit) terminal parity");
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle's ffi/020 drive succeeds: " + oracle.terminal());
            checkEq(List.of("ffi_handle_new", "ffi_handle_value",
                    "ffi_handle_free"), responder.calls,
                "the oracle's seam served the pointer fixture's three calls");
        } finally {
            deleteRecursively(fixture.root());
            deleteRecursively(workspace);
        }
    }

    // =========================================================================
    // 3. The four-input trace entry over the crossings and the construction
    // =========================================================================

    private static void testTraceSessionCrossingsAndConstruction()
            throws Exception {
        System.out.println("-- the trace-mode FFI session over ffi/019: the"
            + " crossings and the construction over the scenario-published"
            + " surface, event-for-event with the oracle, one heap value per"
            + " class-typed crossing --");
        Fixture fixture = compileCorpus(STRUCT_CASE, null);
        Path workspace = Files.createTempDirectory("ffi-trace-struct");
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            String chunk = traceWithSurface(fixture, lowered);
            check(!chunk.contains("__rt.load_ffi(")
                    && !chunk.contains("__rt.load_host("),
                "the four-input trace entry emits no FFI load");
            check(chunk.contains(RUNTIME_BINDING) && chunk.contains(PRELUDE_MARK),
                "the four-input trace entry binds the runtime and the prelude");
            check(chunk.contains("pcall(__rt.class_plan_, " + luaString(PAIR_DESC)
                    + ", __ffiClassPlan(" + luaString(NATIVE_DOTTED)
                    + ", \"Pair\"), __provT,"),
                "the construction runs over the loaded Pair_plan entry");

            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(NATIVE_DOTTED));
            Map<String, String> terminals = new LinkedHashMap<>();
            terminals.put("ffi_pair_swap", "local v = ... return {__kind ="
                + " \"class\", __classname = " + luaString(PAIR_DESC)
                + ", left = v.left + 1000, right = v.right + 2000}");
            String seam = seamPrelude(fixture, module, terminals, Set.of(),
                null, null);
            checkEq(declaredFunctionCount(fixture),
                countOccurrences(seam, "__kind = \"function\""),
                "the seam pre-publishes exactly one function wrapper per declared"
                    + " function");
            checkEq(1, countOccurrences(seam, "[\"Pair_plan\"] = __seamPlans["
                    + luaString(PAIR_DESC) + "].plan"),
                "the seam pre-publishes the Pair_plan entry from the generated"
                    + " plan literal");
            ProcessOutcome run = runTrace(workspace, chunk, NATIVE_DOTTED, seam);
            check(run.exitCode() == 0,
                "the trace-mode FFI session exits 0: exit=" + run.exitCode()
                    + " stdout=" + escaped(run.stdout()) + " stderr="
                    + escaped(run.stderr()));
            check(seamSurvived(run.stdout()),
                "the pre-published surface survives the chunk's or-guards");
            checkEq(1, seamCalls(run.stdout()).get("ffi_pair_swap"),
                "the seam's wrapper served the by-value crossing");
            check(seamCalls(run.stdout()).getOrDefault("ffi_pair_sum", 0) == 0,
                "no unscripted declaration export was invoked");
            TraceRun artifact = decodeTrace(run.stderr());

            SeamResponder responder = new SeamResponder(NATIVE_DOTTED, module);
            List<SemanticOracle.Value> swapped = new ArrayList<>();
            responder.terminals.put("ffi_pair_swap", args -> {
                swapped.add(args.get(0));
                SemanticOracle.Value.ClassValue pair =
                    (SemanticOracle.Value.ClassValue) args.get(0);
                return new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    new SemanticOracle.Value.ClassValue(
                        new ClassId("$external/" + NATIVE, "Pair"),
                        List.of(
                            new SemanticOracle.Value.ClassFieldState.Present(
                                new SemanticOracle.Value.IntValue(
                                    intField(pair, 0) + 1000)),
                            new SemanticOracle.Value.ClassFieldState.Present(
                                new SemanticOracle.Value.IntValue(
                                    intField(pair, 1) + 2000)))));
            });
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), responder, declarationLayouts(lowered));
            TraceRun oracle = oracleRun(oracleRun);
            checkTraceParity("ffi/019", "luajit", oracle, artifact);
            checkEq(terminalText(oracle.terminal()),
                terminalText(artifact.terminal()),
                "ffi/019 (luajit) terminal parity");
            check(oracle.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the oracle's ffi/019 drive succeeds: " + oracle.terminal());
            checkEq(List.of(NATIVE_DOTTED + ".Pair " + PAIR_DESC),
                responder.projectionRequests,
                "the oracle requests the plan projection once with the resolved"
                    + " declaring module, the class name, and the descriptor");
            check(responder.evaluatorInvocations.isEmpty(),
                "both fields are provided: the deferred plan suppliers never run");
            checkEq(1, swapped.size(),
                "the oracle's by-value crossing receives exactly one instance");
            if (!swapped.isEmpty()
                    && swapped.get(0) instanceof SemanticOracle.Value.ClassValue pair) {
                checkEq(4L, intField(pair, 0),
                    "the constructed instance's left field is the provided value");
                checkEq(9L, intField(pair, 1),
                    "the constructed instance's right field is the provided value");
            }

            // The trace-identity rule: the construction's one instance is the
            // value the parameter cell observes, and the returned instance is
            // one projected heap value end to end.
            Map<String, SemanticOp> hostCalls = hostCalls(project);
            SemanticOp swap = hostCalls.get("ffi_pair_swap");
            if (swap == null) {
                fail("the fixture lowers its by-value call");
                return;
            }
            OpId parameterBoundary =
                ((KindPayload.CallPayload) swap.payload())
                    .parameterBoundaryOpIds().get(0);
            OpId returnBoundary =
                ((KindPayload.CallPayload) swap.payload()).returnBoundaryOpId();
            String constructed = firstAtom(artifact, "CLASS_NEW", "SUCCESS", false);
            String parameterInput = eventAtom(artifact, parameterBoundary,
                "BOUNDARY", "START", true);
            String returned = firstAtom(artifact, "CALL", "SUCCESS", false);
            String returnInput = eventAtom(artifact, returnBoundary,
                "BOUNDARY", "START", true);
            String returnSuccess = eventAtom(artifact, returnBoundary,
                "BOUNDARY", "SUCCESS", false);
            check(constructed != null && constructed.startsWith("ref:"),
                "the construction publishes one heap instance: " + constructed);
            checkEq(constructed, parameterInput,
                "the constructed instance is the parameter cell's own value"
                    + " (one heap value per class-typed crossing)");
            check(returned != null && returned.startsWith("ref:"),
                "the projected return is one heap value: " + returned);
            check(!returned.equals(parameterInput),
                "the returned instance is a distinct by-value copy: " + returned);
            checkEq(returned, returnInput,
                "the return boundary's START observes the projected value that"
                    + " the call publishes (one heap value per class-typed"
                    + " crossing)");
            checkEq(returned, returnSuccess,
                "the return boundary's SUCCESS returns that one heap value"
                    + " unchanged");
        } finally {
            deleteRecursively(fixture.root());
            deleteRecursively(workspace);
        }
    }

    /** Whether one artifact trace carries the op's event of the given phase. */
    private static boolean hasEvent(TraceRun run, SemanticOpKind kind,
            String phase) {
        for (TraceEvent event : run.events()) {
            if (kind.name().equals(event.kind()) && phase.equals(event.phase())) {
                return true;
            }
        }
        return false;
    }

    /** The number of declared function exports of one fixture. */
    private static int declaredFunctionCount(Fixture fixture) {
        int count = 0;
        for (Type type : fixture.surface()
                .require(new ModuleId(fixture.dotted())).exports().values()) {
            if (type instanceof Type.Func) {
                count++;
            }
        }
        return count;
    }

    /**
     * The first atom of one artifact event of the given kind/phase: the
     * output when {@code output}, else the first {@code ref:} input.
     */
    private static String firstAtom(TraceRun run, String kind, String phase,
            boolean input) {
        for (TraceEvent event : run.events()) {
            if (!kind.equals(event.kind()) || !phase.equals(event.phase())) {
                continue;
            }
            if (!input) {
                return event.output();
            }
            for (String value : event.inputs()) {
                if (value != null && value.startsWith("ref:")) {
                    return value;
                }
            }
        }
        return null;
    }

    /**
     * The first {@code ref:} input or the output of the event of one exact
     * op and phase (the pinned boundary child of a call site).
     */
    private static String eventAtom(TraceRun run, OpId op, String kind,
            String phase, boolean input) {
        for (TraceEvent event : run.events()) {
            if (!op.equals(event.op()) || !kind.equals(event.kind())
                    || !phase.equals(event.phase())) {
                continue;
            }
            if (!input) {
                return event.output();
            }
            for (String value : event.inputs()) {
                if (value != null && value.startsWith("ref:")) {
                    return value;
                }
            }
        }
        return null;
    }

    private static long intField(SemanticOracle.Value.ClassValue instance, int index) {
        SemanticOracle.Value value = switch (instance.fields().get(index)) {
            case SemanticOracle.Value.ClassFieldState.Present present ->
                present.value();
            case SemanticOracle.Value.ClassFieldState.Missing ignored ->
                throw new IllegalStateException("field " + index + " is absent");
        };
        return ((SemanticOracle.Value.IntValue) value).value();
    }

    // =========================================================================
    // 4. The construction runs the real generated evaluators
    // =========================================================================

    private static final String COUNTING_DECLARATION = """
        // @extern-c

        // @c-struct
        export class Probe {
          a: int = fixture_count_call_int();
          b: int = fixture_count_call_int();
        }

        export function fixture_count_call_int(): int;
        export function fixture_call_count(): int;
        export function fixture_reset_counter(): null;
        """;

    private static final String COUNTING_APP = """
        import * as native from "ffi/valid"

        export function main(): null {
          if (native.fixture_call_count() !== 0) {
            throw { code: "TEST_FAIL", message: "a default evaluated at load" };
          }
          let first: native.Probe = {};
          if (first.a !== 1 || first.b !== 2) {
            throw { code: "TEST_FAIL", message: "the omitted fields' evaluators did not run once each in class source order" };
          }
          if (native.fixture_call_count() !== 2) {
            throw { code: "TEST_FAIL", message: "the per-attempt evaluator count" };
          }
          let second: native.Probe = { a: 99 };
          if (second.a !== 99 || second.b !== 3) {
            throw { code: "TEST_FAIL", message: "a provided field did not suppress its own evaluator" };
          }
          if (native.fixture_call_count() !== 3) {
            throw { code: "TEST_FAIL", message: "the provided-field suppression count" };
          }
          let third: native.Probe = {};
          if (third.a !== 4 || third.b !== 5) {
            throw { code: "TEST_FAIL", message: "the re-executed evaluators did not continue the counter" };
          }
          if (native.fixture_call_count() !== 5) {
            throw { code: "TEST_FAIL", message: "the final evaluator count" };
          }
          return null;
        }
        """;

    private static void testConstructionRunsGeneratedEvaluators()
            throws Exception {
        System.out.println("-- the trace-mode construction runs the real"
            + " generated plan evaluators over the scenario-published"
            + " surface (zero at load, once per omitted field per attempt in"
            + " class source order) --");
        Path workspace = Files.createTempDirectory("ffi-trace-counting");
        Fixture fixture;
        try {
            fixture = compile(FOCUSED_SPECIFIER, COUNTING_DECLARATION,
                "struct-counting.deal", COUNTING_APP, null);
        } catch (IllegalStateException failure) {
            fail(failure.getMessage());
            deleteRecursively(workspace);
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the counting fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            String chunk = traceWithSurface(fixture, lowered);
            check(!chunk.contains("__rt.load_ffi("),
                "the counting trace session emits no FFI load");
            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(FOCUSED_DOTTED));
            Map<String, String> terminals = new LinkedHashMap<>();
            terminals.put("fixture_count_call_int", "return __seamCounter()");
            terminals.put("fixture_call_count", "return __seamCounterValue");
            terminals.put("fixture_reset_counter",
                "__seamCounterReset() return __seamRt.__NULL");
            String seam = "local __seamCounterValue = 0\n"
                + "local function __seamCounter()\n"
                + "  __seamCounterValue = __seamCounterValue + 1\n"
                + "  return __seamCounterValue\n"
                + "end\n"
                + "local function __seamCounterReset() __seamCounterValue = 0 end\n"
                + seamPrelude(fixture, module, terminals, Set.of(),
                    "__seam_bindings", countingBindings());
            check(seam.contains("evaluator = function() return "),
                "the pre-published plan literal carries the generated deferred"
                    + " evaluators (the only default authority)");
            ProcessOutcome run = runTrace(workspace, chunk, FOCUSED_DOTTED, seam);
            check(run.exitCode() == 0,
                "the counting trace session exits 0 through its own assertions"
                    + " (zero at load, one per omitted field per attempt in class"
                    + " source order, provided-field suppression): exit="
                    + run.exitCode() + " stdout=" + escaped(run.stdout())
                    + " stderr=" + escaped(run.stderr()));
            TraceRun artifact = decodeTrace(run.stderr());
            check(artifact.terminal() instanceof SemanticRuntimeModel.Terminal.Success,
                "the counting trace session publishes a success terminal: "
                    + artifact.terminal());
            checkEq(5, seamCalls(run.stdout()).get("eval"),
                "every omitted field's evaluator reached the same-module wrapper"
                    + " exactly once (five invocations over the three attempts)");

            // The oracle: the projection suppliers are the deferred evaluators,
            // and the call terminals share the same counter.
            SeamResponder responder = new SeamResponder(FOCUSED_DOTTED, module);
            int[] counter = {0};
            responder.defaults.put("a", () ->
                new SemanticOracle.Value.IntValue(++counter[0]));
            responder.defaults.put("b", () ->
                new SemanticOracle.Value.IntValue(++counter[0]));
            responder.terminals.put("fixture_call_count", args ->
                new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    new SemanticOracle.Value.IntValue(counter[0])));
            responder.terminals.put("fixture_reset_counter", args -> {
                counter[0] = 0;
                return new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    SemanticOracle.Value.NullValue.INSTANCE);
            });
            responder.terminals.put("fixture_count_call_int", args ->
                new SemanticOracle.HostResponder.SyncOutcome.Returned(
                    new SemanticOracle.Value.IntValue(++counter[0])));
            SemanticRuntimeModel.ConsumerRun oracleRun =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), responder, declarationLayouts(lowered));
            TraceRun oracle = oracleRun(oracleRun);
            checkTraceParity("ffi/valid Probe", "luajit", oracle, artifact);
            checkEq(terminalText(oracle.terminal()),
                terminalText(artifact.terminal()),
                "the counting drive (luajit) terminal parity");
            checkEq(List.of("a", "b", "b", "a", "b"),
                responder.evaluatorInvocations,
                "the oracle's deferred suppliers run once per omitted field per"
                    + " attempt in class source order (provided fields"
                    + " suppressed)");
            checkEq(5, counter[0],
                "the oracle's counter sequence matches the artifact's real"
                    + " generated evaluators");
        } finally {
            deleteRecursively(fixture.root());
            deleteRecursively(workspace);
        }
    }

    /** The scenario bindings table the generated plan's evaluators close over. */
    private static String countingBindings() {
        return "{ state = \"BOUND\", cells = { fixture_count_call_int ="
            + " { state = \"BOUND\", wrapper = { f = function(...)"
            + " __seamCalled(\"eval\") return __seamCounter() end } } } }";
    }

    // =========================================================================
    // 5. The absence negative
    // =========================================================================

    private static final String VALUE_READ_SOURCE = """
        import * as native from "candidate/native";

        export function main(): null {
          let identity: (value: int) => int = native.ffi_identity_int;
          if (identity(7) !== 7) {
            throw { code: "TEST_FAIL", message: "the value-position read did not round-trip" };
          }
          return null;
        }
        """;

    private static void testAbsentSurfaceStaysFailVisible() throws Exception {
        System.out.println("-- the mode/absence negative: an absent surface or"
            + " entry stays the fail-visible missing projection, and the"
            + " invocation fails visibly (the published entry succeeds) --");
        Fixture fixture = compileCorpus(STRUCT_CASE, VALUE_READ_SOURCE);
        Path absentWorkspace = Files.createTempDirectory("ffi-trace-absent");
        Path entryWorkspace = Files.createTempDirectory("ffi-trace-entry");
        Path presentWorkspace = Files.createTempDirectory("ffi-trace-present");
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the value-read fixture lowers: " + lowered.diagnostics());
                return;
            }
            ExecutableLoweredProject project = lowered.project();
            String chunk = traceWithSurface(fixture, lowered);
            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(NATIVE_DOTTED));
            String bareSeam = "local __seamRt = require(\"deal.runtime\")\n"
                + "__seamCalls = {}\n"
                + "local function __seamCalled(name)\n"
                + "  __seamCalls[name] = (__seamCalls[name] or 0) + 1\n"
                + "end\n";

            // (a) The fully absent surface: the read publishes the missing
            // projection and the invocation fails visibly.
            ProcessOutcome absentRun = runTrace(absentWorkspace, chunk,
                NATIVE_DOTTED, bareSeam);
            check(absentRun.exitCode() != 0,
                "the absent-surface drive fails visibly: exit="
                    + absentRun.exitCode());
            TraceRun absentTrace = decodeTrace(absentRun.stderr());
            check(absentTrace.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure,
                "the absent surface's value-position read fails visibly: "
                    + absentTrace.terminal());
            checkEq(List.of("missing"), readAtoms(absentTrace),
                "the absent surface's EXPORT_READ publishes the missing"
                    + " projection (never a silent value)");

            // (b) The surface published without the entry: the same
            // fail-visible missing projection.
            String entrySeam = seamPrelude(fixture, module, Map.of(),
                Set.of("ffi_identity_int"), null, null);
            ProcessOutcome entryRun = runTrace(entryWorkspace, chunk,
                NATIVE_DOTTED, entrySeam);
            check(entryRun.exitCode() != 0,
                "the absent-entry drive fails visibly: exit="
                    + entryRun.exitCode());
            TraceRun entryTrace = decodeTrace(entryRun.stderr());
            checkEq(List.of("missing"), readAtoms(entryTrace),
                "the absent entry's EXPORT_READ publishes the missing"
                    + " projection (never a silent value)");

            // (c) The same drive with the entry published succeeds end to end.
            Map<String, String> terminals = new LinkedHashMap<>();
            terminals.put("ffi_identity_int", "local v = ... return v");
            String presentSeam = seamPrelude(fixture, module, terminals,
                Set.of(), null, null);
            ProcessOutcome presentRun = runTrace(presentWorkspace, chunk,
                NATIVE_DOTTED, presentSeam);
            check(presentRun.exitCode() == 0,
                "the published-entry drive succeeds: exit="
                    + presentRun.exitCode() + " stdout="
                    + escaped(presentRun.stdout()) + " stderr="
                    + escaped(presentRun.stderr()));
            TraceRun presentTrace = decodeTrace(presentRun.stderr());
            check(presentTrace.terminal()
                    instanceof SemanticRuntimeModel.Terminal.Success,
                "the published entry drives the read to success: "
                    + presentTrace.terminal());
            checkEq(1, seamCalls(presentRun.stdout()).get("ffi_identity_int"),
                "the read and the invocation resolve the one published entry");

            // (d) The oracle's landed absent-slot projection: the read of the
            // same closure publishes Value.MissingValue (the artifact's
            // fail-visible projection's oracle twin).
            SeamResponder responder = new SeamResponder(NATIVE_DOTTED, module);
            responder.surfacePublished = false;
            SemanticRuntimeModel.ConsumerRun absentOracle =
                SemanticOracle.executeProjectInits(project, lowered.tables(),
                    lowered.registries(), responder, declarationLayouts(lowered));
            List<String> oracleReadAtoms = new ArrayList<>();
            for (SemanticRuntimeModel.TraceEvent event : absentOracle.trace()) {
                if (event.kind() == SemanticOpKind.EXPORT_READ
                        && event.phase() == SemanticRuntimeModel.Phase.SUCCESS
                        && event.output() != null) {
                    oracleReadAtoms.add(event.output());
                }
            }
            checkEq(List.of("missing"), oracleReadAtoms,
                "the oracle's absent surface publishes the same missing"
                    + " projection");
        } finally {
            deleteRecursively(fixture.root());
            deleteRecursively(absentWorkspace);
            deleteRecursively(entryWorkspace);
            deleteRecursively(presentWorkspace);
        }
    }

    /** The success atoms of the closure's EXPORT_READ events. */
    private static List<String> readAtoms(TraceRun run) {
        List<String> atoms = new ArrayList<>();
        for (TraceEvent event : run.events()) {
            if ("EXPORT_READ".equals(event.kind())
                    && "SUCCESS".equals(event.phase())
                    && event.output() != null) {
                atoms.add(event.output());
            }
        }
        return atoms;
    }

    // =========================================================================
    // 6. Literal determinism
    // =========================================================================

    private static void testLiteralDeterminism() throws Exception {
        System.out.println("-- the generated literals and both mode emissions"
            + " are byte-deterministic --");
        Fixture fixture = compileCorpus(STRUCT_CASE, null);
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(fixture);
            if (lowered.project() == null) {
                fail("the corpus fixture lowers: " + lowered.diagnostics());
                return;
            }
            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(NATIVE_DOTTED));
            LuaFfiBindingGenerator.Generation first =
                LuaFfiBindingGenerator.generate(module, "",
                    "__seam_bindings", "__seam_import_");
            LuaFfiBindingGenerator.Generation second =
                LuaFfiBindingGenerator.generate(module, "",
                    "__seam_bindings", "__seam_import_");
            check(first.failure() == null && second.failure() == null,
                "the generated literals serialize");
            if (first.parts() != null && second.parts() != null) {
                checkEq(first.parts().moduleKeyLiteral(),
                    second.parts().moduleKeyLiteral(),
                    "the module key literal is byte-deterministic");
                checkEq(first.parts().bundleLiteral(),
                    second.parts().bundleLiteral(),
                    "the cdef bundle literal is byte-deterministic");
                checkEq(first.parts().plansLiteral(),
                    second.parts().plansLiteral(),
                    "the plans literal is byte-deterministic");
                checkEq(first.parts().bindingsLiteral(),
                    second.parts().bindingsLiteral(),
                    "the bindings literal is byte-deterministic");
            }
            checkEq(traceWithSurface(fixture, lowered),
                traceWithSurface(fixture, lowered),
                "the four-input trace emission is byte-deterministic");
            checkEq(production(fixture, lowered), production(fixture, lowered),
                "the production emission is byte-deterministic");
        } finally {
            deleteRecursively(fixture.root());
        }

        // The three-input trace entry of a construction-free closure (the
        // FFI_PLAN construction resolves through the declaration surface, so
        // the landed three-input entry stays a call-only session).
        Fixture pointer = compileCorpus(POINTER_CASE, null);
        try {
            SemanticLowerer.ProjectLoweringResult lowered = lower(pointer);
            if (lowered.project() == null) {
                fail("the pointer fixture lowers: " + lowered.diagnostics());
                return;
            }
            checkEq(traceWithoutSurface(lowered), traceWithoutSurface(lowered),
                "the three-input trace emission is byte-deterministic");
        } finally {
            deleteRecursively(pointer.root());
        }
    }

    // =========================================================================
    // The lowered facts of one drive
    // =========================================================================

    /** The extern-C host calls of one closure by export name. */
    private static Map<String, SemanticOp> hostCalls(
            ExecutableLoweredProject project) {
        Map<String, SemanticOp> calls = new LinkedHashMap<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.CALL
                        && op.payload() instanceof KindPayload.CallPayload call
                        && call.callee()
                            instanceof KindPayload.CallCallee.Static staticCallee
                        && staticCallee.binding()
                            instanceof FunctionExecutionBinding.HostFunction host) {
                    calls.put(host.exportName(), op);
                }
            }
        }
        return calls;
    }

    // =========================================================================
    // Trace decoding
    // =========================================================================

    /** One parsed trace protocol line (the event's comparison fields). */
    private record TraceEvent(OpId op, String kind, String phase,
                              List<String> inputs, String output, String text) {
    }

    /** One decoded trace protocol run: the ordered events and the terminal. */
    private record TraceRun(List<TraceEvent> events,
                            SemanticRuntimeModel.Terminal terminal) {
    }

    private static TraceRun decodeTrace(String stderr) {
        List<TraceEvent> events = new ArrayList<>();
        SemanticRuntimeModel.Terminal terminal = null;
        for (String line : stderr.split("\n", -1)) {
            if (line.isEmpty()) {
                continue;
            }
            Object decoded;
            try {
                decoded = SemanticTraceProtocol.decode(line);
            } catch (RuntimeException exception) {
                throw new IllegalStateException("the trace protocol does not decode '"
                    + line + "': " + exception.getMessage());
            }
            if (decoded instanceof SemanticRuntimeModel.TraceEvent event) {
                events.add(new TraceEvent(event.op(), event.kind().name(),
                    event.phase().name(), event.inputs(), event.output(),
                    event.text()));
            } else if (decoded instanceof SemanticRuntimeModel.Terminal term) {
                if (terminal != null) {
                    throw new IllegalStateException("two terminal records: " + line);
                }
                terminal = term;
            }
        }
        if (terminal == null) {
            throw new IllegalStateException(
                "the artifact published no terminal record");
        }
        return new TraceRun(List.copyOf(events), terminal);
    }

    /** The oracle's run in the same decoded shape as the artifact's. */
    private static TraceRun oracleRun(SemanticRuntimeModel.ConsumerRun run) {
        List<TraceEvent> events = new ArrayList<>();
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            events.add(new TraceEvent(event.op(), event.kind().name(),
                event.phase().name(), event.inputs(), event.output(),
                event.text()));
        }
        return new TraceRun(List.copyOf(events), run.terminal());
    }

    /** The canonical text of one terminal (the pinned snapshot fields). */
    private static String terminalText(SemanticRuntimeModel.Terminal terminal) {
        return switch (terminal) {
            case SemanticRuntimeModel.Terminal.Success success ->
                "success:" + success.resultAtom();
            case SemanticRuntimeModel.Terminal.DealFailure failure -> {
                SemanticRuntimeModel.ErrorSnapshot error = failure.error();
                yield "failure:" + error.code() + "|" + error.message() + "|"
                    + error.origin() + "|" + error.expected() + "|" + error.actual();
            }
        };
    }

    /** Asserts one artifact trace equals the oracle's event-for-event. */
    private static void checkTraceParity(String name, String target,
            TraceRun oracle, TraceRun artifact) {
        List<String> expected = new ArrayList<>();
        List<String> actual = new ArrayList<>();
        for (TraceEvent event : oracle.events()) {
            expected.add(event.text());
        }
        for (TraceEvent event : artifact.events()) {
            actual.add(event.text());
        }
        if (!expected.equals(actual)) {
            failed++;
            int limit = Math.min(expected.size(), actual.size());
            for (int i = 0; i < limit; i++) {
                if (!expected.get(i).equals(actual.get(i))) {
                    System.err.println("FAIL: " + name + " (" + target
                        + ") trace event " + i + " oracle [" + expected.get(i)
                        + "] vs artifact [" + actual.get(i) + "]");
                    return;
                }
            }
            System.err.println("FAIL: " + name + " (" + target + ") trace length "
                + expected.size() + " (oracle) vs " + actual.size()
                + " (artifact)");
            return;
        }
        passed++;
    }

    // =========================================================================
    // Process and filesystem helpers
    // =========================================================================

    private record ProcessOutcome(int exitCode, String stdout, String stderr) {
    }

    private static ProcessOutcome runProcess(List<String> command, Path workDir,
            Map<String, String> environment) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(workDir.toFile());
        builder.environment().putAll(environment);
        builder.redirectErrorStream(false);
        Process process = builder.start();
        String stdout = new String(process.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        String stderr = new String(process.getErrorStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = process.waitFor();
        return new ProcessOutcome(exit, stdout, stderr);
    }

    private static String escaped(String text) {
        return text == null ? "null" : text.replace("\n", "\\n");
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        for (int at = text.indexOf(needle); at >= 0;
                at = text.indexOf(needle, at + needle.length())) {
            count++;
        }
        return count;
    }

    /** The declared canonical descriptor text of one declared export type. */
    private static String descriptorText(Type type) {
        return DescriptorService.describe(type).canonicalSpecText();
    }

    /** One Lua string literal (the emitter's own escaping is not public). */
    private static String luaString(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            switch (c) {
                case '"' -> sb.append("\\\"");
                case '\\' -> sb.append("\\\\");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                default -> sb.append(c);
            }
        }
        return sb.append("\"").toString();
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception e) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    // =========================================================================
    // Gate
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI Trace Session Tests (ISSUE-0668) ===");
        System.out.println();
        testBothModeRuntimeBinding();
        testTraceEntryWithoutSurface();
        testTraceSessionCrossingsAndConstruction();
        testConstructionRunsGeneratedEvaluators();
        testAbsentSurfaceStaysFailVisible();
        testLiteralDeterminism();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Trace Session Tests Passed ===");
    }
}
