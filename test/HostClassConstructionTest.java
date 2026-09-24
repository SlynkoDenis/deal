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
import deal.semantic.HostDeclarationSurface;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * ISSUE-0624: host-declared class construction over the loaded
 * {@code <C>_defaults} (design source
 * {@code semantic-ir-construct-coverage-cutover} K10, the K10 contract,
 * and K9 item 3; {@code luajit-jvm-single-lowering-production-cutover} C1;
 * {@code host-module-abi} D2 and the host-load contract).
 *
 * <ol>
 *   <li><b>The lowering shape.</b> A checker-valid host-declared class
 *       literal lowers one {@code CLASS_NEW} with the resolved class
 *       identity, {@code defaultOwner: HOST_DEFAULTS},
 *       {@code classFactoryRef} null, empty {@code classDefaultOpIds}, and
 *       exactly one {@code CLASS_LITERAL_FIELD} boundary per provided field
 *       in declaration order — with zero {@code RETAINED_ABI_DEFERRED} over
 *       the host-class fixtures. No {@code RETAINED_ABI} owner is ever
 *       produced.</li>
 *   <li><b>The construction phases.</b> Provided values evaluate in
 *       literal order by the caller; the loaded {@code <C>_defaults} table
 *       is deep-copied per attempt (the sentinel identities preserved); the
 *       provided overlay rejects an extra provided name with E8007
 *       {@code extra field '<field>' in class '<identity>'} at the literal
 *       origin before any field validation; the {@code __MISSING} entries
 *       are removed from the copy; the instance is tagged with the
 *       canonical class identity — the same phases on LuaJIT under real
 *       {@code luajit}, on the JVM under {@code javac --release 25
 *       -proc:none} + {@code java} together with the deployed corpus host
 *       implementation, and in the oracle through its host-seam defaults
 *       projection.</li>
 *   <li><b>Field operations and {@code has}.</b> Reads (required, optional,
 *       present null, nested class, array), writes (with an alias observing
 *       the commit), deletes (an optional field), and {@code has} all run
 *       through the registered declaration layout on both targets and in
 *       the oracle.</li>
 *   <li><b>The load boundary.</b> A call-free negative seed raises the
 *       pinned E8011 at the import origin on both targets: a missing
 *       declared export, a missing class meta, and a missing or non-table
 *       {@code <C>_defaults}.</li>
 * </ol>
 */
public class HostClassConstructionTest {

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
    // The corpus fixtures of this slice
    // =========================================================================

    /** One admitted host-class fixture: the corpus directory, name, and host stem. */
    private record CorpusFixture(String directory, String name, String hostStem,
                                 String hostSpecifier) {

        String corpusFixture() {
            return "test/conformance/backend-runtime/" + directory + "/" + name + ".deal";
        }

        String corpusSidecar() {
            return "test/conformance/backend-runtime/" + directory + "/" + name
                + ".expect.json";
        }

        String corpusDeclaration() {
            return "test/conformance/host-fixtures/" + hostStem + ".d.deal";
        }

        /** The corpus host implementation's class as the JVM lane deploys it. */
        Path corpusHostJava() {
            return Path.of("test/conformance/host-fixtures/" + hostStem + ".java");
        }

        Path corpusHostLua() {
            return Path.of("test/conformance/host-fixtures/" + hostStem + ".lua");
        }
    }

    private static final CorpusFixture HOST_CLASS_EXPORT =
        new CorpusFixture("host-abi", "host-class-export", "cfg", "host/cfg");
    private static final CorpusFixture HOST_CLASS_DEFAULT_ISOLATION =
        new CorpusFixture("host-abi", "host-class-default-isolation", "cfg", "host/cfg");
    private static final CorpusFixture HOST_CLASS_EXTRA_FIELD =
        new CorpusFixture("host-abi", "host-class-extra-field", "presence",
            "host/presence");
    private static final CorpusFixture HOST_EXPORT_PRESENCE =
        new CorpusFixture("host-abi", "host-export-presence", "presence",
            "host/presence");
    private static final CorpusFixture PLAN_HOST_DISCRIMINATOR =
        new CorpusFixture("defaults", "plan-host-discriminator", "cfg", "host/cfg");

    private static final List<CorpusFixture> RUNTIME_OK_FIXTURES = List.of(
        HOST_CLASS_EXPORT,
        HOST_CLASS_DEFAULT_ISOLATION,
        HOST_EXPORT_PRESENCE,
        PLAN_HOST_DISCRIMINATOR);

    private static final List<CorpusFixture> ALL_FIXTURES = List.of(
        HOST_CLASS_EXPORT,
        HOST_CLASS_DEFAULT_ISOLATION,
        HOST_EXPORT_PRESENCE,
        PLAN_HOST_DISCRIMINATOR,
        HOST_CLASS_EXTRA_FIELD);

    // =========================================================================
    // The compile harness
    // =========================================================================

    private record Fixture(
            Path root,
            String entryPath,
            CheckedProjectInput checkedProject,
            ProjectInterfaceIndex index,
            List<SemanticRequirementManifest> manifests,
            HostDeclarationSurface surface,
            Map<ModuleId, FfiGeneratedModule> externCModules,
            Map<ModuleId, CanonicalModuleIdentity> declarationIdentities,
            Map<String, String> externals,
            int headerLinesStripped) {
    }

    private record Outcome(int exitCode, String stdout, String stderr) {

        String output() {
            return "stdout=" + stdout.replace("\n", "\\n")
                + " stderr=" + stderr.replace("\n", "\\n");
        }
    }

    private static CompilerInvocation harnessInvocation() {
        return CompilerProfileProvider.resolveCommonShadow(
            deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32,
            deal.semantic.ir.ReleaseState.V1_2_ACTIVE,
            deal.semantic.CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            deal.semantic.ReleaseConfiguration.CURRENT_RELEASE_STATE,
            deal.semantic.ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** One corpus fixture compile: the corpus declaration plus the corpus app. */
    private static Fixture compile(CorpusFixture fixture) throws Exception {
        return compileWith(fixture.name(), fixture.hostStem(), fixture.hostSpecifier(),
            ConformanceHarnessMetadata.stripClassificationHeaders(Files.readString(
                Path.of(fixture.corpusDeclaration()), StandardCharsets.UTF_8)),
            Files.readString(Path.of(fixture.corpusFixture()), StandardCharsets.UTF_8));
    }

    /** One synthetic fixture: a host stem, the declaration text, and the app source. */
    private static Fixture compileSource(String name, String hostStem, String hostSpecifier,
            String declarationSource, String appSource) throws Exception {
        return compileWith(name, hostStem, hostSpecifier, declarationSource, appSource);
    }

    private static Fixture compileWith(String name, String hostStem, String hostSpecifier,
            String declarationSource, String rawApp) throws Exception {
        String appSource = ConformanceHarnessMetadata.stripClassificationHeaders(rawApp);
        int headerLinesStripped = rawApp.split("\n", -1).length
            - appSource.split("\n", -1).length;
        Path root = Files.createTempDirectory("host-class-fixture");
        Path src = root.resolve("src");
        Path declarationPath = src.resolve(hostStem + ".d.deal").toAbsolutePath();
        writeFileIn(root, "src/" + hostStem + ".d.deal",
            ConformanceHarnessMetadata.stripClassificationHeaders(declarationSource));
        writeFileIn(root, "src/" + name + ".deal", appSource);
        // The corpus harness's host classification (the lane's own first-entry
        // rule): the dotted typing/class-identity key precedes the raw import
        // key for the one declaration, so the module's public identity — the
        // class atoms the corpus host implementations carry — is the dotted
        // projection while the import still resolves through the raw specifier.
        Map<String, String> externals = new LinkedHashMap<>();
        externals.put(hostSpecifier.replace('/', '.'),
            declarationPath.toString());
        externals.put(hostSpecifier, declarationPath.toString());
        Path entry = src.resolve(name + ".deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, externals,
            List.of(src.toAbsolutePath()), null, null, harnessInvocation());
        orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            deleteRecursively(root);
            throw new IllegalStateException("the host-class fixture '" + name
                + "' did not build: " + detail + " / " + orchestrator.diagnostics());
        }
        HostDeclarationSurface surface = orchestrator.hostDeclarationSurface();
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()), generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule : surface.moduleIds()) {
            identities.put(declarationModule, new CanonicalModuleIdentity.ExternalModule(
                declarationModule.path().replace('/', '.')));
        }
        String entryPath = null;
        for (ModuleId module : built.input().modules().stream()
                .map(module -> module.moduleId()).toList()) {
            if (module.path().endsWith(name)) {
                entryPath = module.path();
            }
        }
        if (entryPath == null) {
            throw new IllegalStateException("the entry module path is not derived");
        }
        return new Fixture(root, entryPath, built.input(), built.index(),
            manifests.manifests(), surface, externCModules, identities, externals,
            headerLinesStripped);
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
    // 1. The lowering shape and the fail-closed accounting
    // =========================================================================

    private static void testLoweringShape() throws Exception {
        System.out.println("-- the host-class lowering shape: CLASS_NEW over"
            + " HOST_DEFAULTS, zero RETAINED_ABI_DEFERRED, no RETAINED_ABI --");
        for (CorpusFixture fixture : ALL_FIXTURES) {
            Fixture compiled = compile(fixture);
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                check(!result.hasErrors() && result.project() != null,
                    "the fixture '" + fixture.name() + "' lowers through the one"
                        + " project entry with zero diagnostics: "
                        + result.diagnostics());
                for (deal.diagnostics.CompilerDiagnostic diagnostic
                        : result.diagnostics()) {
                    check(!diagnostic.message().contains("RETAINED_ABI_DEFERRED"),
                        "the fixture '" + fixture.name() + "' reports zero"
                            + " RETAINED_ABI_DEFERRED: " + diagnostic.message());
                }
                if (result.project() == null) {
                    continue;
                }
                int classNews = 0;
                for (LoweredModuleUnit unit : result.project().modules().values()) {
                    for (SemanticOp op : unit.ops()) {
                        if (op.kind() != SemanticOpKind.CLASS_NEW) {
                            continue;
                        }
                        KindPayload.ClassNewPayload payload =
                            (KindPayload.ClassNewPayload) op.payload();
                        if (payload.defaultOwner() != DefaultOwner.HOST_DEFAULTS) {
                            check(payload.defaultOwner() != DefaultOwner.RETAINED_ABI,
                                "the fixture '" + fixture.name() + "' never"
                                    + " produces a RETAINED_ABI construction");
                            continue;
                        }
                        classNews++;
                        check(payload.classFactoryRef() == null,
                            "the host construction of " + payload.classId()
                                + " carries the null factory ref");
                        check(payload.classDefaultOpIds().isEmpty(),
                            "the host construction of " + payload.classId()
                                + " carries empty classDefaultOpIds");
                        check(payload.fieldBoundaries().stream().allMatch(entry ->
                                entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD),
                            "every boundary of the host construction of "
                                + payload.classId() + " is a CLASS_LITERAL_FIELD");
                        checkEq(payload.providedFields().stream()
                                .map(KindPayload.ProvidedField::name).toList(),
                            payload.fieldBoundaries().stream()
                                .map(KindPayload.FieldBoundary::field).toList(),
                            "the host construction of " + payload.classId()
                                + " carries exactly one CLASS_LITERAL_FIELD boundary"
                                + " per provided field in literal order");
                        check(payload.layout().fields().stream().allMatch(field ->
                                field.defaultOwner() == DefaultOwner.HOST_DEFAULTS),
                            "the host construction of " + payload.classId()
                                + " carries the registered declaration layout");
                        check(result.seeds().registrationFor(payload.classId()) != null
                                && result.seeds().registrationFor(payload.classId())
                                    .owner() == DefaultOwner.HOST_DEFAULTS,
                            "the host construction's class resolves in the class"
                                + " registration seeds under HOST_DEFAULTS: "
                                + payload.classId());
                    }
                }
                check(classNews > 0, "the fixture '" + fixture.name()
                    + "' produces at least one host construction");
                // The composed per-unit chain re-run with the seeds: every
                // unit of the closure passes the class-construction validator.
                for (LoweredModuleUnit unit : result.project().modules().values()) {
                    java.util.Optional<deal.diagnostics.CompilerDiagnostic> failure =
                        SemanticLowerer.validateProjectUnit(unit,
                            result.tableOf(unit.moduleId()),
                            new deal.semantic.ir.SemanticIrValidator.ComparisonFacts(
                                compiled.index().interfaceIndexDigest(),
                                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32,
                                productionInvocation().capabilityRegistryHash()),
                            deal.semantic.BindingsProductionValidator.PinnedWriteFacts
                                .empty(),
                            result.registryOf(unit.moduleId()),
                            new deal.semantic.ir.JsonDefaultChildTable(Map.of()),
                            compiled.index().modules().get(unit.moduleId()),
                            Map.of(), result.seeds().registrations());
                    check(failure.isEmpty(),
                        "the composed chain accepts the unit " + unit.moduleId()
                            + " of '" + fixture.name() + "': "
                            + failure.map(deal.diagnostics.CompilerDiagnostic::message)
                                .orElse(""));
                }
            } finally {
                deleteRecursively(compiled.root());
            }
        }
    }

    // =========================================================================
    // 2. The LuaJIT artifact under real luajit
    // =========================================================================

    private static void testLuaFixtures() throws Exception {
        System.out.println("-- the host-class fixture set under luajit (production"
            + " emission, pinned outcomes) --");
        for (CorpusFixture fixture : RUNTIME_OK_FIXTURES) {
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("host-class-lua");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + fixture.name() + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                String lua = LuaSemanticEmitter.emitProductionProject(
                    result.project(), result.tables(), result.registries(),
                    compiled.surface());
                Path artifact = workspace.resolve("project.lua");
                Files.writeString(artifact, lua, StandardCharsets.UTF_8);
                // The canonical identity tag of every host construction of the
                // fixture (the same text the E8007 projection and the host
                // crossing's identity check carry).
                for (ClassId classId : hostClassIds(result.project())) {
                    check(lua.contains("__instT.__id = " + luaString(classId.text())),
                        "the LuaJIT artifact tags the host instance of " + classId
                            + " with its canonical identity");
                }
                deployRuntime(workspace);
                deployHostLua(workspace, fixture);
                Path probe = workspace.resolve("probe.lua");
                Files.writeString(probe,
                    luaDriver(artifact, compiled.entryPath()), StandardCharsets.UTF_8);
                Outcome outcome = runProcess(List.of("luajit",
                    probe.toAbsolutePath().toString()), workspace, false);
                check(outcome.exitCode() == 0 && outcome.stdout().equals("OK\n"),
                    "the fixture '" + fixture.name() + "' runs runtime-ok under"
                        + " luajit: " + outcome.output());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
        // The pinned E8007 at the literal origin.
        Fixture compiled = compile(HOST_CLASS_EXTRA_FIELD);
        Path workspace = Files.createTempDirectory("host-class-lua-error");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the E8007 fixture lowers: " + result.diagnostics());
                return;
            }
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                compiled.surface()), StandardCharsets.UTF_8);
            deployRuntime(workspace);
            deployHostLua(workspace, HOST_CLASS_EXTRA_FIELD);
            Path probe = workspace.resolve("probe.lua");
            Files.writeString(probe,
                luaDriver(artifact, compiled.entryPath()), StandardCharsets.UTF_8);
            Outcome outcome = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), workspace, false);
            check(outcome.exitCode() == 0
                    && outcome.stdout().startsWith(
                        "ERR:E8007|extra field 'fallback' in class"
                            + " '@$external/host.presence/Config'|")
                    && outcome.stdout().contains("host-class-extra-field.deal:"
                        + (9 - compiled.headerLinesStripped()) + ":28"),
                "the E8007 fixture fails with the pinned code, message, and literal"
                    + " origin under luajit: " + outcome.output());
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
        // The canonical production framing of a literal evaluated on the entry
        // path (the same literal inside main): the artifact's own terminal.
        Fixture framed = compileSource("host-class-e8007-main", "presence",
            "host/presence", EXTRA_FIELD_DECLARATION, EXTRA_FIELD_MAIN_SOURCE);
        Path framedWorkspace = Files.createTempDirectory("host-class-lua-framed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(framed);
            if (result.project() == null) {
                fail("the framed E8007 fixture lowers: " + result.diagnostics());
                return;
            }
            Path artifact = framedWorkspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                result.project(), result.tables(), result.registries(),
                framed.surface()), StandardCharsets.UTF_8);
            deployRuntime(framedWorkspace);
            deployHostLua(framedWorkspace, "presence", "host/presence");
            Outcome outcome = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), framedWorkspace, false);
            check(outcome.exitCode() == 1
                    && outcome.stdout().startsWith("DEAL_ERROR_CODE: E8007"),
                "the production terminal frames the E8007 failure under luajit: "
                    + outcome.output());
        } finally {
            deleteRecursively(framedWorkspace);
            deleteRecursively(framed.root());
        }
    }

    /** The LuaJIT driver: the init walk, then the fixture's test exports. */
    private static String luaDriver(Path artifact, String entryPath) {
        return """
            local function emitError(e)
              if type(e) == "table" and e.__d then
                print("ERR:" .. e.code .. "|" .. tostring(e.m) .. "|"
                  .. tostring(e.o) .. "|" .. tostring(e.e or "-") .. "|"
                  .. tostring(e.a or "-"))
                return
              end
              if type(e) == "table" and e.code ~= nil then
                print("ERR:" .. e.code .. "|" .. tostring(e.message) .. "|"
                  .. tostring(e.file) .. ":" .. tostring(e.line) .. ":"
                  .. tostring(e.column) .. "|" .. tostring(e.expected or "-") .. "|"
                  .. tostring(e.actual or "-"))
                return
              end
              print("ERR:E9999|" .. tostring(e) .. "|-|-|-")
            end
            local chunk = dofile("%s")
            local ok, err = __dealMain()
            if not ok then emitError(err) os.exit(0) end
            local surface = nil
            if type(chunk) == "table" then surface = chunk end
            if surface == nil then surface = __exportSurfaces["%s"] end
            if surface ~= nil then
              local ordered = {}
              for name, candidate in pairs(surface) do ordered[#ordered + 1] = name end
              table.sort(ordered)
              for _, name in ipairs(ordered) do
                if string.sub(name, 1, 5) == "test_" then
                  local ok2, err2 = pcall(surface[name].f)
                  if not ok2 then emitError(err2) os.exit(0) end
                end
              end
            end
            print("OK")
            """.formatted(artifact.toAbsolutePath().toString(), entryPath);
    }

    // =========================================================================
    // 3. The JVM artifact under javac + java
    // =========================================================================

    private static void testJvmFixtures() throws Exception {
        System.out.println("-- the host-class fixture set under javac + java"
            + " (production emission with the deployed host implementations) --");
        for (CorpusFixture fixture : RUNTIME_OK_FIXTURES) {
            Fixture compiled = compile(fixture);
            Path workspace = Files.createTempDirectory("host-class-jvm");
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + fixture.name() + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                String className = JvmBackend.classNameFor(project.entryModule().path());
                JvmSemanticEmitter.EmissionResult emission =
                    JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                        result.registries(), className, compiled.surface());
                Files.writeString(workspace.resolve(className + ".java"),
                    emission.source(), StandardCharsets.UTF_8);
                for (ClassId classId : hostClassIds(project)) {
                    check(emission.source().contains(
                            "this.$identity = " + javaString(classId.text()) + ";"),
                        "the JVM artifact tags the host record of " + classId
                            + " with its canonical identity");
                }
                // The deployed corpus host implementation: it compiles
                // unchanged against the synthesized host-record scope.
                String hostClassName = JvmBackend.classNameFor(
                    fixture.hostSpecifier());
                Files.writeString(workspace.resolve(hostClassName + ".java"),
                    Files.readString(fixture.corpusHostJava(), StandardCharsets.UTF_8),
                    StandardCharsets.UTF_8);
                Files.writeString(workspace.resolve("HostClassProbe.java"),
                    jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
                Path classes = workspace.resolve("classes");
                Files.createDirectories(classes);
                String classpath = absoluteClasspath();
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java", hostClassName + ".java",
                    "HostClassProbe.java"), workspace, false);
                check(javacRun.exitCode() == 0,
                    "the fixture '" + fixture.name() + "' compiles with the deployed"
                        + " corpus host implementation: " + javacRun.output());
                if (javacRun.exitCode() != 0) {
                    continue;
                }
                Outcome outcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "HostClassProbe"), workspace, false);
                check(outcome.exitCode() == 0 && outcome.stdout().equals("OK\n"),
                    "the fixture '" + fixture.name() + "' runs runtime-ok under java: "
                        + outcome.output());
            } finally {
                deleteRecursively(workspace);
                deleteRecursively(compiled.root());
            }
        }
        // The pinned E8007 at the literal origin.
        Fixture compiled = compile(HOST_CLASS_EXTRA_FIELD);
        Path workspace = Files.createTempDirectory("host-class-jvm-error");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the E8007 fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            String hostClassName = JvmBackend.classNameFor(
                HOST_CLASS_EXTRA_FIELD.hostSpecifier());
            Files.writeString(workspace.resolve(hostClassName + ".java"),
                Files.readString(HOST_CLASS_EXTRA_FIELD.corpusHostJava(),
                    StandardCharsets.UTF_8), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("HostClassProbe.java"),
                jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", hostClassName + ".java", "HostClassProbe.java"),
                workspace, false);
            check(javacRun.exitCode() == 0,
                "the E8007 fixture compiles: " + javacRun.output());
            if (javacRun.exitCode() != 0) {
                return;
            }
            Outcome outcome = runProcess(List.of("java", "-cp",
                classpath + java.io.File.pathSeparator + classes, "HostClassProbe"),
                workspace, false);
            check(outcome.exitCode() == 0
                    && outcome.stdout().startsWith(
                        "ERR:E8007|extra field 'fallback' in class"
                            + " '@$external/host.presence/Config'|")
                    && outcome.stdout().contains("host-class-extra-field.deal:"
                        + (9 - compiled.headerLinesStripped()) + ":28"),
                "the E8007 fixture fails with the pinned code, message, and literal"
                    + " origin under java: " + outcome.output());
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
        // The canonical production framing of the same literal on the entry path.
        Fixture framed = compileSource("host-class-e8007-main", "presence",
            "host/presence", EXTRA_FIELD_DECLARATION, EXTRA_FIELD_MAIN_SOURCE);
        Path framedWorkspace = Files.createTempDirectory("host-class-jvm-framed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(framed);
            if (result.project() == null) {
                fail("the framed E8007 fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, framed.surface());
            Files.writeString(framedWorkspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            String hostClassName = JvmBackend.classNameFor("host/presence");
            Files.writeString(framedWorkspace.resolve(hostClassName + ".java"),
                Files.readString(HOST_CLASS_EXTRA_FIELD.corpusHostJava(),
                    StandardCharsets.UTF_8), StandardCharsets.UTF_8);
            Path classes = framedWorkspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", hostClassName + ".java"), framedWorkspace, false);
            check(javacRun.exitCode() == 0,
                "the framed E8007 artifact compiles: " + javacRun.output());
            if (javacRun.exitCode() == 0) {
                Outcome outcome = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, className),
                    framedWorkspace, false);
                check(outcome.exitCode() == 1
                        && outcome.stdout().startsWith("DEAL_ERROR_CODE: E8007"),
                    "the production terminal frames the E8007 failure under java: "
                        + outcome.output());
            }
        } finally {
            deleteRecursively(framedWorkspace);
            deleteRecursively(framed.root());
        }
    }

    /** The JVM driver: the init walk, then the fixture's test exports. */
    private static String jvmDriver(String className, String entryPath) {
        return """
            final class HostClassProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  report(error);
                  return;
                }
                deal.codegen.jvm.JvmRuntime.Table surface =
                    %s.exportSurface(%s);
                for (java.lang.String name : surface.keys) {
                  if (!name.startsWith("test_")) { continue; }
                  try {
                    ((deal.codegen.jvm.JvmRuntime.FunctionValue) surface.read(
                        name)).fn.invoke(new java.lang.Object[]{ });
                  } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                    report(error);
                    return;
                  }
                }
                System.out.println("OK");
              }

              private static void report(deal.codegen.jvm.JvmRuntime.DealError error) {
                System.out.println("ERR:" + error.code + "|" + error.msg + "|"
                    + error.origin + "|" + (error.expected == null ? "-"
                        : error.expected) + "|" + (error.actual == null ? "-"
                            : error.actual));
              }
            }
            """.formatted(className, className, dealerString(entryPath));
    }

    private static String dealerString(String text) {
        return javaString(text);
    }

    /** The presence declaration of the pinned E8007 fixture. */
    private static final String EXTRA_FIELD_DECLARATION = """
        export class Config {
          port: int;
          fallback?: Config | null;
          peers?: Config[];
        }

        export function ping(): string;
        """;

    /** The same literal on the entry path, so the artifact's terminal frames it. */
    private static final String EXTRA_FIELD_MAIN_SOURCE = """
        import * as presence from "host/presence"

        export function main(): null {
          let c: presence.Config = {
            port: 9000,
            fallback: null,
          };
          return null;
        }
        """;

    // =========================================================================
    // 4. The oracle
    // =========================================================================

    private static void testOracle() throws Exception {
        System.out.println("-- the host-class fixture set through the oracle (the"
            + " host-seam defaults projection, the same construction phases) --");
        for (CorpusFixture fixture : ALL_FIXTURES) {
            // The oracle executes the entry module's init walk, so the
            // fixture's operations move onto the entry path (the same
            // statements, the corpus fixture's own body) — exactly the
            // precedent the sibling slices' trace drives set.
            Fixture compiled = compileWith(fixture.name(), fixture.hostStem(),
                fixture.hostSpecifier(),
                ConformanceHarnessMetadata.stripClassificationHeaders(
                    Files.readString(Path.of(fixture.corpusDeclaration()),
                        StandardCharsets.UTF_8)),
                entryPathSource(Files.readString(Path.of(fixture.corpusFixture()),
                    StandardCharsets.UTF_8)));
            try {
                SemanticLowerer.ProjectLoweringResult result = lower(compiled);
                if (result.project() == null) {
                    fail("the fixture '" + fixture.name() + "' lowers: "
                        + result.diagnostics());
                    continue;
                }
                ExecutableLoweredProject project = result.project();
                ModuleId hostModule = hostImportModule(project);
                boolean expectedFailure = fixture.equals(HOST_CLASS_EXTRA_FIELD);
                SemanticOracle.HostResponder responder =
                    corpusResponder(hostModule, fixture.hostStem(),
                        expectedFailure ? "E8007" : null);
                int pinLine = 9 - compiled.headerLinesStripped();
                deal.semantic.SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(project, result.tables(),
                        result.registries(), responder,
                        declarationLayouts(result));
                if (expectedFailure) {
                    check(run.terminal()
                            instanceof deal.semantic.SemanticRuntimeModel.Terminal
                                .DealFailure failure
                            && "E8007".equals(failure.error().code()),
                        "the E8007 fixture fails in the oracle with the pinned code: "
                            + run.terminal());
                    if (run.terminal() instanceof deal.semantic.SemanticRuntimeModel
                            .Terminal.DealFailure failure2) {
                        checkEq("extra field 'fallback' in class"
                                + " '@$external/host.presence/Config'",
                            failure2.error().message(),
                            "the oracle's E8007 message is the pinned projection");
                        check(failure2.error().origin().endsWith(
                                "host-class-extra-field.deal:" + pinLine + ":28"),
                            "the oracle's E8007 origin is the literal origin: "
                                + failure2.error().origin());
                    }
                } else {
                    check(run.terminal()
                            instanceof deal.semantic.SemanticRuntimeModel.Terminal
                                .Success,
                        "the fixture '" + fixture.name() + "' succeeds in the oracle: "
                            + run.terminal());
                    // The constructed instance and its loaded-default fields
                    // are observable through the trace: the host class
                    // construction publishes a class value and the loaded
                    // defaults projection supplies the omitted optionals'
                    // sentinels (never a value).
                    boolean constructed = false;
                    for (deal.semantic.SemanticRuntimeModel.TraceEvent event
                            : run.trace()) {
                        if (event.kind() == SemanticOpKind.CLASS_NEW
                                && event.phase() == deal.semantic.SemanticRuntimeModel
                                    .Phase.SUCCESS) {
                            constructed = true;
                        }
                    }
                    check(constructed, "the fixture '" + fixture.name()
                        + "' executes a successful host class construction in the"
                        + " oracle");
                }
            } finally {
                deleteRecursively(compiled.root());
            }
        }
    }

    /**
     * The oracle-drive source of one fixture: the {@code test_*} export's
     * body moves onto the entry path (the export prefix dropped and the
     * plain {@code main} invokes it), so the oracle's module-init walk — its
     * only execution surface — runs the fixture's own statements. The
     * source is returned with its classification headers (the caller's
     * header-rebase arithmetic stays raw-file-relative).
     */
    private static String entryPathSource(String rawApp) {
        int at = rawApp.indexOf("export function test_");
        if (at < 0) {
            return rawApp;
        }
        int nameStart = at + "export function ".length();
        String testName = rawApp.substring(nameStart, rawApp.indexOf('(', nameStart));
        String unexported = rawApp.substring(0, at) + "function "
            + rawApp.substring(nameStart);
        String mainBody = "export function main(): null {\n  return null;\n}";
        if (!unexported.contains(mainBody)) {
            throw new IllegalStateException("the fixture carries no plain main: "
                + unexported);
        }
        return unexported.replace(mainBody, "export function main(): null {\n  "
            + testName + "();\n  return null;\n}");
    }

    // =========================================================================
    // 5. Field operations and has
    // =========================================================================

    private static final String FIELD_OPS_DECLARATION = """
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

    private static final String FIELD_OPS_SOURCE = """
        import * as cfg from "host/cfg"

        export function test_host_class_field_ops(): string {
          let s: cfg.ServerConfig = {
            port: 9090,
            endpoint: { path: "/api" },
            tags: ["dev"],
            note: null,
          };
          let alias: cfg.ServerConfig = s;
          if (alias.port !== 9090) {
            throw { code: "TEST_FAIL", message: "read through the alias" };
          }
          if (has(alias.note) !== true) {
            throw { code: "TEST_FAIL", message: "present null has()" };
          }
          if (has(alias.tags) !== true) {
            throw { code: "TEST_FAIL", message: "present array has()" };
          }
          alias.port = 8080;
          if (s.port !== 8080) {
            throw { code: "TEST_FAIL", message: "alias observes the commit" };
          }
          delete alias.tags;
          if (has(alias.tags)) {
            throw { code: "TEST_FAIL", message: "deleted field has()" };
          }
          let endpoint: cfg.Endpoint = s.endpoint;
          if (endpoint.path !== "/api") {
            throw { code: "TEST_FAIL", message: "nested class field read" };
          }
          let described: string = cfg.describe(s);
          if (described !== "/api:8080") {
            throw { code: "TEST_FAIL", message: "host boundary roundtrip" };
          }
          return "host class field ops ok";
        }

        export function main(): null {
          return null;
        }
        """;

    private static void testFieldOpsAndHas() throws Exception {
        System.out.println("-- the host-class field operations and has(): reads,"
            + " writes, deletes, and the alias commit on both targets --");
        Fixture compiled = compileSource("host-class-field-ops", "cfg", "host/cfg",
            FIELD_OPS_DECLARATION, FIELD_OPS_SOURCE);
        Path luaWorkspace = Files.createTempDirectory("host-class-field-lua");
        Path jvmWorkspace = Files.createTempDirectory("host-class-field-jvm");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the field-ops fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = luaWorkspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(luaWorkspace);
            deployHostLua(luaWorkspace, "cfg", "host/cfg");
            Outcome lua = runProcess(List.of("luajit",
                artifact.toAbsolutePath().toString()), luaWorkspace, false);
            check(lua.exitCode() == 0 && lua.stdout().isEmpty()
                    && lua.stderr().isEmpty(),
                "the field-ops fixture runs runtime-ok under luajit: " + lua.output());

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(jvmWorkspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(jvmWorkspace.resolve("HostCfg.java"),
                Files.readString(Path.of("test/conformance/host-fixtures/cfg.java"),
                    StandardCharsets.UTF_8), StandardCharsets.UTF_8);
            Path classes = jvmWorkspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostCfg.java"), jvmWorkspace, false);
            check(javacRun.exitCode() == 0,
                "the field-ops artifact compiles with the deployed host"
                    + " implementation: " + javacRun.output());
            if (javacRun.exitCode() == 0) {
                Outcome jvm = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes, className),
                    jvmWorkspace, false);
                check(jvm.exitCode() == 0 && jvm.stdout().isEmpty()
                        && jvm.stderr().isEmpty(),
                    "the field-ops fixture runs runtime-ok under java: "
                        + jvm.output());
            }
            // The oracle executes the same reads, writes, deletes, and has().
            ModuleId hostModule = hostImportModule(project);
            deal.semantic.SemanticRuntimeModel.ConsumerRun run =
                SemanticOracle.execute(project, result.tables(), result.registries(),
                    corpusResponder(hostModule, "cfg", null),
                    declarationLayouts(result));
            check(run.terminal()
                    instanceof deal.semantic.SemanticRuntimeModel.Terminal.Success,
                "the field-ops fixture succeeds in the oracle: " + run.terminal());
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 5b. The nullable and optional numeric field surface
    // =========================================================================

    private static final String NULLABLE_OPS_DECLARATION = """
        export class Bag {
          count?: int;
          limit: int | null;
        }
        """;

    private static final String NULLABLE_OPS_SOURCE = """
        import * as bag from "host/bag"

        export function test_host_class_nullable_ops(): string {
          let b: bag.Bag = { limit: 5 };
          if (has(b.count) !== false) {
            throw { code: "TEST_FAIL", message: "omitted optional field has()" };
          }
          b.count = 3;
          let count: int | null = b.count;
          if (count === null) {
            throw { code: "TEST_FAIL", message: "written optional int read" };
          }
          if (has(b.count) !== true) {
            throw { code: "TEST_FAIL", message: "written optional field has()" };
          }
          delete b.count;
          if (has(b.count) !== false) {
            throw { code: "TEST_FAIL", message: "deleted optional field has()" };
          }
          let limit: int | null = b.limit;
          if (limit === null) {
            throw { code: "TEST_FAIL", message: "required nullable field read" };
          }
          b.limit = null;
          let cleared: int | null = b.limit;
          if (cleared !== null) {
            throw { code: "TEST_FAIL", message: "required nullable field null write" };
          }
          return "host class nullable ops ok";
        }

        export function main(): null {
          return null;
        }
        """;

    /** The synthetic host implementation's declared defaults (the bag shape). */
    private static final String BAG_LUA = """
        local rt = require("deal.runtime")

        return {
          Bag = {
            __kind = "class",
            __classname = "@$external/host.bag/Bag",
          },
          Bag_defaults = {
            count = rt.__MISSING,
            limit = 0,
          },
        }
        """;

    private static final String BAG_JAVA = """
        final class HostBag {
          public static final java.util.Map<String, Object> Bag_defaults =
              java.util.Map.of("count", new Object(),
                  "limit", java.lang.Integer.valueOf(0));
        }
        """;

    private static void testNullableFieldOps() throws Exception {
        System.out.println("-- the nullable/optional numeric host-class fields:"
            + " present null, absence, and the delete commit on both targets and"
            + " through the oracle --");
        Fixture compiled = compileSource("host-class-nullable-ops", "bag", "host/bag",
            NULLABLE_OPS_DECLARATION, NULLABLE_OPS_SOURCE);
        Path luaWorkspace = Files.createTempDirectory("host-class-nullable-lua");
        Path jvmWorkspace = Files.createTempDirectory("host-class-nullable-jvm");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the nullable-ops fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = luaWorkspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(luaWorkspace);
            writeFileIn(luaWorkspace, "host/bag.lua", BAG_LUA);
            Path probe = luaWorkspace.resolve("probe.lua");
            Files.writeString(probe,
                luaDriver(artifact, compiled.entryPath()), StandardCharsets.UTF_8);
            Outcome lua = runProcess(List.of("luajit",
                probe.toAbsolutePath().toString()), luaWorkspace, false);
            check(lua.exitCode() == 0 && lua.stdout().equals("OK\n"),
                "the nullable-ops fixture runs runtime-ok under luajit: "
                    + lua.output());

            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(jvmWorkspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(jvmWorkspace.resolve("HostBag.java"), BAG_JAVA,
                StandardCharsets.UTF_8);
            Files.writeString(jvmWorkspace.resolve("HostClassProbe.java"),
                jvmDriver(className, compiled.entryPath()), StandardCharsets.UTF_8);
            Path classes = jvmWorkspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                "-proc:none", "-cp", classpath, "-d", classes.toString(),
                className + ".java", "HostBag.java", "HostClassProbe.java"),
                jvmWorkspace, false);
            check(javacRun.exitCode() == 0,
                "the nullable-ops artifact compiles: " + javacRun.output());
            if (javacRun.exitCode() == 0) {
                Outcome jvm = runProcess(List.of("java", "-cp",
                    classpath + java.io.File.pathSeparator + classes,
                    "HostClassProbe"), jvmWorkspace, false);
                check(jvm.exitCode() == 0 && jvm.stdout().equals("OK\n"),
                    "the nullable-ops fixture runs runtime-ok under java: "
                        + jvm.output());
            }
            ModuleId hostModule = hostImportModule(project);
            SemanticOracle.HostResponder responder = new SemanticOracle.HostResponder() {
                @Override
                public Map<String, SemanticOracle.Value> loadedClassDefaults(
                        ClassId classId) {
                    if (!classId.text().equals("@$external/host.bag/Bag")) {
                        return null;
                    }
                    Map<String, SemanticOracle.Value> fields = new LinkedHashMap<>();
                    fields.put("count", SemanticOracle.Value.MissingValue.INSTANCE);
                    fields.put("limit", new SemanticOracle.Value.IntValue(0));
                    return fields;
                }
            };
            deal.semantic.SemanticRuntimeModel.ConsumerRun run =
                SemanticOracle.execute(project, result.tables(), result.registries(),
                    responder, declarationLayouts(result));
            check(run.terminal()
                    instanceof deal.semantic.SemanticRuntimeModel.Terminal.Success,
                "the nullable-ops fixture succeeds in the oracle: " + run.terminal());
        } finally {
            deleteRecursively(luaWorkspace);
            deleteRecursively(jvmWorkspace);
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 6. The per-attempt default isolation
    // =========================================================================

    private static final String ISOLATION_SOURCE = """
        import * as cfg from "host/cfg"

        export function test_host_class_default_isolation(): string {
          let a: cfg.ServerConfig = {
            port: 9090,
            endpoint: { path: "/first" },
          };
          let b: cfg.ServerConfig = {
            port: 8080,
            endpoint: { path: "/second" },
            tags: ["two"],
            note: null,
          };
          if (a.port !== 9090) {
            throw { code: "TEST_FAIL", message: "first instance port mismatch" };
          }
          if (b.port !== 8080) {
            throw { code: "TEST_FAIL", message: "default table shared across instances" };
          }
          let tags: string[] | null = b.tags;
          if (tags !== null) {
            if (tags[0] !== "two") {
              throw { code: "TEST_FAIL", message: "second instance tag value mismatch" };
            }
          } else {
            throw { code: "TEST_FAIL", message: "second instance optional field lost" };
          }
          if (b.note !== null) {
            throw { code: "TEST_FAIL", message: "second instance nullable field mismatch" };
          }
          return "host class default isolation ok";
        }

        export function main(): null {
          return null;
        }
        """;

    private static void testDefaultIsolation() throws Exception {
        System.out.println("-- the per-attempt default isolation through the oracle"
            + " (the loaded defaults table is never mutated) --");
        Fixture compiled = compileSource("host-class-isolation", "cfg", "host/cfg",
            FIELD_OPS_DECLARATION, ISOLATION_SOURCE);
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the isolation fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            ModuleId hostModule = hostImportModule(project);
            List<Map<String, SemanticOracle.Value>> defaults = new ArrayList<>();
            SemanticOracle.HostResponder responder =
                corpusResponder(hostModule, "cfg", null, defaults);
            deal.semantic.SemanticRuntimeModel.ConsumerRun run =
                SemanticOracle.execute(project, result.tables(), result.registries(),
                    responder, declarationLayouts(result));
            check(run.terminal()
                    instanceof deal.semantic.SemanticRuntimeModel.Terminal.Success,
                "the isolation fixture succeeds in the oracle: " + run.terminal());
        } finally {
            deleteRecursively(compiled.root());
        }
    }

    // =========================================================================
    // 7. The negative load seeds (call-free)
    // =========================================================================

    private static final String CALL_FREE_SOURCE = """
        import * as cfg from "host/cfg"

        export function main(): null {
          return null;
        }
        """;

    private static final String LOAD_DECLARATION = """
        export class Endpoint {
          path: string;
        }

        export class ServerConfig {
          port: int;
          endpoint: Endpoint;
        }

        export function describe(s: ServerConfig): string;
        """;

    private static void testNegativeLoadSeeds() throws Exception {
        System.out.println("-- the call-free negative load seeds: the pinned E8011 at"
            + " the import origin on both targets --");
        Fixture compiled = compileSource("host-class-load-seed", "cfg", "host/cfg",
            LOAD_DECLARATION, CALL_FREE_SOURCE);
        Path workspace = Files.createTempDirectory("host-class-load-seed");
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(compiled);
            if (result.project() == null) {
                fail("the call-free seed fixture lowers: " + result.diagnostics());
                return;
            }
            ExecutableLoweredProject project = result.project();
            Path artifact = workspace.resolve("project.lua");
            Files.writeString(artifact, LuaSemanticEmitter.emitProductionProject(
                project, result.tables(), result.registries(), compiled.surface()),
                StandardCharsets.UTF_8);
            deployRuntime(workspace);
            // The four pinned loader defects of a declared host class surface.
            Map<String, String> seeds = new LinkedHashMap<>();
            seeds.put("missing-declared-export",
                "return { Endpoint = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/Endpoint\" },\n"
                    + "  Endpoint_defaults = { path = \"/\" },\n"
                    + "  describe = function(s) return \"\" end }\n");
            seeds.put("missing-class-meta",
                "return { Endpoint = 42,\n"
                    + "  ServerConfig = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/ServerConfig\" },\n"
                    + "  ServerConfig_defaults = { port = 8080, endpoint = {} },\n"
                    + "  describe = function(s) return \"\" end }\n");
            seeds.put("missing-defaults",
                "return { Endpoint = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/Endpoint\" },\n"
                    + "  Endpoint_defaults = { path = \"/\" },\n"
                    + "  ServerConfig = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/ServerConfig\" },\n"
                    + "  describe = function(s) return \"\" end }\n");
            seeds.put("non-table-defaults",
                "return { Endpoint = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/Endpoint\" },\n"
                    + "  Endpoint_defaults = { path = \"/\" },\n"
                    + "  ServerConfig = { __kind = \"class\", __classname ="
                    + " \"@$external/host.cfg/ServerConfig\" },\n"
                    + "  ServerConfig_defaults = 42,\n"
                    + "  describe = function(s) return \"\" end }\n");
            for (Map.Entry<String, String> seed : seeds.entrySet()) {
                writeFileIn(workspace, "host/cfg.lua", seed.getValue());
                Path probe = workspace.resolve("probe.lua");
                Files.writeString(probe, luaLoadProbe(artifact), StandardCharsets.UTF_8);
                Outcome outcome = runProcess(List.of("luajit",
                    probe.toAbsolutePath().toString()), workspace, false);
                check(outcome.exitCode() == 0 && outcome.stdout().contains("PROBE-OK"),
                    "the call-free seed '" + seed.getKey() + "' raises the pinned"
                        + " E8011 at the import origin under luajit: "
                        + outcome.output());
            }
            // The JVM load entry raises the same pinned E8011s: a missing
            // declared export, a declared class without its mandatory
            // defaults field, and a non-map defaults value.
            String className = JvmBackend.classNameFor(project.entryModule().path());
            JvmSemanticEmitter.EmissionResult emission =
                JvmSemanticEmitter.emitProductionProject(project, result.tables(),
                    result.registries(), className, compiled.surface());
            Files.writeString(workspace.resolve(className + ".java"),
                emission.source(), StandardCharsets.UTF_8);
            Files.writeString(workspace.resolve("LoadSeedProbe.java"),
                jvmLoadSeedProbe(className), StandardCharsets.UTF_8);
            Map<String, String> jvmSeeds = new LinkedHashMap<>();
            jvmSeeds.put("missing-declared-export",
                "final class HostCfg {\n"
                    + "  public static final java.util.Map<String, Object>"
                    + " Endpoint_defaults = java.util.Map.of(\"path\", \"/\");\n"
                    + "  public static final java.util.Map<String, Object>"
                    + " ServerConfig_defaults = java.util.Map.of(\"port\","
                    + " java.lang.Integer.valueOf(8080));\n"
                    + "}\n");
            jvmSeeds.put("missing-defaults-field",
                "final class HostCfg {\n"
                    + "  public static final java.util.Map<String, Object>"
                    + " Endpoint_defaults = java.util.Map.of(\"path\", \"/\");\n"
                    + "  public static Object describe(Object s) { return \"\"; }\n"
                    + "}\n");
            jvmSeeds.put("non-map-defaults",
                "final class HostCfg {\n"
                    + "  public static final java.util.Map<String, Object>"
                    + " Endpoint_defaults = java.util.Map.of(\"path\", \"/\");\n"
                    + "  public static final Object ServerConfig_defaults ="
                    + " java.lang.Integer.valueOf(42);\n"
                    + "  public static Object describe(Object s) { return \"\"; }\n"
                    + "}\n");
            Path classes = workspace.resolve("classes");
            Files.createDirectories(classes);
            String classpath = absoluteClasspath();
            for (Map.Entry<String, String> jvmSeed : jvmSeeds.entrySet()) {
                Files.writeString(workspace.resolve("HostCfg.java"), jvmSeed.getValue(),
                    StandardCharsets.UTF_8);
                Outcome javacRun = runProcess(List.of("javac", "--release", "25",
                    "-proc:none", "-cp", classpath, "-d", classes.toString(),
                    className + ".java", "HostCfg.java", "LoadSeedProbe.java"),
                    workspace, false);
                check(javacRun.exitCode() == 0,
                    "the call-free JVM seed '" + jvmSeed.getKey() + "' compiles: "
                        + javacRun.output());
                if (javacRun.exitCode() == 0) {
                    Outcome outcome = runProcess(List.of("java", "-cp",
                        classpath + java.io.File.pathSeparator + classes,
                        "LoadSeedProbe"), workspace, false);
                    check(outcome.exitCode() == 0
                            && outcome.stdout().contains("PROBE-OK"),
                        "the call-free JVM seed '" + jvmSeed.getKey() + "' raises the"
                            + " pinned E8011 at the import origin: "
                            + outcome.output());
                }
            }
        } finally {
            deleteRecursively(workspace);
            deleteRecursively(compiled.root());
        }
    }

    /**
     * The LuaJIT call-free probe: the chunk's own entry drive fails the
     * module init with the pinned E8011 at the import origin (the first
     * statement of the fixture source), so the load defect surfaces before
     * any test export runs.
     */
    private static String luaLoadProbe(Path artifact) {
        return """
            local function fail(m) print("PROBE-FAIL: " .. m) os.exit(1) end
            local ok, err = pcall(dofile, "%s")
            if ok then fail("the init succeeded") end
            if type(err) ~= "table" or err.code ~= "E8011" then
              fail("code: " .. tostring(type(err) == "table" and err.code or err))
            end
            -- The import origin: the import statement of the fixture source.
            if err.line ~= 1 or err.column ~= 1 then
              fail("origin: " .. tostring(err.line) .. ":" .. tostring(err.column))
            end
            print("PROBE-OK")
            """.formatted(artifact.toAbsolutePath().toString());
    }

    /** The JVM call-free probe: the load entry fails with E8011. */
    private static String jvmLoadSeedProbe(String className) {
        return """
            final class LoadSeedProbe {
              public static void main(String[] args) {
                try {
                  %s.dealMain();
                  throw new IllegalStateException("FAIL: no error");
                } catch (deal.codegen.jvm.JvmRuntime.DealError error) {
                  if (!"E8011".equals(error.code)) {
                    throw new IllegalStateException("FAIL: code " + error.code);
                  }
                }
                System.out.println("PROBE-OK");
              }
            }
            """.formatted(className);
    }

    // =========================================================================
    // The host-seam responder of the corpus host implementations
    // =========================================================================

    /**
     * The oracle responder of one corpus host implementation: the loaded
     * class defaults projection (the {@code <C>_defaults} tables with the
     * absent optionals as the miss sentinel), the declared host calls the
     * fixtures make ({@code describe}, {@code ping}), and — for the E8007
     * fixture — no defaults for the class the host implementation does not
     * carry a {@code fallback} entry in.
     */
    private static SemanticOracle.HostResponder corpusResponder(ModuleId hostModule,
            String hostStem, String failureClass) {
        return corpusResponder(hostModule, hostStem, failureClass, null);
    }

    private static SemanticOracle.HostResponder corpusResponder(ModuleId hostModule,
            String hostStem, String failureClass,
            List<Map<String, SemanticOracle.Value>> defaultsSink) {
        Map<String, Map<String, SemanticOracle.Value>> defaults = new LinkedHashMap<>();
        if (hostStem.equals("cfg")) {
            defaults.put("@$external/host.cfg/Endpoint", Map.of(
                "path", new SemanticOracle.Value.StrValue("/")));
            Map<String, SemanticOracle.Value> serverConfig = new LinkedHashMap<>();
            serverConfig.put("port", new SemanticOracle.Value.IntValue(8080));
            if (!"E8007".equals(failureClass)) {
                serverConfig.put("endpoint",
                    SemanticOracle.Value.MissingValue.INSTANCE);
                serverConfig.put("tags", SemanticOracle.Value.MissingValue.INSTANCE);
                serverConfig.put("note", SemanticOracle.Value.MissingValue.INSTANCE);
            }
            defaults.put("@$external/host.cfg/ServerConfig", serverConfig);
        } else {
            Map<String, SemanticOracle.Value> config = new LinkedHashMap<>();
            config.put("port", new SemanticOracle.Value.IntValue(8080));
            defaults.put("@$external/host.presence/Config", config);
        }
        return new SemanticOracle.HostResponder() {

            @Override
            public Map<String, SemanticOracle.Value> loadedClassDefaults(
                    ClassId classId) {
                Map<String, SemanticOracle.Value> projected = defaults.get(
                    classId.text());
                if (projected != null && defaultsSink != null) {
                    defaultsSink.add(projected);
                }
                return projected;
            }

            @Override
            public SyncOutcome call(ModuleId module, String export,
                    deal.semantic.ir.RuntimeDescriptor.Func descriptor,
                    List<SemanticOracle.Value> args) {
                if (export.equals("ping")) {
                    return new SyncOutcome.Returned(
                        new SemanticOracle.Value.StrValue("pong"));
                }
                if (export.equals("describe")) {
                    String path = "";
                    long port = 0;
                    if (!args.isEmpty()
                            && args.get(0) instanceof SemanticOracle.Value.ClassValue
                                instance) {
                        for (int i = 0; i < instance.fields().size(); i++) {
                            SemanticOracle.Value field = instance.fields().get(i)
                                instanceof SemanticOracle.Value.ClassFieldState.Present
                                    present ? present.value() : null;
                            if (i == 0 && field
                                    instanceof SemanticOracle.Value.IntValue portValue) {
                                port = portValue.value();
                            }
                            if (i == 1 && field
                                    instanceof SemanticOracle.Value.ClassValue endpoint) {
                                SemanticOracle.Value pathValue = endpoint.fields()
                                    .get(0)
                                    instanceof SemanticOracle.Value.ClassFieldState
                                        .Present present ? present.value() : null;
                                if (pathValue
                                        instanceof SemanticOracle.Value.StrValue str) {
                                    path = str.value();
                                }
                            }
                        }
                    }
                    return new SyncOutcome.Returned(
                        new SemanticOracle.Value.StrValue(path + ":" + port));
                }
                return new SyncOutcome.Thrown("E8010",
                    "the responder scripts no host call for " + module.path() + "."
                        + export);
            }
        };
    }

    // =========================================================================
    // Shared helpers
    // =========================================================================

    /** The distinct host class identities of the closure's host constructions. */
    private static List<ClassId> hostClassIds(ExecutableLoweredProject project) {
        java.util.Set<ClassId> ids = new java.util.LinkedHashSet<>();
        for (LoweredModuleUnit unit : project.modules().values()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_NEW) {
                    continue;
                }
                KindPayload.ClassNewPayload payload =
                    (KindPayload.ClassNewPayload) op.payload();
                if (payload.defaultOwner() == DefaultOwner.HOST_DEFAULTS) {
                    ids.add(payload.classId());
                }
            }
        }
        return List.copyOf(ids);
    }

    /** The single host import of the lowered project. */
    private static ModuleId hostImportModule(ExecutableLoweredProject project) {
        for (ModuleId module : project.modules().keySet()) {
            for (SemanticOp op : project.modules().get(module).ops()) {
                if (op.kind() == SemanticOpKind.MODULE_IMPORT
                        && ((KindPayload.ModuleImportPayload) op.payload()).kind()
                            == deal.semantic.ir.ModuleImportKind.HOST) {
                    return ((KindPayload.ModuleImportPayload) op.payload())
                        .resolvedModule();
                }
            }
        }
        throw new IllegalStateException("the fixture carries no host import");
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

    private static void deployHostLua(Path workspace, CorpusFixture fixture)
            throws Exception {
        deployHostLua(workspace, fixture.hostStem(), fixture.hostSpecifier());
    }

    private static void deployHostLua(Path workspace, String hostStem,
            String hostSpecifier) throws Exception {
        Path target = workspace.resolve(hostSpecifier + ".lua");
        Files.createDirectories(target.getParent());
        Files.copy(Path.of("test/conformance/host-fixtures/" + hostStem + ".lua"),
            target);
    }

    private static Outcome runProcess(List<String> command, Path workDir,
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
        return new Outcome(exit, stdout, stderr);
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

    private static void writeFileIn(Path root, String relative, String content)
            throws Exception {
        Path target = root.resolve(relative);
        Files.createDirectories(target.getParent());
        Files.writeString(target, content, StandardCharsets.UTF_8);
    }

    private static String luaString(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (char c : text.toCharArray()) {
            switch (c) {
                case '\\' -> sb.append("\\\\");
                case '"' -> sb.append("\\\"");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> sb.append(c);
            }
        }
        return sb.append("\"").toString();
    }

    private static String javaString(String text) {
        StringBuilder sb = new StringBuilder("\"");
        for (char c : text.toCharArray()) {
            switch (c) {
                case '\\' -> sb.append("\\\\");
                case '"' -> sb.append("\\\"");
                case '\n' -> sb.append("\\n");
                case '\r' -> sb.append("\\r");
                case '\t' -> sb.append("\\t");
                default -> sb.append(c);
            }
        }
        return sb.append("\"").toString();
    }

    /** A debugging dump of one fixture's emitted artifacts (never a verdict). */
    private static void dumpFixture(String name) throws Exception {
        Fixture compiled;
        switch (name) {
            case "nullable-ops" -> compiled = compileSource("host-class-nullable-ops",
                "bag", "host/bag", NULLABLE_OPS_DECLARATION, NULLABLE_OPS_SOURCE);
            case "field-ops" -> compiled = compileSource("host-class-field-ops", "cfg",
                "host/cfg", FIELD_OPS_DECLARATION, FIELD_OPS_SOURCE);
            default -> {
                CorpusFixture fixture = null;
                for (CorpusFixture candidate : ALL_FIXTURES) {
                    if (candidate.name().equals(name)) {
                        fixture = candidate;
                    }
                }
                if (fixture == null) {
                    throw new IllegalArgumentException("unknown fixture '" + name + "'");
                }
                compiled = compile(fixture);
            }
        }
        SemanticLowerer.ProjectLoweringResult result = lower(compiled);
        if (result.project() == null) {
            System.out.println("LOWERING FAILED: " + result.diagnostics());
            return;
        }
        String lua = LuaSemanticEmitter.emitProductionProject(result.project(),
            result.tables(), result.registries(), compiled.surface());
        Path luaOut = Path.of("/tmp/deal-dump-" + name + ".lua");
        Files.writeString(luaOut, lua, StandardCharsets.UTF_8);
        System.out.println("LUA: " + luaOut);
        String className = JvmBackend.classNameFor(
            result.project().entryModule().path());
        JvmSemanticEmitter.EmissionResult emission =
            JvmSemanticEmitter.emitProductionProject(result.project(), result.tables(),
                result.registries(), className, compiled.surface());
        Path javaOut = Path.of("/tmp/deal-dump-" + name + ".java");
        Files.writeString(javaOut, emission.source(), StandardCharsets.UTF_8);
        System.out.println("JAVA: " + javaOut);
        System.out.println("ENTRY: " + compiled.entryPath());
    }

    private static void deleteRecursively(Path path) {
        if (path == null || !Files.exists(path)) {
            return;
        }
        try (var walk = Files.walk(path)) {
            for (Path entry : walk.sorted(java.util.Comparator.reverseOrder())
                    .toList()) {
                Files.deleteIfExists(entry);
            }
        } catch (Exception ignored) {
            // Best-effort cleanup.
        }
    }

    public static void main(String[] args) throws Exception {
        System.out.println("=== Host-Declared Class Construction Tests (ISSUE-0624) ===\n");
        String dump = System.getenv("DEAL_DUMP_FIXTURE");
        if (dump != null) {
            dumpFixture(dump);
            return;
        }
        testLoweringShape();
        testLuaFixtures();
        testJvmFixtures();
        testOracle();
        testFieldOpsAndHas();
        testNullableFieldOps();
        testDefaultIsolation();
        testNegativeLoadSeeds();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== Host-Declared Class Construction Tests Passed ===");
    }
}
