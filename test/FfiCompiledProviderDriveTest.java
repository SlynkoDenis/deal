package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.distribution.DistributionHome;
import deal.ffi.FfiCdefBundle;
import deal.ffi.FfiGeneratedModule;
import deal.ffi.FfiImportedFunctionReference;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.ProductionProjectEmission;
import deal.project.ProjectLocator;
import deal.publication.PublicationStager;
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

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * ISSUE-0685: the compiled-provider entry adaptation and the end-to-end
 * drive ({@code plan-evaluator-provider-binding-surface} P3, the
 * compiled-provider entry call contract, and Verification 1; sequencing
 * step 2; the acceptance criterion of the compiled-provider drive).
 *
 * <ol>
 *   <li><b>The end-to-end drive.</b> An extern-C declaration importing a
 *       compiled provider module, whose {@code @c-struct} field defaults
 *       name the provider's exports (including an argument literal),
 *       compiles through {@code ProductionProjectEmission} with the
 *       compile's production FFI metadata; the emitted load opens the
 *       real native library of the committed FFIGEN integration fixture,
 *       and the published artifact executes under {@code luajit} with
 *       exit 0 — the program's own checks observe the provider's values
 *       on the constructed instances, the provider invocation count per
 *       attempt (through the shared native counter), the provider body's
 *       own typed boundary, and the native crossing of the same
 *       artifact.</li>
 *   <li><b>The artifact assertions.</b> The per-alias binding line
 *       {@code local <prefix><alias> = __exportSurfaces["<provider>"] or {}},
 *       the generated evaluator text
 *       {@code <prefix><alias>.<export>.f(<args>, nil, nil, nil)}, no
 *       dotted-path provider {@code require}, the bindings literal's
 *       canonical descriptor and provider contract digest, the
 *       {@code __rt.load_ffi(...)} import-statement span triplet, exactly
 *       one publication per referenced provider export (the provider
 *       module's own {@code EXPORT_PUBLISH} wrapper-convention entry,
 *       captured by identity), the plan entries' canonical descriptors
 *       (the phase-3 validation authority), the deployed
 *       {@code deal/runtime.lua} byte-identical to the repository's, and
 *       no {@code ffi.} text of any kind.</li>
 *   <li><b>The provider error's own origin.</b> A DEAL error the provider
 *       body raises propagates unchanged through the evaluator
 *       invocation to the construction site: a second entry whose
 *       construction is uncaught fails the deferred module-init entry
 *       with the provider's {@code code}, {@code message}, and its own
 *       recorded source origin.</li>
 *   <li><b>No compile-time library access.</b> The same checked closure
 *       re-emitted with a doctored generated module whose native-library
 *       text names a library that is never built still emits (no library
 *       open, no symbol resolution, no evaluator invocation at compile
 *       time), and executing that artifact raises the pinned
 *       {@code FFI_LIBRARY_LOAD} at the import statement — the runtime
 *       open is the existence check.</li>
 * </ol>
 */
public class FfiCompiledProviderDriveTest {

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
    // The focused project: an extern-C declaration importing a compiled
    // provider whose exports are the struct fields' deferred defaults
    // =========================================================================

    private static final String SPECIFIER = "native/probe";
    private static final String DOTTED = "native.probe";
    private static final String GAUGE_SPECIFIER = "native/gauge";
    private static final String PROVIDER = "util";
    private static final String NATIVE_LIBRARY = "libs/ffi-compiled-provider.so";

    /** The extern-C declaration: its plan defaults name a compiled provider. */
    private static final String DECLARATION = """
        import * as util from "./util"

        // @extern-c

        // @c-struct
        export class Pair {
          left: int = util.combine(7, 2);
          right: int = util.constant();
        }

        // @c-struct
        export class Counted {
          first: int = util.next();
          second: int = util.next();
        }

        // @c-struct
        export class Broken {
          value: int = util.boom();
        }

        // @c-struct
        export class BadRange {
          value: int = util.outOfRange();
        }

        export function fixture_add_int(a: int, b: int): int;
        """;

    /**
     * The second extern-C declaration: the committed fixture library's
     * shared call counter, the observable channel of the provider's
     * per-attempt invocation count.
     */
    private static final String GAUGE_DECLARATION = """
        // @extern-c

        export function fixture_count_call_int(): int;
        export function fixture_call_count(): int;
        export function fixture_reset_counter(): null;
        """;

    /** The compiled provider module the declaration's defaults call. */
    private static final String PROVIDER_SOURCE = """
        import * as gauge from "native/gauge";
        import * as json from "std/json";

        export function combine(a: int, b: int): int {
          return a - b;
        }

        export function constant(): int {
          return 42;
        }

        export function next(): int {
          return gauge.fixture_count_call_int();
        }

        export function outOfRange(): int {
          let doc: table = json.parse("{\\\"v\\\":2147483648}");
          let v: int = doc.v;
          return v;
        }

        export function boom(): int {
          throw { code: "PROVIDER_FAIL", message: "the provider body failed" };
        }
        """;

    /** The entry: its own checks observe the provider's values. */
    private static final String APP = """
        import * as native from "native/probe";
        import * as gauge from "native/gauge";

        export function main(): null {
          // No default evaluated at load: the plan's evaluators are
          // deferred into the runtime entry, which no module init runs.
          if (gauge.fixture_call_count() !== 0) {
            throw { code: "TEST_FAIL", message: "a provider default evaluated at load" };
          }
          // The compiled-provider default: both fields omitted, so the
          // provider's values land on the constructed instance. The
          // two-argument call is order-observable ((7, 2) -> 5), and the
          // zero-argument call renders the trailing nil triplet only.
          let pair: native.Pair = {};
          if (pair.left !== 5) {
            throw { code: "TEST_FAIL", message: "the provider's argument-literal default did not reach the instance" };
          }
          if (pair.right !== 42) {
            throw { code: "TEST_FAIL", message: "the provider's zero-argument default did not reach the instance" };
          }
          // Exactly one evaluator invocation per omitted required-present
          // field per attempt, in class source order: the provider's own
          // call counter observes two calls, and the second attempt
          // continues the counter.
          let counted: native.Counted = {};
          if (counted.first !== 1 || counted.second !== 2) {
            throw { code: "TEST_FAIL", message: "the omitted fields' provider evaluators did not run once each in class source order" };
          }
          if (gauge.fixture_call_count() !== 2) {
            throw { code: "TEST_FAIL", message: "the per-attempt provider invocation count" };
          }
          let again: native.Counted = {};
          if (again.first !== 3 || again.second !== 4) {
            throw { code: "TEST_FAIL", message: "the re-executed provider evaluators did not continue the counter" };
          }
          if (gauge.fixture_call_count() !== 4) {
            throw { code: "TEST_FAIL", message: "the final provider invocation count" };
          }
          // A provided field suppresses exactly its own provider evaluator:
          // the failing default does not run for the provided construction.
          let provided: native.Broken = { value: 7 };
          if (provided.value !== 7) {
            throw { code: "TEST_FAIL", message: "the provided field was not retained" };
          }
          // The compiled provider body keeps its own typed boundary: a
          // dynamic out-of-range value fails its declared int boundary and
          // the failure reaches the construction site.
          try {
            let bad: native.BadRange = {};
            throw { code: "TEST_FAIL", message: "the out-of-range provider value did not fail" };
          } catch (e) {
            if (e.code !== "E8004") {
              throw { code: "TEST_FAIL", message: "the out-of-range provider value raised the wrong code" };
            }
          }
          // The real native library loaded and its declared symbols
          // resolved: the native crossing of the same artifact still runs.
          if (gauge.fixture_call_count() !== 4) {
            throw { code: "TEST_FAIL", message: "the native counter moved without a provider invocation" };
          }
          if (native.fixture_add_int(20, 22) !== 42) {
            throw { code: "TEST_FAIL", message: "the native crossing did not resolve the real library symbol" };
          }
          return null;
        }
        """;

    /**
     * The error-origin entry: the construction of the failing provider
     * default is uncaught, so the deferred module-init entry observes the
     * provider's own error unchanged.
     */
    private static final String ORIGIN_APP = """
        import * as native from "native/probe";

        export function main(): null {
          let broken: native.Broken = {};
          return null;
        }
        """;

    /** The manifest of the focused project (the real native library). */
    private static String manifest(String libraryPath) {
        return """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "%s": {
                  "declaration": "src/native.d.deal",
                  "nativeLibrary": "%s"
                },
                "%s": {
                  "declaration": "src/gauge.d.deal",
                  "nativeLibrary": "%s"
                }
              }
            }
            """.formatted(SPECIFIER, libraryPath, GAUGE_SPECIFIER,
                libraryPath);
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /** One compiled fixture project of the drives. */
    private record Fixture(
        Path root,
        Path sourceRoot,
        Path outputRoot,
        String entryName,
        String entrySource,
        CheckedProjectInput checkedProject,
        ProjectInterfaceIndex index,
        List<SemanticRequirementManifest> manifests,
        HostDeclarationSurface surface,
        Map<ModuleId, FfiGeneratedModule> externCModules,
        Map<ModuleId, CanonicalModuleIdentity> declarationIdentities) {
    }

    /** One published production artifact. */
    private record Artifact(String name, String text) {
    }

    /** The materialized focused project (the shared gcc-built library). */
    private record Project(Path root, Path sourceRoot, Path outputRoot) {
    }

    /**
     * Materializes the focused project: the committed FFIGEN integration
     * C fixture compiled into the manifest-relative loader path (the real
     * native library), the extern-C declarations, the compiled provider,
     * the two entries, and the manifest.
     */
    private static Project materializeProject() throws Exception {
        Path root = Files.createTempDirectory("ffi-compiled-provider");
        Path libs = root.resolve("libs");
        Files.createDirectories(libs);
        String eventsPath = root.resolve("events.log").toString();
        ProcessOutcome gcc = runProcess(List.of("gcc", "-shared", "-fPIC",
            "-O2", "-DFIXTURE_EVENTS_PATH=\"" + eventsPath + "\"", "-o",
            libs.resolve("ffi-compiled-provider.so").toString(),
            Path.of("test", "fixtures", "ffigen",
                "ffigen-integration-fixture.c").toAbsolutePath().normalize()
                .toString()), root, Map.of());
        if (gcc.exitCode() != 0) {
            deleteRecursively(root);
            throw new IllegalStateException("the native fixture compile failed: "
                + gcc.stdout() + gcc.stderr());
        }
        Path src = root.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("native.d.deal"), DECLARATION,
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve("gauge.d.deal"), GAUGE_DECLARATION,
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve("util.deal"), PROVIDER_SOURCE,
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve("drive.deal"), APP,
            StandardCharsets.UTF_8);
        Files.writeString(src.resolve("origin.deal"), ORIGIN_APP,
            StandardCharsets.UTF_8);
        Files.writeString(root.resolve("deal.json"), manifest(NATIVE_LIBRARY),
            StandardCharsets.UTF_8);
        return new Project(root, src, root.resolve("build/lua"));
    }

    /**
     * Locates and compiles one entry of the focused project through the
     * production frontend (the manifest, the externals wiring, the FFI
     * metadata phase).
     */
    private static Fixture compileEntry(Project project, String entryName)
            throws Exception {
        Path entry = project.sourceRoot().resolve(entryName).toAbsolutePath();
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entry.toString(), null);
        if (located.context() == null) {
            throw new IllegalStateException("the focused project does not"
                + " locate: " + located.e2010());
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entry, false, false, false, false, null,
            productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null
                || built.index() == null || built.hasErrors() || manifests == null
                || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            String detail = built == null ? "no checked project"
                : String.valueOf(built.diagnostics());
            throw new IllegalStateException("the compiled-provider drive"
                + " fixture did not build: " + detail + " / "
                + orchestrator.diagnostics());
        }
        Map<ModuleId, FfiGeneratedModule> externCModules = new LinkedHashMap<>();
        for (Map.Entry<String, FfiGeneratedModule> generated
                : orchestrator.ffiGenerations().entrySet()) {
            externCModules.put(new ModuleId(generated.getKey()),
                generated.getValue());
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declarationModule
                : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declarationModule,
                new CanonicalModuleIdentity.ExternalModule(
                    declarationModule.path().replace('.', '/')));
        }
        return new Fixture(project.root(), project.sourceRoot(),
            project.outputRoot(), entryName,
            Files.readString(entry, StandardCharsets.UTF_8), built.input(),
            built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), externCModules, identities);
    }

    /** Emits one fixture through the production arm and publishes it. */
    private static Artifact emitAndPublish(Fixture fixture, Path out)
            throws Exception {
        return emitAndPublish(fixture, out, fixture.externCModules());
    }

    /** Emits one fixture through the production arm with the given input. */
    private static Artifact emitAndPublish(Fixture fixture, Path out,
            Map<ModuleId, FfiGeneratedModule> externCModules) throws Exception {
        PublicationStager stager = PublicationStager.forRoot(out);
        ProductionProjectEmission.Result result;
        try {
            result = ProductionProjectEmission.run(productionInvocation(),
                fixture.checkedProject(), fixture.index(), fixture.manifests(),
                fixture.surface(), fixture.declarationIdentities(),
                externCModules, fixture.root().toString(),
                BuiltinErrorDeclaration.synthesized(
                    fixture.checkedProject().modules().get(0).ast().span()),
                List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT),
                Set.of(), Backend.LUAJIT, false,
                DistributionHome.forManifestDirectory(
                    fixture.root().toString()),
                stager);
            if (result.emitted()) {
                stager.publish();
            }
        } finally {
            stager.discard();
        }
        if (!result.emitted()) {
            throw new IllegalStateException("the compiled-provider artifact did"
                + " not emit: " + result.diagnostics());
        }
        String name = result.artifactRelativePath();
        return new Artifact(name,
            Files.readString(out.resolve(name), StandardCharsets.UTF_8));
    }

    // =========================================================================
    // 1. The end-to-end drive
    // =========================================================================

    private static void testCompiledProviderEndToEndDrive() throws Exception {
        System.out.println("-- the compiled-provider default executes through"
            + " the production artifact under luajit --");
        Project project = materializeProject();
        try {
            Fixture fixture = compileEntry(project, "drive.deal");
            Path out = fixture.outputRoot();
            check(!fixture.externCModules().isEmpty(),
                "the compile publishes the extern-C generated metadata");
            FfiGeneratedModule module = fixture.externCModules()
                .get(new ModuleId(DOTTED));
            check(module != null, "the metadata is keyed by the declaration"
                + " module's resolved identity");
            if (module == null) {
                return;
            }
            check(module.bindings().importedFunctions().size() >= 5,
                "the metadata carries the provider references: "
                    + module.bindings().importedFunctions().size());
            check(module.bindings().importedFunctions().stream()
                    .allMatch(ref -> PROVIDER.equals(ref.importedModulePath())),
                "every reference resolves the compiled provider module");
            Artifact emitted = emitAndPublish(fixture, out);
            String artifact = emitted.text();
            checkEq("drive.lua", emitted.name(),
                "the one project artifact is named for the entry module");

            // (a) The per-alias binding line and the generated evaluator text.
            String prefix = matchGroup(artifact, Pattern.compile(
                "local (__ffi_import_\\d+_util) = __exportSurfaces\\[\"util\"\\]"
                    + " or \\{\\}"));
            check(prefix != null, "the artifact carries the registry-resolved"
                + " binding line for the provider alias");
            if (prefix == null) {
                return;
            }
            checkEq(1, countOccurrences(artifact, "local " + prefix + " ="),
                "one binding line per referenced alias (several references"
                    + " through one alias emit no second binding)");
            check(artifact.contains("function() return " + prefix
                    + ".combine.f(7, 2, nil, nil, nil) end"),
                "the plans literal carries the generated evaluator text with"
                    + " the argument literal and the trailing nil triplet");
            check(artifact.contains("function() return " + prefix
                    + ".constant.f(nil, nil, nil) end"),
                "a zero-argument provider evaluator renders the trailing nil"
                    + " triplet only");
            check(!artifact.contains("require(\"util\")")
                    && !artifact.contains("require('util')"),
                "no dotted-path provider require is emitted");
            check(artifact.contains("__exportSurfaces[\"util\"] = "
                    + "__exportSurfaces[\"util\"] or {}"),
                "the chunk creates the provider's surface object before any"
                    + " module walk (the binding captures it by identity)");
            String bindingLine = "local " + prefix
                + " = __exportSurfaces[\"util\"] or {}";
            String ordinal = matchGroup(prefix,
                Pattern.compile("__ffi_import_(\\d+)_util"));
            check(ordinal != null, "the binding prefix carries its import"
                + " ordinal: " + prefix);
            if (ordinal != null) {
                String bindingsLine = "local __ffi_bindings_" + ordinal + " =";
                int bindingAt = artifact.indexOf(bindingLine);
                int bindingsAt = artifact.indexOf(bindingsLine);
                int loadAt = artifact.indexOf("__exportSurfaces[\"native.probe\"]"
                    + " = __exportSurfaces[\"native.probe\"] or __rt.load_ffi("
                    + "\"ffi:@$external/native/probe\"");
                check(bindingAt >= 0 && bindingsAt > bindingAt,
                    "the binding line precedes the bindings literal of the"
                        + " same import (ordinal " + ordinal + ")");
                check(loadAt > bindingsAt,
                    "the bindings literal precedes the load publication of the"
                        + " same import (ordinal " + ordinal + ")");
            }

            // (b) The bindings literal's canonical descriptor and provider
            // contract digest.
            for (FfiImportedFunctionReference ref : module.bindings()
                    .importedFunctions()) {
                check(artifact.contains("importAlias = \"util\", exportName = \""
                        + ref.exportName() + "\", importedModulePath = \"util\","
                        + " canonicalDescriptor = \"" + ref.canonicalDescriptor()
                        + "\", providerContractDigest = \""
                        + ref.providerContractDigest() + "\""),
                    "the bindings literal carries the canonical descriptor and"
                        + " the provider contract digest of '" + ref.exportName()
                        + "': " + ref.canonicalDescriptor());
            }

            // (c) The load publication with the import statement's span.
            int importLine = lineOf(fixture.entrySource(),
                "import * as native from");
            String entryText = fixture.sourceRoot()
                .resolve(fixture.entryName()).toAbsolutePath().toString();
            check(artifact.contains("__exportSurfaces[\"native.probe\"] = "
                    + "__exportSurfaces[\"native.probe\"] or __rt.load_ffi("),
                "the artifact publishes the loaded table through load_ffi");
            check(artifact.contains(", \"" + entryText + "\", " + importLine
                    + ", 1)"),
                "the load carries the import statement's span triplet (file, "
                    + importLine + ", 1)");

            // (d) The serviced entry is the provider module's own published
            // EXPORT_PUBLISH entry: exactly one wrapper-convention surface
            // entry per referenced export, captured by identity (no
            // per-alias copy, no surface mutation, no second value shape).
            for (String exportName : List.of("combine", "constant", "next",
                    "outOfRange", "boom")) {
                checkEq(1, countOccurrences(artifact,
                        "__exportSurfaces[\"util\"][\"" + exportName + "\"] = "),
                    "exactly one published surface entry for '" + exportName
                        + "' (the provider module's own EXPORT_PUBLISH)");
            }
            check(artifact.contains("__exportSurfaces[\"util\"][\"combine\"] = "
                    + "{__kind = \"function\", sig = \"(int,int)->int\", f = "
                    + "__unfn("),
                "the serviced entry is the provider's published"
                    + " wrapper-convention entry (the compiled carrier's"
                    + " invoker, next to __kind and sig)");
            // (e) No compile-time library access text, and no ABI conversion
            // for the compiled-provider call.
            check(!artifact.contains("ffi."),
                "the artifact carries no ffi.*/cdef/library text");
            Path deployedRuntime = out.resolve("deal/runtime.lua");
            check(Files.isRegularFile(deployedRuntime)
                    && Files.mismatch(deployedRuntime,
                        Path.of("deal/runtime.lua")) == -1,
                "the artifact deploys the repository's deal/runtime.lua"
                    + " unchanged (the compiled-provider call adds no runtime"
                    + " code)");
            check(artifact.contains("evaluator = function() return " + prefix
                    + ".combine.f(7, 2, nil, nil, nil) end"),
                "the plan entry's evaluator is the direct provider call"
                    + " (no conversion, no adapter)");
            check(artifact.contains("{ name = \"left\", descriptor = \"int\","
                    + " optional = false, evaluator = function() return "
                    + prefix + ".combine.f(7, 2, nil, nil, nil) end }"),
                "the provider-defaulted field's plan entry carries the"
                    + " field's canonical descriptor (the phase-3 validation"
                    + " authority)");

            // (f) The execution: the program's own checks observe the
            // provider's values through the real library load.
            ProcessOutcome run = runProcess(List.of("luajit", emitted.name()),
                out, Map.of());
            checkEq(0, run.exitCode(), "the drive executes clean: exit="
                + run.exitCode() + " stdout=" + escaped(run.stdout())
                + " stderr=" + escaped(run.stderr()));
            check(run.stdout().isEmpty() && run.stderr().isEmpty(),
                "the drive's transcript is empty: stdout="
                    + escaped(run.stdout()) + " stderr="
                    + escaped(run.stderr()));
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 2. The provider error's own origin
    // =========================================================================

    private static void testProviderErrorOriginProbe() throws Exception {
        System.out.println("-- a provider-raised DEAL error reaches the"
            + " construction site unchanged (its own code, message, origin) --");
        Project project = materializeProject();
        try {
            Fixture fixture = compileEntry(project, "origin.deal");
            Path out = fixture.outputRoot().resolve("origin");
            Artifact emitted = emitAndPublish(fixture, out);
            Files.writeString(out.resolve("probe.lua"),
                failureProbe(emitted.name()), StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"),
                out, Map.of("DEAL_DEFER_MAIN", "1"));
            checkEq(0, run.exitCode(), "the origin probe runs: exit="
                + run.exitCode() + " stderr=" + escaped(run.stderr()));
            String[] parts = run.stdout().trim().split("\\|", -1);
            check(parts.length >= 6 && "ERR".equals(parts[0]),
                "the deferred entry fails with a DEAL error: "
                    + escaped(run.stdout()));
            if (parts.length < 6 || !"ERR".equals(parts[0])) {
                return;
            }
            checkEq("PROVIDER_FAIL", parts[1],
                "the provider's own code reaches the construction site");
            checkEq("the provider body failed", parts[2],
                "the provider's own message reaches the construction site");
            String providerText = fixture.sourceRoot().resolve("util.deal")
                .toAbsolutePath().toString();
            checkEq(providerText + ":" + lineOf(PROVIDER_SOURCE,
                    "throw { code: \"PROVIDER_FAIL\"") + ":"
                    + columnOf(PROVIDER_SOURCE, "throw { code"),
                parts[3] + ":" + parts[4] + ":" + parts[5],
                "the provider's own recorded origin reaches the construction"
                    + " site");
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // 3. No compile-time library access
    // =========================================================================

    private static void testNoCompileTimeLibraryAccess() throws Exception {
        System.out.println("-- the emission never opens a library or resolves"
            + " a symbol: a never-built library text still emits --");
        Project project = materializeProject();
        try {
            Fixture fixture = compileEntry(project, "drive.deal");
            Map<ModuleId, FfiGeneratedModule> doctored = new LinkedHashMap<>();
            for (Map.Entry<ModuleId, FfiGeneratedModule> entry
                    : fixture.externCModules().entrySet()) {
                if (!new ModuleId(DOTTED).equals(entry.getKey())) {
                    // The gauge declaration keeps its real library: the
                    // failure must come from the driven import.
                    doctored.put(entry.getKey(), entry.getValue());
                    continue;
                }
                FfiGeneratedModule module = entry.getValue();
                FfiCdefBundle bundle = module.cdefBundle();
                FfiCdefBundle missingLibrary = new FfiCdefBundle(
                    bundle.bundleDigest(), bundle.identityDigest(),
                    bundle.fullContent(), bundle.entries(),
                    "MANIFEST_RELATIVE_PATH", "libs/never-built.so",
                    bundle.functions(), bundle.classes());
                doctored.put(entry.getKey(), new FfiGeneratedModule(
                    module.modulePath(), module.descriptor(), missingLibrary,
                    module.plans(), module.bindings()));
            }
            Path out = fixture.outputRoot().resolve("never-built");
            Artifact emitted = emitAndPublish(fixture, out, doctored);
            String expectedLoaderText = fixture.root().resolve("libs")
                .resolve("never-built.so").toAbsolutePath().toString();
            check(emitted.text().contains("loaderText = \""
                    + expectedLoaderText + "\""),
                "the emission resolves the never-built loader text without"
                    + " opening it: " + expectedLoaderText);
            check(!emitted.text().contains("ffi.cdef")
                    && !emitted.text().contains("ffi.C["),
                "the never-built artifact carries no cdef/library text");
            // The runtime open is the existence check: executing the
            // artifact raises the pinned FFI_LIBRARY_LOAD at the import
            // statement, which proves the emitted text is the load's
            // authority and that the emission itself opened nothing.
            Files.writeString(out.resolve("probe.lua"),
                failureProbe(emitted.name()), StandardCharsets.UTF_8);
            ProcessOutcome run = runProcess(List.of("luajit", "probe.lua"),
                out, Map.of("DEAL_DEFER_MAIN", "1"));
            checkEq(0, run.exitCode(), "the never-built probe runs: exit="
                + run.exitCode() + " stderr=" + escaped(run.stderr()));
            String[] parts = run.stdout().trim().split("\\|", -1);
            check(parts.length >= 6 && "ERR".equals(parts[0]),
                "the never-built load fails with a DEAL error: "
                    + escaped(run.stdout()));
            if (parts.length < 6 || !"ERR".equals(parts[0])) {
                return;
            }
            checkEq("FFI_LIBRARY_LOAD", parts[1],
                "the never-built library fails the runtime load");
            String entryText = fixture.sourceRoot()
                .resolve(fixture.entryName()).toAbsolutePath().toString();
            checkEq(entryText, parts[3],
                "the load failure names the import statement's file");
            checkEq(String.valueOf(lineOf(fixture.entrySource(),
                    "import * as native from")), parts[4],
                "the load failure names the import statement's line");
            checkEq("1", parts[5],
                "the load failure names the import statement's column");
        } finally {
            deleteRecursively(project.root());
        }
    }

    // =========================================================================
    // Process, tool, and filesystem helpers
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

    /** The LuaJIT failure probe of one artifact (the deferred entry). */
    private static String failureProbe(String artifactName) {
        return """
            local function fail(message)
              print("PROBE-FAIL|" .. message)
              os.exit(1)
            end
            local surface = dofile("%s")
            if type(surface) ~= "table" then fail("the chunk returns no surface") end
            local ok, err = __dealMain()
            if ok then fail("the module init succeeded") end
            if type(err) ~= "table" or err.code == nil then
              fail("the raised value is not a runtime error table")
            end
            local message = err.message or err.m
            local file, line, column = err.file, err.line, err.column
            if err.o ~= nil then
              local f, l, c = tostring(err.o):match("^(.*):(%%d+):(%%d+)$")
              file, line, column = f, l, c
            end
            print("ERR|" .. tostring(err.code) .. "|" .. tostring(message)
              .. "|" .. tostring(file) .. "|" .. tostring(line) .. "|"
              .. tostring(column))
            """.formatted(artifactName);
    }

    private static String matchGroup(String text, Pattern pattern) {
        Matcher matcher = pattern.matcher(text);
        return matcher.find() ? matcher.group(1) : null;
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

    private static int lineOf(String source, String needle) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(needle)) {
                return i + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + needle + "'");
    }

    private static int columnOf(String source, String needle) {
        for (String line : source.split("\n", -1)) {
            int at = line.indexOf(needle);
            if (at >= 0) {
                return at + 1;
            }
        }
        throw new IllegalStateException("no line carries '" + needle + "'");
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

    public static void main(String[] args) throws Exception {
        testCompiledProviderEndToEndDrive();
        testProviderErrorOriginProbe();
        testNoCompileTimeLibraryAccess();
        System.out.println();
        System.out.println("passed=" + passed + " failed=" + failed);
        if (failed > 0) {
            System.exit(1);
        }
        System.out.println("=== FFI Compiled-Provider Drive Tests Passed ===");
    }
}
