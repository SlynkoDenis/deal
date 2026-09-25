package deal.test;

import deal.codegen.jvm.JvmSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.RangeOrigin;
import deal.module.CompilationOrchestrator;
import deal.project.CliOverrides;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.test.conformance.CorpusDiscovery;
import deal.test.conformance.CorpusFfi;
import deal.test.conformance.SidecarExpectations;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

/**
 * ISSUE-0669: the JVM pre-artifact E6006 rejection proof and the
 * declaration negatives
 * ({@code ffi-admission-and-jvm-e6006-rejection} A2/A3 and the
 * C-FFI-incapable-target rejection and declaration-negative contracts;
 * {@code luajit-ffi-shared-emission-and-jvm-rejection} F4/F5;
 * sequencing step 7).
 *
 * <ol>
 *   <li>The seven extern-C corpus fixtures ({@code ffi/022} through
 *       {@code ffi/027} plus the T3 fixture
 *       {@code ffi/051-ffi-invalid-string}, enumerated so a missing
 *       fixture fails the drive) compile through the real manifest
 *       locator and the real orchestrator with {@code Backend.JVM} and
 *       fail with exactly one E6006 error whose message is the pinned
 *       {@code FFI_UNSUPPORTED_BACKEND} text at the declaration
 *       module's {@code @extern-c} directive range: the compile fails
 *       after the checked project (declaration validation ran) and
 *       before phase 4 (no {@code FFI_PLAN} lowering, no declaration
 *       surface, no lowering diagnostics); no FFI metadata is
 *       published, no lowering or emission runs, and the previously
 *       published artifact set stays byte-identical with no stage
 *       residue.</li>
 *   <li>Declaration validation runs first: {@code ffi/047} with
 *       {@code support/invalid-async.d.deal} reports its E7002 family
 *       (the async exported function at its pinned range) with no
 *       E6006 for that module under JVM and the same E7002 with no
 *       metadata under LuaJIT; a two-declaration closure reports the
 *       invalid module's E7002 and exactly one E6006 at the valid
 *       sibling's directive range — never an E6006 for the invalid
 *       module.</li>
 *   <li>The declaration negatives keep their pinned diagnostics and
 *       ranges through the real pipeline: async exports, the parameter
 *       and return allowlists ({@code bytes} return, nullable classed
 *       positions), a non-empty {@code @c-pointer} body, an optional
 *       or default-less field, duplicate struct fields, duplicate
 *       exports, a plan-key collision, and the struct-field allowlist
 *       (string, nested class) — each a clean single-diagnostic
 *       rejection with no metadata and nothing staged.</li>
 *   <li>A {@code C_POINTER} class literal stays a checker rejection:
 *       an object-literal construction of a pointer value in a
 *       declaration default or call argument is the validator's E7002
 *       at the literal range, and a pointer-class literal in an
 *       implementation module never reaches a construction (the
 *       compile fails closed at the plan-demand gate before the FFI
 *       phase, with no metadata and nothing staged).</li>
 *   <li>The JS backend keeps its import-site E6006 arm: the same
 *       fixtures under {@code Backend.JS} fail with exactly one E6006
 *       whose message contains {@code FFI_UNSUPPORTED_BACKEND} at the
 *       import statement, with no FFI metadata and nothing
 *       staged.</li>
 *   <li>The JVM production entry keeps its pinned input list (the
 *       validated project, the tables, the registries, the entry class
 *       name, and the host declaration surface; no
 *       {@code deal.ffi.FfiGeneratedModule} input) — the invariant's
 *       single owner is the orchestrator's phase-3.9 arm.</li>
 * </ol>
 */
public class FfiJvmRejectionAndNegativesTest {

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
    // Corpus coordinates and pinned texts
    // =========================================================================

    private static final Path CONFORMANCE_ROOT = Path.of("test/conformance");
    private static final String FFI_DIR = CorpusFfi.FFI_DIR;
    private static final String NATIVE = "candidate/native";
    private static final String INVALID_ASYNC = "candidate/invalid-async";

    /** The pinned JVM rejection message ({@code DiagnosticCode.E6006}). */
    private static final String JVM_PINNED_MESSAGE =
        "JVM backend: C FFI (@extern-c) declarations are not supported"
            + " (FFI_UNSUPPORTED_BACKEND)";

    /** The pinned JS import-site rejection text. */
    private static final String JS_PINNED_MESSAGE =
        "JavaScript backend: @extern-c imports are not supported"
            + " (FFI_UNSUPPORTED_BACKEND, ISSUE-0169 skeleton)";

    /** The unsupported-backend token both rejection arms carry. */
    private static final String UNSUPPORTED_TOKEN = "FFI_UNSUPPORTED_BACKEND";

    /** The {@code @extern-c} directive comment text (the pinned range). */
    private static final String EXTERN_C_DIRECTIVE = "// @extern-c";

    /** The enumeration of the JVM rejection drive (never skipped). */
    private static final List<String> JVM_REJECTION_FIXTURES = List.of(
        "022-ffi-null-string",
        "023-ffi-invalid-utf8",
        "024-ffi-null-pointer",
        "025-ffi-missing-symbol",
        "026-ffi-library-load-failure",
        "027-ffi-unsupported-backends",
        "051-ffi-invalid-string");

    /** The declaration negative of the corpus async fixture. */
    private static final String ASYNC_FIXTURE = "047-ffi-async-declaration-rejected";

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    // =========================================================================
    // The compile harness (the lane-shaped manifest materialization)
    // =========================================================================

    /**
     * One compiled fixture project: the temp root, the entry file, the
     * output override, the mirrored declaration files (raw import
     * specifier to absolute path), the orchestrator, and its success
     * flag.
     */
    private record CompileOutcome(
        Path root,
        Path entry,
        Path output,
        Map<String, Path> declarations,
        CompilationOrchestrator orchestrator,
        boolean success) {

        List<CompilerDiagnostic> diagnostics() {
            return orchestrator.diagnostics();
        }

        List<CompilerDiagnostic> errors() {
            return orchestrator.diagnostics().stream()
                .filter(d -> "error".equals(d.severity())).toList();
        }

        List<CompilerDiagnostic> diagnosticsOf(String code) {
            return orchestrator.diagnostics().stream()
                .filter(d -> code.equals(d.code())).toList();
        }
    }

    /**
     * Materializes one project root (sources plus the injected exact-1.2
     * manifest with the externals wiring), locates it through the real
     * {@link ProjectLocator} with the explicit backend/output overrides,
     * and compiles it through the real orchestrator under the
     * release-owned production invocation.
     */
    private static CompileOutcome compileProject(Path root,
            Map<String, String> rootRelativeSources,
            Map<String, String> externalsToDeclaration,
            String entryRelative, String backend, Path output)
            throws Exception {
        for (Map.Entry<String, String> source : rootRelativeSources.entrySet()) {
            Path file = root.resolve(source.getKey());
            Files.createDirectories(file.getParent());
            Files.writeString(file, source.getValue(),
                StandardCharsets.UTF_8);
        }
        List<String> entries = new ArrayList<>();
        Map<String, Path> declarations = new LinkedHashMap<>();
        for (Map.Entry<String, String> external
                : externalsToDeclaration.entrySet()) {
            entries.add("    \"" + external.getKey()
                + "\": { \"declaration\": \"" + external.getValue()
                + "\", \"nativeLibrary\":"
                + " \"support/libcandidate_native.so\" }");
            declarations.put(external.getKey(),
                root.resolve(external.getValue()).toAbsolutePath().normalize());
        }
        StringBuilder manifest = new StringBuilder();
        manifest.append("{\n");
        manifest.append("  \"languageVersion\": \"1.2\",\n");
        manifest.append("  \"moduleRoots\": [\"src\"],\n");
        manifest.append("  \"output\": \"out\",\n");
        manifest.append("  \"backend\": \"luajit\"");
        if (!entries.isEmpty()) {
            manifest.append(",\n  \"externals\": {\n");
            manifest.append(String.join(",\n", entries));
            manifest.append("\n  }");
        }
        manifest.append("\n}\n");
        Files.writeString(root.resolve("deal.json"), manifest.toString(),
            StandardCharsets.UTF_8);

        Path entry = root.resolve(entryRelative).toAbsolutePath().normalize();
        ProjectLocator.LocateResult located = ProjectLocator.locate(
            entry.toString(), new CliOverrides(backend,
                output == null ? null : output.toString()));
        if (located.context() == null) {
            throw new IllegalStateException("the materialized project '"
                + root + "' does not locate strictly: " + located.e2010());
        }
        CompilerInvocation invocation = productionInvocation();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            located.context(), entry, false, false, false, false, null,
            invocation);
        boolean success = orchestrator.compile();
        return new CompileOutcome(root, entry, output, declarations,
            orchestrator, success);
    }

    /**
     * Materializes one corpus fixture (classification headers stripped,
     * exactly as the lanes do) with the corpus-owned FFI declarations
     * of the imports the fixture actually carries, and compiles it
     * under the given backend.
     */
    private static CompileOutcome compileCorpusFixture(String fixtureName,
            String backend, Path output) throws Exception {
        Path fixture = CONFORMANCE_ROOT.resolve(FFI_DIR)
            .resolve(fixtureName + ".deal");
        String source = ConformanceHarnessMetadata.stripClassificationHeaders(
            Files.readString(fixture, StandardCharsets.UTF_8));
        Path root = Files.createTempDirectory("ffi-jvm-rejection-");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/" + fixtureName + ".deal", source);
        Map<String, String> externals = new LinkedHashMap<>();
        for (String raw : CorpusDiscovery.ffiImportPaths(source)) {
            CorpusFfi.Wiring wiring = CorpusFfi.wiringFor(CONFORMANCE_ROOT,
                raw);
            if (wiring == null || externals.containsKey(raw)) {
                continue;
            }
            String declarationName = "bindings/ffi_"
                + raw.replace('/', '_') + ".d.deal";
            String declaration =
                ConformanceHarnessMetadata.stripClassificationHeaders(
                    Files.readString(CONFORMANCE_ROOT.resolve(FFI_DIR)
                        .resolve(wiring.declarationCorpusPath()),
                        StandardCharsets.UTF_8));
            sources.put(declarationName, declaration);
            externals.put(raw, declarationName);
        }
        return compileProject(root, sources, externals,
            "src/" + fixtureName + ".deal", backend, output);
    }

    // =========================================================================
    // Artifact-set helpers (zero staging / byte identity)
    // =========================================================================

    private static List<String> artifactFiles(Path root) throws Exception {
        if (!Files.isDirectory(root)) {
            return List.of();
        }
        try (Stream<Path> walk = Files.walk(root)) {
            return walk.filter(Files::isRegularFile)
                .map(path -> root.relativize(path).toString()
                    .replace(java.io.File.separatorChar, '/'))
                .sorted().toList();
        }
    }

    private static Map<String, byte[]> snapshotTree(Path root)
            throws Exception {
        Map<String, byte[]> snapshot = new LinkedHashMap<>();
        for (String relative : artifactFiles(root)) {
            snapshot.put(relative, Files.readAllBytes(root.resolve(relative)));
        }
        return snapshot;
    }

    private static void checkTreeIdentical(Map<String, byte[]> before,
            Path root, String context) throws Exception {
        Map<String, byte[]> after = snapshotTree(root);
        boolean same = before.keySet().equals(after.keySet());
        if (same) {
            for (Map.Entry<String, byte[]> entry : before.entrySet()) {
                same = Arrays.equals(entry.getValue(),
                    after.get(entry.getKey()));
                if (!same) {
                    break;
                }
            }
        }
        check(same, context + ": the prior artifact set is byte-identical");
    }

    /** No staging residue survives a failed compile (the D2 cleanup). */
    private static void checkNoStageResidue(Path output, String context)
            throws Exception {
        Path parent = output.toAbsolutePath().normalize().getParent();
        if (parent == null || !Files.isDirectory(parent)) {
            return;
        }
        String prefix = output.getFileName().toString() + ".deal-stage-";
        try (Stream<Path> siblings = Files.list(parent)) {
            List<String> residue = siblings
                .map(p -> p.getFileName().toString())
                .filter(name -> name.startsWith(prefix))
                .sorted().toList();
            check(residue.isEmpty(), context
                + ": no staging residue survives the failed compile: "
                + residue);
        }
    }

    /**
     * The real prior artifact set: one successful release-owned JVM
     * production compile whose published tree every rejection drive
     * must leave byte-identical.
     */
    private record PriorSet(Path projectRoot, Path output,
                            Map<String, byte[]> tree) {
    }

    private static PriorSet publishPriorArtifactSet() throws Exception {
        Path root = Files.createTempDirectory("ffi-jvm-prior-");
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("src/main.deal",
            "export function main(): null {\n  return null;\n}\n");
        Path output = root.resolve("out");
        Files.createDirectories(output);
        CompileOutcome outcome = compileProject(root, sources, Map.of(),
            "src/main.deal", "jvm", output);
        check(outcome.success(), "the prior release-owned JVM production"
            + " artifact set publishes: " + outcome.diagnostics());
        Map<String, byte[]> tree = snapshotTree(output);
        check(!tree.isEmpty(), "the prior artifact set is non-empty");
        return new PriorSet(root, output, tree);
    }

    // =========================================================================
    // Range helpers
    // =========================================================================

    /** The 1-based line of the needle's first occurrence. */
    private static int lineOf(String source, String needle) {
        int line = 1;
        int index = 0;
        int found = source.indexOf(needle);
        if (found < 0) {
            throw new IllegalStateException("the source carries no '"
                + needle + "'");
        }
        while (index < found) {
            if (source.charAt(index) == '\n') {
                line++;
            }
            index++;
        }
        return line;
    }

    /** The 1-based column of the needle on its line. */
    private static int columnOf(String source, String needle) {
        int found = source.indexOf(needle);
        if (found < 0) {
            throw new IllegalStateException("the source carries no '"
                + needle + "'");
        }
        int lineStart = source.lastIndexOf('\n', found - 1) + 1;
        return found - lineStart + 1;
    }

    /** The absolute normalized range-file path of one diagnostic. */
    private static Path rangeFileOf(CompilerDiagnostic diagnostic) {
        return Path.of(diagnostic.range().file()).toAbsolutePath().normalize();
    }

    /**
     * Asserts one diagnostic's range is the whole {@code @extern-c}
     * directive comment of the mirrored declaration file and returns
     * that file.
     */
    private static Path checkExternCDirectiveRange(String context,
            CompilerDiagnostic diagnostic, CompileOutcome outcome)
            throws Exception {
        Path rangeFile = rangeFileOf(diagnostic);
        Path declaration = null;
        for (Path candidate : outcome.declarations().values()) {
            if (candidate.equals(rangeFile)) {
                declaration = candidate;
            }
        }
        check(declaration != null, context + ": the diagnostic range is a"
            + " declaration module of the compile, got " + rangeFile);
        if (declaration == null) {
            return null;
        }
        String text = Files.readString(declaration, StandardCharsets.UTF_8);
        int line = lineOf(text, EXTERN_C_DIRECTIVE);
        checkEq(line, diagnostic.range().startLine(),
            context + ": the @extern-c directive start line");
        checkEq(columnOf(text, EXTERN_C_DIRECTIVE),
            diagnostic.range().startColumn(),
            context + ": the @extern-c directive start column");
        checkEq(line, diagnostic.range().endLine(),
            context + ": the @extern-c directive end line");
        checkEq(columnOf(text, EXTERN_C_DIRECTIVE)
                + EXTERN_C_DIRECTIVE.length(),
            diagnostic.range().endColumn(),
            context + ": the @extern-c directive end column (the whole"
                + " directive comment)");
        checkEq(RangeOrigin.SOURCE, diagnostic.range().origin(),
            context + ": the range is a computed source range");
        return declaration;
    }

    /** The mirrored declaration file of one raw import specifier. */
    private static Path declarationOf(CompileOutcome outcome, String raw) {
        Path declaration = outcome.declarations().get(raw);
        if (declaration == null) {
            throw new IllegalStateException("the materialized project has no"
                + " declaration for '" + raw + "'");
        }
        return declaration;
    }

    // =========================================================================
    // 1. The JVM pre-artifact E6006 rejection over the named fixtures
    // =========================================================================

    private static void testJvmRejectionExactness(PriorSet prior)
            throws Exception {
        System.out.println("-- the JVM pre-artifact E6006 rejection over"
            + " ffi/022-ffi/027 and ffi/051 --");
        for (String name : JVM_REJECTION_FIXTURES) {
            checkJvmRejectionOf(name, prior);
        }
        checkTreeIdentical(prior.tree(), prior.output(),
            "the seven JVM rejections");
        checkNoStageResidue(prior.output(), "the seven JVM rejections");
    }

    private static void checkJvmRejectionOf(String name, PriorSet prior)
            throws Exception {
        Path fixture = CONFORMANCE_ROOT.resolve(FFI_DIR)
            .resolve(name + ".deal");
        Path sidecar = CONFORMANCE_ROOT.resolve(FFI_DIR)
            .resolve(name + ".expect.json");
        // The enumeration never skips a named fixture: a missing file
        // (in particular the T3 fixture ffi/051) fails the drive.
        check(Files.isRegularFile(fixture), name + ": the corpus fixture"
            + " exists (the enumeration never skips a named fixture)");
        check(Files.isRegularFile(sidecar), name + ": the corpus sidecar"
            + " exists");
        if (!Files.isRegularFile(fixture) || !Files.isRegularFile(sidecar)) {
            return;
        }
        checkDivergentSidecar(name, sidecar);

        CompileOutcome outcome = compileCorpusFixture(name, "jvm",
            prior.output());
        try {
            check(!outcome.success(), name + ": the JVM compile fails");
            List<CompilerDiagnostic> errors = outcome.errors();
            checkEq(1, errors.size(), name + ": exactly one error"
                + " diagnostic: " + errors);
            if (errors.size() != 1) {
                return;
            }
            CompilerDiagnostic diagnostic = errors.get(0);
            checkEq("E6006", diagnostic.code(), name + ": the diagnostic"
                + " code");
            checkEq(JVM_PINNED_MESSAGE, diagnostic.message(),
                name + ": the pinned rejection message");
            check(diagnostic.message().contains(UNSUPPORTED_TOKEN),
                name + ": the message contains " + UNSUPPORTED_TOKEN);
            Path declaration = checkExternCDirectiveRange(name, diagnostic,
                outcome);
            if (declaration != null) {
                // The rejected declaration is the module the fixture
                // imports.
                String rejected = Files.readString(declaration,
                    StandardCharsets.UTF_8);
                check(rejected.contains(EXTERN_C_DIRECTIVE),
                    name + ": the rejected module carries the @extern-c"
                        + " directive");
            }

            // The rejection is pre-lowering and pre-emission: the
            // checked project exists (declaration validation ran after
            // phases 0-3.5), phase 4's declaration surface does not
            // exist, no FFI metadata was published, and no lowering or
            // emission ran.
            check(outcome.orchestrator().checkedProject() != null,
                name + ": the rejection runs after the checked project"
                    + " (declaration validation first)");
            check(outcome.orchestrator().hostDeclarationSurface() == null,
                name + ": phase 4 never started (no declaration surface,"
                    + " no FFI_PLAN lowering)");
            check(outcome.orchestrator().ffiGenerations().isEmpty(),
                name + ": no generated-module entry is published on an"
                    + " incapable backend");
            checkEq(0, outcome.orchestrator().semanticEmissionCount(),
                name + ": no production emission ran");
            checkEq(0, outcome.orchestrator().retainedEmissionCount(),
                name + ": no retained emission ran");
            check(outcome.orchestrator().jvmGeneratedResults().isEmpty(),
                name + ": no per-module JVM result exists");
            check(outcome.orchestrator().routePlan() == null,
                name + ": the release-owned invocation computes no route"
                    + " plan");
            checkTreeIdentical(prior.tree(), prior.output(), name);
            checkNoStageResidue(prior.output(), name);
        } finally {
            deleteRecursively(outcome.root());
        }
    }

    /**
     * The corpus sidecar of every rejection fixture keeps the
     * sanctioned divergent form: a LuaJIT execution expectation plus
     * the {@code jvm}/{@code js} {@code compile-reject} E6006 entries.
     */
    private static void checkDivergentSidecar(String name, Path sidecar)
            throws Exception {
        SidecarExpectations.StructuredExpectationSidecar parsed =
            SidecarExpectations.StructuredExpectationSidecar.parse(
                Files.readString(sidecar, StandardCharsets.UTF_8));
        for (String backend : List.of("jvm", "js")) {
            SidecarExpectations.RuntimeExpectation expectation =
                parsed.expectationFor(backend);
            check(expectation
                    instanceof SidecarExpectations.RuntimeExpectation.Rejected,
                name + ": the " + backend + " leg is a compile-reject"
                    + " expectation");
            if (expectation
                    instanceof SidecarExpectations.RuntimeExpectation.Rejected
                        rejected) {
                checkEq("compile-reject", rejected.mode(),
                    name + ": the " + backend + " mode");
                checkEq("E6006", rejected.code(),
                    name + ": the " + backend + " diagnostic code");
            }
        }
    }

    // =========================================================================
    // 2. Declaration validation runs first
    // =========================================================================

    private static void testDeclarationValidationFirst(PriorSet prior)
            throws Exception {
        System.out.println("-- declaration validation first: the invalid"
            + " module reports E7002 with no E6006 for it --");
        checkInvalidAsyncFixture("jvm", prior);
        checkInvalidAsyncFixture("luajit", prior);

        // The two-module ordering: the invalid declaration reports its
        // E7002 and no E6006 for that module, while the valid sibling
        // keeps exactly one E6006 at its own directive range (one
        // diagnostic per declaration module).
        Path root = Files.createTempDirectory("ffi-declaration-first-");
        try {
            String invalid = ConformanceHarnessMetadata
                .stripClassificationHeaders(Files.readString(
                    CONFORMANCE_ROOT.resolve(FFI_DIR).resolve("support")
                        .resolve("invalid-async.d.deal"),
                    StandardCharsets.UTF_8));
            String nativeDeclaration = ConformanceHarnessMetadata
                .stripClassificationHeaders(Files.readString(
                    CONFORMANCE_ROOT.resolve(FFI_DIR).resolve("support")
                        .resolve("native.d.deal"),
                    StandardCharsets.UTF_8));
            Map<String, String> sources = new LinkedHashMap<>();
            sources.put("src/main.deal",
                "import * as bad from \"" + INVALID_ASYNC + "\"\n"
                    + "import * as good from \"" + NATIVE + "\"\n\n"
                    + "export function main(): null {\n  return null;\n}\n");
            sources.put("bindings/ffi_invalid_async.d.deal", invalid);
            sources.put("bindings/ffi_native.d.deal", nativeDeclaration);
            Map<String, String> externals = new LinkedHashMap<>();
            externals.put(INVALID_ASYNC,
                "bindings/ffi_invalid_async.d.deal");
            externals.put(NATIVE, "bindings/ffi_native.d.deal");
            CompileOutcome outcome = compileProject(root, sources, externals,
                "src/main.deal", "jvm", prior.output());
            try {
                check(!outcome.success(), "the mixed-closure JVM compile"
                    + " fails");
                List<CompilerDiagnostic> errors = outcome.errors();
                checkEq(2, errors.size(), "the mixed closure reports the"
                    + " invalid module's E7002 and the valid module's"
                    + " E6006: " + errors);
                Path invalidFile = declarationOf(outcome, INVALID_ASYNC);
                Path nativeFile = declarationOf(outcome, NATIVE);
                String invalidText = Files.readString(invalidFile,
                    StandardCharsets.UTF_8);
                List<CompilerDiagnostic> e7002 =
                    outcome.diagnosticsOf("E7002");
                checkEq(1, e7002.size(), "exactly one E7002 for the invalid"
                    + " module: " + e7002);
                if (e7002.size() == 1) {
                    CompilerDiagnostic diagnostic = e7002.get(0);
                    checkEq(invalidFile, rangeFileOf(diagnostic),
                        "the E7002 is reported on the invalid declaration");
                    checkEq(lineOf(invalidText,
                            "export async function invalidAsync"),
                        diagnostic.range().startLine(),
                        "the E7002 is at the async function declaration");
                    check(diagnostic.message().contains(
                            "async function declaration 'invalidAsync'"),
                        "the E7002 names the async function: "
                            + diagnostic.message());
                }
                List<CompilerDiagnostic> e6006 =
                    outcome.diagnosticsOf("E6006");
                checkEq(1, e6006.size(), "exactly one E6006 for the valid"
                    + " sibling: " + e6006);
                for (CompilerDiagnostic diagnostic : e6006) {
                    checkEq(nativeFile, rangeFileOf(diagnostic),
                        "the E6006 belongs to the valid sibling, never the"
                            + " invalid module");
                    checkEq(JVM_PINNED_MESSAGE, diagnostic.message(),
                        "the E6006 message is the pinned text");
                    checkExternCDirectiveRange("the mixed closure",
                        diagnostic, outcome);
                }
                check(outcome.orchestrator().ffiGenerations().isEmpty(),
                    "the mixed closure publishes no FFI metadata");
                check(outcome.orchestrator().hostDeclarationSurface()
                        == null,
                    "the mixed closure runs no lowering");
                checkTreeIdentical(prior.tree(), prior.output(),
                    "the mixed-closure rejection");
            } finally {
                deleteRecursively(outcome.root());
            }
        } finally {
            deleteRecursively(root);
        }
    }

    private static void checkInvalidAsyncFixture(String backend,
            PriorSet prior) throws Exception {
        String context = ASYNC_FIXTURE + " under " + backend;
        CompileOutcome outcome = compileCorpusFixture(ASYNC_FIXTURE, backend,
            prior.output());
        try {
            check(!outcome.success(), context + ": the compile fails");
            List<CompilerDiagnostic> errors = outcome.errors();
            checkEq(1, errors.size(), context + ": exactly one error"
                + " diagnostic: " + errors);
            if (errors.size() != 1) {
                return;
            }
            CompilerDiagnostic diagnostic = errors.get(0);
            checkEq("E7002", diagnostic.code(), context + ": the pinned"
                + " declaration-negative code");
            check(diagnostic.message().contains(
                    "async function declaration 'invalidAsync'"),
                context + ": the E7002 names the async function: "
                    + diagnostic.message());
            Path declaration = declarationOf(outcome, INVALID_ASYNC);
            String text = Files.readString(declaration,
                StandardCharsets.UTF_8);
            checkEq(declaration, rangeFileOf(diagnostic), context + ": the"
                + " diagnostic is reported on the declaration module");
            checkEq(lineOf(text, "export async function invalidAsync"),
                diagnostic.range().startLine(), context + ": the pinned"
                + " async function line");
            checkEq(columnOf(text, "async function invalidAsync"),
                diagnostic.range().startColumn(), context + ": the pinned"
                + " async function column");
            check(outcome.diagnosticsOf("E6006").isEmpty(), context + ": no"
                + " E6006 for the invalid module");
            check(outcome.orchestrator().ffiGenerations().isEmpty(),
                context + ": no FFI metadata is published for the invalid"
                    + " declaration");
            checkTreeIdentical(prior.tree(), prior.output(), context);
        } finally {
            deleteRecursively(outcome.root());
        }
    }

    // =========================================================================
    // 3. The declaration negatives
    // =========================================================================

    private static void testDeclarationNegatives(PriorSet prior)
            throws Exception {
        System.out.println("-- the declaration negatives keep their pinned"
            + " diagnostics and ranges --");

        // The allowlist: bytes in return position and nullable classed
        // positions (parameter and return).
        checkNegative(prior, "bytes return",
            """
            // @extern-c

            export function bad(): bytes;
            """,
            "E7002", 3, 24, 3,
            "bytes is not a valid C FFI return type (bytes is parameter-only)");
        checkNegative(prior, "nullable parameter",
            """
            // @extern-c

            // @c-pointer
            export class Handle {
            }

            export function bad(h: Handle | null): int;
            """,
            "E7002", 7, 24, 7,
            "parameter type nullable is not in the C FFI parameter"
                + " allowlist");
        checkNegative(prior, "nullable return",
            """
            // @extern-c

            // @c-pointer
            export class Handle {
            }

            export function bad(): Handle | null;
            """,
            "E7002", 7, 24, 7,
            "return type nullable is not in the C FFI return allowlist");

        // The pointer shapes: a non-empty @c-pointer body and the
        // object-literal construction of a pointer value (the
        // C_POINTER literal, section 4).
        checkNegative(prior, "non-empty @c-pointer body",
            """
            // @extern-c

            // @c-pointer
            export class Bad {
              x: int = 0;
            }
            """,
            "E7002", 4, 8, 6,
            "@c-pointer class 'Bad' must have an empty body");

        // The field defaults: an optional field is the validator's
        // E7002, a default-less field is the shared planner's E4001.
        checkNegative(prior, "optional struct field",
            """
            // @extern-c

            // @c-struct
            export class Bad {
              a?: int = 0;
            }
            """,
            "E7002", 5, 3, 6,
            "field 'a' of @c-struct class 'Bad' must be required (not"
                + " optional)");
        checkNegative(prior, "default-less struct field",
            """
            // @extern-c

            // @c-struct
            export class Bad {
              b: int;
            }
            """,
            "E4001", 5, 3, 6,
            "field 'b' of class 'Bad' must provide a default value"
                + " expression");

        // Duplicates: a duplicate struct field (the validator's E7002,
        // never a raw plan-construction defect), a duplicate export
        // (the checker's redeclaration), and a plan-key collision.
        checkNegative(prior, "duplicate struct field",
            """
            // @extern-c

            // @c-struct
            export class Bad {
              a: int = 0;
              a: int = 1;
            }
            """,
            "E7002", 6, 3, 7,
            "duplicate field 'a' in @c-struct class 'Bad'");
        checkNegative(prior, "duplicate export",
            """
            // @extern-c

            export function f(): int;
            export function f(): int;
            """,
            "E2002", 4, 8, 5,
            "Redeclaration of 'f'");
        checkNegative(prior, "plan-key collision",
            """
            // @extern-c

            // @c-struct
            export class Vec2 {
              x: number = 0.0;
            }

            export function Vec2_plan(): int;
            """,
            "E7002", 8, 8, 9,
            "exported function name 'Vec2_plan' collides with a class plan"
                + " entry key");

        // The struct-field allowlist: a string field and a nested
        // same-file class are outside it.
        checkNegative(prior, "string struct field",
            """
            // @extern-c

            // @c-struct
            export class Bad {
              s: string = "";
            }
            """,
            "E7002", 5, 6, 5,
            "struct field type 'string' is not in the struct-field"
                + " allowlist");
        checkNegative(prior, "nested class struct field",
            """
            // @extern-c

            // @c-struct
            export class Inner {
              x: int = 0;
            }

            // @c-struct
            export class Outer {
              inner: Inner = { x: 0 };
            }
            """,
            "E7002", 10, 10, 10,
            "@c-struct fields cannot nest");
    }

    /**
     * Drives one single-negative declaration through the real pipeline
     * under {@code Backend.JVM} and pins its diagnostic code, range,
     * and message: exactly one error, no FFI metadata, phase 4 never
     * started, and the prior artifact set byte-identical.
     */
    private static void checkNegative(PriorSet prior, String label,
            String declaration, String expectedCode, int line, int column,
            int endLine, String messageFragment) throws Exception {
        Path root = Files.createTempDirectory("ffi-negative-");
        try {
            Map<String, String> sources = new LinkedHashMap<>();
            sources.put("src/main.deal",
                "import * as m from \"native/math\"\n\n"
                    + "export function main(): null {\n  return null;\n}\n");
            sources.put("bindings/native.d.deal", declaration);
            CompileOutcome outcome = compileProject(root, sources,
                Map.of("native/math", "bindings/native.d.deal"),
                "src/main.deal", "jvm", prior.output());
            try {
                check(!outcome.success(), label + ": the compile fails");
                List<CompilerDiagnostic> errors = outcome.errors();
                checkEq(1, errors.size(), label + ": exactly one error"
                    + " diagnostic: " + errors);
                if (errors.size() == 1) {
                    CompilerDiagnostic diagnostic = errors.get(0);
                    checkEq(expectedCode, diagnostic.code(), label + ": the"
                        + " pinned code");
                    check(diagnostic.message().contains(messageFragment),
                        label + ": the message [" + diagnostic.message()
                            + "] contains [" + messageFragment + "]");
                    checkEq(line, diagnostic.range().startLine(), label
                        + ": the pinned line");
                    checkEq(column, diagnostic.range().startColumn(), label
                        + ": the pinned column");
                    checkEq(endLine, diagnostic.range().endLine(), label
                        + ": the pinned end line");
                    checkEq(root.resolve("bindings/native.d.deal")
                            .toAbsolutePath().normalize(),
                        rangeFileOf(diagnostic), label + ": the pinned"
                            + " declaration file");
                    check(outcome.diagnosticsOf("E6006").isEmpty(), label
                        + ": no E6006 for the invalid module");
                }
                check(outcome.orchestrator().ffiGenerations().isEmpty(),
                    label + ": no FFI metadata is published");
                check(outcome.orchestrator().hostDeclarationSurface()
                        == null,
                    label + ": phase 4 never started (no lowering)");
                checkTreeIdentical(prior.tree(), prior.output(), label);
            } finally {
                deleteRecursively(outcome.root());
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 4. The C_POINTER class literal stays outside the construct set
    // =========================================================================

    private static void testPointerLiteralOutsideTheConstructSet(
            PriorSet prior) throws Exception {
        System.out.println("-- the C_POINTER class literal stays a checker"
            + " rejection and never reaches a construction --");

        // The declaration-side pointer literals: a struct-field default
        // and a same-file call argument are both the validator's E7002
        // at the literal range (pointer tokens come from C only).
        checkNegative(prior, "pointer literal in a struct default",
            """
            // @extern-c

            // @c-pointer
            export class Handle {
            }

            // @c-struct
            export class Box {
              ptr: Handle = {};
            }
            """,
            "E7002", 9, 17, 9,
            "object-literal construction of @c-pointer value 'Handle'");
        checkNegative(prior, "pointer literal in a call argument",
            """
            // @extern-c

            // @c-pointer
            export class Handle {
            }

            export function wrap(h: Handle): Handle;

            // @c-struct
            export class Box {
              ptr: Handle = wrap({});
            }
            """,
            "E7002", 11, 22, 11,
            "object-literal construction of @c-pointer value 'Handle'");

        // The implementation-side pointer literal is not constructible
        // either: the compile fails closed at the plan-demand gate
        // before the FFI phase, so no construction op, no FFI metadata,
        // and no artifact exists.
        Path root = Files.createTempDirectory("ffi-pointer-literal-");
        try {
            String declaration = ConformanceHarnessMetadata
                .stripClassificationHeaders(Files.readString(
                    CONFORMANCE_ROOT.resolve(FFI_DIR).resolve("support")
                        .resolve("native.d.deal"),
                    StandardCharsets.UTF_8));
            Map<String, String> sources = new LinkedHashMap<>();
            sources.put("src/main.deal",
                "import * as native from \"" + NATIVE + "\";\n\n"
                    + "export function main(): null {\n"
                    + "  let h: native.Handle = {};\n"
                    + "  return null;\n}\n");
            sources.put("bindings/ffi_candidate_native.d.deal",
                declaration);
            CompileOutcome outcome = compileProject(root, sources,
                Map.of(NATIVE, "bindings/ffi_candidate_native.d.deal"),
                "src/main.deal", "jvm", prior.output());
            try {
                check(!outcome.success(), "the implementation-side pointer"
                    + " class literal compile fails closed");
                List<CompilerDiagnostic> errors = outcome.errors();
                checkEq(1, errors.size(), "the pointer literal reports"
                    + " exactly one fail-closed diagnostic: " + errors);
                for (CompilerDiagnostic diagnostic : errors) {
                    checkEq("E6005", diagnostic.code(), "the fail-closed"
                        + " producer code");
                    check(diagnostic.message().contains(
                            "no planned class 'Handle'"),
                        "the failure names the pointer class: "
                            + diagnostic.message());
                    check(!diagnostic.message().contains(
                            "CONSTRUCT_UNLOWERED")
                            && !diagnostic.message().contains(
                                "RETAINED_ABI_DEFERRED"),
                        "the pointer literal is rejected before any"
                            + " construction op: " + diagnostic.message());
                }
                check(outcome.diagnosticsOf("E6006").isEmpty(), "the"
                    + " pointer literal fails before the FFI phase: no"
                    + " E6006");
                check(outcome.orchestrator().ffiGenerations().isEmpty(),
                    "the pointer literal publishes no FFI metadata");
                check(outcome.orchestrator().hostDeclarationSurface()
                        == null,
                    "the pointer literal reaches no lowering");
                checkTreeIdentical(prior.tree(), prior.output(),
                    "the pointer literal rejection");
            } finally {
                deleteRecursively(outcome.root());
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 5. The JS backend keeps its import-site E6006 arm
    // =========================================================================

    private static void testJsImportSiteRejection(PriorSet prior)
            throws Exception {
        System.out.println("-- the JS backend keeps its import-site E6006"
            + " arm --");
        for (String name : List.of("022-ffi-null-string",
                "051-ffi-invalid-string")) {
            CompileOutcome outcome = compileCorpusFixture(name, "js",
                prior.output());
            try {
                check(!outcome.success(), name + " (js): the compile fails");
                List<CompilerDiagnostic> errors = outcome.errors();
                checkEq(1, errors.size(), name + " (js): exactly one error"
                    + " diagnostic: " + errors);
                if (errors.size() == 1) {
                    CompilerDiagnostic diagnostic = errors.get(0);
                    checkEq("E6006", diagnostic.code(), name + " (js): the"
                        + " diagnostic code");
                    checkEq(JS_PINNED_MESSAGE, diagnostic.message(),
                        name + " (js): the pinned import-site text");
                    check(diagnostic.message().contains(UNSUPPORTED_TOKEN),
                        name + " (js): the message contains "
                            + UNSUPPORTED_TOKEN);
                    Path entryFile = outcome.entry();
                    String entryText = Files.readString(entryFile,
                        StandardCharsets.UTF_8);
                    String importStatement = "import * as native";
                    checkEq(entryFile, rangeFileOf(diagnostic), name
                        + " (js): the rejection is reported at the import"
                        + " statement");
                    checkEq(lineOf(entryText, importStatement),
                        diagnostic.range().startLine(), name + " (js): the"
                            + " import statement line");
                    checkEq(columnOf(entryText, importStatement),
                        diagnostic.range().startColumn(), name + " (js):"
                            + " the import statement column");
                }
                check(outcome.orchestrator().ffiGenerations().isEmpty(),
                    name + " (js): no FFI metadata is published");
                checkTreeIdentical(prior.tree(), prior.output(),
                    name + " (js)");
            } finally {
                deleteRecursively(outcome.root());
            }
        }
    }

    // =========================================================================
    // 6. The JVM production entry keeps its pinned input list
    // =========================================================================

    private static void testJvmProductionEntryPinnedInputs() {
        System.out.println("-- the JVM production entry keeps its pinned"
            + " input list --");
        List<Method> entries = new ArrayList<>();
        for (Method method : JvmSemanticEmitter.class.getDeclaredMethods()) {
            if (method.getName().equals("emitProductionProject")) {
                entries.add(method);
            }
        }
        checkEq(1, entries.size(), "JvmSemanticEmitter publishes exactly one"
            + " emitProductionProject entry");
        if (entries.size() != 1) {
            return;
        }
        Method entry = entries.get(0);
        check(Modifier.isPublic(entry.getModifiers())
                && Modifier.isStatic(entry.getModifiers()),
            "emitProductionProject is a public static entry");
        checkEq(List.of(
                ExecutableLoweredProject.class,
                Map.class,
                Map.class,
                String.class,
                HostDeclarationSurface.class),
            List.of(entry.getParameterTypes()),
            "emitProductionProject consumes exactly the validated project,"
                + " the tables, the registries, the entry class name, and"
                + " the host declaration surface");
        for (Class<?> parameter : entry.getParameterTypes()) {
            check(!parameter.getName().equals("deal.ffi.FfiGeneratedModule"),
                "the JVM production entry takes no extern-C emission input: "
                    + parameter.getName());
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            try (Stream<Path> walk = Files.walk(dir)) {
                for (Path path : walk.sorted(Comparator.reverseOrder())
                        .toList()) {
                    Files.deleteIfExists(path);
                }
            }
        } catch (Exception e) {
            // Best-effort temp cleanup only; never part of a test result.
        }
    }

    public static void main(String[] args) throws Exception {
        System.out.println("=== FFI JVM E6006 Rejection and Declaration"
            + " Negatives Tests (ISSUE-0669) ===");
        PriorSet prior = publishPriorArtifactSet();
        try {
            testJvmRejectionExactness(prior);
            testDeclarationValidationFirst(prior);
            testDeclarationNegatives(prior);
            testPointerLiteralOutsideTheConstructSet(prior);
            testJsImportSiteRejection(prior);
            testJvmProductionEntryPinnedInputs();
        } finally {
            deleteRecursively(prior.projectRoot());
        }
        System.out.println();
        System.out.println("passed: " + passed + ", failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
