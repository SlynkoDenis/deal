package deal.test;

import deal.Main;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.project.ProjectLocator;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * ISSUE-0506 D11 production project-graph fixture gates (design source
 * {@code production-project-graph-fixtures} D3/D8; the
 * {@code ProjectIntegrationGatesTest} pattern): the five committed
 * fixture trees under {@code test/project-graph-fixtures/modules-manifests}
 * run through the whole-project pipeline — the test-scope harness compile
 * entry ({@link HarnessCompileEntry}; ISSUE-0643 P10 item 3, mechanism 1)
 * for the compile and artifact verdicts, the release-owned
 * {@link Main#run(String[])} CLI for the production-invocation probes of
 * the three compile-ok gates (their HOST-kind declaration imports are
 * realized by the host load of the module init walk, so ISSUE-0656
 * retargeted their probes to the emitted-and-staged outcome), and a real
 * {@link ProjectLocator#locate(String, deal.project.CliOverrides)} call
 * for the F5 locate verdict — with every pin transcribed from the landed
 * emission, never hand-authored from a message pattern.
 *
 * <p>Gates: G1 declaration-cycle-two-modules (compile-ok), G2
 * runtime-cycle-class-default-three-modules (exactly one E2005), G3
 * leading-import-type (compile-ok), G4 module-roots-bare-import
 * (compile-ok, bare {@code pkg/util} resolved under the configured root),
 * G5 c-ffi-native-library-required (locate failure with the exact landed
 * E2010). The gate-authoring perturbations (Verification 4) run on
 * scratch copies only: F1 without externals → E2010; F2 with the
 * class-field default {@code B.get(1)} replaced by {@code 1} →
 * compile-ok. A perturbation that does not flip its gate fails the gate
 * — never silently kept.</p>
 *
 * <p>Every CLI run redirects {@code --output} to a fresh temp directory
 * (deleted afterwards) and the committed fixture trees stay byte-identical
 * after every run (asserted by a pre/post digest snapshot). The gates
 * spawn no subprocesses: all verdicts come from in-process
 * {@link HarnessCompileEntry} calls, in-process {@link Main#run(String[])}
 * production-invocation probes, or in-process
 * {@code ProjectLocator.locate} calls.</p>
 */
public class ProjectGraphFixturesGatesTest {

    private static int passed = 0;
    private static int failed = 0;

    /** The emitted private module-artifact names: m + 16 lowercase hex. */
    private static final Pattern LUA_MODULE_ID =
        Pattern.compile("m[0-9a-f]{16}\\.lua");

    /** The committed production project-graph fixture root. */
    private static final Path FIXTURES =
        Path.of("test", "project-graph-fixtures", "modules-manifests");
    private static final Path F1_DIR =
        FIXTURES.resolve("cycles/declaration-cycle-two-modules");
    private static final Path F2_DIR =
        FIXTURES.resolve("cycles/runtime-cycle-class-default-three-modules");
    private static final Path F3_DIR =
        FIXTURES.resolve("declarations/leading-import-type");
    private static final Path F4_DIR =
        FIXTURES.resolve("manifests/module-roots-bare-import");
    private static final Path F5_DIR =
        FIXTURES.resolve("manifests/c-ffi-native-library-required");

    /**
     * The F5 pin constants, transcribed from the landed emission's actual
     * formatted output (D8 pin-at-landing mechanics — captured by running
     * the gate against the landed production code, never hand-authored):
     *
     * <pre>
     * &lt;checkout&gt;/.../manifests/c-ffi-native-library-required/deal.json:4:18-6:6:
     *     ERROR E2010: deal.json: externals entry 'host/math': declaration
     *     'bindings/host-math.d.deal' is an extern-C declaration without a
     *     nativeLibrary: a C FFI entry must include nativeLibrary
     *     (docs/spec-v1.2.md:1891) [span 56]
     * </pre>
     *
     * The locate-path CLI emission carries no "N error(s), M warning(s)"
     * summary (that summary is orchestrator-owned and compile-phase only),
     * so the gate pins the single-diagnostic shape instead: exactly one
     * ERROR line, zero warnings, and a structured document field-exact to
     * {@code DiagnosticStructuredOutput.toJson(List.of(e2010))}.
     */
    private static final String F5_PIN_MESSAGE =
        "deal.json: externals entry 'host/math': declaration"
            + " 'bindings/host-math.d.deal' is an extern-C declaration"
            + " without a nativeLibrary: a C FFI entry must include"
            + " nativeLibrary (docs/spec-v1.2.md:1891)";
    /** The checkout-independent verbatim suffix of the formatted line. */
    private static final String F5_PIN_LINE_SUFFIX =
        "deal.json:4:18-6:6: ERROR E2010: " + F5_PIN_MESSAGE + " [span 56]";

    /**
     * The G2 chain (checkout-independent: each emitted path is absolute
     * and ends in the pinned relative components, so the components must
     * appear in order with the " -> " separators between them).
     */
    private static final Pattern E2005_CHAIN = Pattern.compile(
        "support/runtime_three_a\\.deal"
            + " -> .*?support/runtime_three_b\\.deal"
            + " -> .*?support/runtime_three_c\\.deal"
            + " -> .*?support/runtime_three_a\\.deal");

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

    /** A committed fixture file must exist (never silently skipped). */
    private static void requireFixture(Path dir, String rel) {
        Path file = dir.resolve(rel);
        check(Files.isRegularFile(file), "missing fixture file: " + file);
    }

    /**
     * Runs the same CLI-equivalent arguments through the test-scope
     * harness compile entry ({@link HarnessCompileEntry}; ISSUE-0643 P10
     * item 3, mechanism 1) with System.err captured; returns {exitCode,
     * stderr}. The three compile-ok gate fixtures carry HOST-kind
     * declaration imports and a cross-module call the release-owned
     * production invocation fails closed, so the retained per-module
     * artifact verdicts stay green through the harness invocation while
     * the production arm's outcome is asserted separately.
     */
    private static String[] runCliCapturingErr(String[] args) throws IOException {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = HarnessCompileEntry.run(args);
            System.err.flush();
        } finally {
            System.setErr(originalErr);
        }
        return new String[]{String.valueOf(exitCode),
            err.toString(StandardCharsets.UTF_8)};
    }

    /**
     * Runs the release-owned production CLI ({@link Main#run(String[])})
     * with System.err captured; returns {exitCode, stderr}.
     */
    private static String[] runProductionCliCapturingErr(String[] args)
            throws IOException {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        int exitCode;
        try {
            System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
            exitCode = Main.run(args);
            System.err.flush();
        } finally {
            System.setErr(originalErr);
        }
        return new String[]{String.valueOf(exitCode),
            err.toString(StandardCharsets.UTF_8)};
    }

    /**
     * The production-invocation emitted-and-staged assertion of one
     * re-expressed gate fixture (ISSUE-0654/ISSUE-0656): the release-owned
     * {@link Main} compile exits 0, reports no emitter gap, and publishes
     * exactly one project artifact for the entry module (whose identity is
     * the generated private module id here, because the fixture entry is
     * not contained by a configured root), plus the unchanged LuaJIT
     * deployment copies — and no per-module sibling.
     *
     * @param args    the CLI arguments of the fixture
     * @param out     the fixture's fresh output directory
     * @param context the assertion context
     */
    private static void checkProductionEmits(String[] args, Path out,
            String context) throws IOException {
        String[] run = runProductionCliCapturingErr(args);
        check("0".equals(run[0]),
            context + ": the release-owned production invocation compiles"
                + " (exit " + run[0] + "): " + run[1]);
        check(!run[1].contains("E6005"),
            context + ": the production compile reports no emitter gap: "
                + run[1]);
        List<String> artifacts = artifactFilesUnder(out);
        long projectArtifacts = artifacts.stream()
            .filter(p -> LUA_MODULE_ID.matcher(p).matches()).count();
        check(projectArtifacts == 1,
            context + ": the production compile publishes exactly one project"
                + " artifact under " + out + ": " + artifacts);
        check(!artifacts.contains("pkg/util.lua"),
            context + ": the production compile publishes no per-module"
                + " sibling: " + artifacts);
    }

    /** Deletes a temp tree. */
    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) return;
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(f -> {
                    try {
                        Files.deleteIfExists(f);
                    } catch (IOException ignored) {
                    }
                });
        } catch (IOException ignored) {
        }
    }

    /** The root-relative artifact paths under a tree, sorted. */
    private static List<String> artifactFilesUnder(Path root) throws IOException {
        if (!Files.isDirectory(root)) return List.of();
        List<String> files = new ArrayList<>();
        try (var walk = Files.walk(root)) {
            walk.filter(Files::isRegularFile).sorted().forEach(p ->
                files.add(root.relativize(p).toString()
                    .replace(java.io.File.separatorChar, '/')));
        }
        return files;
    }

    /** One field of the canonical structured document (fixed field order). */
    private static String jsonField(String doc, String field) {
        Matcher m = Pattern.compile("\"" + field
                + "\": (\"(?:[^\"\\\\]|\\\\.)*\"|-?\\d+)")
            .matcher(doc);
        if (!m.find()) return null;
        String value = m.group(1);
        if (value.startsWith("\"")) {
            return value.substring(1, value.length() - 1);
        }
        return value;
    }

    /** Counts non-overlapping occurrences. */
    private static int countOccurrences(String haystack, String needle) {
        int count = 0;
        int idx = 0;
        while ((idx = haystack.indexOf(needle, idx)) >= 0) {
            count++;
            idx += needle.length();
        }
        return count;
    }

    /**
     * The formatted-vs-structured agreement check (the
     * ProjectIntegrationGatesTest helper): the formatter's stderr text
     * must carry the range header, code, message, and span length that
     * the structured document's complete range fields pin.
     */
    private static void checkFormattedStructuredAgree(String formatted,
                                                      String doc,
                                                      String context) {
        String file = jsonField(doc, "file");
        String code = jsonField(doc, "code");
        String message = jsonField(doc, "message");
        String startLine = jsonField(doc, "startLine");
        String startColumn = jsonField(doc, "startColumn");
        String endLine = jsonField(doc, "endLine");
        String endColumn = jsonField(doc, "endColumn");
        String scalarLength = jsonField(doc, "scalarLength");
        check(file != null && code != null && message != null
                && startLine != null && startColumn != null
                && endLine != null && endColumn != null
                && scalarLength != null,
            context + ": the structured document carries the complete"
                + " range fields");
        if (file == null) return;
        String header = file + ":" + startLine + ":" + startColumn + "-"
            + endLine + ":" + endColumn;
        check(formatted.contains(header),
            context + ": formatted output carries the structured range"
                + " header '" + header + "': " + formatted);
        check(formatted.contains("ERROR " + code),
            context + ": formatted output carries the structured code "
                + code + ": " + formatted);
        check(formatted.contains("[span " + scalarLength + "]"),
            context + ": formatted output carries the structured span"
                + " length " + scalarLength + ": " + formatted);
        String unescaped = message.replace("\\\"", "\"");
        check(formatted.contains(unescaped),
            context + ": formatted output carries the structured message: "
                + formatted);
    }

    /** SHA-256 hex (lowercase) of the file bytes. */
    private static String sha256(Path file) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(Files.readAllBytes(file));
            StringBuilder hex = new StringBuilder(hash.length * 2);
            for (byte b : hash) {
                hex.append(Character.forDigit((b >> 4) & 0xF, 16));
                hex.append(Character.forDigit(b & 0xF, 16));
            }
            return hex.toString();
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Relative path -> SHA-256 over every committed fixture-tree file. */
    private static Map<String, String> snapshotFixtureTree()
            throws IOException {
        Map<String, String> digests = new TreeMap<>();
        try (var walk = Files.walk(FIXTURES)) {
            walk.filter(Files::isRegularFile).sorted().forEach(p ->
                digests.put(FIXTURES.relativize(p).toString(), sha256(p)));
        }
        return digests;
    }

    /** Copies one fixture tree (scratch copies only). */
    private static Path copyTree(Path source, Path targetRoot)
            throws IOException {
        try (var walk = Files.walk(source)) {
            for (Path p : walk.sorted().toList()) {
                Path dest = targetRoot.resolve(source.relativize(p).toString());
                if (Files.isDirectory(p)) {
                    Files.createDirectories(dest);
                } else {
                    Files.createDirectories(dest.getParent());
                    Files.copy(p, dest);
                }
            }
        }
        return targetRoot;
    }

    // =========================================================================
    // G1. F1 declaration-cycle-two-modules: compile-ok — declaration import
    //     cycles compile; externals entries supply the declaration classes'
    //     public identity; exactly one private module artifact.
    // =========================================================================

    private static void gateDeclarationCycleTwoModules() throws Exception {
        System.out.println("-- G1: declaration-cycle-two-modules"
            + " (compile-ok) --");
        Path dir = F1_DIR;
        Path entry = dir.resolve("declaration-cycle-two-modules.deal");
        requireFixture(dir, "deal.json");
        requireFixture(dir, "declaration-cycle-two-modules.deal");
        requireFixture(dir, "support/decl_two_a.d.deal");
        requireFixture(dir, "support/decl_two_b.d.deal");
        Path base = Files.createTempDirectory("deal_fg1_");
        try {
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", out.toString()});
            check("0".equals(run[0]),
                "F1 compiles with exit 0: " + run[1]);
            check(!run[1].contains("ERROR"),
                "F1 emits no ERROR on stderr: " + run[1]);
            List<String> artifacts = artifactFilesUnder(out);
            long privateArtifacts = artifacts.stream()
                .filter(p -> LUA_MODULE_ID.matcher(p).matches()).count();
            check(privateArtifacts == 1,
                "F1 emits exactly one private module artifact"
                    + " (declaration modules emit no artifacts), got "
                    + privateArtifacts + ": " + artifacts);

            // ISSUE-0656: the release-owned production invocation
            // realizes the same two HOST-declaration-kind imports
            // through the host load of the module init walk, so the
            // production compile succeeds and publishes the entry
            // module's one project artifact (no per-module sibling).
            checkProductionEmits(new String[]{
                "compile", entry.toString(), "--output",
                base.resolve("prod_out").toString()},
                base.resolve("prod_out"),
                "F1 declaration-cycle fixture");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // G2. F2 runtime-cycle-class-default-three-modules: compile-error E2005 —
    //     exactly one E2005 with the three-module chain, the import-anchor
    //     range, and no output directory.
    // =========================================================================

    private static void gateRuntimeCycleClassDefaultThreeModules()
            throws Exception {
        System.out.println("-- G2: runtime-cycle-class-default-three-modules"
            + " (compile-error E2005) --");
        Path dir = F2_DIR;
        Path entry = dir.resolve(
            "runtime-cycle-class-default-three-modules.deal");
        requireFixture(dir, "deal.json");
        requireFixture(dir, "runtime-cycle-class-default-three-modules.deal");
        requireFixture(dir, "support/runtime_three_a.deal");
        requireFixture(dir, "support/runtime_three_b.deal");
        requireFixture(dir, "support/runtime_three_c.deal");
        Path base = Files.createTempDirectory("deal_fg2_");
        try {
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", out.toString()});
            check("1".equals(run[0]),
                "F2 exits 1 with the runtime cycle: " + run[1]);
            check(countOccurrences(run[1], "E2005") == 1,
                "F2 emits exactly one E2005: " + run[1]);
            check(run[1].contains("Circular import with runtime dependency:"),
                "F2 names the runtime-dependency cycle: " + run[1]);
            check(E2005_CHAIN.matcher(run[1]).find(),
                "F2 carries the three-module chain"
                    + " support/runtime_three_a.deal ->"
                    + " support/runtime_three_b.deal ->"
                    + " support/runtime_three_c.deal ->"
                    + " support/runtime_three_a.deal: " + run[1]);
            check(run[1].contains("runtime_three_a.deal:2:1-3:7"),
                "F2 anchors the first cycle module's import declaration"
                    + " (runtime_three_a.deal:2:1-3:7): " + run[1]);
            check(run[1].contains("[span 46]"),
                "F2 pins the import-anchor span 46: " + run[1]);
            check(run[1].contains("1 error(s), 0 warning(s)"),
                "F2 reports 1 error(s), 0 warning(s): " + run[1]);
            check(!Files.exists(out),
                "F2 creates no --output directory: " + out);
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // G3. F3 leading-import-type: compile-ok — the leading import in the
    //     declaration file provides the exported function parameter type.
    // =========================================================================

    private static void gateLeadingImportType() throws Exception {
        System.out.println("-- G3: leading-import-type (compile-ok) --");
        Path dir = F3_DIR;
        Path entry = dir.resolve("leading-import-type.deal");
        requireFixture(dir, "deal.json");
        requireFixture(dir, "leading-import-type.deal");
        requireFixture(dir, "support/importing_declaration.d.deal");
        requireFixture(dir, "support/model.d.deal");
        Path base = Files.createTempDirectory("deal_fg3_");
        try {
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", out.toString()});
            check("0".equals(run[0]),
                "F3 compiles with exit 0: " + run[1]);
            check(!run[1].contains("ERROR"),
                "F3 emits no ERROR on stderr: " + run[1]);
            List<String> artifacts = artifactFilesUnder(out);
            long privateArtifacts = artifacts.stream()
                .filter(p -> LUA_MODULE_ID.matcher(p).matches()).count();
            check(privateArtifacts == 1,
                "F3 emits exactly one private module artifact, got "
                    + privateArtifacts + ": " + artifacts);

            // ISSUE-0656: the release-owned production invocation
            // realizes the same HOST-declaration-kind import through the
            // host load of the module init walk, so the production
            // compile succeeds and publishes the entry module's one
            // project artifact.
            checkProductionEmits(new String[]{
                "compile", entry.toString(), "--output",
                base.resolve("prod_out").toString()},
                base.resolve("prod_out"),
                "F3 leading-import-type fixture");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // G4. F4 module-roots-bare-import: compile-ok — the bare pkg/util import
    //     resolves under moduleRoots: ["src"]; negative control: an empty
    //     moduleRoots list emits E2003.
    // =========================================================================

    private static void gateModuleRootsBareImport() throws Exception {
        System.out.println("-- G4: module-roots-bare-import (compile-ok) --");
        Path dir = F4_DIR;
        Path entry = dir.resolve("main.deal");
        requireFixture(dir, "deal.json");
        requireFixture(dir, "main.deal");
        requireFixture(dir, "src/pkg/util.deal");
        Path base = Files.createTempDirectory("deal_fg4_");
        try {
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", out.toString()});
            check("0".equals(run[0]),
                "F4 compiles with exit 0: " + run[1]);
            check(!run[1].contains("ERROR"),
                "F4 emits no ERROR on stderr: " + run[1]);
            List<String> artifacts = artifactFilesUnder(out);
            check(artifacts.contains("pkg/util.lua"),
                "F4 emits the bare-import module artifact pkg/util.lua: "
                    + artifacts);
            long privateArtifacts = artifacts.stream()
                .filter(p -> LUA_MODULE_ID.matcher(p).matches()).count();
            check(privateArtifacts == 1,
                "F4 emits exactly one private module artifact, got "
                    + privateArtifacts + ": " + artifacts);

            // ISSUE-0654: the release-owned production invocation realizes
            // the same cross-module call (Util.value()) through the callee
            // unit's EXTERNAL_ENTRY inside the one project artifact, so the
            // production compile succeeds and publishes the entry module's
            // one project artifact.
            checkProductionEmits(new String[]{
                "compile", entry.toString(), "--output",
                base.resolve("prod_out").toString()},
                base.resolve("prod_out"),
                "F4 module-roots-bare-import fixture");

            // Negative control (scratch copy only): moduleRoots: [] —
            // the bare import no longer resolves, E2003 flips the gate.
            String committed = Files.readString(dir.resolve("deal.json"));
            check(committed.contains("\"moduleRoots\": [\"src\"]"),
                "F4 negative control precondition: the committed deal.json"
                    + " carries moduleRoots [\"src\"]: " + committed);
            Path scratch = copyTree(dir, base.resolve("scratch"));
            Files.writeString(scratch.resolve("deal.json"),
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": []\n}\n");
            Path scratchOut = base.resolve("scratch_out");
            String[] negative = runCliCapturingErr(new String[]{
                "compile", scratch.resolve("main.deal").toString(),
                "--output", scratchOut.toString()});
            check("1".equals(negative[0]),
                "F4 negative control (moduleRoots []) exits 1: "
                    + negative[1]);
            check(negative[1].contains("E2003")
                    && negative[1].contains("Module not found: 'pkg/util'"),
                "F4 negative control (moduleRoots []) emits E2003"
                    + " Module not found: 'pkg/util': " + negative[1]);
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // G5. F5 c-ffi-native-library-required: locate failure with the exact
    //     landed E2010 (pin-at-landing, D8); negative control: nativeLibrary
    //     added -> locate succeeds.
    // =========================================================================

    private static void gateCffiNativeLibraryRequired() throws Exception {
        System.out.println("-- G5: c-ffi-native-library-required"
            + " (locate failure, landed E2010) --");
        Path dir = F5_DIR;
        Path entry = dir.resolve("main.deal");
        requireFixture(dir, "deal.json");
        requireFixture(dir, "main.deal");
        requireFixture(dir, "bindings/host-math.d.deal");
        String committed = Files.readString(dir.resolve("deal.json"));
        check(!committed.contains("nativeLibrary"),
            "F5 precondition: the committed deal.json carries no"
                + " nativeLibrary member: " + committed);
        Path base = Files.createTempDirectory("deal_fg5_");
        try {
            // (a) The direct locate contract: exactly one E2010, no
            // cliDiagnostic, no published context.
            ProjectLocator.LocateResult located =
                ProjectLocator.locate(entry.toString(), null);
            check(located.e2010() != null,
                "F5 locate publishes an E2010");
            check(located.cliDiagnostic() == null && located.context() == null,
                "F5 locate publishes exactly the E2010 (no cliDiagnostic,"
                    + " no context)");
            if (located.e2010() != null) {
                check("E2010".equals(located.e2010().code()),
                    "F5 locate code is exactly E2010: "
                        + located.e2010().code());
                check(F5_PIN_MESSAGE.equals(located.e2010().message()),
                    "F5 locate message is the verbatim landed message: "
                        + located.e2010().message());
            }

            // (b) The CLI surfaces the verbatim formatted diagnostic and
            // exits 1.
            String[] cli = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(cli[0]),
                "F5 CLI exits 1: " + cli[1]);
            check(cli[1].contains(F5_PIN_LINE_SUFFIX),
                "F5 CLI prints the verbatim landed E2010 line (range"
                    + " header, code, message, span): " + cli[1]);
            check(countOccurrences(cli[1], "ERROR E2010") == 1,
                "F5 CLI prints exactly one ERROR E2010 line: " + cli[1]);
            check(!cli[1].contains("warning(s)"),
                "F5 CLI prints zero warnings: " + cli[1]);
            check(!Files.exists(dir.resolve("build")),
                "no artifact directory exists inside the F5 fixture"
                    + " tree after the run");

            // (c) The structured --diagnostics-json document is
            // field-exact to ProjectLocator's own diagnostic (the
            // field-exact precedent).
            Path json = base.resolve("diag.json");
            String[] jsonRun = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                json.toString()});
            check("1".equals(jsonRun[0]),
                "F5 --diagnostics-json run exits 1: " + jsonRun[1]);
            String doc = Files.readString(json);
            if (located.e2010() != null) {
                check(doc.equals(DiagnosticStructuredOutput.toJson(
                        List.of(located.e2010()))),
                    "the structured F5 document is field-exact to"
                        + " ProjectLocator's own diagnostic: " + doc);
            }
            check("E2010".equals(jsonField(doc, "code"))
                    && "error".equals(jsonField(doc, "severity"))
                    && "4".equals(jsonField(doc, "startLine"))
                    && "18".equals(jsonField(doc, "startColumn"))
                    && "6".equals(jsonField(doc, "endLine"))
                    && "6".equals(jsonField(doc, "endColumn"))
                    && "56".equals(jsonField(doc, "scalarLength"))
                    && "SOURCE".equals(jsonField(doc, "origin")),
                "the structured F5 document pins the externals entry"
                    + " range (deal.json:4:18-6:6, span 56, SOURCE): "
                    + doc);
            checkFormattedStructuredAgree(jsonRun[1], doc, "F5 locate");

            // (d) Negative control (scratch copy only): adding
            // "nativeLibrary": "hostmath" makes locate succeed.
            Path scratch = copyTree(dir, base.resolve("scratch"));
            Files.writeString(scratch.resolve("deal.json"),
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"externals\": {\n"
                    + "    \"host/math\": {\n"
                    + "      \"declaration\": \"bindings/host-math.d.deal\",\n"
                    + "      \"nativeLibrary\": \"hostmath\"\n"
                    + "    }\n"
                    + "  }\n"
                    + "}\n");
            ProjectLocator.LocateResult negative = ProjectLocator.locate(
                scratch.resolve("main.deal").toString(), null);
            check(negative.context() != null
                    && negative.e2010() == null
                    && negative.cliDiagnostic() == null,
                "F5 negative control (nativeLibrary added) locates"
                    + " successfully");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate-authoring perturbations (Verification 4, scratch copies only).
    // =========================================================================

    /** F1 without externals -> E2010 (two no-public-identity errors). */
    private static void perturbationDeclarationCycleNoExternals()
            throws Exception {
        System.out.println("-- Perturbation: declaration-cycle-two-modules"
            + " without externals -> E2010 --");
        Path dir = F1_DIR;
        String committed = Files.readString(dir.resolve("deal.json"));
        check(committed.contains("\"externals\""),
            "F1 perturbation precondition: the committed deal.json"
                + " carries externals entries: " + committed);
        Path base = Files.createTempDirectory("deal_fg1p_");
        try {
            Path scratch = copyTree(dir, base.resolve("scratch"));
            Files.writeString(scratch.resolve("deal.json"),
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile",
                scratch.resolve("declaration-cycle-two-modules.deal")
                    .toString(),
                "--output", out.toString()});
            check("1".equals(run[0]),
                "F1 perturbation (no externals) exits 1: " + run[1]);
            check(countOccurrences(run[1], "E2010") == 2
                    && run[1].contains("no public module identity"),
                "F1 perturbation (no externals) emits two E2010"
                    + " no-public-module-identity errors: " + run[1]);
        } finally {
            deleteRecursively(base);
        }
    }

    /**
     * F2 with the class-field default B.get(1) -> 1: the default edge
     * disappears, but runtime_three_b's function body still calls
     * C.get, so the cycle stays a runtime SCC through the ordinary
     * edge alone (ISSUE-0543 merged ordinary + default edges,
     * provider-versioned-default-plans D7(a): function bodies count)
     * — E2005 again, now with the RUNTIME_USE edge note.
     */
    private static void perturbationRuntimeCycleOrdinaryOnly()
            throws Exception {
        System.out.println("-- Perturbation: runtime cycle with the"
            + " class-field default replaced by 1 -> E2005 through the"
            + " ordinary edge alone --");
        Path dir = F2_DIR;
        Path support = dir.resolve("support/runtime_three_a.deal");
        String committed = Files.readString(support);
        check(committed.contains("B.get(1)"),
            "F2 perturbation precondition: the committed"
                + " support/runtime_three_a.deal carries the class-field"
                + " default B.get(1): " + support);
        Path base = Files.createTempDirectory("deal_fg2p_");
        try {
            Path scratch = copyTree(dir, base.resolve("scratch"));
            Path perturbed = scratch.resolve("support/runtime_three_a.deal");
            String replaced = Files.readString(perturbed)
                .replace("B.get(1)", "1");
            check(replaced.contains("seed: int = 1")
                    && !replaced.contains("B.get(1)"),
                "F2 perturbation actually replaced the class-field"
                    + " default: " + replaced);
            Files.writeString(perturbed, replaced);
            Path out = base.resolve("out");
            String[] run = runCliCapturingErr(new String[]{
                "compile",
                scratch.resolve(
                    "runtime-cycle-class-default-three-modules.deal")
                    .toString(),
                "--output", out.toString()});
            check("1".equals(run[0]),
                "F2 perturbation (ordinary-edge cycle) exits 1: "
                    + run[1]);
            check(countOccurrences(run[1], "E2005") == 1,
                "F2 perturbation emits exactly one E2005: " + run[1]);
            check(run[1].contains("runtime edge RUNTIME_USE"),
                "F2 perturbation's E2005 notes the ordinary runtime"
                    + " edge (RUNTIME_USE): " + run[1]);
            check(run[1].contains("runtime_three_b.deal -> ")
                    && run[1].contains("runtime_three_c.deal"),
                "F2 perturbation's note names the ordinary edge"
                    + " runtime_three_b -> runtime_three_c: " + run[1]);
            check(run[1].contains("1 error(s), 0 warning(s)"),
                "F2 perturbation reports 1 error(s), 0 warning(s): "
                    + run[1]);
            check(!Files.exists(out),
                "F2 perturbation creates no --output directory: " + out);
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Production Project-Graph Fixture Gates"
            + " (ISSUE-0506 D11) ===\n");

        check(Files.isDirectory(FIXTURES),
            "missing fixture tree: " + FIXTURES);
        Map<String, String> before = snapshotFixtureTree();

        gateDeclarationCycleTwoModules();
        gateRuntimeCycleClassDefaultThreeModules();
        gateLeadingImportType();
        gateModuleRootsBareImport();
        gateCffiNativeLibraryRequired();
        perturbationDeclarationCycleNoExternals();
        perturbationRuntimeCycleOrdinaryOnly();

        Map<String, String> after = snapshotFixtureTree();
        check(before.equals(after),
            "the committed fixture trees are byte-identical after every"
                + " gate run" + (before.equals(after) ? ""
                : "; changed: " + changedKeys(before, after)));

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }

    /** The first differing snapshot keys (diagnostic detail only). */
    private static String changedKeys(Map<String, String> before,
                                      Map<String, String> after) {
        List<String> changed = new ArrayList<>();
        for (String key : before.keySet()) {
            if (!before.get(key).equals(after.get(key))) {
                changed.add(key);
            }
        }
        for (String key : after.keySet()) {
            if (!before.containsKey(key)) {
                changed.add(key + " (new)");
            }
        }
        return changed.toString();
    }
}
