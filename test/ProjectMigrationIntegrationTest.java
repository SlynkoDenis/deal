package deal.test;

import deal.Main;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.project.ProjectLocator;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * ISSUE-0269 migration integration gate (design source
 * {@code strict-project-context-resolution-identity} D7 + Failure and
 * operations, verification "Combined (dependencies T4-T7)"):
 * real CLI runs over temporary exact-v1.2 deployments prove the one
 * destructive v1.2 migration unit — the registry re-registration,
 * {@code deal.Main} consuming {@code ProjectLocator}, the orchestrator
 * consuming {@code ProjectContext} + {@code SourceModuleResolver} +
 * {@code ModuleIdentityAssembly}, the re-rooted stdlib surface, the
 * retired {@code DealConfig}/implicit-root/CWD-fallback/computeModulePath
 * surfaces, and the conformance harness routing.
 *
 * <p>Every scenario runs the real production CLI
 * ({@link Main#run(String[])}) or a real {@code deal.Main} subprocess
 * over a temp deployment — never type-level wiring checks alone.</p>
 */
public class ProjectMigrationIntegrationTest {

    private static int passed = 0;
    private static int failed = 0;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    /** Writes one fixture file and returns its absolute path. */
    private static Path write(Path root, String rel, String content)
            throws IOException {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file.toAbsolutePath();
    }

    /**
     * Runs the release-owned production CLI with System.err captured;
     * returns {exitCode, stderr}.
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
     * Runs the same CLI-equivalent arguments through the test-scope
     * harness compile entry ({@link HarnessCompileEntry}; ISSUE-0643 P10
     * item 3, mechanism 1) with System.err captured; returns {exitCode,
     * stderr}. The suite drives the harness arm so its subject — the
     * locator/resolution/identity stack — stays arm-independent, and
     * ISSUE-0654 realizes this suite's cross-module call on the
     * release-owned production invocation as well.
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

    /** Deletes a temp tree. */
    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) return;
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(f -> { try { Files.deleteIfExists(f); }
                    catch (IOException ignored) { } });
        } catch (IOException ignored) { }
    }

    // =========================================================================
    // 1. One ancestor manifest governs the graph; the project runs on
    //    LuaJIT and JVM through the new locator/resolution/identity stack.
    // =========================================================================

    private static void testSingleManifestProjectRunsBothBackends()
            throws Exception {
        System.out.println("-- Single-manifest project: class-free out-of-root "
            + "shared module runs on LuaJIT and JVM --");

        Path root = Files.createTempDirectory("deal_mig_single_");
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            // The shared module lives outside every configured root and
            // outside the manifest directory's rooted sources: an
            // importer-relative ../ import that stays class-free.
            write(root, "shared.deal",
                "export function greet(): string { return \"OK\"; }\n"
                    + "export function add(a: int, b: int): int { return a + b; }\n");
            write(root, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as shared from \"../shared\"\n"
                    + "export function main(): null {\n"
                    + "  console.log(shared.greet());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = root.resolve("src/main.deal").toAbsolutePath();

            // LuaJIT through the production CLI.
            String[] luaRun = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(luaRun[0]),
                "the single-manifest project compiles (LuaJIT): " + luaRun[1]);
            Path luaArtifact = root.resolve("build/lua/main.lua");
            check(Files.exists(luaArtifact),
                "the LuaJIT artifact is emitted under the manifest-derived output");
            if (Files.exists(luaArtifact)) {
                // Run from the output directory so the emitted require
                // paths resolve against the deployed artifact set (the
                // runtime copy and the class-free shared module's
                // deploymentModuleId-named artifact).
                ProcessBuilder pb = new ProcessBuilder("luajit",
                    "main.lua");
                pb.directory(luaArtifact.getParent().toFile());
                pb.redirectErrorStream(true);
                Process p = pb.start();
                String out = new String(p.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                check(p.waitFor() == 0 && out.contains("OK"),
                    "the class-free out-of-root shared module runs under"
                        + " LuaJIT: " + out);
            }

            // JVM through the production CLI (CLI backend alias).
            Path jvmOut = root.resolve("out_jvm");
            String[] jvmRun = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvmRun[0]),
                "the same project compiles with --backend jvm: " + jvmRun[1]);
            Path jvmArtifact = jvmOut.resolve("Main.java");
            check(Files.exists(jvmArtifact),
                "the JVM artifact is emitted under the CLI output override");
            if (Files.exists(jvmArtifact)) {
                ProcessBuilder javac = new ProcessBuilder("javac",
                    "-encoding", "UTF-8", "Main.java");
                javac.directory(jvmOut.toFile());
                javac.redirectErrorStream(true);
                Process p = javac.start();
                String javacOut = new String(
                    p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
                check(p.waitFor() == 0, "the JVM artifact compiles with javac: "
                    + javacOut);
                ProcessBuilder javaRun = new ProcessBuilder("java", "-cp",
                    jvmOut.toString(), "Main");
                javaRun.redirectErrorStream(true);
                Process p2 = javaRun.start();
                String out = new String(p2.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                check(p2.waitFor() == 0 && out.contains("OK"),
                    "the class-free out-of-root shared module runs under"
                        + " JVM: " + out);
            }

            // ISSUE-0654: the release-owned production invocation realizes
            // this suite's cross-module-call fixture — the shared.greet()
            // call runs the callee unit's EXTERNAL_ENTRY inside the one
            // project artifact — so the production compile succeeds, emits
            // one project artifact, and publishes it, while the harness
            // invocation above keeps the locator/resolution/identity
            // subject green.
            Path prodOut = root.resolve("out_prod_probe");
            String[] prod = runProductionCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", prodOut.toString()});
            check("0".equals(prod[0]),
                "the release-owned production invocation compiles the"
                    + " cross-module call: " + prod[1]);
            check(!prod[1].contains("E6005"),
                "the production compile reports no emitter gap: " + prod[1]);
            check(Files.exists(prodOut.resolve("main.lua")),
                "the production compile publishes its one project artifact "
                    + "under " + prodOut);
            if (Files.exists(prodOut.resolve("main.lua"))) {
                ProcessBuilder prodBuilder = new ProcessBuilder("luajit",
                    "main.lua");
                prodBuilder.directory(prodOut.toFile());
                prodBuilder.redirectErrorStream(true);
                Process prodProcess = prodBuilder.start();
                String prodOutput = new String(
                    prodProcess.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                check(prodProcess.waitFor() == 0 && prodOutput.equals("OK"),
                    "the production cross-module call executes under LuaJIT: "
                        + prodOutput);
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 2. An out-of-root class is E2010 at the class name span with no
    //    class metadata/artifact.
    // =========================================================================

    private static void testOutOfRootClassIsE2010() throws Exception {
        System.out.println("-- Out-of-root class: E2010 at the class name span, "
            + "no artifact --");

        Path root = Files.createTempDirectory("deal_mig_outclass_");
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(root, "shared.deal",
                "export function add(a: int, b: int): int { return a + b; }\n"
                    + "\n"
                    + "export class Point { x: int = 0; }\n");
            write(root, "src/main.deal",
                "import * as shared from \"../shared\"\n"
                    + "export function main(): null {\n"
                    + "  let p: shared.Point = { x: 1 };\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = root.resolve("src/main.deal").toAbsolutePath();

            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(run[0]),
                "the out-of-root class attempt exits 1");
            check(run[1].contains("E2010")
                    && run[1].contains("Class 'Point'")
                    && run[1].contains("no public module identity"),
                "the out-of-root class is E2010 at the class name span through"
                    + " the canonical formatter: " + run[1]);
            check(run[1].contains("shared.deal:3:8")
                    && run[1].contains("[span "),
                "the E2010 carries the complete SOURCE class-name range"
                    + " (shared.deal:3:8): " + run[1]);
            check(!Files.exists(root.resolve("build/lua/main.lua"))
                    && !Files.exists(root.resolve("build/lua/shared.lua")),
                "no class metadata/artifact is published for the rejected"
                    + " out-of-root class");
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 2.5. A non-exported class whose public identity is unrepresentable
    //      is E2010 at the class name span before any artifact — never a
    //      backend-dependent raw descriptor-emission exception.
    // =========================================================================

    private static void testNonExportedClassUnrepresentableIdentityIsE2010()
            throws Exception {
        System.out.println("-- Non-exported class, unrepresentable identity: "
            + "E2010 at the class name span, no raw exception --");

        // (a) Reserved-first-component configured root ($external): the
        // public class identity of a non-exported class is required like
        // any exported class's, so the unrepresentable root fails E2010
        // in phase 1 instead of crashing the LuaJIT class-tag emission
        // (the pre-fix behavior: raw IllegalStateException, exit 2).
        Path reserved = Files.createTempDirectory("deal_mig_reserved_");
        try {
            write(reserved, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"$external\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(reserved, "$external/main.deal",
                "class C { x: int = 1; }\n"
                    + "export function main(): null { return null; }\n");
            Path entry = reserved.resolve("$external/main.deal")
                .toAbsolutePath();

            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(run[0]),
                "the non-exported class under a reserved root exits 1 (never"
                    + " the raw exit 2): " + run[1]);
            check(run[1].contains("E2010")
                    && run[1].contains("Class 'C'")
                    && run[1].contains("not representable"),
                "the non-exported class under a reserved root is E2010 at the"
                    + " class name span: " + run[1]);
            check(run[1].contains("main.deal:1:1")
                    && run[1].contains("[span "),
                "the E2010 carries the complete SOURCE class-name range"
                    + " (main.deal:1:1): " + run[1]);
            check(!run[1].contains("Exception")
                    && !run[1].contains("\tat ")
                    && !run[1].contains("deal: internal error"),
                "no raw exception escapes the reserved-root class path: "
                    + run[1]);
            check(!Files.exists(reserved.resolve("build/lua/main.lua")),
                "no artifact is published for the rejected non-exported"
                    + " class");

            // (b) Exported control: the identical exported class pins the
            // same E2010 surface at the class declaration span (1:8).
            write(reserved, "$external/exported.deal",
                "export class C { x: int = 1; }\n"
                    + "export function main(): null { return null; }\n");
            String[] exportedRun = runCliCapturingErr(new String[]{
                "compile", reserved.resolve("$external/exported.deal")
                    .toAbsolutePath().toString()});
            check("1".equals(exportedRun[0])
                    && exportedRun[1].contains("E2010")
                    && exportedRun[1].contains("exported.deal:1:8"),
                "the exported variant keeps the pinned E2010 at the class"
                    + " declaration span (exported.deal:1:8): "
                    + exportedRun[1]);

            // (c) Class-free control: class-free code under the same
            // unrepresentable root stays valid (unrepresentable identity
            // invalidates no class-free module).
            write(reserved, "$external/free.deal",
                "export function main(): null { return null; }\n");
            String[] freeRun = runCliCapturingErr(new String[]{
                "compile", reserved.resolve("$external/free.deal")
                    .toAbsolutePath().toString()});
            check("0".equals(freeRun[0]),
                "class-free code under the unrepresentable root still"
                    + " compiles: " + freeRun[1]);
        } finally {
            deleteRecursively(reserved);
        }

        // (d) Forbidden relative component (contiguous '->' in a source
        // directory): the same gate fires for the non-exported class
        // before any artifact.
        Path arrow = Files.createTempDirectory("deal_mig_arrow_");
        try {
            write(arrow, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(arrow, "src/sub->dir/main.deal",
                "class D { x: int = 1; }\n"
                    + "export function main(): null { return null; }\n");
            Path entry = arrow.resolve("src/sub->dir/main.deal")
                .toAbsolutePath();

            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(run[0]),
                "the non-exported class under a '->'-bearing directory exits"
                    + " 1 (never the raw exit 2): " + run[1]);
            check(run[1].contains("E2010")
                    && run[1].contains("Class 'D'")
                    && run[1].contains("'sub->dir'")
                    && run[1].contains("not representable"),
                "the '->' relative component is E2010 at the class name span: "
                    + run[1]);
            check(run[1].contains("main.deal:1:1")
                    && run[1].contains("[span "),
                "the E2010 carries the complete SOURCE class-name range"
                    + " (main.deal:1:1): " + run[1]);
            check(!run[1].contains("Exception")
                    && !run[1].contains("\tat ")
                    && !run[1].contains("deal: internal error"),
                "no raw exception escapes the '->'-component class path: "
                    + run[1]);
            check(!Files.exists(arrow.resolve("build/lua/main.lua")),
                "no artifact is published for the rejected '->'-component"
                    + " class");
        } finally {
            deleteRecursively(arrow);
        }
    }

    // =========================================================================
    // 3. Zero/two ancestor manifests: one E2010 with the pinned synthetic
    //    range and candidate notes; --diagnostics-json carries the range.
    // =========================================================================

    private static void testAncestorManifestDiscovery() throws Exception {
        System.out.println("-- Ancestor-manifest discovery: zero/two manifests --");

        Path root = Files.createTempDirectory("deal_mig_disc_");
        try {
            // Zero manifests.
            Path noManifest = write(root, "no_man/main.deal",
                "export function main(): null { return null; }\n");
            String[] zero = runCliCapturingErr(new String[]{
                "compile", noManifest.toString()});
            check("1".equals(zero[0]), "zero-manifest compile exits 1");
            check(zero[1].contains("E2010") && zero[1].contains("no deal.json"),
                "zero manifests is one E2010 with the v1.2-manifest note: "
                    + zero[1]);
            check(zero[1].contains("no_man/main.deal:1:1-1:1")
                    && zero[1].contains("[span 0]"),
                "the discovery E2010 carries the pinned synthetic range"
                    + " (entry,1,1,1,1,0,0,0): " + zero[1]);

            // Two manifests: the walk reports every candidate.
            write(root, "two/deal.json",
                "{\"languageVersion\": \"1.2\"}\n");
            write(root, "two/nested/deal.json",
                "{\"languageVersion\": \"1.2\"}\n");
            Path twoEntry = write(root, "two/nested/main.deal",
                "export function main(): null { return null; }\n");
            String[] two = runCliCapturingErr(new String[]{
                "compile", twoEntry.toString()});
            check("1".equals(two[0]), "two-manifest compile exits 1");
            check(two[1].contains("E2010")
                    && two[1].contains("multiple deal.json"),
                "two manifests is one E2010: " + two[1]);
            check(two[1].contains("candidate manifest: ") && two[1].contains("nested"),
                "candidate notes name every candidate manifest: " + two[1]);

            // --diagnostics-json carries the full range of the same
            // discovery E2010, field-exact to ProjectLocator's own
            // diagnostic.
            Path outJson = root.resolve("disc.json");
            String[] zeroJson = runCliCapturingErr(new String[]{
                "compile", noManifest.toString(),
                "--diagnostics-json", outJson.toString()});
            check("1".equals(zeroJson[0]), "zero-manifest with --diagnostics-json exits 1");
            ProjectLocator.LocateResult expected = ProjectLocator.locate(
                noManifest.toString(), null);
            check(expected.e2010() != null,
                "the zero-manifest deployment fails the strict locator");
            String written = Files.readString(outJson);
            String expectedJson = DiagnosticStructuredOutput.toJson(
                List.of(expected.e2010()));
            check(written.equals(expectedJson),
                "the structured document is field-exact (full synthetic range"
                    + " included):\n" + written);
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 4. A malformed manifest fails E2010 before any override is consulted.
    // =========================================================================

    private static void testMalformedManifestBeforeOverride() throws Exception {
        System.out.println("-- Malformed manifests: E2010 before any override --");

        Path root = Files.createTempDirectory("deal_mig_badman_");
        try {
            for (String bad : new String[]{
                    "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\","
                        + " \"backend\": \"jvm\"}",
                    "{\"languageVersion\": \"1.1\"}",
                    "{\"languageVersion\": \"1.2\", \"permissions\": []}"}) {
                String name = "bad_" + Math.abs(bad.hashCode());
                Path entry = write(root, name + "/main.deal",
                    "export function main(): null { return null; }\n");
                write(root, name + "/deal.json", bad);
                String[] run = runCliCapturingErr(new String[]{
                    "compile", entry.toString(),
                    "--backend", "jvm",
                    "--output", root.resolve(name + "/out").toString()});
                check("1".equals(run[0]), "malformed manifest exits 1: " + bad);
                check(run[1].contains("E2010"),
                    "the malformed manifest is E2010 and the CLI overrides are"
                        + " never consulted (no CliDiagnostic, no override"
                        + " effect): " + run[1]);
                check(!Files.exists(root.resolve(name).resolve("out")),
                    "no output directory or artifact exists for the rejected"
                        + " manifest");
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 5. Malformed CLI overrides are CliDiagnostics; valid overrides win.
    // =========================================================================

    private static void testCliOverrides() throws Exception {
        System.out.println("-- CLI overrides: CliDiagnostics and precedence --");

        Path root = Files.createTempDirectory("deal_mig_cli_");
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"backend\": \"jvm\"\n}\n");
            Path entry = write(root, "src/main.deal",
                "export function main(): null { return null; }\n");

            // Whitespace-only output override: CliDiagnostic, exit 1,
            // never E2010, no directory.
            String[] emptyOut = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", "   "});
            check("1".equals(emptyOut[0]),
                "a whitespace-only output override exits 1");
            check(emptyOut[1].contains("output override")
                    && !emptyOut[1].contains("E2010"),
                "the whitespace-only override is a CliDiagnostic, never E2010: "
                    + emptyOut[1]);

            // Invalid backend alias: CliDiagnostic naming the aliases.
            String[] badAlias = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "wasm"});
            check("1".equals(badAlias[0]), "an invalid backend alias exits 1");
            check(badAlias[1].contains("unknown backend alias 'wasm'")
                    && badAlias[1].contains("lua, luajit, jvm, js"),
                "the invalid alias is a CliDiagnostic naming the supported"
                    + " aliases: " + badAlias[1]);

            // Valid alias overrides the manifest backend (jvm → lua alias).
            Path luaOut = root.resolve("cli_lua_out");
            String[] aliasRun = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "lua",
                "--output", luaOut.toString()});
            check("0".equals(aliasRun[0]),
                "the valid lua alias overrides the manifest backend: " + aliasRun[1]);
            check(Files.exists(luaOut.resolve("main.lua")),
                "the alias-selected LuaJIT backend emits the .lua artifact"
                    + " under the CLI output override");
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 6. Post-validation write failure: a deterministic compiler I/O
    //    diagnostic (exit 1), never E2010, never a raw exception.
    // =========================================================================

    private static void testPostValidationWriteFailure() throws Exception {
        System.out.println("-- Post-validation write failure: deterministic "
            + "I/O diagnostic --");

        Path root = Files.createTempDirectory("deal_mig_io_");
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            Path entry = write(root, "src/main.deal",
                "export function main(): null { return null; }\n");

            // A not-yet-existing output whose parent is a non-writable
            // filesystem location: the conversion succeeds (existence is
            // never required) and the write phase fails. Under the
            // transactional publication contract
            // (whole-project-artifact-publication D4) the write-phase
            // failure is a staging failure, reported as the pinned
            // deterministic compiler I/O diagnostic.
            Path procOut = Path.of("/proc").resolve(
                "deal_mig_out_" + ProcessHandle.current().pid());
            if (!Files.isDirectory(Path.of("/proc"))) {
                System.out.println("  SKIP: /proc absent — cannot stage a"
                    + " deterministic write failure");
                return;
            }
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", procOut.toString()});
            check("1".equals(run[0]), "the write failure exits 1");
            check(run[1].contains("deal: cannot publish artifacts to '"),
                "the write failure is the pinned deterministic compiler "
                    + "I/O diagnostic (staging failure, D4): " + run[1]);
            check(!run[1].contains("E2010"),
                "the write failure is never an E2010: " + run[1]);
            check(!run[1].contains("Exception") && !run[1].contains("\tat "),
                "no raw exception or stack trace escapes: " + run[1]);
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 7. Stdlib surface: project-local std/ first, then the distribution
    //    surface; a missing surface is E2003 at the import span.
    // =========================================================================

    private static void testStdlibSurfaceResolution() throws Exception {
        System.out.println("-- Stdlib surface resolution --");

        Path root = Files.createTempDirectory("deal_mig_std_");
        try {
            // Project-local surface wins: a project-local std/console with
            // a marker export the distribution surface does not carry.
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(root, "std/console.d.deal",
                "export function log(s: string): null;\n"
                    + "export function localMarker(): string;\n");
            write(root, "std/console.lua",
                "local __rt = require(\"deal.runtime\")\n"
                    + "local m = {}\n"
                    + "m.log = __rt.function_(\"(string)->null\", function(s)"
                    + " print(s) end)\n"
                    + "m.localMarker = __rt.function_(\"()->string\", function()"
                    + " return \"local\" end)\n"
                    + "return m\n");
            Path entry = write(root, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "export function main(): null {\n"
                    + "  console.log(console.localMarker());\n"
                    + "  return null;\n"
                    + "}\n");
            String[] local = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(local[0]),
                "the project-local std surface resolves and types: " + local[1]);
            check(Files.exists(root.resolve("build/lua/std/console.lua")),
                "the project-local std implementation is deployed from the"
                    + " pinned surface");

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation fails this fixture closed with E6005
            // CONSTRUCT_UNLOWERED (the unrecognized stdlib member call is
            // a later-slice construct) and stages nothing, while the
            // harness invocation above keeps the stdlib-surface resolution
            // subject green.
            Path prodOut = root.resolve("out_prod_probe");
            String[] prod = runProductionCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", prodOut.toString()});
            check(!"0".equals(prod[0]),
                "the release-owned production invocation fails the"
                    + " project-local stdlib fixture closed: " + prod[1]);
            check(prod[1].contains("E6005")
                    && prod[1].contains("CONSTRUCT_UNLOWERED"),
                "the production failure names E6005 CONSTRUCT_UNLOWERED: "
                    + prod[1]);
            check(!Files.exists(prodOut),
                "the production failure stages nothing under " + prodOut);

            // Missing surface: a subprocess whose working directory has no
            // std/ and whose project has no local std/ — the import is
            // E2003 at the import span, never a RuntimeException.
            Path bare = Files.createTempDirectory("deal_mig_nostd_");
            try {
                write(bare, "deal.json",
                    "{\n  \"languageVersion\": \"1.2\",\n"
                        + "  \"moduleRoots\": [\"src\"],\n"
                        + "  \"backend\": \"luajit\"\n}\n");
                write(bare, "src/main.deal",
                    "import * as console from \"std/console\"\n"
                        + "export function main(): null { return null; }\n");
                String buildCp = Path.of("build").toAbsolutePath().toString();
                ProcessBuilder pb = new ProcessBuilder("java", "-cp", buildCp,
                    "deal.Main", "compile", "src/main.deal");
                pb.directory(bare.toFile());
                pb.redirectErrorStream(true);
                Process p = pb.start();
                String out = new String(p.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8);
                int exit = p.waitFor();
                check(exit == 1, "the missing-surface stdlib import exits 1");
                check(out.contains("E2003") && out.contains("stdlib surface is absent"),
                    "a missing surface is E2003 at the import span (never a"
                        + " RuntimeException): " + out);
                check(!out.contains("Exception") && !out.contains("\tat "),
                    "no raw exception escapes the missing-surface path: " + out);
            } finally {
                deleteRecursively(bare);
            }
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // 8. Source-level retirement assertions: no production path constructs
    //    DealConfig, appends the implicit entry-directory root, uses the
    //    CWD bare-lookup fallback, or emits the lossy computeModulePath.
    // =========================================================================

    private static void testProductionSourceRetirement() throws Exception {
        System.out.println("-- Production-source retirement scans --");

        Path dealDir = Path.of("deal");
        check(Files.isDirectory(dealDir), "deal/ exists for the scans");

        // No production file references DealConfig at all (the tolerant
        // reader is retired — replaced by ProjectLocator +
        // StrictManifestParser).
        // Code-level references only (javadoc {@code DealConfig} mentions
        // of the retired reader are documentation, not construction).
        List<String> dealConfigRefs = new ArrayList<>();
        try (var walk = Files.walk(dealDir)) {
            walk.filter(p -> p.toString().endsWith(".java"))
                .sorted()
                .forEach(p -> {
                    try {
                        String text = Files.readString(p);
                        if (text.contains("DealConfig.")
                                || text.contains("DealConfig ")
                                || text.contains("DealConfig;")
                                || text.contains("DealConfig(")) {
                            dealConfigRefs.add(p.toString());
                        }
                    } catch (IOException ignored) { }
                });
        }
        check(dealConfigRefs.isEmpty(),
            "no deal/ production file constructs or references DealConfig: "
                + dealConfigRefs);
        check(!Files.exists(Path.of("deal/module/DealConfig.java")),
            "the tolerant DealConfig reader is deleted");

        // No implicit entry-directory root in the CLI.
        String mainSource = Files.readString(Path.of("deal/Main.java"));
        check(!mainSource.contains("moduleRoots.add"),
            "deal/Main.java appends no implicit entry-directory root");

        // No CWD bare-lookup fallback or classpath module fallback in the
        // orchestrator's resolution.
        String orchestratorSource = Files.readString(
            Path.of("deal/module/CompilationOrchestrator.java"));
        check(!orchestratorSource.contains("buildCandidates("),
            "the CWD bare-lookup fallback (buildCandidates) is gone from the"
                + " orchestrator");
        check(!orchestratorSource.contains("registerResourceModule("),
            "the classpath module fallback is gone from the orchestrator");
        check(!orchestratorSource.contains("computeModulePath("),
            "the lossy computeModulePath method is retired (no definition or"
                + " call site remains)");
        check(!(orchestratorSource.contains("DealConfig.")
                || orchestratorSource.contains("DealConfig ")),
            "the orchestrator consumes ProjectContext + SourceModuleResolver,"
                + " never DealConfig");

        // The stdlib resolver reads the pinned surface, never CWD-relative
        // Path.of("std") reads or a RuntimeException "broken installation".
        String stdlibSource = Files.readString(
            Path.of("deal/module/StdlibModuleResolver.java"));
        check(stdlibSource.contains("stdlibExports("),
            "the stdlib resolver exposes the surface-path extraction API");
        check(!stdlibSource.contains("Path.of(\"std\")"),
            "the stdlib resolver performs no CWD-relative Path.of(\"std\")"
                + " read");
        check(!stdlibSource.contains("throw new RuntimeException(\n"
                + "                    \"Stdlib declaration file not found"),
            "the RuntimeException \"broken installation\" path is gone");
    }

    // =========================================================================
    // 9. Registry behavior: entry-main-missing is E2012, configuration
    //    failures are E2010 (behavior-level checks through the CLI).
    // =========================================================================

    private static void testRegistryBehavior() throws Exception {
        System.out.println("-- Registry behavior: E2012 entry-main, E2010 config --");

        Path root = Files.createTempDirectory("deal_mig_registry_");
        try {
            write(root, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"backend\": \"luajit\"\n}\n");

            // Entry without main: E2012 through the production CLI.
            Path noMain = write(root, "src/no_main.deal",
                "export function run(): int { return 1; }\n");
            String[] missing = runCliCapturingErr(new String[]{
                "compile", noMain.toString()});
            check("1".equals(missing[0]), "the entry-main-missing compile exits 1");
            check(missing[1].contains("E2012")
                    && missing[1].contains("Entry module must export 'main'"),
                "entry-main-missing is E2012 through the formatter: " + missing[1]);
            check(!missing[1].contains("E2010"),
                "entry-main-missing is not E2010: " + missing[1]);

            // Bad main signature: E2011 unchanged.
            Path badMain = write(root, "src/bad_main.deal",
                "export function main(x: int): null { return null; }\n");
            String[] wrong = runCliCapturingErr(new String[]{
                "compile", badMain.toString()});
            check("1".equals(wrong[0]), "the wrong-signature main exits 1");
            check(wrong[1].contains("E2011"),
                "the wrong main signature stays E2011: " + wrong[1]);

            // A configuration failure is E2010 (already pinned by the
            // malformed-manifest scenario; re-assert here for the registry
            // behavior pair).
            Path badEntry = write(root, "bad_proj/main.deal",
                "export function main(): null { return null; }\n");
            write(root, "bad_proj/deal.json",
                "{\"languageVersion\": \"1.1\"}\n");
            String[] bad = runCliCapturingErr(new String[]{
                "compile", badEntry.toString()});
            check(bad[1].contains("E2010"),
                "a configuration failure is E2010: " + bad[1]);
        } finally {
            deleteRecursively(root);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Project Migration Integration Test (ISSUE-0269) ===\n");

        testSingleManifestProjectRunsBothBackends();
        testOutOfRootClassIsE2010();
        testNonExportedClassUnrepresentableIdentityIsE2010();
        testAncestorManifestDiscovery();
        testMalformedManifestBeforeOverride();
        testCliOverrides();
        testPostValidationWriteFailure();
        testStdlibSurfaceResolution();
        testProductionSourceRetirement();
        testRegistryBehavior();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
