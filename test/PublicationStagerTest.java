package deal.test;

import deal.codegen.Backend;
import deal.distribution.DistributionHome;
import deal.module.CompilationOrchestrator;
import deal.publication.Artifact;
import deal.publication.ArtifactSet;
import deal.publication.PublicationStager;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Stream;

/**
 * The transactional publication contract suite (ISSUE-0458, design
 * source {@code whole-project-artifact-publication} Verification 1-7):
 * the forced-failure stage test, fresh-root publish + whole-set
 * semantics, stale-set purge, crash recovery under the per-root lock,
 * concurrency serialization, IR-dump transactionality, out-of-checkout
 * distribution copies, the injected publish I/O failure path with the
 * pinned deterministic diagnostic, and the {@link ArtifactSet} model
 * contract.
 *
 * <p>Every assertion is a real compilation through
 * {@link CompilationOrchestrator} (or a real {@link PublicationStager}
 * publish over a real staging tree), so the {@code run_tests.sh}
 * registration executes the proofs — never dead code. The suite runs
 * from the repository root: the checkout CWD dev-fallback tier of
 * {@link DistributionHome} supplies the committed {@code std/*} and
 * {@code deal/runtime.*} bytes wherever a test does not pin a
 * distribution tier explicitly.</p>
 */
public class PublicationStagerTest {

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

    public static void main(String[] args) throws Exception {
        System.out.println(
            "=== Publication Stager Tests (ISSUE-0458) ===\n");

        testArtifactModel();
        testSkipSitesRemoved();
        testForcedFailureLeavesLiveRootUntouched();
        testFreshRootPublishWholeSetSemantics();
        testStaleSetPurge();
        testCrashRecoveryRestoresTornRetired();
        testStaleStageTreesRemoved();
        testConcurrentCompilationsSerialize();
        testIrDumpsStagedAndTransactional();
        testOutOfCheckoutCopiesResolveDistributionHome();
        testPublishMoveFailureRestoresAndReports();
        testStagingFailureReportsPinnedDiagnostic();
        testDeleteRetiredFailureToleratedAndRecovered();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }

    // =========================================================================
    // Fixture helpers
    // =========================================================================

    private static Path tempDir(String prefix) throws IOException {
        return Files.createTempDirectory(prefix);
    }

    private static void writeText(Path file, String text) throws IOException {
        Files.createDirectories(file.getParent());
        Files.writeString(file, text, StandardCharsets.UTF_8);
    }

    private static void deleteTree(Path dir) {
        if (dir == null || !Files.exists(dir)) {
            return;
        }
        try (Stream<Path> walk = Files.walk(dir)) {
            walk.sorted(java.util.Comparator.reverseOrder())
                .forEach(f -> {
                    try {
                        Files.deleteIfExists(f);
                    } catch (IOException ignored) {
                    }
                });
        } catch (IOException ignored) {
        }
    }

    /**
     * The root-relative {@code '/'}-separated artifact paths under a
     * tree, sorted (the observable set shape).
     */
    private static Set<String> treePaths(Path root) throws IOException {
        if (!Files.isDirectory(root)) {
            return Set.of();
        }
        Set<String> paths = new java.util.TreeSet<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path file : walk.filter(Files::isRegularFile).toList()) {
                paths.add(root.relativize(file).toString()
                    .replace(java.io.File.separatorChar, '/'));
            }
        }
        return paths;
    }

    /** The root-relative path → byte map of one tree (sorted keys). */
    private static Map<String, byte[]> treeBytes(Path root)
            throws IOException {
        Map<String, byte[]> bytes = new TreeMap<>();
        if (!Files.isDirectory(root)) {
            return bytes;
        }
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path file : walk.filter(Files::isRegularFile).toList()) {
                bytes.put(root.relativize(file).toString()
                        .replace(java.io.File.separatorChar, '/'),
                    Files.readAllBytes(file));
            }
        }
        return bytes;
    }

    private static void checkTreeEquals(Map<String, byte[]> expected,
            Map<String, byte[]> actual, String message) {
        if (!expected.keySet().equals(actual.keySet())) {
            check(false, message + " (expected " + expected.keySet()
                + ", actual " + actual.keySet() + ")");
            return;
        }
        boolean identical = true;
        for (Map.Entry<String, byte[]> entry : expected.entrySet()) {
            if (!Arrays.equals(entry.getValue(),
                    actual.get(entry.getKey()))) {
                identical = false;
                break;
            }
        }
        check(identical, message + " (same path set "
            + expected.keySet() + ", byte-identical content)");
    }

    /**
     * The stale publication siblings of one root: siblings whose names
     * start with {@code <rootname>.deal-stage-} or
     * {@code <rootname>.deal-retired-}.
     */
    private static List<Path> staleSiblings(Path root) throws IOException {
        List<Path> siblings = new ArrayList<>();
        Path parent = root.getParent();
        if (parent == null || !Files.isDirectory(parent)) {
            return siblings;
        }
        String rootName = root.getFileName().toString();
        try (Stream<Path> entries = Files.list(parent)) {
            for (Path entry : entries.toList()) {
                String name = entry.getFileName().toString();
                if (name.startsWith(rootName
                            + PublicationStager.STAGE_TREE_MARKER)
                        || name.startsWith(rootName
                            + PublicationStager.RETIRED_TREE_MARKER)) {
                    siblings.add(entry);
                }
            }
        }
        return siblings;
    }

    /** Deep byte comparison of two tree maps (same keys, same bytes). */
    private static boolean treeContentEquals(Map<String, byte[]> a,
            Map<String, byte[]> b) {
        if (!a.keySet().equals(b.keySet())) {
            return false;
        }
        for (Map.Entry<String, byte[]> entry : a.entrySet()) {
            if (!Arrays.equals(entry.getValue(), b.get(entry.getKey()))) {
                return false;
            }
        }
        return true;
    }

    /**
     * One orchestrator compile of a single-source-dir project. The
     * compile resolves the harness invocation (ISSUE-0643 P10 item 3):
     * the suite's subject — the staging/publication transaction over the
     * per-module artifact set — is arm-independent, and the identical
     * compile inputs keep every artifact assertion.
     */
    private static boolean compileProject(Path srcDir, Path outputDir,
            Backend backend, boolean dumpIr, boolean sourceMap,
            StringBuilder capturedErr) throws IOException {
        Path entry = srcDir.resolve("main.deal");
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry.toAbsolutePath().normalize(),
            outputDir.toAbsolutePath().normalize(),
            false, dumpIr, sourceMap, sourceMap, backend,
            (Map<String, String>) null,
            List.of(srcDir.toAbsolutePath().normalize()), null, null,
            ConformanceHarnessMetadata.invocation(
                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32));
        if (capturedErr != null) {
            PrintStream originalErr = System.err;
            ByteArrayOutputStream captured = new ByteArrayOutputStream();
            try {
                System.setErr(new PrintStream(captured, true,
                    StandardCharsets.UTF_8));
                return orchestrator.compile();
            } finally {
                System.err.flush();
                System.setErr(originalErr);
                capturedErr.append(captured.toString(
                    StandardCharsets.UTF_8));
            }
        }
        return orchestrator.compile();
    }

    // =========================================================================
    // The model contract
    // =========================================================================

    private static void testArtifactModel() throws Exception {
        System.out.println("-- Artifact / ArtifactSet model");

        byte[] content = "payload".getBytes(StandardCharsets.UTF_8);
        Artifact artifact = new Artifact("app/main.lua", content);
        check("app/main.lua".equals(artifact.relativePath())
                && Arrays.equals(content, artifact.content()),
            "the artifact carries its relative path and content");
        artifact.content()[0] = 'X';
        check(Arrays.equals(content, artifact.content()),
            "the content accessor returns a defensive copy (the stored "
                + "bytes are immutable)");

        for (String bad : new String[] {
                "", "/leading", "trailing/", "a//b", "a/../b", "a/.", "."
            }) {
            boolean rejected = false;
            try {
                new Artifact(bad, content);
            } catch (IllegalArgumentException expected) {
                rejected = true;
            }
            check(rejected, "the non-canonical path \"" + bad
                + "\" is rejected");
        }

        ArtifactSet set = ArtifactSet.of(
            new Artifact("a.lua", "a".getBytes(StandardCharsets.UTF_8)),
            new Artifact("std/x.lua", "x".getBytes(StandardCharsets.UTF_8)));
        check(set.size() == 2 && !set.isEmpty(),
            "the set models two artifacts");
        check(set.artifact("a.lua").isPresent()
                && set.artifact("missing.lua").isEmpty(),
            "the per-path lookup finds exactly the staged artifact");
        check(set.relativePaths().equals(
                new LinkedHashSet<>(List.of("a.lua", "std/x.lua"))),
            "the relative paths preserve insertion order");
        check(set.artifacts().get(0).relativePath().equals("a.lua"),
            "the artifact list preserves insertion order");

        boolean duplicateRejected = false;
        try {
            new ArtifactSet(List.of(
                new Artifact("a.lua", "a".getBytes(StandardCharsets.UTF_8)),
                new Artifact("a.lua", "b".getBytes(StandardCharsets.UTF_8))));
        } catch (IllegalArgumentException expected) {
            duplicateRejected = true;
        }
        check(duplicateRejected,
            "a duplicate relative path is rejected by the set");
    }

    // =========================================================================
    // The D3 structural criterion: the four skip sites are removed
    // =========================================================================

    private static void testSkipSitesRemoved() throws Exception {
        System.out.println(
            "-- The four Files.exists skip sites are removed");
        String orchestratorSource = Files.readString(
            Path.of("deal/module/CompilationOrchestrator.java"));
        check(!orchestratorSource.contains("Files.exists(runtimeDest)"),
            "no runtime-destination skip remains (copyRuntimeLibrary/"
                + "copyJsRuntimeLibrary stage fresh)");
        check(!orchestratorSource.contains("Files.exists(destFile)"),
            "no stdlib-destination skip remains (copyStdlibModules/"
                + "copyStdlibJsModules stage fresh)");
        check(orchestratorSource.contains("stageRuntimeCopy")
                && orchestratorSource.contains("stageStdlibCopy"),
            "the runtime/stdlib copies stage through the publication "
                + "sink");
    }

    // =========================================================================
    // Verification 1: the forced-failure stage test
    // =========================================================================

    private static void testForcedFailureLeavesLiveRootUntouched()
            throws Exception {
        System.out.println("-- Forced failure in a later module's codegen");

        Path base = tempDir("pub-forced-failure-");
        Path src = base.resolve("src");
        Path out = base.resolve("out");
        try {
            writeText(src.resolve("main.deal"),
                "import * as lib from \"./lib\"\n"
                    + "export function main(): null { return null; }\n"
                    + "export function run(): int { return lib.one(); }\n");
            writeText(src.resolve("lib.deal"),
                "export function one(): int { return 1; }\n");

            boolean first = compileProject(src, out, Backend.JS,
                false, false, null);
            check(first, "the clean JS project compiles");
            Map<String, byte[]> before = treeBytes(out);
            check(!before.isEmpty(),
                "the clean compile published a live set: " + before.keySet());

            // The later module (lib) now fails its codegen with the
            // @extern-c E6006 rejection while the entry still codegens
            // clean — the whole-set failure contract must leave the
            // prior live set byte-identical.
            writeText(src.resolve("ffi.d.deal"),
                "// @extern-c\nexport function cFn(x: int): int;\n");
            writeText(src.resolve("lib.deal"),
                "import * as ffi from \"./ffi\"\n"
                    + "export function one(): int { return ffi.cFn(1); }\n");
            boolean second = compileProject(src, out, Backend.JS,
                false, false, null);
            check(!second, "the @extern-c rejection fails the recompile");

            Map<String, byte[]> after = treeBytes(out);
            checkTreeEquals(before, after,
                "the live root is byte-identical after the forced failure");
            check(staleSiblings(out).isEmpty(),
                "no .deal-stage-*/.deal-retired-* residue: "
                    + staleSiblings(out));
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 2: fresh-root publish + whole-set semantics
    // =========================================================================

    private static void testFreshRootPublishWholeSetSemantics()
            throws Exception {
        System.out.println("-- Fresh-root publish and whole-set semantics");

        Path base = tempDir("pub-fresh-root-");
        Path src = base.resolve("src");
        Path out = base.resolve("build/lua");
        try {
            writeText(src.resolve("main.deal"),
                "import * as lib from \"./lib\"\n"
                    + "export function main(): null { return null; }\n");
            writeText(src.resolve("lib.deal"),
                "export function value(): int { return 7; }\n");

            boolean first = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(first, "the fresh-root LuaJIT compile succeeds");
            Set<String> expected = new LinkedHashSet<>(List.of(
                "main.lua", "lib.lua", "deal/runtime.lua",
                "std/console.lua", "std/string.lua", "std/table.lua",
                "std/json.lua", "std/math.lua", "std/time.lua"));
            check(treePaths(out).equals(expected),
                "the fresh root contains exactly the expected files: "
                    + treePaths(out));

            // Delete the lib module: the whole-set swap removes its
            // orphaned artifact with the replaced set.
            Files.delete(src.resolve("lib.deal"));
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");
            boolean second = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(second, "the second compile after deleting lib succeeds");
            Set<String> expectedAfterDelete = new LinkedHashSet<>(
                List.of("main.lua", "deal/runtime.lua",
                    "std/console.lua", "std/string.lua", "std/table.lua",
                    "std/json.lua", "std/math.lua", "std/time.lua"));
            check(treePaths(out).equals(expectedAfterDelete),
                "the orphaned lib.lua artifact is gone (whole-set "
                    + "semantics): " + treePaths(out));
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 3: stale-set purge
    // =========================================================================

    private static void testStaleSetPurge() throws Exception {
        System.out.println("-- Stale-set purge");

        Path base = tempDir("pub-stale-purge-");
        Path src = base.resolve("src");
        Path out = base.resolve("out");
        try {
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");

            // Pre-populate the live root with a stale stdlib copy, a
            // stale runtime copy, and an obsolete module artifact.
            writeText(out.resolve("std/console.lua"),
                "stale stdlib bytes\n");
            writeText(out.resolve("deal/runtime.lua"),
                "stale runtime bytes\n");
            writeText(out.resolve("obsolete.lua"),
                "stale module artifact\n");

            boolean ok = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(ok, "the compile succeeds over the stale set");
            Map<String, byte[]> published = treeBytes(out);
            check(!published.containsKey("obsolete.lua"),
                "the stale obsolete module artifact is gone: "
                    + published.keySet());
            check(published.containsKey("deal/runtime.lua")
                    && published.containsKey("std/console.lua"),
                "the runtime and stdlib copies were re-staged fresh: "
                    + published.keySet());
            check(Arrays.equals(published.get("deal/runtime.lua"),
                    Files.readAllBytes(Path.of("deal/runtime.lua"))),
                "the runtime copy was re-staged fresh from the resolved "
                    + "surface (no stale bytes survive)");
            check(Arrays.equals(published.get("std/console.lua"),
                    Files.readAllBytes(Path.of("std/console.lua"))),
                "the stdlib copy was re-staged fresh from the resolved "
                    + "surface (no stale bytes survive)");
            check(!new String(published.get("std/console.lua"),
                    StandardCharsets.UTF_8).contains("stale"),
                "the stale stdlib bytes are replaced");
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 4: crash recovery under the lock
    // =========================================================================

    private static void testCrashRecoveryRestoresTornRetired()
            throws Exception {
        System.out.println("-- Crash recovery: torn publish restored under the lock");

        Path base = tempDir("pub-torn-");
        try {
            Path root = base.resolve("out");
            // Simulate a torn publish: the retired set is present and
            // the live set is absent (the crash window between the
            // first move and the swap).
            Path torn = base.resolve("out.deal-retired-pid999-dead");
            writeText(torn.resolve("old.txt"), "old set\n");

            PublicationStager stager = PublicationStager.forRoot(root);
            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_STAGE_TO_LIVE.equals(
                        step)) {
                    throw new IOException(
                        "injected stage-to-live failure");
                }
            });
            stager.stage("new.txt",
                "new set\n".getBytes(StandardCharsets.UTF_8));
            boolean threw = false;
            try {
                stager.publish();
            } catch (PublicationStager.PublishFailure expected) {
                threw = true;
                check(expected.getMessage().contains("injected"),
                    "the injected failure reason is reported: "
                        + expected.getMessage());
                check(expected.publicationRoot().toAbsolutePath()
                        .normalize().equals(root.toAbsolutePath()
                            .normalize()),
                    "the failure names the publication root");
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(threw, "the faulted publish fails with PublishFailure");

            // Recovery restored the torn retired set into live at
            // publish start; the failed swap then restored it again —
            // so the live set is the torn set, never the new set, and
            // never absent.
            Map<String, byte[]> live = treeBytes(root);
            check(live.size() == 1
                    && Arrays.equals(live.get("old.txt"),
                        "old set\n".getBytes(StandardCharsets.UTF_8)),
                "the torn retired set was restored into live: "
                    + live.keySet());
            check(staleSiblings(root).isEmpty(),
                "no stage/retired residue after the faulted publish: "
                    + staleSiblings(root));
        } finally {
            deleteTree(base);
        }
    }

    private static void testStaleStageTreesRemoved() throws Exception {
        System.out.println("-- Crash recovery: stale stage trees removed");

        Path base = tempDir("pub-stale-stage-");
        try {
            // Case 1: a stale stage tree with a prior live set.
            Path root = base.resolve("out");
            writeText(root.resolve("old.txt"), "old\n");
            Path stale = base.resolve("out.deal-stage-pid777-dead");
            writeText(stale.resolve("stale.txt"), "stale\n");

            PublicationStager stager = PublicationStager.forRoot(root);
            stager.stage("new.txt",
                "new\n".getBytes(StandardCharsets.UTF_8));
            stager.publish();
            check(stager.published(),
                "the publish over the stale stage tree succeeds");
            check(treePaths(root).equals(Set.of("new.txt")),
                "the whole set is replaced (old.txt gone, stale.txt "
                    + "never published): " + treePaths(root));
            check(staleSiblings(root).isEmpty(),
                "the stale stage tree is removed: " + staleSiblings(root));
            check(stager.publishedSet().size() == 1
                    && Arrays.equals(
                        stager.publishedSet().artifact("new.txt")
                            .orElseThrow().content(),
                        "new\n".getBytes(StandardCharsets.UTF_8)),
                "the published set models the published artifact");

            // Case 2: a stale stage tree without a retired set and no
            // live set — removed, and the fresh-root publish lands the
            // new set.
            Path freshRoot = base.resolve("out-fresh");
            Path staleFresh = base.resolve(
                "out-fresh.deal-stage-pid777-dead");
            writeText(staleFresh.resolve("stale.txt"), "stale\n");
            PublicationStager fresh = PublicationStager.forRoot(freshRoot);
            fresh.stage("new.txt",
                "new\n".getBytes(StandardCharsets.UTF_8));
            fresh.publish();
            check(fresh.published(), "the fresh-root publish succeeds");
            check(treePaths(freshRoot).equals(Set.of("new.txt")),
                "the fresh root carries exactly the new set: "
                    + treePaths(freshRoot));
            check(staleSiblings(freshRoot).isEmpty(),
                "the stale stage tree without a retired set is removed: "
                    + staleSiblings(freshRoot));
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 5: concurrency
    // =========================================================================

    private static void testConcurrentCompilationsSerialize()
            throws Exception {
        System.out.println("-- Concurrency: two compilations into one root");

        Path base = tempDir("pub-concurrent-");
        try {
            Path srcA = base.resolve("projA");
            writeText(srcA.resolve("main.deal"),
                "export function main(): null { return null; }\n"
                    + "export function tag(): string { return \"A\"; }\n");
            Path srcB = base.resolve("projB");
            writeText(srcB.resolve("main.deal"),
                "export function main(): null { return null; }\n"
                    + "export function tag(): string { return \"B\"; }\n");
            Path out = base.resolve("out");

            // Reference sets: each project compiled alone.
            Path refA = base.resolve("refA");
            Path refB = base.resolve("refB");
            boolean refAOk = compileProject(srcA, refA, Backend.LUAJIT,
                false, false, null);
            boolean refBOk = compileProject(srcB, refB, Backend.LUAJIT,
                false, false, null);
            check(refAOk && refBOk, "the reference compiles succeed");
            Map<String, byte[]> setA = treeBytes(refA);
            Map<String, byte[]> setB = treeBytes(refB);

            AtomicBoolean okA = new AtomicBoolean();
            AtomicBoolean okB = new AtomicBoolean();
            Thread threadA = new Thread(() -> {
                try {
                    okA.set(compileProject(srcA, out, Backend.LUAJIT,
                        false, false, null));
                } catch (IOException e) {
                    okA.set(false);
                }
            });
            Thread threadB = new Thread(() -> {
                try {
                    okB.set(compileProject(srcB, out, Backend.LUAJIT,
                        false, false, null));
                } catch (IOException e) {
                    okB.set(false);
                }
            });
            threadA.start();
            threadB.start();
            threadA.join();
            threadB.join();
            check(okA.get() && okB.get(),
                "both concurrent compilations complete");

            Map<String, byte[]> finalTree = treeBytes(out);
            check(treeContentEquals(finalTree, setA)
                    || treeContentEquals(finalTree, setB),
                "the final root is exactly one complete set — never a "
                    + "blend: " + finalTree.keySet());
            check(staleSiblings(out).isEmpty(),
                "no stage/retired residue after the concurrent compiles: "
                    + staleSiblings(out));
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 6: IR dumps
    // =========================================================================

    private static void testIrDumpsStagedAndTransactional()
            throws Exception {
        System.out.println("-- IR dumps: staged, discarded on failure, atomic on success");

        Path base = tempDir("pub-ir-");
        try {
            Path src = base.resolve("src");
            Path out = base.resolve("out");
            writeText(src.resolve("main.deal"),
                "import * as lib from \"./lib\"\n"
                    + "export function main(): null { return null; }\n");
            writeText(src.resolve("lib.deal"),
                "export function value(): int { return 7; }\n");

            // Successful publish: the dumps appear atomically with the
            // set.
            boolean ok = compileProject(src, out, Backend.LUAJIT,
                true, false, null);
            check(ok, "the --dump-ir compile succeeds");
            Set<String> publishedPaths = treePaths(out);
            check(publishedPaths.contains("main.ir.txt")
                    && publishedPaths.contains("lib.ir.txt"),
                "the IR dumps are published with the set: "
                    + publishedPaths);

            // Failing recompile: the dumps of the failed compilation
            // never reach the live root (byte-identical prior set).
            Map<String, byte[]> before = treeBytes(out);
            writeText(src.resolve("lib.deal"),
                "export function value(): int { return \"broken\"; }\n");
            boolean failedCompile = compileProject(src, out,
                Backend.LUAJIT, true, false, null);
            check(!failedCompile, "the type-broken recompile fails");
            checkTreeEquals(before, treeBytes(out),
                "the live root (including its IR dumps) is byte-identical "
                    + "after the failed --dump-ir run");
            check(staleSiblings(out).isEmpty(),
                "no stage/retired residue after the failed --dump-ir run");

            // Fresh root + failing compile: no live root at all.
            Path freshOut = base.resolve("out-fresh");
            boolean freshFailed = compileProject(src, freshOut,
                Backend.LUAJIT, true, false, null);
            check(!freshFailed, "the fresh-root failing compile fails");
            check(!Files.exists(freshOut),
                "the failing compilation leaves the fresh root absent "
                    + "(no .ir.txt anywhere in it)");
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification 7: out-of-checkout distribution copies
    // =========================================================================

    private static void testOutOfCheckoutCopiesResolveDistributionHome()
            throws Exception {
        System.out.println("-- Out-of-checkout copies resolve through DistributionHome");

        Path base = tempDir("pub-dist-home-");
        try {
            // A language distribution on the DEAL_HOME filesystem tier:
            // distinct marker bytes for the runtime and console stdlib.
            Path dist = base.resolve("distribution");
            writeText(dist.resolve("deal/runtime.lua"),
                "-- distribution runtime marker\n");
            writeText(dist.resolve("std/console.lua"),
                "-- distribution console marker\n");

            Path src = base.resolve("proj");
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");
            Path out = base.resolve("out");

            System.setProperty(DistributionHome.DEAL_HOME_PROPERTY,
                dist.toString());
            try {
                boolean ok = compileProject(src, out, Backend.LUAJIT,
                    false, false, null);
                check(ok, "the distribution-home compile succeeds");
                Map<String, byte[]> published = treeBytes(out);
                check(Arrays.equals(published.get("deal/runtime.lua"),
                        Files.readAllBytes(
                            dist.resolve("deal/runtime.lua"))),
                    "the staged runtime bytes equal the distribution's "
                        + "bytes (never the checkout's)");
                check(Arrays.equals(published.get("std/console.lua"),
                        Files.readAllBytes(
                            dist.resolve("std/console.lua"))),
                    "the staged stdlib bytes equal the distribution's "
                        + "bytes (never the checkout's)");

                // Project-local surface precedence: a project-local
                // std/ override stages its own bytes even with the
                // distribution present.
                Path overrideSrc = base.resolve("proj-override");
                writeText(overrideSrc.resolve("main.deal"),
                    "export function main(): null { return null; }\n");
                writeText(overrideSrc.resolve("std/console.lua"),
                    "-- project-local console marker\n");
                Path overrideOut = base.resolve("out-override");
                boolean overrideOk = compileProject(overrideSrc,
                    overrideOut, Backend.LUAJIT, false, false, null);
                check(overrideOk, "the project-local override compiles");
                Map<String, byte[]> overridePublished =
                    treeBytes(overrideOut);
                check(Arrays.equals(
                        overridePublished.get("std/console.lua"),
                        Files.readAllBytes(overrideSrc.resolve(
                            "std/console.lua"))),
                    "the project-local std/ override stages its own bytes "
                        + "(project surface wins over the distribution)");
                check(Arrays.equals(
                        overridePublished.get("deal/runtime.lua"),
                        Files.readAllBytes(
                            dist.resolve("deal/runtime.lua"))),
                    "the runtime still resolves from the distribution "
                        + "(no project-local runtime tier is pinned)");
            } finally {
                System.clearProperty(DistributionHome.DEAL_HOME_PROPERTY);
            }
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification: the publish I/O failure path (injected moves)
    // =========================================================================

    private static void testPublishMoveFailureRestoresAndReports()
            throws Exception {
        System.out.println("-- Publish I/O failure: restore per D2 + pinned diagnostic");

        Path base = tempDir("pub-publish-fail-");
        try {
            Path src = base.resolve("src");
            Path out = base.resolve("out");
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");
            boolean first = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(first, "the initial compile publishes the prior set");
            Map<String, byte[]> v1 = treeBytes(out);

            // Injected second-move (S -> live) failure: the prior set
            // is restored and the pinned diagnostic reports exit 1.
            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_STAGE_TO_LIVE.equals(
                        step)) {
                    throw new IOException("injected move failure");
                }
            });
            StringBuilder capturedErr = new StringBuilder();
            boolean second;
            try {
                second = compileProject(src, out, Backend.LUAJIT,
                    false, false, capturedErr);
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(!second, "the injected second-move failure fails the "
                + "compile (exit 1 through Main)");
            check(capturedErr.toString().contains(
                    "deal: cannot publish artifacts to '"
                        + out.toAbsolutePath().normalize() + "': "),
                "the pinned deterministic compiler I/O diagnostic is "
                    + "printed: " + capturedErr);
            checkTreeEquals(v1, treeBytes(out),
                "the prior live set is restored byte-identical after the "
                    + "failed second move");
            check(staleSiblings(out).isEmpty(),
                "no stage/retired residue after the failed second move");

            // Injected first-move (live -> retired) failure: the prior
            // set is untouched.
            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_RETIRE_MOVE.equals(
                        step)) {
                    throw new IOException("injected retire failure");
                }
            });
            StringBuilder capturedErr2 = new StringBuilder();
            boolean third;
            try {
                third = compileProject(src, out, Backend.LUAJIT,
                    false, false, capturedErr2);
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(!third, "the injected retire-move failure fails the "
                + "compile");
            check(capturedErr2.toString().contains(
                    "deal: cannot publish artifacts to '"),
                "the retire-move failure reports the pinned diagnostic: "
                    + capturedErr2);
            checkTreeEquals(v1, treeBytes(out),
                "the prior live set is untouched after the failed retire "
                    + "move");
            check(staleSiblings(out).isEmpty(),
                "no stage/retired residue after the failed retire move");

            // Fresh-root injected move failure: the root stays absent.
            Path freshOut = base.resolve("out-fresh");
            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_STAGE_TO_LIVE.equals(
                        step)) {
                    throw new IOException("injected fresh move failure");
                }
            });
            StringBuilder capturedErr3 = new StringBuilder();
            boolean fresh;
            try {
                fresh = compileProject(src, freshOut, Backend.LUAJIT,
                    false, false, capturedErr3);
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(!fresh, "the injected fresh-root move failure fails the "
                + "compile");
            check(!Files.exists(freshOut),
                "the failed fresh-root publish leaves no live set");
            check(staleSiblings(freshOut).isEmpty(),
                "no stage/retired residue after the failed fresh-root "
                    + "publish");
        } finally {
            deleteTree(base);
        }
    }

    // =========================================================================
    // Verification: staging failure + tolerated retired delete
    // =========================================================================

    private static void testStagingFailureReportsPinnedDiagnostic()
            throws Exception {
        System.out.println("-- Staging failure: pinned diagnostic, nothing published");

        Path base = tempDir("pub-staging-fail-");
        try {
            Path src = base.resolve("src");
            Path out = base.resolve("out");
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");
            boolean first = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(first, "the initial compile publishes the prior set");
            Map<String, byte[]> v1 = treeBytes(out);

            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_STAGING_BEGAN.equals(
                        step)) {
                    throw new IOException("injected staging failure");
                }
            });
            StringBuilder capturedErr = new StringBuilder();
            boolean second;
            try {
                second = compileProject(src, out, Backend.LUAJIT,
                    false, false, capturedErr);
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(!second, "the injected staging failure fails the "
                + "compile");
            check(capturedErr.toString().contains(
                    "deal: cannot publish artifacts to '"
                        + out.toAbsolutePath().normalize() + "': "),
                "the staging failure reports the pinned deterministic "
                    + "compiler I/O diagnostic: " + capturedErr);
            checkTreeEquals(v1, treeBytes(out),
                "the prior live set is untouched after the staging "
                    + "failure");
            check(staleSiblings(out).isEmpty(),
                "no stage/retired residue after the staging failure");
        } finally {
            deleteTree(base);
        }
    }

    private static void testDeleteRetiredFailureToleratedAndRecovered()
            throws Exception {
        System.out.println("-- Tolerated retired delete + next-publish recovery");

        Path base = tempDir("pub-delete-retired-");
        try {
            Path src = base.resolve("src");
            Path out = base.resolve("out");
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n"
                    + "export function tag(): string { return \"one\"; }\n");
            boolean first = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(first, "the initial compile succeeds");

            // The post-swap retired delete fails (injected): the publish
            // still succeeds (the live set is the new set) and the
            // retired sibling stays beside the live set.
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n"
                    + "export function tag(): string { return \"two\"; }\n");
            PublicationStager.installPublishFault(step -> {
                if (PublicationStager.FAULT_STEP_DELETE_RETIRED.equals(
                        step)) {
                    throw new IOException("injected retired delete failure");
                }
            });
            boolean second;
            try {
                second = compileProject(src, out, Backend.LUAJIT,
                    false, false, null);
            } finally {
                PublicationStager.clearPublishFault();
            }
            check(second, "the tolerated retired-delete failure still "
                + "publishes (the live set is the new set)");
            String publishedLua = new String(Files.readAllBytes(
                out.resolve("main.lua")), StandardCharsets.UTF_8);
            check(publishedLua.contains("two"),
                "the live set is the new set after the tolerated delete "
                    + "failure");
            check(!staleSiblings(out).isEmpty(),
                "the failed delete leaves the retired sibling beside the "
                    + "live set (the post-swap crash window): "
                    + staleSiblings(out));

            // The next publish start's recovery removes the leftover
            // retired sibling under the lock.
            writeText(src.resolve("main.deal"),
                "export function main(): null { return null; }\n"
                    + "export function tag(): string { return \"three\"; }\n");
            boolean third = compileProject(src, out, Backend.LUAJIT,
                false, false, null);
            check(third, "the recovery publish succeeds");
            check(staleSiblings(out).isEmpty(),
                "the next publish start removed the leftover retired "
                    + "sibling: " + staleSiblings(out));
            String publishedLuaThree = new String(Files.readAllBytes(
                out.resolve("main.lua")), StandardCharsets.UTF_8);
            check(publishedLuaThree.contains("three"),
                "the recovery publish still lands the new set");
        } finally {
            deleteTree(base);
        }
    }
}
