package deal.test;

import deal.codegen.Backend;
import deal.codegen.lua.AsyncExportInvocationRequest;
import deal.codegen.lua.LuaJitAsyncExportInvoker;
import deal.codegen.lua.LuaJitAsyncExportInvoker.EnvelopeJson;
import deal.codegen.lua.LuaJitAsyncExportInvoker.Result;
import deal.codegen.lua.LuaJitAsyncExportInvocationException;
import deal.module.CompilationOrchestrator;
import deal.project.StrictManifestParser;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.junit.Assume.assumeTrue;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Verification 1-5 of the production LuaJIT async-export host invoker
 * (ISSUE-0417 component, ISSUE-0418 verification matrix and release
 * gates, luajit-async-export-invoker): {@link LuaJitAsyncExportInvoker}
 * is exercised end-to-end under real {@code luajit}. The Verification
 * 1-4 fixtures compile through the production
 * {@link CompilationOrchestrator} path and invoke the production
 * {@link LuaJitAsyncExportInvoker}; the duplicate entry chunk and the
 * absent-location completion-matcher case stay staged (compiled
 * artifacts cannot produce duplicate wrappers or a matcher mismatch —
 * the design's own staging technique); fake drivers cover the
 * codec/hard-failure matrix.
 */
public class LuaJitAsyncExportInvokerTest {

    private static final String MARKER = "DEAL_ASYNC_EXPORT_RESULT:";
    private static final String TEMP_PREFIX = "deal-async-export-invoker-";

    private static Path tmp;
    private static Path root;
    private static Path defaultEntry;
    private static boolean luajitAvailable;

    @BeforeClass
    public static void setUpClass() throws IOException {
        luajitAvailable = luajitOnPath();
        tmp = Files.createTempDirectory("deal-async-invoker-test-");
        // Staged deployment root (D5 marker + stdlib surface).
        root = tmp.resolve("root");
        Files.createDirectories(root.resolve("deal"));
        Files.createDirectories(root.resolve("std"));
        Files.copy(Path.of("deal/runtime.lua"),
            root.resolve("deal/runtime.lua"));
        for (String m : new String[] {
                "console", "json", "math", "string", "table", "time"}) {
            Files.copy(Path.of("std", m + ".lua"),
                root.resolve("std").resolve(m + ".lua"));
        }
        Files.createDirectories(root.resolve("entries"));
        defaultEntry = writeEntry("value_null", CHUNK_VALUE_NULL);
    }

    @AfterClass
    public static void tearDownClass() {
        deleteRecursively(tmp);
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static boolean luajitOnPath() {
        try {
            new ProcessBuilder("luajit", "-v").start().waitFor();
            return true;
        } catch (Exception e) {
            return false;
        }
    }

    private static Path writeEntry(String name, String chunk)
            throws IOException {
        Path p = root.resolve("entries").resolve(name + ".lua");
        Files.writeString(p, chunk);
        return p;
    }

    private static Result invoke(Path entryArtifact, String exportName,
                                 String returnDescriptor) {
        return new LuaJitAsyncExportInvoker().invoke(
            new AsyncExportInvocationRequest(entryArtifact, exportName,
                returnDescriptor));
    }

    private static LuaJitAsyncExportInvocationException expectInvocationFailure(
            Path entryArtifact, String exportName, String returnDescriptor) {
        try {
            invoke(entryArtifact, exportName, returnDescriptor);
        } catch (LuaJitAsyncExportInvocationException e) {
            return e;
        }
        fail("expected LuaJitAsyncExportInvocationException");
        return null;
    }

    /** All temp dirs with the invoker's materialization prefix. */
    private static Set<String> invokerTempDirs() throws IOException {
        Set<String> dirs = new TreeSet<>();
        Path tmpDir = Path.of(System.getProperty("java.io.tmpdir"));
        try (Stream<Path> s = Files.list(tmpDir)) {
            for (Path p : s.toList()) {
                if (Files.isDirectory(p)
                        && p.getFileName().toString().startsWith(TEMP_PREFIX)) {
                    dirs.add(p.toAbsolutePath().toString());
                }
            }
        }
        return dirs;
    }

    /**
     * Asserts the per-invocation temp directory was deleted after the
     * luajit child exited (the design's cleanup post-state). Other test
     * JVMs on this shared machine materialize their own invoker dirs
     * under the same {@code /tmp} prefix at any moment, so a stranger
     * dir is a leak only when it persists beyond the grace window;
     * concurrent invokes in other JVMs disappear within it while a real
     * cleanup defect (the invoker deletes the dir in a finally block)
     * persists forever and still fails this assertion.
     */
    private static void assertNoTempDirLeaks(Set<String> before)
            throws IOException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(10);
        while (true) {
            Set<String> after = invokerTempDirs();
            if (after.equals(before)) {
                return;
            }
            Set<String> strangers = new TreeSet<>(after);
            strangers.removeAll(before);
            if (System.nanoTime() >= deadline) {
                fail("per-invocation temp directories leaked: " + strangers);
            }
            try {
                Thread.sleep(50);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                fail("interrupted while verifying temp-dir cleanup");
            }
        }
    }

    private static void deleteRecursively(Path dir) {
        if (dir == null || !Files.exists(dir)) {
            return;
        }
        try (Stream<Path> walk = Files.walk(dir)) {
            walk.sorted(java.util.Comparator.reverseOrder()).forEach(p -> {
                try {
                    Files.deleteIfExists(p);
                } catch (IOException ignored) {
                }
            });
        } catch (IOException ignored) {
        }
    }

    // =========================================================================
    // Production compilation helpers (Verification 1-4 matrix)
    // =========================================================================

    /**
     * Compiles one entry module through the production orchestrator path
     * (the ModuleSystemTest drive): the working-tree root is the stdlib
     * directory, exactly like the CLI, and an optional deal.json manifest
     * carries externals for host-module fixtures.
     *
     * @return the absolute entry source path — the pinned source-location
     *         file of runtime diagnostics
     */
    private static Path compileProductionEntry(Path projectDir,
            String entryFileName, String source, String manifestJson,
            Path outRoot) throws IOException {
        Path srcRoot = projectDir.resolve("src");
        Files.createDirectories(srcRoot);
        Path entrySource = srcRoot.resolve(entryFileName);
        Files.writeString(entrySource, source);
        // ISSUE-0269: the strict parser replaces the retired tolerant
        // DealConfig reader. The isolated-phase orchestrator path takes
        // the externals map (raw specifier → declaration text resolved
        // to an absolute path — the synthesized context resolves
        // relative texts from the entry directory, while the manifest
        // declares them relative to the project root).
        Map<String, String> externals = null;
        if (manifestJson != null) {
            Files.writeString(projectDir.resolve("deal.json"), manifestJson);
            StrictManifestParser.StrictManifestParseResult parsed =
                StrictManifestParser.parse(
                    projectDir.resolve("deal.json").toString(), manifestJson);
            assertNull("the externals manifest must parse strictly cleanly",
                parsed.failure());
            assertNotNull("the externals manifest must yield a manifest",
                parsed.manifest());
            externals = new LinkedHashMap<>();
            for (Map.Entry<String, deal.project.ExternalEntrySpec> entry
                    : parsed.manifest().externals().entrySet()) {
                Path declaration = projectDir.resolve(
                    entry.getValue().declaration().value());
                externals.put(entry.getKey(),
                    declaration.toAbsolutePath().normalize().toString());
            }
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entrySource.toAbsolutePath(), outRoot, false, false, false, false,
            Backend.LUAJIT, externals,
            List.of(srcRoot.toAbsolutePath()),
            Path.of("").toAbsolutePath(), null,
            ConformanceHarnessMetadata.invocation(
                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32));
        boolean ok = orchestrator.compile();
        assertTrue("production compilation must succeed: "
            + orchestrator.diagnostics(), ok);
        return entrySource.toAbsolutePath();
    }

    /**
     * The single backend-generated entry artifact under an output root:
     * the top-level .lua (deal/ and std/ live in subdirectories).
     */
    private static Path entryArtifactOf(Path outRoot) throws IOException {
        List<Path> artifacts;
        try (Stream<Path> s = Files.list(outRoot)) {
            artifacts = s.filter(p -> p.getFileName().toString()
                .endsWith(".lua")).toList();
        }
        assertEquals("exactly one compiled entry artifact under " + outRoot,
            1, artifacts.size());
        return artifacts.get(0);
    }

    /** Compiles a fixture and pins a HostFailure with a runtime reason. */
    private void assertCompiledHostFailure(String caseName, String source,
            String exportName, String descriptor, String reason)
            throws IOException {
        assumeTrue(luajitAvailable);
        Path out = tmp.resolve("matrix-out-" + caseName);
        compileProductionEntry(tmp.resolve("matrix-src-" + caseName),
            "oracle_entry.deal", source, null, out);
        Result result = invoke(entryArtifactOf(out), exportName, descriptor);
        assertTrue("expected HostFailure for " + caseName + ", got "
            + result, result instanceof Result.HostFailure);
        assertEquals("the runtime's pinned reason verbatim, never a DEAL"
            + " code", reason, ((Result.HostFailure) result).reason());
    }

    /**
     * The Verification 4 snapshot assertion: the value JSON parses to an
     * object whose load/main/oracle fields are each 1 — order-insensitive,
     * because the production object encoder iterates pairs(v) and pins no
     * key order (std/json.lua object branch).
     */
    private static void assertExactlyOneSnapshot(Result result) {
        assertTrue("expected Value, got " + result,
            result instanceof Result.Value);
        Result.Value value = (Result.Value) result;
        assertEquals("the oracle's canonical return descriptor",
            "table", value.returnDescriptor());
        final EnvelopeJson.ObjectValue obj;
        try {
            obj = EnvelopeJson.parseObject(value.valueJson());
        } catch (EnvelopeJson.ParseException e) {
            fail("the completion JSON must parse as an object: "
                + value.valueJson());
            return;
        }
        assertEquals("exactly the three probe fields (one host-module"
            + " init, one main call, one oracle invocation)",
            Set.of("load", "main", "oracle"), obj.fields().keySet());
        for (String key : new String[] {"load", "main", "oracle"}) {
            EnvelopeJson.Value field = obj.fields().get(key);
            assertTrue(key + " must be an integral JSON number",
                field instanceof EnvelopeJson.NumberValue
                    && ((EnvelopeJson.NumberValue) field).isIntegralText());
            assertEquals(key + " is exactly 1 per invoker use", 1L,
                ((EnvelopeJson.NumberValue) field).longValue());
        }
    }

    // =========================================================================
    // Staged entry chunks (hand-written, entry-shaped: require deal.runtime,
    // publish wrapper exports, return exports; main runs at chunk end).
    // =========================================================================

    private static final String CHUNK_VALUE_NULL = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->null", function()
          return __rt.async_start(function()
            return __rt.__NULL
          end)
        end)
        return exports
        """;

    private static final String CHUNK_VALUE_42 = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function()
            return 42
          end)
        end)
        return exports
        """;

    private static final String CHUNK_DEAL_ERROR_ORACLE = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function()
            error(__rt._err("E8005", "integer division by zero",
                "staged.deal", 7, 19))
          end)
        end)
        return exports
        """;

    private static final String CHUNK_DEAL_ERROR_MAIN = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.main = __rt.function_("()->null", function()
          error(__rt._err("E8004", "int out of range", "staged.deal", 3, 9))
        end)
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function() return 1 end)
        end)
        exports.main.f()
        return exports
        """;

    private static final String CHUNK_DEAL_ERROR_NO_LOCATION = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function()
            return "not an int"
          end)
        end)
        return exports
        """;

    private static final String CHUNK_EMPTY_EXPORTS = """
        local __rt = require("deal.runtime")
        local exports = {}
        return exports
        """;

    private static final String CHUNK_SYNC = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("()->int", function() return 1 end)
        return exports
        """;

    private static final String CHUNK_PARAMETERIZED = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async(int)->int", function(x)
          return __rt.async_start(function() return x end)
        end)
        return exports
        """;

    private static final String CHUNK_DESCRIPTOR_MISMATCH = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->string", function()
          return __rt.async_start(function() return "x" end)
        end)
        return exports
        """;

    private static final String CHUNK_DUPLICATE = """
        local __rt = require("deal.runtime")
        local exports = {}
        local w = __rt.function_("async()->int", function()
          return __rt.async_start(function() return 1 end)
        end)
        exports.oracle = w
        exports.alias = w
        return exports
        """;

    private static final String CHUNK_NON_WRAPPER = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = 42
        return exports
        """;

    private static final String CHUNK_NON_OPERATION = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->int", function() return 42 end)
        return exports
        """;

    private static final String CHUNK_BYTES = """
        local __rt = require("deal.runtime")
        local exports = {}
        exports.oracle = __rt.function_("async()->bytes", function()
          return __rt.async_start(function()
            return __rt.bytes_new(2)
          end)
        end)
        return exports
        """;

    private static final String CHUNK_INTERLEAVING = """
        local __rt = require("deal.runtime")
        local console = require("std.console")
        console.log.f("user stdout before envelope")
        console.error.f("user stderr line")
        local exports = {}
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function() return 42 end)
        end)
        return exports
        """;

    /** One load/main/oracle probe marker line per execution. */
    private static final String CHUNK_PROBE = """
        local __rt = require("deal.runtime")
        local probe = assert(io.open("@PROBE@", "a"))
        probe:write("load\\n")
        probe:close()
        local exports = {}
        exports.main = __rt.function_("()->null", function()
          local p = assert(io.open("@PROBE@", "a"))
          p:write("main\\n")
          p:close()
          return __rt.__NULL
        end)
        exports.oracle = __rt.function_("async()->int", function()
          return __rt.async_start(function()
            local p = assert(io.open("@PROBE@", "a"))
            p:write("oracle\\n")
            p:close()
            return 42
          end)
        end)
        exports.main.f()
        return exports
        """;

    private static String probeChunk(Path probeFile) {
        return CHUNK_PROBE.replace("@PROBE@",
            probeFile.toString().replace("\\", "\\\\"));
    }

    // =========================================================================
    // =========================================================================
    // Production-path verification matrix: compilation through
    // CompilationOrchestrator, invocation through the production
    // invoker, grep gates.
    // =========================================================================

    @Test
    public void productionCompiledAsyncOracleCompletingNullReturnsExactValue()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("smoke-out");
        compileProductionEntry(tmp.resolve("smoke-src"),
            "oracle_entry.deal", """
                export async function oracle(): null { return null; }
                export function main(): null { return null; }
                """, null, out);

        Path entryArtifact = entryArtifactOf(out);
        Result result = invoke(entryArtifact, "oracle", "null");
        assertEquals("the parent D9 scenario: null completion, byte-exact"
            + " descriptor", new Result.Value("null", "null"), result);

        // Release gates: no generated artifact references the runtime
        // entry or the driver marker; async exports emit the same wrapper
        // shape as sync exports.
        String generated = Files.readString(entryArtifact);
        assertFalse("generated artifacts never call the runtime entry",
            generated.contains("invoke_async_export"));
        assertFalse("generated artifacts never emit the driver marker",
            generated.contains(MARKER));
        assertTrue("async export emits the canonical async wrapper sig",
            generated.contains("\"async()->null\""));
        assertTrue("main emits the sync wrapper sig",
            generated.contains("\"()->null\""));
    }

    @Test
    public void productionCompiledAsyncFortyTwoReturnsExactIntValue()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("smoke-out-42");
        compileProductionEntry(tmp.resolve("smoke-src-42"),
            "oracle_entry.deal", """
                export async function fortyTwo(): int { return 42; }
                export function main(): null { return null; }
                """, null, out);

        Result result = invoke(entryArtifactOf(out), "fortyTwo", "int");
        assertEquals("byte-exact descriptor and exact value JSON",
            new Result.Value("int", "42"), result);
    }

    @Test
    public void generatedArtifactsNeverReachTheRuntimeEntryOrTheDriverMarker()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("gate-out");
        compileProductionEntry(tmp.resolve("gate-src"),
            "oracle_entry.deal", """
                export async function oracle(): null { return null; }
                export async function parameterized(x: int): int {
                  return x;
                }
                export function main(): null { return null; }
                """, null, out);

        // The grep gate (Verification 5): no backend-generated artifact
        // references the runtime entry or the driver marker. The copied
        // deal/runtime.lua and std/ trees are distribution files (the
        // runtime entry legitimately lives there), not generated
        // artifacts.
        try (Stream<Path> walk = Files.walk(out)) {
            for (Path p : walk.toList()) {
                if (!p.getFileName().toString().endsWith(".lua")) {
                    continue;
                }
                Path rel = out.relativize(p);
                if (rel.getNameCount() > 0) {
                    String first = rel.getName(0).toString();
                    if (first.equals("deal") || first.equals("std")) {
                        continue;
                    }
                }
                String text = Files.readString(p);
                assertFalse("generated artifacts never call the runtime"
                    + " entry: " + p, text.contains("invoke_async_export"));
                assertFalse("generated artifacts never emit the driver"
                    + " marker: " + p, text.contains(MARKER));
            }
        }

        // Async exports emit the same single-wrapper-table shape as sync
        // exports with a byte-exact canonical sig, and the E6004 entry
        // gate keeps the chunk-end main call.
        String generated = Files.readString(entryArtifactOf(out));
        assertTrue("async export emits the canonical async wrapper sig",
            generated.contains("__rt.function_(\"async()->null\", function()"));
        assertTrue("parameterized async export emits the canonical"
            + " parameterized wrapper sig",
            generated.contains("__rt.function_(\"async(int)->int\", function(x)"));
        assertTrue("main emits the same single-wrapper-table shape",
            generated.contains("__rt.function_(\"()->null\", function()"));
        assertTrue("the E6004 entry gate emits the chunk-end main call",
            generated.contains("exports.main.f()"));
    }

    // =========================================================================
    // The parent D9 production scenario: an async()->null oracle that
    // assigns and containerizes legal first-class async(bytes)->bytes
    // values, invokes and awaits one, checks bytes identity/content in
    // source, and completes null (ISSUE-0161, E6 bytes composition).
    // =========================================================================

    @Test
    public void productionCompiledAsyncBytesOracleCompletesNull()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("bytes-oracle-out");
        compileProductionEntry(tmp.resolve("bytes-oracle-src"),
            "oracle_entry.deal", """
                async function echo(b: bytes): bytes {
                  return b;
                }
                async function fill(b: bytes): bytes {
                  b[1] = 200;
                  return b;
                }
                export function main(): null {
                  return null;
                }
                export async function oracle(): null {
                  let handlers: (async (b: bytes) => bytes)[] = [];
                  handlers[handlers.length] = echo;
                  handlers[handlers.length] = fill;
                  let buf: bytes = bytes(3);
                  buf[0] = 7;
                  let through: bytes = await handlers[0](buf);
                  through[2] = 9;
                  if (buf[2] !== 9) {
                    throw { code: "TEST_FAIL",
                      message: "async bytes identity lost" };
                  }
                  let filled: bytes = await handlers[1](through);
                  if (filled[0] !== 7 || filled[1] !== 200
                      || filled.length !== 3) {
                    throw { code: "TEST_FAIL",
                      message: "async bytes content mismatch" };
                  }
                  return null;
                }
                """, null, out);

        Path entryArtifact = entryArtifactOf(out);
        String generated = Files.readString(entryArtifact);
        assertTrue("the oracle assigns first-class async bytes function"
            + " values with the byte-exact canonical sig",
            generated.contains("\"async(bytes)->bytes\""));

        Result result = invoke(entryArtifact, "oracle", "null");
        assertEquals("the oracle invokes and awaits one async bytes"
            + " function, checks identity and content, and completes null",
            new Result.Value("null", "null"), result);
    }

    @Test
    public void noAwaitBytesOracleFailsCompilationProvingTheAwaitIsReal()
            throws IOException {
        // The no-await mutation control: removing await leaves an
        // un-awaited async call, which the checker rejects (E3014) — the
        // production scenario cannot pass by skipping the await.
        Path out = tmp.resolve("bytes-oracle-noawait-out");
        compileExpectingFailure(tmp.resolve("bytes-oracle-noawait-src"),
            "oracle_entry.deal", """
                async function echo(b: bytes): bytes {
                  return b;
                }
                export function main(): null {
                  return null;
                }
                export async function oracle(): null {
                  let handlers: (async (b: bytes) => bytes)[] = [echo];
                  handlers[0](bytes(1));
                  return null;
                }
                """, out, "E3014");
    }

    @Test
    public void incorrectBytesOutputMakesTheOracleFailWithItsOwnDealError()
            throws Exception {
        assumeTrue(luajitAvailable);
        // The incorrect-output mutation control: the awaited handler
        // returns different content, so the oracle's own assertion throws
        // TEST_FAIL and the invoker propagates that exact DEAL error — a
        // wrong bytes result can never become a successful value.
        Path out = tmp.resolve("bytes-oracle-bad-out");
        compileProductionEntry(tmp.resolve("bytes-oracle-bad-src"),
            "oracle_entry.deal", """
                async function echo(b: bytes): bytes {
                  return b;
                }
                async function fill(b: bytes): bytes {
                  b[1] = 201;
                  return b;
                }
                export function main(): null {
                  return null;
                }
                export async function oracle(): null {
                  let handlers: (async (b: bytes) => bytes)[] = [echo, fill];
                  let buf: bytes = bytes(3);
                  buf[0] = 7;
                  let through: bytes = await handlers[0](buf);
                  let filled: bytes = await handlers[1](through);
                  if (filled[0] !== 7 || filled[1] !== 200
                      || filled.length !== 3) {
                    throw { code: "TEST_FAIL",
                      message: "async bytes content mismatch" };
                  }
                  return null;
                }
                """, null, out);
        Result result = invoke(entryArtifactOf(out), "oracle", "null");
        assertTrue("the oracle's own TEST_FAIL propagates: " + result,
            result instanceof Result.DealError);
        Result.DealError error = (Result.DealError) result;
        assertEquals("TEST_FAIL", error.code());
        assertEquals("async bytes content mismatch", error.message());
        assertTrue("the raise location propagates from source",
            error.file() != null
                && error.file().endsWith("oracle_entry.deal"));
    }

    @Test
    public void freshBufferEchoMakesTheOracleFailOnBytesIdentity()
            throws Exception {
        assumeTrue(luajitAvailable);
        // The identity mutation control: the awaited handler returns a
        // fresh buffer instead of the same reference, so the
        // alias-observed mutation never reaches the caller buffer — the
        // oracle's identity assertion throws TEST_FAIL.
        Path out = tmp.resolve("bytes-oracle-identity-out");
        compileProductionEntry(tmp.resolve("bytes-oracle-identity-src"),
            "oracle_entry.deal", """
                async function echo(b: bytes): bytes {
                  return bytes(b.length);
                }
                export function main(): null {
                  return null;
                }
                export async function oracle(): null {
                  let handlers: (async (b: bytes) => bytes)[] = [echo];
                  let buf: bytes = bytes(3);
                  let through: bytes = await handlers[0](buf);
                  through[2] = 9;
                  if (buf[2] !== 9) {
                    throw { code: "TEST_FAIL",
                      message: "async bytes identity lost" };
                  }
                  return null;
                }
                """, null, out);
        Result result = invoke(entryArtifactOf(out), "oracle", "null");
        assertTrue("the oracle's identity assertion propagates: " + result,
            result instanceof Result.DealError);
        Result.DealError error = (Result.DealError) result;
        assertEquals("TEST_FAIL", error.code());
        assertEquals("async bytes identity lost", error.message());
        assertTrue("the raise location propagates from source",
            error.file() != null
                && error.file().endsWith("oracle_entry.deal"));
    }

    @Test
    public void noCallBytesOracleFailsWithItsOwnDealError()
            throws Exception {
        assumeTrue(luajitAvailable);
        // The no-call mutation control: the oracle assigns and
        // containerizes the first-class async bytes handler but never
        // invokes it, so the call-observed mutation never happens and the
        // oracle's own guard throws TEST_FAIL — the production scenario
        // can never complete null by skipping the call, and the invoker
        // propagates the oracle's exact DEAL error.
        Path out = tmp.resolve("bytes-oracle-nocall-out");
        compileProductionEntry(tmp.resolve("bytes-oracle-nocall-src"),
            "oracle_entry.deal", """
                async function fill(b: bytes): bytes {
                  b[1] = 200;
                  return b;
                }
                export function main(): null {
                  return null;
                }
                export async function oracle(): null {
                  let handlers: (async (b: bytes) => bytes)[] = [fill];
                  let buf: bytes = bytes(3);
                  if (buf[1] !== 200) {
                    throw { code: "TEST_FAIL",
                      message: "async bytes function was never invoked" };
                  }
                  return null;
                }
                """, null, out);
        Result result = invoke(entryArtifactOf(out), "oracle", "null");
        assertTrue("the no-call guard propagates: " + result,
            result instanceof Result.DealError);
        Result.DealError error = (Result.DealError) result;
        assertEquals("TEST_FAIL", error.code());
        assertEquals("async bytes function was never invoked",
            error.message());
        assertTrue("the raise location propagates from source",
            error.file() != null
                && error.file().endsWith("oracle_entry.deal"));
    }

    /**
     * Compiles a fixture expected to fail with the given diagnostic code
     * (the mutation-control compilation gate): a clean compile fails the
     * assertion, and any diagnostic besides the pinned code is reported.
     */
    private static void compileExpectingFailure(Path projectDir,
            String entryFileName, String source, Path outRoot,
            String expectedCode) throws IOException {
        Path srcRoot = projectDir.resolve("src");
        Files.createDirectories(srcRoot);
        Path entrySource = srcRoot.resolve(entryFileName);
        Files.writeString(entrySource, source);
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entrySource.toAbsolutePath(), outRoot, false, false, false, false,
            Backend.LUAJIT, null,
            List.of(srcRoot.toAbsolutePath()),
            Path.of("").toAbsolutePath(), null,
            ConformanceHarnessMetadata.invocation(
                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32));
        boolean ok = orchestrator.compile();
        assertFalse("the mutation control must fail compilation: "
            + orchestrator.diagnostics(), ok);
        assertTrue("the pinned diagnostic " + expectedCode + " fires",
            orchestrator.diagnostics().stream()
                .anyMatch(d -> d.code().equals(expectedCode)));
    }

    // =========================================================================
    // Value mapping (staged component tests)
    // =========================================================================

    @Test
    public void stagedNullCompletionReturnsExactValueJson() throws Exception {
        assumeTrue(luajitAvailable);
        assertEquals(new Result.Value("null", "null"),
            invoke(defaultEntry, "oracle", "null"));
    }

    @Test
    public void stagedScalarCompletionReturnsExactValueJson() throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("value_42", CHUNK_VALUE_42);
        assertEquals(new Result.Value("int", "42"),
            invoke(entry, "oracle", "int"));
    }

    // =========================================================================
    // DEAL error propagation
    // =========================================================================

    @Test
    public void dealErrorFromOperationPropagatesCodeMessageLocationUnchanged()
            throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("deal_error_oracle", CHUNK_DEAL_ERROR_ORACLE);
        Result result = invoke(entry, "oracle", "int");
        assertEquals(new Result.DealError("E8005", "integer division by zero",
            "staged.deal", 7, 19), result);
    }

    @Test
    public void dealErrorFromMainPropagatesVerbatim() throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("deal_error_main", CHUNK_DEAL_ERROR_MAIN);
        Result result = invoke(entry, "oracle", "int");
        assertEquals(new Result.DealError("E8004", "int out of range",
            "staged.deal", 3, 9), result);
    }

    @Test
    public void dealErrorAbsentLocationFieldsStayNull() throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("deal_error_no_location",
            CHUNK_DEAL_ERROR_NO_LOCATION);
        Result result = invoke(entry, "oracle", "int");
        assertEquals("the completion-matcher failure carries no location",
            new Result.DealError("E8001", "expected int", null, null, null),
            result);
    }

    // =========================================================================
    // Compiled DEAL-error fixtures (Verification 2)
    // =========================================================================

    @Test
    public void productionCompiledOracleDivisionByZeroPropagatesPinnedLocation()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("matrix-out-e8005");
        Path entrySource = compileProductionEntry(tmp.resolve("matrix-src-e8005"),
            "oracle_entry.deal", """
                export async function oracle(): int {
                  return 1 / 0;
                }
                export function main(): null {
                  return null;
                }
                """, null, out);

        Result result = invoke(entryArtifactOf(out), "oracle", "int");
        assertEquals("code/message/file/line/column propagate unchanged",
            new Result.DealError("E8005", "integer division by zero",
                entrySource.toString(), 2, 10), result);
    }

    @Test
    public void productionCompiledMainIntOverflowPropagatesPinnedLocation()
            throws Exception {
        assumeTrue(luajitAvailable);

        Path out = tmp.resolve("matrix-out-e8004-main");
        Path entrySource = compileProductionEntry(
            tmp.resolve("matrix-src-e8004-main"),
            "oracle_entry.deal", """
                export async function oracle(): int {
                  return 1;
                }
                export function main(): null {
                  let x: int = 2147483647;
                  x = x + 1;
                  return null;
                }
                """, null, out);

        Result result = invoke(entryArtifactOf(out), "oracle", "int");
        assertEquals("main's DEAL error propagates verbatim",
            new Result.DealError("E8004", "int out of safe range",
                entrySource.toString(), 6, 7), result);
    }

    // =========================================================================
    // HostInvocationFailure mapping (runtime-pinned reasons, never a DEAL code)
    // =========================================================================

    private void assertHostFailure(String chunkName, String chunk,
                                   String descriptor, String reason)
            throws IOException {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("host_" + chunkName, chunk);
        Result result = invoke(entry, "oracle", descriptor);
        assertTrue("expected HostFailure for " + chunkName + ", got "
            + result, result instanceof Result.HostFailure);
        assertEquals(reason, ((Result.HostFailure) result).reason());
    }

    @Test
    public void missingExportReturnsPinnedHostFailureReason() throws Exception {
        assertHostFailure("missing", CHUNK_EMPTY_EXPORTS, "int",
            "missing export 'oracle'");
    }

    @Test
    public void syncExportReturnsPinnedHostFailureReason() throws Exception {
        assertHostFailure("sync", CHUNK_SYNC, "int",
            "export 'oracle' is sync: expected 'async()->int',"
                + " got '()->int'");
    }

    @Test
    public void parameterizedExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertHostFailure("parameterized", CHUNK_PARAMETERIZED, "int",
            "export 'oracle' is parameterized: expected 'async()->int',"
                + " got 'async(int)->int'");
    }

    @Test
    public void descriptorMismatchedExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertHostFailure("descriptor_mismatch", CHUNK_DESCRIPTOR_MISMATCH,
            "int",
            "export 'oracle' signature mismatch: expected 'async()->int',"
                + " got 'async()->string'");
    }

    @Test
    public void duplicateExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertHostFailure("duplicate", CHUNK_DUPLICATE, "int",
            "duplicate export 'oracle': the same wrapper appears under"
                + " multiple export keys");
    }

    @Test
    public void nonWrapperExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertHostFailure("non_wrapper", CHUNK_NON_WRAPPER, "int",
            "export 'oracle' is not a function wrapper");
    }

    @Test
    public void nonOperationExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertHostFailure("non_operation", CHUNK_NON_OPERATION, "int",
            "export 'oracle' did not produce an async operation");
    }

    @Test
    public void nonCanonicalDescriptorPassesVerbatimToTheRuntimeHalf()
            throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("host_non_canonical_descriptor",
            CHUNK_EMPTY_EXPORTS);
        Result result = invoke(entry, "oracle", "int[]");
        assertTrue("a non-canonical descriptor maps to the runtime's pinned"
            + " host-failure reason, never a driver-side hard failure: "
            + result, result instanceof Result.HostFailure);
        assertEquals("return descriptor is not a canonical descriptor: int[]",
            ((Result.HostFailure) result).reason());
    }

    // =========================================================================
    // Compiled HostInvocationFailure fixtures (Verification 3)
    // =========================================================================

    @Test
    public void productionCompiledMissingExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertCompiledHostFailure("missing", """
            export async function oracle(): int { return 1; }
            export function main(): null { return null; }
            """, "nope", "int", "missing export 'nope'");
    }

    @Test
    public void productionCompiledSyncExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertCompiledHostFailure("sync", """
            export function runner(): null { return null; }
            export function main(): null { return null; }
            """, "runner", "null",
            "export 'runner' is sync: expected 'async()->null',"
                + " got '()->null'");
    }

    @Test
    public void productionCompiledParameterizedExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertCompiledHostFailure("parameterized", """
            export async function takes(x: int): int { return x; }
            export function main(): null { return null; }
            """, "takes", "int",
            "export 'takes' is parameterized: expected 'async()->int',"
                + " got 'async(int)->int'");
    }

    @Test
    public void productionCompiledDescriptorMismatchedExportReturnsPinnedHostFailureReason()
            throws Exception {
        assertCompiledHostFailure("descriptor_mismatch", """
            export async function oracle(): string { return "x"; }
            export function main(): null { return null; }
            """, "oracle", "int",
            "export 'oracle' signature mismatch: expected 'async()->int',"
                + " got 'async()->string'");
    }

    // =========================================================================
    // Hard failures: infrastructure / containment / representation
    // =========================================================================

    @Test
    public void missingEntryArtifactFailsBeforeAnySpawn() {
        LuaJitAsyncExportInvocationException e = expectInvocationFailure(
            root.resolve("entries").resolve("does_not_exist.lua"),
            "oracle", "null");
        assertTrue("hard-failure reason names the missing artifact: "
            + e.getMessage(), e.getMessage().contains("entry artifact not"
            + " found"));
        assertNull("no process ran, so no output was captured", e.stdout());
        assertNull(e.stderr());
    }

    @Test
    public void entryWithoutRuntimeMarkerFailsBeforeAnySpawn()
            throws Exception {
        Path bare = Files.createDirectories(tmp.resolve("bare"));
        Path entry = bare.resolve("entry.lua");
        Files.writeString(entry, CHUNK_VALUE_42);
        LuaJitAsyncExportInvocationException e = expectInvocationFailure(
            entry, "oracle", "int");
        assertTrue("hard-failure reason names the missing marker: "
            + e.getMessage(), e.getMessage().contains("no deployment root"
            + " found"));
        assertNull(e.stdout());
        assertNull(e.stderr());
    }

    @Test
    public void missingDriverResourceFailsBeforeAnySpawn() throws Exception {
        LuaJitAsyncExportInvoker invoker = new MissingDriverInvoker();
        try {
            invoker.invoke(new AsyncExportInvocationRequest(defaultEntry,
                "oracle", "null"));
        } catch (LuaJitAsyncExportInvocationException e) {
            assertTrue("hard-failure reason names the missing driver: "
                + e.getMessage(), e.getMessage().contains("driver resource"
                + " not found"));
            assertNull(e.stdout());
            assertNull(e.stderr());
            return;
        }
        fail("expected LuaJitAsyncExportInvocationException");
    }

    @Test
    public void bytesCompletionIsAValueRepresentationHardFailure()
            throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("bytes", CHUNK_BYTES);
        LuaJitAsyncExportInvocationException e = expectInvocationFailure(
            entry, "oracle", "bytes");
        assertTrue("the hard failure names the representation failure: "
            + e.getMessage(),
            e.getMessage().contains("value-representation failure"));
        String output = e.capturedOutput();
        assertNotNull("captured process output is attached", output);
        assertTrue("the captured envelope pins the encoder reason: " + output,
            output.contains("representation-failure")
                && output.contains("unsupported type for JSON encoding:"
                + " bytes"));
        assertFalse("an encoding failure is never an expected DEAL code",
            output.contains("deal-error"));
    }

    @Test
    public void userConsoleOutputNeverCorruptsTheEnvelopeFrame()
            throws Exception {
        assumeTrue(luajitAvailable);
        Path entry = writeEntry("interleaving", CHUNK_INTERLEAVING);
        assertEquals("user output on both streams leaves the value envelope"
            + " intact", new Result.Value("int", "42"),
            invoke(entry, "oracle", "int"));
    }

    // =========================================================================
    // Fake-driver hard-failure matrix (codec and exit-code fail-closedness)
    // =========================================================================

    private static Path writeFakeDriver(String envelopeLine, int exitCode)
            throws IOException {
        Path driver = Files.createTempFile(tmp, "fake-driver-", ".lua");
        Files.writeString(driver,
            "io.write([==[" + envelopeLine + "]==], \"\\n\")\n"
                + "io.flush()\nos.exit(" + exitCode + ")\n");
        return driver;
    }

    private static LuaJitAsyncExportInvocationException invokeFakeDriver(
            String envelopeLine, int exitCode) throws IOException {
        Path driver = writeFakeDriver(envelopeLine, exitCode);
        LuaJitAsyncExportInvoker invoker = new FakeDriverInvoker(driver);
        try {
            invoker.invoke(new AsyncExportInvocationRequest(defaultEntry,
                "oracle", "null"));
        } catch (LuaJitAsyncExportInvocationException e) {
            return e;
        }
        fail("expected LuaJitAsyncExportInvocationException for: "
            + envelopeLine);
        return null;
    }

    @Test
    public void infrastructureFailureEnvelopeIsAHardFailure()
            throws Exception {
        assumeTrue(luajitAvailable);
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            MARKER + "{\"status\":\"infrastructure-failure\","
                + "\"reason\":\"boom\"}", 1);
        assertTrue("an infrastructure-failure envelope is a hard failure"
            + " regardless of the exit code: " + e.getMessage(),
            e.getMessage().contains("infrastructure failure")
                && e.getMessage().contains("boom"));
        String output = e.capturedOutput();
        assertNotNull(output);
        assertTrue("captured output carries the envelope reason: " + output,
            output.contains("boom"));
    }

    @Test
    public void noEnvelopeLineIsAHardFailure() throws Exception {
        assumeTrue(luajitAvailable);
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            "some unrelated stdout", 1);
        assertTrue("a missing envelope is a hard failure: " + e.getMessage(),
            e.getMessage().contains("no " + MARKER + " envelope line"));
        assertTrue("captured stdout is attached", e.capturedOutput()
            .contains("some unrelated stdout"));
    }

    @Test
    public void unknownStatusIsRejected() throws Exception {
        assumeTrue(luajitAvailable);
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            MARKER + "{\"status\":\"bogus\"}", 0);
        assertTrue("an unknown status is rejected: " + e.getMessage(),
            e.getMessage().contains("unknown envelope status: bogus"));
    }

    @Test
    public void unknownFieldIsRejected() throws Exception {
        assumeTrue(luajitAvailable);
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            MARKER + "{\"status\":\"value\",\"descriptor\":\"null\","
                + "\"value\":\"42\",\"extra\":1}", 0);
        assertTrue("an unknown field is rejected: " + e.getMessage(),
            e.getMessage().contains("malformed async-export envelope"));
    }

    @Test
    public void malformedEnvelopeJsonIsRejected() throws Exception {
        assumeTrue(luajitAvailable);
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            MARKER + "{not json", 0);
        assertTrue("malformed envelope text is rejected: " + e.getMessage(),
            e.getMessage().contains("malformed async-export envelope"));
    }

    @Test
    public void nonIntegralLineFieldIsRejectedEvenThoughTheDecimalParses()
            throws Exception {
        assumeTrue(luajitAvailable);
        // %.17g fractional text parses as a conventional decimal number
        // at the reader level but fails the closed envelope schema for an
        // integer location field.
        LuaJitAsyncExportInvocationException e = invokeFakeDriver(
            MARKER + "{\"status\":\"deal-error\",\"code\":\"E8005\","
                + "\"message\":\"m\",\"line\":0.10000000000000001}", 0);
        assertTrue("a non-integral line is a malformed envelope: "
            + e.getMessage(), e.getMessage().contains("malformed"
            + " async-export envelope"));
    }

    // =========================================================================
    // Codec unit tests (the strict conventional-JSON reader, D6)
    // =========================================================================

    @Test
    public void codecParsesConventionalDecimalNumbers() {
        EnvelopeJson.Value v = EnvelopeJson.parseValue(
            "{\"a\":0.10000000000000001,\"b\":42,\"c\":-3,\"d\":1.5e2}");
        EnvelopeJson.ObjectValue obj = (EnvelopeJson.ObjectValue) v;

        EnvelopeJson.NumberValue a = (EnvelopeJson.NumberValue)
            obj.fields().get("a");
        assertEquals("%.17g fractional text is preserved byte-exactly",
            "0.10000000000000001", a.token());
        assertFalse("fractional tokens are not integral",
            a.isIntegralText());

        EnvelopeJson.NumberValue b = (EnvelopeJson.NumberValue)
            obj.fields().get("b");
        assertEquals("42", b.token());
        assertTrue(b.isIntegralText());
        assertEquals(42L, b.longValue());

        EnvelopeJson.NumberValue c = (EnvelopeJson.NumberValue)
            obj.fields().get("c");
        assertEquals("-3", c.token());
        assertTrue(c.isIntegralText());

        EnvelopeJson.NumberValue d = (EnvelopeJson.NumberValue)
            obj.fields().get("d");
        assertEquals("exponent text is preserved", "1.5e2", d.token());

        assertEquals("a bare conventional decimal parses",
            "0.10000000000000001",
            ((EnvelopeJson.NumberValue)
                EnvelopeJson.parseValue("0.10000000000000001")).token());
    }

    @Test
    public void codecRoundTripsEmbeddedEscapedStrings() {
        String bs = "\\";
        String json = "{\"s\":\"a" + bs + "n" + "b" + bs + "t" + bs + "\""
            + "c" + bs + bs + "d" + bs + "/e" + bs + "u0041" + bs + "u00e9"
            + bs + "ud83d" + bs + "ude00\"}";
        EnvelopeJson.Value v = EnvelopeJson.parseValue(json);
        EnvelopeJson.StringValue s = (EnvelopeJson.StringValue)
            ((EnvelopeJson.ObjectValue) v).fields().get("s");
        assertEquals("escaped strings round-trip byte-exactly (including"
            + " the surrogate pair)", "a\nb\t\"c\\d/eA\u00e9\ud83d\ude00",
            s.text());
    }

    @Test
    public void codecRejectsMalformedText() {
        String[] malformed = {
            "{\"a\":1,}",               // trailing comma
            "{\"a\":1,\"a\":2}",        // duplicate key
            "{\"a\":01}",               // leading zero
            "{\"a\":1.}",               // fraction without digits
            "{\"a\":.5}",               // bare fraction
            "{\"a\":+1}",               // leading plus
            "{\"s\":\"\\x\"}",          // invalid escape
            "{\"s\":\"\\ud800\"}",      // unpaired high surrogate
            "{\"s\":\"\\udc00\"}",      // unpaired low surrogate
            "{\"s\":\"raw\u0001ctl\"}", // raw control character
            "{} trailing",              // trailing content
            "[1]",                      // arrays are outside the schema
            "{\"a\":NaN}",              // non-JSON number
        };
        for (String text : malformed) {
            try {
                EnvelopeJson.parseValue(text);
                fail("expected ParseException for: " + text);
            } catch (EnvelopeJson.ParseException expected) {
            }
        }
    }

    // =========================================================================
    // Exactly one process per invoke / no retry / temp-dir cleanup
    // =========================================================================

    @Test
    public void twoConsecutiveInvokesEachSpawnOneFreshProcessWithExactlyOnceInitMainOracle()
            throws Exception {
        assumeTrue(luajitAvailable);
        Path probe = tmp.resolve("probe_once.txt");
        Path entry = writeEntry("exactly_once", probeChunk(probe));

        Set<String> before = invokerTempDirs();

        assertEquals(new Result.Value("int", "42"),
            invoke(entry, "oracle", "int"));
        assertEquals("one module load, one chunk-end main call, one oracle"
            + " invocation in one runtime instance",
            "load\nmain\noracle\n", Files.readString(probe));
        assertNoTempDirLeaks(before);

        assertEquals(new Result.Value("int", "42"),
            invoke(entry, "oracle", "int"));
        assertEquals("the second invoke spawns one fresh process with its"
            + " own exactly-once sequence",
            "load\nmain\noracle\nload\nmain\noracle\n",
            Files.readString(probe));
        assertNoTempDirLeaks(before);
    }

    // =========================================================================
    // Compiled host-probe exactly-once fixture (Verification 4)
    // =========================================================================

    @Test
    public void productionCompiledHostProbeRunsExactlyOncePerInvoke()
            throws Exception {
        assumeTrue(luajitAvailable);

        // Staged host probe declaration (host-module-abi frozen seam —
        // the same raw-function module shape as
        // test/conformance/host-fixtures/cfg.lua): mainTouch/oracleTouch
        // bump per-invocation counters and snapshot() returns the plain
        // {load, main, oracle} table the oracle completes.
        Path projectDir = Files.createDirectories(tmp.resolve("probe-src"));
        Files.writeString(projectDir.resolve("probe.d.deal"), """
            export function mainTouch(): null;
            export function oracleTouch(): null;
            export function snapshot(): table;
            """);
        Path out = tmp.resolve("probe-out");
        compileProductionEntry(projectDir, "oracle_entry.deal", """
            import * as probe from "host/probe"

            export function main(): null {
              probe.mainTouch();
              return null;
            }

            export async function oracle(): table {
              probe.oracleTouch();
              return probe.snapshot();
            }
            """, """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "externals": {
                "host/probe": { "declaration": "probe.d.deal" }
              }
            }
            """, out);

        // The deployment root carries the staged host implementation at
        // host/probe.lua (the driver's package.path resolves the raw
        // slash-form require verbatim).
        Path hostDir = Files.createDirectories(out.resolve("host"));
        Files.writeString(hostDir.resolve("probe.lua"), """
            local rt = require("deal.runtime")
            local load = 1
            local main = 0
            local oracle = 0
            return {
              mainTouch = function() main = main + 1 return rt.__NULL end,
              oracleTouch = function() oracle = oracle + 1 return rt.__NULL end,
              snapshot = function()
                return { load = load, main = main, oracle = oracle }
              end,
            }
            """);

        Path entryArtifact = entryArtifactOf(out);
        String generated = Files.readString(entryArtifact);
        assertFalse("the probe artifact never references the runtime entry",
            generated.contains("invoke_async_export"));
        assertFalse("the probe artifact never emits the driver marker",
            generated.contains(MARKER));

        Set<String> before = invokerTempDirs();

        // Two consecutive invokes each spawn one fresh runtime instance:
        // one host-module init, one entry init + chunk-end main call,
        // and one oracle invocation inside it (load/main/oracle = 1).
        Result first = invoke(entryArtifact, "oracle", "table");
        assertExactlyOneSnapshot(first);
        assertNoTempDirLeaks(before);

        Result second = invoke(entryArtifact, "oracle", "table");
        assertExactlyOneSnapshot(second);
        assertNoTempDirLeaks(before);
    }

    @Test
    public void concurrentInvokesAreIsolatedProcesses() throws Exception {
        assumeTrue(luajitAvailable);
        Path probeA = tmp.resolve("probe_a.txt");
        Path probeB = tmp.resolve("probe_b.txt");
        Path entryA = writeEntry("conc_a", probeChunk(probeA));
        Path entryB = writeEntry("conc_b", probeChunk(probeB));

        ExecutorService pool = Executors.newFixedThreadPool(2);
        try {
            Future<Result> fa = pool.submit(() -> invoke(entryA, "oracle",
                "int"));
            Future<Result> fb = pool.submit(() -> invoke(entryB, "oracle",
                "int"));
            assertEquals(new Result.Value("int", "42"), fa.get());
            assertEquals(new Result.Value("int", "42"), fb.get());
        } finally {
            pool.shutdownNow();
        }
        assertEquals("each concurrent invoke owns its own process",
            "load\nmain\noracle\n", Files.readString(probeA));
        assertEquals("each concurrent invoke owns its own process",
            "load\nmain\noracle\n", Files.readString(probeB));
    }

    // =========================================================================
    // API shape pins
    // =========================================================================

    @Test
    public void resultHasExactlyThreePermittedVariants() {
        Set<String> names = Arrays.stream(Result.class.getPermittedSubclasses())
            .map(Class::getSimpleName).collect(Collectors.toSet());
        assertEquals("the sealed result admits exactly the three pinned"
            + " variants and no others", Set.of("Value", "DealError",
            "HostFailure"), names);
    }

    @Test(expected = NullPointerException.class)
    public void requestRejectsNullEntryArtifact() {
        new AsyncExportInvocationRequest(null, "oracle", "null");
    }

    @Test(expected = NullPointerException.class)
    public void requestRejectsNullExportName() {
        new AsyncExportInvocationRequest(Path.of("e.lua"), null, "null");
    }

    @Test(expected = NullPointerException.class)
    public void requestRejectsNullReturnDescriptor() {
        new AsyncExportInvocationRequest(Path.of("e.lua"), "oracle", null);
    }

    @Test
    public void theDriverResourceIsTheOnlyHostSurfaceThatReachesTheRuntimeEntry()
            throws IOException {
        String driver = Files.readString(
            Path.of(LuaJitAsyncExportInvoker.DRIVER_RESOURCE));
        assertTrue("the committed driver owns the runtime-entry call",
            driver.contains("__rt.invoke_async_export"));
        // No production Java source reaches the runtime entry: the
        // invoker's own file may name it only in its contract Javadoc.
        try (Stream<Path> s = Files.walk(Path.of("deal"))) {
            for (Path p : s.toList()) {
                if (!p.getFileName().toString().endsWith(".java")
                        || p.getFileName().toString().equals(
                            "LuaJitAsyncExportInvoker.java")) {
                    continue;
                }
                String text = Files.readString(p);
                assertFalse(p + " must never call the runtime entry",
                    text.contains("invoke_async_export"));
            }
        }
    }

    // =========================================================================
    // Test seams: hide driver lookup sources (D1 hard-failure path)
    // =========================================================================

    /** A seam whose driver lookup returns the named file's bytes. */
    private static final class FakeDriverInvoker
            extends LuaJitAsyncExportInvoker {
        private final Path driver;

        FakeDriverInvoker(Path driver) {
            this.driver = driver;
        }

        @Override
        protected InputStream locateDriverResource() throws IOException {
            return Files.newInputStream(driver);
        }
    }

    /** A seam hiding both driver lookup sources. */
    private static final class MissingDriverInvoker
            extends LuaJitAsyncExportInvoker {
        @Override
        protected InputStream locateDriverResource() {
            return null;
        }
    }
}
