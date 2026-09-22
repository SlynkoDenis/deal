package deal.test;

import deal.Main;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.project.ProjectContext;
import deal.project.ProjectLocator;
import deal.project.ProtectedPathOps;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Comparator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * ISSUE-0270 integration gates (epic sequencing item 9, design source
 * {@code strict-project-context-resolution-identity} Verification 5-9):
 * the class-free out-of-root project on both backends, the unconditional
 * E2010 for out-of-root/rooted-declaration/stdlib-directory classes,
 * identity/determinism/privacy checks through the full pipeline, the
 * complete scalar (E1) diagnostic-range gates, and the both-backend
 * equivalence gate.
 *
 * <p>Every fixture runs the real production CLI
 * ({@link Main#run(String[])}) or a real {@code deal.Main} subprocess
 * over a temporary exact-v1.2 deployment and executes the generated
 * artifact through each backend's normal invocation (luajit {@code
 * main.lua}; javac + java {@code Main}) — never test-only isolated phase
 * APIs. Each fixture names its concrete files and its expected
 * E2010/E2003/E2009 outcome, so a broken locate (T4) -> resolution (T6)
 * -> identity (T7) -> CLI/orchestrator (T8) dependency fails the
 * corresponding fixture.</p>
 */
public class ProjectIntegrationGatesTest {

    private static int passed = 0;
    private static int failed = 0;

    /** The emitted private module-artifact names: m + 16 lowercase hex. */
    private static final Pattern LUA_MODULE_ID =
        Pattern.compile("m[0-9a-f]{16}\\.lua");
    private static final Pattern JVM_MODULE_ID =
        Pattern.compile("M[0-9a-f]{16}\\.java");

    /**
     * Double-quoted string literals in emitted artifacts. The repeated
     * alternation is deterministic (at every position exactly one branch
     * can match: {@code [^"\\]} for plain characters, {@code \\.} for
     * backslashes), so the possessive quantifier preserves the matched
     * language and captures byte-exactly while removing the per-character
     * backtracking recursion — the un-possessive form overflowed the
     * default thread stack on grown entry artifacts (the ISSUE-0161
     * reserved async-export host surface adds production text to every
     * entry module).
     */
    private static final Pattern STRING_LITERAL =
        Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*+)\"");

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

    /** Writes one fixture file (UTF-8) and returns its absolute path. */
    private static Path write(Path root, String rel, String content)
            throws IOException {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file.toAbsolutePath();
    }

    /** Writes one fixture file from exact bytes. */
    private static void writeBytes(Path file, byte[] bytes)
            throws IOException {
        Files.createDirectories(file.getParent());
        Files.write(file, bytes);
    }

    /** Runs the CLI with System.err captured; returns {exitCode, stderr}. */
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
     * stderr}. The harness compile resolves the harness invocation, so
     * the fixtures of this suite — multi-module projects with
     * cross-module calls and extern-C declaration imports — keep their
     * retained per-module artifact assertions green while the
     * release-owned production invocation is asserted separately as the
     * fail-closed outcome.
     */
    private static String[] runCliCapturingErr(String[] args)
            throws IOException {
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
     * The production-invocation fail-closed assertion of one fixture
     * whose construct is owned by a later slice (ISSUE-0643 P10 item 2):
     * the release-owned {@code deal.Main} compile exits nonzero with one
     * E6005 {@code SHARED_EMITTER_COVERAGE} carrying the expected stable
     * token and stages no artifact.
     *
     * @param args          the CLI arguments of the fixture
     * @param expectedToken the stable guard detail token
     *                      ({@code HOST_MODULE_IMPORT} or
     *                      {@code EXTERNAL_ASYNC_CALL}); null when the
     *                      fixture fails through the emission arm (no
     *                      stable token)
     * @param artifactDir   the fixture's output directory (must not exist
     *                      after the failed compile); may be null
     * @param context       the assertion context
     */
    private static void checkProductionFailClosed(String[] args,
            String expectedToken, Path artifactDir, String context)
            throws IOException {
        String[] run = runProductionCliCapturingErr(args);
        check(!"0".equals(run[0]),
            context + ": the release-owned production invocation fails"
                + " closed (exit " + run[0] + "): " + run[1]);
        check(run[1].contains("E6005")
                && run[1].contains("SHARED_EMITTER_COVERAGE")
                && (expectedToken == null
                    || run[1].contains(expectedToken)),
            context + ": the production failure is E6005"
                + " SHARED_EMITTER_COVERAGE (" + expectedToken + "): "
                + run[1]);
        if (artifactDir != null) {
            check(!Files.exists(artifactDir),
                context + ": the production failure stages no artifact"
                    + " under " + artifactDir);
        }
    }

    /** One finished subprocess: exit code plus merged stdout/stderr. */
    private record ProcessOutcome(int exitCode, String output) {
    }

    /** Runs a subprocess in {@code dir}; merged output, no timeout. */
    private static ProcessOutcome runProcess(Path dir, List<String> cmd)
            throws Exception {
        ProcessBuilder pb = new ProcessBuilder(cmd);
        pb.directory(dir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String out = new String(p.getInputStream().readAllBytes(),
            StandardCharsets.UTF_8);
        int exit = p.waitFor();
        return new ProcessOutcome(exit, out);
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

    /** Byte-for-byte identity of two artifact trees. */
    private static boolean treesIdentical(Path a, Path b) throws IOException {
        List<String> fa = artifactFilesUnder(a);
        List<String> fb = artifactFilesUnder(b);
        if (!fa.equals(fb)) return false;
        for (String rel : fa) {
            if (!Arrays.equals(Files.readAllBytes(a.resolve(rel)),
                    Files.readAllBytes(b.resolve(rel)))) {
                return false;
            }
        }
        return true;
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
     * The formatted-vs-structured agreement check: the canonical
     * formatter's stderr text must carry the range header, code,
     * message, and span length that the structured document's complete
     * range fields pin.
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
        String origin = jsonField(doc, "origin");
        check(file != null && code != null && message != null
                && startLine != null && startColumn != null
                && endLine != null && endColumn != null
                && scalarLength != null && origin != null,
            context + ": the structured document carries the complete"
                + " range fields (file, positions, offsets, scalarLength,"
                + " origin)");
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

    /** Independent SHA-256 hex (lowercase). */
    private static String sha256Hex(byte[] bytes) {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
        }
        byte[] hash = digest.digest(bytes);
        StringBuilder hex = new StringBuilder(hash.length * 2);
        for (byte b : hash) {
            hex.append(Character.forDigit((b >> 4) & 0xF, 16));
            hex.append(Character.forDigit(b & 0xF, 16));
        }
        return hex.toString();
    }

    /** The shared length-prefixed serialization via ProtectedPathOps. */
    private static byte[] lengthPrefixed(String value) {
        ProtectedPathOps.ByteResult result =
            ProtectedPathOps.lengthPrefixedUtf8(value);
        if (result instanceof ProtectedPathOps.ByteResult.Success s) {
            return s.bytes();
        }
        throw new IllegalStateException(
            ((ProtectedPathOps.ByteResult.Failure) result).reason());
    }

    /**
     * The pinned deploymentModuleId formula, independently recomputed:
     * "m" + first 16 lowercase hex chars of
     * SHA-256(lengthPrefixed(deploymentDigest) ||
     *         lengthPrefixed(canonicalSourceUri)).
     */
    private static String expectedDeploymentModuleId(String deploymentDigest,
                                                     String canonicalUri) {
        byte[] digestPart = lengthPrefixed(deploymentDigest);
        byte[] uriPart = lengthPrefixed(canonicalUri);
        byte[] combined = new byte[digestPart.length + uriPart.length];
        System.arraycopy(digestPart, 0, combined, 0, digestPart.length);
        System.arraycopy(uriPart, 0, combined, digestPart.length,
            uriPart.length);
        return "m" + sha256Hex(combined).substring(0, 16);
    }

    /** The canonical (symlink-resolved) file: URI of an existing file. */
    private static String canonicalFileUri(Path file) throws IOException {
        ProtectedPathOps.UriResult result =
            ProtectedPathOps.toFileUri(file.toRealPath());
        if (result instanceof ProtectedPathOps.UriResult.Success s) {
            return s.uri().toString();
        }
        throw new IllegalStateException(
            ((ProtectedPathOps.UriResult.Failure) result).reason());
    }

    /** The validated context of one entry, or a failure marker. */
    private static ProjectContext locateContext(String entry) {
        ProjectLocator.LocateResult result = ProjectLocator.locate(entry, null);
        return result.context();
    }

    /** The exact-v1.2 manifest used by most fixtures. */
    private static final String MANIFEST =
        "{\n  \"languageVersion\": \"1.2\",\n"
            + "  \"moduleRoots\": [\"src\"],\n"
            + "  \"output\": \"build/lua\",\n"
            + "  \"backend\": \"luajit\"\n}\n";

    /**
     * Asserts the D4 privacy invariant over one emitted artifact tree:
     * no {@code file:} URI, no deployment digest, and no
     * deploymentModuleId in runtime descriptor text (string literals),
     * public export keys, or source-language values — the id may appear
     * only as import wiring (the Lua {@code require} path, the JVM
     * module comment and class-name references).
     */
    private static void assertArtifactPrivacy(Path tree, String digest,
                                              String moduleId, String context)
            throws IOException {
        String upper = Character.toUpperCase(moduleId.charAt(0))
            + moduleId.substring(1);
        String requireWiring = "require(\"" + moduleId + "\")";
        for (String rel : artifactFilesUnder(tree)) {
            Path file = tree.resolve(rel);
            byte[] bytes = Files.readAllBytes(file);
            // Raw-byte needle checks cover every artifact, including the
            // javac-produced .class binaries of the JVM run.
            String raw = new String(bytes, StandardCharsets.ISO_8859_1);
            check(!raw.contains("file:/"),
                context + ": no private file: URI in artifact " + rel);
            check(!raw.contains(digest),
                context + ": no deployment digest in artifact " + rel);
            boolean text = rel.endsWith(".lua") || rel.endsWith(".java");
            if (!text) {
                check(!raw.contains(moduleId),
                    context + ": no deploymentModuleId in non-text artifact "
                        + rel);
                continue;
            }
            String content = new String(bytes, StandardCharsets.UTF_8);
            // Import wiring is the pinned deploymentModuleId surface:
            // strip the Lua require argument before the string-literal
            // scan so only descriptor/export/value literals are judged.
            Matcher m = STRING_LITERAL.matcher(
                content.replace(requireWiring, ""));
            while (m.find()) {
                String lit = m.group(1);
                check(!lit.contains(moduleId) && !lit.contains(digest)
                        && !lit.contains("file:/"),
                    context + ": no private identity in a string literal"
                        + " (runtime descriptor / source-language value)"
                        + " of " + rel + ": " + lit);
            }
            if (rel.endsWith(".lua")) {
                for (String line : content.split("\\R", -1)) {
                    if (line.contains(moduleId)) {
                        check(line.contains(requireWiring),
                            context + ": the deploymentModuleId appears in"
                                + " Lua artifact " + rel + " only as import"
                                + " wiring (require): " + line);
                    }
                }
                check(!Pattern.compile("exports\\[?\"?m[0-9a-f]{16}")
                        .matcher(content).find(),
                    context + ": no public export key carries the"
                        + " deploymentModuleId in " + rel);
            }
            if (rel.endsWith(".java")) {
                for (String line : content.split("\\R", -1)) {
                    if (line.contains(moduleId) || line.contains(upper)) {
                        boolean moduleComment =
                            line.contains("// Module: " + moduleId);
                        boolean ownClassDecl =
                            rel.startsWith(upper + ".java")
                                && line.contains("public final class "
                                    + upper);
                        boolean wiringRef = line.contains(upper + ".");
                        check(moduleComment || ownClassDecl || wiringRef,
                            context + ": the deploymentModuleId appears in"
                                + " JVM artifact " + rel + " only as wiring"
                                + " (module comment, class declaration, or"
                                + " class-name reference): " + line);
                    }
                }
            }
        }
    }

    // =========================================================================
    // Extern-c load_ffi emission gate (ISSUE-0454): the LuaJIT arm routes
    // every // @extern-c declaration import through the metadata phase's
    // FfiGeneratedModule into
    //   local <bindingsLocal> = <bindings literal>
    //   local <alias> = __rt.load_ffi(<moduleKey>, <cdefBundle>,
    //       <plans>, <bindingsLocal>, <import span triplet>)
    // with the metadata-provided module key, the normalized loader text,
    // cdef, plans, bindings, and the source span. The obsolete pre-D6
    // The generated artifact carries no load_host route for the import and no ffi.C
    // access. Isolated fixture copies perturb the externals key and the
    // native-library path independently to prove the emission consumes
    // the current FfiGeneratedModule metadata rather than constants.
    // =========================================================================

    private static void testExternCImportLoadFfiEmission() throws Exception {
        System.out.println("-- Extern-c import: load_ffi emission with the"
            + " metadata-provided module key, normalized loader text,"
            + " cdef, plans, bindings, and source span --");
        Path base = Files.createTempDirectory("deal_gate_ffi_emission_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "ffi_math.d.deal",
                "// @extern-c\n"
                    + "\n"
                    + "// @c-struct\n"
                    + "export class Vec2 {\n"
                    + "  x: number = 0.0;\n"
                    + "  y: number = 1.5;\n"
                    + "}\n"
                    + "\n"
                    + "export function add(a: int, b: int): int;\n");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\",\n"
                    + "  \"externals\": {\n"
                    + "    \"ffi_math\": {\n"
                    + "      \"declaration\": \"ffi_math.d.deal\",\n"
                    + "      \"nativeLibrary\": \"libs/libffi_math.so\"\n"
                    + "    }\n  }\n}\n");
            write(proj, "src/main.deal",
                "import * as ffi from \"ffi_math\"\n"
                    + "export function main(): null {\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the extern-c import compiles on the LuaJIT arm: "
                    + lua[1]);
            check(!lua[1].contains("ERROR"),
                "the extern-c compile emits no diagnostics: " + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            check(Files.exists(luaDir.resolve("main.lua")),
                "the LuaJIT entry artifact exists");

            String mainLua = Files.readString(luaDir.resolve("main.lua"));
            check(mainLua.contains(
                    "local ffi = __rt.load_ffi(\"ffi:@$external/ffi_math\", {"),
                "the extern-c import emits the load_ffi call with the"
                    + " metadata-provided module key");
            check(mainLua.contains("bundleDigest = \"")
                    && mainLua.contains("identityDigest = \"")
                    && mainLua.contains("fullContent = \"")
                    && mainLua.contains("entries = { { entryDigest = \""),
                "the emitted bundle carries the digest fields, the full"
                    + " cdef content, and the ordered entries");
            check(mainLua.contains("dealName = \"add\", cSymbol = \"add\"")
                    && mainLua.contains("privateFunctionPointerType = \"")
                    && mainLua.contains("orderedParams = { { kind = \"INT\","
                        + " canonicalDescriptor = \"int\","
                        + " canonicalClassIdentity = nil }"),
                "the emitted bundle carries the canonical function"
                    + " metadata");
            check(mainLua.contains("name = \"Vec2\","
                    + " canonicalClassIdentity ="
                    + " \"@$external/ffi_math/Vec2\"")
                    && mainLua.contains("kind = \"C_STRUCT\"")
                    && mainLua.contains(
                        "dealName = \"x\", fieldOrdinal = 0"),
                "the emitted bundle carries the canonical class metadata");
            // The normalized loader text (seam S3): the manifest-relative
            // path resolves against the manifest directory through the
            // pinned prefix-resolved symlink conversion.
            ProtectedPathOps.PathResult loaderResolved =
                ProtectedPathOps.normalizePrefixResolved(
                    proj.resolve("libs/libffi_math.so").toString());
            check(loaderResolved
                    instanceof ProtectedPathOps.PathResult.Success,
                "the loader text resolves: " + loaderResolved);
            String expectedLoader =
                ((ProtectedPathOps.PathResult.Success) loaderResolved)
                    .resolvedPath().toString();
            check(mainLua.contains(
                    "nativeLibrary = { kind = \"MANIFEST_RELATIVE_PATH\","
                        + " loaderText = \"" + expectedLoader + "\" }"),
                "the emitted bundle carries the normalized loader text");
            check(mainLua.contains(
                    "[\"@$external/ffi_math/Vec2\"] = { plan = {")
                    && mainLua.contains("name = \"x\", descriptor ="
                        + " \"number\", optional = false,"
                        + " evaluator = function() return 0.0 end")
                    && mainLua.contains("canonicalPlanContent = \"")
                    && mainLua.contains("semanticDefaultContents = \"")
                    && mainLua.contains(
                        "evaluatorImplementationContents = \"")
                    && mainLua.contains("planDigest = \""),
                "the emitted plans literal carries the plan list with"
                    + " deferred evaluators and the three content strings");
            check(mainLua.contains("local __ffi_bindings_1 = { moduleKey ="
                    + " \"ffi:@$external/ffi_math\", state = \"UNBOUND\","
                    + " cells = { add = { state = \"UNBOUND\","
                    + " wrapper = nil, errorValue = nil } }")
                    && mainLua.contains("importedFunctions = {")
                    && mainLua.contains("importedClassPlans = {"),
                "the emitted bindings literal carries the module key, the"
                    + " UNBOUND forward cells, and the carried imported"
                    + " reference lists");
            check(mainLua.contains(", \"" + entry + "\", 1, 1)"),
                "the loader call carries the import span triplet");
            check(!mainLua.contains("load_host"),
                "the extern-c import takes no load_host route");
            check(!mainLua.contains("ffi.C"),
                "the generated chunk carries no ffi.C access");
            check(!mainLua.contains("FFI_UNSUPPORTED_BACKEND"),
                "the LuaJIT arm raises no FFI_UNSUPPORTED_BACKEND");

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation fails the same extern-C fixture closed with
            // E6005 SHARED_EMITTER_COVERAGE naming the HOST-kind import
            // and stages no artifact (the FFI realization is the FFI
            // child's; ISSUE-0625 retargets this to the production
            // outcome).
            checkProductionFailClosed(new String[]{
                "compile", entry.toString(), "--output",
                base.resolve("prod_out").toString()}, "HOST_MODULE_IMPORT",
                base.resolve("prod_out"), "extern-c import");

            // Metadata consumption, part 1: an isolated copy whose
            // externals KEY changes emits the changed module key while
            // the loader text stays pinned.
            Path keyPerturbed = base.resolve("key_perturbed");
            write(keyPerturbed, "ffi_math.d.deal",
                "// @extern-c\n"
                    + "export function add(a: int, b: int): int;\n");
            write(keyPerturbed, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\",\n"
                    + "  \"externals\": {\n"
                    + "    \"ffi_other\": {\n"
                    + "      \"declaration\": \"ffi_math.d.deal\",\n"
                    + "      \"nativeLibrary\":"
                    + " \"libs/libffi_math.so\"\n"
                    + "    }\n  }\n}\n");
            write(keyPerturbed, "src/main.deal",
                "import * as ffi from \"ffi_other\"\n"
                    + "export function main(): null {\n"
                    + "  return null;\n"
                    + "}\n");
            String[] keyRun = runCliCapturingErr(new String[]{
                "compile",
                keyPerturbed.resolve("src/main.deal").toAbsolutePath()
                    .toString()});
            check("0".equals(keyRun[0]),
                "the key-perturbed copy compiles: " + keyRun[1]);
            String keyLua = Files.readString(
                keyPerturbed.resolve("build/lua/main.lua"));
            check(keyLua.contains(
                    "local ffi = __rt.load_ffi(\"ffi:@$external/ffi_other\""
                        + ", {"),
                "a changed externals key changes the emitted module key");
            // The same relative nativeLibrary path resolves against the
            // copy's own manifest directory: the emitted loader text is
            // the copy-local normalized text, never the original
            // project's constant.
            ProtectedPathOps.PathResult keyLoaderResolved =
                ProtectedPathOps.normalizePrefixResolved(
                    keyPerturbed.resolve("libs/libffi_math.so").toString());
            check(keyLoaderResolved
                    instanceof ProtectedPathOps.PathResult.Success,
                "the copy's loader text resolves: " + keyLoaderResolved);
            String keyExpectedLoader =
                ((ProtectedPathOps.PathResult.Success) keyLoaderResolved)
                    .resolvedPath().toString();
            check(keyLua.contains("loaderText = \"" + keyExpectedLoader
                    + "\""),
                "the changed externals key keeps the metadata-provided"
                    + " loader text of the copy");
            check(!keyLua.contains(expectedLoader),
                "the copy's artifact carries no loader text constant of"
                    + " the original project");

            // Metadata consumption, part 2: an isolated copy whose
            // nativeLibrary PATH changes emits the changed loader text
            // while the module key stays pinned.
            Path pathPerturbed = base.resolve("path_perturbed");
            write(pathPerturbed, "ffi_math.d.deal",
                "// @extern-c\n"
                    + "export function add(a: int, b: int): int;\n");
            write(pathPerturbed, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\",\n"
                    + "  \"externals\": {\n"
                    + "    \"ffi_math\": {\n"
                    + "      \"declaration\": \"ffi_math.d.deal\",\n"
                    + "      \"nativeLibrary\":"
                    + " \"libs/libffi_other.so\"\n"
                    + "    }\n  }\n}\n");
            write(pathPerturbed, "src/main.deal",
                "import * as ffi from \"ffi_math\"\n"
                    + "export function main(): null {\n"
                    + "  return null;\n"
                    + "}\n");
            String[] pathRun = runCliCapturingErr(new String[]{
                "compile",
                pathPerturbed.resolve("src/main.deal").toAbsolutePath()
                    .toString()});
            check("0".equals(pathRun[0]),
                "the path-perturbed copy compiles: " + pathRun[1]);
            String pathLua = Files.readString(
                pathPerturbed.resolve("build/lua/main.lua"));
            ProtectedPathOps.PathResult otherResolved =
                ProtectedPathOps.normalizePrefixResolved(
                    pathPerturbed.resolve("libs/libffi_other.so")
                        .toString());
            check(otherResolved
                    instanceof ProtectedPathOps.PathResult.Success,
                "the perturbed loader text resolves: " + otherResolved);
            String expectedOther = ((ProtectedPathOps.PathResult.Success)
                otherResolved).resolvedPath().toString();
            check(pathLua.contains("loaderText = \"" + expectedOther
                    + "\""),
                "a changed native-library path changes the emitted"
                    + " loader text");
            check(pathLua.contains(
                    "local ffi = __rt.load_ffi(\"ffi:@$external/ffi_math\""
                        + ", {"),
                "the changed native-library path leaves the module key"
                    + " unchanged");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // FFIGEN fixture projects compile through the production emitter and
    // preserve their configured module identities and loader paths.
    // =========================================================================

    private static void testFfigenFixtureProjects()
            throws Exception {
        System.out.println("-- FFIGEN fixture projects:"
            + " pairwise-distinct module keys and pinned loader texts"
            + " through the production emitter --");
        Path base = Files.createTempDirectory("deal_gate_ffigen_");
        try {
            String[] projects = {"missing-lib", "missing-symbol", "valid"};
            LinkedHashMap<String, String> artifacts =
                new LinkedHashMap<>();
            for (String project : projects) {
                Path entry = Path.of("test/fixtures/ffigen/" + project
                    + "/src/main.deal").toAbsolutePath();
                Path outDir = base.resolve(project);
                String[] lua = runCliCapturingErr(new String[]{
                    "compile", entry.toString(), "--backend", "lua",
                    "--output", outDir.toString()});
                check("0".equals(lua[0]),
                    project + " compiles through the production CLI: "
                        + lua[1]);
                check(!lua[1].contains("ERROR"),
                    project + " compile emits no diagnostics: " + lua[1]);
                String artifact =
                    Files.readString(outDir.resolve("main.lua"));
                check(artifact.contains("__rt.load_ffi("),
                    project + " artifact emits the load_ffi call");
                check(!artifact.contains("load_host"),
                    project + " artifact takes no load_host route");
                check(!artifact.contains("ffi.C"),
                    project + " artifact carries no ffi.C access");
                artifacts.put(project, artifact);
            }

            // Pairwise-distinct module keys (seam S1): the metadata
            // module keys exactly as pinned.
            Pattern keyPattern = Pattern.compile(
                "__rt\\.load_ffi\\(\"([^\"]*)\"");
            String[] expectedKeys = {
                "ffi:@$external/ffi/missing_lib",
                "ffi:@$external/ffi/missing_symbol",
                "ffi:@$external/ffi/valid",
            };
            for (int i = 0; i < projects.length; i++) {
                Matcher m = keyPattern.matcher(artifacts.get(projects[i]));
                check(m.find(),
                    projects[i] + " artifact carries the load_ffi module"
                        + " key");
                check(expectedKeys[i].equals(m.group(1)),
                    projects[i] + " emits the pinned metadata module key "
                        + expectedKeys[i] + ", got " + m.group(1));
            }

            // Pinned symlink-resolved loader texts (seam S3): the
            // manifest-relative paths resolve to <repo-root>/build/...
            // (each manifest sits four directory levels below the repo
            // root).
            String missingLibLoader = expectedLoaderText("missing-lib",
                "ffigen-no-such-lib.so");
            String fixtureLoader = expectedLoaderText("valid",
                "ffigen-integration-fixture.so");
            check(artifacts.get("missing-lib").contains(
                    "loaderText = \"" + missingLibLoader + "\""),
                "missing-lib carries the pinned resolved-absolute loader"
                    + " text " + missingLibLoader);
            check(artifacts.get("missing-symbol").contains(
                    "loaderText = \"" + fixtureLoader + "\""),
                "missing-symbol carries the pinned resolved-absolute"
                    + " loader text " + fixtureLoader);
            check(artifacts.get("valid").contains(
                    "loaderText = \"" + fixtureLoader + "\""),
                "valid carries the pinned resolved-absolute loader text "
                    + fixtureLoader);

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation of the committed ffigen valid project fails
            // closed with E6005 SHARED_EMITTER_COVERAGE naming the
            // HOST-kind extern-C import and stages nothing.
            checkProductionFailClosed(new String[]{
                "compile", Path.of("test/fixtures/ffigen/valid/src/main.deal")
                    .toAbsolutePath().toString(), "--backend", "lua",
                "--output", base.resolve("prod_valid").toString()},
                "HOST_MODULE_IMPORT", base.resolve("prod_valid"),
                "ffigen valid project");

        } finally {
            deleteRecursively(base);
        }
    }

    /**
     * The expected symlink-resolved loader text of one fixture
     * project: the manifest directory (four levels below the repo root)
     * resolved through symlinks, plus the lexically normalized
     * {@code ../../../../build/...} suffix.
     */
    private static String expectedLoaderText(String project, String soName)
            throws IOException {
        return Path.of("test/fixtures/ffigen/" + project).toRealPath()
            .resolve("../../../../build/" + soName).normalize().toString();
    }

    // =========================================================================
    // Gate 1. Integration fixture 1: a class-free out-of-root project
    //         compiles and runs on both backends through the production
    //         pipeline, with importer-relative resolution outside every
    //         configured root and the manifest directory.
    // =========================================================================

    private static void testClassFreeOutOfRootBothBackends() throws Exception {
        System.out.println("-- Gate 1: class-free out-of-root project runs"
            + " on LuaJIT and JVM --");

        Path base = Files.createTempDirectory("deal_gate_free_");
        try {
            Path proj = base.resolve("proj");
            Path common = base.resolve("common");
            write(proj, "deal.json", MANIFEST);
            // The shared module lives in a sibling directory: outside
            // every configured root (src) and outside the manifest
            // directory (proj).
            write(common, "shared.deal",
                "export function greet(): string { return \"OK\"; }\n"
                    + "export function word(): string { return \"shared\"; }\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as shared from \"../../common/shared\"\n"
                    + "export function main(): null {\n"
                    + "  console.log(shared.greet());\n"
                    + "  console.log(shared.word());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            // LuaJIT through the production CLI (manifest backend and
            // output; the pinned distribution stdlib surface).
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the class-free out-of-root project compiles on LuaJIT: "
                    + lua[1]);
            check(!lua[1].contains("ERROR"),
                "the LuaJIT compile emits no diagnostics: " + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            check(Files.exists(luaDir.resolve("main.lua")),
                "the LuaJIT entry artifact exists under the manifest"
                    + " output");
            ProcessOutcome luaRun = runProcess(luaDir, List.of("luajit",
                "main.lua"));
            check(luaRun.exitCode() == 0
                    && luaRun.output().trim().equals("OK\nshared"),
                "the class-free out-of-root shared module runs under"
                    + " LuaJIT with the pinned output semantics: "
                    + luaRun.output());

            // JVM through the production CLI (valid jvm alias overrides
            // the manifest backend; CLI output override).
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the same project compiles with --backend jvm: " + jvm[1]);
            check(!jvm[1].contains("ERROR"),
                "the JVM compile emits no diagnostics: " + jvm[1]);
            check(lua[1].equals(jvm[1]),
                "both backends emit equivalent (empty) diagnostics: "
                    + jvm[1]);
            List<String> javaFiles = artifactFilesUnder(jvmOut).stream()
                .filter(f -> f.endsWith(".java")).toList();
            check(javaFiles.contains("Main.java"),
                "the JVM entry artifact exists: " + javaFiles);
            List<String> javacCmd = new ArrayList<>(List.of("javac",
                "-encoding", "UTF-8"));
            javacCmd.addAll(javaFiles);
            ProcessOutcome javac = runProcess(jvmOut, javacCmd);
            check(javac.exitCode() == 0,
                "the JVM artifacts compile with javac: " + javac.output());
            ProcessOutcome jvmRun = runProcess(jvmOut, List.of("java",
                "-cp", ".", "Main"));
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("OK\nshared"),
                "the class-free out-of-root shared module runs under JVM"
                    + " with the equivalent output semantics: "
                    + jvmRun.output());

            // ISSUE-0643 P10 item 2: the release-owned production
            // invocation fails the cross-module-call fixture closed with
            // E6005 SHARED_EMITTER_COVERAGE (the cross-module call is the
            // calls child's) and stages nothing.
            checkProductionFailClosed(new String[]{
                "compile", entry.toString(), "--output",
                base.resolve("prod_out").toString()}, null,
                base.resolve("prod_out"), "class-free out-of-root project");

            // Determinism: repeated compiles into fresh output
            // directories are byte-identical on both backends.
            Path luaA = base.resolve("det_lua_a");
            Path luaB = base.resolve("det_lua_b");
            String[] detA = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output",
                luaA.toString()});
            String[] detB = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output",
                luaB.toString()});
            check("0".equals(detA[0]) && "0".equals(detB[0]),
                "the repeated LuaJIT compiles succeed: " + detA[1] + detB[1]);
            check(treesIdentical(luaA, luaB),
                "identical inputs reproduce byte-identical LuaJIT artifact"
                    + " trees (deterministic compile outputs)");
            Path jvmA = base.resolve("det_jvm_a");
            Path jvmB = base.resolve("det_jvm_b");
            String[] detJa = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmA.toString()});
            String[] detJb = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmB.toString()});
            check("0".equals(detJa[0]) && "0".equals(detJb[0]),
                "the repeated JVM compiles succeed: "
                    + detJa[1] + detJb[1]);
            check(treesIdentical(jvmA, jvmB),
                "identical inputs reproduce byte-identical JVM artifact"
                    + " trees (deterministic compile outputs)");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 2. Integration fixture 2: an out-of-root class is exactly one
    //         E2010 at the class name span on both backends with no class
    //         metadata/artifact.
    // =========================================================================

    private static void testOutOfRootClassBothBackends() throws Exception {
        System.out.println("-- Gate 2: out-of-root class is E2010 on both"
            + " backends, no artifact --");

        Path base = Files.createTempDirectory("deal_gate_class_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "deal.json", MANIFEST);
            write(base.resolve("common"), "shared.deal",
                "export function add(a: int, b: int): int { return a + b; }\n"
                    + "\n"
                    + "export class Point { x: int = 0; }\n");
            write(proj, "src/main.deal",
                "import * as shared from \"../../common/shared\"\n"
                    + "export function main(): null {\n"
                    + "  let p: shared.Point = { x: 1 };\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            Path diagJson = base.resolve("class_diag.json");
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                diagJson.toString()});
            check("1".equals(lua[0]),
                "the out-of-root class attempt exits 1 (LuaJIT)");
            String luaErr = lua[1];
            check(countOccurrences(luaErr, "E2010") == 1,
                "exactly one E2010 is emitted: " + luaErr);
            check(luaErr.contains("Class 'Point'")
                    && luaErr.contains("no public module identity"),
                "the out-of-root class is E2010 at the class declaration"
                    + " through the canonical formatter: " + luaErr);
            check(luaErr.contains("shared.deal:3:8-3:35")
                    && luaErr.contains("[span 27]"),
                "the E2010 carries the complete SOURCE class-name range"
                    + " (shared.deal:3:8-3:35, span 27): " + luaErr);
            check(luaErr.contains("1 error(s), 0 warning(s)"),
                "the run reports exactly one error and no warnings: "
                    + luaErr);
            check(!Files.exists(proj.resolve("build/lua")),
                "no artifact of any kind (no class metadata, no class"
                    + " product for the out-of-root module) exists after"
                    + " the rejection");

            // Structured agreement: the written document carries the same
            // complete range the formatter prints.
            String doc = Files.readString(diagJson);
            check("E2010".equals(jsonField(doc, "code"))
                    && "27".equals(jsonField(doc, "scalarLength"))
                    && "8".equals(jsonField(doc, "startColumn"))
                    && "3".equals(jsonField(doc, "startLine"))
                    && "SOURCE".equals(jsonField(doc, "origin")),
                "the structured document pins the class-name range"
                    + " (line 3, column 8, scalarLength 27, SOURCE): "
                    + doc);
            checkFormattedStructuredAgree(luaErr, doc, "out-of-root class");

            // JVM arm: the identical E2010 surface, no artifact.
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("1".equals(jvm[0]),
                "the out-of-root class attempt exits 1 (JVM)");
            check(jvm[1].trim().equals(luaErr.trim()),
                "both backends emit byte-identical E2010 diagnostics"
                    + " (equivalent diagnostics):\nLuaJIT: "
                    + luaErr + "JVM: " + jvm[1]);
            check(!Files.exists(jvmOut),
                "no JVM artifact (no class metadata, no class product)"
                    + " exists after the rejection");

            // Diagnostics privacy: no private identity URI or module id
            // ever appears in diagnostic text.
            check(!luaErr.contains("file:/") && !doc.contains("file:/")
                    && !jvm[1].contains("file:/"),
                "no private identity URI appears in the class"
                    + " diagnostics (formatted or structured)");
            check(!Pattern.compile("m[0-9a-f]{16}").matcher(doc).find(),
                "no deploymentModuleId appears in the structured"
                    + " diagnostics");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 3. A class in a rooted non-externals .d.deal and a class in a
    //         non-spec-listed .d.deal inside the stdlib directory are the
    //         same unconditional E2010 at the class name span.
    // =========================================================================

    private static void testDeclarationClassGates() throws Exception {
        System.out.println("-- Gate 3: rooted non-externals .d.deal and"
            + " non-spec stdlib-directory .d.deal classes --");

        // (a) Rooted non-externals .d.deal.
        Path a = Files.createTempDirectory("deal_gate_rootdecl_");
        try {
            write(a, "deal.json", MANIFEST);
            write(a, "src/host.d.deal",
                "export function probe(): int;\n"
                    + "\n"
                    + "export class Thing { x: int = 0; }\n");
            write(a, "src/main.deal",
                "import * as host from \"./host\"\n"
                    + "export function main(): null {\n"
                    + "  let v: int = host.probe();\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = a.resolve("src/main.deal").toAbsolutePath();

            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(run[0]),
                "the rooted non-externals .d.deal class exits 1: " + run[1]);
            check(run[1].contains("E2010") && run[1].contains("Class 'Thing'")
                    && run[1].contains("no public module identity")
                    && run[1].contains("host.d.deal:3:8-3:35")
                    && run[1].contains("[span 27]"),
                "the rooted non-externals .d.deal class is E2010 at the"
                    + " class name span (host.d.deal:3:8-3:35, span 27): "
                    + run[1]);
            check(!Files.exists(a.resolve("build/lua")),
                "no artifact exists for the rejected rooted .d.deal class");

            // The class-free variant of the same module stays a valid
            // private-identity module.
            write(a, "src/host.d.deal", "export function probe(): int;\n");
            String[] free = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(free[0]),
                "the class-free rooted non-externals .d.deal stays a valid"
                    + " module: " + free[1]);
        } finally {
            deleteRecursively(a);
        }

        // (b) Non-spec-listed .d.deal inside the stdlib directory.
        Path b = Files.createTempDirectory("deal_gate_stdextra_");
        try {
            write(b, "deal.json", MANIFEST);
            write(b, "std/extra.d.deal",
                "export function probe(): int;\n"
                    + "\n"
                    + "export class Extra { x: int = 0; }\n");
            write(b, "src/main.deal",
                "import * as extra from \"../std/extra\"\n"
                    + "export function main(): null {\n"
                    + "  let v: int = extra.probe();\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = b.resolve("src/main.deal").toAbsolutePath();

            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(run[0]),
                "the non-spec-listed stdlib-directory .d.deal class exits"
                    + " 1: " + run[1]);
            check(run[1].contains("E2010") && run[1].contains("Class 'Extra'")
                    && run[1].contains("no public module identity")
                    && run[1].contains("extra.d.deal:3:8-3:35")
                    && run[1].contains("[span 27]"),
                "the non-spec-listed .d.deal inside the stdlib directory"
                    + " is E2010 at the class name span"
                    + " (extra.d.deal:3:8-3:35, span 27): " + run[1]);
            check(!Files.exists(b.resolve("build/lua")),
                "no artifact exists for the rejected stdlib-directory"
                    + " .d.deal class");

            write(b, "std/extra.d.deal", "export function probe(): int;\n");
            String[] free = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(free[0]),
                "the class-free non-spec-listed .d.deal inside the stdlib"
                    + " directory stays a valid private module: " + free[1]);
        } finally {
            deleteRecursively(b);
        }
    }

    // =========================================================================
    // Gate 4. Resolution error gates: E2003 for unresolved/non-spec
    //         stdlib imports and the absent surface; E2009 for a bare
    //         import landing on a non-stdlib .d.deal with no externals
    //         entry — every diagnostic at the import span.
    // =========================================================================

    private static void testImportResolutionErrorGates() throws Exception {
        System.out.println("-- Gate 4: E2003/E2009 at import spans --");

        Path r = Files.createTempDirectory("deal_gate_errors_");
        try {
            write(r, "deal.json", MANIFEST);
            Path entry = r.resolve("src/main.deal").toAbsolutePath();

            // (a) E2003: unresolved relative import.
            String importMissing = "import * as missing from \"./missing\"";
            write(r, "src/main.deal", importMissing + "\n"
                + "export function main(): null { return null; }\n");
            Path missingJson = r.resolve("missing_diag.json");
            String[] missing = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                missingJson.toString()});
            check("1".equals(missing[0]) && missing[1].contains("E2003")
                    && missing[1].contains("Module not found: './missing'"),
                "the unresolved relative import is E2003: " + missing[1]);
            int missingSpan = importMissing.length() + 1 + "export".length();
            check(missing[1].contains("main.deal:1:1-2:7")
                    && missing[1].contains("[span " + missingSpan + "]"),
                "the E2003 carries the complete SOURCE import range"
                    + " (main.deal:1:1-2:7, span " + missingSpan + "): "
                    + missing[1]);
            String missingDoc = Files.readString(missingJson);
            check("E2003".equals(jsonField(missingDoc, "code"))
                    && String.valueOf(missingSpan).equals(
                        jsonField(missingDoc, "scalarLength"))
                    && "SOURCE".equals(jsonField(missingDoc, "origin")),
                "the structured E2003 pins the import span: " + missingDoc);
            checkFormattedStructuredAgree(missing[1], missingDoc,
                "E2003 unresolved import");
            check(!missing[1].contains("file:/")
                    && !missingDoc.contains("file:/")
                    && !Pattern.compile("m[0-9a-f]{16}")
                        .matcher(missingDoc).find(),
                "no private identity URI or deploymentModuleId appears in"
                    + " the E2003 diagnostics (formatted or structured)");

            // (b) E2009: bare import landing on a rooted non-externals
            // .d.deal (no externals entry declares it).
            write(r, "src/host.d.deal", "export function probe(): int;\n");
            String importHost = "import * as host from \"host\"";
            write(r, "src/main.deal", importHost + "\n"
                + "export function main(): null { return null; }\n");
            Path hostJson = r.resolve("host_diag.json");
            String[] host = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                hostJson.toString()});
            check("1".equals(host[0]) && host[1].contains("E2009")
                    && host[1].contains("'host'")
                    && host[1].contains("not declared in deal.json externals")
                    && host[1].contains("host.d.deal"),
                "the bare import landing on a non-externals .d.deal is"
                    + " E2009 naming the resolved declaration file: "
                    + host[1]);
            int hostSpan = importHost.length() + 1 + "export".length();
            check(host[1].contains("main.deal:1:1-2:7")
                    && host[1].contains("[span " + hostSpan + "]"),
                "the E2009 carries the complete SOURCE import range"
                    + " (main.deal:1:1-2:7, span " + hostSpan + "): "
                    + host[1]);
            String hostDoc = Files.readString(hostJson);
            check("E2009".equals(jsonField(hostDoc, "code"))
                    && String.valueOf(hostSpan).equals(
                        jsonField(hostDoc, "scalarLength"))
                    && "SOURCE".equals(jsonField(hostDoc, "origin")),
                "the structured E2009 pins the import span: " + hostDoc);
            checkFormattedStructuredAgree(host[1], hostDoc,
                "E2009 undeclared host module");
            check(!host[1].contains("file:/")
                    && !hostDoc.contains("file:/")
                    && !Pattern.compile("m[0-9a-f]{16}")
                        .matcher(hostDoc).find(),
                "no private identity URI or deploymentModuleId appears in"
                    + " the E2009 diagnostics (formatted or structured)");

            // (c) E2003: a non-spec bare std/... import (the 6-module
            // filter; the distribution surface is present here).
            String importExtra = "import * as extra from \"std/extra\"";
            write(r, "src/main.deal", importExtra + "\n"
                + "export function main(): null { return null; }\n");
            String[] extra = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(extra[0]) && extra[1].contains("E2003")
                    && extra[1].contains("'std/extra'")
                    && extra[1].contains("Not a spec-listed stdlib module"),
                "the non-spec bare std/... import is E2003 naming the"
                    + " 6-module filter: " + extra[1]);
            check(extra[1].contains("[span 41]"),
                "the non-spec stdlib E2003 carries the import span"
                    + " (span 41): " + extra[1]);
            check(!extra[1].contains("Exception"),
                "no raw exception escapes the non-spec stdlib import: "
                    + extra[1]);

            // (d) E2003: a missing stdlib surface (subprocess whose
            // working directory has no std/ and whose project has no
            // local std/) — never a RuntimeException.
            Path bare = Files.createTempDirectory("deal_gate_nostd_");
            try {
                write(bare, "deal.json", MANIFEST);
                write(bare, "src/main.deal",
                    "import * as console from \"std/console\"\n"
                        + "export function main(): null { return null; }\n");
                String buildCp = Path.of("build").toAbsolutePath().toString();
                ProcessOutcome noStd = runProcess(bare, List.of("java",
                    "-cp", buildCp, "deal.Main", "compile",
                    "src/main.deal"));
                check(noStd.exitCode() == 1,
                    "the missing-surface stdlib import exits 1");
                check(noStd.output().contains("E2003")
                        && noStd.output().contains(
                            "stdlib surface is absent"),
                    "a missing surface is E2003 at the import span (never"
                        + " a RuntimeException): " + noStd.output());
                check(!noStd.output().contains("Exception"),
                    "no raw exception escapes the missing-surface path: "
                        + noStd.output());
            } finally {
                deleteRecursively(bare);
            }
        } finally {
            deleteRecursively(r);
        }
    }

    // =========================================================================
    // Gate 5. Identity gates: equivalent import spellings compile to one
    //         identity (deterministic compile outputs + the migration's
    //         identity observables); a manifest byte change changes the
    //         deployment digest and every derived semantic identity; a
    //         source relocation changes that source's identity; private
    //         identities never reach artifacts or diagnostics.
    // =========================================================================

    private static void testIdentityGates() throws Exception {
        System.out.println("-- Gate 5: identity, determinism, and privacy --");

        Path base = Files.createTempDirectory("deal_gate_id_");
        try {
            Path proj = base.resolve("proj");
            Path common = base.resolve("common");
            write(proj, "deal.json", MANIFEST);
            Path shared = write(common, "shared.deal",
                "export function greet(): string { return \"OK\"; }\n");
            write(proj, "src/sub/other.deal",
                "import * as shared from \"../../../common/shared\"\n"
                    + "export function other(): string { return"
                    + " shared.greet(); }\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as shared from \"../../common/shared\"\n"
                    + "import * as other from \"./sub/other\"\n"
                    + "export function main(): null {\n"
                    + "  console.log(shared.greet());\n"
                    + "  console.log(other.other());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            // (a) Equivalent import spellings compile to one identity.
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the two-spelling project compiles on LuaJIT: " + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            List<String> luaModuleArtifacts = artifactFilesUnder(luaDir)
                .stream().filter(f -> LUA_MODULE_ID.matcher(f).find())
                .toList();
            check(luaModuleArtifacts.size() == 1,
                "equivalent spellings of one resolved source emit exactly"
                    + " one private module artifact: " + luaModuleArtifacts);
            if (luaModuleArtifacts.size() != 1) {
                return;
            }
            String moduleId = luaModuleArtifacts.get(0)
                .substring(luaModuleArtifacts.get(0).lastIndexOf('/') + 1,
                    luaModuleArtifacts.get(0).length() - ".lua".length());
            String mainLua = Files.readString(luaDir.resolve("main.lua"));
            String otherLua = Files.readString(
                luaDir.resolve("sub/other.lua"));
            check(mainLua.contains("require(\"" + moduleId + "\")")
                    && otherLua.contains("require(\"" + moduleId + "\")"),
                "both import spellings wire the same deploymentModuleId: "
                    + moduleId);

            // The migration's identity observables: the emitted id equals
            // the pinned formula independently recomputed from the
            // deployment digest and the canonical resolved source URI.
            ProjectContext context = locateContext(entry.toString());
            check(context != null, "the fixture locates a strict context");
            String digest = context.projectDeploymentIdentity()
                .validatedManifestContentDigest();
            String canonicalUri = canonicalFileUri(shared);
            String expectedId = expectedDeploymentModuleId(digest,
                canonicalUri);
            check(moduleId.equals(expectedId),
                "the emitted deploymentModuleId matches the pinned formula"
                    + " (digest + canonical URI): " + moduleId
                    + " vs " + expectedId);

            // One identity on JVM: a single module class whose name
            // derives from the same id, referenced by both importers.
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the two-spelling project compiles on JVM: " + jvm[1]);
            List<String> jvmModuleArtifacts = artifactFilesUnder(jvmOut)
                .stream().filter(f -> JVM_MODULE_ID.matcher(f).find())
                .toList();
            String jvmClass = "M" + moduleId.substring(1);
            check(jvmModuleArtifacts.size() == 1
                    && jvmModuleArtifacts.get(0).equals(
                        jvmClass + ".java"),
                "the JVM module class carries the same identity ("
                    + jvmClass + ".java): " + jvmModuleArtifacts);
            String mainJava = Files.readString(jvmOut.resolve("Main.java"));
            String otherJava = Files.readString(
                jvmOut.resolve("SubOther.java"));
            check(mainJava.contains(jvmClass + ".")
                    && otherJava.contains(jvmClass + "."),
                "both JVM importers wire the same module class (one"
                    + " identity across backends)");
            List<String> javacCmd = new ArrayList<>(List.of("javac",
                "-encoding", "UTF-8"));
            javacCmd.addAll(artifactFilesUnder(jvmOut).stream()
                .filter(f -> f.endsWith(".java")).toList());
            ProcessOutcome javac = runProcess(jvmOut, javacCmd);
            check(javac.exitCode() == 0,
                "the JVM identity fixture compiles: " + javac.output());
            ProcessOutcome jvmRun = runProcess(jvmOut, List.of("java",
                "-cp", ".", "Main"));
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("OK\nOK"),
                "the shared module executes once per importer through the"
                    + " single JVM module class: " + jvmRun.output());

            // (b) A manifest byte change (whitespace-only) changes the
            // deployment digest and every derived semantic identity.
            String manifestText = Files.readString(
                proj.resolve("deal.json"));
            Files.writeString(proj.resolve("deal.json"),
                manifestText + "\n");
            ProjectContext changed = locateContext(entry.toString());
            check(changed != null, "the whitespace-edited manifest still"
                + " locates");
            String changedDigest = changed.projectDeploymentIdentity()
                .validatedManifestContentDigest();
            check(!changedDigest.equals(digest),
                "a manifest byte change changes the deployment digest");
            check(changed.projectDeploymentIdentity().canonicalManifestUri()
                    .equals(context.projectDeploymentIdentity()
                        .canonicalManifestUri()),
                "the canonical manifest URI is unchanged by the whitespace"
                    + " edit");
            String changedId = expectedDeploymentModuleId(changedDigest,
                canonicalUri);
            check(!changedId.equals(moduleId),
                "the manifest byte change changes the derived"
                    + " deploymentModuleId (and every derived semantic"
                    + " identity)");
            Path changedOut = base.resolve("changed_out");
            String[] changedRun = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output",
                changedOut.toString()});
            check("0".equals(changedRun[0]),
                "the recompile after the manifest byte change succeeds: "
                    + changedRun[1]);
            check(artifactFilesUnder(changedOut).contains(
                    changedId + ".lua")
                    && !artifactFilesUnder(changedOut).contains(
                        moduleId + ".lua"),
                "the recompiled artifact set carries the new identity only"
                    + " (deterministic compile outputs reflect the changed"
                    + " digest): " + artifactFilesUnder(changedOut));
            check(Files.readString(changedOut.resolve("main.lua"))
                    .contains("require(\"" + changedId + "\")"),
                "the recompiled entry wires the changed identity");

            // (c) A source relocation changes that source's identity
            // while the deployment digest stays.
            Path renamed = common.resolve("renamed.deal");
            Files.move(shared, renamed);
            write(proj, "src/sub/other.deal",
                "import * as shared from \"../../../common/renamed\"\n"
                    + "export function other(): string { return"
                    + " shared.greet(); }\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as shared from \"../../common/renamed\"\n"
                    + "import * as other from \"./sub/other\"\n"
                    + "export function main(): null {\n"
                    + "  console.log(shared.greet());\n"
                    + "  console.log(other.other());\n"
                    + "  return null;\n"
                    + "}\n");
            ProjectContext relocated = locateContext(entry.toString());
            check(relocated != null,
                "the relocated-source project still locates");
            check(relocated.projectDeploymentIdentity()
                    .validatedManifestContentDigest().equals(changedDigest),
                "the deployment digest is unchanged by the source"
                    + " relocation");
            String relocatedId = expectedDeploymentModuleId(changedDigest,
                canonicalFileUri(renamed));
            check(!relocatedId.equals(changedId)
                    && !relocatedId.equals(moduleId),
                "a source relocation changes that source's identity"
                    + " (deploymentModuleId) while the digest stays");
            Path relocatedOut = base.resolve("relocated_out");
            String[] relocatedRun = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output",
                relocatedOut.toString()});
            check("0".equals(relocatedRun[0]),
                "the recompile after the source relocation succeeds: "
                    + relocatedRun[1]);
            check(artifactFilesUnder(relocatedOut).contains(
                    relocatedId + ".lua")
                    && !artifactFilesUnder(relocatedOut).contains(
                        changedId + ".lua"),
                "the relocated recompile emits the relocated source's new"
                    + " identity only: " + artifactFilesUnder(relocatedOut));

            // (d) Privacy: the successful (a) artifact sets never carry a
            // private identity URI, the deployment digest, or the
            // deploymentModuleId outside import wiring.
            assertArtifactPrivacy(luaDir, digest, moduleId,
                "LuaJIT artifact set");
            assertArtifactPrivacy(jvmOut, digest, moduleId,
                "JVM artifact set");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 6. Diagnostic range gates: manifest (including byte-level
    //         decode), path, and class diagnostics carry complete SOURCE
    //         scalar ranges (or the pinned synthetic shape with anchor
    //         notes) through the canonical formatter and
    //         --diagnostics-json; formatted and structured agree.
    // =========================================================================

    private static void testDiagnosticRangeGates() throws Exception {
        System.out.println("-- Gate 6: complete scalar diagnostic ranges --");

        // (a) Byte-level decode E2010: an invalid UTF-8 continuation byte
        // in the manifest is one E2010 at the first offending byte range.
        Path d = Files.createTempDirectory("deal_gate_decode_");
        try {
            write(d, "src/main.deal",
                "export function main(): null { return null; }\n");
            String prefixText = "{\"languageVersion\": \"1.2\","
                + " \"output\": \"";
            byte[] prefix = prefixText.getBytes(StandardCharsets.UTF_8);
            byte[] suffix = "\", \"backend\": \"luajit\"}\n"
                .getBytes(StandardCharsets.UTF_8);
            byte[] manifestBytes = new byte[prefix.length + 2
                + suffix.length];
            System.arraycopy(prefix, 0, manifestBytes, 0, prefix.length);
            manifestBytes[prefix.length] = (byte) 0xC2;
            manifestBytes[prefix.length + 1] = (byte) 0x41;
            System.arraycopy(suffix, 0, manifestBytes, prefix.length + 2,
                suffix.length);
            writeBytes(d.resolve("deal.json"), manifestBytes);
            Path entry = d.resolve("src/main.deal").toAbsolutePath();
            Path decodeJson = d.resolve("decode_diag.json");
            String[] run = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                decodeJson.toString()});
            check("1".equals(run[0]), "the malformed-UTF-8 manifest exits 1");
            check(run[1].contains("E2010")
                    && run[1].contains("not strictly valid UTF-8"),
                "the malformed byte sequence is one E2010 naming the"
                    + " strict UTF-8 decode: " + run[1]);
            check(run[1].contains("deal.json:1:" + (prefix.length + 1)
                    + "-1:" + (prefix.length + 2))
                    && run[1].contains("[span 1]"),
                "the decode E2010 anchors at the first offending byte"
                    + " (deal.json:1:" + (prefix.length + 1) + "-1:"
                    + (prefix.length + 2) + ", span 1): " + run[1]);
            String doc = Files.readString(decodeJson);
            check("E2010".equals(jsonField(doc, "code"))
                    && "1".equals(jsonField(doc, "scalarLength"))
                    && String.valueOf(prefix.length).equals(
                        jsonField(doc, "startScalarOffset"))
                    && "SOURCE".equals(jsonField(doc, "origin")),
                "the structured decode E2010 pins the first offending byte"
                    + " range: " + doc);
            checkFormattedStructuredAgree(run[1], doc, "decode E2010");
            ProjectLocator.LocateResult expected = ProjectLocator.locate(
                entry.toString(), null);
            check(expected.e2010() != null
                    && doc.equals(DiagnosticStructuredOutput.toJson(
                        List.of(expected.e2010()))),
                "the structured decode document is field-exact to"
                    + " ProjectLocator's own diagnostic");
            check(!run[1].contains("file:/")
                    && !doc.contains("file:/")
                    && !Pattern.compile("m[0-9a-f]{16}").matcher(doc).find(),
                "no private identity URI or deploymentModuleId appears in"
                    + " the decode diagnostics (formatted or structured)");

            // (b) Manifest value-range E2010: a wrong languageVersion.
            write(d, "deal.json", "{\"languageVersion\": \"1.1\"}");
            Path schemaJson = d.resolve("schema_diag.json");
            String[] schema = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                schemaJson.toString()});
            check("1".equals(schema[0]) && schema[1].contains("E2010")
                    && schema[1].contains("must be exactly \"1.2\"")
                    && schema[1].contains("deal.json:1:21-1:26")
                    && schema[1].contains("[span 5]"),
                "the wrong languageVersion is E2010 at the value range"
                    + " (deal.json:1:21-1:26, span 5): " + schema[1]);
            String schemaDoc = Files.readString(schemaJson);
            check("5".equals(jsonField(schemaDoc, "scalarLength"))
                    && "21".equals(jsonField(schemaDoc, "startColumn"))
                    && "SOURCE".equals(jsonField(schemaDoc, "origin")),
                "the structured schema E2010 pins the value range: "
                    + schemaDoc);
            checkFormattedStructuredAgree(schema[1], schemaDoc,
                "schema E2010");
            ProjectLocator.LocateResult schemaExpected =
                ProjectLocator.locate(entry.toString(), null);
            check(schemaExpected.e2010() != null
                    && schemaDoc.equals(DiagnosticStructuredOutput.toJson(
                        List.of(schemaExpected.e2010()))),
                "the structured schema document is field-exact to"
                    + " ProjectLocator's own diagnostic");

            // (c) Zero-manifest discovery E2010: the pinned synthetic
            // shape plus the anchor note.
            Path z = Files.createTempDirectory("deal_gate_noman_");
            try {
                write(z, "main.deal",
                    "export function main(): null { return null; }\n");
                Path zEntry = z.resolve("main.deal").toAbsolutePath();
                Path zJson = z.resolve("discovery_diag.json");
                String[] zero = runCliCapturingErr(new String[]{
                    "compile", zEntry.toString(), "--diagnostics-json",
                    zJson.toString()});
                check("1".equals(zero[0]) && zero[1].contains("E2010")
                        && zero[1].contains("no deal.json")
                        && zero[1].contains("main.deal:1:1-1:1")
                        && zero[1].contains("[span 0]")
                        && zero[1].contains("note: missing anchor:"),
                    "zero manifests is one E2010 with the pinned synthetic"
                        + " range and the anchor note: " + zero[1]);
                String zeroDoc = Files.readString(zJson);
                check("SYNTHETIC".equals(jsonField(zeroDoc, "origin"))
                        && "0".equals(jsonField(zeroDoc, "scalarLength"))
                        && zeroDoc.contains("\"message\": \"missing anchor:"),
                    "the structured discovery E2010 carries the synthetic"
                        + " shape and the anchor note: " + zeroDoc);
                checkFormattedStructuredAgree(zero[1], zeroDoc,
                    "discovery E2010");
            } finally {
                deleteRecursively(z);
            }
        } finally {
            deleteRecursively(d);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Project Integration Gates Test (ISSUE-0270) ===\n");

        testClassFreeOutOfRootBothBackends();
        testExternCImportLoadFfiEmission();
        testFfigenFixtureProjects();
        testOutOfRootClassBothBackends();
        testDeclarationClassGates();
        testImportResolutionErrorGates();
        testIdentityGates();
        testDiagnosticRangeGates();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
