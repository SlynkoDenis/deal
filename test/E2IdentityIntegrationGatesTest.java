package deal.test;

import deal.Main;
import deal.descriptors.CanonicalRuntimeTypeDescriptor;
import deal.descriptors.DescriptorAst;
import deal.descriptors.DescriptorParseResult;
import deal.descriptors.DescriptorSyntaxError;
import deal.project.ProjectContext;
import deal.project.ProjectLocator;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.function.Consumer;
import java.util.regex.Pattern;

/**
 * ISSUE-0316 E2 identity integration gates and the final release gate
 * (epic sequencing item 9, design sources
 * {@code descriptor-identity-propagation} Verification 5/6/7 and
 * {@code deal-v1.2-int32-and-bytes-architecture} Verification 2/4): the
 * pinned E2-integration scenarios run through the real production
 * pipeline (project context &#8594; source resolution &#8594; identity
 * assembly &#8594; checker &#8594; backends &#8594; real luajit /
 * javac+java subprocesses) on both LuaJIT and JVM — never a
 * component-level stub.
 *
 * <ul>
 *   <li><b>Gate 1 — multi-component roots</b> ({@code src},
 *       {@code lib}, {@code lib/utils}): every rooted class projects
 *       its distinct canonical descriptor ({@code @src/User},
 *       {@code @src/models/Thing}, {@code @lib/Widget},
 *       {@code @lib/utils/deep/Gadget}); repeated compiles are
 *       byte-identical (byte-stable); the descriptors parse and render
 *       byte-identically through the production service; the artifacts
 *       run on both backends and the jsonable round trip proves the
 *       runtime construction tags byte-match the canonical identity
 *       text (any drift fails the runtime's byte-exact check).</li>
 *   <li><b>Gate 2 — dot-bearing configured root</b> (root text
 *       {@code src.models}): the legal projection
 *       {@code @src.models/User} is emitted by both backends, parses
 *       and round-trips byte-identically, and byte-matches its runtime
 *       tag on both backends; the class-name-position dotted form
 *       {@code @src.models.User} is parse-rejected and never
 *       emitted.</li>
 *   <li><b>Gate 3 — dotted externals key</b> ({@code host.cfg}): the
 *       legal projection {@code @$external/host.cfg/ServerConfig}
 *       flows through the production orchestrator's externals
 *       classification into the {@code load_host} declared map and the
 *       function-parameter descriptor, runs against a canonical host
 *       fixture (runtime tag byte-match at load and at the call
 *       boundary), and the dotted-legacy tag
 *       {@code @host.cfg/ServerConfig} fails E8011 end-to-end against
 *       the canonical projection. The JVM arm compiles the declared
 *       host class export into the synthesized shared record with the
 *       canonical projection (ISSUE-0303,
 *       jvm-v12-host-abi-completion D4), never the legacy tag, and
 *       runs the constructed record across the class-typed boundary
 *       through a Java host implementation.</li>
 *   <li><b>Gate 4 — unrepresentable required public identity</b> (E2
 *       D6 component rules): a configured root text containing a
 *       descriptor metacharacter ({@code a@b}) and a source-relative
 *       component containing a contiguous arrow ({@code x-&gt;y}) are
 *       E2010 at the class span before any metadata/artifact on both
 *       backends (no partial publication); class-free code in the
 *       unrepresentable root continues compiling and running on both
 *       backends (E2010 only when required).</li>
 *   <li><b>Gate 5 — class-free out-of-root continuation</b>: the
 *       out-of-root class-free project compiles and runs on both
 *       backends and its emitted project artifacts contain no public
 *       descriptor text anywhere.</li>
 *   <li><b>Gate 6 — private-identity exclusion and legacy emission
 *       pins</b>: canonical URIs, the deployment digest, and
 *       {@code deploymentModuleId}s never appear in descriptor text,
 *       diagnostic type names, public export keys, or source-language
 *       values of any identity-bearing artifact set; no producer emits
 *       a legacy spelling ({@code T[]}, {@code T|null}, dotted
 *       class-name text, the dotted v1.1 emission shape).</li>
 * </ul>
 *
 * <p>The conformance host-fixture projections merged by T5
 * ({@code test/conformance/host-fixtures/cfg.lua},
 * {@code presence.lua} tags {@code @$external/host.cfg/...},
 * {@code @$external/host.presence/...}) are verified green through the
 * harness's E2 externals classification by the release gate's
 * conformance suites (ConformanceTest / the lane pin tests) — this
 * battery verifies and never re-migrates them.</p>
 */
public class E2IdentityIntegrationGatesTest {

    private static int passed = 0;
    private static int failed = 0;

    // The pinned canonical projection texts under test.
    private static final String DESC_SRC_USER = "@src/User";
    private static final String DESC_SRC_MODELS_THING = "@src/models/Thing";
    private static final String DESC_LIB_WIDGET = "@lib/Widget";
    private static final String DESC_LIB_UTILS_GADGET = "@lib/utils/deep/Gadget";
    private static final String DESC_DOT_ROOT_USER = "@src.models/User";
    private static final String DESC_DOT_ROOT_USER_LEGACY = "@src.models.User";
    private static final String DESC_EXT_ENDPOINT =
        "@$external/host.cfg/Endpoint";
    private static final String DESC_EXT_SERVER =
        "@$external/host.cfg/ServerConfig";
    private static final String DESC_EXT_SERVER_LEGACY =
        "@host.cfg/ServerConfig";
    private static final String DESC_EXT_DESCRIBE =
        "(@$external/host.cfg/ServerConfig)->string";

    /**
     * The canonical deployed host implementation of gate 3
     * ({@code host.cfg}): the declared class metas carrying the canonical
     * projection, the mandatory {@code <C>_defaults} tables (the optional
     * {@code endpoint} omitted as the runtime's missing sentinel), and the
     * {@code describe} export. Shared by the harness artifact run and the
     * release-owned production artifact run (the dotted-legacy re-pin below
     * carries the same text with the retired tag).
     */
    private static final String HOST_CFG_LUA =
        "local rt = require(\"deal.runtime\")\n"
            + "return {\n"
            + "  Endpoint = { __kind = \"class\", __classname = \""
            + DESC_EXT_ENDPOINT + "\" },\n"
            + "  Endpoint_defaults = { path = \"/\" },\n"
            + "  ServerConfig = { __kind = \"class\", __classname"
            + " = \"" + DESC_EXT_SERVER + "\" },\n"
            + "  ServerConfig_defaults = { port = 8080, endpoint ="
            + " rt.__MISSING },\n"
            + "  describe = function(s)\n"
            + "    return s.endpoint.path .. \":\" .."
            + " tostring(s.port)\n"
            + "  end,\n"
            + "}\n";

    /** The emitted private module-artifact names: m + 16 lowercase hex. */
    private static final Pattern LUA_MODULE_ID =
        Pattern.compile("m[0-9a-f]{16}");
    private static final Pattern JVM_MODULE_ID =
        Pattern.compile("M[0-9a-f]{16}");

    private static void check(boolean condition, String message) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.err.println("FAIL: " + message);
        }
    }

    /** Writes one fixture file (UTF-8) and returns its absolute path. */
    private static Path write(Path root, String rel, String content)
            throws IOException {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file.toAbsolutePath();
    }

    /**
     * Runs the same CLI-equivalent arguments through the test-scope
     * harness compile entry ({@link HarnessCompileEntry}; ISSUE-0643 P10
     * item 3, mechanism 1) with System.err captured; returns {exitCode,
     * stderr}. This suite's fixtures carry cross-module calls and
     * declaration imports the release-owned production invocation fails
     * closed, while the suite's subject — the E2 identity gates — is
     * arm-independent.
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
     * with System.err captured; returns {exitCode, stderr}. The
     * production-invocation fail-closed probes of this suite resolve the
     * release-owned record and drive the production arm.
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

    /** Recursively copies a directory tree (scratch negative runs). */
    private static void copyTree(Path from, Path to) throws IOException {
        Files.createDirectories(to);
        for (String rel : artifactFilesUnder(from)) {
            Path target = to.resolve(rel);
            Files.createDirectories(target.getParent());
            Files.copy(from.resolve(rel), target);
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

    /**
     * Yields every quoted string literal of {@code content} in order via
     * a linear comment-aware walk (double- and single-quoted forms;
     * {@code //} and {@code /*} comments are skipped; an unterminated
     * segment ends the scan) — never regex backtracking.
     */
    private static void forEachStringLiteral(String content,
                                             boolean singleQuotedAreLiterals,
                                             Consumer<String> sink) {
        int i = 0;
        int n = content.length();
        while (i < n) {
            char c = content.charAt(i);
            if (c == '"' || c == '\'') {
                char quote = c;
                boolean collect = quote == '"' || singleQuotedAreLiterals;
                StringBuilder lit = new StringBuilder();
                int j = i + 1;
                boolean closed = false;
                while (j < n) {
                    char d = content.charAt(j);
                    if (d == '\\') {
                        if (j + 1 < n) {
                            lit.append(d).append(content.charAt(j + 1));
                            j += 2;
                        } else {
                            j++;
                        }
                        continue;
                    }
                    if (d == quote) {
                        closed = true;
                        j++;
                        break;
                    }
                    lit.append(d);
                    j++;
                }
                if (collect) {
                    sink.accept(lit.toString());
                }
                i = closed ? j : n;
            } else if (c == '/' && i + 1 < n
                    && content.charAt(i + 1) == '/') {
                int eol = content.indexOf('\n', i);
                i = eol < 0 ? n : eol + 1;
            } else if (c == '/' && i + 1 < n
                    && content.charAt(i + 1) == '*') {
                int end = content.indexOf("*/", i + 2);
                i = end < 0 ? n : end + 2;
            } else {
                i++;
            }
        }
    }

    /**
     * The production service round trip: {@code text} must parse to one
     * complete {@link DescriptorAst} whose verbatim render is
     * byte-identical to {@code text}.
     */
    private static void assertParseRenderRoundTrip(String text, String label) {
        DescriptorParseResult result = CanonicalRuntimeTypeDescriptor.parse(text);
        check(result instanceof DescriptorAst,
            label + ": '" + text + "' parses to a complete atom: " + result);
        if (result instanceof DescriptorAst ast) {
            String rendered = CanonicalRuntimeTypeDescriptor.render(ast);
            check(text.equals(rendered),
                label + ": render(parse('" + text + "')) is byte-identical"
                    + " (got '" + rendered + "')");
        }
    }

    /**
     * The production service rejection pin: {@code text} must be a
     * {@link DescriptorSyntaxError} of the pinned kind.
     */
    private static void assertParseRejected(String text,
                                            DescriptorSyntaxError.Kind kind,
                                            String label) {
        DescriptorParseResult result = CanonicalRuntimeTypeDescriptor.parse(text);
        check(result instanceof DescriptorSyntaxError
                && ((DescriptorSyntaxError) result).kind() == kind,
            label + ": '" + text + "' is parse-rejected with " + kind
                + " (got " + result + ")");
    }

    /** Javac-compiles and runs one generated JVM artifact set. */
    private static ProcessOutcome javacAndRun(Path outDir) throws Exception {
        List<String> javaFiles = artifactFilesUnder(outDir).stream()
            .filter(f -> f.endsWith(".java")).toList();
        check(!javaFiles.isEmpty() && javaFiles.contains("Main.java"),
            "the JVM artifact set exists with an entry Main.java: "
                + javaFiles);
        if (javaFiles.isEmpty()) {
            return new ProcessOutcome(-1, "no java files");
        }
        List<String> javacCmd = new ArrayList<>(List.of("javac",
            "-encoding", "UTF-8"));
        javacCmd.addAll(javaFiles);
        ProcessOutcome javac = runProcess(outDir, javacCmd);
        check(javac.exitCode() == 0,
            "the JVM artifacts compile with javac: " + javac.output());
        if (javac.exitCode() != 0) {
            return javac;
        }
        return runProcess(outDir, List.of("java", "-cp", ".", "Main"));
    }

    /**
     * The privacy gate over one artifact tree: no canonical {@code file:}
     * URI, no deployment digest, and no deploymentModuleId in runtime
     * descriptor text (string literals), public export keys, or
     * source-language values — the id may appear only as import wiring
     * (the Lua {@code require} path, the JVM module comment,
     * class declaration, and class-name references).
     */
    private static void assertPrivacy(Path tree, String digest, String context)
            throws IOException {
        if (tree == null || !Files.isDirectory(tree)) {
            check(true, context + ": no artifact tree exists (nothing to scan)");
            return;
        }
        for (String rel : artifactFilesUnder(tree)) {
            Path file = tree.resolve(rel);
            byte[] bytes = Files.readAllBytes(file);
            String raw = new String(bytes, StandardCharsets.ISO_8859_1);
            check(!raw.contains("file:/"),
                context + ": no private file: URI in artifact " + rel);
            check(!raw.contains(digest),
                context + ": no deployment digest in artifact " + rel);
            boolean text = rel.endsWith(".lua") || rel.endsWith(".java");
            if (!text) {
                // Compiled JVM binaries legitimately carry the UPPERCASE
                // module class name (the compiled class itself); the
                // lowercase private id never appears outside wiring.
                check(!LUA_MODULE_ID.matcher(raw).find(),
                    context + ": no deploymentModuleId in non-text artifact "
                        + rel);
                continue;
            }
            String content = new String(bytes, StandardCharsets.UTF_8);
            // Strip Lua import wiring (require("<id>")) before the
            // string-literal scan so only descriptor/export/value
            // literals are judged.
            String scanContent = content.replaceAll(
                "require\\(\"m[0-9a-f]{16}\"\\)", "require()");
            forEachStringLiteral(scanContent,
                rel.endsWith(".lua"), lit -> {
                check(!lit.contains(digest) && !lit.contains("file:/")
                        && !LUA_MODULE_ID.matcher(lit).find()
                        && !JVM_MODULE_ID.matcher(lit).find(),
                    context + ": no private identity in a string literal"
                        + " (runtime descriptor / source-language value) of "
                        + rel + ": " + lit);
            });
            if (rel.endsWith(".lua")) {
                for (String line : content.split("\\R", -1)) {
                    if (LUA_MODULE_ID.matcher(line).find()) {
                        check(line.contains("require(\""),
                            context + ": the deploymentModuleId appears in Lua"
                                + " artifact " + rel + " only as import wiring"
                                + " (require): " + line);
                    }
                }
                check(!Pattern.compile("exports\\s*\\[\\s*\"m[0-9a-f]{16}")
                        .matcher(content).find(),
                    context + ": no public export key carries the"
                        + " deploymentModuleId in " + rel);
            }
            if (rel.endsWith(".java")) {
                for (String line : content.split("\\R", -1)) {
                    if (JVM_MODULE_ID.matcher(line).find()) {
                        boolean moduleComment = line.contains("// Module: ");
                        boolean ownClassDecl =
                            line.contains("public final class ")
                                || line.contains("class ");
                        boolean wiringRef = line.contains(".");
                        check(moduleComment || ownClassDecl || wiringRef,
                            context + ": the deploymentModuleId appears in JVM"
                                + " artifact " + rel + " only as wiring (module"
                                + " comment, class declaration, or class-name"
                                + " reference): " + line);
                    }
                }
            }
        }
    }

    /**
     * The legacy-emission gate over the project chunks of one artifact
     * tree (the runtime library, the stdlib copies, and the scratch host
     * fixtures are excluded — they are shared runtime surfaces or
     * test-authored hosts, not producer output for this compilation): no
     * string literal carries a legacy descriptor spelling
     * ({@code T[]}, {@code T|null}, {@code ?null}), a dotted
     * class-name-position atom, or the dotted v1.1 emission shape
     * ({@code @host.cfg/...}).
     */
    private static void assertNoLegacyEmission(Path tree, String context)
            throws IOException {
        for (String rel : artifactFilesUnder(tree)) {
            if (!rel.endsWith(".lua") && !rel.endsWith(".java")) continue;
            if (rel.startsWith("deal/runtime") || rel.startsWith("std/")
                    || rel.equals("host/cfg.lua")
                    || rel.equals("runner.lua")) {
                continue;
            }
            String content = Files.readString(tree.resolve(rel),
                StandardCharsets.UTF_8);
            forEachStringLiteral(content,
                rel.endsWith(".lua"), lit -> {
                check(!lit.contains("[]")
                        && !lit.contains("|null")
                        && !lit.contains("?null"),
                    context + ": no legacy descriptor spelling in a string"
                        + " literal of " + rel + ": " + lit);
                check(!lit.contains("@src.models.User")
                        && !lit.contains("@host.cfg/"),
                    context + ": no dotted class-name text or dotted v1.1"
                        + " emission shape in a string literal of " + rel
                        + ": " + lit);
            });
        }
    }

    /** The located project context's validated deployment digest. */
    private static String deploymentDigest(String entry) {
        ProjectLocator.LocateResult result = ProjectLocator.locate(entry, null);
        ProjectContext context = result.context();
        if (context == null) {
            check(false, "the fixture locates a strict context: " + entry);
            return "missing";
        }
        return context.projectDeploymentIdentity()
            .validatedManifestContentDigest();
    }

    // =========================================================================
    // Gate 1. Multi-component roots (src, lib, lib/utils): distinct,
    //         byte-stable canonical descriptors with matching runtime tags.
    // =========================================================================

    private static void gateMultiComponentRoots() throws Exception {
        System.out.println("-- Gate 1: multi-component roots (src, lib,"
            + " lib/utils) on both backends --");

        Path base = Files.createTempDirectory("deal_e2_multiroot_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\", \"lib\", \"lib/utils\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(proj, "src/User.deal",
                "// @jsonable\n"
                    + "export class User { name: string = \"\"; }\n"
                    + "\n"
                    + "export function check(): string {\n"
                    + "  let u: User = { name: \"a\" };\n"
                    + "  let json: string = User$toJson(u);\n"
                    + "  let back: User | null = User$fromJson(json);\n"
                    + "  if (back !== null) {\n"
                    + "    if (back.name !== \"a\") {\n"
                    + "      throw { code: \"TEST_FAIL\", message:"
                    + " \"roundtrip name mismatch\" };\n"
                    + "    }\n"
                    + "  } else {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"roundtrip fromJson returned null\" };\n"
                    + "  }\n"
                    + "  return json;\n"
                    + "}\n");
            write(proj, "src/models/Thing.deal",
                "export class Thing { n: int = 0; }\n");
            write(proj, "lib/Widget.deal",
                "export class Widget { label: string = \"\"; }\n");
            write(proj, "lib/utils/deep/Gadget.deal",
                "export class Gadget { n: int = 0; }\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as u from \"User\"\n"
                    + "import * as t from \"models/Thing\"\n"
                    + "import * as w from \"Widget\"\n"
                    + "import * as g from \"utils/deep/Gadget\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  let thing: t.Thing = { n: 3 };\n"
                    + "  let widget: w.Widget = { label: \"w\" };\n"
                    + "  let gadget: g.Gadget = { n: 7 };\n"
                    + "  if (thing.n !== 3 || widget.label !== \"w\""
                    + " || gadget.n !== 7) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"field mismatch\" };\n"
                    + "  }\n"
                    + "  console.log(u.check());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            // The four projected descriptors are pairwise distinct.
            List<String> descriptors = List.of(DESC_SRC_USER,
                DESC_SRC_MODELS_THING, DESC_LIB_WIDGET,
                DESC_LIB_UTILS_GADGET);
            for (int i = 0; i < descriptors.size(); i++) {
                for (int j = i + 1; j < descriptors.size(); j++) {
                    check(!descriptors.get(i).equals(descriptors.get(j)),
                        "distinct projections: '" + descriptors.get(i)
                            + "' vs '" + descriptors.get(j) + "'");
                }
            }

            // LuaJIT arm.
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the multi-root project compiles on LuaJIT: " + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            String mainLua = Files.readString(luaDir.resolve("main.lua"));
            String userLua = Files.readString(luaDir.resolve("User.lua"));
            check(userLua.contains("export_class(\"" + DESC_SRC_USER
                    + "\")")
                    || userLua.contains("\"" + DESC_SRC_USER + "\""),
                "the src-root class emits @src/User in its artifact");
            check(mainLua.contains("\"" + DESC_SRC_MODELS_THING + "\"")
                    && mainLua.contains("\"" + DESC_LIB_WIDGET + "\"")
                    && mainLua.contains("\"" + DESC_LIB_UTILS_GADGET + "\""),
                "the cross-root construction sites carry the canonical"
                    + " descriptors @src/models/Thing, @lib/Widget,"
                    + " @lib/utils/deep/Gadget");
            ProcessOutcome luaRun = runProcess(luaDir, List.of("luajit",
                "main.lua"));
            check(luaRun.exitCode() == 0
                    && luaRun.output().trim().equals("{\"name\":\"a\"}"),
                "the multi-root project runs under LuaJIT with the jsonable"
                    + " round trip (the runtime construction tag byte-matches"
                    + " the canonical identity): " + luaRun.output());

            // JVM arm.
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the multi-root project compiles on JVM: " + jvm[1]);
            String userJava = Files.readString(jvmOut.resolve("User.java"));
            String thingJava =
                Files.readString(jvmOut.resolve("ModelsThing.java"));
            String widgetJava =
                Files.readString(jvmOut.resolve("Widget.java"));
            String gadgetJava =
                Files.readString(jvmOut.resolve("DeepGadget.java"));
            check(userJava.contains("\"" + DESC_SRC_USER + "\""),
                "the JVM class carries the canonical identity @src/User");
            check(thingJava.contains("\"" + DESC_SRC_MODELS_THING + "\""),
                "the JVM class carries the canonical identity"
                    + " @src/models/Thing");
            check(widgetJava.contains("\"" + DESC_LIB_WIDGET + "\""),
                "the JVM class carries the canonical identity @lib/Widget");
            check(gadgetJava.contains("\"" + DESC_LIB_UTILS_GADGET + "\""),
                "the JVM class carries the canonical identity"
                    + " @lib/utils/deep/Gadget (the most-specific root"
                    + " lib/utils)");
            ProcessOutcome jvmRun = javacAndRun(jvmOut);
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("{\"name\":\"a\"}"),
                "the multi-root project runs under JVM with the jsonable"
                    + " round trip (the runtime construction tag byte-matches"
                    + " the canonical identity): " + jvmRun.output());

            // Byte-stability: repeated compiles into fresh output
            // directories are byte-identical on both backends.
            Path luaA = base.resolve("det_lua_a");
            Path luaB = base.resolve("det_lua_b");
            String[] detA = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", luaA.toString()});
            String[] detB = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", luaB.toString()});
            check("0".equals(detA[0]) && "0".equals(detB[0]),
                "the repeated LuaJIT compiles succeed: " + detA[1] + detB[1]);
            check(treesIdentical(luaA, luaB),
                "identical inputs reproduce byte-identical LuaJIT artifact"
                    + " trees (byte-stable descriptor text)");
            Path jvmA = base.resolve("det_jvm_a");
            Path jvmB = base.resolve("det_jvm_b");
            String[] detJa = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmA.toString()});
            String[] detJb = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmB.toString()});
            check("0".equals(detJa[0]) && "0".equals(detJb[0]),
                "the repeated JVM compiles succeed: " + detJa[1] + detJb[1]);
            check(treesIdentical(jvmA, jvmB),
                "identical inputs reproduce byte-identical JVM artifact"
                    + " trees (byte-stable descriptor text)");

            // Every emitted descriptor round-trips through the production
            // service byte-identically.
            for (String descriptor : descriptors) {
                assertParseRenderRoundTrip(descriptor,
                    "multi-root projection");
            }

            // Legacy and privacy pins over both artifact sets.
            assertNoLegacyEmission(luaDir, "multi-root LuaJIT");
            assertNoLegacyEmission(jvmOut, "multi-root JVM");
            check(!mainLua.contains("\"@src.User\"")
                    && !userJava.contains("\"@src.User\""),
                "no producer emits dotted class-name-position text"
                    + " (@src.User)");
            String digest = deploymentDigest(entry.toString());
            assertPrivacy(luaDir, digest, "multi-root LuaJIT");
            assertPrivacy(jvmOut, digest, "multi-root JVM");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 2. Dot-bearing configured root (src.models): the legal
    //         @src.models/User projection parses, round-trips, and
    //         byte-matches its runtime tag on both backends.
    // =========================================================================

    private static void gateDotBearingRoot() throws Exception {
        System.out.println("-- Gate 2: dot-bearing configured root"
            + " (src.models) on both backends --");

        Path base = Files.createTempDirectory("deal_e2_dotroot_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src.models\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(proj, "src.models/User.deal",
                "// @jsonable\n"
                    + "export class User { name: string = \"\"; }\n"
                    + "\n"
                    + "export function check(): string {\n"
                    + "  let u: User = { name: \"dot\" };\n"
                    + "  let json: string = User$toJson(u);\n"
                    + "  let back: User | null = User$fromJson(json);\n"
                    + "  if (back !== null) {\n"
                    + "    if (back.name !== \"dot\") {\n"
                    + "      throw { code: \"TEST_FAIL\", message:"
                    + " \"roundtrip name mismatch\" };\n"
                    + "    }\n"
                    + "  } else {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"roundtrip fromJson returned null\" };\n"
                    + "  }\n"
                    + "  return json;\n"
                    + "}\n");
            write(proj, "src.models/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as u from \"User\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  console.log(u.check());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src.models/main.deal").toAbsolutePath();

            // Service-level pins: the legal projection parses and
            // round-trips; the class-name-position dotted form is
            // parse-rejected and never emitted.
            assertParseRenderRoundTrip(DESC_DOT_ROOT_USER,
                "dot-bearing root projection");
            assertParseRejected(DESC_DOT_ROOT_USER_LEGACY,
                DescriptorSyntaxError.Kind.INVALID_CLASS_ATOM,
                "dotted class-name-position text");

            // LuaJIT arm.
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the dot-bearing-root project compiles on LuaJIT: "
                    + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            String userLua = Files.readString(luaDir.resolve("User.lua"));
            check(userLua.contains("\"" + DESC_DOT_ROOT_USER + "\""),
                "the LuaJIT emitter projects @src.models/User (root text"
                    + " src.models, class-name component User)");
            check(!userLua.contains("\"" + DESC_DOT_ROOT_USER_LEGACY + "\""),
                "no producer emits the dotted class-name-position form"
                    + " @src.models.User");
            ProcessOutcome luaRun = runProcess(luaDir, List.of("luajit",
                "main.lua"));
            check(luaRun.exitCode() == 0
                    && luaRun.output().trim().equals("{\"name\":\"dot\"}"),
                "the dot-bearing-root project runs under LuaJIT (the runtime"
                    + " tag byte-matches @src.models/User): "
                    + luaRun.output());

            // JVM arm.
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the dot-bearing-root project compiles on JVM: " + jvm[1]);
            String userJava = Files.readString(jvmOut.resolve("User.java"));
            check(userJava.contains("\"" + DESC_DOT_ROOT_USER + "\""),
                "the JVM emitter carries the canonical identity"
                    + " @src.models/User");
            check(!userJava.contains("\"" + DESC_DOT_ROOT_USER_LEGACY
                    + "\""),
                "no JVM producer emits the dotted class-name-position form"
                    + " @src.models.User");
            ProcessOutcome jvmRun = javacAndRun(jvmOut);
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("{\"name\":\"dot\"}"),
                "the dot-bearing-root project runs under JVM (the runtime tag"
                    + " byte-matches @src.models/User): " + jvmRun.output());

            // Byte-stability on both backends.
            Path luaA = base.resolve("det_lua_a");
            Path luaB = base.resolve("det_lua_b");
            String[] detA = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", luaA.toString()});
            String[] detB = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", luaB.toString()});
            check("0".equals(detA[0]) && "0".equals(detB[0]),
                "the repeated dot-root LuaJIT compiles succeed: "
                    + detA[1] + detB[1]);
            check(treesIdentical(luaA, luaB),
                "the dot-bearing-root LuaJIT artifact tree is byte-stable");

            // Legacy and privacy pins.
            assertNoLegacyEmission(luaDir, "dot-root LuaJIT");
            assertNoLegacyEmission(jvmOut, "dot-root JVM");
            String digest = deploymentDigest(entry.toString());
            assertPrivacy(luaDir, digest, "dot-root LuaJIT");
            assertPrivacy(jvmOut, digest, "dot-root JVM");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 3. Dotted externals key (host.cfg): the legal
    //         @$external/host.cfg/<Name> projection through the
    //         production load_host seam; the dotted-legacy tag fails
    //         E8011 end-to-end; the JVM arm synthesizes the shared
    //         host-class record with the canonical projection and
    //         crosses it through the Java host (ISSUE-0303 D4).
    // =========================================================================

    private static void gateDottedExternals() throws Exception {
        System.out.println("-- Gate 3: dotted externals key (host.cfg)"
            + " through the production load_host seam --");

        Path base = Files.createTempDirectory("deal_e2_ext_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\",\n"
                    + "  \"externals\": {\n"
                    + "    \"host.cfg\": {\n"
                    + "      \"declaration\": \"decl/cfg.d.deal\"\n"
                    + "    }\n  }\n}\n");
            write(proj, "decl/cfg.d.deal",
                "export class Endpoint {\n"
                    + "  path: string;\n"
                    + "}\n"
                    + "\n"
                    + "export class ServerConfig {\n"
                    + "  port: int;\n"
                    + "  endpoint: Endpoint;\n"
                    + "}\n"
                    + "\n"
                    + "export function describe(s: ServerConfig): string;\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as cfg from \"host.cfg\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  let s: cfg.ServerConfig = {\n"
                    + "    port: 9090,\n"
                    + "    endpoint: { path: \"/api\" },\n"
                    + "  };\n"
                    + "  let described: string = cfg.describe(s);\n"
                    + "  console.log(described);\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            // Service-level pins for the dotted-externals projections.
            assertParseRenderRoundTrip(DESC_EXT_SERVER,
                "dotted externals class projection");
            assertParseRenderRoundTrip(DESC_EXT_ENDPOINT,
                "dotted externals nested class projection");
            assertParseRenderRoundTrip(DESC_EXT_DESCRIBE,
                "dotted externals function-parameter descriptor");

            // LuaJIT arm: the production orchestrator's externals
            // classification projects the canonical descriptors into the
            // emitted declared map.
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the dotted-externals project compiles on LuaJIT: "
                    + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            String mainLua = Files.readString(luaDir.resolve("main.lua"));
            check(mainLua.contains("__rt.load_host(\"host.cfg\", {")
                    && mainLua.contains("ServerConfig = \""
                        + DESC_EXT_SERVER + "\",")
                    && mainLua.contains("Endpoint = \""
                        + DESC_EXT_ENDPOINT + "\",")
                    && mainLua.contains("describe = \""
                        + DESC_EXT_DESCRIBE + "\","),
                "the emitted declared map carries the canonical dotted"
                    + " externals projections (load_host raw specifier"
                    + " host.cfg, class atoms @$external/host.cfg/<Name>,"
                    + " and the class-bearing function descriptor)");
            check(!mainLua.contains("\"" + DESC_EXT_SERVER_LEGACY + "\""),
                "no producer emits the dotted v1.1 emission shape"
                    + " @host.cfg/ServerConfig");

            // ISSUE-0624: the declaration-owned host-class construction
            // lands on the production path (semantic-ir-construct-coverage-
            // cutover K10), so the release-owned production invocation of
            // this fixture compiles, publishes the one project artifact, and
            // executes the constructed instance through the deployed host
            // implementation: the ISSUE-0656 CONSTRUCTION_COHERENCE pin over
            // the HOST_DEFAULTS registration seed is retargeted here (never
            // deleted) to the realized construction.
            Path prodOut = base.resolve("prod_probe");
            String[] prod = runProductionCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output", prodOut.toString()});
            check("0".equals(prod[0]),
                "the release-owned production invocation realizes the"
                    + " dotted-externals fixture with the host-declared class"
                    + " construction over the loaded <C>_defaults: " + prod[1]);
            check(Files.exists(prodOut.resolve("main.lua")),
                "the production compile publishes the one project artifact"
                    + " under " + prodOut);
            check(!prod[1].contains("CONSTRUCTION_COHERENCE")
                    && !prod[1].contains("HOST_MODULE_IMPORT"),
                "the production invocation fails at neither the"
                    + " declaration-owned construction shape nor the narrowed"
                    + " import guard: " + prod[1]);
            String productionLua = Files.readString(prodOut.resolve("main.lua"),
                StandardCharsets.UTF_8);
            check(productionLua.contains("__rt.load_host(\"host.cfg\", {")
                    && productionLua.contains("\"" + DESC_EXT_SERVER + "\"")
                    && productionLua.contains("\"" + DESC_EXT_ENDPOINT + "\""),
                "the production project artifact carries the declared-map"
                    + " host load and the canonical class projections");
            write(prodOut, "host/cfg.lua", HOST_CFG_LUA);
            ProcessOutcome productionRun = runProcess(prodOut, List.of("luajit",
                "main.lua"));
            check(productionRun.exitCode() == 0
                    && productionRun.output().trim().equals("/api:9090"),
                "the release-owned production artifact constructs the"
                    + " host-declared class over the loaded defaults and"
                    + " crosses it through the host implementation ("
                    + DESC_EXT_DESCRIBE + "): " + productionRun.output());

            // The canonical host fixture (the T5-conformance shape, not a
            // re-migration — this copy lives in the scratch deployment):
            // require("host.cfg") resolves to ./host/cfg.lua via the
            // default package.path dot-to-slash conversion.
            write(luaDir, "host/cfg.lua", HOST_CFG_LUA);
            ProcessOutcome luaRun = runProcess(luaDir, List.of("luajit",
                "main.lua"));
            check(luaRun.exitCode() == 0
                    && luaRun.output().trim().equals("/api:9090"),
                "the dotted-externals project runs under LuaJIT: the host"
                    + " class tag byte-matches the canonical projection at"
                    + " load and the constructed instance passes the"
                    + " class-bearing boundary check ("
                    + DESC_EXT_DESCRIBE + "): " + luaRun.output());

            // Dotted-legacy re-pin end-to-end: a scratch copy whose host
            // class carries the retired v1.1 emission shape fails E8011
            // at load against the canonical projection.
            Path legacyDir = base.resolve("legacy_run");
            copyTree(luaDir, legacyDir);
            write(legacyDir, "host/cfg.lua",
                "local rt = require(\"deal.runtime\")\n"
                    + "return {\n"
                    + "  Endpoint = { __kind = \"class\", __classname = \""
                    + DESC_EXT_ENDPOINT + "\" },\n"
                    + "  Endpoint_defaults = { path = \"/\" },\n"
                    + "  ServerConfig = { __kind = \"class\", __classname"
                    + " = \"" + DESC_EXT_SERVER_LEGACY + "\" },\n"
                    + "  ServerConfig_defaults = { port = 8080, endpoint ="
                    + " rt.__MISSING },\n"
                    + "  describe = function(s)\n"
                    + "    return s.endpoint.path .. \":\" .."
                    + " tostring(s.port)\n"
                    + "  end,\n"
                    + "}\n");
            write(legacyDir, "runner.lua",
                "local ok, err = pcall(dofile, \"main.lua\")\n"
                    + "if ok then\n"
                    + "  print(\"RUN_OK\")\n"
                    + "else\n"
                    + "  print(\"RUN_FAILED\")\n"
                    + "  if type(err) == \"table\" then\n"
                    + "    for k, v in pairs(err) do\n"
                    + "      print(k .. \"=\" .. tostring(v))\n"
                    + "    end\n"
                    + "  else\n"
                    + "    print(tostring(err))\n"
                    + "  end\n"
                    + "end\n");
            ProcessOutcome legacyRun = runProcess(legacyDir, List.of("luajit",
                "runner.lua"));
            check(legacyRun.output().contains("RUN_FAILED")
                    && legacyRun.output().contains("code=E8011")
                    && legacyRun.output().contains("expected="
                        + DESC_EXT_SERVER)
                    && legacyRun.output().contains("actual="
                        + DESC_EXT_SERVER_LEGACY),
                "the dotted-legacy tag @host.cfg/ServerConfig fails E8011"
                    + " identity mismatch against the canonical projection"
                    + " @$external/host.cfg/ServerConfig at host load: "
                    + legacyRun.output());

            // JVM arm: ISSUE-0303 (jvm-v12-host-abi-completion D4)
            // supports declared host class exports — the compile
            // succeeds, the synthesized shared record carries the
            // canonical projection, the dotted-legacy tag appears
            // nowhere, and the constructed record crosses the
            // class-typed boundary through the Java host.
            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the dotted-externals project compiles on JVM (declared"
                    + " host class exports are supported): " + jvm[1]);
            boolean jvmCanonical = false;
            String serverRecord = null;
            for (String rel : artifactFilesUnder(jvmOut)) {
                if (!rel.endsWith(".java")) continue;
                String content = Files.readString(jvmOut.resolve(rel),
                    StandardCharsets.UTF_8);
                if (content.contains("\"" + DESC_EXT_SERVER + "\"")) {
                    jvmCanonical = true;
                }
                check(!content.contains("\"" + DESC_EXT_SERVER_LEGACY
                        + "\""),
                    "no JVM producer emits the dotted v1.1 emission shape"
                        + " @host.cfg/ServerConfig");
                java.util.regex.Matcher rec = Pattern.compile(
                    "static final class (\\$Host\\$[A-Za-z0-9_$]+"
                        + "ServerConfig) \\{").matcher(content);
                if (rec.find()) {
                    serverRecord = rec.group(1);
                }
            }
            check(jvmCanonical,
                "the synthesized JVM host-class record carries the"
                    + " canonical identity @$external/host.cfg/ServerConfig");
            check(serverRecord != null,
                "the synthesized shared ServerConfig record class exists"
                    + " in the emitted JVM artifact set");
            // The Java host implementation — the JVM analog of the Lua
            // host fixture above: static export methods plus the
            // mandatory <C>_defaults maps, declared over the JVM-mapped
            // carriers (the synthesized shared record).
            write(jvmOut, "HostCfg.java",
                "public final class HostCfg {\n"
                    + "    public static final java.util.Map<String, Object>"
                    + " Endpoint_defaults = java.util.Map.of(\"path\", \"/\");\n"
                    + "    public static final java.util.Map<String, Object>"
                    + " ServerConfig_defaults = java.util.Map.of(\"port\","
                    + " Integer.valueOf(8080), \"endpoint\", new Object());\n"
                    + "    public static Object describe($DealRt."
                    + serverRecord + " s) { return s.endpoint.path"
                    + " + \":\" + s.port; }\n"
                    + "}\n");
            ProcessOutcome jvmRun = javacAndRun(jvmOut);
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("/api:9090"),
                "the dotted-externals project runs under JVM: the"
                    + " synthesized record crosses the class-typed host"
                    + " boundary and the Java host reads its fields ("
                    + DESC_EXT_DESCRIBE + "): " + jvmRun.output());

            // Legacy and privacy pins over both artifact sets.
            assertNoLegacyEmission(luaDir, "dotted-externals LuaJIT");
            assertNoLegacyEmission(jvmOut, "dotted-externals JVM");
            String digest = deploymentDigest(entry.toString());
            assertPrivacy(luaDir, digest, "dotted-externals LuaJIT");
            assertPrivacy(jvmOut, digest, "dotted-externals JVM");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Gate 4. Unrepresentable required public identity (E2 D6 component
    //         rules) is E2010 at the class span before any
    //         metadata/artifact; class-free code in the same root
    //         continues on both backends.
    // =========================================================================

    private static void gateUnrepresentableIdentity() throws Exception {
        System.out.println("-- Gate 4: unrepresentable required public"
            + " identity (root text a@b; relative component x->y) --");

        // (a) A configured root whose text carries a descriptor
        // metacharacter ('@').
        Path base = Files.createTempDirectory("deal_e2_unrep_");
        try {
            Path proj = base.resolve("proj");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"a@b\", \"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(proj, "a@b/Thing.deal",
                "export class Thing { n: int = 0; }\n");
            write(proj, "a@b/free.deal",
                "export function free(): int { return 1; }\n");

            // Class-free continuation: the unrepresentable root's
            // class-free module compiles and runs on both backends.
            write(proj, "src/main.deal",
                "import * as free from \"free\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  let v: int = free.free();\n"
                    + "  if (v !== 1) {\n"
                    + "    throw { code: \"TEST_FAIL\", message:"
                    + " \"free mismatch\" };\n"
                    + "  }\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();
            Path freeLuaOut = base.resolve("free_lua");
            String[] freeLua = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--output",
                freeLuaOut.toString()});
            check("0".equals(freeLua[0]),
                "the class-free module in the unrepresentable root compiles"
                    + " on LuaJIT (E2010 only when required): " + freeLua[1]);
            ProcessOutcome freeLuaRun = runProcess(freeLuaOut,
                List.of("luajit", "main.lua"));
            check(freeLuaRun.exitCode() == 0,
                "the class-free module in the unrepresentable root runs"
                    + " under LuaJIT: " + freeLuaRun.output());
            Path freeJvmOut = base.resolve("free_jvm");
            String[] freeJvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", freeJvmOut.toString()});
            check("0".equals(freeJvm[0]),
                "the class-free module in the unrepresentable root compiles"
                    + " on JVM: " + freeJvm[1]);
            ProcessOutcome freeJvmRun = javacAndRun(freeJvmOut);
            check(freeJvmRun.exitCode() == 0,
                "the class-free module in the unrepresentable root runs"
                    + " under JVM: " + freeJvmRun.output());

            // Class variant: exactly one E2010 at the class span before
            // any artifact on both backends (the class-free runs used
            // explicit --output overrides, so the manifest output never
            // exists).
            write(proj, "src/main.deal",
                "import * as thingmod from \"Thing\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  let t: thingmod.Thing = { n: 1 };\n"
                    + "  return null;\n"
                    + "}\n");
            Path diagJson = base.resolve("unrep_diag.json");
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--diagnostics-json",
                diagJson.toString()});
            check("1".equals(lua[0]),
                "the unrepresentable-root class attempt exits 1 (LuaJIT)");
            String luaErr = lua[1];
            check(luaErr.contains("E2010")
                    && luaErr.contains("Class 'Thing'")
                    && luaErr.contains("not representable")
                    && luaErr.contains("'a@b'"),
                "the unrepresentable root text 'a@b' is E2010 at the class"
                    + " declaration: " + luaErr);
            check(luaErr.contains("Thing.deal:1:8-1:35"),
                "the E2010 anchors at the complete class-name range: "
                    + luaErr);
            check(!luaErr.contains("file:/"),
                "no private identity URI appears in the E2010 diagnostics");
            check(!Files.exists(proj.resolve("build")),
                "no artifact (no class/export/default/FFI metadata or"
                    + " product) exists after the rejection");
            String doc = Files.readString(diagJson);
            check(doc.contains("\"code\": \"E2010\"")
                    && doc.contains("\"scalarLength\": 27")
                    && doc.contains("\"origin\": \"SOURCE\""),
                "the structured document pins the E2010 class-name range: "
                    + doc);

            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("1".equals(jvm[0]) && jvm[1].trim().equals(luaErr.trim()),
                "both backends emit byte-identical E2010 diagnostics"
                    + " (the identity gate precedes backend selection): "
                    + jvm[1]);
            check(!Files.exists(jvmOut),
                "no JVM artifact exists after the rejection");
        } finally {
            deleteRecursively(base);
        }

        // (b) A source-relative component containing a contiguous arrow.
        Path base2 = Files.createTempDirectory("deal_e2_unrep2_");
        try {
            Path proj = base2.resolve("proj");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(proj, "src/x->y/Thing.deal",
                "export class Thing { n: int = 0; }\n");
            write(proj, "src/main.deal",
                "import * as thingmod from \"x->y/Thing\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  let t: thingmod.Thing = { n: 1 };\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();
            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("1".equals(lua[0]),
                "the arrow-component class attempt exits 1: " + lua[1]);
            check(lua[1].contains("E2010")
                    && lua[1].contains("Class 'Thing'")
                    && lua[1].contains("not representable")
                    && lua[1].contains("'x->y'"),
                "the relative module path component 'x->y' is E2010 at the"
                    + " class span: " + lua[1]);
            check(!Files.exists(proj.resolve("build")),
                "no artifact exists after the arrow-component rejection");
            Path jvmOut = base2.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("1".equals(jvm[0]) && jvm[1].trim().equals(lua[1].trim()),
                "both backends emit byte-identical E2010 diagnostics for"
                    + " the arrow component: " + jvm[1]);
            check(!Files.exists(jvmOut),
                "no JVM artifact exists after the arrow-component"
                    + " rejection");
        } finally {
            deleteRecursively(base2);
        }
    }

    // =========================================================================
    // Gate 5. Class-free out-of-root continuation: no public descriptor
    //         is produced anywhere in either backend's artifact set.
    // =========================================================================

    private static void gateClassFreeNoPublicDescriptor() throws Exception {
        System.out.println("-- Gate 5: class-free out-of-root artifacts"
            + " carry no public descriptor anywhere --");

        Path base = Files.createTempDirectory("deal_e2_nodesc_");
        try {
            Path proj = base.resolve("proj");
            Path common = base.resolve("common");
            write(proj, "deal.json",
                "{\n  \"languageVersion\": \"1.2\",\n"
                    + "  \"moduleRoots\": [\"src\"],\n"
                    + "  \"output\": \"build/lua\",\n"
                    + "  \"backend\": \"luajit\"\n}\n");
            write(common, "shared.deal",
                "export function greet(): string { return \"OK\"; }\n");
            write(proj, "src/main.deal",
                "import * as console from \"std/console\"\n"
                    + "import * as shared from \"../../common/shared\"\n"
                    + "\n"
                    + "export function main(): null {\n"
                    + "  console.log(shared.greet());\n"
                    + "  return null;\n"
                    + "}\n");
            Path entry = proj.resolve("src/main.deal").toAbsolutePath();

            String[] lua = runCliCapturingErr(new String[]{
                "compile", entry.toString()});
            check("0".equals(lua[0]),
                "the class-free out-of-root project compiles on LuaJIT: "
                    + lua[1]);
            Path luaDir = proj.resolve("build/lua");
            ProcessOutcome luaRun = runProcess(luaDir, List.of("luajit",
                "main.lua"));
            check(luaRun.exitCode() == 0
                    && luaRun.output().trim().equals("OK"),
                "the class-free out-of-root project runs under LuaJIT: "
                    + luaRun.output());
            for (String rel : artifactFilesUnder(luaDir)) {
                if (!rel.endsWith(".lua")
                        || rel.startsWith("deal/runtime")
                        || rel.startsWith("std/")) {
                    continue;
                }
                String content = Files.readString(luaDir.resolve(rel),
                    StandardCharsets.UTF_8);
                check(!content.contains("@"),
                    "the class-free LuaJIT project artifact " + rel
                        + " carries no descriptor atom text at all");
            }

            Path jvmOut = base.resolve("out_jvm");
            String[] jvm = runCliCapturingErr(new String[]{
                "compile", entry.toString(), "--backend", "jvm",
                "--output", jvmOut.toString()});
            check("0".equals(jvm[0]),
                "the class-free out-of-root project compiles on JVM: "
                    + jvm[1]);
            ProcessOutcome jvmRun = javacAndRun(jvmOut);
            check(jvmRun.exitCode() == 0
                    && jvmRun.output().trim().equals("OK"),
                "the class-free out-of-root project runs under JVM: "
                    + jvmRun.output());
            for (String rel : artifactFilesUnder(jvmOut)) {
                if (!rel.endsWith(".java")) continue;
                String content = Files.readString(jvmOut.resolve(rel),
                    StandardCharsets.UTF_8);
                // The emitted $check carries a pinned grammar-documentation
                // comment about class-atom shapes; outside comment lines no
                // descriptor atom text may exist.
                for (String line : content.split("\\R", -1)) {
                    if (line.trim().startsWith("//")) continue;
                    check(!line.contains("@src/")
                            && !line.contains("@lib/")
                            && !line.contains("@$external/")
                            && !line.contains("@$builtin/")
                            && !line.contains("\"@"),
                        "the class-free JVM project artifact " + rel
                            + " carries no public descriptor text outside"
                            + " the pinned grammar comment: " + line);
                }
                forEachStringLiteral(content, false, lit -> {
                    check(!lit.contains("@"),
                        "the class-free JVM project artifact " + rel
                            + " carries no descriptor string literal: "
                            + lit);
                });
            }

            String digest = deploymentDigest(entry.toString());
            assertPrivacy(luaDir, digest, "class-free LuaJIT");
            assertPrivacy(jvmOut, digest, "class-free JVM");
        } finally {
            deleteRecursively(base);
        }
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== E2 Identity Integration Gates Test"
            + " (ISSUE-0316) ===\n");

        gateMultiComponentRoots();
        gateDotBearingRoot();
        gateDottedExternals();
        gateUnrepresentableIdentity();
        gateClassFreeNoPublicDescriptor();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
