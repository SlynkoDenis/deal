package deal.test;

import deal.Main;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticFormatter;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.DiagnosticStructuredOutput;
import deal.diagnostics.RangeOrigin;
import deal.ast.*;
import deal.checker.*;
import deal.codegen.lua.LuaBackend;
import deal.lexer.*;
import deal.module.*;
import deal.parser.*;
import deal.project.ProjectContext;
import deal.project.ProjectLocator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ir.ReleaseState;
import deal.source.ScalarSourceCursor;
import deal.types.Type;
import deal.types.Types;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/**
 * Tests for the module system, compilation orchestration, and CLI.
 * Covers ISSUE-0008 requirements.
 */
public class ModuleSystemTest {

    private static int passed = 0;
    private static int failed = 0;
    private static Path tmpDir;

    private static void check(boolean condition, String message) {
        if (condition) { passed++; }
        else { failed++; System.err.println("FAIL: " + message); }
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    // =========================================================================
    // Stdlib Compiler Integration Tests (ISSUE-0009)
    // =========================================================================

    private static void testStdlibConsoleCompilerIntegration() throws Exception {
        System.out.println("-- Stdlib Compiler Integration: std/console --");

        writeFile("src/sci_console.deal", """
            import * as console from "std/console"
            export function test(): null { console.log("hello"); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_console.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_console");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib console: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testStdlibTableCompilerIntegration() throws Exception {
        System.out.println("-- Stdlib Compiler Integration: std/table --");

        writeFile("src/sci_table.deal", """
            import * as tbl from "std/table"
            export function getKeys(t: table): string[] { return tbl.keys(t); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_table.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_table");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib table: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testStdlibJsonCompilerIntegration() throws Exception {
        System.out.println("-- Stdlib Compiler Integration: std/json --");

        writeFile("src/sci_json.deal", """
            import * as json from "std/json"
            export function encode(t: table): string { return json.stringify(t); }
            export function decode(s: string): table { return json.parse(s); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_json.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_json");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib json: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testStdlibMathCompilerIntegration() throws Exception {
        System.out.println("-- Stdlib Compiler Integration: std/math --");

        writeFile("src/sci_math.deal", """
            import * as math from "std/math"
            export function absVal(x: number): number { return math.abs(x); }
            export function roundUp(x: number): int { return math.ceil(x); }
            export function roundDown(x: number): int { return math.floor(x); }
            export function bigger(a: int, b: int): int { return math.max(a, b); }
            export function smaller(a: int, b: int): int { return math.min(a, b); }
            export function sqRoot(x: number): number { return math.sqrt(x); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_math.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_math");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, Path.of(".").toAbsolutePath().normalize());

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib math: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testStdlibTimeCompilerIntegration() throws Exception {
        System.out.println("-- Stdlib Compiler Integration: std/time --");

        writeFile("src/sci_time.deal", """
            import * as time from "std/time"
            export function currentTime(): int { return time.nowMillis(); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_time.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_time");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib time: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testStdlibCrossModuleUsage() throws Exception {
        System.out.println("-- Stdlib: Cross-Module Usage (string + math) --");

        writeFile("src/sci_cross.deal", """
            import * as strings from "std/string"
            import * as math from "std/math"
            export function analyze(s: string): int {
                let len: int = strings.length(s);
                return math.maxInt(len, 0);
            }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_cross.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_cross");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, Path.of(".").toAbsolutePath().normalize());

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib cross-module: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }

        // Runtime verification if luajit is available
        if (luajitAvailable() && success) {
            try {
                Path runtimeDest = outputDir.resolve("deal/runtime.lua");
                if (!Files.exists(runtimeDest)) {
                    Files.createDirectories(runtimeDest.getParent());
                    Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
                }

                String luaCode = "package.path = '" + outputDir.toRealPath()
                    + "/?.lua;' "
                    + "local m = require('sci_cross') "
                    + "local result = m.analyze.f('hello') "
                    + "assert(result == 5, 'expected 5, got ' .. tostring(result)) "
                    + "print('OK: stdlib cross-module runtime')";
                ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
                pb.redirectErrorStream(true);
                Process proc = pb.start();
                String output = new String(proc.getInputStream().readAllBytes());
                int exitCode = proc.waitFor();
                check(exitCode == 0,
                    "Stdlib cross-module: runtime verification (exit " + exitCode
                    + "): " + output.trim());
            } catch (Exception e) {
                check(false, "Stdlib cross-module: runtime verification failed: " + e.getMessage());
            }
        }
    }

    private static void testStdlibJsonRoundTrip() throws Exception {
        System.out.println("-- Stdlib: JSON Round-Trip End-to-End --");

        writeFile("src/sci_jsonrt.deal", """
            import * as json from "std/json"
            export function roundTrip(data: table): table {
                let encoded: string = json.stringify(data);
                return json.parse(encoded);
            }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/sci_jsonrt.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sci_jsonrt");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, Path.of(".").toAbsolutePath().normalize());

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "Stdlib json round-trip: no E2003 module-not-found");
        if (!success) {
            System.out.println("  Note: compilation had errors: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }

        // Runtime verification of JSON round-trip
        if (luajitAvailable() && success) {
            try {
                Path runtimeDest = outputDir.resolve("deal/runtime.lua");
                if (!Files.exists(runtimeDest)) {
                    Files.createDirectories(runtimeDest.getParent());
                    Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
                }

                String luaCode = "package.path = '" + outputDir.toRealPath()
                    + "/?.lua;' "
                    + "local m = require('sci_jsonrt') "
                    + "local input = {a=1, b='hi', c=true} "
                    + "local result = m.roundTrip.f(input) "
                    + "assert(result.a == 1, 'a mismatch: ' .. tostring(result.a)) "
                    + "assert(result.b == 'hi', 'b mismatch: ' .. tostring(result.b)) "
                    + "assert(result.c == true, 'c mismatch: ' .. tostring(result.c)) "
                    + "print('OK: stdlib json round-trip')";
                ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
                pb.redirectErrorStream(true);
                Process proc = pb.start();
                String output = new String(proc.getInputStream().readAllBytes());
                int exitCode = proc.waitFor();
                check(exitCode == 0,
                    "Stdlib json round-trip: runtime verification (exit " + exitCode
                    + "): " + output.trim());
            } catch (Exception e) {
                check(false, "Stdlib json round-trip: runtime verification failed: " + e.getMessage());
            }
        }
    }


    // =========================================================================
    // Helpers
    // =========================================================================

    private static Path writeFile(String relativePath, String content) throws IOException {
        Path file = tmpDir.resolve(relativePath);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file;
    }

    // =========================================================================
    // Exact-v1.2 project configuration through the CLI (ISSUE-0269)
    // =========================================================================

    /**
     * The strict exact-v1.2 project surface through the production CLI:
     * one ancestor deal.json with languageVersion "1.2" governs the
     * graph, malformed manifests fail E2010 before any override is
     * consulted, zero/two ancestor manifests are one E2010 with the
     * pinned notes, valid CLI aliases override a valid manifest, invalid
     * CLI overrides are CliDiagnostics, and the tolerant DealConfig
     * reader — permissive JSON, duplicate last-wins, the legacy externals
     * list form, lua/js backends, the absent-manifest default config —
     * is gone (its behavior is re-pinned by the strict
     * ProjectLocatorTest/StrictManifestParserTest suites).
     */
    private static void testStrictProjectConfiguration() throws Exception {
        System.out.println("-- Exact-v1.2 project configuration (strict) --");

        // (1) A minimal strict manifest compiles through the new locator:
        // the default backend is luajit and the default output is
        // <manifestDirectory>/build/lua.
        Path minEntry = writeFile("strict_proj/src/min_main.deal",
            "export function main(): null { return null; }\n"
            + "export function run(): int { return 7; }\n").toAbsolutePath();
        writeFile("strict_proj/deal.json",
            "{\n  \"languageVersion\": \"1.2\",\n  \"moduleRoots\": [\"src\"]\n}\n");
        Path defaultOut = tmpDir.resolve("strict_proj/build/lua");
        String[] minRun = runCliCapturingErr(new String[] {
            "compile", minEntry.toString()});
        check("0".equals(minRun[0]),
            "minimal strict manifest compiles, got " + minRun[0] + ": " + minRun[1]);
        check(Files.exists(defaultOut.resolve("min_main.lua")),
            "the backend-dependent default output build/lua holds the artifact");

        // (2) Zero ancestor manifests is one E2010 with the pinned
        // synthetic range plus the v1.2-manifest note.
        Path noManifestEntry = writeFile("no_manifest_proj/src/nm_main.deal",
            "export function main(): null { return null; }\n").toAbsolutePath();
        String[] noManifest = runCliCapturingErr(new String[] {
            "compile", noManifestEntry.toString()});
        check("1".equals(noManifest[0]), "manifest-less compile exits 1");
        check(noManifest[1].contains("E2010") && noManifest[1].contains("no deal.json"),
            "zero-manifest E2010 prints through the canonical formatter: " + noManifest[1]);

        // (3) Two ancestor manifests is one E2010 with candidate notes
        // naming every candidate.
        writeFile("two_proj/deal.json", "{\"languageVersion\": \"1.2\"}\n");
        writeFile("two_proj/nested/deal.json", "{\"languageVersion\": \"1.2\"}\n");
        Path twoEntry = writeFile("two_proj/nested/main.deal",
            "export function main(): null { return null; }\n").toAbsolutePath();
        String[] twoRun = runCliCapturingErr(new String[] {
            "compile", twoEntry.toString()});
        check("1".equals(twoRun[0]), "two-manifest compile exits 1");
        check(twoRun[1].contains("E2010") && twoRun[1].contains("multiple deal.json"),
            "multiple-manifest E2010: " + twoRun[1]);
        check(twoRun[1].contains("candidate manifest:"),
            "candidate notes list every candidate: " + twoRun[1]);

        // (4) Malformed manifests fail E2010 before any override is
        // consulted: duplicate keys, a wrong version, an unknown member,
        // invalid backends (including the retired tolerant aliases), the
        // legacy externals list form, and an absolute root — each exactly
        // one E2010 through the canonical formatter, exit 1.
        for (String bad : new String[] {
                "{\"languageVersion\": \"1.2\", \"backend\": \"luajit\", \"backend\": \"jvm\"}",
                "{\"languageVersion\": \"1.1\"}",
                "{\"languageVersion\": \"1.2\", \"permissions\": []}",
                "{\"languageVersion\": \"1.2\", \"backend\": \"wasm\"}",
                "{\"languageVersion\": \"1.2\", \"backend\": \"lua\"}",
                "{\"languageVersion\": \"1.2\", \"externals\": []}",
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"/absolute\"]}"}) {
            String name = "bad_proj_" + Math.abs(bad.hashCode());
            Path badEntry = writeFile(name + "/main.deal",
                "export function main(): null { return null; }\n").toAbsolutePath();
            writeFile(name + "/deal.json", bad);
            String[] badRun = runCliCapturingErr(new String[] {
                "compile", badEntry.toString(), "--backend", "jvm",
                "--output", "build/x"});
            check("1".equals(badRun[0]), "malformed manifest exits 1: " + bad);
            check(badRun[1].contains("E2010"),
                "malformed manifest is E2010 (override never bypasses): " + badRun[1]);
        }

        // (5) A valid CLI backend alias (trim + lowercase) overrides a
        // valid manifest; the effective backend drives the default
        // output.
        Path aliasEntry = writeFile("alias_proj/src/alias_main.deal",
            "export function main(): null { return null; }\n").toAbsolutePath();
        writeFile("alias_proj/deal.json",
            "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"], \"backend\": \"jvm\"}\n");
        String[] aliasRun = runCliCapturingErr(new String[] {
            "compile", aliasEntry.toString(), "--backend", "lua"});
        check("0".equals(aliasRun[0]),
            "--backend lua alias overrides the manifest: " + aliasRun[1]);
        check(Files.exists(tmpDir.resolve("alias_proj/build/lua/alias_main.lua")),
            "the lua alias selects LuaJIT and the effective-backend default output");

        // (6) An invalid CLI backend alias is a CliDiagnostic (exit 1),
        // never E2010.
        String[] badAlias = runCliCapturingErr(new String[] {
            "compile", minEntry.toString(), "--backend", "wasm"});
        check("1".equals(badAlias[0]), "invalid CLI backend alias exits 1");
        check(badAlias[1].contains("unknown backend alias 'wasm'")
                && badAlias[1].contains("lua, luajit, jvm, js"),
            "invalid alias is a CliDiagnostic naming the supported aliases: "
                + badAlias[1]);
        check(!badAlias[1].contains("E2010"),
            "invalid alias is not an E2010: " + badAlias[1]);

        // (7) An empty/whitespace-only CLI output override is a
        // CliDiagnostic; a valid override is CWD-relative and its
        // directory is created only in the write phase.
        String[] emptyOut = runCliCapturingErr(new String[] {
            "compile", minEntry.toString(), "--output", "   "});
        check("1".equals(emptyOut[0]), "whitespace-only output override exits 1");
        check(emptyOut[1].contains("output override"),
            "whitespace-only override is a CliDiagnostic: " + emptyOut[1]);
        Path cliOut = tmpDir.resolve("cli_over_out");
        String[] cliOutRun = runCliCapturingErr(new String[] {
            "compile", minEntry.toString(), "--output", cliOut.toString()});
        check("0".equals(cliOutRun[0]),
            "valid CLI output override compiles: " + cliOutRun[1]);
        check(Files.exists(cliOut.resolve("min_main.lua")),
            "the CLI output override path holds the artifact");
    }

    // =========================================================================
    // ExportExtractor Tests
    // =========================================================================

    private static void testExportExtractor() throws Exception {
        System.out.println("-- ExportExtractor --");

        String source = """
            export function add(a: int, b: int): int { return a + b; }
            export class Point {
                x: int;
                y: int;
            }
            let localVar: int = 42;
            """;

        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "Parser: no errors");

        ExportExtractor extractor = new ExportExtractor("test", false);
        Map<String, Type> exports = extractor.extract(parse.program());

        check(exports.containsKey("add"), "exports contains add");
        check(exports.containsKey("Point"), "exports contains Point");
        check(!exports.containsKey("localVar"), "exports does not contain localVar");

        Type addType = exports.get("add");
        check(addType instanceof Type.Func, "add is a function type");
        Type.Func addFunc = (Type.Func) addType;
        check(addFunc.paramTypes().size() == 2, "add has 2 params");
        check(addFunc.paramTypes().get(0) == Type.Int.INSTANCE, "add param 0 is int");
        check(addFunc.returnType() == Type.Int.INSTANCE, "add returns int");

        Type pointType = exports.get("Point");
        check(pointType instanceof Type.Class, "Point is a class type");
    }


    // =========================================================================
    // ExportExtractor: async function isAsync propagation (ISSUE-0052)
    // =========================================================================

    private static void testExportExtractorAsyncFunc() throws Exception {
        System.out.println("-- ExportExtractor: async function isAsync --");

        String source = """
            export async function fetch(a: int): int { return a; }
            export function sync(a: int): int { return a; }
            """;

        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "Parser: no errors");

        ExportExtractor extractor = new ExportExtractor("test", false);
        Map<String, Type> exports = extractor.extract(parse.program());

        check(exports.containsKey("fetch"), "exports contains fetch");
        check(exports.containsKey("sync"), "exports contains sync");

        // Async function should have isAsync=true
        Type fetchType = exports.get("fetch");
        check(fetchType instanceof Type.Func, "fetch is a function type");
        Type.Func fetchFunc = (Type.Func) fetchType;
        check(fetchFunc.isAsync(), "fetch should be async");
        check(fetchFunc.paramTypes().size() == 1, "fetch has 1 param");
        check(fetchFunc.paramTypes().get(0) == Type.Int.INSTANCE, "fetch param is int");
        check(fetchFunc.returnType() == Type.Int.INSTANCE, "fetch returns int");

        // Sync function should have isAsync=false
        Type syncType = exports.get("sync");
        check(syncType instanceof Type.Func, "sync is a function type");
        Type.Func syncFunc = (Type.Func) syncType;
        check(!syncFunc.isAsync(), "sync should NOT be async");
    }

    private static void testExportExtractorAsyncFuncTypeAnnotation() throws Exception {
        System.out.println("-- ExportExtractor: async function type annotation isAsync --");

        // Test that a function type annotation with async in an export context
        // propagates isAsync correctly.  We test this by exporting a function
        // whose parameter type is an async function type.
        String source = """
            export function register(cb: async (p: int) => string): null { return null; }
            """;

        LexResult lex = new Lexer(source, "test.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "Parser: no errors");

        ExportExtractor extractor = new ExportExtractor("test", false);
        Map<String, Type> exports = extractor.extract(parse.program());

        check(exports.containsKey("register"), "exports contains register");
        Type registerType = exports.get("register");
        check(registerType instanceof Type.Func, "register is a function type");
        Type.Func registerFunc = (Type.Func) registerType;
        // register itself is sync, but its parameter is an async function type
        check(!registerFunc.isAsync(), "register itself should be sync");
        check(registerFunc.paramTypes().size() == 1, "register has 1 param");

        Type cbType = registerFunc.paramTypes().get(0);
        check(cbType instanceof Type.Func, "cb param is a function type");
        Type.Func cbFunc = (Type.Func) cbType;
        check(cbFunc.isAsync(), "cb param should be async");
        check(cbFunc.paramTypes().size() == 1, "cb has 1 param");
        check(cbFunc.returnType() instanceof Type.String, "cb returns string");
    }

    // =========================================================================
    // ExportExtractor: .d.deal function body validation
    // =========================================================================

    private static void testDeclarationFileBodyValidation() throws Exception {
        System.out.println("-- ExportExtractor: .d.deal body validation --");

        // Valid .d.deal: no function bodies
        String validDecl = """
            export function add(a: int, b: int): int;
            export class Result { value: int; }
            """;

        LexResult lex = new Lexer(validDecl, "test.d.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test.d.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "Parser: no errors for valid .d.deal");

        ExportExtractor extractor = new ExportExtractor("test", true);
        Map<String, Type> exports = extractor.extract(parse.program());
        check(exports.containsKey("add"), "valid .d.deal: exports contains add");
        check(exports.containsKey("Result"), "valid .d.deal: exports contains Result");
        check(extractor.diagnostics().isEmpty(), "valid .d.deal: no diagnostics");

        // Invalid .d.deal: function with body
        String invalidDecl = """
            export function add(a: int, b: int): int { return a + b; }
            """;

        LexResult lex2 = new Lexer(invalidDecl, "test2.d.deal").tokenize();
        ParseResult parse2 = new Parser(lex2.tokens(), "test2.d.deal", lex2.directiveEvents()).parse();
        check(!parse2.hasErrors(), "Parser: no errors for invalid .d.deal");

        ExportExtractor extractor2 = new ExportExtractor("test2", true);
        Map<String, Type> exports2 = extractor2.extract(parse2.program());
        check(exports2.containsKey("add"), "invalid .d.deal: exports still contains add");

        boolean hasE7001 = extractor2.diagnostics().stream()
            .anyMatch(d -> "E7001".equals(d.code()) && "error".equals(d.severity()));
        check(hasE7001, "invalid .d.deal: E7001 for function with body");
    }

    // =========================================================================
    // Module Resolution Tests
    // =========================================================================


    // =========================================================================
    // ExportExtractor: .d.deal with executable let statement
    // =========================================================================

    private static void testDeclarationFileLetStmt() throws Exception {
        System.out.println("-- ExportExtractor: .d.deal let statement --");

        // .d.deal with top-level let statement should produce E7001
        String invalidDecl = """
            export function add(a: int, b: int): int;
            let x: int = 42;
            """;

        LexResult lex = new Lexer(invalidDecl, "test_let.d.deal").tokenize();
        ParseResult parse = new Parser(lex.tokens(), "test_let.d.deal", lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "Parser: no errors for .d.deal with let");

        ExportExtractor extractor = new ExportExtractor("test_let", true);
        Map<String, Type> exports = extractor.extract(parse.program());
        check(exports.containsKey("add"), ".d.deal with let: exports still contains add");

        boolean hasE7001 = extractor.diagnostics().stream()
            .anyMatch(d -> "E7001".equals(d.code()) && "error".equals(d.severity()));
        check(hasE7001, ".d.deal with let: E7001 for executable statement");
    }

    // =========================================================================
    // Topological Sort: Diamond Dependency
    // =========================================================================

    private static void testTopologicalSortDiamond() throws Exception {
        System.out.println("-- Topological Sort: Diamond --");

        // A depends on B and C; B and C both depend on D
        writeFile("src/diamondA.deal", """
            import * as B from "./diamondB"
            import * as C from "./diamondC"
            export function main(): null { return null; }
            export function run(): int { return B.val() + C.val(); }
            """);
        writeFile("src/diamondB.deal", """
            import * as D from "./diamondD"
            export function val(): int { return D.get(); }
            """);
        writeFile("src/diamondC.deal", """
            import * as D from "./diamondD"
            export function val(): int { return D.get() + 10; }
            """);
        writeFile("src/diamondD.deal", """
            export function get(): int { return 5; }
            """);

        Path entryFile = tmpDir.resolve("src/diamondA.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/diamond");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Diamond dependency: compilation succeeded");
        check(Files.exists(outputDir.resolve("diamondA.lua")), "diamondA.lua exists");
        check(Files.exists(outputDir.resolve("diamondD.lua")), "diamondD.lua exists");
    }

    // =========================================================================
    // Topological Sort: Module outside cycle depending on cycle module
    // =========================================================================

    private static void testModuleOutsideCycle() throws Exception {
        System.out.println("-- Module Outside Declaration-Only Cycle --");

        // A and B form a type-only cycle: each module references the
        // other exclusively in type positions (qualified class
        // annotations) — v1.2 function bodies count as ordinary
        // runtime edges (provider-versioned-default-plans D7(a)), so
        // the cycle must carry no runtime edge to stay legal.
        // C depends on A (module outside cycle that depends on cycle
        // module).
        writeFile("src/ocA.deal", """
            import * as B from "./ocB"
            export class TA { tag: int = 1; }
            export function value(): int { return 42; }
            export function foo(x: B.TB): B.TB { return x; }
            """);
        writeFile("src/ocB.deal", """
            import * as A from "./ocA"
            export class TB { tag: int = 2; }
            export function transform(x: A.TA): A.TA { return x; }
            """);
        writeFile("src/ocC.deal", """
            import * as A from "./ocA"
            export function main(): null { return null; }
            export function run(): int { return A.value(); }
            """);

        Path entryFile = tmpDir.resolve("src/ocC.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/oc");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Module outside cycle: compilation succeeded");
        check(Files.exists(outputDir.resolve("ocC.lua")), "ocC.lua exists");
        check(Files.exists(outputDir.resolve("ocA.lua")), "ocA.lua exists");
        check(Files.exists(outputDir.resolve("ocB.lua")), "ocB.lua exists");

        // Verify no E2005 errors (should be declaration-only cycle)
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasE2005 = diags.stream().anyMatch(d -> "E2005".equals(d.code()));
        check(!hasE2005, "Module outside cycle: no E2005");
    }

    private static void testModuleResolution() throws Exception {
        System.out.println("-- Module Resolution --");

        writeFile("src/main.deal", """
            import * as lib from "./lib"
            let x: int = lib.add(1, 2);
            """);
        writeFile("src/lib.deal", """
            export function add(a: int, b: int): int { return a + b; }
            """);

        Path entryFile = tmpDir.resolve("src/main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        Path mainFile = tmpDir.resolve("src/main.deal");
        String resolved = orchestrator.resolveImportPath("./lib", mainFile);
        check(resolved != null, "resolveImportPath returns non-null");
        check(resolved.endsWith("lib.deal"), "resolved path ends with lib.deal");

        resolved = orchestrator.resolveImportPath("./nonexistent", mainFile);
        check(resolved == null, "resolveImportPath returns null for nonexistent");

        // D5: a re-emission without an import declaration span resolves
        // through the T6 resolver and falls back to the canonical
        // synthetic shape plus an anchor note (the resolver's own
        // pinned anchorless carrier).
        CompilerDiagnostic fallback = orchestrator.diagnostics().stream()
            .filter(d -> "E2003".equals(d.code()))
            .findFirst().orElse(null);
        check(fallback != null, "resolveImportPath re-emission records E2003");
        if (fallback != null) {
            check(fallback.message().contains("Module not found: './nonexistent'"),
                "re-emission message names the import path: " + fallback.message());
            check(fallback.range().isCanonicalSynthetic()
                    && fallback.range().origin() == RangeOrigin.SYNTHETIC,
                "resolveImportPath fallback range is canonical synthetic: "
                    + fallback.range());
            check(!fallback.notes().isEmpty(),
                "fallback carries the anchor note: " + fallback.notes());
        }
    }

    // =========================================================================
    // Compilation Orchestration: Single Module
    // =========================================================================

    private static void testSingleModuleCompilation() throws Exception {
        System.out.println("-- Single Module Compilation --");

        writeFile("src/hello.deal", """
            export function main(): null { return null; }
            export function greet(): string { return "hi"; }
            """);

        Path entryFile = tmpDir.resolve("src/hello.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, true, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Single module compilation succeeded");

        Path outputFile = outputDir.resolve("hello.lua");
        check(Files.exists(outputFile), "Output file exists: " + outputFile);

        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        boolean runtimeExists = Files.exists(runtimeDest);
        if (Files.exists(Path.of("deal/runtime.lua"))) {
            check(runtimeExists, "Runtime library copied");
        }

        String luaOutput = Files.readString(outputFile);
        check(luaOutput.contains("greet"), "Output contains greet");
        check(luaOutput.contains("__exportSurfaces[\"hello\"][\"greet\"] = "
                + "{__kind = \"function\", sig = \"()->string\", f = "),
            "Exports greet (the ISSUE-0639 per-module export-surface publication, the "
                + "retained wrapper ABI)");
    }

    // =========================================================================
    // Compilation Orchestration: Multi Module
    // =========================================================================

    private static void testMultiModuleCompilation() throws Exception {
        System.out.println("-- Multi Module Compilation --");

        writeFile("src/main.deal", """
            import * as lib from "./lib"
            export function main(): null { return null; }
            export function run(): int { return lib.add(10, 20); }
            """);
        writeFile("src/lib.deal", """
            export function add(a: int, b: int): int { return a + b; }
            """);

        Path entryFile = tmpDir.resolve("src/main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua2");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, true, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Multi-module compilation succeeded");

        check(Files.exists(outputDir.resolve("main.lua")), "main.lua exists");
        check(Files.exists(outputDir.resolve("lib.lua")), "lib.lua exists");

        String mainLua = Files.readString(outputDir.resolve("main.lua"));
        check(mainLua.contains("require(\"lib\")"), "main.lua requires lib");
    }

    // =========================================================================
    // Compilation Orchestration: Error Handling
    // =========================================================================

    private static void testCompilationWithError() throws Exception {
        System.out.println("-- Compilation With Error --");

        writeFile("src/bad.deal", """
            export function foo(): int { return "not an int"; }
            """);

        Path entryFile = tmpDir.resolve("src/bad.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua3");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(!success, "Compilation with type error should fail");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasTypeError = diags.stream().anyMatch(
            d -> "error".equals(d.severity()));
        check(hasTypeError, "Has type error diagnostic");
    }

    // =========================================================================
    // Circular Import: Runtime dependency (E2005)
    // =========================================================================


    // =========================================================================
    // ISSUE-0052: CompilationOrchestrator — import retention under await
    // =========================================================================

    /**
     * Verify that exprReferencesImport correctly tracks import references
     * through AwaitExpression nodes.  An import used only inside
     * {@code await B.foo()} should still be detected as a runtime usage.
     *
     * <p>This test creates two modules: module A exports an async function,
     * module B imports A and uses it only inside an await expression.
     * The compilation should succeed (no unused import removal issues),
     * confirming that the import is correctly tracked through the
     * AwaitExpression in exprReferencesImport.</p>
     */
    private static void testCompilationOrchestratorAwaitImportRetention() throws Exception {
        System.out.println("-- CompilationOrchestrator: await import retention --");

        // Module A: exports an async function
        writeFile("src/ai_await_lib.deal", """
            export async function getValue(): int { return 42; }
            """);

        // Module B: imports A and uses it under await
        // The import alias "Lib" is used only in: await Lib.getValue()
        // exprReferencesImport must track through AwaitExpression
        writeFile("src/ai_await_main.deal", """
            import * as Lib from "./ai_await_lib"
            export function main(): null { return null; }
            async function worker(): int { return await Lib.getValue(); }
            """);

        Path entryFile = tmpDir.resolve("src/ai_await_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/ai_await");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();

        // The compilation should succeed — if exprReferencesImport didn't
        // handle AwaitExpression, the import might appear unused and cause
        // errors or incorrect cycle detection.
        if (!success) {
            System.out.println("  Compilation diags: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
        check(success, "await import retention: compilation succeeds");
        check(Files.exists(outputDir.resolve("ai_await_main.lua")),
            "await import retention: main.lua exists");
        check(Files.exists(outputDir.resolve("ai_await_lib.lua")),
            "await import retention: lib.lua exists");
    }


    // =========================================================================
    // ISSUE-0056: Cross-module async call without await → E3014
    // =========================================================================

    /**
     * Verify that calling an imported async function without {@code await}
     * produces E3014 across module boundaries.  Module A exports an async
     * function; module B imports A and calls it without await.
     *
     * <p>This is the cross-module complement of the single-file E3014 test
     * in {@code CheckerTest.testAsyncCallWithoutAwait_E3014}.  It exercises
     * the full pipeline: ExportExtractor propagates {@code isAsync},
     * NameResolver resolves the imported symbol to an async function type,
     * and TypeChecker fires E3014 when the call is not inside an
     * {@code await} expression.</p>
     */
    private static void testCrossModuleAsyncCallWithoutAwait_E3014() throws Exception {
        System.out.println("-- Cross-module E3014: imported async called without await --");

        // Module A: exports an async function
        writeFile("src/e3014_xm_lib.deal", """
            export async function compute(): int { return 99; }
            """);

        // Module B: imports A and calls the async function WITHOUT await
        writeFile("src/e3014_xm_main.deal", """
            import * as Lib from "./e3014_xm_lib"
            export function run(): int { return Lib.compute(); }
            """);

        Path entryFile = tmpDir.resolve("src/e3014_xm_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e3014_xm");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();

        // The compilation must fail because Lib.compute() is async and called without await
        check(!success, "cross-module async call without await: compilation must fail");

        boolean hasE3014 = diags.stream()
            .anyMatch(d -> "E3014".equals(d.code()) && "error".equals(d.severity()));
        if (!hasE3014) {
            System.out.println("  Compilation diags: " + diags.stream()
                .filter(d -> "error".equals(d.severity()))
                .map(d -> d.code() + ": " + d.message()).toList());
        }
        check(hasE3014, "cross-module async call without await → E3014");
    }

    private static void testCircularImportRuntime() throws Exception {
        System.out.println("-- Circular Import: Runtime Dependency --");

        // a.deal uses B at top level in a variable initializer -> runtime dependency
        // b.deal imports a but only uses it in function bodies -> type-only from b's side
        // But a.deal's top-level expression creates a runtime dependency cycle
        writeFile("src/rta.deal", """
            import * as B from "./rtb"
            export function main(): null { return null; }
            let x: int = B.getValue();
            export function foo(): int { return 42; }
            """);
        writeFile("src/rtb.deal", """
            import * as A from "./rta"
            export function getValue(): int { return 10; }
            """);

        Path entryFile = tmpDir.resolve("src/rta.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua_cycle_rt");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(!success, "Top-level executable statement should fail in v1.2");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        // v1.2: the top-level `let` is rejected as a module-shape error
        // before any cycle analysis (E1049).  Runtime import cycles can no
        // longer be constructed from source because module top level holds
        // only declarations.
        boolean hasShapeError = diags.stream().anyMatch(
            d -> "error".equals(d.severity())
                && "E1049".equals(d.code()));
        check(hasShapeError, "Has E1049 top-level statement diagnostic");
    }

    // =========================================================================
    // Circular Import: Class field default referencing the cycle (E2005)
    // =========================================================================

    /**
     * DEAL v1.2 evaluates class field defaults at module initialization,
     * so a default expression that references a cyclic import creates a
     * runtime initialization dependency and must be rejected with E2005
     * — even though the cycle looks "declaration-only" at statement level.
     */
    private static void testCircularImportClassFieldDefault() throws Exception {
        System.out.println("-- Circular Import: Class Field Default (runtime dep) --");

        writeFile("src/cfda.deal", """
            import * as B from \"./cfdb\"
            export function main(): null { return null; }
            export class Holder {
              seed: int = B.get(1);
            }
            """);
        writeFile("src/cfdb.deal", """
            import * as A from \"./cfda\"
            export function get(x: int): int { return x + 1; }
            """);

        Path entryFile = tmpDir.resolve("src/cfda.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua_cycle_cfd");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(!success, "Class-field-default cycle must fail in v1.2");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasE2005 = diags.stream().anyMatch(
            d -> "E2005".equals(d.code()));
        check(hasE2005, "Class-field-default cycle: E2005 diagnostic");
    }

    // =========================================================================
    // Circular Import: Declaration-only (allowed)
    // =========================================================================

    private static void testCircularImportDeclarationOnly() throws Exception {
        System.out.println("-- Circular Import: Declaration-Only (allowed) --");

        // Both modules reference the cyclic import exclusively in
        // type positions (qualified class annotations). v1.2 function
        // bodies count as ordinary runtime edges
        // (provider-versioned-default-plans D7(a)), so any call
        // through the cyclic import inside a body makes the cycle a
        // runtime SCC and E2005; a type-only cycle stays legal.
        writeFile("src/da.deal", """
            import * as B from "./db"
            export function main(): null { return null; }
            export class A1 { tag: int = 1; }
            export function foo(x: B.B1): B.B1 { return x; }
            """);
        writeFile("src/db.deal", """
            import * as A from "./da"
            export class B1 { tag: int = 2; }
            export function get(x: A.A1): A.A1 { return x; }
            """);

        Path entryFile = tmpDir.resolve("src/da.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua_cycle_decl");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Declaration-only cycle should succeed");

        // Verify no E2005 errors
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasE2005 = diags.stream().anyMatch(
            d -> "E2005".equals(d.code()));
        check(!hasE2005, "Declaration-only cycle: no E2005 diagnostic");
    }


    // =========================================================================
    // Two Disconnected Cycles: One Declaration-Only, One Runtime (regression)
    // =========================================================================

    private static void testTwoDisconnectedCyclesOneRuntime() throws Exception {
        System.out.println("-- Two Disconnected Cycles: One Declaration-Only, One Runtime --");

        // SCC1: A↔B — declaration-only (only type references in function bodies)
        writeFile("src/tdc_a.deal", """
            import * as B from "./tdc_b"
            export function callB(x: int): int { return B.transform(x); }
            """);
        writeFile("src/tdc_b.deal", """
            import * as A from "./tdc_a"
            export function transform(x: int): int { return x + 1; }
            """);

        // SCC2: X↔Y — runtime (top-level expression uses cyclic import)
        writeFile("src/tdc_x.deal", """
            import * as Y from "./tdc_y"
            let val: int = Y.getVal();
            export function getX(): int { return 1; }
            """);
        writeFile("src/tdc_y.deal", """
            import * as X from "./tdc_x"
            export function getVal(): int { return X.getX(); }
            """);

        // Entry: imports A first (decl-only cycle), then X (runtime cycle)
        writeFile("src/tdc_entry.deal", """
            import * as A from "./tdc_a"
            import * as X from "./tdc_x"
            export function main(): null { return null; }
            export function test(): int { return A.callB(1); }
            """);

        Path entryFile = tmpDir.resolve("src/tdc_entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/tdc");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(!success, "Two disconnected cycles (top-level statement): compilation should fail");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        // v1.2: the top-level `let` in tdc_x.deal is an E1049 module-shape
        // error; no E2005 cycle analysis can fire on v1.2 sources.
        boolean hasE1049 = diags.stream().anyMatch(
            d -> "E1049".equals(d.code()) && "error".equals(d.severity()));
        check(hasE1049, "Two disconnected cycles: E1049 for top-level statement");
    }

    // =========================================================================
    // Two Disconnected Cycles: Both Declaration-Only (should succeed)
    // =========================================================================

    private static void testTwoDisconnectedCyclesBothDecl() throws Exception {
        System.out.println("-- Two Disconnected Cycles: Both Declaration-Only --");

        // SCC1: A↔B — type-only (qualified class annotations only;
        // v1.2 function bodies count as ordinary runtime edges,
        // provider-versioned-default-plans D7(a))
        writeFile("src/tdc2_a.deal", """
            import * as B from "./tdc2_b"
            export class TA { tag: int = 1; }
            export function val(): int { return 1; }
            export function callB(x: B.TB): B.TB { return x; }
            """);
        writeFile("src/tdc2_b.deal", """
            import * as A from "./tdc2_a"
            export class TB { tag: int = 2; }
            export function transform(x: A.TA): A.TA { return x; }
            """);

        // SCC2: C↔D — type-only
        writeFile("src/tdc2_c.deal", """
            import * as D from "./tdc2_d"
            export class TC { tag: int = 3; }
            export function val(): int { return 2; }
            export function callD(x: D.TD): D.TD { return x; }
            """);
        writeFile("src/tdc2_d.deal", """
            import * as C from "./tdc2_c"
            export class TD { tag: int = 4; }
            export function convert(x: C.TC): C.TC { return x; }
            """);

        // Entry: imports A first, then C — its calls are ordinary
        // edges out of the cycles (acyclic)
        writeFile("src/tdc2_entry.deal", """
            import * as A from "./tdc2_a"
            import * as C from "./tdc2_c"
            export function main(): null { return null; }
            export function test(): int { return A.val() + C.val(); }
            """);

        Path entryFile = tmpDir.resolve("src/tdc2_entry.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/tdc2");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        boolean success = orchestrator.compile();
        check(success, "Two disconnected cycles (both decl-only): compilation should succeed");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasE2005 = diags.stream().anyMatch(
            d -> "E2005".equals(d.code()));
        check(!hasE2005, "Two disconnected cycles (both decl-only): no E2005");
    }

    // =========================================================================
    // Stdlib .lua fallback when .d.deal exists without .lua in stdlibDir (regression)
    // =========================================================================

    private static void testStdlibFallbackAfterDdeal() throws Exception {
        System.out.println("-- Stdlib .lua fallback after .d.deal (regression) --");

        // Create a stdlibDir with ONLY .d.deal, no .lua
        Path stdlibDir = tmpDir.resolve("stdlib_fallback");
        Files.createDirectories(stdlibDir.resolve("std"));
        Files.writeString(stdlibDir.resolve("std/string.d.deal"),
            "// DEAL Standard Library: std/string (declaration)\n"
            + "export function length(s: string): int;\n");
        // Intentionally do NOT create std/string.lua

        writeFile("src/sf_main.deal", """
            import * as strings from "std/string"
            export function main(): null { return null; }
            export function getLen(s: string): int { return strings.length(s); }
            """);

        Path entryFile = tmpDir.resolve("src/sf_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/sf");
        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());
        roots.add(stdlibDir.toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, stdlibDir.toAbsolutePath());

        // The compilation should succeed because the .d.deal provides type info.
        // The .lua not being copied is acceptable — the host provides it at runtime.
        // The important thing: no crash/exception during copyStdlibModules.
        boolean success = orchestrator.compile();
        check(success, "Stdlib fallback: compilation should succeed with .d.deal only");

        // Verify that copyStdlibModules was reached and didn't crash.
        // The .lua file may or may not exist depending on classpath resources,
        // but the orchestrator should not have thrown an exception.
        Path stdlibLua = outputDir.resolve("std/string.lua");
        // Either the .lua was found on classpath and copied, or it wasn't.
        // Both outcomes are acceptable — the fix ensures the classpath
        // fallback is at least attempted.
        System.out.println("  std/string.lua in output: " + Files.exists(stdlibLua));
    }

    // =========================================================================
    // Compilation Orchestration: Declaration File
    // =========================================================================

    // =========================================================================
    // Cross-Module Class Tests (F1-F5 fix for MR-0007 review)
    // =========================================================================

    private static void testCrossModuleClassFieldAccess() throws Exception {
        System.out.println("-- Cross-Module Class: Field Access --");

        writeFile("src/cm_class.deal", """
            export class Point { x: int = 0; y: int = 0; }
            export function create(x: int, y: int): Point {
                return { x: x, y: y };
            }
            """);

        writeFile("src/cm_main.deal", """
            import * as P from "./cm_class"
            export function main(): null { return null; }
            export function getX(p: P.Point): int { return p.x; }
            export function getY(p: P.Point): int { return p.y; }
            """);

        Path entryFile = tmpDir.resolve("src/cm_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cm_field");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(success, "Cross-module class field access: compilation should succeed");
        if (!success) {
            for (CompilerDiagnostic d : orchestrator.diagnostics()) {
                System.out.println("  Diag: " + d.code() + ": " + d.message());
            }
        }

        // Verify output files exist
        check(Files.exists(outputDir.resolve("cm_main.lua")),
            "Cross-module class field access: cm_main.lua exists");
        check(Files.exists(outputDir.resolve("cm_class.lua")),
            "Cross-module class field access: cm_class.lua exists");

        // Verify the generated code references the imported class defaults
        String genCode = Files.readString(outputDir.resolve("cm_main.lua"));
        check(genCode.contains("require(\"cm_class\")"),
            "Cross-module class field access: generated code requires cm_class");
    }

    private static void testCrossModuleClassConstruction() throws Exception {
        System.out.println("-- Cross-Module Class: Construction --");

        writeFile("src/cc_class.deal", """
            export class Vec { x: int = 0; y: int = 0; }
            """);

        writeFile("src/cc_main.deal", """
            import * as V from "./cc_class"
            export function main(): null { return null; }
            export function makeVec(): V.Vec {
                return { x: 1, y: 2 };
            }
            """);

        Path entryFile = tmpDir.resolve("src/cc_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cm_constr");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(success, "Cross-module class construction: compilation should succeed");
        if (!success) {
            for (CompilerDiagnostic d : orchestrator.diagnostics()) {
                System.out.println("  Diag: " + d.code() + ": " + d.message());
            }
        }

        // Verify the generated code constructs through the imported
        // default plan (emitter page D4: alias["<C>_plan"]).
        String genCode = Files.readString(outputDir.resolve("cc_main.lua"));
        check(genCode.contains("V.Vec_plan"),
            "Cross-module class construction: generated code uses V.Vec_plan");
        check(genCode.contains("__rt.class_plan_("),
            "Cross-module class construction: generated code uses class_plan_");
    }

    private static void testCrossModuleClassHas() throws Exception {
        System.out.println("-- Cross-Module Class: has() --");

        writeFile("src/ch_class.deal", """
            export class Opt { name?: string; }
            """);

        writeFile("src/ch_main.deal", """
            import * as O from "./ch_class"
            export function main(): null { return null; }
            export function checkName(obj: O.Opt): boolean {
                return has(obj.name);
            }
            """);

        Path entryFile = tmpDir.resolve("src/ch_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cm_has");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(success, "Cross-module class has(): compilation should succeed");
        if (!success) {
            for (CompilerDiagnostic d : orchestrator.diagnostics()) {
                System.out.println("  Diag: " + d.code() + ": " + d.message());
            }
        }
    }

    private static void testQualifiedTypeAnnotation() throws Exception {
        System.out.println("-- Qualified Type Annotation --");

        writeFile("src/qt_class.deal", """
            export class Data { value: int = 0; }
            """);

        writeFile("src/qt_main.deal", """
            import * as D from "./qt_class"
            export function main(): null { return null; }
            export function getValue(d: D.Data): int { return d.value; }
            """);

        Path entryFile = tmpDir.resolve("src/qt_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cm_qt");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(success, "Qualified type annotation: compilation should succeed");
        if (!success) {
            for (CompilerDiagnostic d : orchestrator.diagnostics()) {
                System.out.println("  Diag: " + d.code() + ": " + d.message());
            }
        }
    }

    private static void testCrossModuleClassE2E() throws Exception {
        System.out.println("-- Cross-Module Class: End-to-End Runtime --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("src/ce_class.deal", """
            export class Result { value: int = 0; ok: boolean = true; }
            export function make(value: int): Result {
                return { value: value, ok: true };
            }
            """);

        writeFile("src/ce_main.deal", """
            import * as R from "./ce_class"
            export function main(): null { return null; }
            export function getValue(r: R.Result): int { return r.value; }
            export function makeAndGet(): int {
                let r = R.make(42);
                return r.value;
            }
            """);

        Path entryFile = tmpDir.resolve("src/ce_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cm_e2e");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(success, "Cross-module class E2E: compilation should succeed");
        if (!success) {
            for (CompilerDiagnostic d : orchestrator.diagnostics()) {
                System.out.println("  Diag: " + d.code() + ": " + d.message());
            }
            return;
        }

        // Runtime verification
        try {
            Path runtimeLib = outputDir.resolve("deal/runtime.lua");
            String luaCode = "package.path = '" + outputDir.toRealPath()
                + "/?.lua;' "
                + "local m = require('ce_main') "
                + "local r = m.makeAndGet.f() "
                + "assert(r == 42, 'expected 42, got ' .. tostring(r)) "
                + "print('OK: cross-module class e2e')";
            ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
            pb.redirectErrorStream(true);
            Process proc = pb.start();
            String output = new String(proc.getInputStream().readAllBytes());
            int exitCode = proc.waitFor();
            check(exitCode == 0,
                "Cross-module class E2E: runtime verification (exit " + exitCode
                + "): " + output.trim());
        } catch (Exception e) {
            check(false, "Cross-module class E2E: runtime verification failed: " + e.getMessage());
        }
    }

    private static void testDeclarationFile() throws Exception {
        System.out.println("-- Declaration File --");

        writeFile("src/runner.deal", """
            import * as C from "./calc"
            export function main(): null { return null; }
            export function run(): int { return C.add(1, 2); }
            """);
        writeFile("src/calc.d.deal", """
            export function add(a: int, b: int): int;
            export class Result {
                value: int;
            }
            """);

        Path entryFile = tmpDir.resolve("src/runner.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/lua5");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);

        // ISSUE-0269 (D6 (d)): a class in a rooted non-externals .d.deal
        // has no public module identity — the only available form would
        // be the project form and no ProjectModule identity exists — so
        // the declaration is E2010 at the class name span unconditionally
        // before any class/export metadata or artifact (the retired
        // behavior compiled unlisted declaration classes).
        boolean success = orchestrator.compile();
        check(!success, "a class in an unlisted rooted .d.deal fails the compile");
        check(orchestrator.diagnostics().stream()
                .anyMatch(d -> "E2010".equals(d.code())
                    && d.message().contains("Class 'Result'")),
            "the unlisted declaration class is E2010 at the class name span: "
                + orchestrator.diagnostics());

        check(!Files.exists(outputDir.resolve("calc.lua")),
            "calc.lua is never generated for the rejected declaration module");

        // A class-free declaration file is unchanged: it resolves with a
        // private identity only and compiles.
        writeFile("src/runner_free.deal", """
            import * as C from "./calc_free"
            export function main(): null { return null; }
            export function run(): int { return C.add(1, 2); }
            """);
        writeFile("src/calc_free.d.deal", """
            export function add(a: int, b: int): int;
            """);
        Path freeEntry = tmpDir.resolve("src/runner_free.deal").toAbsolutePath();
        CompilationOrchestrator freeOrchestrator = new CompilationOrchestrator(
            freeEntry, outputDir, false, null, moduleRoots, null);
        check(freeOrchestrator.compile(),
            "a class-free declaration file compiles: " + freeOrchestrator.diagnostics());
        check(!Files.exists(outputDir.resolve("calc_free.lua")),
            "no artifact is generated for a class-free .d.deal");
    }


    // =========================================================================
    // Host Externals (ISSUE-0082, host-module-abi D5)
    // =========================================================================

    /**
     * Compiles an externals-listed bare host import and pins the emitted
     * loader shape: {@code __rt.load_host} with the raw import specifier
     * byte-for-byte ({@code "host/cfg"}, never the dotted typing name), the
     * Lua-keyword declared-map key as a bracket string, the class descriptor
     * carrying the dotted typing/class-identity module path, and the stdlib
     * trusted path still emitting a raw require.
     */
    /**
     * The production orchestrator over a strictly located context (the
     * ISSUE-0269 production path): the effective backend, output root,
     * roots, externals declarations, and stdlib surface all come from
     * the published immutable ProjectContext.
     */
    private static CompilationOrchestrator productionOrchestrator(
            ProjectContext context, Path entryFile, boolean verbose,
            boolean dumpIr) {
        return new CompilationOrchestrator(context, entryFile, verbose,
            dumpIr, false, false, null,
            CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry()));
    }

    /**
     * Locates the temp project's exact-v1.2 manifest through production
     * ProjectLocator and fails the test when the strict locate does not
     * succeed.
     */
    private static ProjectContext locateTempProject(Path entryFile) {
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entryFile.toString(), null);
        check(located.context() != null,
            "strict locate succeeds: " + (located.e2010() != null
                ? located.e2010() : located.cliDiagnostic()));
        return located.context();
    }

    private static void testExternalsHostModuleCompiles() throws Exception {
        System.out.println("-- Externals host module: compile + loader emission --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "host/cfg": { "declaration": "bindings/host-cfg.d.deal" }
              }
            }""");
        // ISSUE-0273: @jsonable on a declaration-file class has no
        // effect (fixed-name-directive-events D4) — the JSON surface is
        // declared explicitly, never synthesized.
        writeFile("bindings/host-cfg.d.deal", """
            export function ping(): int;
            export function repeat(): int;
            export class User {
                name: string;
            }
            export function User$fromJson(s: string): User | null;
            export function User$toJson(u: User): string;
            """);
        writeFile("src/ext_main.deal", """
            import * as cfg from "host/cfg"
            import * as console from "std/console"
            export function main(): null { return null; }
            export function run(): int { console.log("x"); return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/ext_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/ext_host");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        // ISSUE-0269: the project routes through production
        // ProjectLocator + the context-driven orchestrator — the
        // externals declaration is validated (exists/regular/readable)
        // and published in the immutable context.
        ProjectContext context = locateTempProject(entryFile);
        check(context.externals().containsKey("host/cfg"),
            "externals map has host/cfg");
        // The production orchestrator writes to the context's classified
        // output path (the manifest output "build/lua"), never a
        // caller-chosen directory.
        outputDir = Path.of(context.outputPath().absoluteNormalizedPath());

        CompilationOrchestrator orchestrator = productionOrchestrator(
            context, entryFile, false, false);

        boolean success = orchestrator.compile();
        check(success, "Externals host module: compilation should succeed");

        String lua = Files.readString(outputDir.resolve("ext_main.lua"));
        check(lua.contains("__rt.load_host(\"host/cfg\", {"),
            "Loader first argument is the raw import specifier byte-for-byte");
        check(!lua.contains("__rt.load_host(\"host.cfg\""),
            "Loader never emits the dotted typing name as the require path");
        check(!lua.contains("require(\"host/cfg\")"),
            "Host imports never emit a raw require");
        check(lua.contains("[\"repeat\"] = \"()->int\""),
            "Lua-keyword export name emits a bracket-string declared-map key");
        check(lua.contains("ping = \"()->int\""),
            "Safe export name emits a dot-form declared-map key");
        check(lua.contains("User = \"@$external/host/cfg/User\""),
            "Class descriptor uses the canonical @$external projection (external raw key)");
        check(lua.contains("[\"User$fromJson\"] = \"(string)->?@$external/host/cfg/User\""),
            "explicitly declared User$fromJson emits a bracket-string declared-map key");
        check(lua.contains("[\"User$toJson\"] = \"(@$external/host/cfg/User)->string\""),
            "explicitly declared User$toJson emits a bracket-string key");
        boolean dollarOnlyInQuotedKeys = true;
        for (int i = lua.indexOf('$'); i >= 0; i = lua.indexOf('$', i + 1)) {
            int open = lua.lastIndexOf('\"', i);
            int close = lua.indexOf('\"', i + 1);
            if (!(open >= 0 && close >= 0 && open < i && i < close)) {
                dollarOnlyInQuotedKeys = false;
            }
        }
        check(dollarOnlyInQuotedKeys, "loader $ keys stay inside quoted strings");
        check(lua.contains("require(\"std.console\")"),
            "Stdlib import keeps the trusted raw require");
    }

    /**
     * A bare import whose resolution lands on a non-stdlib declaration file
     * that is not listed in deal.json externals is rejected with E2009.
     */
    private static void testExternalsGatingE2009() throws Exception {
        System.out.println("-- Externals gating: unlisted bare .d.deal → E2009 --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {}
            }""");
        writeFile("src/undeclared/hostmod.d.deal", """
            export function ping(): int;
            """);
        writeFile("src/gate_main.deal", """
            import * as cfg from "undeclared/hostmod"
            export function run(): int { return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/gate_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/gate");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        ProjectContext context = locateTempProject(entryFile);
        CompilationOrchestrator orchestrator = productionOrchestrator(
            context, entryFile, false, false);

        boolean success = orchestrator.compile();
        check(!success, "Unlisted bare .d.deal import must fail compilation");
        check(orchestrator.diagnostics().stream()
                .anyMatch(d -> "E2009".equals(d.code())),
            "E2009 reported for the unlisted host import");
    }

    /**
     * An externals-listed declaration file missing on disk is E2010 at
     * the declaration value range during locate (ISSUE-0269, D1 step
     * 4(b)) — the retired E2003-at-import-time surface: a missing
     * declaration is a configuration failure before any resolution, and
     * no context is published.
     */
    private static void testExternalsMissingDeclarationE2010() throws Exception {
        System.out.println("-- Externals declaration missing on disk → E2010 at locate --");

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "host/missing": { "declaration": "bindings/host-missing.d.deal" }
              }
            }""");
        // bindings/host-missing.d.deal intentionally not written
        writeFile("src/missing_main.deal", """
            import * as cfg from "host/missing"
            export function run(): int { return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/missing_main.deal").toAbsolutePath();
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entryFile.toString(), null);
        check(located.context() == null && located.e2010() != null,
            "missing externals declaration fails locate with exactly one E2010");
        if (located.e2010() != null) {
            CompilerDiagnostic e2010 = located.e2010();
            check(e2010.message().contains("host/missing")
                    && e2010.message().contains("bindings/host-missing.d.deal"),
                "E2010 names the entry and the authoritative declaration path: "
                    + e2010.message());
            check(e2010.range().origin() == RangeOrigin.SOURCE
                    && e2010.range().file().endsWith("deal.json"),
                "E2010 anchors at the declaration value range in the manifest: "
                    + e2010.range());
        }
    }

    /**
     * Combined C2+C3 evidence: an externals-listed project compiles, the
     * generated module executes under LuaJIT with a minimal host
     * implementation on package.path, and the wrapped host call returns the
     * runtime-checked value (the loader + from_lua_function pipeline).
     */
    private static void testHostModuleEndToEnd() throws Exception {
        System.out.println("-- Host module E2E: externals-listed project runs under LuaJIT --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "host/cfg": { "declaration": "bindings/host-cfg.d.deal" }
              }
            }""");
        writeFile("bindings/host-cfg.d.deal", """
            export function ping(): int;
            """);
        writeFile("src/host_smoke.deal", """
            import * as cfg from "host/cfg"
            export function main(): null { return null; }
            export function run(): int { return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/host_smoke.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/host_smoke");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        ProjectContext context = locateTempProject(entryFile);
        outputDir = Path.of(context.outputPath().absoluteNormalizedPath());
        CompilationOrchestrator orchestrator = productionOrchestrator(
            context, entryFile, false, false);

        boolean success = orchestrator.compile();
        check(success, "Host E2E: compilation should succeed");
        if (!success) return;

        String lua = Files.readString(outputDir.resolve("host_smoke.lua"));
        check(lua.contains("__rt.load_host(\"host/cfg\", {"),
            "Host E2E: loader emits the raw import specifier");

        // Host implementation placed on package.path (host-environment policy,
        // host-module-abi assumption b): outputDir/host/cfg.lua resolves as
        // ./host/cfg.lua for the verbatim require("host/cfg").
        Path hostImpl = outputDir.resolve("host/cfg.lua");
        Files.createDirectories(hostImpl.getParent());
        Files.writeString(hostImpl, """
            local M = {}
            function M.ping() return 7 end
            return M
            """);

        // Copy the runtime if the classpath/CWD fallback did not (belt and braces).
        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        if (!Files.exists(runtimeDest)) {
            Files.createDirectories(runtimeDest.getParent());
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }

        try {
            String luaCode = "package.path = '" + outputDir.toRealPath()
                + "/?.lua;' "
                + "local m = require('host_smoke') "
                + "local v = m.run.f() "
                + "assert(v == 7, 'expected 7, got ' .. tostring(v)) "
                + "print('OK: host ping -> ' .. tostring(v))";
            ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
            pb.redirectErrorStream(true);
            Process proc = pb.start();
            String output = new String(proc.getInputStream().readAllBytes());
            int exitCode = proc.waitFor();
            check(exitCode == 0,
                "Host E2E: runtime verification (exit " + exitCode + "): "
                    + output.trim());
        } catch (Exception e) {
            check(false, "Host E2E: runtime verification failed: " + e.getMessage());
        }
    }

    /**
     * Regression (C3 review): an externals key containing a backslash must
     * not leak unescaped into generated Lua.  The key reaches descriptor
     * strings as the canonical identity projection
     * ("@$external/host/x\y/User" — the externals raw key through the
     * identity index), and an unescaped backslash makes the generated
     * chunk invalid Lua ("invalid escape sequence" at require time, with
     * no compile-time diagnostic).  The generated module must load AND run
     * under LuaJIT: the loader declared-map values, the loader path
     * argument, and the wrapper signature descriptors all carry the
     * escaped form.
     */
    private static void testHostModuleBackslashExternalsKeyE2E() throws Exception {
        System.out.println("-- Host E2E: backslash externals key emits escaped descriptors --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        // JSON needs the backslash escaped: "host/x\\y" is the key
        // "host/x\y" (the raw import path as written).
        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "host/x\\\\y": { "declaration": "bindings/host-xy.d.deal" }
              }
            }""");
        writeFile("bindings/host-xy.d.deal", """
            export function ping(): int;
            export class User {
                port: int = 0;
            }
            """);
        // The DEAL import path is taken verbatim from the source
        // (parseImportDeclaration keeps the raw string between the
        // quotes), so the raw "host/x\y" matches the JSON
        // externals key byte-for-byte — the reviewer-probe scenario.
        writeFile("src/backslash_smoke.deal", """
            import * as cfg from "host/x\\y"
            export function main(): null { return null; }
            export function echo(u: cfg.User): int { return u.port; }
            export function run(): int { return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/backslash_smoke.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/backslash_smoke");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        ProjectContext context = locateTempProject(entryFile);
        outputDir = Path.of(context.outputPath().absoluteNormalizedPath());
        CompilationOrchestrator orchestrator = productionOrchestrator(
            context, entryFile, false, false);

        boolean success = orchestrator.compile();
        check(success, "Backslash key: compilation should succeed");
        if (!success) return;

        String lua = Files.readString(outputDir.resolve("backslash_smoke.lua"));
        // Generated Lua source must carry the escaped forms (each "\\"
        // here is one backslash in the generated text).
        check(lua.contains("__rt.load_host(\"host/x\\\\y\", {"),
            "Backslash key: loader path argument is Lua-escaped");
        check(lua.contains("User = \"@$external/host/x\\\\y/User\""),
            "Backslash key: loader class descriptor is Lua-escaped");
        check(lua.contains("echo = __rt.function_(\"(@$external/host/x\\\\y/User)->int\", function("),
            "Backslash key: wrapper signature descriptor is Lua-escaped");
        check(!lua.contains("$external/host/x\\y/User\""),
            "Backslash key: no raw (unescaped) descriptor text remains");

        // Host implementation: the raw require path is "host/x\y", so the
        // file lives at outputDir/host/x\y.lua (a literal backslash in the
        // file name on POSIX filesystems).
        Path hostImpl = outputDir.resolve("host").resolve("x\\y.lua");
        Files.createDirectories(hostImpl.getParent());
        Files.writeString(hostImpl, """
            local M = {}
            function M.ping() return 9 end
            M.User = { __kind = "class", __classname = "@$external/host/x\\\\y/User" }
            M.User_defaults = { port = 0 }
            return M
            """);

        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        if (!Files.exists(runtimeDest)) {
            Files.createDirectories(runtimeDest.getParent());
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }

        try {
            String luaCode = "package.path = '" + outputDir.toRealPath()
                + "/?.lua;' "
                + "local m = require('backslash_smoke') "
                + "local v = m.run.f() "
                + "assert(v == 9, 'expected 9, got ' .. tostring(v)) "
                + "print('OK: backslash host ping -> ' .. tostring(v))";
            ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
            pb.redirectErrorStream(true);
            Process proc = pb.start();
            String output = new String(proc.getInputStream().readAllBytes());
            int exitCode = proc.waitFor();
            check(exitCode == 0,
                "Backslash key: runtime verification (exit " + exitCode + "): "
                    + output.trim());
        } catch (Exception e) {
            check(false, "Backslash key: runtime verification failed: " + e.getMessage());
        }
    }

    /**
     * Regression (C3 review round 3): descriptor text embedded in quoted Lua
     * strings at the @jsonable field-descriptor sites must be Lua-escaped.
     * A DEAL @jsonable class holding a host-class field (typed from an
     * externals-listed declaration) emits the class identity descriptor as
     * the field's {@code className} value; the descriptor carries the
     * externals-derived identity projection
     * ("@$external/host/x\y/User" — the externals raw key), so a
     * backslash in the externals key made the generated chunk invalid Lua
     * ("invalid escape sequence" at require time, with no compile-time
     * diagnostic).  The
     * generated module must carry the escaped
     * {@code className = "@$external/host/x\\y/User"} text and load AND run under
     * LuaJIT.
     */
    private static void testHostModuleBackslashExternalsKeyJsonableE2E() throws Exception {
        System.out.println("-- Host E2E: backslash externals key + @jsonable host-class field --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("deal.json", """
            {
              "languageVersion": "1.2",
              "moduleRoots": ["src"],
              "output": "build/lua",
              "backend": "luajit",
              "externals": {
                "host/x\\\\y": { "declaration": "bindings/host-xy.d.deal" }
              }
            }""");
        // ISSUE-0273: @jsonable on a declaration-file class has no
        // effect — the JSON surface is declared explicitly (the
        // checker's jsonable-field rule keys on the exported
        // C$fromJson/C$toJson signatures).
        writeFile("bindings/host-xy.d.deal", """
            export function ping(): int;

            export class User {
                port: int = 0;
            }
            export function User$fromJson(s: string): User | null;
            export function User$toJson(u: User): string;
            """);

        // The @jsonable Wrapper holds a host-class field: the emitted
        // Wrapper_fields descriptor embeds the class identity
        // "@$external/host/x\y/User" as a quoted-string className value.  The null
        // default avoids constructing the host class from DEAL (host-class
        // literals stay latent in production — declaration files have no
        // symbol table), while the field descriptor itself is emitted at
        // module load.
        writeFile("src/jsonable_host.deal", """
            import * as cfg from "host/x\\y"
            // @jsonable
            export class Wrapper {
                u: cfg.User | null = null;
                name: string = "";
            }
            export function main(): null { return null; }
            export function run(): int { return cfg.ping(); }
            """);

        Path entryFile = tmpDir.resolve("src/jsonable_host.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/jsonable_host");
        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());

        ProjectContext context = locateTempProject(entryFile);
        outputDir = Path.of(context.outputPath().absoluteNormalizedPath());
        CompilationOrchestrator orchestrator = productionOrchestrator(
            context, entryFile, false, false);

        boolean success = orchestrator.compile();
        check(success, "Jsonable backslash key: compilation should succeed");
        if (!success) return;

        String lua = Files.readString(outputDir.resolve("jsonable_host.lua"));
        // The @jsonable field descriptor's className value must carry the
        // Lua-escaped form (each "\\" here is one backslash in the
        // generated text).
        check(lua.contains("className = \"@$external/host/x\\\\y/User\""),
            "Jsonable backslash key: field-descriptor className is Lua-escaped");
        check(!lua.contains("$external/host/x\\y/User"),
            "Jsonable backslash key: no raw (unescaped) descriptor text remains");

        // Host implementation on the raw require path outputDir/host/x\y.lua
        // (a literal backslash in the file name on POSIX filesystems),
        // supplying the class META, defaults, and the optional <C>_fields
        // descriptor table the loader copies through (host-module-abi D2).
        Path hostImpl = outputDir.resolve("host").resolve("x\\y.lua");
        Files.createDirectories(hostImpl.getParent());
        Files.writeString(hostImpl, """
            local M = {}
            function M.ping() return 9 end
            M.User = { __kind = "class", __classname = "@$external/host/x\\\\y/User" }
            M.User_defaults = { port = 0 }
            M.User_fields = { { name = "port", jtype = "int", optional = false, nullable = false } }
            -- The @jsonable declaration adds User$fromJson/User$toJson
            -- synthetics to the declared surface; the loader requires them
            -- (never called by this test).
            M["User$fromJson"] = function(s) return nil end
            M["User$toJson"] = function(u) return "" end
            return M
            """);

        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        if (!Files.exists(runtimeDest)) {
            Files.createDirectories(runtimeDest.getParent());
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }
        // The @jsonable pass requires std.json at load; place it on
        // package.path like the host environment would (host policy).
        Path jsonDest = outputDir.resolve("std/json.lua");
        if (!Files.exists(jsonDest)) {
            Files.createDirectories(jsonDest.getParent());
            Files.copy(Path.of("std/json.lua"), jsonDest);
        }

        try {
            String luaCode = "package.path = '" + outputDir.toRealPath()
                + "/?.lua;' "
                + "local m = require('jsonable_host') "
                + "local v = m.run.f() "
                + "assert(v == 9, 'expected 9, got ' .. tostring(v)) "
                + "print('OK: jsonable backslash host ping -> ' .. tostring(v))";
            ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
            pb.redirectErrorStream(true);
            Process proc = pb.start();
            String output = new String(proc.getInputStream().readAllBytes());
            int exitCode = proc.waitFor();
            check(exitCode == 0,
                "Jsonable backslash key: runtime verification (exit " + exitCode + "): "
                    + output.trim());
        } catch (Exception e) {
            check(false, "Jsonable backslash key: runtime verification failed: " + e.getMessage());
        }
    }

    // =========================================================================
    // CLI Tests
    // =========================================================================

    private static void testCli() throws Exception {
        System.out.println("-- CLI --");

        int exitCode = Main.run(new String[]{});
        check(exitCode == 1, "No args -> exit 1");

        exitCode = Main.run(new String[]{"unknown"});
        check(exitCode == 1, "Unknown command -> exit 1");

        exitCode = Main.run(new String[]{"compile"});
        check(exitCode == 1, "Missing entry -> exit 1");

        exitCode = Main.run(new String[]{"compile", "/nonexistent/file.deal"});
        check(exitCode == 1, "Nonexistent entry -> exit 1");

        writeFile("src/cli_test.deal", """
            export function main(): null { return null; }
            export function hello(): string { return "world"; }
            """);
        // ISSUE-0269: the CLI locates exactly one ancestor exact-v1.2
        // manifest — the temp project carries its own.
        writeFile("deal.json",
            "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"]}\n");
        Path entryFile = tmpDir.resolve("src/cli_test.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/cli_test");

        exitCode = Main.run(new String[]{"compile",
            entryFile.toString(), "--output", outputDir.toString()});
        check(exitCode == 0, "Valid compile -> exit 0");
        check(Files.exists(outputDir.resolve("cli_test.lua")),
            "Output file exists");
    }

    /**
     * CLI --diagnostics-json end-to-end on manifest-configuration failures
     * (D8/D10): the flag is parsed here because manifest failures occur
     * before the orchestrator exists. A missing argument is a CLI usage
     * diagnostic; a successful write is field-exact with exit 1 unchanged;
     * an unwritable path is a deterministic I/O diagnostic with exit 1 and
     * no raw exception.
     */
    private static void testCliDiagnosticsJson() throws Exception {
        System.out.println("-- CLI: --diagnostics-json --");

        // Missing argument: usage diagnostic, exit 1.
        String[] missing = runCliCapturingErr(new String[] {
            "compile", "--diagnostics-json"});
        check("1".equals(missing[0]), "--diagnostics-json without a path exits 1");
        check(missing[1].contains("--diagnostics-json requires a path argument"),
            "missing-argument usage diagnostic: " + missing[1]);

        // Usage text documents the flag.
        String[] noArgs = runCliCapturingErr(new String[] {});
        check("1".equals(noArgs[0]), "no-args usage exits 1");
        check(noArgs[1].contains("--diagnostics-json <path>"),
            "usage documents --diagnostics-json: " + noArgs[1]);

        // Manifest-configuration failure: the structured document is
        // field-exact to ProjectLocator's own E2010, the human E2010
        // prints on stderr, exit 1 (ISSUE-0269: the configuration
        // failure surface is E2010, never the retired E2012).
        writeFile("json_err_proj/deal.json", "{\"backend\": \"wasm\"}");
        Path entry = writeFile("json_err_proj/main.deal",
            "export function main(): null { return null; }\n").toAbsolutePath();
        Path outJson = tmpDir.resolve("diag.json");

        String[] captured = runCliCapturingErr(new String[] {
            "compile", entry.toString(), "--diagnostics-json", outJson.toString()});
        check("1".equals(captured[0]),
            "manifest failure with --diagnostics-json exits 1: " + captured[1]);
        check(captured[1].contains("E2010") && captured[1].contains("deal.json"),
            "human E2010 prints on stderr through the formatter: " + captured[1]);

        ProjectLocator.LocateResult expected = ProjectLocator.locate(
            entry.toString(), null);
        check(expected.e2010() != null,
            "the same manifest fails the strict locator with E2010");
        String expectedJson = DiagnosticStructuredOutput.toJson(
            List.of(expected.e2010()));
        String written = Files.readString(outJson);
        check(written.equals(expectedJson),
            "structured document is field-exact:\n" + written);

        // Unwritable path: deterministic I/O diagnostic, exit 1, no stack
        // trace, no raw path exception.
        Path badPath = Path.of("/nonexistent-parent-dir-0413/out.json");
        String[] capturedBad = runCliCapturingErr(new String[] {
            "compile", entry.toString(), "--diagnostics-json", badPath.toString()});
        check("1".equals(capturedBad[0]),
            "unwritable --diagnostics-json exits 1");
        check(capturedBad[1].contains("deal: cannot write diagnostics JSON"),
            "deterministic I/O diagnostic: " + capturedBad[1]);
        check(!capturedBad[1].contains("Exception")
                && !capturedBad[1].contains("\tat "),
            "no raw exception or stack trace escapes: " + capturedBad[1]);
    }

    /** Runs the CLI with System.err captured; returns {exitCode, stderr}. */
    private static String[] runCliCapturingErr(String[] args) throws IOException {
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
        return new String[] {String.valueOf(exitCode),
            err.toString(StandardCharsets.UTF_8)};
    }

    // =========================================================================
    // End-to-End Integration Tests
    // =========================================================================

    private static void testEndToEndSingleModule() throws Exception {
        System.out.println("-- E2E: Single Module --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("src/e2e_single.deal", """
            export function main(): null { return null; }
            export function greet(name: string): string {
                return "Hello, " + name;
            }
            """);

        Path entryFile = tmpDir.resolve("src/e2e_single.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e2e_single");

        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, true, null, roots, null);

        check(orchestrator.compile(), "E2E single: compile succeeded");

        // Copy runtime
        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        if (!Files.exists(runtimeDest)) {
            Files.createDirectories(runtimeDest.getParent());
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }

        // Create test runner
        Path testFile = outputDir.resolve("__test.lua");
        String testLua = """
            local m = require("e2e_single")
            local result = m.greet.f("DEAL")
            assert(result == "Hello, DEAL", "Expected 'Hello, DEAL', got '" .. tostring(result) .. "'")
            print("OK: " .. result)
            """;
        Files.writeString(testFile, testLua);

        ProcessBuilder pb = new ProcessBuilder("luajit", testFile.toString());
        pb.directory(outputDir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes());
        int exit = p.waitFor();

        check(exit == 0, "E2E single: LuaJIT exit 0, output: " + output.trim());
        check(output.contains("Hello, DEAL"), "E2E single: correct greeting");
    }

    private static void testEndToEndMultiModule() throws Exception {
        System.out.println("-- E2E: Multi Module --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("src/e2e_main.deal", """
            import * as lib from "./e2e_lib"
            export function main(): null { return null; }
            export function run(): int { return lib.add(10, 20); }
            """);
        writeFile("src/e2e_lib.deal", """
            export function add(a: int, b: int): int { return a + b; }
            """);

        Path entryFile = tmpDir.resolve("src/e2e_main.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e2e_multi");

        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, true, null, roots, null);

        check(orchestrator.compile(), "E2E multi: compile succeeded");

        // Copy runtime
        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        Files.createDirectories(runtimeDest.getParent());
        if (!Files.exists(runtimeDest)) {
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }

        // Create test runner
        Path testFile = outputDir.resolve("__test.lua");
        String testLua = """
            local m = require("e2e_main")
            local result = m.run.f()
            assert(result == 30, "Expected 30, got " .. tostring(result))
            print("OK: " .. result)
            """;
        Files.writeString(testFile, testLua);

        ProcessBuilder pb = new ProcessBuilder("luajit", testFile.toString());
        pb.directory(outputDir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes());
        int exit = p.waitFor();

        check(exit == 0, "E2E multi: LuaJIT exit 0, output: " + output.trim());
        check(output.contains("OK: 30"), "E2E multi: correct result");
    }

    private static void testEndToEndStdlib() throws Exception {
        System.out.println("-- E2E: Stdlib Import --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        // Create a stdlib with .d.deal and .lua implementation
        Path stdlibDir = tmpDir.resolve("stdlib");
        Files.createDirectories(stdlibDir.resolve("std"));
        Files.writeString(stdlibDir.resolve("std/string.d.deal"),
            "export function length(s: string): int;\n");
        Files.writeString(stdlibDir.resolve("std/string.lua"),
            "local __rt = require(\"deal.runtime\")\n"
            + "local m = {}\n"
            + "m.length = __rt.function_(\"(string)->int\", function(s) "
            + "__rt.check_string(s); return #s end)\n"
            + "return m\n");

        // Create a source file that imports std/string
        writeFile("src/e2e_std.deal", """
            import * as strings from "std/string"
            export function test_len(): int { return strings.length("hello"); }
            export function main(): null { return null; }
            """);

        Path entryFile = tmpDir.resolve("src/e2e_std.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e2e_std");

        List<Path> roots = new ArrayList<>();
        roots.add(tmpDir.resolve("src").toAbsolutePath());
        roots.add(stdlibDir.toAbsolutePath());

        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, true, null, roots, stdlibDir.toAbsolutePath());

        boolean success = orchestrator.compile();
        List<CompilerDiagnostic> diags = orchestrator.diagnostics();

        // Core assertion: import resolution of a stdlib module must succeed
        // (no E2003 "module not found" errors)
        boolean hasModuleNotFound = diags.stream()
            .anyMatch(d -> "E2003".equals(d.code()));
        check(!hasModuleNotFound, "E2E stdlib: no E2003 module-not-found error");

        // If compilation succeeded, verify the output structure
        if (success) {
            check(Files.exists(outputDir.resolve("e2e_std.lua")),
                "E2E stdlib: output file exists after successful compile");

            // Verify the generated code contains require for std.string
            String genCode = Files.readString(outputDir.resolve("e2e_std.lua"));
            check(genCode.contains("require(\"std.string\")"),
                "E2E stdlib: generated code requires std.string");
            check(genCode.contains("strings.length"),
                "E2E stdlib: generated code references strings.length");

            // Verify that the orchestrator copied the stdlib .lua to output
            Path stdDest = outputDir.resolve("std/string.lua");
            check(Files.exists(stdDest),
                "E2E stdlib: std/string.lua copied to output");

            // Runtime verification: execute the compiled module with LuaJIT
            // to verify that the wrapped stdlib function works correctly at runtime.
            // Note: Use a single -e argument because LuaJIT treats each -e as a
            // separate chunk with its own local scope.
            try {
                String luaCode = "package.path = '" + outputDir.toRealPath()
                    + "/?.lua;" + outputDir.toRealPath() + "/?/init.lua;"
                    + stdlibDir.toRealPath() + "/?.lua;' "
                    + "local m = require('e2e_std') "
                    + "local result = m.test_len.f() "
                    + "assert(result == 5, 'expected 5, got ' .. tostring(result)) "
                    + "print('OK: e2e stdlib runtime')";
                ProcessBuilder pb = new ProcessBuilder("luajit", "-e", luaCode);
                pb.redirectErrorStream(true);
                Process proc = pb.start();
                String output = new String(proc.getInputStream().readAllBytes());
                int exitCode = proc.waitFor();
                check(exitCode == 0,
                    "E2E stdlib: runtime verification failed (exit " + exitCode
                    + "): " + output.trim());
            } catch (Exception e) {
                check(false, "E2E stdlib: runtime verification failed: " + e.getMessage());
            }
        } else {
            // Compilation failed for non-E2003 reasons
            System.out.println("  Note: stdlib compilation had errors: "
                + diags.stream().filter(d -> "error".equals(d.severity()))
                    .map(d -> d.code() + ": " + d.message()).toList());
        }
    }

    private static void testEndToEndWithError() throws Exception {
        System.out.println("-- E2E: Error Output --");

        writeFile("src/e2e_err.deal", """
            export function bad(): int { return "wrong"; }
            """);

        Path entryFile = tmpDir.resolve("src/e2e_err.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e2e_err");

        List<Path> roots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, roots, null);

        boolean success = orchestrator.compile();
        check(!success, "E2E error: compilation should fail");

        List<CompilerDiagnostic> diags = orchestrator.diagnostics();
        boolean hasProperDiag = false;
        for (CompilerDiagnostic d : diags) {
            if ("error".equals(d.severity())) {
                check(d.code() != null && !d.code().isEmpty(),
                    "Diagnostic has code: " + d.code());
                check(d.file() != null && !d.file().isEmpty(),
                    "Diagnostic has file");
                check(d.line() > 0, "Diagnostic has line > 0");
                check(d.column() > 0, "Diagnostic has column > 0");
                check(d.message() != null && !d.message().isEmpty(),
                    "Diagnostic has message");
                hasProperDiag = true;
            }
        }
        check(hasProperDiag, "Has at least one properly formatted diagnostic");
    }

    // =========================================================================
    // E2E: Complete Pipeline via CLI
    // =========================================================================

    private static void testEndToEndCliPipeline() throws Exception {
        System.out.println("-- E2E: CLI Pipeline --");
        if (!luajitAvailable()) {
            System.out.println("  SKIP: LuaJIT not available");
            return;
        }

        writeFile("src/e2e_cli.deal", """
            export function main(): null { return null; }
            export function add(a: int, b: int): int { return a + b; }
            """);

        Path entryFile = tmpDir.resolve("src/e2e_cli.deal").toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/e2e_cli");

        int exitCode = Main.run(new String[]{"compile",
            entryFile.toString(), "--output", outputDir.toString(), "--verbose"});
        check(exitCode == 0, "E2E CLI: exit 0");

        check(Files.exists(outputDir.resolve("e2e_cli.lua")),
            "E2E CLI: output file exists");

        Path runtimeDest = outputDir.resolve("deal/runtime.lua");
        Files.createDirectories(runtimeDest.getParent());
        if (!Files.exists(runtimeDest)) {
            Files.copy(Path.of("deal/runtime.lua"), runtimeDest);
        }

        Path testFile = outputDir.resolve("__test.lua");
        Files.writeString(testFile, """
            local m = require("e2e_cli")
            local result = m.add.f(5, 7)
            assert(result == 12, "Expected 12, got " .. tostring(result))
            print("OK: " .. result)
            """);

        ProcessBuilder pb = new ProcessBuilder("luajit", testFile.toString());
        pb.directory(outputDir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes());
        int exit = p.waitFor();

        check(exit == 0, "E2E CLI: LuaJIT exit 0, output: " + output.trim());
        check(output.contains("OK: 12"), "E2E CLI: correct result");
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    private static boolean luajitAvailable() {
        try {
            new ProcessBuilder("luajit", "-v").start().waitFor();
            return true;
        } catch (Exception e) {
            return false;
        }
    }


    // =========================================================================
    // DEAL v1.2 module shape validation and selected-entry main() rules
    // (ISSUE-0104)
    // =========================================================================

    /** Parses a source and runs the post-parse ModuleShapeValidator. */
    private static List<CompilerDiagnostic> shapeDiags(String source, boolean isDeclFile) {
        LexResult lex = new Lexer(source, isDeclFile ? "t.d.deal" : "t.deal")
            .tokenize();
        ParseResult parse = new Parser(lex.tokens(),
            isDeclFile ? "t.d.deal" : "t.deal").parse();
        return ModuleShapeValidator.validate(parse.program(),
            isDeclFile ? "t.d.deal" : "t.deal", isDeclFile);
    }

    private static void testModuleShapeValidV12() {
        System.out.println("-- v1.2 module shape: imports first + main() compiles --");
        List<CompilerDiagnostic> diags = shapeDiags("""
            import * as lib from "./lib"
            export function main(): null { return null; }
            export class Point { x: number = 0.0; }
            function helper(): int { return 1; }
            """, false);
        check(diags.isEmpty(), "v1.2-conformant module has no shape diagnostics");
    }

    private static void testModuleShapeImportAfterDeclaration() {
        System.out.println("-- v1.2 module shape: import after declaration (E1048) --");
        List<CompilerDiagnostic> diags = shapeDiags("""
            export function main(): null { return null; }
            import * as lib from "./lib"
            """, false);
        check(diags.stream().anyMatch(d -> "E1048".equals(d.code())
                && "error".equals(d.severity())),
            "import after declaration produces E1048");
    }

    private static void testModuleShapeTopLevelStatement() {
        System.out.println("-- v1.2 module shape: top-level statement (E1049) --");
        List<CompilerDiagnostic> diags = shapeDiags("""
            let x: int = 1;
            export function main(): null { return null; }
            """, false);
        check(diags.stream().anyMatch(d -> "E1049".equals(d.code())
                && "error".equals(d.severity())),
            "top-level let produces E1049");
    }

    private static void testModuleShapeNestedExportAndImport() {
        System.out.println("-- v1.2 module shape: nested import/export (E1050) --");
        List<CompilerDiagnostic> diags = shapeDiags("""
            export function main(): null {
              export function inner(): null { return null; }
              return null;
            }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested export produces E1050");

        diags = shapeDiags("""
            export function main(): null {
              import * as lib from "./lib"
              return null;
            }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested import produces E1050");
    }

    private static void testModuleShapeNestedInFunctionExpressions()
            throws Exception {
        System.out.println(
            "-- v1.2 module shape: import/export inside function expressions (E1050) --");

        // Function expression in statement position (variable initializer).
        List<CompilerDiagnostic> diags = shapeDiags("""
            export function main(): null {
              let f = function(): null { import * as x from "./x"; return null; };
              return null;
            }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested import in function expression (statement position) produces E1050");

        diags = shapeDiags("""
            export function main(): null {
              let f = function(): null { export function inner(): null { return null; } return null; };
              return null;
            }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested export in function expression (statement position) produces E1050");

        // Function expression in a class-field default.
        diags = shapeDiags("""
            class C { f: (() => null) = function(): null { import * as x from "./x"; return null; }; }
            export function main(): null { return null; }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested import in class-field default function expression produces E1050");

        diags = shapeDiags("""
            class C { f: (() => null) = function(): null { export function inner(): null { return null; } return null; }; }
            export function main(): null { return null; }
            """, false);
        check(diags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "nested export in class-field default function expression produces E1050");

        // Deeply nested clean function expressions stay valid (no false
        // positives from descending through expressions).
        diags = shapeDiags("""
            import * as lib from "./lib"
            export function main(): null {
              let f = function(): null { let g = function(): int { return 1; }; return null; };
              let a = [1, function(): int { return 2; }];
              return null;
            }
            """, false);
        check(diags.isEmpty(),
            "clean nested function expressions produce no shape diagnostics");

        // End to end: the orchestrator must reject the module instead of
        // silently miscompiling when a function-expression body carries a
        // nested export.
        List<CompilerDiagnostic> orchestratorDiags = compileEntry(
            "nested_fn_expr_export", """
            export function main(): null {
              let f = function(): null { export function inner(): null { return null; } return null; };
              return null;
            }
            """);
        check(orchestratorDiags.stream().anyMatch(d -> "E1050".equals(d.code())
                && "error".equals(d.severity())),
            "orchestrator rejects nested export in function expression with E1050");
    }

    private static void testModuleShapeBodylessInImplementation()
            throws Exception {
        System.out.println("-- v1.2 module shape: bodyless declaration in .deal (E1051) --");
        List<CompilerDiagnostic> diags = shapeDiags(
            "export function main(): null;\n", false);
        check(diags.stream().anyMatch(d -> "E1051".equals(d.code())
                && "error".equals(d.severity())),
            "bodyless function in .deal produces E1051");

        // .d.deal files may declare external functions.
        diags = shapeDiags(
            "export function add(a: int, b: int): int;\n", true);
        check(diags.isEmpty(), ".d.deal external declaration is accepted");

        // A bodyless declaration nested inside a function body is external
        // too: implementation files must reject it with E1051 instead of
        // silently dropping the declared signature.
        diags = shapeDiags("""
            export function main(): null {
              function g(): null;
              let n: null = g();
              return n;
            }
            """, false);
        check(diags.stream().anyMatch(d -> "E1051".equals(d.code())
                && "error".equals(d.severity())),
            "nested bodyless function in a function body produces E1051");

        // A bodyless declaration nested inside a class-field-default
        // function expression is reached through the expression walk.
        diags = shapeDiags("""
            class C { f: (() => null) = function(): null { function g(): null; return null; }; }
            export function main(): null { return null; }
            """, false);
        check(diags.stream().anyMatch(d -> "E1051".equals(d.code())
                && "error".equals(d.severity())),
            "nested bodyless function in a class-field-default function expression produces E1051");

        // Declaration files may nest external declarations; only the
        // implementation-file gate is threaded into the nested walk.
        diags = shapeDiags("""
            export function add(a: int, b: int): int {
              function helper(): int;
              return helper();
            }
            """, true);
        check(diags.isEmpty(),
            "nested bodyless function in .d.deal is accepted");

        // Bodied nested declarations stay valid in implementation files.
        diags = shapeDiags("""
            export function main(): null {
              function g(): null { return null; }
              let f = function(): null { function h(): null { return null; } return null; };
              return null;
            }
            """, false);
        check(diags.isEmpty(),
            "bodied nested declarations produce no shape diagnostics");

        // End to end: the orchestrator must reject the module that
        // previously compiled cleanly with a dropped signature.
        List<CompilerDiagnostic> orchestratorDiags = compileEntry(
            "nested_bodyless", """
            export function main(): null {
              function g(): null;
              let n: null = g();
              return n;
            }
            """);
        check(orchestratorDiags.stream().anyMatch(d -> "E1051".equals(d.code())
                && "error".equals(d.severity())),
            "orchestrator rejects nested bodyless declaration with E1051");
    }

    /** Compiles one entry module and returns orchestrator diagnostics. */
    private static List<CompilerDiagnostic> compileEntry(String name, String source)
            throws Exception {
        writeFile("src/" + name + ".deal", source);
        Path entryFile = tmpDir.resolve("src/" + name + ".deal")
            .toAbsolutePath();
        Path outputDir = tmpDir.resolve("build/" + name);
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, outputDir, false, null, moduleRoots, null);
        orchestrator.compile();
        return orchestrator.diagnostics();
    }

    private static void testEntryMainValidation() throws Exception {
        System.out.println("-- v1.2 selected-entry main() validation --");

        // Missing main → E2012 (ISSUE-0269 re-registration: E2012
        // carries the former E2010 entry-main-missing meaning).
        List<CompilerDiagnostic> diags = compileEntry("em_missing",
            "export function run(): int { return 1; }\n");
        check(diags.stream().anyMatch(d -> "E2012".equals(d.code())
                && "error".equals(d.severity())),
            "entry without main produces E2012");

        // Wrong parameter shape → E2011.
        diags = compileEntry("em_params",
            "export function main(x: int): null { return null; }\n");
        check(diags.stream().anyMatch(d -> "E2011".equals(d.code())
                && "error".equals(d.severity())),
            "main(x: int) produces E2011");

        // Wrong return type → E2011.
        diags = compileEntry("em_return",
            "export function main(): int { return 1; }\n");
        check(diags.stream().anyMatch(d -> "E2011".equals(d.code())
                && "error".equals(d.severity())),
            "main(): int produces E2011");

        // Async main → E2011.
        diags = compileEntry("em_async",
            "export async function main(): null { return null; }\n");
        check(diags.stream().anyMatch(d -> "E2011".equals(d.code())
                && "error".equals(d.severity())),
            "async main produces E2011");

        // Correct shape → no E2012/E2011.
        diags = compileEntry("em_ok",
            "export function main(): null { return null; }\n");
        check(diags.stream().noneMatch(d -> "E2012".equals(d.code())
                || "E2011".equals(d.code())),
            "main(): null produces no entry diagnostics");
    }

    // =========================================================================
    // Diagnostic-range pins (orchestrator anchors)
    // =========================================================================

    /**
     * Verification-2 program-span pins: E2012/E2011 carry SOURCE ranges
     * starting at the program start with the exact non-zero start scalar
     * offset when the first statement does not start at (1,1); an
     * empty/whitespace-only entry file yields
     * {@code (file,1,1,1,1,0,0,0,SOURCE)} — never SYNTHETIC, no anchor
     * note.
     */
    private static void testEntryMainProgramSpanAnchors() throws Exception {
        System.out.println("-- v1.2 entry-main program-span anchors (E2012/E2011) --");

        // A leading comment moves the first statement off (1,1): the
        // program span (and the E2012 anchor) must start at the export
        // with the exact scalar offset of the comment prefix.
        String commented = "// leading comment\n"
            + "export function run(): int { return 1; }\n";
        Path commentedFile = writeFile("src/em_anchor.deal", commented)
            .toAbsolutePath();
        Path commentedOut = tmpDir.resolve("build/em_anchor");
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator commentedOrchestrator = new CompilationOrchestrator(
            commentedFile, commentedOut, false, null, moduleRoots, null);
        check(!commentedOrchestrator.compile(),
            "commented entry without main fails compilation");
        CompilerDiagnostic commentedE2012 = commentedOrchestrator.diagnostics()
            .stream().filter(d -> "E2012".equals(d.code()))
            .findFirst().orElse(null);
        check(commentedE2012 != null, "commented entry produces E2012");
        if (commentedE2012 != null) {
            DiagnosticRange range = commentedE2012.range();
            check(range.origin() == RangeOrigin.SOURCE,
                "E2012 range origin is SOURCE: " + range);
            int expectedOffset = ScalarSourceCursor.scalarCount(
                commented.substring(0, commented.indexOf("export")));
            check(range.startLine() == 2 && range.startColumn() == 1,
                "E2012 starts at the program start 2:1: " + range);
            check(range.startScalarOffset() == expectedOffset,
                "E2012 start scalar offset is exact (" + expectedOffset
                    + "): " + range);
            check(range.endScalarOffset() > range.startScalarOffset(),
                "E2012 spans the program: " + range);
            check(range.scalarLength()
                    == range.endScalarOffset() - range.startScalarOffset(),
                "E2012 scalar length is offset-consistent: " + range);
            check(commentedE2012.notes().isEmpty(),
                "no anchor note on a SOURCE anchor: "
                    + commentedE2012.notes());
        }

        // Empty entry file: the pinned zero-length SOURCE program-span
        // shape, never SYNTHETIC and no anchor note.
        Path emptyFile = writeFile("src/em_empty.deal", "").toAbsolutePath();
        CompilationOrchestrator emptyOrchestrator = new CompilationOrchestrator(
            emptyFile, tmpDir.resolve("build/em_empty"), false, null,
            moduleRoots, null);
        emptyOrchestrator.compile();
        CompilerDiagnostic emptyE2012 = emptyOrchestrator.diagnostics().stream()
            .filter(d -> "E2012".equals(d.code()))
            .findFirst().orElse(null);
        check(emptyE2012 != null, "empty entry produces E2012");
        if (emptyE2012 != null) {
            DiagnosticRange range = emptyE2012.range();
            check(range.origin() == RangeOrigin.SOURCE
                    && range.startLine() == 1 && range.startColumn() == 1
                    && range.endLine() == 1 && range.endColumn() == 1
                    && range.startScalarOffset() == 0
                    && range.endScalarOffset() == 0
                    && range.scalarLength() == 0,
                "empty entry E2012 pins (file,1,1,1,1,0,0,0,SOURCE): "
                    + range);
            check(emptyE2012.notes().isEmpty(),
                "empty entry E2012 carries no anchor note: "
                    + emptyE2012.notes());
        }

        // Whitespace-only entry file: the same pinned document-start
        // shape (zero tokens; the program span is the explicit zero-length
        // SOURCE range at file start).
        Path wsFile = writeFile("src/em_ws.deal", " \t\n").toAbsolutePath();
        CompilationOrchestrator wsOrchestrator = new CompilationOrchestrator(
            wsFile, tmpDir.resolve("build/em_ws"), false, null,
            moduleRoots, null);
        wsOrchestrator.compile();
        CompilerDiagnostic wsE2012 = wsOrchestrator.diagnostics().stream()
            .filter(d -> "E2012".equals(d.code()))
            .findFirst().orElse(null);
        check(wsE2012 != null, "whitespace-only entry produces E2012");
        if (wsE2012 != null) {
            DiagnosticRange range = wsE2012.range();
            check(range.origin() == RangeOrigin.SOURCE
                    && range.startLine() == 1 && range.startColumn() == 1
                    && range.endLine() == 1 && range.endColumn() == 1
                    && range.startScalarOffset() == 0
                    && range.endScalarOffset() == 0
                    && range.scalarLength() == 0,
                "whitespace-only entry E2012 pins (file,1,1,1,1,0,0,0,SOURCE): "
                    + range);
            check(wsE2012.notes().isEmpty(),
                "whitespace-only entry E2012 carries no anchor note: "
                    + wsE2012.notes());
        }
    }

    /**
     * D5 anchor pins: E2003 (discovery) and E2009 anchor at the import
     * declaration span with SOURCE origin and exact scalar offsets.
     */
    private static void testImportSpanAnchorPins() throws Exception {
        System.out.println("-- E2003/E2009 import declaration span anchors --");

        // E2003: an unresolved relative import anchors at the import
        // declaration's full span.
        writeFile("src/importspan_main.deal",
            "import * as X from \"./missing\"\n"
                + "export function main(): null { return null; }\n");
        Path entryFile = tmpDir.resolve("src/importspan_main.deal")
            .toAbsolutePath();
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, tmpDir.resolve("build/importspan"), false, null,
            moduleRoots, null);
        check(!orchestrator.compile(), "unresolved import fails compilation");
        CompilerDiagnostic e2003 = orchestrator.diagnostics().stream()
            .filter(d -> "E2003".equals(d.code()))
            .findFirst().orElse(null);
        check(e2003 != null, "E2003 emitted for the unresolved import");
        if (e2003 != null) {
            DiagnosticRange range = e2003.range();
            // The E2003 range must equal the parser's own import
            // declaration span (SOURCE-exact, same file/positions/offsets).
            String src = "import * as X from \"./missing\"\n"
                + "export function main(): null { return null; }\n";
            ParseResult parsed = new Parser(
                new Lexer(src, entryFile.toString()).tokenize().tokens(),
                entryFile.toString()).parse();
            Span impSpan = parsed.program().statements().stream()
                .filter(st -> st instanceof ImportDeclaration)
                .map(st -> ((ImportDeclaration) st).span())
                .findFirst().orElse(null);
            check(impSpan != null, "fixture parses an import declaration");
            DiagnosticRange expected = impSpan.range();
            check(range.origin() == RangeOrigin.SOURCE,
                "E2003 range origin is SOURCE: " + range);
            check(range.equals(expected),
                "E2003 range equals the import declaration span: " + range
                    + " vs " + expected);
            check(range.file().endsWith("importspan_main.deal"),
                "E2003 names the importing file: " + range.file());
        }

        // E2009: the undeclared host import anchors at the import
        // declaration span (SOURCE-exact).
        writeFile("src/e2009span/hostmod.d.deal",
            "export function ping(): int;\n");
        writeFile("src/e2009span/gate_main.deal",
            "import * as cfg from \"e2009span/hostmod\"\n"
                + "export function main(): null { return null; }\n");
        Path gateEntry = tmpDir.resolve("src/e2009span/gate_main.deal")
            .toAbsolutePath();
        CompilationOrchestrator gateOrchestrator = new CompilationOrchestrator(
            gateEntry, tmpDir.resolve("build/e2009span"), false, null,
            moduleRoots, null);
        check(!gateOrchestrator.compile(),
            "undeclared host import fails compilation");
        CompilerDiagnostic e2009 = gateOrchestrator.diagnostics().stream()
            .filter(d -> "E2009".equals(d.code()))
            .findFirst().orElse(null);
        check(e2009 != null, "E2009 emitted for the undeclared host import");
        if (e2009 != null) {
            DiagnosticRange range = e2009.range();
            String src = "import * as cfg from \"e2009span/hostmod\"\n"
                + "export function main(): null { return null; }\n";
            ParseResult parsed = new Parser(
                new Lexer(src, gateEntry.toString()).tokenize().tokens(),
                gateEntry.toString()).parse();
            Span impSpan = parsed.program().statements().stream()
                .filter(st -> st instanceof ImportDeclaration)
                .map(st -> ((ImportDeclaration) st).span())
                .findFirst().orElse(null);
            check(impSpan != null, "fixture parses an import declaration");
            check(range.origin() == RangeOrigin.SOURCE,
                "E2009 range origin is SOURCE: " + range);
            check(range.equals(impSpan.range()),
                "E2009 range equals the import declaration span: " + range
                    + " vs " + impSpan.range());
        }
    }

    /**
     * D5 anchor pin: E2005 uses the import declaration span of the first
     * cycle module that targets another cycle member (SOURCE-exact).
     */
    private static void testE2005ImportSpanAnchor() throws Exception {
        System.out.println("-- E2005 import declaration span anchor --");

        writeFile("src/cya.deal",
            "import * as B from \"./cyb\"\n"
                + "export function main(): null { return null; }\n"
                + "export class Holder {\n"
                + "  seed: int = B.get(1);\n"
                + "}\n");
        writeFile("src/cyb.deal",
            "import * as A from \"./cya\"\n"
                + "export function get(x: int): int { return x + 1; }\n");
        Path entryFile = tmpDir.resolve("src/cya.deal").toAbsolutePath();
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entryFile, tmpDir.resolve("build/cya"), false, null,
            moduleRoots, null);
        check(!orchestrator.compile(), "runtime cycle fails compilation");
        CompilerDiagnostic e2005 = orchestrator.diagnostics().stream()
            .filter(d -> "E2005".equals(d.code()))
            .findFirst().orElse(null);
        check(e2005 != null, "E2005 emitted for the runtime cycle");
        if (e2005 != null) {
            DiagnosticRange range = e2005.range();
            // The E2005 range must equal the parser's import declaration
            // span of the first cycle module (cya) targeting another
            // cycle member (cyb).
            String src = "import * as B from \"./cyb\"\n"
                + "export function main(): null { return null; }\n"
                + "export class Holder {\n"
                + "  seed: int = B.get(1);\n"
                + "}\n";
            ParseResult parsed = new Parser(
                new Lexer(src, entryFile.toString()).tokenize().tokens(),
                entryFile.toString()).parse();
            Span impSpan = parsed.program().statements().stream()
                .filter(st -> st instanceof ImportDeclaration)
                .map(st -> ((ImportDeclaration) st).span())
                .findFirst().orElse(null);
            check(impSpan != null, "fixture parses an import declaration");
            check(range.origin() == RangeOrigin.SOURCE,
                "E2005 range origin is SOURCE: " + range);
            check(range.equals(impSpan.range()),
                "E2005 range equals the cycle-edge import declaration span: "
                    + range + " vs " + impSpan.range());
            check(range.file().endsWith("cya.deal"),
                "E2005 anchors in the first cycle module: " + range.file());
        }
    }

    /**
     * Verification-6 fixture: the E2005 anchor fallback chain — import
     * declaration span, then the module program span, then the canonical
     * synthetic range plus a cycle-edge-naming note.
     */
    private static void testE2005AnchorFallbackChain() {
        System.out.println("-- E2005 anchor fallback chain (synthetic pin) --");

        List<String> cycle = List.of("a.deal", "b.deal", "a.deal");
        String message = "Circular import with runtime dependency: "
            + "a.deal -> b.deal -> a.deal";

        // No edge spans and no program spans: canonical synthetic plus the
        // cycle-edge-naming note.
        CompilerDiagnostic fallback = CompilationOrchestrator.e2005Diagnostic(
            cycle, Map.of(), Map.of(), message);
        check(fallback.code().equals("E2005")
                && "error".equals(fallback.severity()),
            "E2005 fallback keeps code and severity");
        check(fallback.range().isCanonicalSynthetic()
                && fallback.range().origin() == RangeOrigin.SYNTHETIC,
            "E2005 fallback range is canonical synthetic: "
                + fallback.range());
        check(fallback.notes().stream().anyMatch(n -> n.message().contains(
                "missing anchor: import declaration closing the module "
                    + "cycle a.deal -> b.deal -> a.deal")),
            "E2005 fallback note names the cycle edge: " + fallback.notes());

        // Import declaration span present: SOURCE at that span.
        Span importSpan = new Span("a.deal", 1, 1, 1, 29, 0, 29);
        CompilerDiagnostic anchored = CompilationOrchestrator.e2005Diagnostic(
            cycle, Map.of("a.deal", Map.of("b.deal", importSpan)),
            Map.of(), message);
        check(anchored.range().origin() == RangeOrigin.SOURCE
                && anchored.range().startScalarOffset() == 0
                && anchored.range().scalarLength() == 29,
            "E2005 anchors at the retained import span: "
                + anchored.range());

        // The first cycle module targets a cycle member but the edge span
        // is unknown: the module program span is the fallback.
        Span programSpan = new Span("a.deal", 2, 1, 5, 1, 30, 100);
        Map<String, Span> aEdges = new HashMap<>();
        aEdges.put("b.deal", null);
        CompilerDiagnostic programFallback =
            CompilationOrchestrator.e2005Diagnostic(
                cycle, Map.of("a.deal", aEdges), Map.of("a.deal", programSpan),
                message);
        check(programFallback.range().origin() == RangeOrigin.SOURCE
                && programFallback.range().startLine() == 2
                && programFallback.range().startScalarOffset() == 30,
            "E2005 falls back to the module program span: "
                + programFallback.range());

        // No module targets a cycle member at all: the canonical
        // synthetic fallback regardless of available program spans.
        CompilerDiagnostic noEdgeFallback =
            CompilationOrchestrator.e2005Diagnostic(
                cycle, Map.of("a.deal", Map.of(), "b.deal", Map.of()),
                Map.of("a.deal", programSpan), message);
        check(noEdgeFallback.range().isCanonicalSynthetic()
                && noEdgeFallback.range().origin() == RangeOrigin.SYNTHETIC,
            "E2005 without any cycle-member edge is synthetic: "
                + noEdgeFallback.range());
    }

    /**
     * Verification-6 fixture: an E6001 IR-dump failure carries the
     * canonical synthetic range plus a note naming the failed path.
     */
    private static void testE6001IrDumpFailureSynthetic() {
        System.out.println("-- E6001 IR-dump failure synthetic pin --");

        CompilerDiagnostic e6001 =
            CompilationOrchestrator.e6001IrDumpFailure("/proj/lib.deal", "boom");
        check(e6001.code().equals("E6001")
                && "error".equals(e6001.severity()),
            "E6001 keeps code and severity");
        check(e6001.range().isCanonicalSynthetic()
                && e6001.range().origin() == RangeOrigin.SYNTHETIC
                && e6001.range().file().equals("/proj/lib.deal"),
            "E6001 range is the canonical synthetic shape: " + e6001.range());
        check(e6001.notes().stream().anyMatch(n -> n.message().equals(
                "missing anchor: IR dump path for module '/proj/lib.deal'")),
            "E6001 note names the failed path: " + e6001.notes());
        check(e6001.message().equals("IR dump failed for /proj/lib.deal: boom"),
            "E6001 message unchanged: " + e6001.message());
    }

    /**
     * Verification-6 fixtures: a nonexistent queue file and an unreadable
     * module file yield canonical synthetic ranges plus notes naming the
     * unresolved path (D5/D6).
     */
    private static void testMissingModuleSyntheticNotes() throws Exception {
        System.out.println("-- Missing/unreadable module file synthetic anchors --");

        // A nonexistent entry file: the discovery queue holds no import
        // declaration, so "Module not found" is synthetic + note naming
        // the unresolved path.
        Path missingEntry = tmpDir.resolve("src/no_such.deal")
            .toAbsolutePath();
        List<Path> moduleRoots = List.of(tmpDir.resolve("src").toAbsolutePath());
        CompilationOrchestrator missingOrchestrator = new CompilationOrchestrator(
            missingEntry, tmpDir.resolve("build/no_such"), false, null,
            moduleRoots, null);
        check(!missingOrchestrator.compile(), "nonexistent entry fails");
        CompilerDiagnostic missing = missingOrchestrator.diagnostics().stream()
            .filter(d -> "E2003".equals(d.code()))
            .findFirst().orElse(null);
        check(missing != null, "E2003 emitted for the nonexistent entry");
        if (missing != null) {
            check(missing.range().isCanonicalSynthetic()
                    && missing.range().origin() == RangeOrigin.SYNTHETIC,
                "nonexistent entry E2003 range is canonical synthetic: "
                    + missing.range());
            check(missing.range().file().equals(missingEntry.toString()),
                "synthetic range carries the unresolved path: "
                    + missing.range().file());
            // ISSUE-0269: the entry-file seam carries the carrier's
            // canonical synthetic anchor note (naming the entry path),
            // not the retired custom note text.
            check(missing.notes().stream().anyMatch(n -> n.message().equals(
                    "missing anchor: " + missingEntry.toString() + ":1:1")),
                "note names the unresolved path: " + missing.notes());
        }

        // An unreadable module file (a directory answering to the
        // .deal candidate): "Cannot read module" is synthetic + note
        // naming the unreadable path.
        Files.createDirectories(tmpDir.resolve("src/unreadable.deal"));
        writeFile("src/um_main.deal",
            "import * as U from \"./unreadable\"\n"
                + "export function main(): null { return null; }\n");
        Path umEntry = tmpDir.resolve("src/um_main.deal").toAbsolutePath();
        CompilationOrchestrator unreadableOrchestrator =
            new CompilationOrchestrator(
                umEntry, tmpDir.resolve("build/um"), false, null,
                moduleRoots, null);
        check(!unreadableOrchestrator.compile(), "unreadable module fails");
        // ISSUE-0269: an unreadable candidate (a directory answering
        // to the .deal candidate) is E2003 at the import span from the
        // T6 resolver — a SOURCE anchor at the import declaration,
        // naming the unreadable candidate (the retired queue-file
        // synthetic shape is superseded).
        CompilerDiagnostic unreadable = unreadableOrchestrator.diagnostics()
            .stream().filter(d -> "E2003".equals(d.code())
                    && d.message().contains("not a readable module"))
            .findFirst().orElse(null);
        check(unreadable != null, "E2003 emitted for the unreadable module");
        if (unreadable != null) {
            check(unreadable.range().origin() == RangeOrigin.SOURCE
                    && unreadable.range().file().endsWith("um_main.deal"),
                "unreadable module E2003 anchors at the import span: "
                    + unreadable.range());
            check(unreadable.message().contains("./unreadable")
                    && unreadable.message().contains("src/unreadable.deal"),
                "message names the import and the unreadable candidate: "
                    + unreadable.message());
        }
    }

    /**
     * End-to-end --diagnostics-json compilation path (D8): a failing
     * compilation prints through the canonical formatter and writes a
     * field-exact document with exit 1; a successful compilation writes
     * the empty document with exit 0; an unwritable path produces the
     * deterministic I/O diagnostic with exit 1 and no stack trace.
     */
    private static void testCliDiagnosticsJsonCompilationPath()
            throws Exception {
        System.out.println("-- CLI: --diagnostics-json compilation path --");

        // ISSUE-0269: the CLI locates exactly one ancestor manifest, so
        // the diagnostics-json fixtures carry their own exact-v1.2
        // project (moduleRoots src).
        writeFile("dj_proj/deal.json",
            "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"]}\n");
        Path entry = writeFile("dj_proj/src/dj_fail.deal",
            "export function bad(): int { return \"wrong\"; }\n")
            .toAbsolutePath();
        Path outJson = tmpDir.resolve("dj_fail.json");

        String[] captured = runCliCapturingErr(new String[] {
            "compile", entry.toString(),
            "--output", tmpDir.resolve("build/dj_fail").toString(),
            "--diagnostics-json", outJson.toString()});
        check("1".equals(captured[0]),
            "failing compilation with --diagnostics-json exits 1");
        check(captured[1].contains("[span "),
            "human diagnostics print through the canonical formatter: "
                + captured[1]);
        check(captured[1].contains("error(s)"),
            "summary counts print: " + captured[1]);

        // Field-exact against the in-process carrier on the same fixture.
        ByteArrayOutputStream noise = new ByteArrayOutputStream();
        PrintStream originalErr = System.err;
        CompilationOrchestrator orchestrator;
        try {
            System.setErr(new PrintStream(noise, true, StandardCharsets.UTF_8));
            orchestrator = new CompilationOrchestrator(
                entry, tmpDir.resolve("build/dj_fail_direct"), false,
                (Map<String, String>) null,
                List.of(tmpDir.resolve("dj_proj/src").toAbsolutePath()), null);
            orchestrator.compile();
        } finally {
            System.err.flush();
            System.setErr(originalErr);
        }
        String expectedJson =
            DiagnosticStructuredOutput.toJson(orchestrator.diagnostics());
        String written = Files.readString(outJson);
        check(written.equals(expectedJson),
            "failing-compilation document is field-exact:\n" + written);

        // Successful compilation: the document with empty diagnostics,
        // exit 0 (the write does not change the exit code).
        Path okEntry = writeFile("dj_proj/src/dj_ok.deal",
            "export function main(): null { return null; }\n")
            .toAbsolutePath();
        Path okJson = tmpDir.resolve("dj_ok.json");
        String[] okCaptured = runCliCapturingErr(new String[] {
            "compile", okEntry.toString(),
            "--output", tmpDir.resolve("build/dj_ok").toString(),
            "--diagnostics-json", okJson.toString()});
        check("0".equals(okCaptured[0]),
            "successful compilation with --diagnostics-json exits 0: "
                + okCaptured[1]);
        check(Files.readString(okJson).equals(
                DiagnosticStructuredOutput.toJson(List.of())),
            "successful compilation writes the empty document: "
                + Files.readString(okJson));

        // Unwritable path on a failing compilation: deterministic stderr
        // I/O diagnostic, exit 1, no stack trace, no raw path exception.
        Path badPath = Path.of("/nonexistent-parent-dir-0413/dj.json");
        String[] badCaptured = runCliCapturingErr(new String[] {
            "compile", entry.toString(),
            "--output", tmpDir.resolve("build/dj_fail_bad").toString(),
            "--diagnostics-json", badPath.toString()});
        check("1".equals(badCaptured[0]),
            "unwritable --diagnostics-json on a failing compilation exits 1");
        check(badCaptured[1].contains("deal: cannot write diagnostics JSON"),
            "deterministic I/O diagnostic: " + badCaptured[1]);
        check(!badCaptured[1].contains("Exception")
                && !badCaptured[1].contains("\tat "),
            "no raw exception or stack trace escapes: " + badCaptured[1]);
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Running Module System Tests ===\n");

        tmpDir = Files.createTempDirectory("deal_module_test_");

        try {
            testStrictProjectConfiguration();
            testExportExtractor();
            testExportExtractorAsyncFunc();
            testExportExtractorAsyncFuncTypeAnnotation();
            testDeclarationFileBodyValidation();
            testDeclarationFileLetStmt();
            testModuleResolution();
            testModuleShapeValidV12();
            testModuleShapeImportAfterDeclaration();
            testModuleShapeTopLevelStatement();
            testModuleShapeNestedExportAndImport();
            testModuleShapeNestedInFunctionExpressions();
            testModuleShapeBodylessInImplementation();
            testEntryMainValidation();
            testEntryMainProgramSpanAnchors();
            testImportSpanAnchorPins();
            testE2005ImportSpanAnchor();
            testE2005AnchorFallbackChain();
            testE6001IrDumpFailureSynthetic();
            testMissingModuleSyntheticNotes();
            testCliDiagnosticsJsonCompilationPath();
            testTopologicalSortDiamond();
            testModuleOutsideCycle();
            testSingleModuleCompilation();
            testMultiModuleCompilation();
            testCompilationWithError();
            testCompilationOrchestratorAwaitImportRetention();
            testCrossModuleAsyncCallWithoutAwait_E3014();
            testCircularImportRuntime();
            testCircularImportDeclarationOnly();
            testCircularImportClassFieldDefault();
            testTwoDisconnectedCyclesOneRuntime();
            testTwoDisconnectedCyclesBothDecl();
            testStdlibFallbackAfterDdeal();
            testCrossModuleClassFieldAccess();
            testCrossModuleClassConstruction();
            testCrossModuleClassHas();
            testQualifiedTypeAnnotation();
            testCrossModuleClassE2E();
            testDeclarationFile();
            testExternalsHostModuleCompiles();
            testExternalsGatingE2009();
            testExternalsMissingDeclarationE2010();
            testHostModuleEndToEnd();
            testHostModuleBackslashExternalsKeyE2E();
            testHostModuleBackslashExternalsKeyJsonableE2E();
            testCli();
            testCliDiagnosticsJson();
            testEndToEndSingleModule();
            testEndToEndMultiModule();
            testEndToEndStdlib();
            testEndToEndWithError();
            testEndToEndCliPipeline();
            // Stdlib compiler integration tests (ISSUE-0009)
            testStdlibConsoleCompilerIntegration();
            testStdlibTableCompilerIntegration();
            testStdlibJsonCompilerIntegration();
            testStdlibMathCompilerIntegration();
            testStdlibTimeCompilerIntegration();
            testStdlibCrossModuleUsage();
            testStdlibJsonRoundTrip();
        } finally {
            try {
                Files.walk(tmpDir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(f -> {
                        try { Files.deleteIfExists(f); } catch (IOException ignored) {}
                    });
            } catch (IOException ignored) {}
        }

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
