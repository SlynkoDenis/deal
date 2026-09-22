package deal.test;

import deal.ast.*;
import deal.checker.*;
import deal.diagnostics.CompilerDiagnostic;
import deal.codegen.lua.LuaBackend;
import deal.lexer.*;
import deal.module.CompilationOrchestrator;
import deal.parser.*;
import deal.types.Type;

import java.io.*;
import java.nio.file.*;
import java.util.*;

/**
 * Runtime source-location tests.
 *
 * <p>Verifies that runtime errors (array OOB, type mismatch, division by zero,
 * throw) report the correct DEAL source file, line, and column.
 *
 * <p>Requires LuaJIT to be available.
 */
public class RuntimeSourceLocationTest {

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

    // =========================================================================
    // Helpers
    // =========================================================================

    /**
     * Compile DEAL source, generate Lua, run with LuaJIT, and capture the
     * error output (both stdout and stderr). Returns the combined output.
     * Returns null if LuaJIT is not available.
     */
    private static String compileAndRunExpectError(String dealSource,
                                                    String filename)
                                                    throws Exception {
        try {
            new ProcessBuilder("luajit", "-v").start().waitFor();
        } catch (IOException e) {
            return null;
        }

        LexResult lex = new Lexer(dealSource, filename).tokenize();
        ParseResult parse = new Parser(lex.tokens(), filename, lex.directiveEvents()).parse();

        StubModuleResolver resolver = new StubModuleResolver();
        NameResolver nr = new NameResolver(filename, resolver);
        SymbolTable symTable = nr.resolve(parse.program());

        List<CompilerDiagnostic> diags = new ArrayList<>(nr.diagnostics());
        if (diags.stream().anyMatch(d -> "error".equals(d.severity()))) {
            fail("Compilation error: " + diags);
            return null;
        }

        CheckResult result = TypeChecker.check(filename, symTable, nr, parse.program());
        diags.addAll(result.diagnostics());
        if (diags.stream().anyMatch(d -> "error".equals(d.severity()))) {
            fail("Type error: " + diags);
            return null;
        }

        String lua = LuaBackend.generate(parse.program(), result, filename);

        Path tmpDir = Files.createTempDirectory("deal_rtloc_");
        Path luaFile = tmpDir.resolve("test_main.lua");
        Files.writeString(luaFile, lua);

        // Copy runtime library
        Path runtimeDir = tmpDir.resolve("deal");
        Files.createDirectories(runtimeDir);
        Files.copy(Path.of("deal/runtime.lua"), runtimeDir.resolve("runtime.lua"));

        // Run with pcall wrapper so we can capture the error
        String wrapper =
            "package.path = './?.lua;' .. package.path\n" +
            "local ok, err = pcall(function()\n" +
            "  local mod = loadfile(\"" +
            luaFile.toString().replace("\\", "/") + "\")()\n" +
            "  if mod.main ~= nil then mod.main.f() end\n" +
            "end)\n" +
            "if not ok then\n" +
            "  if type(err) == 'table' then\n" +
            "    print('FILE:' .. tostring(err.file))\n" +
            "    print('LINE:' .. tostring(err.line))\n" +
            "    print('COLUMN:' .. tostring(err.column))\n" +
            "    print('CODE:' .. tostring(err.code))\n" +
            "    print('MESSAGE:' .. tostring(err.message))\n" +
            "  else\n" +
            "    print('RAW_ERROR:' .. tostring(err))\n" +
            "  end\n" +
            "end\n";

        Path wrapperFile = tmpDir.resolve("wrapper.lua");
        Files.writeString(wrapperFile, wrapper);

        ProcessBuilder pb = new ProcessBuilder("luajit", wrapperFile.toString());
        pb.directory(tmpDir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes()).trim();
        p.waitFor();

        try {
            Files.walk(tmpDir).sorted(Comparator.reverseOrder())
                .forEach(f -> { try { Files.deleteIfExists(f); }
                    catch (IOException ignored) {} });
        } catch (IOException ignored) {}

        return output;
    }

    /** Parse the error output lines into a map. */
    private static Map<String, String> parseErrorOutput(String output) {
        Map<String, String> map = new HashMap<>();
        if (output == null) return map;
        for (String line : output.split("\n")) {
            line = line.trim();
            if (line.startsWith("FILE:")) {
                map.put("file", line.substring(5).trim());
            } else if (line.startsWith("LINE:")) {
                map.put("line", line.substring(5).trim());
            } else if (line.startsWith("COLUMN:")) {
                map.put("column", line.substring(7).trim());
            } else if (line.startsWith("CODE:")) {
                map.put("code", line.substring(5).trim());
            } else if (line.startsWith("MESSAGE:")) {
                map.put("message", line.substring(8).trim());
            } else if (line.startsWith("RAW_ERROR:")) {
                map.put("raw_error", line.substring(10).trim());
            }
        }
        return map;
    }

    /**
     * Compile and run a multi-module project and capture the error output.
     * Uses CompilationOrchestrator to compile two modules, then runs with LuaJIT.
     */
    private static String compileMultiModuleAndRun(
            String mainSource, String mainModuleName,
            String importedSource, String importedModuleName,
            String importedFileName) throws Exception {

        try {
            new ProcessBuilder("luajit", "-v").start().waitFor();
        } catch (IOException e) {
            return null;
        }

        Path tmpDir = Files.createTempDirectory("deal_rtloc_multi_");

        // Create source files
        Path srcDir = tmpDir.resolve("src");
        Files.createDirectories(srcDir);

        Path mainFile = srcDir.resolve(mainModuleName + ".deal");
        Files.writeString(mainFile, mainSource);

        Path importedFile = srcDir.resolve(importedFileName);
        Files.createDirectories(importedFile.getParent());
        Files.writeString(importedFile, importedSource);

        // Also copy runtime.lua to std/ for the orchestrator
        Path stdlibDir = tmpDir;
        // stdlibDir is tmpDir itself
        // runtime.lua is copied by orchestrator

        Path outputDir = tmpDir.resolve("build/lua");
        List<Path> moduleRoots = List.of(srcDir);

        // ISSUE-0643 P10 item 3: the suite's subject — the runtime source
        // location framing over the per-module artifacts — is
        // arm-independent, so the compile resolves the harness invocation
        // and keeps the retained artifact set.
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            mainFile, outputDir, false, false, false, false,
            deal.codegen.Backend.LUAJIT, null, moduleRoots,
            stdlibDir, null, ConformanceHarnessMetadata.invocation(
                deal.semantic.ir.SemanticProfile.DEAL_V1_2_INT32));

        boolean success = orchestrator.compile();
        if (!success) {
            fail("Compilation failed for multi-module test");
            return null;
        }

        // Run with pcall wrapper. The v1.2 backend invokes main() from the
        // entry module at chunk end, so loading the module already runs
        // main(); the wrapper only needs the guarded require.
        String wrapper =
            "package.path = '" + outputDir.toString().replace("\\", "/") + "/?.lua;' .. package.path\n" +
            "local ok, err = pcall(function()\n" +
            "  require(\"" + mainModuleName + "\")\n" +
            "end)\n" +
            "if not ok then\n" +
            "  if type(err) == 'table' then\n" +
            "    print('FILE:' .. tostring(err.file))\n" +
            "    print('LINE:' .. tostring(err.line))\n" +
            "    print('COLUMN:' .. tostring(err.column))\n" +
            "    print('CODE:' .. tostring(err.code))\n" +
            "    print('MESSAGE:' .. tostring(err.message))\n" +
            "  else\n" +
            "    print('RAW_ERROR:' .. tostring(err))\n" +
            "  end\n" +
            "end\n";

        Path wrapperFile = tmpDir.resolve("wrapper.lua");
        Files.writeString(wrapperFile, wrapper);

        ProcessBuilder pb = new ProcessBuilder("luajit", wrapperFile.toString());
        pb.directory(tmpDir.toFile());
        pb.redirectErrorStream(true);
        Process p = pb.start();
        String output = new String(p.getInputStream().readAllBytes()).trim();
        p.waitFor();

        try {
            Files.walk(tmpDir).sorted(Comparator.reverseOrder())
                .forEach(f -> { try { Files.deleteIfExists(f); }
                    catch (IOException ignored) {} });
        } catch (IOException ignored) {}

        return output;
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Running Runtime Source Location Tests ===");

        boolean luajitAvailable;
        try {
            new ProcessBuilder("luajit", "-v").start().waitFor();
            luajitAvailable = true;
        } catch (IOException e) {
            luajitAvailable = false;
        }

        if (!luajitAvailable) {
            System.out.println("SKIP: luajit not available. Runtime tests require LuaJIT.");
            System.out.println("Passed: 0, Failed: 0 (all skipped)");
            return;
        }

        testDivisionByZero();
        testInt32Overflow();
        testThrowStatement();
        testArrayOutOfBounds();
        testTypeMismatch();

        // Critical case: multi-line expression
        testMultiLineExpression();

        // Critical case: nested function calls
        testNestedFunctionCalls();

        // Critical case: module boundary
        testModuleBoundary();

        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }

    // =========================================================================
    // Test: Division by zero reports correct location
    // =========================================================================

    static void testDivisionByZero() throws Exception {
        System.out.println("-- Division By Zero --");

        String source =
            "export function main(): int {\n" +    // line 1
            "  let a: int = 10;\n" +                // line 2
            "  let b: int = 0;\n" +                  // line 3
            "  return a / b;\n" +                     // line 4 (error here)
            "}\n";

        String output = compileAndRunExpectError(source, "test_div0.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("E8005".equals(err.get("code")),
            "division by zero error code is E8005, got: " + err.get("code"));
        check("test_div0.deal".equals(err.get("file")),
            "file is test_div0.deal, got: " + err.get("file"));
        check("4".equals(err.get("line")),
            "line is 4, got: " + err.get("line"));

        if (err.containsKey("column") && !err.get("column").equals("nil")) {
            int col = Integer.parseInt(err.get("column"));
            check(col >= 1, "column >= 1: " + col);
        } else {
            System.out.println("  Note: column is nil (no span for binary op)");
        }
    }

    // =========================================================================
    // Test: Int32 overflow reports correct location
    // =========================================================================

    static void testInt32Overflow() throws Exception {
        System.out.println("-- Int32 Overflow --");

        // The overflowing expression `max + one` is on line 4 and starts
        // at column 18 (the start of the `max` operand); the emitted
        // __rt.int_add carries the binary expression's span. The overflow
        // lives inside main() because the location wrapper only invokes
        // the exported main.
        String source =
            "export function main(): int {\n" +       // line 1
            "  let max: int = 2147483647;\n" +        // line 2
            "  let one: int = 1;\n" +                 // line 3
            "  let sum: int = max + one;\n" +         // line 4 (error here)
            "  return sum;\n" +                       // line 5
            "}\n";

        String output = compileAndRunExpectError(source, "test_overflow.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("E8004".equals(err.get("code")),
            "int32 overflow error code is E8004, got: " + err.get("code"));
        check("test_overflow.deal".equals(err.get("file")),
            "file is test_overflow.deal, got: " + err.get("file"));
        check("4".equals(err.get("line")),
            "int32 overflow line is 4, got: " + err.get("line"));
        check("18".equals(err.get("column")),
            "int32 overflow column is 18 (overflowing expression start), got: "
                + err.get("column"));
    }

    // =========================================================================
    // Test: Throw statement reports correct location
    // =========================================================================

    static void testThrowStatement() throws Exception {
        System.out.println("-- Throw Statement --");

        String source =
            "export function main(): int {\n" +     // line 1
            "  let x: int = 1;\n" +                  // line 2
            "  throw { code: \"E_LIMIT\", message: \"limit\" };\n" +  // line 3
            "  return x;\n" +                         // line 4
            "}\n";

        String output = compileAndRunExpectError(source, "test_throw.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("test_throw.deal".equals(err.get("file")),
            "file is test_throw.deal, got: " + err.get("file"));

        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            check("3".equals(err.get("line")),
                "throw line is 3, got: " + err.get("line"));
        } else {
            System.out.println("  Note: line info not extracted, raw: " + err.get("raw_error"));
        }
    }

    // =========================================================================
    // Test: Array out-of-bounds reports correct location
    // =========================================================================

    static void testArrayOutOfBounds() throws Exception {
        System.out.println("-- Array Out Of Bounds --");

        String source =
            "export function main(): int {\n" +     // line 1
            "  let xs: int[] = [1, 2, 3];\n" +       // line 2
            "  let idx: int = 99;\n" +                // line 3
            "  let val: int = xs[idx];\n" +           // line 4 (error: nil is not int)
            "  return val;\n" +                        // line 5
            "}\n";

        String output = compileAndRunExpectError(source, "test_oob.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("test_oob.deal".equals(err.get("file")),
            "file is test_oob.deal, got: " + err.get("file"));

        // The array index access is on line 4, column 12 (xs[idx])
        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            check("4".equals(err.get("line")),
                "OOB: error line is 4, got: " + err.get("line"));
        }
        if (err.containsKey("column") && !err.get("column").equals("nil")) {
            check("12".equals(err.get("column")),
                "OOB: error column is 12, got: " + err.get("column"));
        }

        if (err.containsKey("code")) {
            System.out.println("  Error code: " + err.get("code"));
            System.out.println("  Message: " + err.get("message"));
        }
    }

    // =========================================================================
    // Test: Type mismatch in table read
    // =========================================================================
    static void testTypeMismatch() throws Exception {
        System.out.println("-- Type Mismatch --");

        String source =
            "export function main(): string {\n" +  // line 1
            "  let t: table = { x: 42 };\n" +        // line 2
            "  let s: string = t.x;\n" +              // line 3 (runtime: number is not string)
            "  return s;\n" +                          // line 4
            "}\n";

        String output = compileAndRunExpectError(source, "test_mismatch.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("test_mismatch.deal".equals(err.get("file")),
            "file is test_mismatch.deal, got: " + err.get("file"));

        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            check("3".equals(err.get("line")),
                "line is 3, got: " + err.get("line"));
        }

        if (err.containsKey("code")) {
            System.out.println("  Error code: " + err.get("code"));
            System.out.println("  Message: " + err.get("message"));
        }
    }

    // =========================================================================
    // Test: Multi-line expression — error reports the inner line
    // =========================================================================

    static void testMultiLineExpression() throws Exception {
        System.out.println("-- Multi-Line Expression --");

        // The division expression spans lines 3-5 (starting at the / operator).
        // The error should report the line where the operator is (line 4), not
        // the line of the enclosing return statement (line 3).
        String source =
            "export function main(): int {\n" +      // line 1
            "  let a: int = 10;\n" +                  // line 2
            "  return a /\n" +                         // line 3 (operator here)
            "    (5 -\n" +                              // line 4
            "     5);\n" +                              // line 5 (b = 0 here)
            "}\n";

        String output = compileAndRunExpectError(source, "test_multiline.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        // The division operator is on line 3, so the error should report
        // line 3 (not line 1 or some other line).
        check("test_multiline.deal".equals(err.get("file")),
            "multi-line: file is test_multiline.deal, got: " + err.get("file"));

        // The division operator is on line 3, so the error must report
        // line 3 exactly — not the first line of the enclosing function (line 1),
        // not an adjacent line.  A range check is too loose; if a regression
        // shifted the line to 4 or 5 the test would still pass spuriously.
        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            check("3".equals(err.get("line")),
                "multi-line: error line is 3 (the division operator), got: " + err.get("line"));
        }

        if (err.containsKey("code")) {
            System.out.println("  Error code: " + err.get("code"));
        }
    }

    // =========================================================================
    // Test: Nested function calls — inner call reports inner line
    // =========================================================================

    static void testNestedFunctionCalls() throws Exception {
        System.out.println("-- Nested Function Calls --");

        // f calls g, g calls h, h divides by zero.
        // The error should report the line inside h (where division happens),
        // not the line in main where f is called.
        String source =
            "function h(a: int, b: int): int {\n" +   // line 1
            "  return a / b;\n" +                        // line 2 (division by zero here)
            "}\n" +
            "function g(x: int, y: int): int {\n" +    // line 4
            "  return h(x, y);\n" +                      // line 5
            "}\n" +
            "function f(p: int, q: int): int {\n" +    // line 7
            "  return g(p, q);\n" +                      // line 8
            "}\n" +
            "export function main(): int {\n" +         // line 10
            "  return f(10, 0);\n" +                     // line 11
            "}\n";

        String output = compileAndRunExpectError(source, "test_nested.deal");
        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        check("test_nested.deal".equals(err.get("file")),
            "nested: file is test_nested.deal, got: " + err.get("file"));

        // The error should be on line 2 (inside h), not line 11 (main call)
        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            int line = Integer.parseInt(err.get("line"));
            check("2".equals(err.get("line")),
                "nested: error line is 2 (inside h), got: " + err.get("line"));
            check(line != 11,
                "nested: error line is not 11 (main call site)");
        }

        if (err.containsKey("code")) {
            check("E8005".equals(err.get("code")),
                "nested: error code is E8005, got: " + err.get("code"));
        }
    }

    // =========================================================================
    // Test: Module boundary — error in imported module reports its file
    // =========================================================================

    static void testModuleBoundary() throws Exception {
        System.out.println("-- Module Boundary --");

        // Imported module (lib.deal) has a function that divides by zero.
        // Main module imports and calls it. Error should report lib.deal's
        // file name, not main.deal's.
        String mainSource =
            "import * as lib from \"./lib\";\n" +      // line 1
            "export function main(): null {\n" +        // line 2 (v1.2 entry signature)
            "  let _: int = lib.div(10, 0);\n" +         // line 3
            "  return null;\n" +                         // line 4
            "}\n";

        String importedSource =
            "export function div(a: int, b: int): int {\n" +  // line 1
            "  return a / b;\n" +                               // line 2 (error here)
            "}\n";

        String output = compileMultiModuleAndRun(
            mainSource, "main",
            importedSource, "lib",
            "lib.deal");

        if (output == null) return;

        Map<String, String> err = parseErrorOutput(output);
        System.out.println("  Error output: " + output);

        // The error file should reference the imported module, not main
        if (err.containsKey("file") && !err.get("file").equals("nil")) {
            // The file should contain "lib" (the imported module's source path)
            String file = err.get("file");
            check(file.contains("lib"),
                "module boundary: error file contains 'lib', got: " + file);
        }

        // The error line should be 2 (inside div function in lib)
        if (err.containsKey("line") && !err.get("line").equals("nil")) {
            check("2".equals(err.get("line")),
                "module boundary: error line is 2 (inside div), got: " + err.get("line"));
        }

        if (err.containsKey("code")) {
            check("E8005".equals(err.get("code")),
                "module boundary: error code is E8005, got: " + err.get("code"));
        }
    }
}
