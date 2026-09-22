package deal.test;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.BreakStatement;
import deal.ast.CallExpr;
import deal.ast.ClassDeclaration;
import deal.ast.ClassField;
import deal.ast.ContinueStatement;
import deal.ast.DeleteStatement;
import deal.ast.Either;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.ForInit;
import deal.ast.ForOfStatement;
import deal.ast.ForStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.HasExpr;
import deal.ast.IdentifierExpr;
import deal.ast.IfStatement;
import deal.ast.ImportDeclaration;
import deal.ast.IndexExpr;
import deal.ast.LiteralExpr;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.ThrowStatement;
import deal.ast.TryStatement;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.ast.WhileStatement;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.codegen.Backend;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.DescriptorService;
import deal.semantic.StdlibCallRecognition;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StdlibFunctionId;
import deal.types.Type;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

/**
 * Verifies the ISSUE-0493 closed stdlib surface: the single closed
 * {@link StdlibFunctionCatalog} — the declared exports of
 * {@code std/console}, {@code std/string}, {@code std/table},
 * {@code std/json}, {@code std/math}, and (since K7) {@code std/time}
 * with their declared parameter
 * and return descriptors in the {@link DescriptorService} domain — and
 * the closed checked-fact recognition predicate
 * {@link StdlibCallRecognition}, which classifies a call callee as a
 * stdlib call only from checker facts ({@code Symbol.ModuleSymbol} on an
 * import whose resolved module is classified
 * {@code ExternalModuleKind.STDLIB}, plus a catalog key). No consumer may
 * interpret a module/name pair as a stdlib algorithm outside the catalog
 * and the predicate.
 *
 * <p>Tests:
 * <ol>
 *   <li>Enumeration battery: the catalog's key set equals exactly the
 *       closed 21-id {@link StdlibFunctionId} set with the K7
 *       {@code std.time}/{@code nowMillis} row last; per entry, the exact
 *       id, module path, export name, and declared parameter/return
 *       descriptors — an added, removed, or renamed entry fails.</li>
 *   <li>Negative lookups: unknown members of known stdlib modules, other
 *       {@code std.time} members, a user module, a host module,
 *       and absent inputs all return "not a stdlib call" — never an
 *       error; the table is immutable and pure.</li>
 *   <li>Recognition over real checked projects: one {@code .deal} module
 *       importing all six cataloged stdlib modules through namespace
 *       imports, resolved through {@code TypeChecker}'s
 *       {@code ModuleSymbol} export resolution — positive per id for all
 *       21 call sites plus a value-position export read.</li>
 *   <li>Recognition negatives over real checked projects: member access
 *       on a shadowing local variable, on a user-module alias, on a
 *       host-module alias, on a non-{@code IdentifierExpr} object, and a
 *       non-member callee — none recognized.</li>
 *   <li>Anti-hollow control: an identifier whose spelling equals a
 *       stdlib alias but whose checked resolution is a non-STDLIB module
 *       is never recognized — spelling-based matching is rejected and
 *       the checked-scope resolution path is forced; the same is pinned
 *       synthetically over hand-built checker facts (kind, alias join,
 *       scope shadowing, non-catalog members).</li>
 *   <li>The K7 time row: {@code time.nowMillis} is recognized through the
 *       closed {@code std.time}/{@code nowMillis} catalog row with its
 *       declared {@code ()->int} descriptors (the superseded D8
 *       reservation is retired, the catalog row is the closed authority).</li>
 * </ol>
 */
public class StdlibFunctionCatalogTest {

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
    // Shared checked-fact fixtures
    // =========================================================================

    private static Span span() {
        return new Span("test.deal", 1, 1, 1, 1);
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

    /**
     * Compiles the fixture sources under one temp source directory
     * through the full orchestrator pipeline (phase 3 + the checked
     * project builder) and returns the checked project input; null when
     * the compile or the checked project failed.
     */
    private static CheckedProjectInput compileProject(Path tmp, Map<String, String> sources,
                                                      String entryName) throws Exception {
        Path src = tmp.resolve("src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Files.writeString(src.resolve(source.getKey()), source.getValue());
        }
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(entryName).toAbsolutePath(), tmp.resolve("build"), false, false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
        boolean ok = orchestrator.compile();
        check(ok, entryName + " compiles through phase 3 + builder: "
            + orchestrator.diagnostics());
        if (!ok) {
            return null;
        }
        CheckedProjectBuildResult checked = orchestrator.checkedProject();
        check(checked != null && !checked.hasErrors(),
            "the orchestrator built exactly one checked project: "
                + (checked == null ? "null" : checked.diagnostics()));
        if (checked == null || checked.hasErrors()) {
            return null;
        }
        return checked.input();
    }

    private static CheckedModuleInput moduleOf(CheckedProjectInput input,
                                               String modulePath) {
        if (input == null) {
            return null;
        }
        for (CheckedModuleInput module : input.modules()) {
            if (module.moduleId().path().equals(modulePath)) {
                return module;
            }
        }
        return null;
    }

    // =========================================================================
    // Scoped AST walk: member accesses paired with their checker scope
    // =========================================================================

    @FunctionalInterface
    private interface MemberAccessSink {
        void accept(MemberAccessExpr access, SymbolTable scope);
    }

    /**
     * Walks statements with the checker's per-scoped-statement symbol
     * table (the {@code CheckResult.scopeMap} entries keyed by node
     * identity, exactly like the checker resolved names), reporting every
     * member access together with the innermost enclosing scope.
     */
    private static void walkStatements(List<StatementNode> statements, SymbolTable scope,
                                       Map<StatementNode, SymbolTable> scopeMap,
                                       MemberAccessSink sink) {
        for (StatementNode stmt : statements) {
            SymbolTable stmtScope = scopeMap.getOrDefault(stmt, scope);
            switch (stmt) {
                case Block block ->
                    walkStatements(block.statements(), stmtScope, scopeMap, sink);
                case ImportDeclaration ignored -> { }
                case ExportDeclaration exportDeclaration ->
                    walkStatements(List.of(exportDeclaration.declaration()), stmtScope,
                        scopeMap, sink);
                case ClassDeclaration classDeclaration -> {
                    for (ClassField field : classDeclaration.fields()) {
                        field.defaultExpr().ifPresent(
                            expr -> walkExpression(expr, stmtScope, scopeMap, sink));
                    }
                }
                case FunctionDeclaration function ->
                    walkStatements(List.of(function.body()), stmtScope, scopeMap, sink);
                case VariableDeclaration variable ->
                    walkExpression(variable.initializer(), stmtScope, scopeMap, sink);
                case ReturnStatement returnStatement ->
                    returnStatement.expr().ifPresent(
                        expr -> walkExpression(expr, stmtScope, scopeMap, sink));
                case IfStatement ifStatement -> {
                    walkExpression(ifStatement.condition(), stmtScope, scopeMap, sink);
                    walkStatements(List.of(ifStatement.thenBlock()), stmtScope, scopeMap,
                        sink);
                    ifStatement.elseBranch().ifPresent(branch -> {
                        switch (branch) {
                            case Either.Left<IfStatement, Block> left ->
                                walkStatements(List.of(left.value()), stmtScope, scopeMap,
                                    sink);
                            case Either.Right<IfStatement, Block> right ->
                                walkStatements(List.of(right.value()), stmtScope, scopeMap,
                                    sink);
                        }
                    });
                }
                case WhileStatement whileStatement -> {
                    walkExpression(whileStatement.condition(), stmtScope, scopeMap, sink);
                    walkStatements(List.of(whileStatement.body()), stmtScope, scopeMap,
                        sink);
                }
                case ForStatement forStatement -> {
                    forStatement.init().ifPresent(init -> {
                        switch (init) {
                            case ForInit.VarDecl varDecl ->
                                walkExpression(varDecl.decl().initializer(), stmtScope,
                                    scopeMap, sink);
                            case ForInit.AssignExpr assignExpr ->
                                walkExpression(assignExpr.expr(), stmtScope, scopeMap,
                                    sink);
                        }
                    });
                    forStatement.condition().ifPresent(
                        expr -> walkExpression(expr, stmtScope, scopeMap, sink));
                    forStatement.update().ifPresent(
                        expr -> walkExpression(expr, stmtScope, scopeMap, sink));
                    walkStatements(List.of(forStatement.body()), stmtScope, scopeMap, sink);
                }
                case ForOfStatement forOf -> {
                    walkExpression(forOf.iterable(), stmtScope, scopeMap, sink);
                    walkStatements(List.of(forOf.body()), stmtScope, scopeMap, sink);
                }
                case ExpressionStatement expressionStatement ->
                    walkExpression(expressionStatement.expr(), stmtScope, scopeMap, sink);
                case DeleteStatement deleteStatement ->
                    walkExpression(deleteStatement.target(), stmtScope, scopeMap, sink);
                case TryStatement tryStatement -> {
                    walkStatements(List.of(tryStatement.tryBlock()), stmtScope, scopeMap,
                        sink);
                    walkStatements(List.of(tryStatement.catchBlock()), stmtScope, scopeMap,
                        sink);
                }
                case ThrowStatement throwStatement ->
                    walkExpression(throwStatement.expr(), stmtScope, scopeMap, sink);
                case BreakStatement ignored -> { }
                case ContinueStatement ignored -> { }
            }
        }
    }

    private static void walkExpression(ExpressionNode expr, SymbolTable scope,
                                       Map<StatementNode, SymbolTable> scopeMap,
                                       MemberAccessSink sink) {
        switch (expr) {
            case LiteralExpr ignored -> { }
            case IdentifierExpr ignored -> { }
            case MemberAccessExpr access -> {
                sink.accept(access, scope);
                walkExpression(access.object(), scope, scopeMap, sink);
            }
            case BinaryExpr binary -> {
                walkExpression(binary.left(), scope, scopeMap, sink);
                walkExpression(binary.right(), scope, scopeMap, sink);
            }
            case UnaryExpr unary -> walkExpression(unary.expr(), scope, scopeMap, sink);
            case CallExpr call -> {
                walkExpression(call.callee(), scope, scopeMap, sink);
                for (ExpressionNode arg : call.args()) {
                    walkExpression(arg, scope, scopeMap, sink);
                }
            }
            case IndexExpr index -> {
                walkExpression(index.array(), scope, scopeMap, sink);
                walkExpression(index.index(), scope, scopeMap, sink);
            }
            case ArrayLiteralExpr array -> {
                for (ExpressionNode element : array.elements()) {
                    walkExpression(element, scope, scopeMap, sink);
                }
            }
            case ObjectLiteralExpr object -> {
                for (Property property : object.properties()) {
                    walkExpression(property.value(), scope, scopeMap, sink);
                }
            }
            case FunctionExpr function ->
                walkStatements(List.of(function.body()), scope, scopeMap, sink);
            case HasExpr has -> walkExpression(has.object(), scope, scopeMap, sink);
            case AssignmentExpr assignment -> {
                walkExpression(assignment.target(), scope, scopeMap, sink);
                walkExpression(assignment.value(), scope, scopeMap, sink);
            }
            case TemplateLiteralExpr template -> {
                for (ExpressionNode part : template.parts()) {
                    walkExpression(part, scope, scopeMap, sink);
                }
            }
            case AwaitExpression await ->
                walkExpression(await.callee(), scope, scopeMap, sink);
        }
    }

    /** Every member access of the checked module, paired with its checker scope. */
    private static List<Map.Entry<MemberAccessExpr, SymbolTable>> memberAccessesOf(
            CheckedModuleInput module) {
        List<Map.Entry<MemberAccessExpr, SymbolTable>> accesses = new ArrayList<>();
        walkStatements(module.ast().statements(), module.checks().symbolTable(),
            module.checks().scopeMap(),
            (access, scope) -> accesses.add(Map.entry(access, scope)));
        return accesses;
    }

    // =========================================================================
    // 1. Enumeration battery
    // =========================================================================

    static void testCatalogEnumerationBattery() {
        System.out.println("-- Enumeration battery: closed 21-row table, exact descriptors --");

        RuntimeDescriptor string = DescriptorService.describe(Type.String.INSTANCE);
        RuntimeDescriptor intD = DescriptorService.describe(Type.Int.INSTANCE);
        RuntimeDescriptor number = DescriptorService.describe(Type.Number.INSTANCE);
        RuntimeDescriptor bool = DescriptorService.describe(Type.Boolean.INSTANCE);
        RuntimeDescriptor table = DescriptorService.describe(Type.Table.INSTANCE);
        RuntimeDescriptor nullD = DescriptorService.describe(Type.Null.INSTANCE);
        RuntimeDescriptor stringArray =
            DescriptorService.describe(new Type.Array(Type.String.INSTANCE));

        List<StdlibFunctionCatalog.Entry> expected = List.of(
            entry(StdlibFunctionId.CONSOLE_LOG, "std.console", "log",
                List.of(string), nullD),
            entry(StdlibFunctionId.CONSOLE_ERROR, "std.console", "error",
                List.of(string), nullD),
            entry(StdlibFunctionId.STRING_LENGTH, "std.string", "length",
                List.of(string), intD),
            entry(StdlibFunctionId.STRING_SUBSTRING, "std.string", "substring",
                List.of(string, intD, intD), string),
            entry(StdlibFunctionId.STRING_CONTAINS, "std.string", "contains",
                List.of(string, string), bool),
            entry(StdlibFunctionId.STRING_STARTS_WITH, "std.string", "startsWith",
                List.of(string, string), bool),
            entry(StdlibFunctionId.STRING_ENDS_WITH, "std.string", "endsWith",
                List.of(string, string), bool),
            entry(StdlibFunctionId.STRING_REPLACE, "std.string", "replace",
                List.of(string, string, string), string),
            entry(StdlibFunctionId.STRING_SPLIT, "std.string", "split",
                List.of(string, string), stringArray),
            entry(StdlibFunctionId.STRING_TRIM, "std.string", "trim",
                List.of(string), string),
            entry(StdlibFunctionId.TABLE_KEYS, "std.table", "keys",
                List.of(table), stringArray),
            entry(StdlibFunctionId.JSON_PARSE, "std.json", "parse",
                List.of(string), table),
            entry(StdlibFunctionId.JSON_STRINGIFY, "std.json", "stringify",
                List.of(table), string),
            entry(StdlibFunctionId.MATH_FLOOR, "std.math", "floor",
                List.of(number), number),
            entry(StdlibFunctionId.MATH_CEIL, "std.math", "ceil",
                List.of(number), number),
            entry(StdlibFunctionId.MATH_SQRT, "std.math", "sqrt",
                List.of(number), number),
            entry(StdlibFunctionId.MATH_ABS_INT, "std.math", "absInt",
                List.of(intD), intD),
            entry(StdlibFunctionId.MATH_ABS_NUMBER, "std.math", "absNumber",
                List.of(number), number),
            entry(StdlibFunctionId.MATH_MIN_INT, "std.math", "minInt",
                List.of(intD, intD), intD),
            entry(StdlibFunctionId.MATH_MAX_INT, "std.math", "maxInt",
                List.of(intD, intD), intD),
            entry(StdlibFunctionId.TIME_NOW_MILLIS, "std.time", "nowMillis",
                List.of(), intD));

        check(StdlibFunctionCatalog.entries().size() == 21,
            "the catalog has exactly 21 entries; got " + StdlibFunctionCatalog.entries().size());
        check(StdlibFunctionCatalog.entries().equals(expected),
            "the catalog rows equal the closed D1 table plus the K7 std.time row in pinned "
                + "order (an added, "
                + "removed, or renamed entry fails): " + StdlibFunctionCatalog.entries());

        EnumSet<StdlibFunctionId> ids = EnumSet.noneOf(StdlibFunctionId.class);
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            ids.add(entry.function());
        }
        check(ids.equals(EnumSet.allOf(StdlibFunctionId.class)),
            "the catalog's key set equals exactly the closed 21-id StdlibFunctionId set; got "
                + ids);
        check(ids.size() == 21 && StdlibFunctionId.values().length == 21,
            "the closed StdlibFunctionId enum is exactly 21 values (TIME_NOW_MILLIS is the "
                + "21st member; the D8 reservation is retired)");
        check(StdlibFunctionId.values()[20] == StdlibFunctionId.TIME_NOW_MILLIS
                && StdlibFunctionId.RESERVED_NAMES.isEmpty(),
            "TIME_NOW_MILLIS is the 21st member in the pinned order and RESERVED_NAMES is "
                + "empty while the reserved-name guard stays");
        check(StdlibFunctionCatalog.entries().get(20).modulePath().equals("std.time"),
            "the std.time group is the single last row — no existing row moved");

        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            Optional<StdlibFunctionCatalog.Entry> lookedUp =
                StdlibFunctionCatalog.lookup(entry.modulePath(), entry.exportName());
            check(lookedUp.isPresent() && lookedUp.get().equals(entry),
                "lookup(" + entry.modulePath() + ", " + entry.exportName() + ") returns the "
                    + "exact catalog row");
            check(!StdlibFunctionId.isReservedName(entry.function().name()),
                "catalog id " + entry.function() + " is not a reserved selector name");
        }
        check(StdlibFunctionCatalog.lookup("std.time", "nowMillis")
                .map(StdlibFunctionCatalog.Entry::function)
                .orElse(null) == StdlibFunctionId.TIME_NOW_MILLIS,
            "std.time.nowMillis resolves to TIME_NOW_MILLIS through the closed catalog");
        check(StdlibFunctionCatalog.lookup("std.time", "nowMillis")
                .map(entry -> entry.parameterDescriptors().isEmpty()
                    && entry.returnDescriptor().equals(intD))
                .orElse(false),
            "the std.time.nowMillis row carries the declared ()->int descriptors");

        // Immutability and purity of the static surface.
        try {
            StdlibFunctionCatalog.entries().add(expected.get(0));
            fail("entries() is mutable (a catalog row could be appended at runtime)");
        } catch (UnsupportedOperationException expectedUnsupported) {
            check(true, "entries() is immutable");
        }
        check(StdlibFunctionCatalog.entries().equals(
                StdlibFunctionCatalog.entries()),
            "entries() is stable across calls (pure, no state)");
        check(StdlibFunctionCatalog.lookup("std.string", "length").equals(
                StdlibFunctionCatalog.lookup("std.string", "length")),
            "lookup is pure and deterministic");
    }

    private static StdlibFunctionCatalog.Entry entry(StdlibFunctionId id, String module,
                                                     String exportName,
                                                     List<RuntimeDescriptor> params,
                                                     RuntimeDescriptor result) {
        return new StdlibFunctionCatalog.Entry(id, module, exportName, params, result);
    }

    // =========================================================================
    // 2. Negative lookups
    // =========================================================================

    static void testNegativeLookups() {
        System.out.println("-- Negative lookups: absent modules/members are never errors --");

        // std/time: exactly the single nowMillis row; every other member is
        // not a stdlib call.
        for (String member : List.of("length", "log", "keys", "time")) {
            check(StdlibFunctionCatalog.lookup("std.time", member).isEmpty(),
                "std.time." + member + " is not a stdlib call (no catalog entry)");
        }
        check(StdlibFunctionCatalog.lookup("std.time", "nowMillis").isPresent(),
            "std.time.nowMillis is the K7 catalog row");
        // Unknown members of known stdlib modules.
        check(StdlibFunctionCatalog.lookup("std.string", "nope").isEmpty(),
            "std.string.nope is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("std.console", "logx").isEmpty(),
            "std.console.logx is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("std.math", "keys").isEmpty(),
            "std.math.keys is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("std.json", "log").isEmpty(),
            "std.json.log is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("std.table", "length").isEmpty(),
            "std.table.length is not a stdlib call");
        // The slash form is the raw import specifier, never the resolved
        // module path the catalog keys on (resolved module ids are dotted).
        check(StdlibFunctionCatalog.lookup("std/console", "log").isEmpty()
                && StdlibFunctionCatalog.lookup("std/string", "length").isEmpty()
                && StdlibFunctionCatalog.lookup("std/time", "nowMillis").isEmpty(),
            "raw import specifiers (slash form) are not resolved module paths — "
                + "never catalog keys");
        // User and host modules: never catalog keys.
        check(StdlibFunctionCatalog.lookup("app/user", "length").isEmpty(),
            "user module app/user.length is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("util", "length").isEmpty(),
            "user module util.length is not a stdlib call");
        check(StdlibFunctionCatalog.lookup("host/lib", "log").isEmpty(),
            "host module host/lib.log is not a stdlib call");
        // Absent module and null inputs: absent, never an error.
        check(StdlibFunctionCatalog.lookup("std/other", "length").isEmpty(),
            "absent module std/other is not a stdlib call");
        check(StdlibFunctionCatalog.lookup(null, "length").isEmpty(),
            "a null module path is an absent module (never an error)");
        check(StdlibFunctionCatalog.lookup("std.string", null).isEmpty(),
            "a null export name is an absent member (never an error)");
        check(StdlibFunctionCatalog.lookup(null, null).isEmpty(),
            "null/null is an absent lookup (never an error)");
    }

    // =========================================================================
    // 3. Recognition positives over a real checked project (all 21 ids)
    // =========================================================================

    static void testRecognitionPositiveBattery() throws Exception {
        System.out.println("-- Recognition positives: one checked project, every cataloged id --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-positive");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as console from "std/console"
                    import * as str from "std/string"
                    import * as tbl from "std/table"
                    import * as json from "std/json"
                    import * as math from "std/math"
                    import * as time from "std/time"

                    export function main(): null {
                      console.log("log")
                      console.error("error")
                      let n1: int = str.length("abc")
                      let s2: string = str.substring("abc", 1, 2)
                      let b3: boolean = str.contains("abc", "b")
                      let b4: boolean = str.startsWith("abc", "a")
                      let b5: boolean = str.endsWith("abc", "c")
                      let s6: string = str.replace("aba", "a", "z")
                      let xs7: string[] = str.split("a,b", ",")
                      let s8: string = str.trim(" x ")
                      let t: table = {k: 1}
                      let ks9: string[] = tbl.keys(t)
                      let jt10: table = json.parse("{\\"a\\": 1}")
                      let js11: string = json.stringify(t)
                      let f12: number = math.floor(1.5)
                      let f13: number = math.ceil(1.5)
                      let f14: number = math.sqrt(4.0)
                      let i15: int = math.absInt(-3)
                      let f16: number = math.absNumber(-1.5)
                      let i17: int = math.minInt(2, 3)
                      let i18: int = math.maxInt(2, 3)
                      let now: int = time.nowMillis()
                      let g: (x: string) => null = console.log
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            Map<String, StdlibFunctionId> expectedByField = new LinkedHashMap<>();
            expectedByField.put("log", StdlibFunctionId.CONSOLE_LOG);
            expectedByField.put("error", StdlibFunctionId.CONSOLE_ERROR);
            expectedByField.put("length", StdlibFunctionId.STRING_LENGTH);
            expectedByField.put("substring", StdlibFunctionId.STRING_SUBSTRING);
            expectedByField.put("contains", StdlibFunctionId.STRING_CONTAINS);
            expectedByField.put("startsWith", StdlibFunctionId.STRING_STARTS_WITH);
            expectedByField.put("endsWith", StdlibFunctionId.STRING_ENDS_WITH);
            expectedByField.put("replace", StdlibFunctionId.STRING_REPLACE);
            expectedByField.put("split", StdlibFunctionId.STRING_SPLIT);
            expectedByField.put("trim", StdlibFunctionId.STRING_TRIM);
            expectedByField.put("keys", StdlibFunctionId.TABLE_KEYS);
            expectedByField.put("parse", StdlibFunctionId.JSON_PARSE);
            expectedByField.put("stringify", StdlibFunctionId.JSON_STRINGIFY);
            expectedByField.put("floor", StdlibFunctionId.MATH_FLOOR);
            expectedByField.put("ceil", StdlibFunctionId.MATH_CEIL);
            expectedByField.put("sqrt", StdlibFunctionId.MATH_SQRT);
            expectedByField.put("absInt", StdlibFunctionId.MATH_ABS_INT);
            expectedByField.put("absNumber", StdlibFunctionId.MATH_ABS_NUMBER);
            expectedByField.put("minInt", StdlibFunctionId.MATH_MIN_INT);
            expectedByField.put("maxInt", StdlibFunctionId.MATH_MAX_INT);
            expectedByField.put("nowMillis", StdlibFunctionId.TIME_NOW_MILLIS);

            Map<StdlibFunctionId, Integer> seen = new HashMap<>();
            int total = 0;
            for (Map.Entry<MemberAccessExpr, SymbolTable> site : memberAccessesOf(module)) {
                String field = site.getKey().field();
                StdlibFunctionId expectedId = expectedByField.get(field);
                if (expectedId == null) {
                    continue;
                }
                total++;
                Optional<StdlibFunctionCatalog.Entry> recognized =
                    StdlibCallRecognition.recognize(site.getKey(), site.getValue(),
                        module.imports());
                check(recognized.isPresent(), "the checked member access ." + field
                    + " is recognized as a stdlib call (checked ModuleSymbol + STDLIB "
                    + "import + catalog key)");
                if (recognized.isEmpty()) {
                    continue;
                }
                StdlibFunctionCatalog.Entry entry = recognized.get();
                check(entry.function() == expectedId,
                    "." + field + " recognizes " + expectedId + "; got " + entry.function());
                check(entry.equals(StdlibFunctionCatalog.lookup(entry.modulePath(),
                        entry.exportName()).orElse(null)),
                    "the recognized ." + field + " row equals the closed catalog row "
                        + "(declared descriptors included)");
                seen.merge(expectedId, 1, Integer::sum);
            }
            check(total == 22,
                "the positive fixture exposes 22 catalog-member accesses (21 call "
                    + "callees + one value-position export read); got " + total);
            check(seen.get(StdlibFunctionId.CONSOLE_LOG) != null
                    && seen.get(StdlibFunctionId.CONSOLE_LOG) == 2,
                "console.log appears once as a call callee and once as a value-position "
                    + "read; got " + seen.get(StdlibFunctionId.CONSOLE_LOG));
            check(seen.size() == 21
                    && seen.keySet().equals(EnumSet.allOf(StdlibFunctionId.class)),
                "every one of the 21 closed ids is recognized exactly through its cataloged "
                    + "member; got " + seen.keySet());
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 4. Recognition negatives over real checked projects
    // =========================================================================

    static void testRecognitionNegativeUserModuleAlias() throws Exception {
        System.out.println("-- Negative: user-module alias is never a stdlib call --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-user");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "util.deal", """
                    export function length(s: string): int {
                      return 0
                    }
                    """,
                "main.deal", """
                    import * as s from "./util"

                    export function main(): null {
                      s.length("x")
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            List<Map.Entry<MemberAccessExpr, SymbolTable>> sites = memberAccessesOf(module);
            check(sites.size() == 1 && sites.get(0).getKey().field().equals("length"),
                "exactly one member access (s.length) exists; got " + sites.size());
            check(StdlibCallRecognition.recognize(sites.get(0).getKey(),
                    sites.get(0).getValue(), module.imports()).isEmpty(),
                "s.length on a user-module import is not a stdlib call (the import's "
                    + "resolved module is IMPLEMENTATION, not STDLIB)");
            ResolvedImport utilImport = module.imports().get(0);
            check(utilImport.kind() == ExternalModuleKind.IMPLEMENTATION,
                "the user-module import fact is classified IMPLEMENTATION by the checked "
                    + "project builder");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRecognitionNegativeHostModuleAlias() throws Exception {
        System.out.println("-- Negative: host-module alias is never a stdlib call --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-host");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "hostlog.d.deal", """
                    export function log(s: string): null;
                    """,
                "main.deal", """
                    import * as h from "./hostlog"

                    export function main(): null {
                      h.log("x")
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            List<Map.Entry<MemberAccessExpr, SymbolTable>> sites = memberAccessesOf(module);
            check(sites.size() == 1 && sites.get(0).getKey().field().equals("log"),
                "exactly one member access (h.log) exists; got " + sites.size());
            check(StdlibCallRecognition.recognize(sites.get(0).getKey(),
                    sites.get(0).getValue(), module.imports()).isEmpty(),
                "h.log on a host-module import is not a stdlib call (the import's "
                    + "resolved module is HOST, not STDLIB)");
            ResolvedImport hostImport = module.imports().get(0);
            check(hostImport.kind() == ExternalModuleKind.HOST,
                "the host-module import fact is classified HOST by the checked project "
                    + "builder");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRecognitionNegativeSpellingAntiHollow() throws Exception {
        System.out.println("-- Anti-hollow: stdlib-alias spelling on a non-STDLIB module --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-hollow");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "fakeconsole.deal", """
                    export function log(s: string): null {
                      return null
                    }
                    """,
                "main.deal", """
                    import * as console from "./fakeconsole"

                    export function main(): null {
                      console.log("x")
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            List<Map.Entry<MemberAccessExpr, SymbolTable>> sites = memberAccessesOf(module);
            check(sites.size() == 1 && sites.get(0).getKey().field().equals("log"),
                "exactly one member access (console.log) exists; got " + sites.size());
            check(sites.get(0).getKey().object() instanceof IdentifierExpr identifier
                    && identifier.name().equals("console"),
                "the object of console.log is the identifier 'console' (the stdlib alias "
                    + "spelling)");
            check(StdlibCallRecognition.recognize(sites.get(0).getKey(),
                    sites.get(0).getValue(), module.imports()).isEmpty(),
                "an alias spelled 'console' resolving to a non-STDLIB module is never "
                    + "recognized — the checked-scope resolution path rejects "
                    + "spelling-based matching (anti-hollow)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRecognitionNegativeLocalShadowing() throws Exception {
        System.out.println("-- Negative: shadowing local variable is never a stdlib call --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-shadow");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as s from "std/string"

                    export function main(): null {
                      let s: table = { length: "shadowed" }
                      let v: string = s.length
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            List<Map.Entry<MemberAccessExpr, SymbolTable>> sites = memberAccessesOf(module);
            check(sites.size() == 1 && sites.get(0).getKey().field().equals("length"),
                "exactly one member access (s.length) exists; got " + sites.size());
            check(sites.get(0).getValue().resolve("s") instanceof Symbol.VariableSymbol,
                "the checker's scope resolves 's' to the shadowing local VariableSymbol, "
                    + "not the std/string ModuleSymbol");
            check(StdlibCallRecognition.recognize(sites.get(0).getKey(),
                    sites.get(0).getValue(), module.imports()).isEmpty(),
                "s.length on a local table binding is not a stdlib call (local/shadowed "
                    + "bindings are never module symbols)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRecognitionNegativeNonIdentifierObject() throws Exception {
        System.out.println("-- Negative: non-IdentifierExpr object and non-member callee --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-object");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as s from "std/string"

                    function tableOf(): table {
                      let t: table = { length: "x" }
                      return t
                    }

                    export function main(): null {
                      let t = s
                      let f: (text: string) => int = t.length
                      let g: (text: string) => int = tableOf().length
                      f("x")
                      g("x")
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            int lengthSites = 0;
            int callResultObjects = 0;
            int nonMemberCalleges = 0;
            for (Map.Entry<MemberAccessExpr, SymbolTable> site : memberAccessesOf(module)) {
                if (site.getKey().field().equals("length")) {
                    lengthSites++;
                    check(StdlibCallRecognition.recognize(site.getKey(), site.getValue(),
                            module.imports()).isEmpty(),
                        "the .length site on a non-module-symbol object is not a stdlib "
                            + "call");
                    if (!(site.getKey().object() instanceof IdentifierExpr)) {
                        callResultObjects++;
                    }
                }
            }
            check(lengthSites == 2,
                "two .length sites exist (t.length and tableOf().length); got "
                    + lengthSites);
            check(callResultObjects == 1,
                "exactly one .length site has a non-IdentifierExpr object "
                    + "(tableOf().length); got " + callResultObjects);
            // The non-member callee: f("x")/g("x") callees are identifiers.
            for (StatementNode stmt : module.ast().statements()) {
                StatementNode declared = stmt instanceof ExportDeclaration export
                    ? export.declaration() : stmt;
                if (declared instanceof FunctionDeclaration function
                        && function.name().equals("main")) {
                    for (StatementNode bodyStmt : function.body().statements()) {
                        if (bodyStmt instanceof ExpressionStatement expressionStatement
                                && expressionStatement.expr() instanceof CallExpr call
                                && call.callee() instanceof IdentifierExpr) {
                            nonMemberCalleges++;
                            check(StdlibCallRecognition.recognize(call.callee(),
                                    module.checks().symbolTable(), module.imports())
                                .isEmpty(),
                                "a non-member callee (" + call.callee()
                                    + ") is never a stdlib call");
                        }
                    }
                }
            }
            check(nonMemberCalleges == 2,
                "two non-member callees exist (f and g); got " + nonMemberCalleges);
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRecognitionPositiveTimeRow() throws Exception {
        System.out.println("-- Time row: std/time.nowMillis is a recognized stdlib call (K7) --");

        Path tmp = Files.createTempDirectory("deal-stdlib-catalog-time");
        try {
            CheckedProjectInput input = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      time.nowMillis()
                      return null
                    }
                    """), "main.deal");
            if (input == null) {
                return;
            }
            CheckedModuleInput module = moduleOf(input, "main");
            check(module != null, "the checked project contains module main");
            if (module == null) {
                return;
            }
            List<Map.Entry<MemberAccessExpr, SymbolTable>> sites = memberAccessesOf(module);
            check(sites.size() == 1 && sites.get(0).getKey().field().equals("nowMillis"),
                "exactly one member access (time.nowMillis) exists; got " + sites.size());
            Optional<StdlibFunctionCatalog.Entry> recognized =
                StdlibCallRecognition.recognize(sites.get(0).getKey(),
                    sites.get(0).getValue(), module.imports());
            check(recognized.isPresent()
                    && recognized.get().function() == StdlibFunctionId.TIME_NOW_MILLIS,
                "time.nowMillis is recognized through the closed std.time/nowMillis "
                    + "catalog row (K7); got "
                    + (recognized.isEmpty() ? "empty"
                        : recognized.get().function().name()));
            check(recognized.isPresent()
                    && recognized.get().parameterDescriptors().isEmpty()
                    && recognized.get().returnDescriptor()
                        .equals(DescriptorService.describe(Type.Int.INSTANCE)),
                "the recognized row carries the declared ()->int descriptors");
            check(module.imports().get(0).kind() == ExternalModuleKind.STDLIB,
                "std/time is STDLIB-classified by the index — the recognition runs the "
                    + "checked-fact predicate over the closed catalog row");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 5. Synthetic checked-fact battery (predicate conditions one by one)
    // =========================================================================

    static void testRecognitionSyntheticFactBattery() {
        System.out.println("-- Synthetic facts: the predicate's six conditions, one by one --");

        Span span = span();
        MemberAccessExpr access =
            new MemberAccessExpr(span, new IdentifierExpr(span, "s"), "length");
        MemberAccessExpr unknownMember =
            new MemberAccessExpr(span, new IdentifierExpr(span, "s"), "nope");
        MemberAccessExpr nestedObject = new MemberAccessExpr(span,
            new MemberAccessExpr(span, new IdentifierExpr(span, "s"), "nested"), "length");
        MemberAccessExpr callObject = new MemberAccessExpr(span,
            new CallExpr(span, new IdentifierExpr(span, "f"), List.of()), "length");
        IdentifierExpr identifierCallee = new IdentifierExpr(span, "length");

        SymbolTable root = new SymbolTable();
        Type.Func lengthType = new Type.Func(List.of(Type.String.INSTANCE), Type.Int.INSTANCE);
        root.define("s", new Symbol.ModuleSymbol("s", Map.of("length", lengthType), span));

        ResolvedImport stdlibImport = new ResolvedImport("s", "std/string",
            new ModuleId("std.string"), ExternalModuleKind.STDLIB);
        ResolvedImport hostKindImport = new ResolvedImport("s", "std/string",
            new ModuleId("std.string"), ExternalModuleKind.HOST);
        ResolvedImport nonSpecStdlibImport = new ResolvedImport("s", "./other",
            new ModuleId("other/impl"), ExternalModuleKind.STDLIB);
        ResolvedImport wrongAliasImport = new ResolvedImport("x", "std/string",
            new ModuleId("std.string"), ExternalModuleKind.STDLIB);

        // Condition (1)-(2) + (3)-(6): the full positive.
        Optional<StdlibFunctionCatalog.Entry> positive = StdlibCallRecognition.recognize(
            access, root, List.of(stdlibImport));
        check(positive.isPresent()
                && positive.get().function() == StdlibFunctionId.STRING_LENGTH,
            "ModuleSymbol on a STDLIB import with a catalog key recognizes STRING_LENGTH");

        // Non-member callee.
        check(StdlibCallRecognition.recognize(identifierCallee, root, List.of(stdlibImport))
                .isEmpty(), "a non-member callee is never recognized");
        // Member chain whose object is not an IdentifierExpr.
        check(StdlibCallRecognition.recognize(nestedObject, root, List.of(stdlibImport))
                .isEmpty(), "a member chain object (a.b.length) is never recognized");
        check(StdlibCallRecognition.recognize(callObject, root, List.of(stdlibImport))
                .isEmpty(), "a call-result object (f().length) is never recognized");
        // Member name is not a catalog key.
        check(StdlibCallRecognition.recognize(unknownMember, root, List.of(stdlibImport))
                .isEmpty(), "an unknown member of a STDLIB module is never recognized");
        // Classification: HOST kind wins over a catalog-path spelling.
        check(StdlibCallRecognition.recognize(access, root, List.of(hostKindImport))
                .isEmpty(), "a HOST-classified import is never recognized even when its "
                    + "resolved path spells a stdlib module");
        // Classification: STDLIB kind with a non-spec resolved path is absent.
        check(StdlibCallRecognition.recognize(access, root, List.of(nonSpecStdlibImport))
                .isEmpty(), "a STDLIB-classified import resolving outside the catalog "
                    + "module paths is never recognized");
        // Alias join: the import fact must carry the module symbol's alias.
        check(StdlibCallRecognition.recognize(access, root, List.of(wrongAliasImport))
                .isEmpty(), "an import fact under another alias never matches the module "
                    + "symbol's alias (the join is exact)");
        check(StdlibCallRecognition.recognize(access, root, List.of()).isEmpty(),
            "no import fact means no resolved module — never recognized");
        // Null scope resolves nothing.
        check(StdlibCallRecognition.recognize(access, null, List.of(stdlibImport)).isEmpty(),
            "a null checker scope resolves no ModuleSymbol — never recognized");

        // Scope shadowing: the inner scope's VariableSymbol wins over the root
        // ModuleSymbol (the checked-scope resolution path, anti-hollow).
        SymbolTable inner = root.enterScope();
        inner.define("s", new Symbol.VariableSymbol("s", Type.Table.INSTANCE, false));
        check(StdlibCallRecognition.recognize(access, inner, List.of(stdlibImport)).isEmpty(),
            "a shadowing VariableSymbol in the checker scope is never recognized (the "
                + "scope-resolution path is forced)");
        check(StdlibCallRecognition.recognize(access, root, List.of(stdlibImport)).isPresent(),
            "the same site resolves through the root scope to the ModuleSymbol and is "
                + "recognized (scope selection is a checked fact)");

        // The lookup is the only module/name interpretation: the same name pair
        // with no checker facts is absent from the catalog alone.
        check(StdlibFunctionCatalog.lookup("std.string", "length").isPresent(),
            "the catalog row exists for std.string.length");
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Stdlib Function Catalog / Checked-Fact Recognition Test "
            + "(ISSUE-0493) ===\n");

        testCatalogEnumerationBattery();
        testNegativeLookups();
        testRecognitionPositiveBattery();
        testRecognitionNegativeUserModuleAlias();
        testRecognitionNegativeHostModuleAlias();
        testRecognitionNegativeSpellingAntiHollow();
        testRecognitionNegativeLocalShadowing();
        testRecognitionNegativeNonIdentifierObject();
        testRecognitionPositiveTimeRow();
        testRecognitionSyntheticFactBattery();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
