package deal.test;

import deal.ast.ClassDeclaration;
import deal.ast.LiteralValue;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.NameResolver;
import deal.checker.SymbolTable;
import deal.descriptors.CanonicalRuntimeTypeDescriptor;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticRange;
import deal.diagnostics.RangeOrigin;
import deal.identity.CanonicalClassIdentity;
import deal.identity.CanonicalClassIdentityIndex;
import deal.identity.CanonicalModuleIdentity;
import deal.identity.ProjectModuleIdentity;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.module.CompilationOrchestrator;
import deal.module.CompilerClassDefaultEntry;
import deal.module.CompilerClassDefaultPlan;
import deal.module.DefaultIrNode;
import deal.module.DefaultResourceOccurrence;
import deal.module.DefaultSerializerModuleInput;
import deal.module.DefaultSemanticSerializer;
import deal.module.LexicalDeclarationIdentity;
import deal.module.PlannedDefaultClass;
import deal.module.ResolvedDefaultExpression;
import deal.module.RuntimeResourceReference;
import deal.module.SemanticModuleIdentity;
import deal.module.SemanticResourceIdentity;
import deal.module.SourceModuleLocation;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.project.ProjectDeploymentIdentity;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;
import deal.types.Type;
import deal.types.Types;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The canonical serializer verification battery of ISSUE-0542 (design
 * source {@code provider-versioned-default-plans} Verification 3/4 and
 * the task-pinned acceptance criteria): the versioned canonical
 * expression and statement grammars, the digest derivations, the
 * {@code canonicalPlanContent}/{@code planDigest}/
 * {@code semanticDefaultContents} projections, the provider digests
 * per kind, and the completion of the plan-embedded
 * {@code runtimeResources} — exercised through the real orchestrator
 * path (ProjectLocator &rarr; the production CompilationOrchestrator
 * &rarr; {@code compile()} &rarr; the E2 planner output) over real
 * scratch-project fixtures plus synthetic serializer inputs for the
 * reentrant-demand guard, the broken-occurrence fail-closed paths, and
 * the non-behavior-affecting-range rule.
 *
 * <p>Variant comparisons recompile over the <em>same</em> scratch root
 * (same deployment identity), so an unchanged provider must produce
 * identical content and digests across the variants — the assertions
 * that pin the exact sensitivity boundaries.</p>
 *
 * <p>Covered:</p>
 * <ol>
 *   <li>Epic criterion 5's serializer parts: canonical-content tests
 *       distinguish changes in literals, operators, types, call
 *       targets, semantic module/resource identity, provider digest,
 *       and behavior-affecting ranges; a non-behavior-affecting range
 *       change changes nothing; equality is full-content and digests
 *       are indexes.</li>
 *   <li>Function-provider content distinguishes statement changes,
 *       call-target changes, embedded imported-provider digest
 *       changes, and behavior-affecting reference-range changes; a
 *       same-module callee's body change changes that callee's digest
 *       but not the caller's; nested function/class declarations
 *       inline.</li>
 *   <li>Provider versioning: a provider resolution or implementation
 *       change changes the provider digest and the consumer's
 *       {@code planDigest}; unchanged providers keep stable digests
 *       across runs (acyclic fixtures).</li>
 *   <li>The serializer is total over the fourteen expression kinds
 *       and the closed statement set, with tests covering every
 *       kind.</li>
 *   <li>Resource completion and the cyclic-path contract: complete
 *       digest-bearing {@code runtimeResources} in first-occurrence
 *       order, real provider digests embedded in canonical targets,
 *       no placeholder observable, broken E2 occurrences fail closed,
 *       and reentrant digest demand fails closed deterministically
 *       (never a hang).</li>
 *   <li>Leaf verification: real acyclic fixtures serialized through
 *       the orchestrator's planning phase, including the out-of-root
 *       provider fixture and the host-declared seams.</li>
 * </ol>
 */
public class DefaultSemanticSerializerTest {

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

    private static void write(Path root, String rel, String content)
            throws Exception {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
    }

    private static void deleteRecursively(Path dir) {
        try {
            if (dir == null || !Files.exists(dir)) {
                return;
            }
            Files.walk(dir).sorted(Comparator.reverseOrder())
                .forEach(f -> {
                    try {
                        Files.deleteIfExists(f);
                    } catch (Exception ignored) {
                    }
                });
        } catch (Exception ignored) {
        }
    }

    /**
     * The harness invocation of this suite's compiles (ISSUE-0643 P10
     * item 3): the suite's subject — the default-semantics serialization
     * — is arm-independent, and the fixtures keep the harness arm's
     * retained artifact behavior.
     */
    private static CompilerInvocation invocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
    }

    /** One in-process production compile over a scratch project; a
     * recompile rewrites the same root and runs a fresh compile, so
     * the deployment identity (and therefore every derived identity
     * and digest) stays byte-stable across variants. */
    private static final class Compile {
        final Path root;
        final Path entry;
        final CompilationOrchestrator orchestrator;
        final boolean success;
        final List<CompilerDiagnostic> diagnostics;

        Compile(Map<String, String> files, String entryRel)
                throws Exception {
            root = Files.createTempDirectory("deal_ser_");
            for (Map.Entry<String, String> file : files.entrySet()) {
                write(root, file.getKey(), file.getValue());
            }
            entry = root.resolve(entryRel);
            ProjectLocator.LocateResult located =
                ProjectLocator.locate(entry.toString(), null);
            if (located.context() == null) {
                throw new IllegalStateException(
                    "ProjectLocator failed: " + located.e2010());
            }
            orchestrator = new CompilationOrchestrator(
                located.context(), entry, false, false, false, false,
                null, invocation());
            success = orchestrator.compile();
            diagnostics = orchestrator.diagnostics();
        }

        private Compile(Path root, Path entry) throws Exception {
            this.root = root;
            this.entry = entry;
            ProjectLocator.LocateResult located =
                ProjectLocator.locate(entry.toString(), null);
            if (located.context() == null) {
                throw new IllegalStateException(
                    "ProjectLocator failed: " + located.e2010());
            }
            orchestrator = new CompilationOrchestrator(
                located.context(), entry, false, false, false, false,
                null, invocation());
            success = orchestrator.compile();
            diagnostics = orchestrator.diagnostics();
        }

        /** Rewrites the same scratch root and recompiles in place
         * (same deployment identity). */
        Compile recompile(Map<String, String> files) throws Exception {
            for (Map.Entry<String, String> file : files.entrySet()) {
                write(root, file.getKey(), file.getValue());
            }
            return new Compile(root, entry);
        }

        /** Serializes the compile's plans through the serializer
         * API. */
        DefaultSemanticSerializer.Result serialize() {
            return DefaultSemanticSerializer.serialize(
                orchestrator.defaultSerializerModuleInputs(),
                orchestrator.plannedDefaultClasses());
        }

        /** The serialized class with the given simple name in the
         * given module (path suffix), or null. */
        DefaultSemanticSerializer.SerializedDefaultClass serializedOf(
                String sourceSuffix, String className) {
            DefaultSemanticSerializer.Result result = serialize();
            for (Map.Entry<String, List<DefaultSemanticSerializer
                    .SerializedDefaultClass>> entry
                    : result.serializedClasses().entrySet()) {
                if (entry.getKey().endsWith(sourceSuffix)) {
                    for (DefaultSemanticSerializer.SerializedDefaultClass
                            cls : entry.getValue()) {
                        if (cls.completedPlan().classIdentity()
                                .className().equals(className)) {
                            return cls;
                        }
                    }
                }
            }
            return null;
        }

        /** The provider digest of the given declared name in the
         * module whose path ends with the given suffix, or null. */
        String providerDigestOf(String sourceSuffix, String declaredName) {
            DefaultSemanticSerializer.Result result = serialize();
            for (Map.Entry<SemanticResourceIdentity, String> entry
                    : result.providerDigests().entrySet()) {
                if (entry.getKey().semanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith(sourceSuffix)
                        && entry.getKey().lexicalDeclarationIdentity()
                            .declaredName().equals(declaredName)) {
                    return entry.getValue();
                }
            }
            return null;
        }

        /** The provider canonical content of the given declared name
         * in the module whose path ends with the given suffix, or
         * null. */
        String providerContentOf(String sourceSuffix, String declaredName) {
            DefaultSemanticSerializer.Result result = serialize();
            for (Map.Entry<SemanticResourceIdentity, String> entry
                    : result.providerContents().entrySet()) {
                if (entry.getKey().semanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith(sourceSuffix)
                        && entry.getKey().lexicalDeclarationIdentity()
                            .declaredName().equals(declaredName)) {
                    return entry.getValue();
                }
            }
            return null;
        }
    }

    private static final String MANIFEST = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "backend": "luajit",
          "output": "build"
        }
        """;

    /** The digest of canonical content (the pinned derivation). */
    private static String digestOf(String content) {
        return RuntimeResourceReference.providerContractDigestOf(content);
    }

    /** True iff the given text is a 64-lowercase-hex-char SHA-256. */
    private static boolean isSha256Hex(String text) {
        return text != null && text.matches("[0-9a-f]{64}");
    }

    /** The serialized classes of the module whose path ends with the
     * given suffix, or an empty list. */
    private static List<DefaultSemanticSerializer.SerializedDefaultClass>
            modulePlansOf(DefaultSemanticSerializer.Result result,
                          String sourceSuffix) {
        for (Map.Entry<String, List<DefaultSemanticSerializer
                .SerializedDefaultClass>> entry
                : result.serializedClasses().entrySet()) {
            if (entry.getKey().endsWith(sourceSuffix)) {
                return entry.getValue();
            }
        }
        return List.of();
    }

    private static final List<String> FOURTEEN_KINDS = List.of(
        "ARRAY_LITERAL", "ASSIGNMENT", "AWAIT", "BINARY", "CALL",
        "FUNCTION_EXPRESSION", "HAS", "IDENTIFIER", "INDEX", "LITERAL",
        "MEMBER_ACCESS", "OBJECT_LITERAL", "TEMPLATE_LITERAL", "UNARY");

    private static final List<String> FIFTEEN_STATEMENT_KINDS = List.of(
        "BLOCK", "BREAK", "CLASS_DECLARATION", "CONTINUE", "DELETE",
        "EXPRESSION_STATEMENT", "FOR", "FOR_OF", "FUNCTION_DECLARATION",
        "IF", "RETURN", "THROW", "TRY", "VARIABLE_DECLARATION", "WHILE");

    public static void main(String[] args) throws Exception {
        testFourteenExpressionKinds();
        testStatementGrammarTotality();
        testCanonicalSensitivity();
        testPlanProjectionsAndDigestDerivation();
        testPlanEntryOrderSensitivity();
        testDefaultNestedScopeResolution();
        testSameNamedClassesDistinctScopes();
        testSameNamedNestedAndImportedPlans();
        testProviderVersioningAndStability();
        testResourceCompletion();
        testFunctionProviderContent();
        testDeclaredWrapperAndHostClassSeams();
        testSyntheticJsonableExportProvider();
        testDeclarationModuleCStructPlan();
        testOutOfRootProvider();
        testReentrantGuardFailsClosed();
        testBrokenOccurrenceFailsClosed();
        testNonBehaviorAffectingRangeIgnored();
        testEqualityByFullContent();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.err.println("DefaultSemanticSerializerTest FAILED: "
                + failed + " failure(s)");
            System.exit(1);
        }
    }

    // =========================================================================
    // Totality: the fourteen expression kinds through the real pipeline
    // =========================================================================

    private static void testFourteenExpressionKinds() throws Exception {
        System.out.println("-- Fourteen expression kinds (real"
            + " orchestrator path) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class Kinds {
                  a: int = 1 + 2;
                  b: int = -3;
                  c: int[] = [1, 2];
                  d: table = { k: 5 };
                  e: string = `v=${label()}`;
                  f: int = tableOf().k;
                  g: int = arrayOf()[0];
                  h: boolean = has(box().tag);
                  i: int = helper(2);
                  j: (x: int) => int = function(x: int): int { return x; };
                  l: int = (function(x: int): int { return (x = 2); })(1);
                  m: async () => int = async function(): int { return await source(); };
                }

                class HasBox {
                  tag?: int = 0;
                }

                function helper(v: int): int {
                  return v;
                }

                function label(): string {
                  return "v";
                }

                function tableOf(): table {
                  return { k: 5 };
                }

                function arrayOf(): int[] {
                  return [1, 2];
                }

                function box(): HasBox {
                  return { tag: 1 };
                }

                async function source(): int {
                  return 3;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the fourteen-kind fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors() && result.diagnostics().isEmpty(),
                "the serializer accepts the planner output: "
                    + result.diagnostics());
            DefaultSemanticSerializer.SerializedDefaultClass kinds =
                compile.serializedOf("main.deal", "Kinds");
            check(kinds != null, "Kinds has a serialized plan");
            if (kinds == null) {
                return;
            }
            StringBuilder allContent = new StringBuilder();
            for (CompilerClassDefaultEntry entry
                    : kinds.completedPlan().orderedFields()) {
                check(entry.defaultExpression() != null,
                    "Kinds entries all carry defaults");
                if (entry.defaultExpression() != null) {
                    String content = entry.defaultExpression()
                        .canonicalSemanticContent();
                    allContent.append(content).append(' ');
                    check(content.contains(
                            "\"serializerVersion\":\"1\""),
                        "canonical content carries the serializer"
                            + " version constant '1'");
                    check(isSha256Hex(entry.defaultExpression()
                            .semanticDigest()),
                        "the semantic digest is a 64-hex SHA-256");
                    check(entry.defaultExpression().semanticDigest()
                            .equals(digestOf(content)),
                        "semanticDigest = SHA-256 over the"
                            + " length-prefixed UTF-8 of the content");
                    check(!content.contains(
                            "\"providerContractDigest\":null"),
                        "no placeholder digest is observable");
                    check(!content.contains("file:"),
                        "canonical content never exposes deployment"
                            + " paths");
                }
            }
            for (String kind : FOURTEEN_KINDS) {
                check(allContent.toString().contains(
                        "\"kind\":\"" + kind + "\""),
                    "the canonical content covers expression kind "
                        + kind);
            }
            check(allContent.toString().contains(
                    "\"kind\":\"AWAIT\""),
                "the nested async function-expression body's await"
                    + " serializes through the expression grammar");
            check(allContent.toString().contains(
                    "\"kind\":\"ASSIGNMENT\""),
                "the nested function-expression body's assignment"
                    + " serializes through the expression grammar");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Totality: the fifteen statement kinds through the statement grammar
    // =========================================================================

    private static void testStatementGrammarTotality() throws Exception {
        System.out.println("-- Statement grammar totality and roles"
            + " (real orchestrator path) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"

                class AllStatements {
                  f: int = L.allStatements(1, [2]);
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                export function allStatements(n: int, arr: int[]): int {
                  let total: int = 0;
                  total = total + 1;
                  if (n > 0) {
                    total = total + 1;
                  } else {
                    total = total - 1;
                  }
                  let i = 0;
                  while (i < 2) {
                    i = i + 1;
                    if (i === 1) { continue; }
                    break;
                  }
                  for (let j: int = 0; j < 2; j = j + 1) {
                    total = total + j;
                  }
                  for (let s: int of arr) {
                    total = total + s;
                  }
                  let t: table = { k: 1 };
                  delete t.k;
                  try {
                    if (total < 0) { throw { message: "bad" }; }
                  } catch (e) {
                    total = 0;
                  }
                  function innerFn(v: int): int {
                    return v + 1;
                  }
                  total = total + innerFn(1);
                  class LocalBox {
                    n: int = 1;
                  }
                  return total;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the statement-grammar fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass cls =
                compile.serializedOf("main.deal", "AllStatements");
            check(cls != null, "AllStatements has a serialized plan");
            if (cls == null) {
                return;
            }
            String content = compile.providerContentOf("lib.deal",
                "allStatements");
            for (String kind : FIFTEEN_STATEMENT_KINDS) {
                check(content.contains("\"kind\":\"" + kind + "\""),
                    "the canonical statement grammar covers statement"
                        + " kind " + kind);
            }
            check(content.contains("\"bindingMarker\":\"total\""),
                "the variable declaration binding marker serializes");
            check(content.contains("\"typeDescriptor\":\"int\""),
                "the annotated variable declaration type descriptor"
                    + " serializes");
            check(content.contains("\"condition\""),
                "conditions serialize in their fixed role");
            check(content.contains("\"value\""),
                "return/throw values serialize in their fixed role");
            check(content.contains("\"nested\":{\"function\":"
                    + "{\"body\""),
                "the nested function declaration inlines its full"
                    + " CanonicalFunctionSemantics");
            check(content.contains("\"nested\":{\"planContent\":"
                    + "\"{\\\"classIdentity\\\":\\\"@src/LocalBox\\\""),
                "the nested class declaration inlines its full"
                    + " canonical default-plan content");
            check(compile.providerDigestOf("lib.deal", "allStatements")
                    != null,
                "the statement-provider digest was demanded");
            ResolvedDefaultExpression f = cls.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(f.runtimeResources().size() == 1
                    && "allStatements".equals(f.runtimeResources()
                        .iterator().next().semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "the importing default completes the wrapper"
                    + " reference");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Epic criterion 5: canonical-content sensitivity (same-root
    // recompiles, so unchanged inputs stay byte-identical)
    // =========================================================================

    private static final String SENSITIVITY_BASE_MAIN = """
        class Sens {
          a: int = 1 + 2;
          c: int[] = [];
          f: int = helper();
          n: number = 1.5;
        }

        function helper(): int {
          return 1;
        }

        export function main(): null {
          return null;
        }
        """;

    private static Map<String, String> sensFiles(String mainSource) {
        return Map.of("deal.json", MANIFEST, "src/main.deal", mainSource);
    }

    private static String sensContentOf(Compile compile, String fieldName) {
        DefaultSemanticSerializer.SerializedDefaultClass cls =
            compile.serializedOf("main.deal", "Sens");
        if (cls == null) {
            return null;
        }
        for (CompilerClassDefaultEntry entry
                : cls.completedPlan().orderedFields()) {
            if (entry.name().equals(fieldName)
                    && entry.defaultExpression() != null) {
                return entry.defaultExpression()
                    .canonicalSemanticContent();
            }
        }
        return null;
    }

    private static void testCanonicalSensitivity() throws Exception {
        System.out.println("-- Canonical-content sensitivity (literal,"
            + " operator, type, target, identity, provider digest,"
            + " behavior-affecting range) --");
        Compile base = new Compile(sensFiles(SENSITIVITY_BASE_MAIN),
            "src/main.deal");
        try {
            check(base.success, "the sensitivity base compiles: "
                + base.diagnostics);
            String baseA = sensContentOf(base, "a");
            String baseF = sensContentOf(base, "f");
            String baseC = sensContentOf(base, "c");
            String basePlanDigest = base.serializedOf("main.deal", "Sens")
                .planDigest();
            check(baseA != null && baseF != null && baseC != null,
                "the base defaults serialize");

            // Literal change (field a only).
            Compile literal = base.recompile(sensFiles(
                SENSITIVITY_BASE_MAIN.replace("a: int = 1 + 2;",
                    "a: int = 1 + 3;")));
            check(literal.success, "the literal variant compiles");
            check(!sensContentOf(literal, "a").equals(baseA),
                "a literal change changes canonicalSemanticContent");
            check(!literal.serializedOf("main.deal", "Sens").planDigest()
                    .equals(basePlanDigest),
                "a literal change changes the consumer planDigest");
            check(sensContentOf(literal, "f").equals(baseF),
                "an unrelated default stays byte-identical (full-content"
                    + " equality across same-deployment recompiles)");

            // Operator change.
            Compile operator = base.recompile(sensFiles(
                SENSITIVITY_BASE_MAIN.replace("a: int = 1 + 2;",
                    "a: int = 1 * 2;")));
            check(operator.success, "the operator variant compiles");
            check(!sensContentOf(operator, "a").equals(baseA),
                "an operator change changes canonicalSemanticContent");
            check(!sensContentOf(operator, "a")
                    .equals(sensContentOf(literal, "a")),
                "operator and literal changes yield distinct content");

            // Type change (int[] -> number[] with the same literal).
            Compile typeChange = base.recompile(sensFiles(
                SENSITIVITY_BASE_MAIN.replace("c: int[] = [];",
                    "c: number[] = [];")));
            check(typeChange.success, "the type variant compiles: "
                + typeChange.diagnostics);
            check(!sensContentOf(typeChange, "c").equals(baseC),
                "a resolved type change changes the canonical content"
                    + " (resultDescriptor)");
            check(sensContentOf(typeChange, "c").contains(
                    "\"resultDescriptor\":\"[number]\"")
                    && baseC.contains(
                        "\"resultDescriptor\":\"[int]\""),
                "the type change is visible as the E4 canonical result"
                    + " descriptor");

            // Call-target change (same-module callee).
            Compile target = base.recompile(sensFiles("""
                class Sens {
                  a: int = 1 + 2;
                  c: int[] = [];
                  f: int = helper2();
                  n: number = 1.5;
                }

                function helper(): int {
                  return 1;
                }

                function helper2(): int {
                  return 2;
                }

                export function main(): null {
                  return null;
                }
                """));

            check(target.success, "the target variant compiles: "
                + target.diagnostics);
            check(!sensContentOf(target, "f").equals(baseF),
                "a call-target change changes canonicalSemanticContent");

            // Behavior-affecting range change (field a moves; every
            // serialized range shifts).
            Compile range = base.recompile(sensFiles(
                SENSITIVITY_BASE_MAIN.replace("class Sens {",
                    "class Sens {\n  // a leading comment moves every"
                        + " behavior-affecting range")));
            check(range.success, "the range variant compiles");
            check(!sensContentOf(range, "a").equals(baseA),
                "a behavior-affecting range change changes"
                    + " canonicalSemanticContent");
            check(baseA.contains("\"startLine\":2")
                    && sensContentOf(range, "a")
                        .contains("\"startLine\":3"),
                "the root range is serialized exactly when"
                    + " behavior-affecting");

            // Semantic module/resource identity change (the same API
            // moves to a different provider file; same root).
            Map<String, String> identityFiles = new LinkedHashMap<>();
            identityFiles.put("deal.json", MANIFEST);
            identityFiles.put("src/main.deal", """
                import * as L from "./lib"

                class Sens {
                  a: int = 1 + 2;
                  c: int[] = [];
                  f: int = L.pick();
                  n: number = 1.5;
                }

                export function main(): null {
                  return null;
                }
                """);
            identityFiles.put("src/lib.deal", """
                export function pick(): int {
                  return 1;
                }
                """);
            Compile identity = new Compile(identityFiles, "src/main.deal");
            try {
                check(identity.success, "the identity variant compiles: "
                    + identity.diagnostics);
                String pickDigestBefore = identity.providerDigestOf(
                    "lib.deal", "pick");
                String planBefore = identity.serializedOf("main.deal",
                    "Sens").planDigest();
                Map<String, String> movedFiles = new LinkedHashMap<>();
                movedFiles.put("deal.json", MANIFEST);
                movedFiles.put("src/main.deal",
                    identityFiles.get("src/main.deal")
                        .replace("\"./lib\"", "\"./lib2\""));
                movedFiles.put("src/lib2.deal",
                    identityFiles.get("src/lib.deal"));
                Compile moved = identity.recompile(movedFiles);
                check(moved.success, "the moved-provider variant"
                    + " compiles: " + moved.diagnostics);
                check(!moved.serializedOf("main.deal", "Sens")
                        .planDigest().equals(planBefore),
                    "a provider resolution change (same API, different"
                        + " module) changes the consumer planDigest");
                String pickContentBefore = identity.providerContentOf(
                    "lib.deal", "pick");
                String pickContentAfter = moved.providerContentOf(
                    "lib2.deal", "pick");
                check(pickContentBefore.equals(pickContentAfter),
                    "identical provider bodies serialize byte-identically"
                        + " (the signature/body grammar is path-free)");
                check(pickDigestBefore.equals(moved.providerDigestOf(
                        "lib2.deal", "pick")),
                    "identical provider bodies in different modules"
                        + " yield the identical provider digest (D5: the"
                        + " digest covers the signature plus typed body"
                        + " semantics; no address, path, or ordinal"
                        + " enters it)");
                String fBefore = sensContentOf(identity, "f");
                String fAfter = sensContentOf(moved, "f");
                check(!fBefore.equals(fAfter),
                    "the provider identity change is visible in the"
                        + " consumer canonical content");
            } finally {
                deleteRecursively(identity.root);
            }

            // Provider digest (implementation) change: the same
            // provider file with a changed body (same root).
            Map<String, String> providerFiles = new LinkedHashMap<>(
                identityFiles);
            Compile provider = new Compile(providerFiles, "src/main.deal");
            try {
                check(provider.success, "the provider variant compiles");
                String pickBefore = provider.providerDigestOf("lib.deal",
                    "pick");
                String planBefore = provider.serializedOf("main.deal",
                    "Sens").planDigest();
                Map<String, String> changed = new LinkedHashMap<>(
                    providerFiles);
                changed.put("src/lib.deal", """
                    export function pick(): int {
                      return 3;
                    }
                    """);
                Compile changedCompile = provider.recompile(changed);
                check(changedCompile.success,
                    "the changed-provider variant compiles: "
                        + changedCompile.diagnostics);
                String pickAfter = changedCompile.providerDigestOf(
                    "lib.deal", "pick");
                check(isSha256Hex(pickBefore) && isSha256Hex(pickAfter)
                        && !pickBefore.equals(pickAfter),
                    "a provider implementation change changes the"
                        + " provider digest");
                check(!changedCompile.serializedOf("main.deal", "Sens")
                        .planDigest().equals(planBefore),
                    "a provider digest change changes the consumer"
                        + " planDigest before any cache reuse (provider"
                        + " versioning)");
            } finally {
                deleteRecursively(provider.root);
            }
        } finally {
            deleteRecursively(base.root);
        }
    }

    // =========================================================================
    // Plan projections and digest derivation
    // =========================================================================

    private static void testPlanProjectionsAndDigestDerivation()
            throws Exception {
        System.out.println("-- canonicalPlanContent / planDigest /"
            + " semanticDefaultContents projections --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class Pair {
                  y: int = 1;
                  x: int = 2;
                  z?: int;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the projection fixture compiles: " + compile.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass cls =
                compile.serializedOf("main.deal", "Pair");
            check(cls != null, "Pair has a serialized plan");
            if (cls == null) {
                return;
            }
            String planContent = cls.canonicalPlanContent();
            check(planContent.contains("\"serializerVersion\":\"1\""),
                "canonicalPlanContent carries the serializer version");
            check(planContent.contains(
                    "\"classIdentity\":\"@src/Pair\""),
                "canonicalPlanContent carries the canonical class"
                    + " identity text");
            check(planContent.contains(
                    "\"declaringSemanticModuleIdentityDigest\":\"")
                    && !planContent.contains("file:"),
                "canonicalPlanContent carries the declaring module"
                    + " identity as a digest only (privacy)");
            check(cls.planDigest().equals(digestOf(planContent)),
                "planDigest = SHA-256 over the length-prefixed UTF-8 of"
                    + " canonicalPlanContent");
            check(planContent.contains("\"entries\":["),
                "canonicalPlanContent serializes the entries as an"
                    + " ordered JSON array (not a key-sorted object)");
            check(planContent.indexOf("\"name\":\"y\"")
                    < planContent.indexOf("\"name\":\"x\"")
                    && planContent.indexOf("\"name\":\"x\"")
                        < planContent.indexOf("\"name\":\"z\""),
                "canonicalPlanContent keeps entry order in class"
                    + " source order (y, x, z — not alphabetical)");
            check(planContent.contains("\"optional\":false")
                    && planContent.contains("\"optional\":true"),
                "the optional flags serialize per entry");
            check(planContent.contains(
                    "\"canonicalDefaultContent\":null"),
                "the optional entry carries the absence marker");
            String semanticContents = cls.semanticDefaultContents();
            check(semanticContents.contains("\"entries\":["),
                "semanticDefaultContents serializes the entries as an"
                    + " ordered JSON array (not a key-sorted object)");
            check(semanticContents.indexOf("\"name\":\"y\"")
                    < semanticContents.indexOf("\"name\":\"x\"")
                    && semanticContents.indexOf("\"name\":\"x\"")
                        < semanticContents.indexOf(
                            "\"name\":\"z\""),
                "semanticDefaultContents keeps entry order in class"
                    + " source order (y, x, z — not alphabetical)");
            check(semanticContents.contains("\"optional\":false")
                    && semanticContents.contains("\"optional\":true")
                    && semanticContents.contains(
                        "\"canonicalDefaultContent\":null"),
                "the semanticDefaultContents projection carries the"
                    + " full per-entry shape (name, runtimeTypeDescriptor,"
                    + " optional, canonicalDefaultContent)");
            String xContent = cls.completedPlan().orderedFields().get(1)
                .defaultExpression().canonicalSemanticContent();
            check(planContent.contains(xContent),
                "canonicalPlanContent embeds the canonical default"
                    + " content byte-exactly");
            check(!cls.semanticDefaultContents().contains(
                    "\"runtimeDependencies\"")
                    && !cls.semanticDefaultContents().contains(
                        "\"importAlias\""),
                "dependencies stay outside plan content (graph data):"
                    + " no dependency-record field is present");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Plan entry order: the pinned class-source entry order enters the
    // canonical plan text literally (an order-only plan variant must
    // never share one planDigest, D6/D8)
    // =========================================================================

    private static void testPlanEntryOrderSensitivity() throws Exception {
        System.out.println("-- Plan entry order: class source order"
            + " enters canonicalPlanContent/planDigest literally --");
        Map<String, String> ordered = Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class OrderSensitive {
                  b?: int;
                  a?: int;
                }

                export function main(): null {
                  return null;
                }
                """);
        Map<String, String> reordered = Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class OrderSensitive {
                  a?: int;
                  b?: int;
                }

                export function main(): null {
                  return null;
                }
                """);
        Compile first = new Compile(ordered, "src/main.deal");
        try {
            check(first.success, "the entry-order fixture compiles: "
                + first.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass before =
                first.serializedOf("main.deal", "OrderSensitive");
            check(before != null,
                "OrderSensitive has a serialized plan");
            if (before == null) {
                return;
            }
            List<String> namesBefore = before.completedPlan()
                .orderedFields().stream()
                .map(CompilerClassDefaultEntry::name).toList();
            check(namesBefore.equals(List.of("b", "a")),
                "the completed plan preserves the source order (b, a)");
            String planBefore = before.canonicalPlanContent();
            check(planBefore.indexOf("\"name\":\"b\"")
                    < planBefore.indexOf("\"name\":\"a\""),
                "canonicalPlanContent lists b before a (class source"
                    + " order, not key-sorted)");
            check(before.semanticDefaultContents().indexOf(
                    "\"name\":\"b\"")
                    < before.semanticDefaultContents().indexOf(
                        "\"name\":\"a\""),
                "semanticDefaultContents lists b before a (class"
                    + " source order, not key-sorted)");
            Compile second = first.recompile(reordered);
            check(second.success, "the reordered variant compiles: "
                + second.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass after =
                second.serializedOf("main.deal", "OrderSensitive");
            check(after != null,
                "the reordered variant has a serialized plan");
            if (after == null) {
                return;
            }
            List<String> namesAfter = after.completedPlan()
                .orderedFields().stream()
                .map(CompilerClassDefaultEntry::name).toList();
            check(namesAfter.equals(List.of("a", "b")),
                "the reordered plan preserves its source order (a, b)");
            check(!before.planDigest().equals(after.planDigest()),
                "an order-only plan variant changes planDigest (the"
                    + " pinned plan identity never collapses distinct"
                    + " plans)");
            check(!before.canonicalPlanContent().equals(
                    after.canonicalPlanContent()),
                "an order-only plan variant changes"
                    + " canonicalPlanContent (every per-entry default"
                    + " content is byte-identical here — the absence"
                    + " markers — so only the order differs)");
            check(!before.semanticDefaultContents().equals(
                    after.semanticDefaultContents()),
                "an order-only plan variant changes the"
                    + " semanticDefaultContents projection");
        } finally {
            deleteRecursively(first.root);
        }
    }

    // =========================================================================
    // Default-nested function-expression bodies resolve type
    // annotations at the body/declaration scope — never the module
    // root scope (checker-accepted programs with body-local class
    // annotations must not be E6005-rejected, D6/D9 losslessness)
    // =========================================================================

    private static void testDefaultNestedScopeResolution()
            throws Exception {
        System.out.println("-- Default-nested function-expression body"
            + " annotations resolve at the declaration scope --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                function make(): null {
                  class LocalClass {
                    n: int = 1;
                  }
                  class Box {
                    f: (v: LocalClass) => LocalClass = function(v: LocalClass): LocalClass {
                      class FeLocal {
                        m: int = 2;
                      }
                      let x: LocalClass = v;
                      function innerCopy(w: LocalClass): LocalClass {
                        return v;
                      }
                      return v;
                    };
                  }
                  return null;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the nested-scope fixture compiles (the checker"
                    + " accepts the body-local annotations): "
                    + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors(),
                "the serializer resolves the body-local annotations at"
                    + " the class declaration scope, never the module"
                    + " root scope (no E6005 false rejection): "
                    + result.diagnostics());
            DefaultSemanticSerializer.SerializedDefaultClass box =
                compile.serializedOf("main.deal", "Box");
            check(box != null, "Box has a serialized plan");
            if (box == null) {
                return;
            }
            String content = box.completedPlan().orderedFields().get(0)
                .defaultExpression().canonicalSemanticContent();
            check(content.contains(
                    "\"typeDescriptor\":\"@src/LocalClass\""),
                "the annotated body-local let serializes the E4"
                    + " descriptor of the locally declared class");
            check(content.contains("\"bindingMarker\":\"x\""),
                "the body-local let binding marker serializes");
            check(content.contains(
                    "\"returnDescriptor\":\"@src/LocalClass\"")
                    && content.contains(
                        "\"bindingMarker\":\"innerCopy\""),
                "the nested function declaration's signature resolves"
                    + " against the function-expression body scope and"
                    + " inlines its semantics");
            check(content.contains("\"resultDescriptor\":"
                    + "\"(@src/LocalClass)->@src/LocalClass\""),
                "the function-expression result descriptor carries the"
                    + " local class descriptor");
            check(content.contains(
                    "\"nested\":{\"planContent\":"
                        + "\"{\\\"classIdentity\\\":"
                        + "\\\"@src/FeLocal\\\""),
                "the function-expression-body class declaration"
                    + " inlines its full canonical plan content");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Same-named classes in distinct scopes: class plans, the digest
    // memo, and the declaration-scope lookup are keyed by the exact
    // declaration (name plus complete scalar range), never by declared
    // name alone — the second same-named class serializes its own
    // content/digest and resolves its defaults in its own declaration
    // scope (D6/D8 identity, provider versioning, fail-closed totality)
    // =========================================================================

    private static void testSameNamedClassesDistinctScopes()
            throws Exception {
        System.out.println("-- Same-named classes in distinct scopes:"
            + " declaration-keyed plans, scopes, and digests --");
        String mainSource = """
            function makeA(): null {
              class LocalA {
                x: int = 1;
              }
              class Same {
                f: int = (function(v: LocalA): int {
                  return v.x;
                })({});
              }
              return null;
            }

            function makeB(): null {
              class LocalB {
                y: int = 5;
              }
              class Same {
                g: int = (function(w: LocalB): int {
                  return w.y + 1;
                })({});
              }
              return null;
            }

            export function main(): null {
              return null;
            }
            """;
        Compile first = new Compile(Map.of(
            "deal.json", MANIFEST, "src/main.deal", mainSource),
            "src/main.deal");
        try {
            check(first.success,
                "the same-named fixture compiles: "
                    + first.diagnostics);
            DefaultSemanticSerializer.Result result = first.serialize();
            check(!result.hasErrors() && result.diagnostics().isEmpty(),
                "the serializer accepts the same-named classes: "
                    + result.diagnostics());
            List<DefaultSemanticSerializer.SerializedDefaultClass> plans =
                modulePlansOf(result, "main.deal");
            check(plans.size() == 4,
                "the module serializes all four plans (LocalA, Same,"
                    + " LocalB, Same): got " + plans.size());
            if (plans.size() != 4) {
                return;
            }
            DefaultSemanticSerializer.SerializedDefaultClass sameF =
                null;
            DefaultSemanticSerializer.SerializedDefaultClass sameG =
                null;
            for (DefaultSemanticSerializer.SerializedDefaultClass plan
                    : plans) {
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"f\"")) {
                    sameF = plan;
                }
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"g\"")) {
                    sameG = plan;
                }
            }
            check(sameF != null && sameG != null,
                "both same-named Same plans serialize their own"
                    + " fields (f and g)");
            if (sameF == null || sameG == null) {
                return;
            }
            check("Same".equals(sameF.completedPlan().classIdentity()
                    .className())
                    && "Same".equals(sameG.completedPlan().classIdentity()
                        .className()),
                "both same-named plans carry the class name Same");
            check(sameF.canonicalPlanContent().contains("\"name\":\"f\"")
                    && !sameF.canonicalPlanContent().contains(
                        "\"name\":\"g\""),
                "the f-bearing Same plan serializes exactly its own"
                    + " field f (never the other class's fields)");
            check(sameG.canonicalPlanContent().contains("\"name\":\"g\"")
                    && !sameG.canonicalPlanContent().contains(
                        "\"name\":\"f\""),
                "the g-bearing Same plan serializes exactly its own"
                    + " field g (never the other class's fields)");
            String fContent = sameF.completedPlan().orderedFields().get(0)
                .defaultExpression().canonicalSemanticContent();
            String gContent = sameG.completedPlan().orderedFields().get(0)
                .defaultExpression().canonicalSemanticContent();
            check(fContent.contains(
                    "\"(@src/LocalA)->int\""),
                "the f-bearing Same default's function-expression"
                    + " parameter annotation resolves in its own"
                    + " declaration scope (LocalA)");
            check(gContent.contains(
                    "\"(@src/LocalB)->int\""),
                "the g-bearing Same default's function-expression"
                    + " parameter annotation resolves in its own"
                    + " declaration scope (LocalB)");
            check(!sameF.planDigest().equals(sameG.planDigest()),
                "same-named classes carry distinct planDigests (no"
                    + " silent collapse)");
            check(sameF.planDigest().equals(digestOf(
                    sameF.canonicalPlanContent()))
                    && sameG.planDigest().equals(digestOf(
                        sameG.canonicalPlanContent())),
                "each same-named plan's planDigest derives from its own"
                    + " canonicalPlanContent");

            // Provider versioning: changing a literal inside the
            // second same-named class's default changes exactly that
            // class's planDigest; the first class stays stable.
            String mutated = mainSource.replace("return w.y + 1;",
                "return w.y + 2;");
            Compile second = first.recompile(Map.of(
                "deal.json", MANIFEST, "src/main.deal", mutated));
            check(second.success,
                "the mutated variant compiles: " + second.diagnostics);
            List<DefaultSemanticSerializer.SerializedDefaultClass>
                mutatedPlans = modulePlansOf(second.serialize(),
                    "main.deal");
            check(mutatedPlans.size() == 4,
                "the mutated variant serializes all four plans: got "
                    + mutatedPlans.size());
            if (mutatedPlans.size() != 4) {
                return;
            }
            DefaultSemanticSerializer.SerializedDefaultClass
                mutatedF = null;
            DefaultSemanticSerializer.SerializedDefaultClass
                mutatedG = null;
            for (DefaultSemanticSerializer.SerializedDefaultClass plan
                    : mutatedPlans) {
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"f\"")) {
                    mutatedF = plan;
                }
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"g\"")) {
                    mutatedG = plan;
                }
            }
            check(mutatedF != null && mutatedG != null,
                "the mutated variant still serializes both same-named"
                    + " plans");
            if (mutatedF == null || mutatedG == null) {
                return;
            }
            check(mutatedF.planDigest().equals(sameF.planDigest()),
                "changing the second class's literal leaves the first"
                    + " same-named class's planDigest stable (provider"
                    + " versioning)");
            check(!mutatedG.planDigest().equals(sameG.planDigest()),
                "changing the second class's literal changes that"
                    + " class's planDigest (its content is its own)");
            check(mutatedG.canonicalPlanContent().contains(
                    "\"literalValue\":2"),
                "the mutated literal enters the second class's"
                    + " canonical plan content");
        } finally {
            deleteRecursively(first.root);
        }
    }

    // =========================================================================
    // Same-named nested and imported class plans: inline nesting and
    // digest demand resolve by the exact declaration (name plus
    // complete scalar range) — never the first same-named plan in
    // module order
    // =========================================================================

    private static void testSameNamedNestedAndImportedPlans()
            throws Exception {
        System.out.println("-- Same-named nested/imported class plans:"
            + " inline nesting and digest demand keyed by"
            + " declaration --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"

                class Same {
                  n: int = 1;
                }

                class Box {
                  f: int = (function(): int {
                    class Same {
                      m: int = 7;
                    }
                    return 3;
                  })();
                  g: L.Widget = {};
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                function make(): null {
                  class Widget {
                    inner: int = 9;
                  }
                  return null;
                }

                export class Widget {
                  tag: int = 3;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the same-named nested/imported fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors() && result.diagnostics().isEmpty(),
                "the serializer accepts the plans: "
                    + result.diagnostics());
            List<DefaultSemanticSerializer.SerializedDefaultClass>
                mainPlans = modulePlansOf(result, "main.deal");
            List<DefaultSemanticSerializer.SerializedDefaultClass>
                libPlans = modulePlansOf(result, "lib.deal");
            check(mainPlans.size() == 3,
                "the main module serializes three plans (top Same,"
                    + " Box, nested Same): got " + mainPlans.size());
            check(libPlans.size() == 2,
                "the lib module serializes both same-named Widget"
                    + " plans: got " + libPlans.size());
            if (mainPlans.size() != 3 || libPlans.size() != 2) {
                return;
            }
            DefaultSemanticSerializer.SerializedDefaultClass box =
                null;
            DefaultSemanticSerializer.SerializedDefaultClass topSame =
                null;
            DefaultSemanticSerializer.SerializedDefaultClass nestedSame =
                null;
            for (DefaultSemanticSerializer.SerializedDefaultClass plan
                    : mainPlans) {
                String content = plan.canonicalPlanContent();
                if (content.contains("\"name\":\"f\"")
                        && content.contains("\"name\":\"g\"")) {
                    box = plan;
                } else if (content.contains("\"name\":\"n\"")) {
                    topSame = plan;
                } else if (content.contains("\"name\":\"m\"")) {
                    nestedSame = plan;
                }
            }
            check(box != null && topSame != null
                    && nestedSame != null,
                "the main plans are identifiable by their own field"
                    + " content (Box, top Same, nested Same)");
            if (box == null || topSame == null || nestedSame == null) {
                return;
            }
            String fContent = box.completedPlan().orderedFields().get(0)
                .defaultExpression().canonicalSemanticContent();
            check(fContent.contains("\\\"name\\\":\\\"m\\\"")
                    && fContent.contains("\\\"literalValue\\\":7"),
                "the function-expression body's nested Same inlines"
                    + " its own plan (field m), never the top-level"
                    + " Same's (field n)");
            check(!fContent.contains("\\\"name\\\":\\\"n\\\""),
                "the top-level Same plan is never inlined for the"
                    + " nested declaration");
            check(nestedSame.canonicalPlanContent().contains(
                    "\"name\":\"m\"")
                    && nestedSame.canonicalPlanContent()
                        .contains("\"literalValue\":7"),
                "the nested Same serializes its own plan with field m");
            check(topSame.canonicalPlanContent().contains(
                    "\"name\":\"n\"")
                    && topSame.canonicalPlanContent()
                        .contains("\"literalValue\":1"),
                "the top-level Same serializes its own plan with"
                    + " field n");
            check(!topSame.planDigest().equals(
                    nestedSame.planDigest()),
                "same-named top-level and nested plans carry distinct"
                    + " planDigests");

            DefaultSemanticSerializer.SerializedDefaultClass topWidget =
                null;
            DefaultSemanticSerializer.SerializedDefaultClass
                nestedWidget = null;
            for (DefaultSemanticSerializer.SerializedDefaultClass plan
                    : libPlans) {
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"tag\"")) {
                    topWidget = plan;
                }
                if (plan.canonicalPlanContent().contains(
                        "\"name\":\"inner\"")) {
                    nestedWidget = plan;
                }
            }
            check(topWidget != null && nestedWidget != null,
                "both same-named Widget plans are identifiable by"
                    + " their own field content (tag, inner)");
            if (topWidget == null || nestedWidget == null) {
                return;
            }
            check(nestedWidget.canonicalPlanContent().contains(
                    "\"name\":\"inner\"")
                    && nestedWidget.canonicalPlanContent().contains(
                        "\"literalValue\":9"),
                "the nested Widget serializes its own plan (inner)");
            check(topWidget.canonicalPlanContent().contains(
                    "\"name\":\"tag\"")
                    && topWidget.canonicalPlanContent().contains(
                        "\"literalValue\":3"),
                "the exported Widget serializes its own plan (tag)");
            check(!topWidget.planDigest().equals(
                    nestedWidget.planDigest()),
                "the same-named Widget plans carry distinct"
                    + " planDigests");

            ResolvedDefaultExpression g = box.completedPlan()
                .orderedFields().get(1).defaultExpression();
            check(g.runtimeResources().size() == 1,
                "the imported Widget literal completes one resource");
            RuntimeResourceReference gRef = g.runtimeResources()
                .iterator().next();
            check(gRef.kind() == RuntimeResourceReference.Kind
                    .IMPORTED_CLASS_DEFAULT_PLAN
                    && "Widget".equals(gRef.semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "the completed resource is the imported Widget plan");
            check(gRef.providerContractDigest().equals(
                    topWidget.planDigest()),
                "the digest demand resolves the exported Widget by"
                    + " declaration range (top-level), never the"
                    + " nested same-named Widget");
            check(!gRef.providerContractDigest().equals(
                    nestedWidget.planDigest()),
                "the nested same-named Widget's digest is never"
                    + " substituted");
            check(g.canonicalSemanticContent().contains(
                    topWidget.planDigest()),
                "the canonical target embeds the exported Widget's"
                    + " provider digest");
            check(topWidget.canonicalPlanContent().equals(
                    result.providerContents().get(
                        gRef.semanticResourceIdentity())),
                "the demanded provider's canonical content is the"
                    + " exported Widget's plan content");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Provider versioning and determinism across runs
    // =========================================================================

    private static void testProviderVersioningAndStability()
            throws Exception {
        System.out.println("-- Provider versioning and cross-run"
            + " digest stability --");
        Map<String, String> files = Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"

                class Consumer {
                  n: int = L.pick();
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                export function pick(): int {
                  return 7;
                }
                """);
        Compile first = new Compile(files, "src/main.deal");
        try {
            check(first.success, "the versioning fixture compiles: "
                + first.diagnostics);
            String pickDigest = first.providerDigestOf("lib.deal",
                "pick");
            String planDigest = first.serializedOf("main.deal",
                "Consumer").planDigest();
            String pickContent = first.providerContentOf("lib.deal",
                "pick");
            check(isSha256Hex(pickDigest),
                "the provider digest is a 64-hex SHA-256");
            check(pickContent != null
                    && pickContent.contains("\"serializerVersion\":\"1\"")
                    && pickContent.contains("\"body\""),
                "the provider canonical content is the statement-level"
                    + " CanonicalFunctionSemantics");
            check(pickDigest.equals(digestOf(pickContent)),
                "the provider digest derives from the canonical"
                    + " function content");
            String pickAgain = first.providerDigestOf("lib.deal",
                "pick");
            check(pickDigest.equals(pickAgain),
                "re-serializing the same compile yields identical"
                    + " digests");
            // An identical recompile over the same root: identical
            // digests and content (unchanged providers stay stable
            // across runs).
            Compile second = first.recompile(files);
            check(second.providerDigestOf("lib.deal", "pick")
                    .equals(pickDigest)
                    && second.providerContentOf("lib.deal", "pick")
                        .equals(pickContent)
                    && second.serializedOf("main.deal", "Consumer")
                        .planDigest().equals(planDigest),
                "an unchanged provider keeps byte-stable content and"
                    + " digests across runs (acyclic fixture)");
        } finally {
            deleteRecursively(first.root);
        }
    }

    // =========================================================================
    // Resource completion (the plan-embedded runtimeResources)
    // =========================================================================

    private static void testResourceCompletion() throws Exception {
        System.out.println("-- Resource completion: digest-bearing"
            + " runtimeResources in first-occurrence order --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"
                import * as S from "../shared"

                class Outer {
                  a: int = localHelper();
                  b: L.Rec = {};
                  c: L.Rec[] = [L.makeRec({ tag: 5 })];
                  d: L.Rec[] = [];
                  e: L.Rec | null = null;
                  f: int = L.getTag({ tag: 3 });
                  g: int = S.scale(2);
                  h: L.Rec = { inner: { tag: 9 } };
                }

                function localHelper(): int {
                  return 7;
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                export class Rec {
                  tag: int = 0;
                  inner: Rec = {};
                }
                export function getTag(r: Rec): int {
                  return r.tag;
                }
                export function makeRec(r: Rec): Rec {
                  return r;
                }
                """,
            "shared.deal", """
                export function scale(v: int): int {
                  return v * 2;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the completion fixture compiles: " + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors(),
                "the serializer completes the plans: "
                    + result.diagnostics());
            DefaultSemanticSerializer.SerializedDefaultClass outer =
                compile.serializedOf("main.deal", "Outer");
            check(outer != null, "Outer has a serialized plan");
            if (outer == null) {
                return;
            }
            List<String> fieldNames = outer.completedPlan().orderedFields()
                .stream().map(CompilerClassDefaultEntry::name).toList();
            check(fieldNames.equals(List.of("a", "b", "c", "d", "e",
                    "f", "g", "h")),
                "the completed plan preserves class source order");
            ResolvedDefaultExpression b = outer.completedPlan()
                .orderedFields().get(1).defaultExpression();
            check(b.runtimeResources().size() == 1
                    && b.runtimeResources().iterator().next().kind()
                        == RuntimeResourceReference.Kind
                            .IMPORTED_CLASS_DEFAULT_PLAN,
                "field b completes exactly one class-plan resource");
            RuntimeResourceReference bRef =
                b.runtimeResources().iterator().next();
            check("Rec".equals(bRef.semanticResourceIdentity()
                    .lexicalDeclarationIdentity().declaredName()),
                "field b's resource is the imported Rec plan");
            check(isSha256Hex(bRef.providerContractDigest()),
                "field b's resource carries a real provider digest");
            String recPlanDigest = compile.serializedOf("lib.deal",
                "Rec").planDigest();
            check(bRef.providerContractDigest().equals(recPlanDigest),
                "the class-plan provider digest is the provider plan's"
                    + " planDigest");
            check(b.canonicalSemanticContent().contains(
                    recPlanDigest),
                "the canonical target embeds the real provider digest");
            check(b.canonicalSemanticContent().contains(
                    "\"sourceRange\""),
                "the reference site serializes its behavior-affecting"
                    + " range");

            ResolvedDefaultExpression c = outer.completedPlan()
                .orderedFields().get(2).defaultExpression();
            check(c.runtimeResources().size() == 1
                    && c.runtimeResources().iterator().next().kind()
                        == RuntimeResourceReference.Kind
                            .IMPORTED_FUNCTION_WRAPPER
                    && "makeRec".equals(c.runtimeResources().iterator()
                        .next().semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "field c completes the imported makeRec wrapper");
            check(c.runtimeResources().iterator().next()
                    .providerContractDigest().equals(
                        compile.providerDigestOf("lib.deal", "makeRec")),
                "the wrapper resource carries the function provider"
                    + " digest");
            ResolvedDefaultExpression f = outer.completedPlan()
                .orderedFields().get(5).defaultExpression();
            check("getTag".equals(f.runtimeResources().iterator().next()
                    .semanticResourceIdentity()
                    .lexicalDeclarationIdentity().declaredName()),
                "field f completes the imported getTag wrapper");
            ResolvedDefaultExpression g = outer.completedPlan()
                .orderedFields().get(6).defaultExpression();
            check("scale".equals(g.runtimeResources().iterator().next()
                    .semanticResourceIdentity()
                    .lexicalDeclarationIdentity().declaredName())
                    && g.runtimeResources().iterator().next()
                        .semanticResourceIdentity()
                        .semanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith("shared.deal"),
                "field g completes the out-of-root provider wrapper");
            ResolvedDefaultExpression h = outer.completedPlan()
                .orderedFields().get(7).defaultExpression();
            check(h.runtimeResources().isEmpty(),
                "the deduplicated Rec repeat (field h) carries no"
                    + " additional resource");
            ResolvedDefaultExpression a = outer.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(a.runtimeResources().isEmpty()
                    && a.resolvedBindings().containsKey("localHelper"),
                "the same-module call publishes no resource");
            List<RuntimeResourceReference> flattened = new ArrayList<>();
            for (CompilerClassDefaultEntry entry
                    : outer.completedPlan().orderedFields()) {
                if (entry.defaultExpression() != null) {
                    flattened.addAll(entry.defaultExpression()
                        .runtimeResources());
                }
            }
            List<DefaultResourceOccurrence> occurrences = new ArrayList<>();
            for (Map.Entry<String, List<PlannedDefaultClass>> entry
                    : compile.orchestrator.plannedDefaultClasses()
                        .entrySet()) {
                if (entry.getKey().endsWith("main.deal")) {
                    for (PlannedDefaultClass planned : entry.getValue()) {
                        if (planned.plan().classIdentity().className()
                                .equals("Outer")) {
                            occurrences.addAll(planned.occurrences());
                        }
                    }
                }
            }
            check(flattened.size() == occurrences.size()
                    && occurrences.size() == 4,
                "the completed resources equal the four planner"
                    + " occurrences (first-occurrence order)");
            for (int i = 0; i < flattened.size(); i++) {
                RuntimeResourceReference ref = flattened.get(i);
                DefaultResourceOccurrence occurrence = occurrences.get(i);
                check(ref.kind() == occurrence.kind()
                        && ref.semanticResourceIdentity().equals(
                            occurrence.semanticResourceIdentity())
                        && ref.sourceRange().equals(
                            occurrence.sourceRange()),
                    "completed resource " + i + " preserves kind,"
                        + " identity, and first-occurrence range");
            }
            check(result.providerDigests().size() == 4,
                "exactly four provider digests were demanded (Rec"
                    + " plan, makeRec, getTag, scale), got "
                    + result.providerDigests().size());
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Function-provider content: statements, targets, embedded digests,
    // ranges, and same-module identity-only embedding
    // =========================================================================

    private static final String FUNCTION_BASE_MAIN = """
        import * as L from "./lib"

        class Consumer {
          n: int = L.outer(1);
        }

        export function main(): null {
          return null;
        }
        """;

    private static final String FUNCTION_BASE_LIB = """
        import * as S from "./other"

        export function inner1(v: int): int {
          return v + 1;
        }

        export function inner2(v: int): int {
          return v + 2;
        }

        export function outer(x: int): int {
          let s = S.scale(x);
          return s + inner1(x) + inner2(x);
        }

        export function main(): null {
          return null;
        }
        """;

    private static final String OTHER = """
        export function scale(v: int): int {
          return v * 2;
        }
        """;

    private static Map<String, String> functionFiles(String libSource) {
        return Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", FUNCTION_BASE_MAIN,
            "src/lib.deal", libSource,
            "src/other.deal", OTHER);
    }

    private static void testFunctionProviderContent() throws Exception {
        System.out.println("-- Function-provider content sensitivity"
            + " and inline nesting --");
        Compile base = new Compile(functionFiles(FUNCTION_BASE_LIB),
            "src/main.deal");
        try {
            check(base.success,
                "the function-provider fixture compiles: "
                    + base.diagnostics);
            String outerContent = base.providerContentOf("lib.deal",
                "outer");
            String outerDigest = base.providerDigestOf("lib.deal",
                "outer");
            check(outerContent != null && isSha256Hex(outerDigest)
                    && outerDigest.equals(digestOf(outerContent)),
                "the outer provider content derives its digest");
            // (Nested function/class inline nesting is asserted on
            // the statement-totality provider content above; this
            // fixture keeps only top-level callees so the sensitivity
            // boundaries are exact.)
            String baseConsumerDigest = base.serializedOf("main.deal",
                "Consumer").planDigest();

            // Statement change in the provider body.
            Compile statement = base.recompile(functionFiles(
                FUNCTION_BASE_LIB.replace(
                    "  return s + inner1(x) + inner2(x);",
                    "  let extra = 1;\n  return s + inner1(x)"
                        + " + inner2(x) + extra;")));
            check(statement.success, "the statement variant compiles: "
                + statement.diagnostics);
            check(!statement.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "a statement change changes the function-provider"
                    + " content/digest");
            check(!statement.serializedOf("main.deal", "Consumer")
                    .planDigest().equals(baseConsumerDigest),
                "the consumer planDigest follows the provider statement"
                    + " change");

            // Call-target change (same-module target identity).
            Compile target = base.recompile(functionFiles(
                FUNCTION_BASE_LIB.replace("inner1(x)",
                    "inner2(x + 1)")));
            check(target.success, "the target variant compiles: "
                + target.diagnostics);
            check(!target.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "a call-target change changes the function-provider"
                    + " content/digest");

            // Embedded imported-provider digest change (other.scale
            // body; same root).
            Map<String, String> embeddedFiles = functionFiles(
                FUNCTION_BASE_LIB);
            embeddedFiles = new LinkedHashMap<>(embeddedFiles);
            embeddedFiles.put("src/other.deal", """
                export function scale(v: int): int {
                  return v * 3;
                }
                """);
            Compile embedded = base.recompile(embeddedFiles);
            check(embedded.success, "the embedded-provider variant"
                + " compiles: " + embedded.diagnostics);
            check(!embedded.providerDigestOf("other.deal", "scale")
                    .equals(base.providerDigestOf("other.deal", "scale")),
                "the imported provider's own digest changes");
            check(!embedded.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "an embedded imported-provider digest change changes"
                    + " the caller's provider content/digest");
            check(!embedded.serializedOf("main.deal", "Consumer")
                    .planDigest().equals(baseConsumerDigest),
                "the consumer planDigest follows the embedded provider"
                    + " change");

            // Behavior-affecting reference-range change (the scale
            // call moves; same-module declaration spans stay fixed).
            Compile range = base.recompile(functionFiles(
                FUNCTION_BASE_LIB.replace("  let s = S.scale(x);",
                    "  let s =\n    S.scale(x);")));
            check(range.success, "the range variant compiles: "
                + range.diagnostics);
            check(!range.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "a behavior-affecting reference-range change changes"
                    + " the function-provider content/digest");
            check(outerContent.contains("\"startLine\":12")
                    && range.providerContentOf("lib.deal", "outer")
                        .contains("\"startLine\":13"),
                "the reference site serializes its exact range (the"
                    + " scale call moved from line 10 to line 11)");

            // Non-behavior-affecting range change (the same-module
            // inner call moves; the scale reference stays fixed).
            Compile nonRange = base.recompile(functionFiles(
                FUNCTION_BASE_LIB.replace(
                    "  return s + inner1(x) + inner2(x);",
                    "  return s + inner1(x)\n    + inner2(x);")));
            check(nonRange.success, "the non-range variant compiles: "
                + nonRange.diagnostics);
            check(nonRange.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "a non-behavior-affecting range change (same-module"
                    + " call move) changes nothing");
            check(nonRange.providerContentOf("lib.deal", "outer")
                    .equals(outerContent),
                "the provider content is byte-identical under the"
                    + " non-behavior-affecting range change");

            // Same-module callee body change: the caller's content
            // does not change (identity-only embedding).
            Map<String, String> calleeFiles = functionFiles(
                FUNCTION_BASE_LIB);
            calleeFiles = new LinkedHashMap<>(calleeFiles);
            calleeFiles.put("src/lib.deal",
                FUNCTION_BASE_LIB.replace("  return v + 2;",
                    "  return v + 3;"));
            Compile callee = base.recompile(calleeFiles);
            check(callee.success, "the callee variant compiles: "
                + callee.diagnostics);
            check(callee.providerDigestOf("lib.deal", "outer")
                    .equals(outerDigest),
                "a same-module callee's body change changes the"
                    + " caller's content not at all (identity-only"
                    + " embedding)");
            check(callee.providerContentOf("lib.deal", "outer")
                    .equals(outerContent),
                "the caller's canonical content is byte-identical"
                    + " under the same-module callee body change");
            check(callee.serializedOf("main.deal", "Consumer")
                    .planDigest().equals(baseConsumerDigest),
                "the consumer planDigest is stable under the"
                    + " same-module callee body change");
            check(callee.providerDigestOf("lib.deal", "inner2")
                    == null,
                "the same-module callee is never demanded as a"
                    + " provider (no digest)");
        } finally {
            deleteRecursively(base.root);
        }
    }

    // =========================================================================
    // Declared wrapper digest and the host-declared class seam
    // =========================================================================

    private static void testDeclaredWrapperAndHostClassSeams()
            throws Exception {
        System.out.println("-- Declared function wrapper digest and"
            + " host-declared class identity-only targets --");
        Compile compile = new Compile(Map.of(
            "deal.json", """
                {
                  "languageVersion": "1.2",
                  "moduleRoots": ["src"],
                  "backend": "luajit",
                  "output": "build",
                  "externals": {
                    "host/cfg": {
                      "declaration": "bindings/cfg.d.deal"
                    }
                  }
                }
                """,
            "src/main.deal", """
                import * as cfg from "host/cfg"

                class UsesHost {
                  d: string = cfg.describe({});
                  e: cfg.Endpoint = {};
                }

                export function main(): null {
                  return null;
                }
                """,
            "bindings/cfg.d.deal", """
                export class Endpoint {
                  path?: string;
                }

                export function describe(e: Endpoint): string;
                """), "src/main.deal");
        try {
            check(compile.success,
                "the host-declared fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass usesHost =
                compile.serializedOf("main.deal", "UsesHost");
            check(usesHost != null, "UsesHost has a serialized plan");
            if (usesHost == null) {
                return;
            }
            String describeDigest = compile.providerDigestOf("cfg.d.deal",
                "describe");
            check(isSha256Hex(describeDigest),
                "the declared wrapper carries a real provider digest");
            String describeContent = compile.providerContentOf(
                "cfg.d.deal", "describe");
            check(describeContent != null
                    && describeContent.contains(
                        "\"kind\":\"DECLARED_FUNCTION_SIGNATURE\"")
                    && describeContent.contains(
                        "\"semanticResourceIdentityDigest\":\"")
                    && !describeContent.contains("file:"),
                "the declared wrapper content is the canonical declared"
                    + " signature plus the declaration identity (digest"
                    + " only)");
            check(describeDigest.equals(digestOf(describeContent)),
                "the declared wrapper digest derives from its content");
            ResolvedDefaultExpression d = usesHost.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(d.runtimeResources().size() == 1
                    && d.runtimeResources().iterator().next()
                        .providerContractDigest()
                        .equals(describeDigest),
                "the declared wrapper reference completes with the"
                    + " wrapper digest");
            ResolvedDefaultExpression e = usesHost.completedPlan()
                .orderedFields().get(1).defaultExpression();
            check(e.runtimeResources().isEmpty(),
                "the host-declared class literal publishes no resource"
                    + " (no plan exists)");
            check(e.canonicalSemanticContent().contains(
                    "\"semanticResourceIdentityDigest\":\"")
                    && !e.canonicalSemanticContent().contains(
                        "\"providerContractDigest\""),
                "the host-declared class literal target serializes"
                    + " identity-only (never a placeholder digest)");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Synthetic @jsonable export providers: imported C$fromJson/C$toJson
    // digests derive from the resolved export signature plus the resource
    // identity digest (the declared-wrapper rule of D5) — never E6005 —
    // and a demanded class provider's canonical plan content stays present
    // in providerContents on the digest-memo fast-path.
    // =========================================================================

    private static void testSyntheticJsonableExportProvider()
            throws Exception {
        System.out.println("-- Imported synthetic @jsonable export"
            + " providers (C$fromJson/C$toJson wrapper digests) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"

                class Consumer {
                  w: L.Widget | null = L.Widget$fromJson("{}");
                  t: string = L.Widget$toJson({});
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                // @jsonable
                export class Widget {
                  label: string = "";
                  count: int = 0;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the synthetic-jsonable-export fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors(),
                "the serializer completes the synthetic-jsonable-export"
                    + " plans: " + result.diagnostics());
            DefaultSemanticSerializer.SerializedDefaultClass consumer =
                compile.serializedOf("main.deal", "Consumer");
            check(consumer != null, "Consumer has a serialized plan");
            if (consumer == null) {
                return;
            }

            ResolvedDefaultExpression w = consumer.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(w.runtimeResources().size() == 1
                    && w.runtimeResources().iterator().next().kind()
                        == RuntimeResourceReference.Kind
                            .IMPORTED_FUNCTION_WRAPPER
                    && "Widget$fromJson".equals(w.runtimeResources()
                        .iterator().next().semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "field w completes the imported Widget$fromJson"
                    + " wrapper");
            RuntimeResourceReference wRef = w.runtimeResources()
                .iterator().next();
            check(isSha256Hex(wRef.providerContractDigest()),
                "field w's resource carries a real provider digest");
            String fromJsonDigest = compile.providerDigestOf("lib.deal",
                "Widget$fromJson");
            check(isSha256Hex(fromJsonDigest),
                "the synthetic fromJson export has a real provider"
                    + " digest");
            check(wRef.providerContractDigest().equals(fromJsonDigest),
                "field w's wrapper digest is the synthetic export's"
                    + " provider digest");
            String fromJsonContent = compile.providerContentOf(
                "lib.deal", "Widget$fromJson");
            check(fromJsonContent != null
                    && fromJsonContent.contains(
                        "\"kind\":\"SYNTHETIC_JSONABLE_EXPORT_SIGNATURE\"")
                    && fromJsonContent.contains(
                        "\"semanticResourceIdentityDigest\":\"")
                    && !fromJsonContent.contains("file:"),
                "the synthetic export content is the canonical resolved"
                    + " signature plus the declaration identity (digest"
                    + " only)");
            check(fromJsonDigest.equals(digestOf(fromJsonContent)),
                "the synthetic export digest derives from its content");
            check(w.canonicalSemanticContent().contains(fromJsonDigest),
                "the canonical target embeds the real provider digest");

            ResolvedDefaultExpression t = consumer.completedPlan()
                .orderedFields().get(1).defaultExpression();
            check(t.runtimeResources().size() == 2,
                "field t completes two resources (toJson wrapper,"
                    + " Widget plan), got "
                    + t.runtimeResources().size());
            List<RuntimeResourceReference> tRefs = List.copyOf(
                t.runtimeResources());
            check(tRefs.get(0).kind()
                        == RuntimeResourceReference.Kind
                            .IMPORTED_FUNCTION_WRAPPER
                    && "Widget$toJson".equals(tRefs.get(0)
                        .semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "first-occurrence order: the toJson wrapper precedes"
                    + " the contextual class-literal plan");
            check(tRefs.get(1).kind()
                        == RuntimeResourceReference.Kind
                            .IMPORTED_CLASS_DEFAULT_PLAN
                    && "Widget".equals(tRefs.get(1)
                        .semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "the contextual Widget literal completes the class-plan"
                    + " resource");
            String widgetPlanContent = compile.serializedOf("lib.deal",
                "Widget").canonicalPlanContent();
            check(tRefs.get(1).providerContractDigest().equals(
                    digestOf(widgetPlanContent)),
                "the Widget plan resource carries the provider plan's"
                    + " planDigest");
            check(tRefs.get(1).providerContractDigest().equals(
                    compile.providerDigestOf("lib.deal", "Widget")),
                "the demanded class provider digest is published");
            String demandedPlanContent = compile.providerContentOf(
                "lib.deal", "Widget");
            check(widgetPlanContent.equals(demandedPlanContent),
                "providerContents carries the demanded class provider's"
                    + " plan content (memo fast-path republish)");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Declaration-module C-struct class plans serialize through the
    // declaration module's rebuilt root scope (the declaration
    // analyzer's resolution surface)
    // =========================================================================

    private static void testDeclarationModuleCStructPlan()
            throws Exception {
        System.out.println("-- Declaration-module C-struct class plans"
            + " (declaration root scope) --");
        Compile compile = new Compile(Map.of(
            "deal.json", """
                {
                  "languageVersion": "1.2",
                  "moduleRoots": ["src"],
                  "backend": "luajit",
                  "output": "build",
                  "externals": {
                    "native/math": {
                      "declaration": "bindings/ffi.d.deal",
                      "nativeLibrary": "libm.so"
                    }
                  }
                }
                """,
            "src/main.deal", """
                import * as M from "native/math"

                class Uses {
                  v: M.Vec2 = {};
                }

                export function main(): null {
                  return null;
                }
                """,
            "bindings/ffi.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number = 1.5;
                  y: number = 2.5;
                }

                export function length(v: Vec2): number;
                """), "src/main.deal");
        try {
            check(compile.success,
                "the C-struct declaration fixture compiles: "
                    + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors(),
                "the serializer serializes the C-struct class plan"
                    + " through the declaration module's root scope: "
                    + result.diagnostics());
            DefaultSemanticSerializer.SerializedDefaultClass vec2 =
                compile.serializedOf("ffi.d.deal", "Vec2");
            check(vec2 != null, "Vec2 has a serialized plan");
            if (vec2 == null) {
                return;
            }
            check(vec2.canonicalPlanContent().indexOf(
                    "\"name\":\"x\"")
                    < vec2.canonicalPlanContent().indexOf(
                        "\"name\":\"y\""),
                "the C-struct plan keeps class source order (x before"
                    + " y)");
            check(vec2.completedPlan().orderedFields().get(0)
                    .defaultExpression().canonicalSemanticContent()
                    .contains("\"literalValue\":0x1.8p0"),
                "the C-struct default serializes its exact IEEE-754"
                    + " literal (1.5 as the unique hex float)");
            DefaultSemanticSerializer.SerializedDefaultClass uses =
                compile.serializedOf("main.deal", "Uses");
            check(uses != null, "Uses has a serialized plan");
            if (uses == null) {
                return;
            }
            ResolvedDefaultExpression v = uses.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(v.runtimeResources().size() == 1
                    && v.runtimeResources().iterator().next()
                        .providerContractDigest()
                        .equals(vec2.planDigest()),
                "the imported C-struct class literal completes with the"
                    + " declaration-module plan digest");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Out-of-root class-free provider (leaf verification with E2 output)
    // =========================================================================

    private static void testOutOfRootProvider() throws Exception {
        System.out.println("-- Out-of-root class-free provider"
            + " serialization (leaf verification) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as S from "../shared"

                class Rooted {
                  g: int = S.scale(2);
                }

                export function main(): null {
                  return null;
                }
                """,
            "shared.deal", """
                export function scale(v: int): int {
                  return v * 2;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the out-of-root fixture compiles: " + compile.diagnostics);
            DefaultSemanticSerializer.Result result = compile.serialize();
            check(!result.hasErrors(),
                "the serializer accepts the out-of-root provider: "
                    + result.diagnostics());
            String scaleDigest = compile.providerDigestOf("shared.deal",
                "scale");
            check(isSha256Hex(scaleDigest),
                "the out-of-root provider function receives a real"
                    + " digest");
            DefaultSemanticSerializer.SerializedDefaultClass rooted =
                compile.serializedOf("main.deal", "Rooted");
            ResolvedDefaultExpression g = rooted.completedPlan()
                .orderedFields().get(0).defaultExpression();
            check(g.runtimeResources().size() == 1
                    && g.runtimeResources().iterator().next()
                        .providerContractDigest().equals(scaleDigest),
                "the out-of-root provider reference completes with the"
                    + " provider digest");
            check(g.canonicalSemanticContent().contains(scaleDigest),
                "the canonical target embeds the out-of-root provider"
                    + " digest");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Cyclic-path contract: reentrant digest demand fails closed
    // =========================================================================

    private static final ProjectDeploymentIdentity DEPLOYMENT =
        new ProjectDeploymentIdentity("file:///proj/deal.json",
            "a".repeat(64));

    private static final SemanticModuleIdentity MODULE_A =
        new SemanticModuleIdentity(DEPLOYMENT,
            "file:///proj/src/main.deal");

    private static final SemanticModuleIdentity MODULE_B =
        new SemanticModuleIdentity(DEPLOYMENT,
            "file:///proj/src/lib.deal");

    private static final CanonicalClassIdentity IDENTITY_A =
        new CanonicalClassIdentity(
            new CanonicalModuleIdentity.ProjectModule(
                new ProjectModuleIdentity("src", "/proj/src",
                    List.of())),
            "A");

    private static final CanonicalClassIdentity IDENTITY_B =
        new CanonicalClassIdentity(
            new CanonicalModuleIdentity.ProjectModule(
                new ProjectModuleIdentity("src", "/proj/src",
                    List.of())),
            "B");

    private static final CanonicalClassIdentity IDENTITY_R =
        new CanonicalClassIdentity(
            new CanonicalModuleIdentity.ProjectModule(
                new ProjectModuleIdentity("src", "/proj/src",
                    List.of())),
            "R");

    private static final Type TYPE_A = Types.classType("A", IDENTITY_A);
    private static final Type TYPE_B = Types.classType("B", IDENTITY_B);

    private static final SourceModuleLocation LOCATION_A =
        new SourceModuleLocation("/proj/src/main.deal", MODULE_A,
            "ma", null,
            new CanonicalModuleIdentity.ProjectModule(
                new ProjectModuleIdentity("src", "/proj/src",
                    List.of())));

    private static final SourceModuleLocation LOCATION_B =
        new SourceModuleLocation("/proj/src/lib.deal", MODULE_B,
            "mb", null,
            new CanonicalModuleIdentity.ProjectModule(
                new ProjectModuleIdentity("src", "/proj/src",
                    List.of())));

    /** Parses a tiny program through the real lexer/parser. */
    private static ProgramNode parseProgram(String source) {
        LexResult lex = new Lexer(source, "synthetic.deal").tokenize();
        check(!lex.hasErrors(), "synthetic fixture lexes: "
            + lex.diagnostics());
        ParseResult parse = new Parser(lex.tokens(), "synthetic.deal",
            lex.directiveEvents()).parse();
        check(!parse.hasErrors(), "synthetic fixture parses: "
            + parse.diagnostics());
        return parse.program();
    }

    /** The top-level class declaration of a parsed program. */
    private static ClassDeclaration classOf(ProgramNode program,
                                            String name) {
        for (StatementNode stmt : program.statements()) {
            if (stmt instanceof ClassDeclaration cd
                    && cd.name().equals(name)) {
                return cd;
            }
        }
        check(false, "synthetic fixture declares class " + name);
        return null;
    }

    /** A canonical class-identity index over the synthetic
     * classes. */
    private static CanonicalClassIdentityIndex indexOf(
            Map<CanonicalClassIdentity, String> texts) {
        return new CanonicalClassIdentityIndex() {
            @Override
            public String descriptorTextFor(
                    CanonicalClassIdentity identity) {
                String text = texts.get(identity);
                if (text == null) {
                    throw new IllegalStateException("unregistered");
                }
                return text;
            }

            @Override
            public CanonicalClassIdentity identityForDescriptorText(
                    String descriptorText) {
                for (Map.Entry<CanonicalClassIdentity, String> entry
                        : texts.entrySet()) {
                    if (entry.getValue().equals(descriptorText)) {
                        return entry.getKey();
                    }
                }
                throw new IllegalStateException("unregistered");
            }
        };
    }

    /** An empty-but-valid checked-facts snapshot carrying the given
     * class's recorded declaration scope (the serializer's
     * declaration-scope seam). */
    private static CheckResult checkResultFor(ClassDeclaration cd) {
        return new CheckResult(Map.of(), new SymbolTable(), Map.of(),
            List.of(), Map.of(cd, new SymbolTable()));
    }

    private static void testReentrantGuardFailsClosed() throws Exception {
        System.out.println("-- Reentrant digest demand fails closed"
            + " (never a hang, never a placeholder) --");
        ProgramNode programA = parseProgram(
            "import * as L from \"./lib\"\n"
                + "class A { b: L.B = {}; }\n");
        ProgramNode programB = parseProgram(
            "import * as M from \"./main\"\n"
                + "class B { a: M.A = {}; }\n");
        ClassDeclaration cdA = classOf(programA, "A");
        ClassDeclaration cdB = classOf(programB, "B");
        if (cdA == null || cdB == null) {
            return;
        }
        DiagnosticRange aLiteralRange = cdA.fields().get(0)
            .defaultExpr().orElseThrow().span().range();
        DiagnosticRange bLiteralRange = cdB.fields().get(0)
            .defaultExpr().orElseThrow().span().range();

        SemanticResourceIdentity resourceB = new SemanticResourceIdentity(
            MODULE_B, LexicalDeclarationIdentity.DeclarationKind.CLASS,
            new LexicalDeclarationIdentity(
                LexicalDeclarationIdentity.DeclarationKind.CLASS, "B",
                "src.lib", cdB.span().range()));
        SemanticResourceIdentity resourceA = new SemanticResourceIdentity(
            MODULE_A, LexicalDeclarationIdentity.DeclarationKind.CLASS,
            new LexicalDeclarationIdentity(
                LexicalDeclarationIdentity.DeclarationKind.CLASS, "A",
                "src.main", cdA.span().range()));

        DefaultIrNode rootA = new DefaultIrNode(
            DefaultIrNode.NodeKind.OBJECT_LITERAL, null, TYPE_B,
            List.of(TYPE_B), List.of(), null,
            DefaultIrNode.Target.importedResource("B", resourceB),
            null, null, null, aLiteralRange);
        DefaultIrNode rootB = new DefaultIrNode(
            DefaultIrNode.NodeKind.OBJECT_LITERAL, null, TYPE_A,
            List.of(TYPE_A), List.of(), null,
            DefaultIrNode.Target.importedResource("A", resourceA),
            null, null, null, bLiteralRange);

        ResolvedDefaultExpression exprA = new ResolvedDefaultExpression(
            cdA.fields().get(0).defaultExpr().orElseThrow(), TYPE_B,
            aLiteralRange,
            new deal.module.DefaultDeclaringContext(MODULE_A, Map.of()),
            Map.of(), rootA, null, null, java.util.Set.of());
        ResolvedDefaultExpression exprB = new ResolvedDefaultExpression(
            cdB.fields().get(0).defaultExpr().orElseThrow(), TYPE_A,
            bLiteralRange,
            new deal.module.DefaultDeclaringContext(MODULE_B, Map.of()),
            Map.of(), rootB, null, null, java.util.Set.of());

        CompilerClassDefaultPlan planA = new CompilerClassDefaultPlan(
            IDENTITY_A, MODULE_A,
            List.of(new CompilerClassDefaultEntry("b", TYPE_B,
                "@src/B", false, exprA)),
            java.util.Set.of());
        CompilerClassDefaultPlan planB = new CompilerClassDefaultPlan(
            IDENTITY_B, MODULE_B,
            List.of(new CompilerClassDefaultEntry("a", TYPE_A,
                "@src/A", false, exprB)),
            java.util.Set.of());

        PlannedDefaultClass plannedA = new PlannedDefaultClass(planA,
            cdA, List.of(new DefaultResourceOccurrence(
                RuntimeResourceReference.Kind
                    .IMPORTED_CLASS_DEFAULT_PLAN,
                MODULE_A, MODULE_B, "L", resourceB, aLiteralRange)));
        PlannedDefaultClass plannedB = new PlannedDefaultClass(planB,
            cdB, List.of(new DefaultResourceOccurrence(
                RuntimeResourceReference.Kind
                    .IMPORTED_CLASS_DEFAULT_PLAN,
                MODULE_B, MODULE_A, "M", resourceA, bLiteralRange)));

        Map<CanonicalClassIdentity, String> texts = new HashMap<>();
        texts.put(IDENTITY_A, "@src/A");
        texts.put(IDENTITY_B, "@src/B");
        CanonicalRuntimeTypeDescriptor descriptors =
            new CanonicalRuntimeTypeDescriptor(indexOf(texts));
        Map<String, CanonicalModuleIdentity> classification = Map.of();

        DefaultSerializerModuleInput inputA =
            new DefaultSerializerModuleInput(
                "/proj/src/main.deal", "src.main", programA, LOCATION_A,
                checkResultFor(cdA),
                new NameResolver("src.main", new StubModuleResolver()),
                Map.of(), Map.of(), descriptors, classification, null,
                false, false);
        DefaultSerializerModuleInput inputB =
            new DefaultSerializerModuleInput(
                "/proj/src/lib.deal", "src.lib", programB, LOCATION_B,
                checkResultFor(cdB),
                new NameResolver("src.lib", new StubModuleResolver()),
                Map.of(), Map.of(), descriptors, classification, null,
                false, false);

        Map<String, List<PlannedDefaultClass>> planned = Map.of(
            "/proj/src/main.deal", List.of(plannedA),
            "/proj/src/lib.deal", List.of(plannedB));
        long before = System.nanoTime();
        DefaultSemanticSerializer.Result result =
            DefaultSemanticSerializer.serialize(
                Map.of("/proj/src/main.deal", inputA,
                    "/proj/src/lib.deal", inputB),
                planned);
        long elapsedMillis = (System.nanoTime() - before) / 1_000_000;
        check(result.hasErrors()
                && result.serializedClasses().isEmpty()
                && result.providerDigests().isEmpty(),
            "reentrant digest demand fails closed with a deterministic"
                + " error and publishes nothing: " + result.diagnostics());
        check(result.diagnostics().get(0).code().equals("E6005")
                && result.diagnostics().get(0).message().contains(
                    "reentrant provider digest demand"),
            "the reentrant guard reports E6005 with the canonical"
                + " reentrant message, got " + result.diagnostics());
        check(elapsedMillis < 10_000,
            "the reentrant guard terminates (never a hang): "
                + elapsedMillis + " ms");
    }

    // =========================================================================
    // Broken E2 occurrence data fails closed
    // =========================================================================

    private static void testBrokenOccurrenceFailsClosed()
            throws Exception {
        System.out.println("-- Broken E2 occurrence data fails closed"
            + " (kind, identity, range) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                import * as L from "./lib"

                class Outer {
                  b: L.Rec = {};
                }

                export function main(): null {
                  return null;
                }
                """,
            "src/lib.deal", """
                export class Rec {
                  tag: int = 0;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the broken-occurrence fixture compiles: "
                    + compile.diagnostics);
            PlannedDefaultClass planned = null;
            String sourcePath = null;
            for (Map.Entry<String, List<PlannedDefaultClass>> entry
                    : compile.orchestrator.plannedDefaultClasses()
                        .entrySet()) {
                if (entry.getKey().endsWith("main.deal")
                        && entry.getValue().size() == 1) {
                    planned = entry.getValue().get(0);
                    sourcePath = entry.getKey();
                }
            }
            check(planned != null && planned.occurrences().size() == 1,
                "the fixture produced one occurrence");
            if (planned == null) {
                return;
            }
            Map<String, DefaultSerializerModuleInput> inputs =
                compile.orchestrator.defaultSerializerModuleInputs();

            DefaultResourceOccurrence occurrence = planned.occurrences()
                .get(0);
            DefaultResourceOccurrence wrongKind =
                new DefaultResourceOccurrence(
                    RuntimeResourceReference.Kind
                        .IMPORTED_FUNCTION_WRAPPER,
                    occurrence.fromSemanticModuleIdentity(),
                    occurrence.toSemanticModuleIdentity(),
                    occurrence.importAlias(),
                    occurrence.semanticResourceIdentity(),
                    occurrence.sourceRange());
            Map<String, List<PlannedDefaultClass>> allPlanned =
                compile.orchestrator.plannedDefaultClasses();
            check(failsClosed(inputs, allPlanned, sourcePath, planned,
                    wrongKind),
                "a broken occurrence kind fails closed");

            SemanticResourceIdentity wrongIdentity =
                new SemanticResourceIdentity(
                    occurrence.semanticResourceIdentity()
                        .semanticModuleIdentity(),
                    LexicalDeclarationIdentity.DeclarationKind.CLASS,
                    new LexicalDeclarationIdentity(
                        LexicalDeclarationIdentity.DeclarationKind.CLASS,
                        "Ghost",
                        occurrence.semanticResourceIdentity()
                            .lexicalDeclarationIdentity()
                            .enclosingLexicalDeclarationPath(),
                        occurrence.semanticResourceIdentity()
                            .lexicalDeclarationIdentity()
                            .sourceScalarRange()));
            DefaultResourceOccurrence wrongIdentityOccurrence =
                new DefaultResourceOccurrence(occurrence.kind(),
                    occurrence.fromSemanticModuleIdentity(),
                    occurrence.toSemanticModuleIdentity(),
                    occurrence.importAlias(), wrongIdentity,
                    occurrence.sourceRange());
            check(failsClosed(inputs, allPlanned, sourcePath,
                    planned, wrongIdentityOccurrence),
                "a broken occurrence identity fails closed");

            DiagnosticRange shifted = new DiagnosticRange(
                occurrence.sourceRange().file(),
                occurrence.sourceRange().startLine() + 5,
                occurrence.sourceRange().startColumn(),
                occurrence.sourceRange().endLine() + 5,
                occurrence.sourceRange().endColumn(),
                occurrence.sourceRange().startScalarOffset() + 5,
                occurrence.sourceRange().endScalarOffset() + 5,
                occurrence.sourceRange().scalarLength(),
                occurrence.sourceRange().origin());
            DefaultResourceOccurrence wrongRange =
                new DefaultResourceOccurrence(occurrence.kind(),
                    occurrence.fromSemanticModuleIdentity(),
                    occurrence.toSemanticModuleIdentity(),
                    occurrence.importAlias(),
                    occurrence.semanticResourceIdentity(), shifted);
            check(failsClosed(inputs, allPlanned, sourcePath,
                    planned, wrongRange),
                "a broken occurrence range fails closed");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    private static boolean failsClosed(
            Map<String, DefaultSerializerModuleInput> inputs,
            Map<String, List<PlannedDefaultClass>> allPlanned,
            String sourcePath, PlannedDefaultClass planned,
            DefaultResourceOccurrence corrupted) {
        // The full orchestrator planned map with the tested module's
        // classes replaced: the serializer's digest demand resolves
        // provider plans through the map, so the map must stay
        // complete while only the tested occurrence record is
        // corrupted.
        PlannedDefaultClass broken = new PlannedDefaultClass(
            planned.plan(), planned.declaration(), List.of(corrupted));
        Map<String, List<PlannedDefaultClass>> plannedMap =
            new LinkedHashMap<>();
        for (Map.Entry<String, List<PlannedDefaultClass>> entry
                : allPlanned.entrySet()) {
            plannedMap.put(entry.getKey(),
                entry.getKey().equals(sourcePath)
                    ? List.of(broken) : entry.getValue());
        }
        DefaultSemanticSerializer.Result result =
            DefaultSemanticSerializer.serialize(inputs, plannedMap);
        boolean ok = result.hasErrors()
            && result.serializedClasses().isEmpty()
            && result.diagnostics().get(0).code().equals("E6005")
            && result.diagnostics().get(0).message().contains(
                "broken occurrence data");
        if (!ok) {
            System.err.println("    failsClosed diagnostics: "
                + result.diagnostics());
        }
        return ok;
    }

    // =========================================================================
    // Non-behavior-affecting range changes change nothing
    // =========================================================================

    private static void testNonBehaviorAffectingRangeIgnored()
            throws Exception {
        System.out.println("-- Non-behavior-affecting range changes"
            + " change nothing --");
        ProgramNode program = parseProgram(
            "class R { x: int = 1 + 2; }\n");
        ClassDeclaration cd = classOf(program, "R");
        if (cd == null) {
            return;
        }
        deal.ast.ExpressionNode defaultAst = cd.fields().get(0)
            .defaultExpr().orElseThrow();
        DiagnosticRange rootRange = defaultAst.span().range();

        Map<CanonicalClassIdentity, String> texts = new HashMap<>();
        texts.put(IDENTITY_R, "@src/R");
        CanonicalRuntimeTypeDescriptor descriptors =
            new CanonicalRuntimeTypeDescriptor(indexOf(texts));

        String contentWithSpans =
            serializeSpanVariant(program, cd, descriptors, rootRange,
                new DiagnosticRange("synthetic.deal", 1, 3, 1, 4, 8, 9,
                    1, RangeOrigin.SOURCE),
                new DiagnosticRange("synthetic.deal", 1, 7, 1, 8, 12,
                    13, 1, RangeOrigin.SOURCE));
        String contentWithShiftedSpans =
            serializeSpanVariant(program, cd, descriptors, rootRange,
                new DiagnosticRange("synthetic.deal", 4, 3, 4, 4, 19,
                    20, 1, RangeOrigin.SOURCE),
                new DiagnosticRange("synthetic.deal", 4, 7, 4, 8, 23,
                    24, 1, RangeOrigin.SOURCE));
        check(contentWithSpans != null
                && contentWithSpans.equals(contentWithShiftedSpans),
            "shifting only non-root, non-reference node spans changes"
                + " the canonical content not at all");
        check(contentWithSpans.contains("\"sourceRange\"")
                && contentWithSpans.contains("\"startLine\":1"),
            "the root range is the only serialized range here (the"
                + " default expression anchor)");
    }

    /** Serializes a synthetic class R whose binary operand spans are
     * the given literal spans. */
    private static String serializeSpanVariant(ProgramNode program,
            ClassDeclaration cd,
            CanonicalRuntimeTypeDescriptor descriptors,
            DiagnosticRange rootRange, DiagnosticRange leftSpan,
            DiagnosticRange rightSpan) {
        DefaultIrNode left = new DefaultIrNode(
            DefaultIrNode.NodeKind.LITERAL, null, Type.Int.INSTANCE,
            List.of(), List.of(), new LiteralValue.IntLiteral(1), null,
            null, null, null, leftSpan);
        DefaultIrNode right = new DefaultIrNode(
            DefaultIrNode.NodeKind.LITERAL, null, Type.Int.INSTANCE,
            List.of(), List.of(), new LiteralValue.IntLiteral(2), null,
            null, null, null, rightSpan);
        DefaultIrNode root = new DefaultIrNode(
            DefaultIrNode.NodeKind.BINARY, "ADD", Type.Int.INSTANCE,
            List.of(Type.Int.INSTANCE), List.of(left, right), null, null,
            null, null, null, rootRange);
        ResolvedDefaultExpression expr = new ResolvedDefaultExpression(
            cd.fields().get(0).defaultExpr().orElseThrow(),
            Type.Int.INSTANCE, rootRange,
            new deal.module.DefaultDeclaringContext(MODULE_A, Map.of()),
            Map.of(), root, null, null, java.util.Set.of());
        CompilerClassDefaultPlan plan = new CompilerClassDefaultPlan(
            IDENTITY_R, MODULE_A,
            List.of(new CompilerClassDefaultEntry("x",
                Type.Int.INSTANCE, "int", false, expr)),
            java.util.Set.of());
        PlannedDefaultClass planned = new PlannedDefaultClass(plan, cd,
            List.of());
        DefaultSerializerModuleInput input =
            new DefaultSerializerModuleInput(
                "/proj/src/main.deal", "src.main", program, LOCATION_A,
                checkResultFor(cd),
                new NameResolver("src.main", new StubModuleResolver()),
                Map.of(), Map.of(), descriptors, Map.of(), null, false,
                false);
        DefaultSemanticSerializer.Result result =
            DefaultSemanticSerializer.serialize(
                Map.of("/proj/src/main.deal", input),
                Map.of("/proj/src/main.deal", List.of(planned)));
        if (result.hasErrors()) {
            check(false, "the span variant serializes: "
                + result.diagnostics());
            return null;
        }
        return result.serializedClasses().get("/proj/src/main.deal")
            .get(0).completedPlan().orderedFields().get(0)
            .defaultExpression().canonicalSemanticContent();
    }

    // =========================================================================
    // Equality by full content; digests as indexes
    // =========================================================================

    private static final Map<String, String> EQUALITY_FILES = Map.of(
        "deal.json", MANIFEST,
        "src/main.deal", """
            class Eq {
              x: int = 1;
              z: int = 2;
            }

            export function main(): null {
              return null;
            }
            """);

    private static void testEqualityByFullContent() throws Exception {
        System.out.println("-- Equality by full content; digests as"
            + " indexes --");
        Compile compile = new Compile(EQUALITY_FILES, "src/main.deal");
        try {
            check(compile.success,
                "the equality fixture compiles: " + compile.diagnostics);
            DefaultSemanticSerializer.SerializedDefaultClass eq =
                compile.serializedOf("main.deal", "Eq");
            String xContent = eq.completedPlan().orderedFields().get(0)
                .defaultExpression().canonicalSemanticContent();
            String zContent = eq.completedPlan().orderedFields().get(1)
                .defaultExpression().canonicalSemanticContent();
            String xDigest = eq.completedPlan().orderedFields().get(0)
                .defaultExpression().semanticDigest();
            check(!xContent.equals(zContent),
                "different defaults serialize to different full"
                    + " content");
            check(xDigest.equals(digestOf(xContent)),
                "the semantic digest derives from the full content");
            check(!xDigest.equals(eq.completedPlan().orderedFields()
                    .get(1).defaultExpression().semanticDigest()),
                "digests index content (unequal content &rarr;"
                    + " unequal digest)");
            // Cross-run equality: an identical recompile over the same
            // root reproduces byte-identical content and digests.
            Compile again = compile.recompile(EQUALITY_FILES);
            check(again.serializedOf("main.deal", "Eq")
                    .completedPlan().orderedFields().get(0)
                    .defaultExpression().canonicalSemanticContent()
                    .equals(xContent),
                "an identical recompile reproduces byte-identical"
                    + " canonical content (full-content equality across"
                    + " runs)");
            check(again.serializedOf("main.deal", "Eq")
                    .completedPlan().orderedFields().get(0)
                    .defaultExpression().semanticDigest()
                    .equals(xDigest),
                "an identical recompile reproduces the identical"
                    + " digest (index stability)");
        } finally {
            deleteRecursively(compile.root);
        }
    }
}
