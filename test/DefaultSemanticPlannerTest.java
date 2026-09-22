package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.identity.CanonicalClassIdentity;
import deal.module.CompilationOrchestrator;
import deal.module.CompilerClassDefaultEntry;
import deal.module.CompilerClassDefaultPlan;
import deal.module.DefaultResourceOccurrence;
import deal.module.PlannedDefaultClass;
import deal.module.ResolvedDefaultExpression;
import deal.project.ProjectContext;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;

import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The planner-level verification battery of ISSUE-0541 (design source
 * {@code provider-versioned-default-plans} Verification 1; the
 * task-pinned acceptance criteria): the shared default planning
 * pipeline — {@code DefaultSemanticPlanner} for implementation classes
 * and {@code DeclarationSemanticAnalyzer} for declaration/C-struct
 * classes — exercised through the real orchestrator path
 * ({@link ProjectLocator} → the production
 * {@link CompilationOrchestrator} constructor → {@code compile()}) over
 * real scratch-project fixtures, inspecting the produced
 * {@link CompilerClassDefaultPlan}s and the provisional
 * {@link DefaultResourceOccurrence} data — not isolated API calls.
 *
 * <p>Covered:</p>
 * <ol>
 *   <li>Epic criterion 1 at the plan level: same-module and imported
 *       calls, imported class plans, contextual class literals
 *       (including a literal nested in a call nested in an array, and a
 *       literal nested in a literal field), out-of-root class-free
 *       providers, and type-only references — with source order of
 *       {@code orderedFields} and first-IR-walk-occurrence order plus
 *       deduplication by semantic resource identity on the provisional
 *       occurrence records (kind, from/to semantic module identities,
 *       import alias, semantic resource identity, reference range — and
 *       no digest field).</li>
 *   <li>The E4001 declaration-shape gate at the field declaration range
 *       for implementation and C-struct classes; host-declared classes
 *       exempt (the host defaults seam keeps compiling).</li>
 *   <li>The E3020 sync gate at the await range for evaluator-scope
 *       await — including a class declared inside an async function
 *       body; await inside a nested async function-expression body
 *       compiles.</li>
 *   <li>E3001 at the default expression range through the real
 *       pipeline (implementation default via the checker; C-struct
 *       default via the declaration analyzer's checker).</li>
 *   <li>Zero evaluator invocation, zero library loading, no digest
 *       computation and no final-edge construction: plans carry empty
 *       {@code runtimeDependencies}, expressions carry null canonical
 *       content/digest and empty {@code runtimeResources}, and the
 *       occurrence record has no digest component.</li>
 * </ol>
 */
public class DefaultSemanticPlannerTest {

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

    private static Path write(Path root, String rel, String content)
            throws Exception {
        Path file = root.resolve(rel);
        Files.createDirectories(file.getParent());
        Files.writeString(file, content);
        return file.toAbsolutePath();
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
     * item 3): the suite's subject — the default-class planning phase —
     * is arm-independent, and the fixtures keep the harness arm's
     * retained artifact behavior.
     */
    private static CompilerInvocation invocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
    }

    /** One in-process production compile over a scratch project. */
    private static final class Compile {
        final Path root;
        final Path entry;
        final CompilationOrchestrator orchestrator;
        final boolean success;
        final List<CompilerDiagnostic> diagnostics;

        Compile(Map<String, String> files, String entryRel)
                throws Exception {
            root = Files.createTempDirectory("deal_plan_");
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

        /** The planned classes of the module whose path ends with the
         * given suffix, or an empty list. */
        List<PlannedDefaultClass> plannedFor(String sourceSuffix) {
            for (Map.Entry<String, List<PlannedDefaultClass>> entry
                    : orchestrator.plannedDefaultClasses().entrySet()) {
                if (entry.getKey().endsWith(sourceSuffix)) {
                    return entry.getValue();
                }
            }
            return List.of();
        }

        /** The plan of the class with the given simple name in the given
         * module (path suffix), or null. */
        CompilerClassDefaultPlan planOf(String sourceSuffix,
                                        String className) {
            for (PlannedDefaultClass planned : plannedFor(sourceSuffix)) {
                if (planned.plan().classIdentity().className()
                        .equals(className)) {
                    return planned.plan();
                }
            }
            return null;
        }

        PlannedDefaultClass plannedOf(String sourceSuffix,
                                      String className) {
            for (PlannedDefaultClass planned : plannedFor(sourceSuffix)) {
                if (planned.plan().classIdentity().className()
                        .equals(className)) {
                    return planned;
                }
            }
            return null;
        }

        CompilerDiagnostic errorOf(String code) {
            return diagnostics.stream()
                .filter(d -> "error".equals(d.severity())
                    && code.equals(d.code()))
                .findFirst().orElse(null);
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

    public static void main(String[] args) throws Exception {
        testOccurrenceRecordShape();
        testPlanShapeAndResolutionThroughOrchestrator();
        testE4001ImplementationClass();
        testE4001CStructClass();
        testHostDeclaredExemption();
        testE3020EvaluatorScopeAwaitInAsyncBody();
        testE3020AwaitInsideAsyncFunctionExpressionCompiles();
        testE3001DefaultRange();
        testDeterminism();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.err.println("DefaultSemanticPlannerTest FAILED: "
                + failed + " failure(s)");
            System.exit(1);
        }
    }

    // =========================================================================
    // The provisional occurrence record shape: no digest field
    // =========================================================================

    private static void testOccurrenceRecordShape() {
        System.out.println("-- DefaultResourceOccurrence shape --");
        List<String> components = new ArrayList<>();
        for (RecordComponent component
                : DefaultResourceOccurrence.class.getRecordComponents()) {
            components.add(component.getName());
        }
        check(components.equals(List.of("kind", "fromSemanticModuleIdentity",
                "toSemanticModuleIdentity", "importAlias",
                "semanticResourceIdentity", "sourceRange")),
            "DefaultResourceOccurrence components are (kind, from, to,"
                + " importAlias, semanticResourceIdentity, sourceRange),"
                + " got " + components);
        check(!components.contains("providerContractDigest")
                && !components.contains("digest"),
            "the provisional occurrence record carries no digest component");
        List<String> plannedComponents = new ArrayList<>();
        for (RecordComponent component
                : PlannedDefaultClass.class.getRecordComponents()) {
            plannedComponents.add(component.getName());
        }
        check(plannedComponents.equals(List.of("plan", "declaration",
                "occurrences")),
            "PlannedDefaultClass components are (plan, declaration,"
                + " occurrences), got " + plannedComponents);
    }

    // =========================================================================
    // Epic criterion 1 at the plan level (the real orchestrator path)
    // =========================================================================

    private static void testPlanShapeAndResolutionThroughOrchestrator()
            throws Exception {
        System.out.println("-- Plan shape, resolution, and provisional"
            + " occurrences (real orchestrator path) --");
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
                "the planning fixture compiles: " + compile.diagnostics);

            // ---- The Outer plan: source-ordered entries ----
            CompilerClassDefaultPlan outer = compile.planOf("main.deal",
                "Outer");
            check(outer != null, "Outer has a compiler default plan");
            if (outer == null) {
                return;
            }
            check(outer.orderedFields().stream()
                    .map(CompilerClassDefaultEntry::name).toList()
                    .equals(List.of("a", "b", "c", "d", "e", "f", "g", "h")),
                "Outer orderedFields are in class source order, got "
                    + outer.orderedFields().stream()
                        .map(CompilerClassDefaultEntry::name).toList());
            check(outer.orderedFields().get(0).resolvedFieldType()
                        == deal.types.Type.Int.INSTANCE
                    && "int".equals(
                        outer.orderedFields().get(0).runtimeTypeDescriptor()),
                "field a: int descriptor 'int'");
            check("@src/Rec".equals(
                    outer.orderedFields().get(1).runtimeTypeDescriptor()),
                "field b: imported class descriptor '@src/Rec', got "
                    + outer.orderedFields().get(1).runtimeTypeDescriptor());
            check("[@src/Rec]".equals(
                    outer.orderedFields().get(2).runtimeTypeDescriptor()),
                "field c: imported class array descriptor '[@src/Rec]', got "
                    + outer.orderedFields().get(2).runtimeTypeDescriptor());
            check(outer.orderedFields().stream()
                    .allMatch(e -> !e.optional()
                        && e.defaultExpression() != null),
                "every required-present Outer entry carries a default"
                    + " expression");
            check(outer.runtimeDependencies().isEmpty(),
                "the plan carries empty runtimeDependencies (no"
                    + " RuntimeImportDependency was constructed)");
            check(outer.declaringSemanticModuleIdentity()
                    .canonicalResolvedSourceUri()
                    .endsWith("src/main.deal"),
                "the plan carries the declaring module's semantic identity");

            // ---- Resolved default facts: same-module binding ----
            ResolvedDefaultExpression a = outer.orderedFields().get(0)
                .defaultExpression();
            check(a.resolvedBindings().containsKey("localHelper"),
                "the same-module call records the callee in"
                    + " resolvedBindings");
            check(a.resolvedBindings().get("localHelper")
                        instanceof deal.checker.Symbol.FunctionSymbol,
                "the same-module binding is the checker's FunctionSymbol");
            check(a.canonicalSemanticContent() == null
                    && a.semanticDigest() == null
                    && a.runtimeResources().isEmpty(),
                "the default expression stays pre-serializer (null"
                    + " canonical content/digest, empty runtimeResources)");
            check(a.semanticIr() instanceof deal.module.TypedEvaluatorIr,
                "the default expression carries typed evaluator IR");

            // ---- Provisional occurrences: order, dedup, ranges ----
            PlannedDefaultClass outerPlanned = compile.plannedOf("main.deal",
                "Outer");
            List<DefaultResourceOccurrence> occurrences =
                outerPlanned.occurrences();
            check(occurrences.size() == 4,
                "exactly four occurrences (Rec plan, makeRec call, getTag"
                    + " call, scale call), got " + occurrences.size()
                    + ": " + occurrences);
            if (occurrences.size() != 4) {
                return;
            }
            DefaultResourceOccurrence plan = occurrences.get(0);
            check(plan.kind().name().equals("IMPORTED_CLASS_DEFAULT_PLAN"),
                "first occurrence is the imported class default plan, got "
                    + plan.kind());
            check(plan.importAlias().equals("L"),
                "the class plan occurrence carries alias 'L', got "
                    + plan.importAlias());
            check(plan.toSemanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith("src/lib.deal"),
                "the class plan occurrence targets the lib module");
            check(plan.semanticResourceIdentity().resourceKind().name()
                        .equals("CLASS")
                    && "Rec".equals(plan.semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "the class plan occurrence carries the Rec resource"
                    + " identity");
            check(plan.sourceRange().startLine() == 6
                    && plan.sourceRange().startColumn() == 14,
                "the class plan occurrence keeps the FIRST literal range"
                    + " (field b's '{}' at line 6 column 14), got "
                    + plan.sourceRange().startLine() + ":"
                    + plan.sourceRange().startColumn());

            DefaultResourceOccurrence makeRec = occurrences.get(1);
            check(makeRec.kind().name().equals("IMPORTED_FUNCTION_WRAPPER")
                    && "makeRec".equals(makeRec.semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "second occurrence is the imported makeRec wrapper");
            check(makeRec.sourceRange().startLine() == 7,
                "the makeRec wrapper records the call-site range"
                    + " (line 7), got " + makeRec.sourceRange().startLine());

            DefaultResourceOccurrence getTag = occurrences.get(2);
            check(getTag.kind().name().equals("IMPORTED_FUNCTION_WRAPPER")
                    && "getTag".equals(getTag.semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "third occurrence is the imported getTag wrapper");
            check(getTag.sourceRange().startLine() == 10,
                "the getTag wrapper records the call-site range"
                    + " (line 10), got " + getTag.sourceRange().startLine());

            DefaultResourceOccurrence scale = occurrences.get(3);
            check(scale.kind().name().equals("IMPORTED_FUNCTION_WRAPPER")
                    && "scale".equals(scale.semanticResourceIdentity()
                        .lexicalDeclarationIdentity().declaredName()),
                "fourth occurrence is the imported scale wrapper of the"
                    + " class-free out-of-root provider");
            check(scale.importAlias().equals("S"),
                "the out-of-root occurrence carries alias 'S', got "
                    + scale.importAlias());
            check(scale.toSemanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith("shared.deal"),
                "the out-of-root occurrence targets the class-free"
                    + " provider module");
            check(scale.fromSemanticModuleIdentity()
                        .canonicalResolvedSourceUri().endsWith("src/main.deal"),
                "every occurrence records the consuming module identity");

            // Type-only references publish nothing: fields d and e carry
            // no occurrence and no imported target.
            ResolvedDefaultExpression d = outer.orderedFields().get(3)
                .defaultExpression();
            deal.module.DefaultIrNode dIr =
                (deal.module.DefaultIrNode) d.semanticIr();
            check(dIr.target() == null
                    && dIr.children().isEmpty(),
                "the empty array default publishes nothing (type-only)");
            ResolvedDefaultExpression e = outer.orderedFields().get(4)
                .defaultExpression();
            deal.module.DefaultIrNode eIr =
                (deal.module.DefaultIrNode) e.semanticIr();
            check(eIr.target() == null,
                "the null default publishes nothing (type-only)");

            // ---- The Rec plan in the provider module ----
            CompilerClassDefaultPlan rec = compile.planOf("lib.deal",
                "Rec");
            check(rec != null, "Rec has a compiler default plan");
            if (rec != null) {
                check(rec.orderedFields().stream()
                        .map(CompilerClassDefaultEntry::name).toList()
                        .equals(List.of("tag", "inner")),
                    "Rec orderedFields are source-ordered");
                ResolvedDefaultExpression inner = rec.orderedFields().get(1)
                    .defaultExpression();
                check(inner.resolvedBindings().containsKey("Rec"),
                    "the same-module contextual class literal records the"
                        + " class in resolvedBindings");
                check(compile.plannedOf("lib.deal", "Rec").occurrences()
                        .isEmpty(),
                    "the provider's own plan has no occurrences"
                        + " (same-module targets publish no edge)");
            }

            // ---- The class-free shared provider plans nothing ----
            check(compile.plannedFor("shared.deal").isEmpty(),
                "the class-free out-of-root provider plans no class");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // E4001: implementation class declaration shape
    // =========================================================================

    private static void testE4001ImplementationClass() throws Exception {
        System.out.println("-- E4001 at the field declaration range"
            + " (implementation class) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class Bad {
                  x: int;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(!compile.success, "the missing-default class fails the"
                + " compile");
            CompilerDiagnostic e4001 = compile.errorOf("E4001");
            check(e4001 != null,
                "E4001 fired, got " + compile.diagnostics);
            if (e4001 != null) {
                check(e4001.range().startLine() == 2
                        && e4001.range().startColumn() == 3,
                    "E4001 anchors the field declaration range (line 2"
                        + " column 3), got " + e4001.range().startLine()
                        + ":" + e4001.range().startColumn());
                check(e4001.message().contains(
                        "Class field without default is not valid"),
                    "E4001 carries the canonical message, got "
                        + e4001.message());
            }
            check(compile.orchestrator.plannedDefaultClasses().values()
                    .stream().allMatch(List::isEmpty),
                "failure publishes no plan");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // E4001: C-struct class declaration shape (declaration analyzer)
    // =========================================================================

    private static void testE4001CStructClass() throws Exception {
        System.out.println("-- E4001 at the field declaration range"
            + " (C-struct class) --");
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

                export function main(): null {
                  return null;
                }
                """,
            "bindings/ffi.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number = 0.0;
                  y: number;
                }

                export function length(v: Vec2): number;
                """), "src/main.deal");
        try {
            check(!compile.success, "the missing-default C-struct class"
                + " fails the compile");
            CompilerDiagnostic e4001 = compile.errorOf("E4001");
            check(e4001 != null,
                "E4001 fired for the C-struct class, got "
                    + compile.diagnostics);
            if (e4001 != null) {
                check(e4001.range().startLine() == 6
                        && e4001.range().startColumn() == 3,
                    "E4001 anchors the field declaration range (line 6"
                        + " column 3), got " + e4001.range().startLine()
                        + ":" + e4001.range().startColumn());
            }
            check(compile.errorOf("E7002") == null,
                "the FFI missing-default E7002 never fires (the planner"
                    + " gate precedes the FFI phase)");
            check(compile.orchestrator.plannedDefaultClasses().values()
                    .stream().allMatch(List::isEmpty),
                "failure publishes no plan");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Host-declared classes: exempt from the plan gates, no plan
    // =========================================================================

    private static void testHostDeclaredExemption() throws Exception {
        System.out.println("-- Host-declared classes stay exempt"
            + " (the host defaults seam) --");
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

                export function main(): null {
                  return null;
                }
                """,
            "bindings/cfg.d.deal", """
                export class Endpoint {
                  path: string;
                }

                export class ServerConfig {
                  port: int;
                  endpoint: Endpoint;
                }

                export function describe(c: ServerConfig): string;
                """), "src/main.deal");
        try {
            check(compile.success,
                "the host-declared required-no-default fields keep"
                    + " compiling, got " + compile.diagnostics);
            check(compile.errorOf("E4001") == null,
                "no E4001 for host-declared classes");
            check(compile.plannedFor("cfg.d.deal").isEmpty(),
                "host-declared classes produce no plan");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // E3020: evaluator-scope await (class inside an async function body)
    // =========================================================================

    private static void testE3020EvaluatorScopeAwaitInAsyncBody()
            throws Exception {
        System.out.println("-- E3020 at the await range (class declared"
            + " inside an async function body) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                async function build(): null {
                  class Inner {
                    x: int = await source();
                  }
                  return null;
                }

                async function source(): int {
                  return 3;
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(!compile.success, "the evaluator-scope await fails the"
                + " compile");
            CompilerDiagnostic e3020 = compile.errorOf("E3020");
            check(e3020 != null,
                "E3020 fired, got " + compile.diagnostics);
            if (e3020 != null) {
                check(e3020.range().startLine() == 3
                        && e3020.range().startColumn() == 14,
                    "E3020 anchors the await range (line 3 column 14),"
                        + " got " + e3020.range().startLine() + ":"
                        + e3020.range().startColumn());
                check(e3020.message().contains("'await' in class default"),
                    "E3020 carries the canonical message, got "
                        + e3020.message());
            }
            check(compile.errorOf("E3012") == null,
                "the checker's E3012 does not fire inside the async"
                    + " function body (the planner gate is the pinned"
                    + " rejection)");
            check(compile.orchestrator.plannedDefaultClasses().isEmpty(),
                "failure publishes no plan");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // E3020 negative: await inside a nested async function-expression body
    // =========================================================================

    private static void testE3020AwaitInsideAsyncFunctionExpressionCompiles()
            throws Exception {
        System.out.println("-- await inside a nested async"
            + " function-expression body compiles --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class Holder {
                  f: async () => int = async function(): int {
                    return await source();
                  };
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
                "the nested async function-expression body keeps"
                    + " compiling, got " + compile.diagnostics);
            check(compile.errorOf("E3020") == null,
                "no E3020 for await inside the nested async"
                    + " function-expression body");
            CompilerClassDefaultPlan holder = compile.planOf("main.deal",
                "Holder");
            check(holder != null, "Holder still receives its plan");
            if (holder != null) {
                ResolvedDefaultExpression f = holder.orderedFields().get(0)
                    .defaultExpression();
                check(((deal.module.DefaultIrNode) f.semanticIr())
                        .kind().name().equals("FUNCTION_EXPRESSION"),
                    "the default's IR root is the function expression");
            }
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // E3001 at the default expression range (both owners)
    // =========================================================================

    private static void testE3001DefaultRange() throws Exception {
        System.out.println("-- E3001 at the default expression range --");
        Compile implementation = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", """
                class Bad {
                  x: int = "oops";
                }

                export function main(): null {
                  return null;
                }
                """), "src/main.deal");
        try {
            check(!implementation.success,
                "the mismatched implementation default fails the compile");
            CompilerDiagnostic e3001 = implementation.errorOf("E3001");
            check(e3001 != null,
                "E3001 fired for the implementation default, got "
                    + implementation.diagnostics);
            if (e3001 != null) {
                check(e3001.range().startLine() == 2
                        && e3001.range().startColumn() == 12,
                    "E3001 anchors the default expression range (line 2"
                        + " column 12), got " + e3001.range().startLine()
                        + ":" + e3001.range().startColumn());
            }
        } finally {
            deleteRecursively(implementation.root);
        }

        Compile declaration = new Compile(Map.of(
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

                export function main(): null {
                  return null;
                }
                """,
            "bindings/ffi.d.deal", """
                // @extern-c

                // @c-struct
                export class Vec2 {
                  x: number = "oops";
                }

                export function length(v: Vec2): number;
                """), "src/main.deal");
        try {
            check(!declaration.success,
                "the mismatched C-struct default fails the compile");
            CompilerDiagnostic e3001 = declaration.errorOf("E3001");
            check(e3001 != null,
                "E3001 fired for the C-struct default (the declaration"
                    + " analyzer's checker), got " + declaration.diagnostics);
            if (e3001 != null) {
                check(e3001.range().startLine() == 5
                        && e3001.range().startColumn() == 15,
                    "E3001 anchors the default expression range (line 5"
                        + " column 15), got " + e3001.range().startLine()
                        + ":" + e3001.range().startColumn());
                check(e3001.message().contains(
                        "Default value type mismatch for field 'x'"),
                    "E3001 keeps the checker message identity, got "
                        + e3001.message());
            }
            check(declaration.orchestrator.plannedDefaultClasses().values()
                    .stream().allMatch(List::isEmpty),
                "failure publishes no plan");
        } finally {
            deleteRecursively(declaration.root);
        }
    }

    // =========================================================================
    // Determinism: byte-equal projects plan byte-equal plans
    // =========================================================================

    private static void testDeterminism() throws Exception {
        System.out.println("-- Deterministic planning across runs --");
        Map<String, String> files = Map.of(
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
                """);
        Path root = Files.createTempDirectory("deal_plan_det_");
        try {
            for (Map.Entry<String, String> file : files.entrySet()) {
                write(root, file.getKey(), file.getValue());
            }
            Path entry = root.resolve("src/main.deal");
            ProjectLocator.LocateResult located =
                ProjectLocator.locate(entry.toString(), null);
            CompilationOrchestrator first = new CompilationOrchestrator(
                located.context(), entry, false, false, false, false,
                null, invocation());
            boolean firstOk = first.compile();
            CompilationOrchestrator second = new CompilationOrchestrator(
                located.context(), entry, false, false, false, false,
                null, invocation());
            boolean secondOk = second.compile();
            check(firstOk && secondOk, "both compiles succeed");
            CompilerClassDefaultPlan firstPlan = null;
            CompilerClassDefaultPlan secondPlan = null;
            for (Map.Entry<String, List<PlannedDefaultClass>> entrySet
                    : first.plannedDefaultClasses().entrySet()) {
                if (entrySet.getKey().endsWith("main.deal")) {
                    for (PlannedDefaultClass planned : entrySet.getValue()) {
                        if (planned.plan().classIdentity().className()
                                .equals("Outer")) {
                            firstPlan = planned.plan();
                        }
                    }
                }
            }
            for (Map.Entry<String, List<PlannedDefaultClass>> entrySet
                    : second.plannedDefaultClasses().entrySet()) {
                if (entrySet.getKey().endsWith("main.deal")) {
                    for (PlannedDefaultClass planned : entrySet.getValue()) {
                        if (planned.plan().classIdentity().className()
                                .equals("Outer")) {
                            secondPlan = planned.plan();
                        }
                    }
                }
            }
            check(firstPlan != null && secondPlan != null,
                "both compiles produce the plan");
            if (firstPlan != null && secondPlan != null) {
                check(firstPlan.equals(secondPlan)
                        && firstPlan.orderedFields()
                            .equals(secondPlan.orderedFields()),
                    "byte-equal inputs produce equal plans");
                List<DefaultResourceOccurrence> firstOccurrences = null;
                List<DefaultResourceOccurrence> secondOccurrences = null;
                for (Map.Entry<String, List<PlannedDefaultClass>> entrySet
                        : first.plannedDefaultClasses().entrySet()) {
                    if (entrySet.getKey().endsWith("main.deal")) {
                        for (PlannedDefaultClass planned : entrySet.getValue()) {
                            if (planned.plan().classIdentity().className()
                                    .equals("Outer")) {
                                firstOccurrences = planned.occurrences();
                            }
                        }
                    }
                }
                for (Map.Entry<String, List<PlannedDefaultClass>> entrySet
                        : second.plannedDefaultClasses().entrySet()) {
                    if (entrySet.getKey().endsWith("main.deal")) {
                        for (PlannedDefaultClass planned : entrySet.getValue()) {
                            if (planned.plan().classIdentity().className()
                                    .equals("Outer")) {
                                secondOccurrences = planned.occurrences();
                            }
                        }
                    }
                }
                check(firstOccurrences != null
                        && firstOccurrences.equals(secondOccurrences),
                    "byte-equal inputs produce equal occurrence records");
            }
        } finally {
            deleteRecursively(root);
        }
    }
}
