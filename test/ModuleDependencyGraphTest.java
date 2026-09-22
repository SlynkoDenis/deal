package deal.test;

import deal.module.CompilationOrchestrator;
import deal.module.CompilerClassDefaultPlan;
import deal.module.ModuleDependencyGraph;
import deal.module.PlannedDefaultClass;
import deal.module.ResolvedDefaultExpression;
import deal.module.RuntimeImportDependency;
import deal.project.ProjectLocator;
import deal.semantic.CompilerInvocation;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ReleaseConfiguration;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The merged runtime dependency graph verification battery of
 * ISSUE-0543 (design source
 * {@code provider-versioned-default-plans} Verification 2 and the
 * task-pinned acceptance criteria): the digest-free SCC pass over the
 * merged ordinary ({@code RUNTIME_USE}) and default
 * ({@code DEFERRED_DEFAULT_BINDING}) edges, E2005 with per-edge notes
 * for default-only, ordinary-only, and mixed runtime SCCs, the
 * publication gate (no plan, FFI metadata, or artifact on E2005),
 * type-only cycle legality, and the acyclic path — provider digests
 * requested only after the SCC pass, final digest-bearing
 * {@link RuntimeImportDependency} records, completed plans, and the
 * initialization order preserving first-import order — exercised
 * through the real orchestrator path (ProjectLocator &rarr; the
 * production CompilationOrchestrator &rarr; {@code compile()}) plus
 * direct unit pins of the shared ordering algorithm.
 *
 * <p>Rejection-before-digest-demand is pinned structurally: a runtime
 * SCC emits exactly E2005 with no E6005 — the serializer's reentrant
 * digest guard would fail closed with E6005 if any provider digest
 * were demanded on the cyclic occurrence structure first, so an
 * E2005-only failure proves the digest-free SCC pass ran before any
 * digest request.</p>
 */
public class ModuleDependencyGraphTest {

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
     * item 3): the suite's subject — the runtime dependency graph and its
     * SCC gates — is arm-independent, and the fixtures keep the harness
     * arm's retained artifact behavior.
     */
    private static CompilerInvocation invocation() {
        return ConformanceHarnessMetadata.invocation(
            SemanticProfile.DEAL_V1_2_INT32);
    }

    private static final String MANIFEST = """
        {
          "languageVersion": "1.2",
          "moduleRoots": ["src"],
          "backend": "luajit",
          "output": "build"
        }
        """;

    /** One in-process production compile over a scratch project. */
    private static final class Compile {
        final Path root;
        final CompilationOrchestrator orchestrator;
        final boolean success;

        Compile(Map<String, String> files, String entryRel)
                throws Exception {
            root = Files.createTempDirectory("deal_graph_");
            for (Map.Entry<String, String> file : files.entrySet()) {
                write(root, file.getKey(), file.getValue());
            }
            Path entry = root.resolve(entryRel);
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
        }

        List<deal.diagnostics.CompilerDiagnostic> errorOf(String code) {
            List<deal.diagnostics.CompilerDiagnostic> matches =
                new ArrayList<>();
            for (deal.diagnostics.CompilerDiagnostic d
                    : orchestrator.diagnostics()) {
                if (code.equals(d.code())
                        && "error".equals(d.severity())) {
                    matches.add(d);
                }
            }
            return matches;
        }

        List<RuntimeImportDependency> edgesFrom(String sourceSuffix) {
            List<RuntimeImportDependency> edges = new ArrayList<>();
            for (RuntimeImportDependency edge
                    : orchestrator.runtimeDependencies()) {
                if (edge.fromSemanticModuleIdentity()
                        .canonicalResolvedSourceUri()
                        .endsWith(sourceSuffix)) {
                    edges.add(edge);
                }
            }
            return edges;
        }
    }

    /**
     * Recompiles the same scratch root in place (same deployment
     * identity, so unchanged providers keep byte-identical digests).
     */
    private static CompilationOrchestrator recompile(Compile compile)
            throws Exception {
        Path entry = compile.root.resolve("src/main.deal");
        ProjectLocator.LocateResult located =
            ProjectLocator.locate(entry.toString(), null);
        if (located.context() == null) {
            throw new IllegalStateException(
                "ProjectLocator failed: " + located.e2010());
        }
        CompilationOrchestrator orchestrator =
            new CompilationOrchestrator(located.context(), entry, false,
                false, false, false, null, invocation());
        if (!orchestrator.compile()) {
            throw new IllegalStateException(
                "recompile failed: " + orchestrator.diagnostics());
        }
        return orchestrator;
    }

    /** True iff the text is a 64-lowercase-hex-char SHA-256 digest. */
    private static boolean isSha256Hex(String text) {
        return text != null && text.matches("[0-9a-f]{64}");
    }

    /**
     * The decoded-Unicode-scalar start offset of the first occurrence
     * of the given text in the given source (the fixture sources are
     * ASCII, so Java string offsets are scalar offsets) — used to pin
     * the first-occurrence reference ranges of the merged edges.
     */
    private static int scalarOffsetOf(String source, String text) {
        return source.indexOf(text);
    }

    public static void main(String[] args) throws Exception {
        testInitializationOrderAlgorithm();
        testAcyclicOrdinaryAndDefaultEdges();
        testDefaultOnlyRuntimeCycle();
        testOrdinaryOnlyRuntimeCycle();
        testMixedRuntimeCycle();
        testTwoDisconnectedRuntimeSccs();
        testTypeOnlyCycleRemainsValid();
        testRejectionPrecedesDigestDemandAndPublication();
        System.out.println();
        System.out.println("Passed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.err.println("ModuleDependencyGraphTest FAILED: "
                + failed + " failure(s)");
            System.exit(1);
        }
    }

    // =========================================================================
    // The one shared initialization-order algorithm
    // =========================================================================

    private static void testInitializationOrderAlgorithm() {
        System.out.println("-- Initialization order (the shared"
            + " algorithm) --");

        // Acyclic: topological order in discovery order.
        Map<String, Set<String>> diamond = new LinkedHashMap<>();
        diamond.put("a", new LinkedHashSet<>(List.of("b", "c")));
        diamond.put("b", new LinkedHashSet<>(List.of("d")));
        diamond.put("c", new LinkedHashSet<>(List.of("d")));
        diamond.put("d", new LinkedHashSet<>());
        check(ModuleDependencyGraph.initializationOrder(
                new ArrayList<>(diamond.keySet()), diamond)
                .equals(List.of("d", "b", "c", "a")),
            "diamond orders as [d, b, c, a], got "
                + ModuleDependencyGraph.initializationOrder(
                    new ArrayList<>(diamond.keySet()), diamond));

        // A type-only cycle with a dependent: cycle members precede the
        // dependent.
        Map<String, Set<String>> cycleWithDependent =
            new LinkedHashMap<>();
        cycleWithDependent.put("a",
            new LinkedHashSet<>(List.of("b")));
        cycleWithDependent.put("b",
            new LinkedHashSet<>(List.of("a")));
        cycleWithDependent.put("c",
            new LinkedHashSet<>(List.of("a")));
        check(ModuleDependencyGraph.initializationOrder(
                new ArrayList<>(cycleWithDependent.keySet()),
                cycleWithDependent)
                .equals(List.of("a", "b", "c")),
            "cycle-with-dependent orders [a, b, c], got "
                + ModuleDependencyGraph.initializationOrder(
                    new ArrayList<>(cycleWithDependent.keySet()),
                    cycleWithDependent));

        // A ready module precedes the cycle members (first-import /
        // discovery order preserved).
        Map<String, Set<String>> readyThenCycle = new LinkedHashMap<>();
        readyThenCycle.put("d", new LinkedHashSet<>());
        readyThenCycle.put("a",
            new LinkedHashSet<>(List.of("b")));
        readyThenCycle.put("b",
            new LinkedHashSet<>(List.of("a")));
        readyThenCycle.put("c",
            new LinkedHashSet<>(List.of("a")));
        check(ModuleDependencyGraph.initializationOrder(
                new ArrayList<>(readyThenCycle.keySet()),
                readyThenCycle)
                .equals(List.of("d", "a", "b", "c")),
            "ready-module-then-cycle orders [d, a, b, c], got "
                + ModuleDependencyGraph.initializationOrder(
                    new ArrayList<>(readyThenCycle.keySet()),
                    readyThenCycle));

        // Two disconnected cycles plus a late importer.
        Map<String, Set<String>> twoCycles = new LinkedHashMap<>();
        twoCycles.put("entry",
            new LinkedHashSet<>(List.of("a", "c")));
        twoCycles.put("a", new LinkedHashSet<>(List.of("b")));
        twoCycles.put("b", new LinkedHashSet<>(List.of("a")));
        twoCycles.put("c", new LinkedHashSet<>(List.of("d")));
        twoCycles.put("d", new LinkedHashSet<>(List.of("c")));
        check(ModuleDependencyGraph.initializationOrder(
                new ArrayList<>(twoCycles.keySet()), twoCycles)
                .equals(List.of("a", "b", "c", "d", "entry")),
            "two disconnected cycles order [a, b, c, d, entry], got "
                + ModuleDependencyGraph.initializationOrder(
                    new ArrayList<>(twoCycles.keySet()), twoCycles));
    }

    // =========================================================================
    // Acyclic: ordinary + default edges, digests, plans, order
    // =========================================================================

    private static void testAcyclicOrdinaryAndDefaultEdges()
            throws Exception {
        System.out.println("-- Acyclic graph: ordinary + default edges,"
            + " digests, completed plans, initialization order --");
        String mainSource = """
            import * as L from "./lib"

            class Holder {
              seed: int = L.get(1);
              rec: L.Rec = {};
            }

            export function build(): L.Rec {
              return { tag: 2 };
            }

            export function probe(): int {
              return L.get(3);
            }

            export function main(): null {
              return null;
            }
            """;
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/main.deal", mainSource,
            "src/lib.deal", """
                export class Rec {
                  tag: int = 0;
                }
                export function get(x: int): int {
                  return x + 1;
                }
                """), "src/main.deal");
        try {
            check(compile.success,
                "the acyclic fixture compiles: "
                    + compile.orchestrator.diagnostics());

            // ---- Initialization order: imported module first ----
            List<String> order = compile.orchestrator.dependencyOrder();
            check(order.size() == 2,
                "two modules in the initialization order, got " + order);
            check(order.get(0).endsWith("lib.deal")
                    && order.get(1).endsWith("main.deal"),
                "initialization order is [lib, main], got " + order);

            // ---- Ordinary records: reason, digests, first ranges ----
            List<RuntimeImportDependency> ordinary =
                compile.edgesFrom("main.deal");
            List<RuntimeImportDependency> use = ordinary.stream()
                .filter(e -> e.reason()
                    == RuntimeImportDependency.Reason.RUNTIME_USE)
                .toList();
            check(use.size() == 2,
                "exactly two ordinary records from main (Rec plan via"
                    + " the contextual literal, get call via probe),"
                    + " got " + use);
            for (RuntimeImportDependency edge : use) {
                check(isSha256Hex(edge.providerContractDigest()),
                    "ordinary record carries a real provider digest: "
                        + edge.providerContractDigest());
                check(edge.sourceRange().file().endsWith("main.deal"),
                    "ordinary record range lives in main.deal: "
                        + edge.sourceRange());
            }
            int getOffset = scalarOffsetOf(mainSource, "L.get(3)");
            boolean firstRange = use.stream().anyMatch(e ->
                e.semanticResourceIdentity().resourceKind()
                    == deal.module.LexicalDeclarationIdentity
                        .DeclarationKind.FUNCTION
                    && e.importAlias().equals("L")
                    && e.sourceRange().startScalarOffset() == getOffset
                    && e.sourceRange().scalarLength() == 8);
            check(firstRange,
                "the ordinary function-wrapper record carries the"
                    + " probe call's first call-site range, got "
                    + use);
            // The contextual class literal in build() records the
            // class plan at the literal range (first occurrence):
            // main's first class-plan occurrence is the Holder default
            // (DEFERRED), so the ordinary class-literal record carries
            // the build() literal range.
            boolean classLiteralEdge = use.stream().anyMatch(e ->
                e.semanticResourceIdentity().resourceKind()
                    == deal.module.LexicalDeclarationIdentity
                        .DeclarationKind.CLASS);
            check(classLiteralEdge,
                "the build() contextual literal publishes an ordinary"
                    + " class-plan record: " + use);

            // ---- Default records + completed plans ----
            List<RuntimeImportDependency> deferred = ordinary.stream()
                .filter(e -> e.reason()
                    == RuntimeImportDependency.Reason
                        .DEFERRED_DEFAULT_BINDING)
                .toList();
            check(deferred.size() == 2,
                "exactly two default records from main (get wrapper,"
                    + " Rec plan), got " + deferred);
            for (RuntimeImportDependency edge : deferred) {
                check(isSha256Hex(edge.providerContractDigest()),
                    "default record carries a real provider digest: "
                        + edge.providerContractDigest());
            }
            Map<String, List<PlannedDefaultClass>> completed =
                compile.orchestrator.completedDefaultPlans();
            check(completed.size() == 2,
                "both modules publish completed plans, got "
                    + completed.keySet());
            CompilerClassDefaultPlan holder = null;
            for (List<PlannedDefaultClass> plans : completed.values()) {
                for (PlannedDefaultClass planned : plans) {
                    if (planned.plan().classIdentity().className()
                            .equals("Holder")) {
                        holder = planned.plan();
                    }
                }
            }
            check(holder != null, "Holder has a completed plan");
            if (holder != null) {
                check(holder.runtimeDependencies().size() == 2,
                    "Holder completes two runtimeDependencies, got "
                        + holder.runtimeDependencies());
                check(holder.runtimeDependencies().stream()
                        .allMatch(e -> e.reason()
                            == RuntimeImportDependency.Reason
                                .DEFERRED_DEFAULT_BINDING
                            && isSha256Hex(
                                e.providerContractDigest())),
                    "Holder dependencies carry the default reason and"
                        + " real digests");
                for (deal.module.CompilerClassDefaultEntry entry
                        : holder.orderedFields()) {
                    ResolvedDefaultExpression expr =
                        entry.defaultExpression();
                    check(expr != null && expr.canonicalSemanticContent()
                            != null && expr.semanticDigest() != null,
                        "Holder entry '" + entry.name()
                            + "' carries canonical content and digest");
                    check(expr != null && expr.runtimeResources()
                            .stream().allMatch(r -> isSha256Hex(
                                r.providerContractDigest())),
                        "Holder entry '" + entry.name()
                            + "' completes digest-bearing"
                            + " runtimeResources");
                }
            }

            // ---- Provider digests are real and stable across a
            // second compile of the same root (same deployment
            // identity) ----
            List<String> firstDigests = compile.orchestrator
                .runtimeDependencies().stream()
                .map(RuntimeImportDependency::providerContractDigest)
                .toList();
            CompilationOrchestrator second = recompile(compile);
            List<String> secondDigests = second
                .runtimeDependencies().stream()
                .map(RuntimeImportDependency::providerContractDigest)
                .toList();
            check(firstDigests.equals(secondDigests),
                "identical compilations over the same root produce"
                    + " identical provider digests");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Default-only runtime SCC -> E2005 with notes, nothing published
    // =========================================================================

    private static void testDefaultOnlyRuntimeCycle() throws Exception {
        System.out.println("-- Default-only runtime SCC: E2005 notes and"
            + " the publication gate --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/da.deal", """
                import * as B from "./db"
                export function main(): null { return null; }
                export class Holder {
                  seed: int = B.get(1);
                }
                """,
            "src/db.deal", """
                import * as A from "./da"
                export function get(x: int): int { return x + 1; }
                """), "src/da.deal");
        try {
            check(!compile.success,
                "the default-only runtime cycle fails");
            List<deal.diagnostics.CompilerDiagnostic> e2005s =
                compile.errorOf("E2005");
            check(e2005s.size() == 1,
                "exactly one E2005, got " + e2005s);
            if (e2005s.size() == 1) {
                deal.diagnostics.CompilerDiagnostic e2005 =
                    e2005s.get(0);
                check(e2005.message().contains("da.deal")
                        && e2005.message().contains("db.deal"),
                    "the E2005 message names the cycle: "
                        + e2005.message());
                check(e2005.range().file().endsWith("da.deal"),
                    "the E2005 anchor is the first cycle module's"
                        + " import declaration (da.deal): "
                        + e2005.range());
                boolean hasDefaultNote = e2005.notes().stream()
                    .anyMatch(n -> n.message().contains(
                        "runtime edge DEFERRED_DEFAULT_BINDING")
                        && n.message().contains("da.deal")
                        && n.message().contains("db.deal"));
                check(hasDefaultNote,
                    "E2005 notes the DEFERRED_DEFAULT_BINDING edge"
                        + " da -> db: " + e2005.notes());
                deal.diagnostics.DiagnosticNote note =
                    e2005.notes().stream().filter(n -> n.message()
                        .contains("DEFERRED_DEFAULT_BINDING"))
                        .findFirst().orElse(null);
                check(note != null && note.range() != null
                        && note.range().file().endsWith("da.deal")
                        && note.range().scalarLength() == 8,
                    "the edge note carries the first-occurrence"
                        + " reference range (B.get(1), span 8): "
                        + (note == null ? null : note.range()));
            }
            check(compile.orchestrator.plannedDefaultClasses().isEmpty(),
                "E2005 publishes no plan (provisional plans"
                    + " discarded)");
            check(compile.orchestrator.completedDefaultPlans().isEmpty(),
                "E2005 publishes no completed plan");
            check(compile.orchestrator.runtimeDependencies().isEmpty(),
                "E2005 publishes no dependency record");
            check(!Files.exists(compile.root.resolve("build")),
                "E2005 publishes no artifact (no output directory)");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Ordinary-only runtime SCC -> E2005 with RUNTIME_USE notes
    // =========================================================================

    private static void testOrdinaryOnlyRuntimeCycle() throws Exception {
        System.out.println("-- Ordinary-only runtime SCC (function"
            + " bodies): E2005 with RUNTIME_USE notes --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/oa.deal", """
                import * as B from "./ob"
                export function main(): null { return null; }
                export function foo(): int { return B.get(); }
                export function value(): int { return 1; }
                """,
            "src/ob.deal", """
                import * as A from "./oa"
                export function get(): int { return A.value(); }
                """), "src/oa.deal");
        try {
            check(!compile.success,
                "the ordinary-only runtime cycle fails");
            List<deal.diagnostics.CompilerDiagnostic> e2005s =
                compile.errorOf("E2005");
            check(e2005s.size() == 1,
                "exactly one E2005, got " + e2005s);
            if (e2005s.size() == 1) {
                deal.diagnostics.CompilerDiagnostic e2005 =
                    e2005s.get(0);
                long useNotes = e2005.notes().stream().filter(n ->
                    n.message().contains(
                        "runtime edge RUNTIME_USE")).count();
                check(useNotes == 2,
                    "one RUNTIME_USE note per ordinary edge (oa -> ob"
                        + " and ob -> oa), got " + e2005.notes());
                boolean oaToOb = e2005.notes().stream().anyMatch(n ->
                    n.message().contains("oa.deal -> ")
                        && n.message().contains("ob.deal")
                        && n.range() != null
                        && n.range().file().endsWith("oa.deal"));
                boolean obToOa = e2005.notes().stream().anyMatch(n ->
                    n.message().contains("ob.deal -> ")
                        && n.message().contains("oa.deal")
                        && n.range() != null
                        && n.range().file().endsWith("ob.deal"));
                check(oaToOb && obToOa,
                    "both ordinary edges carry their first-occurrence"
                        + " ranges in the notes: " + e2005.notes());
            }
            check(compile.orchestrator.runtimeDependencies().isEmpty()
                    && compile.orchestrator.plannedDefaultClasses()
                        .isEmpty(),
                "E2005 publishes no record and no plan");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Mixed runtime SCC: notes for both reason values
    // =========================================================================

    private static void testMixedRuntimeCycle() throws Exception {
        System.out.println("-- Mixed runtime SCC: notes for both reason"
            + " values --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/ma.deal", """
                import * as B from "./mb"
                export function main(): null { return null; }
                export class Holder {
                  seed: int = B.get(1);
                }
                export function value(): int { return 1; }
                """,
            "src/mb.deal", """
                import * as A from "./ma"
                export function get(x: int): int {
                  return A.value() + x;
                }
                """), "src/ma.deal");
        try {
            check(!compile.success, "the mixed runtime cycle fails");
            List<deal.diagnostics.CompilerDiagnostic> e2005s =
                compile.errorOf("E2005");
            check(e2005s.size() == 1,
                "exactly one E2005, got " + e2005s);
            if (e2005s.size() == 1) {
                deal.diagnostics.CompilerDiagnostic e2005 =
                    e2005s.get(0);
                boolean defaultNote = e2005.notes().stream().anyMatch(
                    n -> n.message().contains(
                        "DEFERRED_DEFAULT_BINDING")
                        && n.message().contains("ma.deal")
                        && n.message().contains("mb.deal"));
                boolean useNote = e2005.notes().stream().anyMatch(
                    n -> n.message().contains("RUNTIME_USE")
                        && n.message().contains("mb.deal")
                        && n.message().contains("ma.deal"));
                check(defaultNote && useNote,
                    "the mixed SCC notes both reason values with their"
                        + " ranges: " + e2005.notes());
            }
            check(compile.orchestrator.completedDefaultPlans().isEmpty()
                    && compile.orchestrator.runtimeDependencies()
                        .isEmpty(),
                "the mixed SCC publishes nothing");
            check(!Files.exists(compile.root.resolve("build")),
                "the mixed SCC publishes no artifact");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Two disconnected runtime SCCs -> two deterministic E2005s
    // =========================================================================

    private static void testTwoDisconnectedRuntimeSccs()
            throws Exception {
        System.out.println("-- Two disconnected runtime SCCs: two"
            + " deterministic E2005 diagnostics --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/entry.deal", """
                import * as A from "./ta"
                import * as C from "./tc"
                export function main(): null { return null; }
                export function probe(): int { return 1; }
                """,
            "src/ta.deal", """
                import * as B from "./tb"
                export function foo(): int { return B.get(); }
                export function value(): int { return 1; }
                """,
            "src/tb.deal", """
                import * as A from "./ta"
                export function get(): int { return A.value(); }
                """,
            "src/tc.deal", """
                import * as D from "./td"
                export function foo(): int { return D.get(); }
                export function value(): int { return 2; }
                """,
            "src/td.deal", """
                import * as C from "./tc"
                export function get(): int { return C.value(); }
                """), "src/entry.deal");
        try {
            check(!compile.success,
                "two disconnected runtime SCCs fail the compile");
            List<deal.diagnostics.CompilerDiagnostic> e2005s =
                compile.errorOf("E2005");
            check(e2005s.size() == 2,
                "exactly two E2005 diagnostics (one per runtime SCC),"
                    + " got " + e2005s);
            if (e2005s.size() == 2) {
                check(e2005s.get(0).message().contains("ta.deal"),
                    "the first E2005 anchors the ta/tb SCC: "
                        + e2005s.get(0).message());
                check(e2005s.get(1).message().contains("tc.deal"),
                    "the second E2005 anchors the tc/td SCC: "
                        + e2005s.get(1).message());
                check(e2005s.get(0).notes().size() == 2
                        && e2005s.get(1).notes().size() == 2,
                    "each E2005 notes its two runtime edges: "
                        + e2005s.get(0).notes() + " / "
                        + e2005s.get(1).notes());
            }
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Type-only cycle remains valid
    // =========================================================================

    private static void testTypeOnlyCycleRemainsValid() throws Exception {
        System.out.println("-- Type-only cycle remains valid --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/tya.deal", """
                import * as B from "./tyb"
                export function main(): null { return null; }
                export class TA { tag: int = 1; }
                export function pass(x: B.TB): B.TB { return x; }
                """,
            "src/tyb.deal", """
                import * as A from "./tya"
                export class TB { tag: int = 2; }
                export function pass(x: A.TA): A.TA { return x; }
                """), "src/tya.deal");
        try {
            check(compile.success,
                "the type-only cycle compiles: "
                    + compile.orchestrator.diagnostics());
            check(compile.errorOf("E2005").isEmpty(),
                "no E2005 for the type-only cycle");
            check(Files.exists(compile.root.resolve("build")
                    .resolve("tya.lua")),
                "the type-only cycle publishes artifacts");
        } finally {
            deleteRecursively(compile.root);
        }
    }

    // =========================================================================
    // Rejection precedes digest demand; publication gate
    // =========================================================================

    private static void testRejectionPrecedesDigestDemandAndPublication()
            throws Exception {
        System.out.println("-- Rejection precedes digest demand (no"
            + " serializer error on a cyclic graph) --");
        Compile compile = new Compile(Map.of(
            "deal.json", MANIFEST,
            "src/rma.deal", """
                import * as B from "./rmb"
                export function main(): null { return null; }
                export class Holder {
                  rec: B.Rec = {};
                }
                """,
            "src/rmb.deal", """
                import * as A from "./rma"
                export class Rec {
                  tag: int = 1;
                }
                export function make(): A.Holder {
                  return {};
                }
                """), "src/rma.deal");
        try {
            check(!compile.success,
                "the class-plan runtime cycle fails");
            List<deal.diagnostics.CompilerDiagnostic> e2005s =
                compile.errorOf("E2005");
            check(e2005s.size() == 1,
                "exactly one E2005, got " + e2005s);
            // The serializer's reentrant digest guard fails closed
            // with E6005 when a provider digest is demanded on a
            // cyclic occurrence structure; an E2005-only failure
            // therefore proves the digest-free SCC pass rejected the
            // cycle before any digest request.
            check(compile.errorOf("E6005").isEmpty(),
                "no E6005 — the serializer (and therefore every"
                    + " provider digest demand) never ran before the"
                    + " SCC rejection: "
                    + compile.orchestrator.diagnostics());
            check(compile.orchestrator.runtimeDependencies().isEmpty()
                    && compile.orchestrator.plannedDefaultClasses()
                        .isEmpty()
                    && compile.orchestrator.completedDefaultPlans()
                        .isEmpty(),
                "the rejected cycle publishes no plan and no record");
            check(!Files.exists(compile.root.resolve("build")),
                "the rejected cycle publishes no artifact");
        } finally {
            deleteRecursively(compile.root);
        }
    }
}
