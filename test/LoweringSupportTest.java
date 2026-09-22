package deal.test;

import deal.ast.ImportDeclaration;
import deal.ast.ProgramNode;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.checker.CheckResult;
import deal.checker.SymbolTable;
import deal.codegen.Backend;
import deal.ir.IrDumper;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.LoweringSupport;
import deal.semantic.RequirementManifestResult;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ConstructKind;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

/**
 * Verifies the ISSUE-0289 foundation surface: {@link LoweringSupport}
 * computing exactly one {@link SemanticRequirementManifest} per
 * implementation module over T8's checked project — the closed
 * capability claims (every module claims {@code FOUNDATION_VALUES}; the
 * {@code std/time.nowMillis} reference claims through the landed
 * cataloged-call arm since K7, and the superseded four-part
 * {@code STDLIB_TIME_CONFLICT} detector is retired) — plus the
 * reachable-construct coverage rows over T2's closed construct→op
 * detector table, E6005 on inconsistent checked facts via T5/T1, and
 * byte-identical determinism.
 *
 * <p>Tests:
 * <ol>
 *   <li>The K7 cataloged-call claim: a direct
 *       {@code time.nowMillis()} call claims {@code STDLIB_SEMANTICS}
 *       (never {@code STDLIB_TIME_CONFLICT}), and a
 *       value-position access ({@code let f: () => int =
 *       time.nowMillis; f();}) claims nothing from the read.</li>
 *   <li>The retired table-alias shapes: {@code let t = time;
 *       let g: () => int = t.nowMillis; g();} and a
 *       table-typed parameter passthrough carry no conflict claim (the K15
 *       namespace-value slice owns their lowering).</li>
 *   <li>The retired closure shapes: the cross-module table escape and
 *       the table re-export chain carry no conflict claim at any site;
 *       the wrappers' roots still claim no conflict.</li>
 *   <li>The retired propagation: wrapper escape and propagation chains
 *       through re-exporting intermediates carry no conflict claim in
 *       any module.</li>
 *   <li>Negatives: a {@code std/time} importer without any
 *       {@code nowMillis} access claims exactly FOUNDATION_VALUES +
 *       MODULES; an alias bound to {@code std/time} claims
 *       STDLIB_SEMANTICS through the cataloged call, an
 *       identically-named alias bound to another module does not.</li>
 *   <li>The retired over-claim direction: a direct importer or a closure
 *       member reading an unrelated table's {@code nowMillis}, and a
 *       module importing a nowMillis-using module, all carry no conflict
 *       claim.</li>
 *   <li>{@code constructCoverage}: one real module exercising every one
 *       of the 23 rows carrying a required common form (the
 *       {@code std/time.nowMillis} row included) records exactly
 *       those T2 rows with the verbatim mapped op kinds; a synthetic
 *       {@link LoweredModuleUnit} built from the manifest rows carries
 *       them on its own enum-keyed {@code constructCoverage} (the S1
 *       coverage fact).</li>
 *   <li>E6005: an import resolving outside the dependency-ordered index
 *       raises E6005 through T5 with the prescribed payload (module,
 *       capability {@code FOUNDATION_VALUES}, validatorRule
 *       {@code MANIFEST_INTERNAL_ERROR_SENTINEL}, semanticProfile,
 *       irVersion, origin) — a T8 wrong-index-fact fault fails this
 *       suite; the record guards reject a manifest without
 *       {@code FOUNDATION_VALUES}, a T2-corrupted coverage row, and a
 *       coverage row diverging from the closed mapped op kinds (the
 *       formerly excluded {@code STDLIB_TIME_NOW_MILLIS} row included);
 *       a T8 input entry without {@code checks} is
 *       rejected at record construction; the T1 capability enum admits
 *       exactly the closed set.</li>
 *   <li>Determinism: two orchestrator compiles of the same fixture
 *       produce byte-identical manifest canonical texts and equal
 *       digests; recomputation over the same checked project is
 *       identical and leaves the frontend facts byte-unchanged
 *       (IrDumper output equal before and after).</li>
 * </ol>
 */
public class LoweringSupportTest {

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
    // Small helpers
    // =========================================================================

    private static Span span() {
        return new Span("test.deal", 1, 1, 1, 1);
    }

    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
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
     * through the full orchestrator pipeline (phase 3 + T8's builder +
     * the manifest phase) and returns the manifest result; null when the
     * compile or the checked project failed.
     */
    /**
     * The harness invocation of this suite's compiles (ISSUE-0643 P10
     * item 3): the fixtures carry later-slice constructs
     * ({@code time.nowMillis}, function-typed values) the release-owned
     * production invocation fails closed, while the suite's subject —
     * the checked project, the manifests, and the read-only recomputation
     * — is arm-independent.
     */
    private static CompilationOrchestrator harnessOrchestrator(Path entry,
                                                               Path output) {
        return new CompilationOrchestrator(entry, output, false, false, false,
            false, Backend.LUAJIT, null,
            List.of(entry.getParent().toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null,
            ConformanceHarnessMetadata.invocation(
                SemanticProfile.DEAL_V1_2_INT32));
    }

    /**
     * The release-owned production invocation (ISSUE-0643 P10 item 2):
     * the probe resolves the same record {@code deal.Main} and
     * {@code CompilationOrchestrator.defaultInvocation()} resolve, so
     * the compile dispatches to the production arm.
     */
    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(
            ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    /**
     * ISSUE-0623 (K7): the {@code time.nowMillis} fixture drives through
     * the release-owned production invocation to exactly one project
     * artifact that executes under the real toolchain with the pinned
     * E8004 {@code int out of safe range} terminal — the declared
     * {@code int} boundary is the single terminal of the target-clock
     * read. The value-position export-read shape
     * ({@code let f: () => int = time.nowMillis}) belongs to the export-read
     * slice (E10/K2) and is not this slice's fixture.
     */
    static void testProductionInvocationTimeDrive() throws Exception {
        System.out.println("-- The release-owned production invocation of the"
            + " time.nowMillis fixture: one artifact, the pinned E8004 terminal"
            + " --");

        Path tmp = Files.createTempDirectory("deal-manifest-production-");
        try {
            productionAccept(tmp.resolve("direct"), Map.of("main.deal", """
                import * as time from "std/time"

                export function main(): null {
                  time.nowMillis()
                  return null
                }
                """), "main.deal",
                "the direct time.nowMillis() production drive", "E8004");
        } finally {
            deleteRecursively(tmp);
        }
    }

    /**
     * The release-owned production acceptance of one covered fixture
     * (ISSUE-0619): the fixture compiles through the production invocation
     * to exactly one project artifact, the artifact exists, and the
     * artifact executes under its real toolchain with the pinned terminal —
     * the empty success output, or the canonical
     * {@code DEAL_ERROR_CODE: <code>} terminal of the declared failure.
     */
    private static void productionAccept(Path tmp, Map<String, String> sources,
                                         String entryName, String what,
                                         String expectedFailureCode)
            throws Exception {
        Path src = tmp.resolve("prod-src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Files.writeString(src.resolve(source.getKey()), source.getValue());
        }
        Path output = tmp.resolve("prod-build");
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            src.resolve(entryName).toAbsolutePath(), output, false, false,
            false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()),
            Path.of("std").toAbsolutePath().normalize(), null,
            productionInvocation());
        boolean ok = orchestrator.compile();
        check(ok, what + ": the release-owned production invocation accepts the "
            + "fixture: " + orchestrator.diagnostics());
        if (!ok) {
            return;
        }
        check(orchestrator.semanticEmissionCount() == 1
                && orchestrator.retainedEmissionCount() == 0,
            what + ": the production arm emits exactly one project artifact: "
                + "semantic=" + orchestrator.semanticEmissionCount()
                + " retained=" + orchestrator.retainedEmissionCount());
        check(Files.exists(output.resolve("main.lua")),
            what + ": the production artifact is staged");
        ProcessBuilder builder = new ProcessBuilder("luajit", "main.lua");
        builder.directory(output.toFile());
        builder.redirectErrorStream(true);
        Process process = builder.start();
        String runOutput = new String(process.getInputStream().readAllBytes(),
            java.nio.charset.StandardCharsets.UTF_8);
        int exitCode = process.waitFor();
        if (expectedFailureCode == null) {
            check(exitCode == 0 && runOutput.isEmpty(),
                what + ": the production artifact runs under luajit: exit="
                    + exitCode + " output=" + runOutput.replace("\n", "\\n"));
        } else {
            check(exitCode == 1
                    && runOutput.contains("DEAL_ERROR_CODE: " + expectedFailureCode),
                what + ": the production artifact publishes the pinned failure "
                    + "terminal DEAL_ERROR_CODE: " + expectedFailureCode + ": exit="
                    + exitCode + " output=" + runOutput.replace("\n", "\\n"));
        }
    }

    private static RequirementManifestResult compileAndCompute(Path tmp,
                                                               Map<String, String> sources,
                                                               String entryName)
            throws Exception {
        Path src = tmp.resolve("src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Files.writeString(src.resolve(source.getKey()), source.getValue());
        }
        CompilationOrchestrator orchestrator =
            harnessOrchestrator(src.resolve(entryName).toAbsolutePath(),
                tmp.resolve("build"));
        boolean ok = orchestrator.compile();
        check(ok, entryName + " compiles through phase 3 + builder + manifests: "
            + orchestrator.diagnostics());
        if (!ok) {
            return null;
        }
        CheckedProjectBuildResult checked = orchestrator.checkedProject();
        check(checked != null && !checked.hasErrors(),
            "the orchestrator built exactly one checked project before the manifests");
        RequirementManifestResult result = orchestrator.requirementManifests();
        check(result != null && !result.hasErrors(),
            "the orchestrator computed exactly one manifest result: "
                + (result == null ? "null" : result.diagnostics()));
        return result;
    }

    private static SemanticRequirementManifest manifestOf(RequirementManifestResult result,
                                                          String modulePath) {
        if (result == null || result.hasErrors()) {
            return null;
        }
        for (SemanticRequirementManifest manifest : result.manifests()) {
            if (manifest.moduleId().path().equals(modulePath)) {
                return manifest;
            }
        }
        return null;
    }

    /**
     * The K7 retirement pin: no manifest claims the inert
     * {@code STDLIB_TIME_CONFLICT} routing marker — the superseded
     * four-part line trigger and its planning claim are retired, and a
     * {@code std/time.nowMillis} reference claims through the landed
     * cataloged-call arm instead.
     */
    private static boolean noConflictClaim(SemanticRequirementManifest manifest) {
        return manifest != null
            && !manifest.capabilities().contains(SemanticCapability.STDLIB_TIME_CONFLICT);
    }

    /**
     * The K7 cataloged-call claim: {@code STDLIB_SEMANTICS} is carried by a
     * module whose checked source contains a cataloged stdlib call (the
     * produced {@code STDLIB_CALL} op is its evidence) —
     * {@code time.nowMillis()} included since the {@code std.time} row is
     * closed.
     */
    private static boolean claimsStdlibSemantics(SemanticRequirementManifest manifest) {
        return manifest != null
            && manifest.capabilities().contains(SemanticCapability.STDLIB_SEMANTICS);
    }

    private static boolean claimsOnlyFoundation(SemanticRequirementManifest manifest) {
        return manifest != null
            && manifest.capabilities().equals(EnumSet.of(SemanticCapability.FOUNDATION_VALUES));
    }

    /**
     * The ISSUE-0239 MODULES import claim plus FOUNDATION_VALUES: an
     * importing module with no other trigger claims exactly these two
     * capabilities (the reserved parent verification-3 plan-time edge
     * reroute condition; an export declaration or the entry delegation
     * never claims it).
     */
    private static boolean claimsFoundationAndModules(SemanticRequirementManifest manifest) {
        return manifest != null
            && manifest.capabilities().equals(EnumSet.of(
                SemanticCapability.FOUNDATION_VALUES, SemanticCapability.MODULES));
    }

    /** The I3 signed32 claim: exactly FOUNDATION_VALUES + SIGNED_INT32, nothing else. */
    private static boolean claimsSignedInt32(SemanticRequirementManifest manifest) {
        return manifest != null
            && manifest.capabilities().equals(EnumSet.of(
                SemanticCapability.FOUNDATION_VALUES, SemanticCapability.SIGNED_INT32));
    }

    /** I3 signed32 plus the ISSUE-0239 MODULES arms (importing/imported-by). */
    private static boolean claimsSignedInt32AndModules(
            SemanticRequirementManifest manifest) {
        return manifest != null
            && manifest.capabilities().equals(EnumSet.of(
                SemanticCapability.FOUNDATION_VALUES, SemanticCapability.SIGNED_INT32,
                SemanticCapability.MODULES));
    }

    // =========================================================================
    // 1. The K7 cataloged call and the retired access trigger
    // =========================================================================

    static void testDirectCallClaimsStdlibSemantics() throws Exception {
        System.out.println("-- K7: the direct cataloged call claims STDLIB_SEMANTICS, "
            + "never the conflict marker --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-a-call");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      time.nowMillis()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main"))
                    && claimsStdlibSemantics(manifestOf(result, "main")),
                "a direct time.nowMillis() call claims STDLIB_SEMANTICS through the "
                    + "landed cataloged-call arm and never STDLIB_TIME_CONFLICT (K7)");
            check(!manifestOf(result, "main").capabilities().isEmpty()
                    && manifestOf(result, "main").capabilities()
                        .contains(SemanticCapability.FOUNDATION_VALUES),
                "every implementation module claims FOUNDATION_VALUES");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testValuePositionReadClaimsNothing() throws Exception {
        System.out.println("-- the value-position read claims nothing from the read --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-a-value");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      let f: () => int = time.nowMillis
                      f()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main")),
                "let f: () => int = time.nowMillis; f(); carries no "
                    + "STDLIB_TIME_CONFLICT claim — the value-position read claims nothing "
                    + "from the read (D3) and the retired trigger never fires");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 2. The retired table-alias trigger (the K15 namespace-value slice)
    // =========================================================================

    static void testRetiredTriggerTableAlias() throws Exception {
        System.out.println("-- the retired table-alias shape --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-b-alias");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      let t = time
                      let g: () => int = t.nowMillis
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main")),
                "let t = time; let g: () => int = t.nowMillis; g(); carries no "
                    + "STDLIB_TIME_CONFLICT claim — the table-typed escape is the K15 "
                    + "namespace-value slice, never a reroute claim");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRetiredTriggerParameterPassthrough() throws Exception {
        System.out.println("-- the retired table-parameter passthrough shape --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-b-param");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function pick(t: table): () => int {
                      return t.nowMillis
                    }

                    export function main(): null {
                      let g: () => int = pick(time)
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main")),
                "a table-typed parameter passthrough returning p.nowMillis carries no "
                    + "STDLIB_TIME_CONFLICT claim");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 3. The retired closure trigger
    // =========================================================================

    static void testRetiredTriggerCrossModuleTableEscape() throws Exception {
        System.out.println("-- the retired cross-module table escape --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-c-escape");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getTime(): table {
                      return time
                    }
                    """,
                "main.deal", """
                    import * as a from "./a"

                    export function main(): null {
                      let t: table = a.getTime()
                      let g: () => int = t.nowMillis
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(result, "a")),
                "module A exporting the live stdlib table claims nothing — A contains no "
                    + "nowMillis member access");
            check(noConflictClaim(manifestOf(result, "main")),
                "the cross-module table escape carries no STDLIB_TIME_CONFLICT claim: "
                    + "the access site's shape is the K15 namespace-value slice and no "
                    + "closure propagation exists");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRetiredTriggerTableReExportChain() throws Exception {
        System.out.println("-- the retired table re-export chain --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-c-chain");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getTime(): table {
                      return time
                    }
                    """,
                "b.deal", """
                    import * as a from "./a"

                    export function getTime2(): table {
                      return a.getTime()
                    }
                    """,
                "main.deal", """
                    import * as b from "./b"

                    export function main(): null {
                      let t: table = b.getTime2()
                      let g: () => int = t.nowMillis
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(result, "a")),
                "the std/time importer A claims nothing (no member access)");
            check(claimsFoundationAndModules(manifestOf(result, "b")),
                "the non-accessing intermediate B claims nothing (no member access)");
            check(noConflictClaim(manifestOf(result, "main")),
                "C carries no STDLIB_TIME_CONFLICT claim through the intermediate B: "
                    + "the closure propagation is retired (K7)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 4. The retired claim propagation
    // =========================================================================

    static void testRetiredTriggerWrapperEscape() throws Exception {
        System.out.println("-- the retired wrapper escape --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-d-wrapper");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getNow(): () => int {
                      return time.nowMillis
                    }
                    """,
                "main.deal", """
                    import * as a from "./a"

                    export function main(): null {
                      let g: () => int = a.getNow()
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "a")),
                "module A exporting the locked wrapper carries no STDLIB_TIME_CONFLICT "
                    + "claim (the retired Arm A trigger never fires)");
            check(noConflictClaim(manifestOf(result, "main")),
                "module B carries no STDLIB_TIME_CONFLICT claim either: B contains no "
                    + "nowMillis member access, and no cross-module propagation exists");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRetiredTriggerPropagationChain() throws Exception {
        System.out.println("-- the retired propagation chains --");

        Path tmp = Files.createTempDirectory("deal-manifest-arm-d-chain");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getNow(): () => int {
                      return time.nowMillis
                    }
                    """,
                "b.deal", """
                    import * as a from "./a"

                    export function getNow2(): () => int {
                      return a.getNow()
                    }
                    """,
                "main.deal", """
                    import * as b from "./b"

                    export function main(): null {
                      let g: () => int = b.getNow2()
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "a")),
                "the access origin A carries no STDLIB_TIME_CONFLICT claim");
            check(noConflictClaim(manifestOf(result, "b")),
                "the re-exporting intermediate B carries no STDLIB_TIME_CONFLICT claim "
                    + "(the propagation arm is retired)");
            check(noConflictClaim(manifestOf(result, "main")),
                "C carries no STDLIB_TIME_CONFLICT claim through the intermediate B");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 5. Negatives: no access → no claim; the alias join is exact
    // =========================================================================

    static void testNoAccessImporterDoesNotClaim() throws Exception {
        System.out.println("-- Negative: a std/time importer without any nowMillis access --");

        Path tmp = Files.createTempDirectory("deal-manifest-no-access");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(result, "main")),
                "a module importing std/time without any member access of nowMillis does "
                    + "not claim STDLIB_TIME_CONFLICT");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testAliasJoinExactness() throws Exception {
        System.out.println("-- Alias join exactness: the std/time alias claims "
            + "STDLIB_SEMANTICS, an identically-named other alias does not --");

        Path tmp = Files.createTempDirectory("deal-manifest-alias-join");
        try {
            RequirementManifestResult triggers = compileAndCompute(tmp.resolve("triggers"),
                Map.of(
                    "main.deal", """
                        import * as time from "std/time"

                        export function main(): null {
                          time.nowMillis()
                          return null
                        }
                        """), "main.deal");
            RequirementManifestResult other = compileAndCompute(tmp.resolve("other"),
                Map.of(
                    "other.deal", """
                        export function nowMillis(): int {
                          return 0
                        }
                        """,
                    "main.deal", """
                        import * as time from "./other"

                        export function main(): null {
                          time.nowMillis()
                          return null
                        }
                        """), "main.deal");
            if (triggers == null || other == null) {
                return;
            }
            check(noConflictClaim(manifestOf(triggers, "main"))
                    && claimsStdlibSemantics(manifestOf(triggers, "main")),
                "an alias bound to std/time claims STDLIB_SEMANTICS through the cataloged "
                    + "call and never the retired conflict marker");
            check(claimsFoundationAndModules(manifestOf(other, "main")),
                "an identically-named alias bound to another module does not trigger: the "
                    + "join matches the resolved ModuleSymbol name against the module's "
                    + "ImportDeclaration records, and the resolved target is not std/time");
            check(claimsSignedInt32AndModules(manifestOf(other, "other")),
                "the other module exporting nowMillis claims FOUNDATION_VALUES + "
                    + "SIGNED_INT32 + MODULES (its return 0 int literal is CONST(Int) "
                    + "— the I3 derivation row claims at the construct kind, never the "
                    + "magnitude; the imported-by arm adds MODULES) "
                    + "and never STDLIB_TIME_CONFLICT");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 6. The retired over-claim direction: no claim fires anywhere
    // =========================================================================

    static void testRetiredOverClaimDirectImporter() throws Exception {
        System.out.println("-- Retired over-claim: a direct importer reading an unrelated "
            + "table carries no claim --");

        Path tmp = Files.createTempDirectory("deal-manifest-overclaim-b");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    function unrelated(): table {
                      return {}
                    }

                    export function main(): null {
                      let t: table = unrelated()
                      let g: () => int = t.nowMillis
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main")),
                "a std/time importer reading an unrelated table's nowMillis field carries "
                    + "no STDLIB_TIME_CONFLICT claim (the retired Arm B over-claim never "
                    + "fires; the read shape is the K15 namespace-value slice)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRetiredOverClaimClosureMember() throws Exception {
        System.out.println("-- Retired over-claim: a closure member reading an unrelated "
            + "table carries no claim --");

        Path tmp = Files.createTempDirectory("deal-manifest-overclaim-c");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getTable(): table {
                      return {}
                    }
                    """,
                "main.deal", """
                    import * as a from "./a"

                    export function main(): null {
                      let t: table = a.getTable()
                      let g: () => int = t.nowMillis
                      g()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(result, "a")),
                "the std/time importer A exporting an unrelated table claims nothing");
            check(noConflictClaim(manifestOf(result, "main")),
                "a module in the transitive closure reading an unrelated table's "
                    + "nowMillis field carries no STDLIB_TIME_CONFLICT claim (the "
                    + "retired Arm C over-claim never fires)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testRetiredOverClaimImporter() throws Exception {
        System.out.println("-- Retired over-claim: importing a nowMillis module carries no "
            + "claim --");

        Path tmp = Files.createTempDirectory("deal-manifest-overclaim-d");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "a.deal", """
                    import * as time from "std/time"

                    export function getNow(): () => int {
                      return time.nowMillis
                    }
                    """,
                "main.deal", """
                    import * as a from "./a"

                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(noConflictClaim(manifestOf(result, "main")),
                "a module importing a nowMillis-using module carries no "
                    + "STDLIB_TIME_CONFLICT claim even when it never invokes the wrapper "
                    + "(the retired Arm D propagation never fires)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testModulesImportClaim() throws Exception {
        System.out.println("-- ISSUE-0239 E10 plan-time arm: import declarations claim "
            + "MODULES; exports and the entry delegation never do --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-import");
        try {
            // An import declaration of any resolved kind claims MODULES
            // (the reserved parent verification-3 plan-time edge reroute
            // condition): the over-claim only forces LEGACY post-activation.
            RequirementManifestResult importer = compileAndCompute(tmp.resolve("imp"),
                Map.of(
                    "lib.deal", """
                        export function greet(): string {
                          return "ok"
                        }
                        """,
                    "main.deal", """
                        import * as lib from "./lib"

                        export function main(): null {
                          return null
                        }
                        """), "main.deal");
            if (importer == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(importer, "main")),
                "an import declaration claims MODULES (ISSUE-0239 E10 plan-time arm): "
                    + manifestOf(importer, "main").capabilities());
            check(claimsFoundationAndModules(manifestOf(importer, "lib")),
                "the implementation dependency claims MODULES through the "
                    + "imported-by arm (the reverse edge of the import graph — the "
                    + "retained-caller ABI facts stay SHADOW in this slice): "
                    + manifestOf(importer, "lib").capabilities());
            // An import-free single-module project with exports claims
            // nothing beyond FOUNDATION_VALUES (+SIGNED_INT32): export
            // declarations and the entry delegation never claim MODULES.
            RequirementManifestResult single = compileAndCompute(tmp.resolve("single"),
                Map.of("main.deal", """
                    export function value(): int {
                      return 42
                    }
                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (single == null) {
                return;
            }
            check(claimsSignedInt32(manifestOf(single, "main")),
                "the import-free single-module project claims exactly "
                    + "FOUNDATION_VALUES + SIGNED_INT32 (exports and the entry "
                    + "delegation never claim MODULES): "
                    + manifestOf(single, "main").capabilities());

            // A stdlib import claims MODULES even without any cataloged
            // call (the import-observation row attaches to the import
            // declaration itself).
            RequirementManifestResult stdlib = compileAndCompute(tmp.resolve("stdimp"),
                Map.of("main.deal", """
                    import * as console from "std/console"

                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (stdlib == null) {
                return;
            }
            check(claimsFoundationAndModules(manifestOf(stdlib, "main")),
                "a call-free stdlib import claims MODULES from the import declaration: "
                    + manifestOf(stdlib, "main").capabilities());
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 6b. I3 capability derivation rows: SIGNED_INT32 at the construct
    //     kind, never the magnitude
    // =========================================================================

    static void testSignedInt32LiteralClaims() throws Exception {
        System.out.println("-- I3 claims: int literals claim SIGNED_INT32, number literals do not --");

        Path tmp = Files.createTempDirectory("deal-manifest-i3-literals");
        try {
            RequirementManifestResult small = compileAndCompute(tmp.resolve("small"),
                Map.of("main.deal", """
                    export function one(): int {
                      return 1
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult max = compileAndCompute(tmp.resolve("max"),
                Map.of("main.deal", """
                    export function maxInt(): int {
                      return 2147483647
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult numberLiteral = compileAndCompute(tmp.resolve("number"),
                Map.of("main.deal", """
                    export function half(): number {
                      return 1.5
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            if (small == null || max == null || numberLiteral == null) {
                return;
            }
            check(claimsSignedInt32(manifestOf(small, "main")),
                "a module with the small literal 1 claims SIGNED_INT32 — the claim "
                    + "attaches to CONST(Int), never the magnitude");
            check(claimsSignedInt32(manifestOf(max, "main")),
                "a module with the literal 2147483647 claims SIGNED_INT32 exactly "
                    + "like the small literal — small literals waive nothing");
            check(claimsOnlyFoundation(manifestOf(numberLiteral, "main")),
                "a module with only a number literal claims exactly FOUNDATION_VALUES "
                    + "(CONST(Number) never claims SIGNED_INT32)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testSignedInt32UnaryBinaryClaims() throws Exception {
        System.out.println("-- I3 claims: UNARY(INT32_NEG)/BINARY(INT32_*) claim; "
            + "number/boolean rows do not --");

        Path tmp = Files.createTempDirectory("deal-manifest-i3-unary-binary");
        try {
            RequirementManifestResult neg = compileAndCompute(tmp.resolve("neg"),
                Map.of("main.deal", """
                    export function neg(x: int): int {
                      return -x
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult not = compileAndCompute(tmp.resolve("not"),
                Map.of("main.deal", """
                    export function not(b: boolean): boolean {
                      return !b
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult add = compileAndCompute(tmp.resolve("add"),
                Map.of("main.deal", """
                    export function add(x: int, y: int): int {
                      return x + y
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult eq = compileAndCompute(tmp.resolve("eq"),
                Map.of("main.deal", """
                    export function eq(x: int, y: int): boolean {
                      return x === y
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult addNumber = compileAndCompute(tmp.resolve("add-number"),
                Map.of("main.deal", """
                    export function addN(x: number, y: number): number {
                      return x + y
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            if (neg == null || not == null || add == null || eq == null
                    || addNumber == null) {
                return;
            }
            check(claimsSignedInt32(manifestOf(neg, "main")),
                "unary negation over an int operand claims SIGNED_INT32 "
                    + "(UNARY(INT32_NEG))");
            check(claimsOnlyFoundation(manifestOf(not, "main")),
                "boolean negation claims exactly FOUNDATION_VALUES (BOOL_NOT never "
                    + "claims SIGNED_INT32)");
            check(claimsSignedInt32(manifestOf(add, "main")),
                "int addition claims SIGNED_INT32 (BINARY(INT32_ADD))");
            check(claimsSignedInt32(manifestOf(eq, "main")),
                "int comparison claims SIGNED_INT32 (BINARY(INT32_EQ) — the "
                    + "BINARY(INT32_*) row covers comparison selectors too)");
            check(claimsOnlyFoundation(manifestOf(addNumber, "main")),
                "number addition claims exactly FOUNDATION_VALUES (NUMBER_ADD never "
                    + "claims SIGNED_INT32)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testIntrinsicConversionClaims() throws Exception {
        System.out.println("-- I3 claims: int(...) claims SIGNED_INT32; number(...) "
            + "claims FOUNDATION_VALUES only --");

        Path tmp = Files.createTempDirectory("deal-manifest-i3-intrinsics");
        try {
            RequirementManifestResult toInt = compileAndCompute(tmp.resolve("to-int"),
                Map.of("main.deal", """
                    export function cvt(x: number): int {
                      return int(x)
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            RequirementManifestResult toNumber = compileAndCompute(tmp.resolve("to-number"),
                Map.of("main.deal", """
                    export function cvtN(x: int): number {
                      return number(x)
                    }

                    export function main(): null { return null; }
                    """), "main.deal");
            if (toInt == null || toNumber == null) {
                return;
            }
            check(claimsSignedInt32(manifestOf(toInt, "main")),
                "int(...) claims SIGNED_INT32 (INTRINSIC_CALL(INT_CONVERT))");
            check(claimsOnlyFoundation(manifestOf(toNumber, "main")),
                "number(...) claims exactly FOUNDATION_VALUES "
                    + "(INTRINSIC_CALL(NUMBER_CONVERT)) and never SIGNED_INT32 — the "
                    + "module carries no int construct");
            check(manifestOf(toNumber, "main").capabilities()
                    .contains(SemanticCapability.FOUNDATION_VALUES),
                "NUMBER_CONVERT claims FOUNDATION_VALUES (the module-level row)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 7. constructCoverage: the closed 23-row detector table + the S1 copy
    // =========================================================================

    static void testConstructCoverageRows() throws Exception {
        System.out.println("-- constructCoverage: every required-common-form row recorded verbatim --");

        Path tmp = Files.createTempDirectory("deal-manifest-coverage");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "helper.deal", """
                    export function helperFn(): int {
                      return 1
                    }
                    """,
                "main.deal", """
                    import * as time from "std/time"
                    import * as helper from "./helper"

                    export class Point {
                      x: int = 1
                      y?: int
                    }

                    async function asyncOne(): int { return 1 }

                    export async function compute(a: int[]): int {
                      let sum: int = 0
                      let n: number = 1.5
                      let s: string = "a" + "b"
                      let t: string = `v${s}`
                      let neg: int = -sum
                      let eq: boolean = sum === 0 && n > 1.0
                      let arr: int[] = [1, 2]
                      let obj: table = { k: 1 }
                      let p: Point = { x: 2, y: 4 }
                      p.y = 3
                      delete obj.k
                      if (has(p.y)) { sum = 1 } else { sum = 2 }
                      let i: int = 0
                      while (i < a.length) {
                        if (i > 5) { break }
                        sum = sum + a[i]
                        i = i + 1
                      }
                      for (let j: int = 0; j < 2; j = j + 1) {
                        if (j === 1) { continue }
                        sum = sum + j
                      }
                      for (let v: int of a) { sum = sum + v }
                      let f: () => int = function(): int { return 1 }
                      let g: () => int = f
                      g()
                      sum = sum + g()
                      sum = sum + await asyncOne()
                      sum = sum + helper.helperFn()
                      let now: int = time.nowMillis()
                      try {
                        if (now < 0) { throw { code: "E", message: "x" } }
                      } catch (e) {
                        sum = 9
                      }
                      return sum
                    }

                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            SemanticRequirementManifest manifest = manifestOf(result, "main");
            check(manifest != null, "the coverage fixture produced a manifest");
            if (manifest == null) {
                return;
            }
            // The fixture exercises every one of the 23 rows carrying a
            // required common form (call, cross-module call,
            // unary/arithmetic/comparison, function
            // declaration/expression, and the K7 std.time row included) —
            // so the manifest records exactly those rows, verbatim from
            // T2's closed table. The cross-module call is a genuine
            // implementation-module call: a cataloged stdlib call records
            // the CALL row's STDLIB_CALL form, never CROSS_MODULE_CALL.
            EnumSet<ConstructKind> expected = EnumSet.allOf(ConstructKind.class);
            check(manifest.constructCoverage().keySet().equals(expected),
                "the module's reachable constructs produce exactly the 23 rows carrying a "
                    + "required common form; got "
                    + manifest.constructCoverage().keySet());
            for (Map.Entry<ConstructKind, List<deal.semantic.ir.SemanticOpKind>> entry
                    : manifest.constructCoverage().entrySet()) {
                check(entry.getValue().equals(entry.getKey().mappedOpKinds()),
                    "row " + entry.getKey() + " carries T2's mapped op kinds verbatim; got "
                        + entry.getValue());
            }
            check(manifest.constructCoverage()
                    .containsKey(ConstructKind.STDLIB_TIME_NOW_MILLIS),
                "the std/time.nowMillis coverage row is recorded like every other row");
            check(noConflictClaim(manifest) && claimsStdlibSemantics(manifest),
                "the coverage fixture (time.nowMillis() present) claims "
                    + "STDLIB_SEMANTICS through the cataloged call, never the retired "
                    + "conflict marker");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testSyntheticUnitCopy() throws Exception {
        System.out.println("-- S1: the unit producer copies the manifest rows at lowering start --");

        Path tmp = Files.createTempDirectory("deal-manifest-s1-copy");
        try {
            RequirementManifestResult result = compileAndCompute(tmp, Map.of(
                "main.deal", """
                    import * as time from "std/time"

                    export function main(): null {
                      time.nowMillis()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            SemanticRequirementManifest manifest = manifestOf(result, "main");
            check(manifest != null, "the S1 fixture produced a manifest");
            if (manifest == null) {
                return;
            }
            // The synthetic unit producer records the manifest's rows onto
            // the unit's own enum-keyed constructCoverage at lowering
            // start (S1) — the validator's pinned R-COVERAGE fact.
            LoweredModuleUnit unit = new LoweredModuleUnit(
                LoweredModuleUnit.FORMAT_VERSION,
                SemanticProfile.DEAL_V1_2_INT32,
                manifest.moduleId(),
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                    invocation().capabilityRegistryHash()),
                manifest.capabilities(),
                manifest.constructCoverage(),
                Map.of(),
                Map.of(),
                new ModuleInitPlan(List.of(), new BlockId(0)),
                ExportPlan.empty(),
                Map.of());
            check(unit.constructCoverage().equals(manifest.constructCoverage()),
                "the synthetic unit's constructCoverage equals the manifest's rows — the "
                    + "rows are the S1 coverage fact the unit producer records at "
                    + "lowering start");
            check(unit.constructCoverage().containsKey(ConstructKind.STDLIB_TIME_NOW_MILLIS),
                "the std/time.nowMillis row is carried onto the unit's coverage (S1) like "
                    + "every other recorded row");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 8. E6005 on inconsistent checked facts (T5 payload) + record guards
    // =========================================================================

    static void testE6005InconsistentFacts() {
        System.out.println("-- E6005: inconsistent checked/interface facts through T5 --");

        CompilerInvocation invocation = invocation();
        ModuleId mainId = new ModuleId("main");
        ModuleId ghostId = new ModuleId("ghost");
        ResolvedImport ghostImport = new ResolvedImport("g", "./ghost", ghostId,
            ExternalModuleKind.IMPLEMENTATION);

        // A T8 wrong-index-fact fault: the input module imports "./ghost"
        // but the index misses the ghost entry — the closure computation
        // cannot decide the Arm C gate and must fail closed.
        ProgramNode ast = new ProgramNode(span(),
            List.of(new ImportDeclaration(span(), "g", "./ghost")));
        CheckedModuleInput mainModule = new CheckedModuleInput(mainId,
            "src/main.deal", Path.of("src/main.deal"), ast,
            new CheckResult(Map.of(), new SymbolTable(), List.of()),
            List.of(ghostImport), List.of(), CheckedModuleKind.IMPLEMENTATION);
        CheckedProjectInput input = new CheckedProjectInput(invocation, mainId,
            List.of(mainModule), invocation.releaseStateHash());
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(
            ProjectInterfaceIndex.FORMAT_VERSION, Map.of(mainId,
                new ExternalModuleInterface(mainId, ExternalModuleKind.IMPLEMENTATION,
                    List.of(ghostImport), List.of(), List.of(),
                    InitializationMode.ONCE_AFTER_DEPENDENCIES)));

        RequirementManifestResult result =
            LoweringSupport.computeManifests(invocation, input, index);
        check(result != null && result.hasErrors() && result.manifests() == null,
            "an import resolving outside the dependency-ordered index fails the "
                + "computation (never a silent under-claim)");
        if (result == null || !result.hasErrors()) {
            return;
        }
        check(result.diagnostics().size() == 1,
            "exactly one E6005 diagnostic; got " + result.diagnostics().size());
        deal.diagnostics.CompilerDiagnostic diagnostic = result.diagnostics().get(0);
        check("E6005".equals(diagnostic.code())
                && diagnostic.diagnosticCode()
                    == deal.diagnostics.DiagnosticCode.E6005
                && "error".equals(diagnostic.severity()),
            "the diagnostic is error-severity E6005; got " + diagnostic.code()
                + "/" + diagnostic.severity());
        String message = diagnostic.message();
        check(message.contains("module 'main'")
                && message.contains("capability FOUNDATION_VALUES")
                && message.contains("validatorRule "
                    + LoweringSupport.MANIFEST_INTERNAL_ERROR_SENTINEL)
                && message.contains("semanticProfile LEGACY_SAFE_INT")
                && message.contains("irVersion " + LoweredModuleUnit.FORMAT_VERSION)
                && message.contains("origin LoweringSupport "
                    + LoweringSupport.MANIFEST_INTERNAL_ERROR_SENTINEL),
            "the E6005 message carries the prescribed LoweringFailureDetail payload "
                + "(module/capability/validatorRule/semanticProfile/irVersion/origin); got "
                + message);
    }

    static void testRecordAndClosedSetInvariants() {
        System.out.println("-- Record guards + closed-set invariants (T1/T2/T5/T8 faults) --");

        // Manifest record: FOUNDATION_VALUES is mandatory for every
        // implementation-module manifest (F3).
        try {
            new SemanticRequirementManifest(new ModuleId("m"),
                EnumSet.of(SemanticCapability.STDLIB_TIME_CONFLICT), Map.of(), false);
            fail("a manifest without FOUNDATION_VALUES must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a manifest without FOUNDATION_VALUES is rejected at construction");
        }
        try {
            new SemanticRequirementManifest(new ModuleId("m"),
                EnumSet.of(SemanticCapability.FOUNDATION_VALUES),
                Map.of(ConstructKind.STDLIB_TIME_NOW_MILLIS, List.of()), false);
            fail("a std/time.nowMillis coverage row diverging from its mapped op kinds "
                + "must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "the std/time.nowMillis row diverges from the closed mapped op kinds "
                + "and is rejected at construction");
        }
        // T2 fault: a corrupt construct→op detector row is rejected — the
        // manifest carries the closed table verbatim, never a mutated row.
        try {
            new SemanticRequirementManifest(new ModuleId("m"),
                EnumSet.of(SemanticCapability.FOUNDATION_VALUES),
                Map.of(ConstructKind.CALL,
                    List.of(deal.semantic.ir.SemanticOpKind.BINARY)), false);
            fail("a constructCoverage row diverging from T2's mapped op kinds must be "
                + "rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "a row diverging from T2's closed mapped op kinds is rejected at "
                + "construction");
        }
        try {
            new SemanticRequirementManifest(new ModuleId("m"),
                EnumSet.noneOf(SemanticCapability.class), Map.of(), false);
            fail("an empty-capability manifest must be rejected");
        } catch (IllegalArgumentException expected) {
            check(true, "an empty capability set is rejected at construction");
        }

        // T8 fault: an IMPLEMENTATION input entry without checks is a
        // producer defect rejected at record construction, never a
        // legitimate state.
        try {
            new CheckedModuleInput(new ModuleId("m"), "src/m.deal", Path.of("src/m.deal"),
                new ProgramNode(span(), List.of()), null, List.of(), List.of(),
                CheckedModuleKind.IMPLEMENTATION);
            fail("an IMPLEMENTATION input entry without a CheckResult must be rejected");
        } catch (RuntimeException expected) {
            check(true, "an IMPLEMENTATION input entry without checks is rejected at "
                + "record construction (T8 guard): " + expected.getClass().getSimpleName());
        }

        // T1 fault: the capability enum is closed — exactly the pinned
        // twelve values in the pinned order, no open/unknown member.
        List<String> pinnedCapabilities = List.of(
            "FOUNDATION_VALUES", "SIGNED_INT32", "CONTAINERS_AND_STRINGS",
            "DESCRIPTORS", "BOUNDARIES", "EVALUATION_ORDER", "BINDINGS", "CALLS",
            "STDLIB_SEMANTICS", "STDLIB_TIME_CONFLICT", "CLASSES", "MODULES");
        List<String> actual = new ArrayList<>();
        for (SemanticCapability capability : SemanticCapability.values()) {
            actual.add(capability.name());
        }
        check(actual.equals(pinnedCapabilities),
            "SemanticCapability is exactly the pinned closed set in the pinned order; got "
                + actual);
        check(SemanticCapability.class.isEnum(),
            "SemanticCapability is an enum — a manifest admitting an out-of-set "
                + "capability is impossible at the type level");
    }

    // =========================================================================
    // 9. Determinism + no frontend mutation
    // =========================================================================

    static void testDeterminismByteIdentical() throws Exception {
        System.out.println("-- Determinism: byte-identical manifests across repeated builds --");

        Path tmp = Files.createTempDirectory("deal-manifest-determinism");
        try {
            String source = """
                import * as time from "std/time"

                export class Point {
                  x: int = 1
                  y?: int
                }

                export function main(): null {
                  let p: Point = { x: 2, y: 3 }
                  let g: () => int = time.nowMillis
                  g()
                  return null
                }
                """;
            RequirementManifestResult first = compileAndCompute(tmp.resolve("first"),
                Map.of("main.deal", source), "main.deal");
            RequirementManifestResult second = compileAndCompute(tmp.resolve("second"),
                Map.of("main.deal", source), "main.deal");
            if (first == null || second == null) {
                return;
            }
            check(first.manifests().size() == second.manifests().size(),
                "both builds produce one manifest per implementation module");
            for (int index = 0;
                    index < Math.min(first.manifests().size(), second.manifests().size());
                    index++) {
                SemanticRequirementManifest a = first.manifests().get(index);
                SemanticRequirementManifest b = second.manifests().get(index);
                check(a.moduleId().equals(b.moduleId())
                        && a.capabilities().equals(b.capabilities())
                        && a.constructCoverage().equals(b.constructCoverage()),
                    "manifest " + index + " is equal across builds");
                check(a.canonicalText().equals(b.canonicalText()),
                    "manifest " + index + " serializes byte-identically across builds");
                check(CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(
                            a.toCanonicalJson()))
                        .equals(CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(
                            b.toCanonicalJson()))),
                    "manifest " + index + " digests are stable across builds");
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testNoFrontendMutationAndRecompute() throws Exception {
        System.out.println("-- Read-only: recomputation is identical and the frontend is untouched --");

        Path tmp = Files.createTempDirectory("deal-manifest-readonly");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            String source = """
                import * as time from "std/time"

                export function main(): null {
                  time.nowMillis()
                  return null
                }
                """;
            Files.writeString(src.resolve("main.deal"), source);
            CompilationOrchestrator orchestrator =
                harnessOrchestrator(src.resolve("main.deal").toAbsolutePath(),
                    tmp.resolve("build"));
            boolean ok = orchestrator.compile();
            check(ok, "the fixture compiles: " + orchestrator.diagnostics());
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            if (!ok || checked == null || checked.hasErrors()) {
                return;
            }
            CheckedProjectInput input = checked.input();
            String dumpBefore = IrDumper.dump(
                input.modules().get(0).ast(), input.modules().get(0).checks(),
                input.modules().get(0).moduleId().path());

            RequirementManifestResult recomputed = LoweringSupport.computeManifests(
                orchestrator.invocation(), input, checked.index());
            check(recomputed != null && !recomputed.hasErrors(),
                "recomputation over the same checked project succeeds");
            RequirementManifestResult original = orchestrator.requirementManifests();
            check(original != null && recomputed.manifests().equals(original.manifests()),
                "recomputation over the same checked project is identical (the "
                    + "dependency-ordered pass is deterministic)");

            String dumpAfter = IrDumper.dump(
                input.modules().get(0).ast(), input.modules().get(0).checks(),
                input.modules().get(0).moduleId().path());
            check(dumpBefore.equals(dumpAfter),
                "the AST/CheckResult facts are byte-unchanged after manifest computation "
                    + "(no frontend mutation)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 10. Combined dependencies (T1/T2/T5/T8)
    // =========================================================================

    static void testCombinedDependencies() throws Exception {
        System.out.println("-- Combined T1/T2/T5/T8: full pipeline on the wrapper scenario --");

        Path tmp = Files.createTempDirectory("deal-manifest-combined");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("a.deal"), """
                import * as time from "std/time"

                export function getNow(): () => int {
                  return time.nowMillis
                }
                """);
            Files.writeString(src.resolve("main.deal"), """
                import * as a from "./a"

                export function main(): null {
                  let g: () => int = a.getNow()
                  g()
                  return null
                }
                """);
            CompilationOrchestrator orchestrator =
                harnessOrchestrator(src.resolve("main.deal").toAbsolutePath(),
                    tmp.resolve("build"));
            boolean ok = orchestrator.compile();
            check(ok, "the wrapper scenario compiles end to end: " + orchestrator.diagnostics());
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            check(checked != null && !checked.hasErrors(),
                "T8 produced exactly one checked project + index with no diagnostics: "
                    + (checked == null ? "null" : checked.diagnostics()));
            RequirementManifestResult manifests = orchestrator.requirementManifests();
            check(manifests != null && !manifests.hasErrors(),
                "the manifest phase produced exactly one result with no diagnostics: "
                    + (manifests == null ? "null" : manifests.diagnostics()));
            if (!ok || checked == null || checked.hasErrors()
                    || manifests == null || manifests.hasErrors()) {
                return;
            }
            check(checked.input().releaseStateHash()
                    .equals(orchestrator.invocation().releaseStateHash()),
                "T8 recorded the invocation's releaseStateHash verbatim");
            check(manifests.manifests().stream()
                    .allMatch(m -> m.capabilities().contains(SemanticCapability.FOUNDATION_VALUES)
                        && m.capabilities().stream()
                            .allMatch(c -> EnumSet.allOf(SemanticCapability.class).contains(c))
                        && m.constructCoverage().entrySet().stream()
                            .allMatch(e -> e.getValue().equals(e.getKey().mappedOpKinds()))),
                "every manifest carries only closed T1 capabilities (FOUNDATION_VALUES "
                    + "included) and verbatim T2 coverage rows");
            check(noConflictClaim(manifestOf(manifests, "a"))
                    && noConflictClaim(manifestOf(manifests, "main")),
                "the wrapper scenario carries no STDLIB_TIME_CONFLICT claim in either "
                    + "module (the retired access/propagation arms never fire)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 11. ISSUE-0239 E10 plan-time arms: bytes values, class literals,
    //     dynamic calls, nested functions, adapters, uncalled declarations
    // =========================================================================

    static void testE10BytesValueArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: bytes-typed values claim "
            + "CONTAINERS_AND_STRINGS --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-bytes");
        try {
            RequirementManifestResult result = compileAndCompute(tmp,
                Map.of("main.deal", """
                    export function test_bytes_length(): null {
                      let n: int = 3;
                      let b: bytes = bytes(n);
                      if (b.length !== 3) {
                        throw { code: "TEST_FAIL", message: "bytes: length mismatch" };
                      }
                      return null;
                    }

                    export function main(): null {
                      return null;
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(manifestOf(result, "main").capabilities().contains(
                    SemanticCapability.CONTAINERS_AND_STRINGS),
                "the bytes(...) call and the bytes .length read claim "
                    + "CONTAINERS_AND_STRINGS (ISSUE-0158 boundary, never E6005): "
                    + manifestOf(result, "main").capabilities());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10ClassLiteralArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: a class-typed object literal claims "
            + "CLASSES --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-classlit");
        try {
            RequirementManifestResult result = compileAndCompute(tmp,
                Map.of("main.deal", """
                    export function main(): null {
                      throw { code: "TEST_FAIL", message: "boom" }
                    }
                    """), "main.deal");
            if (result != null) {
                check(manifestOf(result, "main").capabilities().contains(
                        SemanticCapability.CLASSES),
                    "the builtin Error literal of the throw claims CLASSES at the "
                        + "literal position (no declaring declaration exists): "
                        + manifestOf(result, "main").capabilities());
            }
            // ISSUE-0619: the fixture's only remaining blocker was the builtin
            // Error construct, so the same source compiles through the
            // release-owned production pipeline and its artifact executes.
            productionAccept(tmp.resolve("production"), Map.of("main.deal", """
                export function main(): null {
                  throw { code: "TEST_FAIL", message: "boom" }
                }
                """), "main.deal",
                "the builtin-Error-only E10 arm", "TEST_FAIL");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10DynamicCallArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: a call of a function-typed variable "
            + "claims CALLS --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-dyncall");
        try {
            RequirementManifestResult result = compileAndCompute(tmp,
                Map.of("main.deal", """
                    export function main(): null {
                      let f: () => int = function(): int { return 1 }
                      f()
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(manifestOf(result, "main").capabilities().contains(
                    SemanticCapability.CALLS),
                "the call of the function-typed local claims CALLS (dynamic "
                    + "resolution is ISSUE-0531's): "
                    + manifestOf(result, "main").capabilities());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10NestedFunctionArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: a nested function declaration claims "
            + "CALLS --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-nested");
        try {
            RequirementManifestResult result = compileAndCompute(tmp,
                Map.of("main.deal", """
                    export function main(): null {
                      function down(n: int): int {
                        if (n === 0) { return 0; }
                        return down(n - 1);
                      }
                      down(2)
                      return null
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(manifestOf(result, "main").capabilities().contains(
                    SemanticCapability.CALLS),
                "the nested local function declaration (recursion shape) claims "
                    + "CALLS: " + manifestOf(result, "main").capabilities());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10AdapterCreationArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: an adapter-creation position claims "
            + "CALLS --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-adapter");
        try {
            RequirementManifestResult result = compileAndCompute(tmp,
                Map.of("main.deal", """
                    export function main(): null {
                      let f: (a: int, b: int) => int = one
                      f(1, 2)
                      return null
                    }
                    function one(x: int): int {
                      return x
                    }
                    """), "main.deal");
            if (result == null) {
                return;
            }
            check(manifestOf(result, "main").capabilities().contains(
                    SemanticCapability.CALLS),
                "the assignable-but-not-exact initializer position produces "
                    + "FUNCTION_ADAPT and claims CALLS (the closed D15 creation "
                    + "rule): " + manifestOf(result, "main").capabilities());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10UncalledDeclarationArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: an uncalled non-exported declared "
            + "function claims CALLS; a called one does not --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-uncalled");
        try {
            RequirementManifestResult uncalled = compileAndCompute(tmp.resolve("uncalled"),
                Map.of("main.deal", """
                    function orphan(): int { return 1 }

                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (uncalled != null) {
                check(manifestOf(uncalled, "main").capabilities().contains(
                        SemanticCapability.CALLS),
                    "the never-called non-exported declaration claims CALLS (its "
                        + "single return boundary names no invocation): "
                        + manifestOf(uncalled, "main").capabilities());
            }
            RequirementManifestResult called = compileAndCompute(tmp.resolve("called"),
                Map.of("main.deal", """
                    function helper(x: int): int {
                      return x
                    }

                    export function main(): null {
                      helper(1)
                      return null
                    }
                    """), "main.deal");
            if (called != null) {
                check(claimsSignedInt32(manifestOf(called, "main")),
                    "the called non-exported declaration claims exactly "
                        + "FOUNDATION_VALUES + SIGNED_INT32 (one call site, no CALLS "
                        + "claim): " + manifestOf(called, "main").capabilities());
            }
            // The declaration-order-independence pin (ISSUE-0239 E10):
            // the identical module with the entry function declared
            // first (the conventional v1.2 layout) counts the call site
            // exactly like the callee-first layout — the call accounting
            // collects the called symbols over the whole statement walk
            // and the never-called arm runs after it, so a call site
            // walked before the callee's declaration is never lost.
            RequirementManifestResult calledMainFirst =
                compileAndCompute(tmp.resolve("called-main-first"),
                Map.of("main.deal", """
                    export function main(): null {
                      helper(1)
                      return null
                    }

                    function helper(x: int): int {
                      return x
                    }
                    """), "main.deal");
            if (calledMainFirst != null) {
                check(claimsSignedInt32(manifestOf(calledMainFirst, "main")),
                    "the main-first called non-exported declaration claims exactly "
                        + "FOUNDATION_VALUES + SIGNED_INT32 (declaration-order-"
                        + "independent call accounting, one call site, no CALLS "
                        + "claim): " + manifestOf(calledMainFirst, "main")
                            .capabilities());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testE10StoredFunctionExpressionArm() throws Exception {
        System.out.println("-- ISSUE-0239 E10 arm: a stored/embedded function "
            + "expression claims CALLS --");

        Path tmp = Files.createTempDirectory("deal-manifest-e10-storedfn");
        try {
            RequirementManifestResult binding = compileAndCompute(
                tmp.resolve("binding"), Map.of("main.deal", """
                    export function main(): null {
                      let g: () => int = function(): int { return 7 }
                      return null
                    }
                    """), "main.deal");
            if (binding != null) {
                check(manifestOf(binding, "main").capabilities().contains(
                        SemanticCapability.CALLS),
                    "a function expression stored in a binding initializer claims "
                        + "CALLS (its body's RETURN boundary names no invocation; "
                        + "F4 rule 4 reroutes LEGACY, never E6005): "
                        + manifestOf(binding, "main").capabilities());
            }
            RequirementManifestResult arrayElement = compileAndCompute(
                tmp.resolve("array"), Map.of("main.deal", """
                    export function main(): null {
                      let fs: (() => int)[] = [function(): int { return 7 }]
                      return null
                    }
                    """), "main.deal");
            if (arrayElement != null) {
                check(manifestOf(arrayElement, "main").capabilities().contains(
                        SemanticCapability.CALLS),
                    "a function expression embedded in an array literal element "
                        + "claims CALLS: "
                        + manifestOf(arrayElement, "main").capabilities());
            }
            RequirementManifestResult tableField = compileAndCompute(
                tmp.resolve("table"), Map.of("main.deal", """
                    export function main(): null {
                      let t: table = { f: function(): int { return 7 } }
                      return null
                    }
                    """), "main.deal");
            if (tableField != null) {
                check(manifestOf(tableField, "main").capabilities().contains(
                        SemanticCapability.CALLS),
                    "a function expression embedded in a table literal field "
                        + "claims CALLS: "
                        + manifestOf(tableField, "main").capabilities());
            }
            // The directly-invoked shape (an IIFE callee) claims CALLS
            // through the dynamic-callee arm (the callee is not a
            // statically-resolved identifier) — the stored-expression
            // arm's exemption never leaves an IIFE unclaimed.
            RequirementManifestResult iife = compileAndCompute(
                tmp.resolve("iife"), Map.of("main.deal", """
                    export function main(): null {
                      let x: int = (function(): int { return 7 })()
                      return null
                    }
                    """), "main.deal");
            if (iife != null) {
                check(manifestOf(iife, "main").capabilities().contains(
                        SemanticCapability.CALLS),
                    "a directly-invoked function expression claims CALLS through "
                        + "the dynamic-callee arm (never an unclaimed stored shape): "
                        + manifestOf(iife, "main").capabilities());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 12. ISSUE-0574 bytes guard: the bytesBearing marker and its
    //     canonical JSON key (determinism + the unchanged claim arm)
    // =========================================================================

    static void testBytesBearingMarkerDeterminism() throws Exception {
        System.out.println("-- ISSUE-0574 bytes guard: bytesBearing is a fixed "
            + "per-module boolean with a byte-identical canonical JSON key --");

        Path tmp = Files.createTempDirectory("deal-manifest-bytesmarker");
        try {
            String bytesSource = """
                export function test_bytes_length(): null {
                  let n: int = 3;
                  let b: bytes = bytes(n);
                  if (b.length !== 3) {
                    throw { code: "TEST_FAIL", message: "bytes: length mismatch" };
                  }
                  return null;
                }

                export function main(): null {
                  return null;
                }
                """;
            RequirementManifestResult first = compileAndCompute(tmp.resolve("first"),
                Map.of("main.deal", bytesSource), "main.deal");
            RequirementManifestResult second = compileAndCompute(tmp.resolve("second"),
                Map.of("main.deal", bytesSource), "main.deal");
            if (first == null || second == null) {
                return;
            }
            SemanticRequirementManifest bytesManifest = manifestOf(first, "main");
            check(bytesManifest != null && bytesManifest.bytesBearing(),
                "the bytes-bearing module's manifest carries bytesBearing=true "
                    + "(exactly scan.bytesInContainer || scan.bytesValue)");
            check(bytesManifest != null && bytesManifest.capabilities().contains(
                    SemanticCapability.CONTAINERS_AND_STRINGS),
                "the unchanged claim arm still claims CONTAINERS_AND_STRINGS "
                    + "(the construct-ownership fact): "
                    + bytesManifest.capabilities());
            if (bytesManifest == null) {
                return;
            }
            String textA = bytesManifest.canonicalText();
            String textB = bytesManifest.canonicalText();
            String textC = bytesManifest.canonicalText();
            check(textA.equals(textB) && textA.equals(textC),
                "repeated canonicalText() over the same bytes manifest is "
                    + "byte-identical");
            check(countOccurrences(textA, "\"bytesBearing\"") == 1
                    && textA.contains("\"bytesBearing\":true"),
                "the canonical JSON carries exactly one bytesBearing key with "
                    + "the fixed true value: " + textA);
            check(manifestOf(second, "main").canonicalText().equals(textA),
                "two builds of the same bytes project serialize the manifest "
                    + "byte-identically (a fixed per-module boolean, never a "
                    + "build-dependent value)");

            // Non-bytes control: the same triggers absent -> the fixed
            // false value, one key, byte-identical across repeats.
            RequirementManifestResult plain = compileAndCompute(tmp.resolve("plain"),
                Map.of("main.deal", """
                    export function main(): null {
                      return null
                    }
                    """), "main.deal");
            if (plain == null) {
                return;
            }
            SemanticRequirementManifest plainManifest = manifestOf(plain, "main");
            check(plainManifest != null && !plainManifest.bytesBearing(),
                "a non-bytes module's manifest carries bytesBearing=false");
            if (plainManifest == null) {
                return;
            }
            String plainTextA = plainManifest.canonicalText();
            check(countOccurrences(plainTextA, "\"bytesBearing\"") == 1
                    && plainTextA.contains("\"bytesBearing\":false"),
                "the non-bytes canonical JSON carries exactly one bytesBearing "
                    + "key with the fixed false value: " + plainTextA);
            check(plainManifest.canonicalText().equals(plainTextA),
                "the non-bytes manifest's canonical text is byte-identical "
                    + "across repeated computation");
        } finally {
            deleteRecursively(tmp);
        }
    }

    private static int countOccurrences(String text, String needle) {
        int count = 0;
        int index = 0;
        while ((index = text.indexOf(needle, index)) >= 0) {
            count++;
            index += needle.length();
        }
        return count;
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Lowering Support / Requirement Manifest Test (ISSUE-0289) ===\n");

        testDirectCallClaimsStdlibSemantics();
        testValuePositionReadClaimsNothing();
        testRetiredTriggerTableAlias();
        testRetiredTriggerParameterPassthrough();
        testRetiredTriggerCrossModuleTableEscape();
        testRetiredTriggerTableReExportChain();
        testRetiredTriggerWrapperEscape();
        testRetiredTriggerPropagationChain();
        testNoAccessImporterDoesNotClaim();
        testAliasJoinExactness();
        testRetiredOverClaimDirectImporter();
        testRetiredOverClaimClosureMember();
        testRetiredOverClaimImporter();
        testModulesImportClaim();
        testSignedInt32LiteralClaims();
        testSignedInt32UnaryBinaryClaims();
        testIntrinsicConversionClaims();
        testConstructCoverageRows();
        testSyntheticUnitCopy();
        testE6005InconsistentFacts();
        testRecordAndClosedSetInvariants();
        testDeterminismByteIdentical();
        testNoFrontendMutationAndRecompute();
        testCombinedDependencies();
        testE10BytesValueArm();
        testE10ClassLiteralArm();
        testE10DynamicCallArm();
        testE10NestedFunctionArm();
        testE10AdapterCreationArm();
        testE10UncalledDeclarationArm();
        testE10StoredFunctionExpressionArm();
        testBytesBearingMarkerDeterminism();
        testProductionInvocationTimeDrive();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
