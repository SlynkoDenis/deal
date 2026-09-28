package deal.test;

import deal.Main;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.module.CompilationOrchestrator;
import deal.project.StrictManifestParser;
import deal.publication.PublicationStager;
import deal.semantic.ArtifactOwner;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.MigrationPlanner;
import deal.semantic.ModuleRoute;
import deal.semantic.ModuleRoutePlan;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.RoutePlanResult;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.StagedArtifact;
import deal.semantic.Target;
import deal.semantic.TargetModuleAbi;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FunctionSignatureAbi;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SyncInvocationEntry;

import deal.ast.ArrayLiteralExpr;
import deal.ast.AssignmentExpr;
import deal.ast.AwaitExpression;
import deal.ast.BinaryExpr;
import deal.ast.Block;
import deal.ast.CallExpr;
import deal.ast.Either;
import deal.ast.ExportDeclaration;
import deal.ast.ExpressionNode;
import deal.ast.ExpressionStatement;
import deal.ast.FunctionDeclaration;
import deal.ast.FunctionExpr;
import deal.ast.HasExpr;
import deal.ast.IfStatement;
import deal.ast.IndexExpr;
import deal.ast.MemberAccessExpr;
import deal.ast.ObjectLiteralExpr;
import deal.ast.ProgramNode;
import deal.ast.Property;
import deal.ast.ReturnStatement;
import deal.ast.Span;
import deal.ast.StatementNode;
import deal.ast.TemplateLiteralExpr;
import deal.ast.UnaryExpr;
import deal.ast.VariableDeclaration;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.SharedValueSemantics;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Verifies the ISSUE-0292 integration wiring (foundation F8; Sequencing
 * item 11): one combined flow drives a full compiler invocation through
 * profile selection (T4) → the orchestrator's checked project + interface
 * index (T8) → requirement manifests (T9) → route plan (T10) → a
 * synthetic validated unit (T2 records + T3 digests, validated through
 * T6) → active ABI validation and transactional publication (T11 with
 * synthetically completed ABI records) — and fails when any constituent is broken.
 *
 * <p>Tests:
 * <ol>
 *   <li>Happy path: {@code CompilationOrchestrator.compile()} resolves the
 *       internal {@code COMMON_SHADOW + DEAL_V1_2_INT32} invocation, the
 *       foundation phase runs after phase 3 and before phase 4 (exactly
 *       one checked project input, one interface index, one manifest set,
 *       one route plan), phase 4 public dispatch is unchanged (the
 *       retained artifacts are emitted), and the internal shadow harness
 *       completes the flow through a synthetic validated unit into an
 *       atomically published artifact set.</li>
 *   <li>Fault-injection matrix: each variant faults exactly one
 *       constituent and asserts the combined flow fails on that
 *       constituent with the named defect — wrong profile resolution
 *       (E6005 {@code LOWER_LEGACY_PROFILE_REJECTED} at the lowering
 *       boundary), corrupted checked project/index (planner E6005
 *       {@code ROUTE_INTERNAL_ERROR_SENTINEL}), wrong manifest claim
 *       (ABI validator E6005 {@code ABI_OWNER_ROUTE_MISMATCH}), wrong route
 *       plan (validator E6005 {@code ABI_EDGE_MISSING}), an invalid
 *       synthetic unit (validator E6005 {@code R-PROFILE}), and an
 *       incomplete ABI record (validator E6005
 *       {@code ABI_MISSING_LOAD_KEY}).</li>
 *   <li>Legacy-profile lowering rejection (F1 verification 1): a lowering
 *       request carrying {@code LEGACY_SAFE_INT} is rejected at the
 *       pipeline boundary with E6005 through T5/T1 and the prescribed
 *       {@code LoweringFailureDetail} payload.</li>
 *   <li>Verbose-report wiring: a verbose invocation prints purpose,
 *       profile, release state, and the release-state hash equal to the
 *       invocation record field; a non-verbose invocation still records
 *       the hash on the invocation.</li>
 *   <li>A1 matrix: the provider factories admit the closed
 *       purpose × profile × release-state matrix ({@code PUBLIC_BUILD}
 *       derivation-only; {@code COMMON_SHADOW} requires an explicit
 *       {@code DEAL_V1_2_INT32} under any release state;
 *       {@code LEGACY_REGRESSION} requires an explicit
 *       {@code LEGACY_SAFE_INT} under any release state), each
 *       wrong-profile combination is rejected at resolution and at the
 *       {@code CompilerInvocation} record guard.</li>
 *   <li>ReleaseConfiguration consumers (A2):
 *       {@code CURRENT_RELEASE_STATE} is pinned to
 *       {@code V1_2_ACTIVE} (the committed E12 flip) with the release
 *       registry carrying the E12 promotion list;
 *       {@code deal/Main.java} and
 *       {@code CompilationOrchestrator.defaultInvocation()} both consume
 *       the constant with no hardcoded release-state literal remaining;
 *       the default invocation and the CLI path resolve the public build
 *       from the release configuration.</li>
 *   <li>Activated gate + rollback owned halves (A2/A3): a
 *       {@code PRE_ACTIVATION} public build of an int-using module
 *       derives {@code LEGACY_SAFE_INT} with an all-LEGACY plan and
 *       empty {@code shadowModules} (the internal matrix row — never a
 *       post-activation rollback target); the post-flip
 *       {@code V1_2_ACTIVE} public build over the promoted release
 *       registry derives {@code DEAL_V1_2_INT32} and routes the
 *       int-using module {@code SHARED} (F4 rule 4 reachable); a
 *       {@code V1_2_ACTIVE} public build over the all-SHADOW release
 *       registry produces the route-only terminal state (profile
 *       {@code DEAL_V1_2_INT32}, release state {@code V1_2_ACTIVE},
 *       source/AST unchanged, only routes LEGACY); no provider, record,
 *       or guard path revives a legacy public profile after
 *       activation.</li>
 *   <li>Capability-registry transition rollback observation
 *       (D4 steps 1-11 + D5; ISSUE-0413): a promoted registry
 *       routes the import-free int-using fixture module
 *       {@code SHARED} over the real planner; a one-capability
 *       {@code PROMOTED → SHADOW} demotion reroutes it
 *       {@code LEGACY} at plan time, before emission, with zero
 *       diagnostics, changing only {@code ModuleRoutePlan.entries}
 *       among decision-content fields; every recorded/derived hash
 *       recomputes and differs; source/AST stay byte-identical;
 *       the D5 boundary negatives hold.</li>
 *   <li>Wiring proof (A1): an orchestrator compile with
 *       {@code COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION} passes
 *       phase 3.7 and returns an all-LEGACY route plan with empty
 *       {@code shadowModules} (provider + record guard + planner guard +
 *       F4 rules through the real orchestrator).</li>
 *   <li>SignedInt32 integration verification (ISSUE-0398; design name
 *       {@code SignedInt32IntegrationTest}, I6 part 4 + Verification 6):
 *       the fixed {@link SignedInt32Corpus} runs on all four
 *       constituents — the profile-aware parser, the shared
 *       value-semantics primitive, the retained LuaJIT subprocess, and
 *       the retained JVM subprocess — and every case agrees per the
 *       pinned outcome (code + origin compared; the pinned
 *       {@code int out of safe range} for the shared primitive and for
 *       the retained routes alike — the former two-template split is
 *       retired; raw
 *       messages never compared across sides). The activated-state gate
 *       facts are asserted (activated at {@code V1_2_ACTIVE}, the public
 *       build of an int-using module derives {@code DEAL_V1_2_INT32}
 *       with a SHARED plan over the promoted release registry and empty
 *       shadowModules, a re-armed {@code PRE_ACTIVATION} probe fails,
 *       the flip stays exactly the one {@code ReleaseConfiguration}
 *       constant edit plus the promotion list and is never re-edited),
 *       and each named constituent — parser, shared
 *       semantics, LuaJIT route, JVM route, provider matrix, release
 *       configuration, catalog, harness seam — is faulted in turn and
 *       proven to fail the verification (no hollow pass).</li>
 * </ol>
 */
public class FoundationIntegrationTest {

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

    public static void main(String[] args) {
        try {
            testFullPipelineIntegration();
            testFaultWrongProfileResolution();
            testFaultCorruptedCheckedProjectIndex();
            testFaultWrongManifestClaim();
            testFaultWrongRoutePlan();
            testFaultInvalidSyntheticUnit();
            testFaultIncompleteAbiRecord();
            testLegacyProfileLoweringRejection();
            testVerboseReportWiring();
            testA1MatrixResolutionAndRecordGuard();
            testReleaseConfigurationConsumers();
            testActivatedStateAndRollbackOwnedHalves();
            testCapabilityRegistryTransitionRollbackObservation();
            testCommonShadowPreActivationWiringProof();
            testProfileAwareParserWiringProof();
            SignedInt32IntegrationTest.runAll();
        } catch (Throwable t) {
            failed++;
            System.err.println("FAIL: unexpected " + t);
            t.printStackTrace();
        }
        System.out.println();
        System.out.println("FoundationIntegrationTest: " + passed + " passed, "
            + failed + " failed");
        System.exit(failed > 0 ? 1 : 0);
    }

    // =========================================================================
    // Shared fixtures
    // =========================================================================

    private static final ModuleId MOD_A = new ModuleId("a");
    private static final ModuleId MOD_MAIN = new ModuleId("main");

    private static final RuntimeDescriptor DESC_ADD = new RuntimeDescriptor.Func(
        List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.Int.INSTANCE),
        RuntimeDescriptor.Int.INSTANCE);
    private static final RuntimeDescriptor DESC_MAIN = new RuntimeDescriptor.Func(
        List.of(), RuntimeDescriptor.Null.INSTANCE);

    private static byte[] bytes(String text) {
        return text.getBytes(StandardCharsets.UTF_8);
    }

    private static void deleteRecursively(Path dir) throws IOException {
        if (!Files.exists(dir)) {
            return;
        }
        try (Stream<Path> walk = Files.walk(dir)) {
            List<Path> paths = walk.sorted(Comparator.reverseOrder()).toList();
            for (Path path : paths) {
                Files.deleteIfExists(path);
            }
        }
    }

    private static Map<String, byte[]> readTree(Path tree) throws IOException {
        Map<String, byte[]> contents = new LinkedHashMap<>();
        if (!Files.exists(tree)) {
            return contents;
        }
        try (Stream<Path> walk = Files.walk(tree)) {
            for (Path file : walk.filter(Files::isRegularFile).toList()) {
                String relative = tree.relativize(file).toString()
                    .replace(java.io.File.separatorChar, '/');
                contents.put(relative, Files.readAllBytes(file));
            }
        }
        return contents;
    }

    private static List<Path> siblingTrees(Path root, String marker) throws IOException {
        List<Path> trees = new ArrayList<>();
        try (Stream<Path> entries = Files.list(root.getParent())) {
            for (Path entry : entries.toList()) {
                String name = entry.getFileName().toString();
                if (name.startsWith(root.getFileName() + marker)
                        && Files.isDirectory(entry)) {
                    trees.add(entry);
                }
            }
        }
        return trees;
    }

    private static void checkNoSiblings(Path root, String what) throws IOException {
        List<Path> stage = siblingTrees(root, PublicationStager.STAGE_TREE_MARKER);
        List<Path> retired = siblingTrees(root, PublicationStager.RETIRED_TREE_MARKER);
        check(stage.isEmpty() && retired.isEmpty(),
            what + ": no staging/retired siblings remain (stage=" + stage
                + ", retired=" + retired + ")");
    }

    /** Asserts the prescribed E6005 {@code LoweringFailureDetail} payload. */
    private static void assertE6005Rule(CompilerDiagnostic diagnostic, String rule,
                                        String module, SemanticCapability capability,
                                        SemanticProfile profile, String origin) {
        check(diagnostic != null, rule + " produces a diagnostic");
        if (diagnostic == null) {
            return;
        }
        check("E6005".equals(diagnostic.code()), rule + " code is E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            rule + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            rule + " phase is BACKEND_LOWERING");
        check("error".equals(diagnostic.severity()), rule + " severity is error");
        String message = diagnostic.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " instantiates the registry-owned E6005 template (T5)");
        check(message.contains("module '" + module + "'"),
            rule + " names module '" + module + "'; got \"" + message + "\"");
        check(message.contains("capability " + capability),
            rule + " carries capability " + capability + "; got \"" + message + "\"");
        check(message.contains("validatorRule " + rule + ","),
            rule + " is named as the validator rule; got \"" + message + "\"");
        check(message.contains("semanticProfile " + profile),
            rule + " carries the semantic profile " + profile);
        check(message.contains("irVersion deal.semantic-ir/1"),
            rule + " carries the pinned irVersion");
        check(message.contains("origin " + origin),
            rule + " names the producing component '" + origin + "'");
    }

    /** The T2-record synthetic unit passing the closed T6 rules. */
    private static LoweredModuleUnit validUnit(ModuleId module, ProjectInterfaceIndex index,
                                               CompilerInvocation invocation) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, module, index.interfaceIndexDigest(),
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                invocation.capabilityRegistryHash()),
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            List.of());
    }

    /** The invalid synthetic unit: an interfaceHash contradicting the index (T6 R-PROFILE). */
    private static LoweredModuleUnit invalidUnit(ProjectInterfaceIndex index,
                                                 CompilerInvocation invocation) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MOD_MAIN, "corrupted-interface-hash",
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32,
                invocation.capabilityRegistryHash()),
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of(),
            List.of());
    }

    /** The synthetically completed stage-time record for legacy dependency a (F5/F6). */
    private static TargetModuleAbi completeAbiA(TargetModuleAbi planTime) {
        return new TargetModuleAbi(planTime.moduleId(), planTime.target(),
            planTime.artifactOwner(), planTime.semanticProfile(),
            planTime.classFactoryAbi(), planTime.classLayoutAbi(),
            Map.of("add", DESC_ADD), "a/artifact.lua", "a_init",
            Map.of("add", new FunctionSignatureAbi("add_wrapper", "(int, int) => int")),
            Map.of("add", new SyncInvocationEntry.AbiWrapper("add_wrapper")),
            List.of());
    }

    /** The emitted SHARED-owner ABI manifest of the shared entry module. */
    private static TargetModuleAbi emittedMainManifest() {
        return new TargetModuleAbi(MOD_MAIN, Target.LUAJIT, ArtifactOwner.SHARED,
            SemanticProfile.DEAL_V1_2_INT32,
            Map.of(), Map.of(), Map.of("main", DESC_MAIN),
            "main/artifact.lua", "main_init",
            Map.of("main", new FunctionSignatureAbi("main_wrapper", "() => null")),
            Map.of("main", new SyncInvocationEntry.AbiWrapper("main_wrapper")),
            List.of());
    }

    /** The forged wrong manifest claim: main claims STDLIB_TIME_CONFLICT (a T9 defect). */
    private static List<SemanticRequirementManifest> forgedConflictManifest(
            List<SemanticRequirementManifest> manifests) {
        List<SemanticRequirementManifest> forged = new ArrayList<>();
        for (SemanticRequirementManifest manifest : manifests) {
            if (manifest.moduleId().equals(MOD_MAIN)) {
                forged.add(new SemanticRequirementManifest(MOD_MAIN,
                    EnumSet.of(SemanticCapability.FOUNDATION_VALUES,
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                    manifest.constructCoverage(), manifest.bytesBearing()));
            } else {
                forged.add(manifest);
            }
        }
        return forged;
    }

    /** The corrupted interface index: module a dropped (a T8 defect). */
    private static ProjectInterfaceIndex corruptedIndex(ProjectInterfaceIndex index) {
        Map<ModuleId, ExternalModuleInterface> corrupted =
            new LinkedHashMap<>(index.modules());
        corrupted.remove(MOD_A);
        return new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION, corrupted);
    }

    // =========================================================================
    // The combined integration pipeline (Sequencing item 11)
    // =========================================================================

    /** The named single-constituent faults; exactly one per variant. */
    private enum Fault { NONE, PROFILE, INDEX, MANIFEST, PLAN, UNIT, ABI }

    /** The outcome of one combined-flow run: the result plus the pinned products. */
    private record PipelineRun(
        boolean ok,
        String failureStep,
        List<CompilerDiagnostic> diagnostics,
        CompilerInvocation invocation,
        CheckedProjectBuildResult checked,
        List<SemanticRequirementManifest> manifests,
        ProjectInterfaceIndex index,
        ModuleRoutePlan orchestratorPlan,
        ModuleRoutePlan harnessPlan,
        LoweredModuleUnit unit,
        String harnessPlanTextBeforeStaging,
        Path publicationRoot
    ) {

        static PipelineRun success(CompilerInvocation invocation,
                CheckedProjectBuildResult checked,
                List<SemanticRequirementManifest> manifests, ProjectInterfaceIndex index,
                ModuleRoutePlan orchestratorPlan, ModuleRoutePlan harnessPlan,
                LoweredModuleUnit unit, String harnessPlanTextBeforeStaging,
                Path publicationRoot) {
            return new PipelineRun(true, "complete", List.of(), invocation, checked,
                manifests, index, orchestratorPlan, harnessPlan, unit,
                harnessPlanTextBeforeStaging, publicationRoot);
        }

        static PipelineRun failure(String step, List<CompilerDiagnostic> diagnostics,
                CompilerInvocation invocation, CheckedProjectBuildResult checked,
                List<SemanticRequirementManifest> manifests, ProjectInterfaceIndex index,
                ModuleRoutePlan orchestratorPlan, ModuleRoutePlan harnessPlan,
                LoweredModuleUnit unit, String harnessPlanTextBeforeStaging,
                Path publicationRoot) {
            return new PipelineRun(false, step, diagnostics, invocation, checked, manifests,
                index, orchestratorPlan, harnessPlan, unit, harnessPlanTextBeforeStaging,
                publicationRoot);
        }
    }

    /**
     * The two-module fixture written into {@code tmp}: {@code a.deal}
     * exports {@code add(x, y)}, {@code main.deal} imports it and exports
     * {@code main(): null} — one real mixed edge (a legacy dependency of
     * the shared entry module).
     */
    private static Path writeProjectFixture(Path tmp) throws IOException {
        Path src = tmp.resolve("src");
        Files.createDirectories(src);
        Files.writeString(src.resolve("a.deal"), """
            export function add(x: int, y: int): int {
              return x + y
            }
            """);
        Files.writeString(src.resolve("main.deal"), """
            import * as a from "./a"

            export function main(): null {
              a.add(1, 2)
              return null
            }
            """);
        return src;
    }

    /**
     * Runs the complete combined flow once with at most one faulted
     * constituent:
     *
     * <ol>
     *   <li><b>T4 profile selection</b> — the internal
     *       {@code COMMON_SHADOW + DEAL_V1_2_INT32} invocation.</li>
     *   <li><b>Orchestrator (F8 wiring)</b> — phases 0-4 plus the
     *       foundation phase: exactly one checked project input + one
     *       interface index (T8), one manifest set (T9), one route plan
     *       (T10) per compile.</li>
     *   <li><b>Internal shadow harness (T10)</b> — shadow-request the
     *       entry module; the plan routes {@code a} LEGACY (the retained
     *       dependency) and {@code main} SHARED with one plan-time ABI
     *       record for {@code a}.</li>
     *   <li><b>T2/T3 + T6</b> — the synthetic validated unit built from
     *       the real index digest and the invocation's lowering-context
     *       facts, validated against the comparison facts.</li>
     *   <li><b>T11</b> — synthetically completed ABI records plus the
     *       active staged-artifact view, ABI-validated and atomically
     *       published through {@code PublicationStager}.</li>
     * </ol>
     *
     * @param tmp   the scratch directory (source, build, and publication
     *              root live inside it)
     * @param fault the single faulted constituent, or {@code NONE}
     * @return the run outcome; never null
     */
    private static PipelineRun runIntegratedPipeline(Path tmp, Fault fault)
            throws IOException {
        Path src = writeProjectFixture(tmp);
        Path entry = src.resolve("main.deal").toAbsolutePath();
        List<Path> roots = List.of(src.toAbsolutePath());
        Path stdlib = Path.of("std").toAbsolutePath().normalize();

        // T4: profile selection — the internal shadow invocation.
        CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
            CapabilityRegistry.releaseRegistry());

        // F8 wiring: the orchestrator carries the resolved invocation,
        // runs phases 0-4, and runs the foundation phase after phase 3
        // (checked project -> index -> manifests -> route plan) before
        // phase 4.
        Path outDir = tmp.resolve("build");
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(
            entry, outDir, false, false, false, false, Backend.LUAJIT, null,
            roots, null, null, invocation);
        if (!orchestrator.compile()) {
            return PipelineRun.failure("orchestrator", orchestrator.diagnostics(),
                invocation, null, List.of(), null, null, null, null, null, null);
        }
        CheckedProjectBuildResult checked = orchestrator.checkedProject();
        if (checked == null || checked.hasErrors()) {
            return PipelineRun.failure("checked-project",
                checked == null ? List.of() : checked.diagnostics(), invocation, checked,
                List.of(), null, null, null, null, null, null);
        }
        RequirementManifestResult manifestResult = orchestrator.requirementManifests();
        if (manifestResult == null || manifestResult.hasErrors()) {
            return PipelineRun.failure("manifests",
                manifestResult == null ? List.of() : manifestResult.diagnostics(),
                invocation, checked, List.of(), null, null, null, null, null, null);
        }
        List<SemanticRequirementManifest> manifests =
            new ArrayList<>(manifestResult.manifests());

        // Fault INDEX: the corrupted interface index handed to the planner.
        ProjectInterfaceIndex index = checked.index();
        if (fault == Fault.INDEX) {
            index = corruptedIndex(checked.index());
        }
        // Fault MANIFEST: the forged wrong claim handed to the planner.
        if (fault == Fault.MANIFEST) {
            manifests = forgedConflictManifest(manifests);
        }

        // T10 (internal COMMON_SHADOW harness): shadow-request the entry
        // module over the real checked project, index, and manifests.
        RoutePlanResult planned = MigrationPlanner.planRoutes(invocation,
            CapabilityRegistry.releaseRegistry(), checked.input(), index, manifests,
            Target.LUAJIT, Set.of(MOD_MAIN));
        if (planned.hasErrors()) {
            return PipelineRun.failure("route-plan", planned.diagnostics(), invocation,
                checked, manifests, index, orchestrator.routePlan() == null ? null
                    : orchestrator.routePlan().plan(), null, null, null, null);
        }
        ModuleRoutePlan harnessPlan = planned.plan();
        // Fault PLAN: the forged wrong plan handed to the stager — the
        // legacy dependency's ABI edge is dropped while main stays SHARED.
        if (fault == Fault.PLAN) {
            harnessPlan = new ModuleRoutePlan(harnessPlan.target(), harnessPlan.entries(),
                harnessPlan.shadowModules(), harnessPlan.bytesExceptions(), List.of(),
                harnessPlan.invocationHash(), harnessPlan.planId());
        }

        // T2/T3: the synthetic unit built from the real index digest and
        // the invocation's lowering-context facts.
        LoweredModuleUnit unit = validUnit(MOD_MAIN, index, invocation);
        if (fault == Fault.UNIT) {
            unit = invalidUnit(index, invocation);
        }

        // T6: validation against the comparison facts.
        SemanticIrValidator.ComparisonFacts facts = new SemanticIrValidator.ComparisonFacts(
            index.interfaceIndexDigest(), invocation.semanticProfile(),
            invocation.capabilityRegistryHash());
        Optional<CompilerDiagnostic> unitFailure = SemanticIrValidator.validate(unit, facts);
        if (unitFailure.isPresent()) {
            return PipelineRun.failure("unit-validation", List.of(unitFailure.get()),
                invocation, checked, manifests, index,
                orchestrator.routePlan() == null ? null : orchestrator.routePlan().plan(),
                harnessPlan, unit, null, null);
        }

        // T11: validate the completed ABI records against the active staged
        // artifact set, then publish those bytes through PublicationStager.
        List<TargetModuleAbi> abiEdges = new ArrayList<>();
        for (TargetModuleAbi planTime : harnessPlan.abiEdges()) {
            abiEdges.add(fault == Fault.ABI ? planTime : completeAbiA(planTime));
        }
        abiEdges.add(emittedMainManifest());
        List<StagedArtifact> stagedArtifacts = List.of(
            new StagedArtifact("a/artifact.lua", bytes("a-artifact")),
            new StagedArtifact("main/artifact.lua", bytes("main-artifact")));

        if (fault == Fault.PROFILE) {
            CompilerInvocation legacyInvocation = CompilerProfileProvider.resolve(
                ReleaseState.PRE_ACTIVATION, CapabilityRegistry.releaseRegistry());
            deal.semantic.SemanticLowerer.LoweringResult rejected =
                deal.semantic.SemanticLowerer.lowerModule(checked.input().modules().get(0),
                    legacyInvocation.semanticProfile(), Map.of(), index.interfaceIndexDigest(),
                    legacyInvocation.capabilityRegistryHash(),
                    deal.semantic.ir.SemanticIdAllocator.over(
                        checked.input().modules().stream().map(m -> m.moduleId()).toList()));
            return PipelineRun.failure("lowering", rejected.diagnostics(), invocation, checked,
                manifests, index,
                orchestrator.routePlan() == null ? null : orchestrator.routePlan().plan(),
                harnessPlan, unit, null, tmp.resolve("live"));
        }

        String planTextBefore = harnessPlan.canonicalText();
        Path root = tmp.resolve("live");
        Optional<CompilerDiagnostic> abiFailure = deal.semantic.TargetAbiValidator.validate(
            new deal.semantic.StagedArtifactSet(stagedArtifacts), harnessPlan, abiEdges, index,
            invocation.semanticProfile());
        if (abiFailure.isPresent()) {
            return PipelineRun.failure("abi-validation", List.of(abiFailure.get()), invocation,
                checked, manifests, index,
                orchestrator.routePlan() == null ? null : orchestrator.routePlan().plan(),
                harnessPlan, unit, planTextBefore, root);
        }
        try (PublicationStager publication = PublicationStager.forRoot(root)) {
            for (StagedArtifact artifact : stagedArtifacts) {
                publication.stage(artifact.name(), artifact.bytes());
            }
            publication.publish();
        }
        return PipelineRun.success(invocation, checked, manifests, index,
            orchestrator.routePlan() == null ? null : orchestrator.routePlan().plan(),
            harnessPlan, unit, planTextBefore, root);
    }

    // =========================================================================
    // 1. Happy path: the full combined flow
    // =========================================================================

    static void testFullPipelineIntegration() throws Exception {
        System.out.println("-- Full pipeline: profile -> checked project -> index -> "
            + "manifests -> route plan -> synthetic validated unit -> atomic publication --");

        Path tmp = Files.createTempDirectory("deal-foundation-integration");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.NONE);
            check(run.ok() && "complete".equals(run.failureStep()),
                "the combined flow succeeds end to end; step='" + run.failureStep()
                    + "' diagnostics=" + run.diagnostics());

            // T4: exactly one profile/purpose/release state per invocation.
            CompilerInvocation invocation = run.invocation();
            check(invocation.purpose() == InvocationPurpose.COMMON_SHADOW
                    && invocation.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                    && invocation.releaseState() == ReleaseState.V1_2_ACTIVE,
                "the invocation carries exactly one purpose/profile/release state");
            check(invocation.releaseStateHash().equals(
                    CompilerProfileProvider.deriveReleaseStateHash(
                        ReleaseState.V1_2_ACTIVE, invocation.capabilityRegistryHash())),
                "the invocation records the derived release-state hash");

            // T8: exactly one checked project input + one interface index.
            CheckedProjectInput input = run.checked().input();
            check(input.releaseStateHash().equals(invocation.releaseStateHash()),
                "the checked project records the invocation's releaseStateHash verbatim");
            check(input.modules().size() == 2,
                "the input covers exactly the two implementation modules; got "
                    + input.modules().size());
            check(new ArrayList<>(run.index().modules().keySet()).equals(
                    List.of(MOD_A, MOD_MAIN)),
                "the index covers the closure in dependency order; got "
                    + run.index().modules().keySet());

            // T9: exactly one manifest per implementation module.
            check(run.manifests().size() == 2,
                "the foundation phase computed exactly one manifest per implementation "
                    + "module; got " + run.manifests().size());
            check(run.manifests().get(0).moduleId().equals(MOD_A)
                    && run.manifests().get(1).moduleId().equals(MOD_MAIN),
                "the manifests are in dependency order");
            for (SemanticRequirementManifest manifest : run.manifests()) {
                check(manifest.capabilities().contains(SemanticCapability.FOUNDATION_VALUES)
                        && !manifest.capabilities().contains(
                            SemanticCapability.STDLIB_TIME_CONFLICT),
                    "manifest " + manifest.moduleId() + " claims FOUNDATION_VALUES and "
                        + "no STDLIB_TIME_CONFLICT (no time access in the fixture)");
            }

            // T10: the orchestrator's own plan (no shadow request) is
            // all-LEGACY; the internal shadow harness plan routes the
            // entry module SHARED with one plan-time ABI edge for a.
            ModuleRoutePlan orchestratorPlan = run.orchestratorPlan();
            check(orchestratorPlan != null
                    && orchestratorPlan.entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY)
                    && orchestratorPlan.shadowModules().isEmpty(),
                "the orchestrator's COMMON_SHADOW plan without shadow requests is "
                    + "all-LEGACY with no shadow entries");
            ModuleRoutePlan harnessPlan = run.harnessPlan();
            check(harnessPlan.entries().get(MOD_A) == ModuleRoute.LEGACY
                    && harnessPlan.entries().get(MOD_MAIN) == ModuleRoute.SHARED,
                "the shadow harness plan routes a LEGACY (retained) and main SHARED");
            check(harnessPlan.shadowModules().equals(Set.of(MOD_MAIN)),
                "the shadow harness plan records main as a shadow SHARED entry");
            check(harnessPlan.abiEdges().size() == 1
                    && harnessPlan.abiEdges().get(0).moduleId().equals(MOD_A)
                    && harnessPlan.abiEdges().get(0).artifactOwner()
                        == ArtifactOwner.RETAINED_LUAJIT
                    && harnessPlan.abiEdges().get(0).loadKey() == null,
                "the plan carries exactly one plan-time ABI record for a "
                    + "(RETAINED_LUAJIT, planner-owned fields only)");

            // T11: the atomically published live set equals the staged
            // content; no stale siblings; the nonce never enters the plan.
            Map<String, byte[]> live = readTree(run.publicationRoot());
            check(live.size() == 2
                    && Arrays.equals(live.get("a/artifact.lua"), bytes("a-artifact"))
                    && Arrays.equals(live.get("main/artifact.lua"), bytes("main-artifact")),
                "the published live set carries the staged artifacts byte-identically; "
                    + "got " + live.keySet());
            checkNoSiblings(run.publicationRoot(), "full pipeline");
            check(run.harnessPlan().canonicalText().equals(
                    run.harnessPlanTextBeforeStaging()),
                "the staging nonce never enters the plan record (byte-identical plan "
                    + "text)");

            // Phase 4 public dispatch is unchanged: the retained emitters
            // wrote their artifacts directly into the build root.
            check(Files.exists(tmp.resolve("build/main.lua"))
                    && Files.exists(tmp.resolve("build/a.lua")),
                "phase 4 public dispatch is unchanged (retained Lua artifacts exist)");

            // The combined flow is deterministic: a second identical run
            // publishes the identical set.
            PipelineRun second = runIntegratedPipeline(
                Files.createTempDirectory("deal-foundation-integration-2"), Fault.NONE);
            check(second.ok(), "the repeated combined flow succeeds: " + second.diagnostics());
            if (second.ok()) {
                check(second.harnessPlan().canonicalText().equals(
                        run.harnessPlan().canonicalText()),
                    "repeated builds produce byte-identical route plans");
                check(second.index().interfaceIndexDigest().equals(
                        run.index().interfaceIndexDigest()),
                    "repeated builds produce byte-identical interface indexes");
            }
            deleteRecursively(Path.of(second.publicationRoot().getParent().toString()));
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 2. Fault-injection matrix (each variant faults exactly one constituent)
    // =========================================================================

    static void testFaultWrongProfileResolution() throws Exception {
        System.out.println("-- Fault: wrong profile resolution (T4) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-profile");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.PROFILE);
            check(!run.ok() && "lowering".equals(run.failureStep()),
                "a wrongly resolved profile fails the combined flow at the lowering "
                    + "boundary; step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && deal.semantic.SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED.equals(
                        ruleOf(run.diagnostics().get(0))),
                "the named defect 'wrong profile resolution' is detected "
                    + "(LOWER_LEGACY_PROFILE_REJECTED); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
            if (!run.diagnostics().isEmpty()) {
                assertE6005Rule(run.diagnostics().get(0),
                    deal.semantic.SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED, MOD_A.toString(),
                    SemanticCapability.FOUNDATION_VALUES, SemanticProfile.LEGACY_SAFE_INT,
                    "SemanticLowerer");
            }
            check(!Files.exists(run.publicationRoot()),
                "the rejected lowering request publishes nothing (no live set)");
            checkNoSiblings(run.publicationRoot(), "wrong profile resolution");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testFaultCorruptedCheckedProjectIndex() throws Exception {
        System.out.println("-- Fault: corrupted checked project/index (T8) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-index");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.INDEX);
            check(!run.ok() && "route-plan".equals(run.failureStep()),
                "a corrupted interface index fails the combined flow at route planning; "
                    + "step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && "ROUTE_INTERNAL_ERROR_SENTINEL".equals(ruleOf(run.diagnostics().get(0))),
                "the named defect 'corrupted checked project/index' is detected "
                    + "(ROUTE_INTERNAL_ERROR_SENTINEL); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testFaultWrongManifestClaim() throws Exception {
        System.out.println("-- Fault: wrong manifest claim (T9) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-manifest");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.MANIFEST);
            check(!run.ok() && "abi-validation".equals(run.failureStep()),
                "a wrong manifest claim fails the combined flow at active ABI validation "
                    + "after rerouting the module LEGACY; step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && "ABI_OWNER_ROUTE_MISMATCH".equals(ruleOf(run.diagnostics().get(0))),
                "the named defect 'wrong manifest claim' is detected "
                    + "(ABI_OWNER_ROUTE_MISMATCH); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testFaultWrongRoutePlan() throws Exception {
        System.out.println("-- Fault: wrong route plan (T10) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-plan");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.PLAN);
            check(!run.ok() && "abi-validation".equals(run.failureStep()),
                "a wrong route plan fails the combined flow at staging (the legacy "
                    + "dependency's ABI edge is missing); step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && "ABI_EDGE_MISSING".equals(ruleOf(run.diagnostics().get(0))),
                "the named defect 'wrong route plan' is detected (ABI_EDGE_MISSING); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
            check(!Files.exists(run.publicationRoot()),
                "the wrong plan publishes nothing (no live set)");
            checkNoSiblings(run.publicationRoot(), "wrong route plan");
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testFaultInvalidSyntheticUnit() throws Exception {
        System.out.println("-- Fault: invalid synthetic unit (T2/T3/T6) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-unit");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.UNIT);
            check(!run.ok() && "unit-validation".equals(run.failureStep()),
                "an invalid synthetic unit fails the combined flow at T6 validation; "
                    + "step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && SemanticIrValidator.R_PROFILE.equals(ruleOf(run.diagnostics().get(0))),
                "the named defect 'invalid synthetic unit' is detected (R-PROFILE); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
            if (!run.diagnostics().isEmpty()) {
                assertE6005Rule(run.diagnostics().get(0), SemanticIrValidator.R_PROFILE,
                    MOD_MAIN.toString(), SemanticCapability.FOUNDATION_VALUES,
                    SemanticProfile.DEAL_V1_2_INT32, "SemanticIrValidator");
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testFaultIncompleteAbiRecord() throws Exception {
        System.out.println("-- Fault: incomplete ABI record (T11) --");
        Path tmp = Files.createTempDirectory("deal-foundation-fault-abi");
        try {
            PipelineRun run = runIntegratedPipeline(tmp, Fault.ABI);
            check(!run.ok() && "abi-validation".equals(run.failureStep()),
                "an incomplete ABI record fails the combined flow at stage-time "
                    + "validation; step='" + run.failureStep() + "'");
            check(!run.diagnostics().isEmpty()
                    && "ABI_MISSING_LOAD_KEY".equals(ruleOf(run.diagnostics().get(0))),
                "the named defect 'incomplete ABI record' is detected "
                    + "(ABI_MISSING_LOAD_KEY); got "
                    + run.diagnostics().stream().map(CompilerDiagnostic::message).toList());
            if (!run.diagnostics().isEmpty()) {
                assertE6005Rule(run.diagnostics().get(0),
                    "ABI_MISSING_LOAD_KEY", MOD_A.toString(), SemanticCapability.MODULES,
                    SemanticProfile.DEAL_V1_2_INT32, "TargetAbiValidator");
            }
            check(!Files.exists(run.publicationRoot()),
                "the incomplete record publishes nothing (no live set)");
            checkNoSiblings(run.publicationRoot(), "incomplete ABI record");
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** Extracts the {@code validatorRule} value from an E6005 message. */
    private static String ruleOf(CompilerDiagnostic diagnostic) {
        String message = diagnostic.message();
        int index = message.indexOf("validatorRule ");
        if (index < 0) {
            return null;
        }
        String rest = message.substring(index + "validatorRule ".length());
        int comma = rest.indexOf(',');
        return comma < 0 ? rest : rest.substring(0, comma);
    }

    // =========================================================================
    // 3. Legacy-profile lowering rejection (F1 verification 1)
    // =========================================================================

    static void testLegacyProfileLoweringRejection() throws Exception {
        System.out.println("-- Legacy-profile lowering rejection: LEGACY_SAFE_INT -> E6005 --");

        Path tmp = Files.createTempDirectory("deal-foundation-legacy-reject");
        try {
            // A valid T4 resolution whose profile LEGACY_SAFE_INT makes it
            // a rejected lowering request: lowering admits only
            // DEAL_V1_2_INT32 (F1).
            CompilerInvocation legacyInvocation = CompilerProfileProvider.resolve(
                ReleaseState.PRE_ACTIVATION, CapabilityRegistry.releaseRegistry());
            check(legacyInvocation.purpose() == InvocationPurpose.PUBLIC_BUILD
                    && legacyInvocation.semanticProfile() == SemanticProfile.LEGACY_SAFE_INT,
                "T4 resolves the public PRE_ACTIVATION invocation with "
                    + "LEGACY_SAFE_INT (inspectable for routing/regression)");

            Path src = writeProjectFixture(tmp);
            // ISSUE-0643 P10 item 3: the fixture carries a cross-module call
            // (a later-slice construct), while the suite's subject is the
            // legacy-profile lowering rejection — arm-independent, so the
            // orchestrator compile resolves the harness invocation.
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"),
                false, false, false, false, Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()), Path.of("std").toAbsolutePath(),
                null, CompilerProfileProvider.resolveCommonShadow(
                    SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                    CapabilityRegistry.releaseRegistry()));
            check(orchestrator.compile(),
                "the legacy-profile lowering fixture builds checked inputs");
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            var subject = checked.input().modules().stream()
                .filter(module -> module.moduleId().equals(MOD_MAIN)).findFirst().orElseThrow();
            deal.semantic.SemanticLowerer.LoweringResult outcome =
                deal.semantic.SemanticLowerer.lowerModule(subject,
                    legacyInvocation.semanticProfile(), Map.of(),
                    checked.index().interfaceIndexDigest(),
                    legacyInvocation.capabilityRegistryHash(),
                    deal.semantic.ir.SemanticIdAllocator.over(
                        checked.input().modules().stream().map(m -> m.moduleId()).toList()));

            check(outcome.hasErrors() && outcome.unit() == null,
                "a lowering request carrying LEGACY_SAFE_INT is rejected before IR exists");
            check(outcome.diagnostics().size() == 1,
                "the rejection is exactly one E6005; got " + outcome.diagnostics());
            assertE6005Rule(outcome.diagnostics().get(0),
                deal.semantic.SemanticLowerer.LOWER_LEGACY_PROFILE_REJECTED,
                MOD_MAIN.toString(), SemanticCapability.FOUNDATION_VALUES,
                SemanticProfile.LEGACY_SAFE_INT, "SemanticLowerer");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 4. Verbose-report wiring (F1/F8)
    // =========================================================================

    static void testVerboseReportWiring() throws Exception {
        System.out.println("-- Verbose report wiring: purpose/profile/release state/hash --");

        Path tmp = Files.createTempDirectory("deal-foundation-verbose");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("trivial.deal"),
                "export function main(): null { return null; }\n");
            Path entry = src.resolve("trivial.deal").toAbsolutePath();
            List<Path> roots = List.of(src.toAbsolutePath());
            CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                CapabilityRegistry.releaseRegistry());

            // Non-verbose path: the derived hash is recorded on the
            // invocation regardless of the report.
            CompilationOrchestrator quiet = new CompilationOrchestrator(
                entry, tmp.resolve("build-quiet"), false, false, false, false,
                Backend.LUAJIT, null, roots, null, null, invocation);
            ByteArrayOutputStream quietOut = new ByteArrayOutputStream();
            PrintStream originalOut = System.out;
            System.setOut(new PrintStream(quietOut, true, StandardCharsets.UTF_8));
            boolean quietOk;
            try {
                quietOk = quiet.compile();
            } finally {
                System.setOut(originalOut);
            }
            check(quietOk, "the non-verbose compile succeeds");
            check(quiet.invocation().equals(invocation)
                    && invocation.releaseStateHash().equals(
                        quiet.invocation().releaseStateHash()),
                "the non-verbose path still records the derived hash on the "
                    + "invocation record");
            check(!quietOut.toString(StandardCharsets.UTF_8).contains("Purpose:"),
                "the non-verbose report prints no invocation facts (display-only)");

            // Verbose path: the report prints the recorded facts and the
            // printed hash equals the invocation record field — the
            // recording location is the record, never the report.
            CompilationOrchestrator verbose = new CompilationOrchestrator(
                entry, tmp.resolve("build-verbose"), true, false, false, false,
                Backend.LUAJIT, null, roots, null, null, invocation);
            ByteArrayOutputStream verboseOut = new ByteArrayOutputStream();
            System.setOut(new PrintStream(verboseOut, true, StandardCharsets.UTF_8));
            boolean verboseOk;
            try {
                verboseOk = verbose.compile();
            } finally {
                System.setOut(originalOut);
            }
            check(verboseOk, "the verbose compile succeeds");
            String text = verboseOut.toString(StandardCharsets.UTF_8);
            check(text.contains("Purpose: " + invocation.purpose()),
                "the verbose report prints the purpose");
            check(text.contains("Semantic profile: " + invocation.semanticProfile()),
                "the verbose report prints the profile");
            check(text.contains("Release state: " + invocation.releaseState()),
                "the verbose report prints the release state");
            check(text.contains("Release-state hash: " + invocation.releaseStateHash()),
                "the verbose report prints the release-state hash equal to the "
                    + "invocation record field");
            check(verbose.invocation().releaseStateHash().equals(
                    invocation.releaseStateHash()),
                "the verbose path records the same derived hash on the invocation "
                    + "record");

            // The foundation phase runs in both paths: exactly one checked
            // project, one manifest set, and one route plan per compile.
            check(verbose.checkedProject() != null
                    && !verbose.checkedProject().hasErrors()
                    && quiet.checkedProject() != null
                    && !quiet.checkedProject().hasErrors(),
                "verbose and non-verbose compiles each build exactly one checked "
                    + "project + interface index");
            check(verbose.requirementManifests() != null
                    && verbose.requirementManifests().manifests().size() == 1
                    && verbose.routePlan() != null && !verbose.routePlan().hasErrors(),
                "the verbose compile computes exactly one manifest set and one route "
                    + "plan (foundation phase before phase 4)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 5. A1 matrix + record guard (provider factories, CompilerInvocation)
    // =========================================================================

    static void testA1MatrixResolutionAndRecordGuard() {
        System.out.println("-- A1 matrix: provider factories + CompilerInvocation record guard --");

        CapabilityRegistry registry = CapabilityRegistry.releaseRegistry();
        String registryHash = registry.capabilityRegistryHash();

        // PUBLIC_BUILD is derivation-only through resolve(releaseState,
        // registry) — the only PUBLIC_BUILD constructor.
        CompilerInvocation publicPre = CompilerProfileProvider.resolve(
            ReleaseState.PRE_ACTIVATION, registry);
        check(publicPre.purpose() == InvocationPurpose.PUBLIC_BUILD
                && publicPre.semanticProfile() == SemanticProfile.LEGACY_SAFE_INT
                && publicPre.releaseState() == ReleaseState.PRE_ACTIVATION,
            "PUBLIC_BUILD + PRE_ACTIVATION derives LEGACY_SAFE_INT");
        CompilerInvocation publicActive = CompilerProfileProvider.resolve(
            ReleaseState.V1_2_ACTIVE, registry);
        check(publicActive.purpose() == InvocationPurpose.PUBLIC_BUILD
                && publicActive.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                && publicActive.releaseState() == ReleaseState.V1_2_ACTIVE,
            "PUBLIC_BUILD + V1_2_ACTIVE derives DEAL_V1_2_INT32");

        // COMMON_SHADOW + DEAL_V1_2_INT32: admitted under both release states.
        CompilerInvocation shadowPre = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION, registry);
        check(shadowPre.purpose() == InvocationPurpose.COMMON_SHADOW
                && shadowPre.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                && shadowPre.releaseState() == ReleaseState.PRE_ACTIVATION,
            "COMMON_SHADOW + DEAL_V1_2_INT32 resolves under PRE_ACTIVATION");
        CompilerInvocation shadowActive = CompilerProfileProvider.resolveCommonShadow(
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE, registry);
        check(shadowActive.purpose() == InvocationPurpose.COMMON_SHADOW
                && shadowActive.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                && shadowActive.releaseState() == ReleaseState.V1_2_ACTIVE,
            "COMMON_SHADOW + DEAL_V1_2_INT32 resolves under V1_2_ACTIVE");

        // LEGACY_REGRESSION + LEGACY_SAFE_INT: admitted under both release
        // states (the retention window extends past activation).
        CompilerInvocation legacyPre = CompilerProfileProvider.resolveLegacyRegression(
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION, registry);
        check(legacyPre.purpose() == InvocationPurpose.LEGACY_REGRESSION
                && legacyPre.semanticProfile() == SemanticProfile.LEGACY_SAFE_INT
                && legacyPre.releaseState() == ReleaseState.PRE_ACTIVATION,
            "LEGACY_REGRESSION + LEGACY_SAFE_INT resolves under PRE_ACTIVATION");
        CompilerInvocation legacyActive =
            CompilerProfileProvider.resolveLegacyRegression(
                SemanticProfile.LEGACY_SAFE_INT, ReleaseState.V1_2_ACTIVE, registry);
        check(legacyActive.purpose() == InvocationPurpose.LEGACY_REGRESSION
                && legacyActive.semanticProfile() == SemanticProfile.LEGACY_SAFE_INT
                && legacyActive.releaseState() == ReleaseState.V1_2_ACTIVE,
            "LEGACY_REGRESSION + LEGACY_SAFE_INT resolves under V1_2_ACTIVE");

        // Wrong-profile combinations rejected at resolution, under both
        // release states.
        for (ReleaseState state : ReleaseState.values()) {
            try {
                CompilerProfileProvider.resolveCommonShadow(
                    SemanticProfile.LEGACY_SAFE_INT, state, registry);
                fail("COMMON_SHADOW + LEGACY_SAFE_INT + " + state + " must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "COMMON_SHADOW + LEGACY_SAFE_INT + " + state
                    + " is rejected at resolution");
            }
            try {
                CompilerProfileProvider.resolveLegacyRegression(
                    SemanticProfile.DEAL_V1_2_INT32, state, registry);
                fail("LEGACY_REGRESSION + DEAL_V1_2_INT32 + " + state
                    + " must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "LEGACY_REGRESSION + DEAL_V1_2_INT32 + " + state
                    + " is rejected at resolution");
            }
        }

        // The record guard: the matrix holds at the record, not only at
        // the factories.
        try {
            new CompilerInvocation(InvocationPurpose.COMMON_SHADOW,
                SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
                registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                    ReleaseState.PRE_ACTIVATION, registryHash));
            fail("the record must reject COMMON_SHADOW + LEGACY_SAFE_INT");
        } catch (IllegalArgumentException expected) {
            check(true, "the record guard rejects COMMON_SHADOW + LEGACY_SAFE_INT");
        }
        try {
            new CompilerInvocation(InvocationPurpose.LEGACY_REGRESSION,
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                    ReleaseState.V1_2_ACTIVE, registryHash));
            fail("the record must reject LEGACY_REGRESSION + DEAL_V1_2_INT32");
        } catch (IllegalArgumentException expected) {
            check(true, "the record guard rejects LEGACY_REGRESSION + DEAL_V1_2_INT32");
        }
        try {
            new CompilerInvocation(InvocationPurpose.PUBLIC_BUILD,
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
                registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                    ReleaseState.PRE_ACTIVATION, registryHash));
            fail("the record must reject a non-derived PUBLIC_BUILD profile");
        } catch (IllegalArgumentException expected) {
            check(true, "the record guard rejects a non-derived PUBLIC_BUILD profile");
        }

        // The provider-derived records are admitted by the record guard.
        new CompilerInvocation(InvocationPurpose.COMMON_SHADOW,
            SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
            registryHash, shadowPre.releaseStateHash());
        new CompilerInvocation(InvocationPurpose.LEGACY_REGRESSION,
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.V1_2_ACTIVE,
            registryHash, legacyActive.releaseStateHash());
        check(true, "the A1 provider-derived records are admitted by the record guard");
    }

    // =========================================================================
    // 6. ReleaseConfiguration consumers (A2)
    // =========================================================================

    static void testReleaseConfigurationConsumers() throws Exception {
        System.out.println("-- ReleaseConfiguration: single selection point consumed by Main + defaultInvocation --");


        // Fired (E12): the constant is pinned to V1_2_ACTIVE and the
        // release registry carries the E12 promotion derivation.
        check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
            "ReleaseConfiguration.CURRENT_RELEASE_STATE == V1_2_ACTIVE (the "
                + "committed E12 flip)");
        check(!ReleaseConfiguration.releaseCapabilityRegistry()
                .capabilityRegistryHash()
                .equals(CapabilityRegistry.releaseRegistry()
                    .capabilityRegistryHash()),
            "ReleaseConfiguration carries the promoted release registry (its "
                + "digest differs from the all-SHADOW release default)");
        check(ReleaseConfiguration.releaseCapabilityRegistry()
                .state(SemanticCapability.SIGNED_INT32, Target.LUAJIT)
                == CapabilityRegistry.State.PROMOTED,
            "the release registry promotes SIGNED_INT32 × LUAJIT (the E12 "
                + "promotion list)");
        // Both former hardcoded selection sites now read the constant:
        // no ReleaseState.PRE_ACTIVATION selection literal remains in
        // deal/Main.java or the orchestrator.
        String mainSource = Files.readString(Path.of("deal/Main.java"));
        check(mainSource.contains("ReleaseConfiguration.CURRENT_RELEASE_STATE")
                && !mainSource.contains("ReleaseState.PRE_ACTIVATION"),
            "deal/Main.java consumes ReleaseConfiguration.CURRENT_RELEASE_STATE and "
                + "carries no hardcoded release-state literal");
        String orchestratorSource =
            Files.readString(Path.of("deal/module/CompilationOrchestrator.java"));
        check(orchestratorSource.contains("ReleaseConfiguration.CURRENT_RELEASE_STATE")
                && !orchestratorSource.contains("ReleaseState.PRE_ACTIVATION"),
            "CompilationOrchestrator.defaultInvocation consumes "
                + "ReleaseConfiguration.CURRENT_RELEASE_STATE and carries no hardcoded "
                + "release-state literal");

        Path tmp = Files.createTempDirectory("deal-foundation-release-config");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"),
                "export function main(): null { return null; }\n");
            List<Path> roots = List.of(src.toAbsolutePath());

            // defaultInvocation: an orchestrator compile without an
            // explicit invocation resolves the public build from the
            // release configuration.
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                false, false, false, Backend.LUAJIT, null, roots,
                Path.of("std").toAbsolutePath().normalize());
            boolean ok = orchestrator.compile();
            check(ok, "the default-invocation compile succeeds: "
                + orchestrator.diagnostics());
            CompilerInvocation invocation = orchestrator.invocation();
            check(invocation.purpose() == InvocationPurpose.PUBLIC_BUILD
                    && invocation.releaseState()
                        == ReleaseConfiguration.CURRENT_RELEASE_STATE
                    && invocation.semanticProfile()
                        == CompilerProfileProvider.publicProfile(
                            ReleaseConfiguration.CURRENT_RELEASE_STATE),
                "defaultInvocation resolves PUBLIC_BUILD from "
                    + "ReleaseConfiguration.CURRENT_RELEASE_STATE");

            // deal/Main's CLI path consumes the same configuration.
            // ISSUE-0269: the production CLI locates exactly one
            // ancestor exact-v1.2 deal.json (the retired config-less
            // pipeline is gone), so the CLI project carries an injected
            // deal.json — same as every conformance harness project.
            Files.writeString(tmp.resolve("deal.json"),
                "{\"languageVersion\": \"1.2\", \"moduleRoots\": [\"src\"]}\n");
            ByteArrayOutputStream cliOut = new ByteArrayOutputStream();
            PrintStream originalOut = System.out;
            System.setOut(new PrintStream(cliOut, true, StandardCharsets.UTF_8));
            int rc;
            try {
                rc = Main.run(new String[]{"compile",
                    src.resolve("main.deal").toAbsolutePath().toString(),
                    "--output", tmp.resolve("build-cli").toString(), "--verbose"});
            } finally {
                System.setOut(originalOut);
            }
            check(rc == 0, "the CLI compile exits 0");
            check(cliOut.toString(StandardCharsets.UTF_8)
                    .contains("Release state: V1_2_ACTIVE"),
                "the CLI verbose report prints the release state read from the "
                    + "release configuration");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 7. Activated gate facts (A2, post-flip) + rollback owned halves (A3)
    // =========================================================================

    static void testActivatedStateAndRollbackOwnedHalves() throws Exception {
        System.out.println("-- Activated gate (A2, post-flip) + rollback owned "
            + "halves (A3) --");

        CapabilityRegistry registry = CapabilityRegistry.releaseRegistry();

        // Activated gate fact: E12's public flip is committed —
        // V1_2_ACTIVE with the promoted release registry.
        check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
            "the gate is activated at V1_2_ACTIVE (the committed E12 flip)");

        Path tmp = Files.createTempDirectory("deal-foundation-activated");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                export function add(x: int, y: int): int {
                  return x + y
                }

                export function main(): null {
                  return null
                }
                """);
            List<Path> roots = List.of(src.toAbsolutePath());
            Path entry = src.resolve("main.deal").toAbsolutePath();

            // The pre-activation matrix row remains an internal
            // derivation fact: PUBLIC_BUILD + PRE_ACTIVATION derives
            // LEGACY_SAFE_INT with an all-LEGACY plan and empty
            // shadowModules (F4 rule 3) — inspection only, never a
            // post-activation rollback target.
            CompilerInvocation publicPre = CompilerProfileProvider.resolve(
                ReleaseState.PRE_ACTIVATION, registry);
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, tmp.resolve("build"), false, false, false, false,
                Backend.LUAJIT, null, roots, Path.of("std").toAbsolutePath().normalize(),
                null, publicPre);
            boolean ok = orchestrator.compile();
            check(ok, "the PRE_ACTIVATION public int-using build compiles: "
                + orchestrator.diagnostics());
            check(orchestrator.invocation().semanticProfile()
                    == SemanticProfile.LEGACY_SAFE_INT,
                "a PRE_ACTIVATION public build of an int-using module derives "
                    + "LEGACY_SAFE_INT (the internal matrix row)");
            RoutePlanResult plan = orchestrator.routePlan();
            check(plan != null && !plan.hasErrors() && plan.plan() != null,
                "the PRE_ACTIVATION public build produces exactly one route plan");
            if (plan != null && !plan.hasErrors() && plan.plan() != null) {
                check(plan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                    "the PRE_ACTIVATION public plan is all-LEGACY (F4 rule 3)");
                check(plan.plan().shadowModules().isEmpty(),
                    "the PRE_ACTIVATION public plan has empty shadowModules "
                        + "(production SHARED ineligible)");
            }

            // The post-flip public build: V1_2_ACTIVE over the promoted
            // release registry derives DEAL_V1_2_INT32 and (ISSUE-0643 P4)
            // runs the production arm — no route plan is computed or
            // consulted, and exactly one project artifact is emitted with
            // zero retained emissions.
            CompilerInvocation postFlip = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE,
                ReleaseConfiguration.releaseCapabilityRegistry());
            check(postFlip.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                    && postFlip.releaseState() == ReleaseState.V1_2_ACTIVE
                    && postFlip.capabilityRegistryHash().equals(
                        ReleaseConfiguration.releaseCapabilityRegistry()
                            .capabilityRegistryHash()),
                "the post-flip public build derives DEAL_V1_2_INT32 under "
                    + "V1_2_ACTIVE with the promoted release registry hash recorded");
            CompilationOrchestrator postFlipOrchestrator =
                new CompilationOrchestrator(entry, tmp.resolve("build-postflip"),
                    false, false, false, false, Backend.LUAJIT, null, roots,
                    Path.of("std").toAbsolutePath().normalize(), null, postFlip);
            boolean postFlipOk = postFlipOrchestrator.compile();
            check(postFlipOk, "the post-flip public int-using build compiles: "
                + postFlipOrchestrator.diagnostics());
            check(postFlipOrchestrator.routePlan() == null,
                "the post-flip public build computes and consults no route plan "
                    + "(ISSUE-0643 P4: the production arm skips phase 3.7)");
            check(postFlipOrchestrator.semanticEmissionCount() == 1
                    && postFlipOrchestrator.retainedEmissionCount() == 0,
                "the post-flip public build records exactly one project emission "
                    + "and zero retained emissions");
            check(Files.exists(tmp.resolve("build-postflip/main.lua")),
                "the post-flip public build publishes the one project artifact");

            // ISSUE-0239 E10 plan-time arm: an exported function called
            // from source carries two invocation shapes under the
            // statically-resolved call machine (ISSUE-0531's runtime
            // selection), so the manifest claims CALLS and the harness
            // plan reroutes the module LEGACY — never E6005, never a
            // within-run fallback. The retained route compiles the
            // dual-shape module end to end. ISSUE-0643 P10 item 2: the
            // release-owned production invocation fails the same fixture
            // closed (the shape lowers to CONSTRUCT_UNLOWERED), so the
            // reroute subject is re-expressed through the harness
            // invocation.
            Path dualSrc = tmp.resolve("dualsrc");
            Files.createDirectories(dualSrc);
            Files.writeString(dualSrc.resolve("main.deal"), """
                export function add(x: int, y: int): int {
                  return x + y
                }

                export function main(): null {
                  add(2147483647, 1)
                  return null
                }
                """);
            CompilerInvocation dualInvocation =
                CompilerProfileProvider.resolveCommonShadow(
                    SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                    CapabilityRegistry.releaseRegistry());
            CompilationOrchestrator dualOrchestrator =
                new CompilationOrchestrator(
                    dualSrc.resolve("main.deal").toAbsolutePath(),
                    tmp.resolve("build-dual"), false, false, false, false,
                    Backend.LUAJIT, null, List.of(dualSrc.toAbsolutePath()),
                    Path.of("std").toAbsolutePath().normalize(), null,
                    dualInvocation);
            boolean dualOk = dualOrchestrator.compile();
            check(dualOk, "the dual-shape build compiles on the retained "
                + "harness route: " + dualOrchestrator.diagnostics());
            RequirementManifestResult dualManifests =
                dualOrchestrator.requirementManifests();
            check(dualManifests != null && !dualManifests.hasErrors()
                    && dualManifests.manifests().get(0).capabilities()
                        .contains(SemanticCapability.CALLS),
                "the dual-shape module's manifest claims CALLS (the ISSUE-0239 "
                    + "plan-time arm)");
            RoutePlanResult dualPlan = dualOrchestrator.routePlan();
            check(dualPlan != null && !dualPlan.hasErrors()
                    && dualPlan.plan() != null
                    && dualPlan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                "the dual-shape module reroutes LEGACY at plan time "
                    + "(CALLS not promoted — the parent verification-3 reroute, "
                    + "never E6005)");

            // ISSUE-0654: the release-owned production invocation realizes
            // the dual-shape fixture — the exported function called from
            // source runs its recorded EXTERNAL_ENTRY (the closed
            // CALL(EXTERNAL) SHARED_BODY cell) inside the one project
            // artifact — so it compiles and publishes its one artifact
            // while the harness invocation above keeps the plan-time
            // reroute subject.
            CompilationOrchestrator dualProduction = new CompilationOrchestrator(
                dualSrc.resolve("main.deal").toAbsolutePath(),
                tmp.resolve("build-dual-production"), false, false, false,
                false, Backend.LUAJIT, null,
                List.of(dualSrc.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null,
                CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE,
                    ReleaseConfiguration.releaseCapabilityRegistry()));
            boolean dualProductionOk = dualProduction.compile();
            check(dualProductionOk && dualProduction.diagnostics().isEmpty(),
                "the release-owned production invocation compiles the "
                    + "dual-shape fixture: " + dualProduction.diagnostics());
            check(dualProduction.routePlan() == null,
                "the production dual-shape compile consults no route plan");
            check(dualProductionOk
                    && dualProduction.semanticEmissionCount() == 1
                    && dualProduction.retainedEmissionCount() == 0,
                "the production dual-shape compile emits one project artifact "
                    + "and no retained artifact: semantic="
                    + dualProduction.semanticEmissionCount() + " retained="
                    + dualProduction.retainedEmissionCount());
            check(Files.exists(tmp.resolve("build-dual-production/main.lua")),
                "the production dual-shape compile stages its project artifact");

            // An internal V1_2_ACTIVE construction over the all-SHADOW
            // release default derives DEAL_V1_2_INT32 (the A1 row).
            CompilerInvocation internalActive = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, registry);
            check(internalActive.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                    && internalActive.releaseState() == ReleaseState.V1_2_ACTIVE,
                "an internal V1_2_ACTIVE construction derives DEAL_V1_2_INT32");

            // A3 owned halves: a V1_2_ACTIVE PUBLIC_BUILD invocation over
            // the all-SHADOW release registry derives DEAL_V1_2_INT32 and
            // produces an all-LEGACY plan — the route-only terminal state
            // a post-activation demotion produces (profile
            // DEAL_V1_2_INT32, release state V1_2_ACTIVE, source/AST
            // unchanged, only routes LEGACY).
            CompilationOrchestrator activeOrchestrator =
                new CompilationOrchestrator(entry, tmp.resolve("build-active"), false,
                    false, false, false, Backend.LUAJIT, null, roots,
                    Path.of("std").toAbsolutePath().normalize(), null, internalActive);
            boolean activeOk = activeOrchestrator.compile();
            check(activeOk, "the V1_2_ACTIVE build over the all-SHADOW registry "
                + "compiles: " + activeOrchestrator.diagnostics());
            RoutePlanResult activePlan = activeOrchestrator.routePlan();
            check(activePlan != null && !activePlan.hasErrors()
                    && activePlan.plan() != null,
                "the V1_2_ACTIVE all-SHADOW build produces exactly one route plan");
            if (activePlan != null && !activePlan.hasErrors()
                    && activePlan.plan() != null) {
                check(activeOrchestrator.invocation().semanticProfile()
                        == SemanticProfile.DEAL_V1_2_INT32
                        && activeOrchestrator.invocation().releaseState()
                            == ReleaseState.V1_2_ACTIVE,
                    "the rollback terminal state keeps DEAL_V1_2_INT32 under "
                        + "V1_2_ACTIVE");
                check(activePlan.plan().entries().values().stream()
                        .allMatch(route -> route == ModuleRoute.LEGACY),
                    "the V1_2_ACTIVE build over the all-SHADOW registry routes "
                        + "all-LEGACY (F4 rule 4: no PROMOTED capability)");
                check(activePlan.plan().shadowModules().isEmpty()
                        && activePlan.plan().abiEdges().isEmpty(),
                    "the route-only terminal plan carries no shadow entries and no "
                        + "ABI edges — only ModuleRoutePlan.entries hold routes");
            }
            if (ok && activeOk) {
                check(orchestrator.checkedProject().index().interfaceIndexDigest()
                        .equals(activeOrchestrator.checkedProject().index()
                            .interfaceIndexDigest()),
                    "source/AST are unchanged across the route-only terminal state "
                        + "(identical interface index digest)");
            }

            // No legacy-public revival path: V1_2_ACTIVE derives
            // DEAL_V1_2_INT32; no record and no factory revives a legacy
            // public profile after activation.
            check(CompilerProfileProvider.publicProfile(ReleaseState.V1_2_ACTIVE)
                    == SemanticProfile.DEAL_V1_2_INT32,
                "publicProfile(V1_2_ACTIVE) = DEAL_V1_2_INT32 (no derivation back "
                    + "to a legacy public profile)");
            check(CompilerProfileProvider.publicProfile(ReleaseState.PRE_ACTIVATION)
                    == SemanticProfile.LEGACY_SAFE_INT,
                "publicProfile(PRE_ACTIVATION) = LEGACY_SAFE_INT (the internal "
                    + "matrix row — never a production rollback target)");
            String registryHash = registry.capabilityRegistryHash();
            try {
                new CompilerInvocation(InvocationPurpose.LEGACY_REGRESSION,
                    SemanticProfile.DEAL_V1_2_INT32, ReleaseState.V1_2_ACTIVE,
                    registryHash, CompilerProfileProvider.deriveReleaseStateHash(
                        ReleaseState.V1_2_ACTIVE, registryHash));
                fail("a legacy-public revival record must be rejected");
            } catch (IllegalArgumentException expected) {
                check(true, "no record revives LEGACY_SAFE_INT under V1_2_ACTIVE");
            }
            try {
                CompilerProfileProvider.class.getDeclaredMethod("resolve",
                    InvocationPurpose.class, ReleaseState.class,
                    CapabilityRegistry.class);
                fail("the purpose-taking derivation factory must not exist");
            } catch (NoSuchMethodException expected) {
                check(true, "no provider factory derives a non-PUBLIC_BUILD profile "
                    + "from the release state alone (no revival path)");
            }
        } finally {
            deleteRecursively(tmp);
        }
    }
    // 7b. Capability-registry transition rollback observation
    // (ISSUE-0413: D4 steps 1-11 + D5 negatives)
    // =========================================================================

    /**
     * Plans one target through the real planner seam with fail-loud
     * reporting (E3): a planner guard {@code IllegalArgumentException}
     * (digest mismatch, A1-matrix inconsistency, shadow-request
     * violation, coverage mismatch) or a {@link RoutePlanResult} that is
     * null or carries diagnostics fails the test with the fact named —
     * never an anonymous stack trace, never a silent skip.
     */
    private static ModuleRoutePlan planOrFail(String name,
                                              CompilerInvocation invocation,
                                              CapabilityRegistry registry,
                                              CheckedProjectInput input,
                                              ProjectInterfaceIndex index,
                                              List<SemanticRequirementManifest> manifests,
                                              Target target) {
        RoutePlanResult result;
        try {
            result = MigrationPlanner.planRoutes(invocation, registry, input, index,
                manifests, target, Set.of());
        } catch (IllegalArgumentException e) {
            fail("planner guard rejected the " + name + ": " + e.getMessage());
            return null;
        }
        if (result == null || result.hasErrors() || result.plan() == null) {
            fail("the " + name + " carried diagnostics: "
                + (result == null ? "null result" : result.diagnostics()));
            return null;
        }
        check(true, "the " + name + " plans with zero diagnostics (silent plan-time "
            + "routing — never E6005)");
        return result.plan();
    }

    static void testCapabilityRegistryTransitionRollbackObservation() throws Exception {
        System.out.println("-- Capability registry transition rollback observation "
            + "(D4 steps 1-11 + D5) --");

        // D5: the committed V1_2_ACTIVE flip holds at every derivation
        // boundary; the V1_2_ACTIVE invocations below are internal T1
        // derivations only — the release constant is never edited.
        check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
            "V1_2_ACTIVE holds at observation entry (the public flip is committed by E12 and never "
                + "re-edited here)");

        CapabilityRegistry release = CapabilityRegistry.releaseRegistry();
        String releaseDigestBefore = release.capabilityRegistryHash();

        Path tmp = Files.createTempDirectory("deal-foundation-rollback-observation");
        try {
            // D4 step 1: one import-free int-using fixture module — no
            // imports, so abiEdges and shadowModules are empty in every
            // derived plan and STDLIB_TIME_CONFLICT cannot be claimed
            // (foundation F3's trigger requires std/time import facts).
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                export function add(x: int, y: int): int {
                  return x + y
                }

                export function main(): null {
                  return null
                }
                """);
            List<Path> roots = List.of(src.toAbsolutePath());
            Path entryFile = src.resolve("main.deal").toAbsolutePath();
            Path stdlibDir = Path.of("std").toAbsolutePath().normalize();

            // D4 step 2 / E2: compile #1 through the real orchestrator
            // with resolve(V1_2_ACTIVE, releaseRegistry()), dumpIr
            // enabled, Backend.LUAJIT; capture input/index/manifests once.
            CompilerInvocation factsInvocation = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
            Path factsRoot = tmp.resolve("build-facts");
            CompilationOrchestrator facts = new CompilationOrchestrator(entryFile, factsRoot,
                false, true, false, false, Backend.LUAJIT, null, roots, stdlibDir,
                null, factsInvocation);
            boolean factsOk = facts.compile();
            check(factsOk, "compile #1 (facts) succeeds: " + facts.diagnostics());
            check(facts.diagnostics().isEmpty(),
                "compile #1 (facts) reports zero diagnostics: " + facts.diagnostics());

            CheckedProjectBuildResult checked = facts.checkedProject();
            check(checked != null && !checked.hasErrors() && checked.input() != null
                    && checked.index() != null,
                "compile #1 produced exactly one checked project input and one "
                    + "interface index with zero diagnostics: " + checked);
            RequirementManifestResult manifestResult = facts.requirementManifests();
            check(manifestResult != null && !manifestResult.hasErrors()
                    && manifestResult.manifests() != null,
                "compile #1 produced the requirement manifests with zero "
                    + "diagnostics: " + manifestResult);

            byte[] irBefore = Files.readAllBytes(factsRoot.resolve("main.ir.txt"));

            check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
                "V1_2_ACTIVE holds after compile #1 (the facts compile is an "
                    + "internal T1 derivation)");

            if (checked == null || checked.hasErrors() || checked.input() == null
                    || checked.index() == null || manifestResult == null
                    || manifestResult.hasErrors() || manifestResult.manifests() == null) {
                return; // the named facts above already failed
            }
            CheckedProjectInput input = checked.input();
            ProjectInterfaceIndex index = checked.index();
            List<SemanticRequirementManifest> manifests = manifestResult.manifests();

            ModuleId m = input.entryModule();
            check(manifests.size() == 1 && manifests.get(0).moduleId().equals(m),
                "the manifest list carries exactly one manifest for the single "
                    + "module m=" + m + ": " + manifests);

            // D4 step 2 (E4): C is asserted by containment, never
            // equality; a missing SIGNED_INT32 row fails loudly
            // (assumption A2).
            Set<SemanticCapability> capabilities = manifests.get(0).capabilities();
            check(capabilities.contains(SemanticCapability.FOUNDATION_VALUES),
                "the computed manifest C contains FOUNDATION_VALUES (foundation F3); "
                    + "C=" + capabilities);
            check(capabilities.contains(SemanticCapability.SIGNED_INT32),
                "the computed manifest C contains SIGNED_INT32 (the I3 int-construct "
                    + "claim row is active — assumption A2); C=" + capabilities);
            check(!capabilities.contains(SemanticCapability.STDLIB_TIME_CONFLICT),
                "the import-free fixture claims no STDLIB_TIME_CONFLICT (the "
                    + "foundation F3 trigger requires std/time import facts); C="
                    + capabilities);

            // D4 step 3: derive the promoted registry P purely through
            // the D3 withState surface — every c ∈ C at LUAJIT PROMOTED,
            // every other entry SHADOW. No amendment, reflection, or
            // test double.
            CapabilityRegistry promoted = CapabilityRegistry.releaseRegistry();
            for (SemanticCapability capability : capabilities) {
                promoted = promoted.withState(capability, Target.LUAJIT,
                    CapabilityRegistry.State.PROMOTED);
            }
            for (SemanticCapability capability : capabilities) {
                check(promoted.state(capability, Target.LUAJIT)
                        == CapabilityRegistry.State.PROMOTED,
                    "P.state(" + capability + ", LUAJIT) == PROMOTED (D3 derivation)");
            }
            int promotedCount = 0;
            int shadowCount = 0;
            for (CapabilityRegistry.Entry entry : promoted.entries()) {
                if (entry.state() == CapabilityRegistry.State.PROMOTED) {
                    promotedCount++;
                    if (entry.target() != Target.LUAJIT) {
                        fail("a PROMOTED P entry must sit at LUAJIT; got " + entry);
                    }
                } else if (entry.state() == CapabilityRegistry.State.SHADOW) {
                    shadowCount++;
                }
            }
            check(promotedCount == capabilities.size(),
                "exactly |C|=" + capabilities.size() + " P entries are PROMOTED; got "
                    + promotedCount);
            check(shadowCount == CapabilityRegistry.ENTRY_COUNT - capabilities.size(),
                "the remaining " + (CapabilityRegistry.ENTRY_COUNT - capabilities.size())
                    + " P entries are SHADOW; got " + shadowCount);
            check(promoted.capabilityRegistryHash().equals(CanonicalJson.sha256Hex(
                    CanonicalJson.serializeBytes(promoted.canonicalJson()))),
                "P.capabilityRegistryHash() is the canonical recomputation over P's "
                    + "own entries (D3.4)");
            check(!promoted.capabilityRegistryHash().equals(releaseDigestBefore),
                "P.capabilityRegistryHash() differs from the release digest (the "
                    + "transition recomputes the digest)");

            check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
                "V1_2_ACTIVE holds after the P derivation (withState derives a "
                    + "new registry; the release constant is never edited)");

            // D4 step 4: the promoted plan over the real planner seam.
            CompilerInvocation invP = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, promoted);
            ModuleRoutePlan planP = planOrFail("promoted LUAJIT plan", invP, promoted,
                input, index, manifests, Target.LUAJIT);
            if (planP != null) {
                check(planP.entries().get(m) == ModuleRoute.SHARED,
                    "the promoted LUAJIT plan routes entries(m) == SHARED (F4 rule 4: "
                        + "every manifest capability PROMOTED for LUAJIT); got "
                        + planP.entries());
                check(planP.shadowModules().isEmpty(),
                    "the promoted LUAJIT plan has empty shadowModules (import-free, "
                        + "no shadow requests)");
                check(planP.abiEdges().isEmpty(),
                    "the promoted LUAJIT plan has empty abiEdges (import-free)");
                check(planP.invocationHash().equals(MigrationPlanner.deriveInvocationHash(
                        invP, index.interfaceIndexDigest(), Target.LUAJIT)),
                    "the promoted plan invocationHash equals the pinned derivation");
                check(planP.planId().equals(MigrationPlanner.planIdFor(
                        planP.invocationHash())),
                    "the promoted plan planId follows the pinned derivation");
            }

            // D4 step 5: per-target discrimination — the same invP/P for
            // JVM routes LEGACY (promotion is per target, F7; rule 4's
            // lookup is the capability × target lookup).
            ModuleRoutePlan planJ = planOrFail("JVM discrimination plan", invP, promoted,
                input, index, manifests, Target.JVM);
            if (planJ != null) {
                check(planJ.entries().get(m) == ModuleRoute.LEGACY,
                    "the JVM discrimination plan routes entries(m) == LEGACY "
                        + "(per-target promotion, F7; SIGNED_INT32 × JVM stays "
                        + "SHADOW); got " + planJ.entries());
            }

            // D4 step 6: the one-capability PROMOTED → SHADOW demotion.
            CapabilityRegistry demoted = promoted.withState(
                SemanticCapability.SIGNED_INT32, Target.LUAJIT,
                CapabilityRegistry.State.SHADOW);
            int differing = 0;
            CapabilityRegistry.Entry differingPromoted = null;
            CapabilityRegistry.Entry differingDemoted = null;
            List<CapabilityRegistry.Entry> promotedEntries = promoted.entries();
            List<CapabilityRegistry.Entry> demotedEntries = demoted.entries();
            for (int i = 0; i < CapabilityRegistry.ENTRY_COUNT; i++) {
                if (!promotedEntries.get(i).equals(demotedEntries.get(i))) {
                    differing++;
                    differingPromoted = promotedEntries.get(i);
                    differingDemoted = demotedEntries.get(i);
                }
            }
            check(differing == 1,
                "exactly one entry differs between D and P over the 24-entry cross "
                    + "product; got " + differing);
            if (differingPromoted != null) {
                check(differingPromoted.capability() == SemanticCapability.SIGNED_INT32
                        && differingPromoted.target() == Target.LUAJIT
                        && differingPromoted.state() == CapabilityRegistry.State.PROMOTED,
                    "the single differing entry is (SIGNED_INT32 × LUAJIT) PROMOTED "
                        + "in P; got " + differingPromoted);
            }
            if (differingDemoted != null) {
                check(differingDemoted.capability() == SemanticCapability.SIGNED_INT32
                        && differingDemoted.target() == Target.LUAJIT
                        && differingDemoted.state() == CapabilityRegistry.State.SHADOW,
                    "the single differing entry is (SIGNED_INT32 × LUAJIT) SHADOW in "
                        + "D; got " + differingDemoted);
            }
            check(!demoted.capabilityRegistryHash().equals(promoted.capabilityRegistryHash()),
                "D.capabilityRegistryHash() != P.capabilityRegistryHash() (the "
                    + "demotion recomputes the digest)");

            check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
                "V1_2_ACTIVE holds after the D derivation");

            // D4 step 7: the demoted plan — silent plan-time
            // ineligibility, never E6005; zero diagnostics by the helper.
            CompilerInvocation invD = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, demoted);
            ModuleRoutePlan planD = planOrFail("demoted LUAJIT plan", invD, demoted,
                input, index, manifests, Target.LUAJIT);
            if (planD != null) {
                check(planD.entries().get(m) == ModuleRoute.LEGACY,
                    "the demoted LUAJIT plan routes entries(m) == LEGACY (silent "
                        + "plan-time ineligibility — never E6005); got " + planD.entries());
                check(planD.shadowModules().isEmpty(),
                    "the demoted LUAJIT plan has empty shadowModules (import-free, "
                        + "no shadow requests)");
                check(planD.abiEdges().isEmpty(),
                    "the demoted LUAJIT plan has empty abiEdges (import-free)");
            }

            // D4 step 8 (by construction): P and D reached the planner
            // only through planOrFail → MigrationPlanner.planRoutes (the
            // direct seam, the same method the orchestrator's phase 3.7
            // calls); both orchestrator compiles use only
            // resolve(V1_2_ACTIVE, releaseRegistry()); no emitter, no
            // orchestrator phase 4, and no publication ever runs over P
            // or D — the reroute happens at plan time, before emission.

            // D4 step 9: content comparison — the pinned reading of the
            // A3 sentence (among decision-content fields only entries
            // change; the derived identifiers recompute and differ).
            if (planP != null && planD != null) {
                check(planP.target().equals(planD.target()),
                    "planP.target() == planD.target() == LUAJIT across the transition");
                check(planP.shadowModules().equals(planD.shadowModules()),
                    "planP and planD shadowModules are equal across the transition");
                check(planP.abiEdges().equals(planD.abiEdges()),
                    "planP and planD abiEdges are equal across the transition");
                check(planP.entries().size() == 1 && planD.entries().size() == 1
                        && planP.entries().keySet().equals(planD.entries().keySet())
                        && planP.entries().containsKey(m) && planD.entries().containsKey(m),
                    "both plans carry exactly the single entry m=" + m);
                check(planP.entries().get(m) == ModuleRoute.SHARED
                        && planD.entries().get(m) == ModuleRoute.LEGACY,
                    "entries differ at exactly the fixture module m (planP → SHARED, "
                        + "planD → LEGACY) — the route-only consequence");
                check(!planP.invocationHash().equals(planD.invocationHash()),
                    "planP.invocationHash() != planD.invocationHash() (the registry "
                        + "hash is a pinned invocation-hash input — recomputed, never "
                        + "stale)");
                check(!planP.planId().equals(planD.planId()),
                    "planP.planId() != planD.planId() (planId derives from the "
                        + "recomputed invocationHash)");
            }

            // D4 step 10 / E2: compile #2 after the last plan call with
            // identical arguments and a distinct output root — the same
            // fact objects, the identical index digest, byte-identical
            // IrDumper output.
            CompilerInvocation afterInvocation = CompilerProfileProvider.resolve(
                ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
            Path afterRoot = tmp.resolve("build-after");
            CompilationOrchestrator after = new CompilationOrchestrator(entryFile, afterRoot,
                false, true, false, false, Backend.LUAJIT, null, roots, stdlibDir,
                null, afterInvocation);
            boolean afterOk = after.compile();
            check(afterOk, "compile #2 (after the last plan call) succeeds with "
                + "identical arguments: " + after.diagnostics());
            byte[] irAfter = Files.readAllBytes(afterRoot.resolve("main.ir.txt"));
            check(Arrays.equals(irBefore, irAfter),
                "the module IrDumper output is byte-identical before the first plan "
                    + "call and after the last (planning and registry transitions "
                    + "never touch frontend state, F4/F8)");
            CheckedProjectBuildResult afterChecked = after.checkedProject();
            if (afterChecked != null && !afterChecked.hasErrors()
                    && afterChecked.index() != null) {
                check(afterChecked.index().interfaceIndexDigest()
                        .equals(index.interfaceIndexDigest()),
                    "the interface index digest is identical across both compiles "
                        + "(source/AST unchanged across the transition)");
            } else {
                fail("compile #2 produced no checked project/index (the identical-"
                    + "arguments facts are missing)");
            }

            check(ReleaseConfiguration.CURRENT_RELEASE_STATE == ReleaseState.V1_2_ACTIVE,
                "V1_2_ACTIVE holds after the last plan call plus compile #2");

            // D4 step 11: hash and state discipline — the A1 PUBLIC_BUILD
            // row, profile/release state equal across the transition,
            // every recorded/derived hash recomputes and differs.
            check(invP.purpose() == InvocationPurpose.PUBLIC_BUILD
                    && invD.purpose() == InvocationPurpose.PUBLIC_BUILD,
                "invP and invD both carry purpose PUBLIC_BUILD (A1)");
            check(invP.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                    && invD.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
                "invP and invD both carry DEAL_V1_2_INT32 (profile equal across "
                    + "the transition)");
            check(invP.releaseState() == ReleaseState.V1_2_ACTIVE
                    && invD.releaseState() == ReleaseState.V1_2_ACTIVE,
                "invP and invD both carry V1_2_ACTIVE (release state equal across "
                    + "the transition)");
            check(invP.capabilityRegistryHash().equals(promoted.capabilityRegistryHash()),
                "invP records P.capabilityRegistryHash() (recorded, recomputed — "
                    + "never stale)");
            check(invD.capabilityRegistryHash().equals(demoted.capabilityRegistryHash()),
                "invD records D.capabilityRegistryHash() (recorded, recomputed — "
                    + "never stale)");
            check(!invP.capabilityRegistryHash().equals(invD.capabilityRegistryHash()),
                "invP and invD capabilityRegistryHash values are unequal across "
                    + "the transition");
            check(invP.releaseStateHash().equals(CompilerProfileProvider
                    .deriveReleaseStateHash(ReleaseState.V1_2_ACTIVE,
                        promoted.capabilityRegistryHash())),
                "invP.releaseStateHash() equals deriveReleaseStateHash(V1_2_ACTIVE, "
                    + "P.capabilityRegistryHash())");
            check(invD.releaseStateHash().equals(CompilerProfileProvider
                    .deriveReleaseStateHash(ReleaseState.V1_2_ACTIVE,
                        demoted.capabilityRegistryHash())),
                "invD.releaseStateHash() equals deriveReleaseStateHash(V1_2_ACTIVE, "
                    + "D.capabilityRegistryHash())");
            check(!invP.releaseStateHash().equals(invD.releaseStateHash()),
                "invP and invD releaseStateHash values are unequal across the "
                    + "transition (F1 pins capabilityRegistryHash as an input)");
            check(CompilerProfileProvider.publicProfile(ReleaseState.V1_2_ACTIVE)
                    == SemanticProfile.DEAL_V1_2_INT32,
                "publicProfile(V1_2_ACTIVE) == DEAL_V1_2_INT32 (A1 matrix row "
                    + "unchanged)");
            check(CompilerProfileProvider.publicProfile(ReleaseState.PRE_ACTIVATION)
                    == SemanticProfile.LEGACY_SAFE_INT,
                "publicProfile(PRE_ACTIVATION) == LEGACY_SAFE_INT (A1 matrix row "
                    + "unchanged)");

            // D5: the release default is source-immutable across the P/D
            // derivations — all 24 entries SHADOW with the pinned digest
            // (the D3.2 source-immutability observation).
            List<CapabilityRegistry.Entry> releaseEntries =
                CapabilityRegistry.releaseRegistry().entries();
            boolean allShadow = releaseEntries.stream()
                .allMatch(e -> e.state() == CapabilityRegistry.State.SHADOW);
            check(releaseEntries.size() == CapabilityRegistry.ENTRY_COUNT && allShadow,
                "releaseRegistry() still yields the pinned all-SHADOW shape (24 "
                    + "entries) after the P/D derivations (D3.2 source-immutability)");
            check(CapabilityRegistry.releaseRegistry().capabilityRegistryHash()
                    .equals(releaseDigestBefore),
                "releaseRegistry().capabilityRegistryHash() equals the digest "
                    + "recorded before the P/D derivations (D3.2 source-immutability)");

            // D5: no legacy public revival — the matrix rows above hold
            // and both observation invocations carry DEAL_V1_2_INT32
            // under V1_2_ACTIVE, so LEGACY_SAFE_INT is never a rollback
            // target after activation. Retained v1.2 code intact: the
            // demoted plan's silent LEGACY reroute with zero diagnostics
            // (asserted above via planOrFail and entries(m) == LEGACY)
            // demonstrates rollback availability — the retained route
            // stays assignable with the unchanged profile.

            // Summary naming the promoted and demoted plans and the
            // compared fields.
            System.out.println("  promoted LUAJIT plan "
                + (planP == null ? "missing" : planP.planId())
                + ": entries(main)=" + (planP == null ? "?" : planP.entries().get(m)));
            System.out.println("  JVM discrimination plan "
                + (planJ == null ? "missing" : planJ.planId())
                + ": entries(main)=" + (planJ == null ? "?" : planJ.entries().get(m)));
            System.out.println("  demoted LUAJIT plan "
                + (planD == null ? "missing" : planD.planId())
                + ": entries(main)=" + (planD == null ? "?" : planD.entries().get(m)));
            System.out.println("  compared fields across the transition: target, "
                + "shadowModules, abiEdges (equal); entries (differ at exactly "
                + "main); capabilityRegistryHash, releaseStateHash, invocationHash, "
                + "planId (recomputed, differ); profile DEAL_V1_2_INT32 and release "
                + "state V1_2_ACTIVE (equal)");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 8. Wiring proof: COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION
    // =========================================================================

    static void testCommonShadowPreActivationWiringProof() throws Exception {
        System.out.println("-- Wiring proof: COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION "
            + "through the real orchestrator --");

        Path tmp = Files.createTempDirectory("deal-foundation-shadow-pre");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("a.deal"), """
                export function add(x: int, y: int): int {
                  return x + y
                }
                """);
            Files.writeString(src.resolve("main.deal"), """
                import * as a from "./a"

                export function main(): null {
                  a.add(1, 2)
                  return null
                }
                """);

            // The internal pre-activation shadow invocation: provider +
            // record guard admit it; the planner guard admits it at phase
            // 3.7; F4 rule 5 leaves every module on the LEGACY route with
            // zero shadow requests.
            CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry());
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false,
                false, false, false, Backend.LUAJIT, null,
                List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean ok = orchestrator.compile();
            check(ok, "the COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION compile "
                + "succeeds end to end (phase 3.7 no longer throws): "
                + orchestrator.diagnostics());
            RoutePlanResult result = orchestrator.routePlan();
            check(result != null && !result.hasErrors() && result.plan() != null,
                "phase 3.7 produced exactly one route plan with zero diagnostics: "
                    + (result == null ? "null" : result.diagnostics()));
            if (result != null && !result.hasErrors() && result.plan() != null) {
                ModuleRoutePlan plan = result.plan();
                check(plan.entries().size() == 2
                        && plan.entries().values().stream()
                            .allMatch(route -> route == ModuleRoute.LEGACY),
                    "the plan routes every implementation module LEGACY (F4 rule 5, "
                        + "zero shadow requests)");
                check(plan.shadowModules().isEmpty() && plan.abiEdges().isEmpty(),
                    "the plan has empty shadowModules and no ABI records");
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // 9. Wiring proof: profile-aware phase-0 parsing (signed-int32
    // foundation I1) through the real orchestrator under
    // COMMON_SHADOW + DEAL_V1_2_INT32 + PRE_ACTIVATION
    // =========================================================================

    static void testProfileAwareParserWiringProof() throws Exception {
        System.out.println("-- Wiring proof: profile-aware parser (I1) through real "
            + "phase-0 discovery under COMMON_SHADOW + DEAL_V1_2_INT32 + "
            + "PRE_ACTIVATION --");

        Path tmp = Files.createTempDirectory("deal-foundation-parser-i1");
        try {
            Path src = tmp.resolve("src");
            Files.createDirectories(src);

            CompilerInvocation invocation = CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry());

            // (a) The bare out-of-range literal raises E1036 at the token
            // during real phase-0 discovery/parsing.
            Files.writeString(src.resolve("overflow.deal"), """
                export function bad(): int {
                  return 2147483648
                }

                export function main(): null { return null; }
                """);
            CompilationOrchestrator overflow = new CompilationOrchestrator(
                src.resolve("overflow.deal").toAbsolutePath(),
                tmp.resolve("build-overflow"), false, false, false, false,
                Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean ok = overflow.compile();
            check(!ok, "the v1.2 compile of '2147483648' fails through real "
                + "phase-0 discovery/parsing");
            List<CompilerDiagnostic> diags = overflow.diagnostics();
            check(diags.size() == 1,
                "the v1.2 out-of-range compile reports exactly one diagnostic: "
                    + diags);
            if (!diags.isEmpty()) {
                CompilerDiagnostic d = diags.get(0);
                check("E1036".equals(d.code()) && "error".equals(d.severity())
                        && "Integer literal out of range: 2147483648"
                            .equals(d.message()),
                    "the phase-0 diagnostic is E1036 'Integer literal out of "
                        + "range: 2147483648' at error severity: " + d);
                check(d.line() == 2 && d.column() == 10,
                    "the E1036 diagnostic is anchored at the offending token "
                        + "(line 2, column 10): got line " + d.line()
                        + ", column " + d.column());
                check(d.file() != null
                        && d.file().replace(java.io.File.separatorChar, '/')
                            .endsWith("overflow.deal"),
                    "the E1036 diagnostic names the parsed module file: " + d.file());
            }

            // (b) The immediate-minus in-range literal parses through
            // phase 0 and the compile proceeds to completion.
            Files.writeString(src.resolve("min.deal"), """
                export function int32_min(): int {
                  return -2147483648
                }

                export function main(): null { return null; }
                """);
            CompilationOrchestrator min = new CompilationOrchestrator(
                src.resolve("min.deal").toAbsolutePath(),
                tmp.resolve("build-min"), false, false, false, false,
                Backend.LUAJIT, null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, invocation);
            boolean minOk = min.compile();
            check(minOk, "the v1.2 compile of '-2147483648' parses through "
                + "phase 0 and proceeds to completion: " + min.diagnostics());
            check(min.diagnostics().isEmpty(),
                "the v1.2 '-2147483648' compile reports no diagnostics: "
                    + min.diagnostics());
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 10. SignedInt32 integration verification (ISSUE-0398): fixed corpus,
    // four-way agreement, activated-state gate facts, fault-injection matrix
    // =========================================================================

    /**
     * The final decomposition task of the signed-int32 epic (I6 part 4 and
     * Verification 6 of both design pages; design name
     * {@code SignedInt32IntegrationTest}). It runs the fixed
     * {@link SignedInt32Corpus} on all four constituents — the
     * profile-aware parser, the shared value-semantics primitive, the
     * retained LuaJIT subprocess, and the retained JVM subprocess — and
     * asserts per-case agreement with the pinned outcome: code + origin
     * compared, the pinned {@code int out of safe range} template for the
     * shared primitive and the same pinned retained template for both
     * retained routes (ISSUE-0618 retired the intentional two-template
     * state), raw messages never compared across sides. Then it asserts the activated-state
     * activated-state gate facts (A2) and faults each named constituent in
     * turn — parser, shared semantics, LuaJIT route, JVM route, provider
     * matrix, release configuration, catalog, harness seam — proving the
     * verification fails when any constituent is broken (anti-hollow).
     */
    static final class SignedInt32IntegrationTest {

        // =====================================================================
        // Driver configuration: the named fault seams, exactly one per probe
        // =====================================================================

        private static final class CorpusConfig {
            SemanticProfile parserProfile = SemanticProfile.DEAL_V1_2_INT32;
            /** Fault PARSE: the legacy parse contract (no E1036 int32 gate). */
            boolean legacyParserConstructor = false;
            /** Fault SEMANTICS: a wrong int-conversion range row. */
            boolean tamperConversionRow = false;
            /** Fault LUAJIT: the emitted int32 gate is flipped back to legacy. */
            boolean tamperLuaInt32Flag = false;
            /** Fault SEAM (LuaJIT lane): the legacy-regression invocation. */
            boolean legacyLuaInvocation = false;
            /** Fault JVM: the legacy invocation (legacy helpers, raw Math.pow). */
            boolean legacyJvmInvocation = false;
            /** Fault PROVIDER: a flipped provider matrix (rejected combination). */
            boolean flipProviderMatrix = false;
        }

        /** One verification run's summary; never touches the global counters. */
        private record AgreementReport(int casesRun, int disagreements) {}

        /** One LuaJIT batch case outcome. */
        private record LuaCaseRun(boolean ok, String code, String message,
                                  String file, Integer line, Integer column) {}

        /** One JVM batch case outcome. */
        private record JvmCaseRun(boolean ok, String code, String message) {}

        /** One parser-driver outcome. */
        private record ParserOutcome(boolean parsed, List<CompilerDiagnostic> diagnostics,
                                     Integer locatedLine, Integer locatedColumn) {}

        /**
         * One semantics-row outcome. Error rows carry the failure origin
         * the primitive returned — the caller-supplied
         * {@code SourceOrigin} this driver handed in — so the error-case
         * comparison pins code + canonical template + origin (the
         * shared-side leg of the {@code LegacyErrorNormalization}
         * code+origin rule).
         */
        private record SemRowOutcome(String value, String failCode, String failTemplate,
                                     String originFile, Integer originLine,
                                     Integer originColumn) {

            static SemRowOutcome value(String value) {
                return new SemRowOutcome(value, null, null, null, null, null);
            }

            static SemRowOutcome failure(SharedValueSemantics.Int32Result.Fail fail) {
                return new SemRowOutcome(null, fail.code().code(), fail.template(),
                    fail.origin().span().file(), fail.origin().span().startLine(),
                    fail.origin().span().startColumn());
            }
        }

        static void runAll() throws Exception {
            testCorpusFourWayAgreement();
            testActivatedStateGateFacts();
            testFaultMatrix();
        }

        // =====================================================================
        // Invocations and compilation
        // =====================================================================

        private static CompilerInvocation v12Invocation() {
            return CompilerProfileProvider.resolveCommonShadow(
                SemanticProfile.DEAL_V1_2_INT32, ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry());
        }

        private static CompilerInvocation legacyRegressionInvocation() {
            return CompilerProfileProvider.resolveLegacyRegression(
                SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
                CapabilityRegistry.releaseRegistry());
        }
        private static CompilerInvocation publicBuildInvocation(ReleaseState state) {
            return CompilerProfileProvider.resolve(state,
                ReleaseConfiguration.releaseCapabilityRegistry());
        }
        private static Path stdlibDir() {
            return Path.of("std").toAbsolutePath().normalize();
        }

        /**
         * One orchestrator compile; returns null on failure. The
         * externals map (raw import specifier &rarr; declaration text
         * relative to the entry directory) drives the test-only
         * isolated-phase context synthesis (ISSUE-0269: the retired
         * tolerant DealConfig reader is gone).
         */
        private static CompilationOrchestrator compile(Path entry, Path out,
                Backend backend, List<Path> roots, CompilerInvocation invocation,
                Map<String, String> externals) throws IOException {
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                entry, out, false, false, false, false, backend, externals,
                roots, stdlibDir(), null, invocation);
            orchestrator.compile();
            return orchestrator;
        }

        /** The JVM class name for a corpus case file stem (the emitter rule). */
        private static String jvmClassName(String name) {
            return Character.toUpperCase(name.charAt(0)) + name.substring(1);
        }

        // =====================================================================
        // Parser driver (T3)
        // =====================================================================

        private static ParserOutcome runParserDriver(SignedInt32Corpus.Case c,
                                                     CorpusConfig config) {
            String file = c.name() + ".deal";
            LexResult lex = new Lexer(c.source(), file).tokenize();
            if (lex.hasErrors()) {
                return new ParserOutcome(false, lex.diagnostics(), null, null);
            }
            ParseResult result = config.legacyParserConstructor
                ? new Parser(lex.tokens(), file, lex.directiveEvents()).parse()
                : new Parser(lex.tokens(), file, config.parserProfile,
                    lex.directiveEvents()).parse();
            Integer locatedLine = null;
            Integer locatedColumn = null;
            if (!result.hasErrors() && c.expected()
                    instanceof SignedInt32Corpus.RuntimeOutcome out
                    && out.opKind() != SignedInt32Corpus.OpKind.NONE) {
                int[] located = locateOperationOrigin(result.program(), out.opKind(),
                    out.originLine(), out.originColumn());
                if (located != null) {
                    locatedLine = located[0];
                    locatedColumn = located[1];
                }
            }
            return new ParserOutcome(!result.hasErrors(), result.diagnostics(),
                locatedLine, locatedColumn);
        }

        /**
         * The span start of the pinned operation node in source order; for
         * the descriptor-tail boundary the origin the emitters forward is
         * the declaration's type-annotation span.
         */
        private static int[] locateOperationOrigin(ProgramNode program,
                SignedInt32Corpus.OpKind kind, Integer originLine, Integer originColumn) {
            if (kind == SignedInt32Corpus.OpKind.DECL_TYPE) {
                for (StatementNode stmt : allStatements(program)) {
                    if (stmt instanceof VariableDeclaration v
                            && v.typeAnnotation().isPresent()) {
                        Span span = v.typeAnnotation().get().span();
                        if (span.startLine() == originLine
                                && span.startColumn() == originColumn) {
                            return new int[]{span.startLine(), span.startColumn()};
                        }
                    }
                }
                return null;
            }
            List<ExpressionNode> collected = new ArrayList<>();
            collectStatements(program.statements(), collected);
            for (ExpressionNode node : collected) {
                boolean match = switch (kind) {
                    case BINARY -> node instanceof BinaryExpr;
                    case UNARY -> node instanceof UnaryExpr;
                    case CALL -> node instanceof CallExpr;
                    case MEMBER -> node instanceof MemberAccessExpr;
                    case DECL_TYPE, NONE -> false;
                };
                if (match) {
                    return new int[]{node.span().startLine(), node.span().startColumn()};
                }
            }
            return null;
        }

        private static List<StatementNode> allStatements(ProgramNode program) {
            List<StatementNode> flat = new ArrayList<>();
            collectAllStatements(program.statements(), flat);
            return flat;
        }

        private static void collectAllStatements(List<StatementNode> statements,
                                                 List<StatementNode> out) {
            for (StatementNode stmt : statements) {
                out.add(stmt);
                switch (stmt) {
                    case ExportDeclaration e ->
                        collectAllStatements(List.of(e.declaration()), out);
                    case FunctionDeclaration f ->
                        collectAllStatements(f.body().statements(), out);
                    case IfStatement i -> {
                        collectAllStatements(i.thenBlock().statements(), out);
                        i.elseBranch().ifPresent(branch -> {
                            if (branch instanceof Either.Left<?, ?> left) {
                                collectAllStatements(List.of((IfStatement) left.value()), out);
                            } else if (branch instanceof Either.Right<?, ?> right) {
                                collectAllStatements(((Block) right.value()).statements(), out);
                            }
                        });
                    }
                    case Block b -> collectAllStatements(b.statements(), out);
                    default -> { }
                }
            }
        }

        private static void collectStatements(List<StatementNode> statements,
                                              List<ExpressionNode> out) {
            for (StatementNode stmt : statements) {
                switch (stmt) {
                    case ExportDeclaration e ->
                        collectStatements(List.of(e.declaration()), out);
                    case FunctionDeclaration f ->
                        collectStatements(f.body().statements(), out);
                    case ReturnStatement r ->
                        r.expr().ifPresent(e -> collectExpr(e, out));
                    case ExpressionStatement es -> collectExpr(es.expr(), out);
                    case IfStatement i -> {
                        collectExpr(i.condition(), out);
                        collectStatements(i.thenBlock().statements(), out);
                        i.elseBranch().ifPresent(branch -> {
                            if (branch instanceof Either.Left<?, ?> left) {
                                collectStatements(List.of((IfStatement) left.value()), out);
                            } else if (branch instanceof Either.Right<?, ?> right) {
                                collectStatements(((Block) right.value()).statements(), out);
                            }
                        });
                    }
                    case VariableDeclaration v -> collectExpr(v.initializer(), out);
                    case Block b -> collectStatements(b.statements(), out);
                    default -> { }
                }
            }
        }

        private static void collectExpr(ExpressionNode node, List<ExpressionNode> out) {
            switch (node) {
                case BinaryExpr b -> {
                    out.add(b);
                    collectExpr(b.left(), out);
                    collectExpr(b.right(), out);
                }
                case UnaryExpr u -> {
                    out.add(u);
                    collectExpr(u.expr(), out);
                }
                case CallExpr c -> {
                    out.add(c);
                    collectExpr(c.callee(), out);
                    for (ExpressionNode arg : c.args()) {
                        collectExpr(arg, out);
                    }
                }
                case MemberAccessExpr m -> {
                    out.add(m);
                    collectExpr(m.object(), out);
                }
                case IndexExpr ix -> {
                    collectExpr(ix.array(), out);
                    collectExpr(ix.index(), out);
                }
                case ArrayLiteralExpr al -> {
                    for (ExpressionNode element : al.elements()) {
                        collectExpr(element, out);
                    }
                }
                case ObjectLiteralExpr ol -> {
                    for (Property property : ol.properties()) {
                        collectExpr(property.value(), out);
                    }
                }
                case AssignmentExpr a -> collectExpr(a.value(), out);
                case HasExpr h -> collectExpr(h.object(), out);
                case AwaitExpression aw -> collectExpr(aw.callee(), out);
                case FunctionExpr fe -> collectStatements(fe.body().statements(), out);
                case TemplateLiteralExpr t -> {
                    for (ExpressionNode part : t.parts()) {
                        collectExpr(part, out);
                    }
                }
                default -> { }
            }
        }

        // =====================================================================
        // Shared value-semantics driver (T2)
        // =====================================================================

        private static SourceOrigin pinnedOrigin(SignedInt32Corpus.Case c) {
            int line = 1;
            int column = 1;
            if (c.expected() instanceof SignedInt32Corpus.RuntimeOutcome out
                    && out.originLine() != null) {
                line = out.originLine();
                column = out.originColumn();
            }
            return new SourceOrigin(c.name() + ".deal",
                new SourceSpan(c.name() + ".deal", line, column, line, column),
                SourceOriginKind.USER, new AnchorId(1), null);
        }

        /** The conversion row with the injected fault: out-of-range returns 0. */
        private static SharedValueSemantics.Int32Result intFromNumberSeam(double value,
                SourceOrigin origin, boolean tamper) {
            SharedValueSemantics.Int32Result result =
                SharedValueSemantics.intFromNumber(value, origin);
            if (tamper && result instanceof SharedValueSemantics.Int32Result.Fail fail
                    && "E8004".equals(fail.code().code())) {
                return SharedValueSemantics.Int32Result.value(0);
            }
            return result;
        }

        private static String numberText(double value) {
            if (Double.isNaN(value)) {
                return "NaN";
            }
            if (value == Double.POSITIVE_INFINITY) {
                return "Infinity";
            }
            if (value == Double.NEGATIVE_INFINITY) {
                return "-Infinity";
            }
            if (value == 0.0 && Double.doubleToRawLongBits(value) != 0L) {
                return "-0.0";
            }
            return Double.toString(value);
        }

        private static SemRowOutcome runSemRow(SignedInt32Corpus.SemRow row,
                SourceOrigin origin, boolean tamper) {
            switch (row) {
                case SignedInt32Corpus.SemInt32Binary b -> {
                    SharedValueSemantics.Int32Result r = switch (b.op()) {
                        case "add" -> SharedValueSemantics.int32Add(b.a(), b.b(), origin);
                        case "sub" -> SharedValueSemantics.int32Sub(b.a(), b.b(), origin);
                        case "mul" -> SharedValueSemantics.int32Mul(b.a(), b.b(), origin);
                        case "div" -> SharedValueSemantics.int32Div(b.a(), b.b(), origin);
                        case "mod" -> SharedValueSemantics.int32Mod(b.a(), b.b(), origin);
                        case "pow" -> SharedValueSemantics.int32Pow(b.a(), b.b(), origin);
                        default -> throw new IllegalArgumentException("unknown int32 op " + b.op());
                    };
                    return int32Text(r);
                }
                case SignedInt32Corpus.SemInt32Unary u -> {
                    return int32Text(SharedValueSemantics.int32Neg(u.a(), origin));
                }
                case SignedInt32Corpus.SemIntFromNumber n -> {
                    return int32Text(intFromNumberSeam(n.value(), origin, tamper));
                }
                case SignedInt32Corpus.SemInt32Integral i -> {
                    return int32Text(
                        SharedValueSemantics.checkInt32Integral(i.value(), origin));
                }
                case SignedInt32Corpus.SemNumberBinary b -> {
                    double v = switch (b.op()) {
                        case "add" -> SharedValueSemantics.numberAdd(b.a(), b.b());
                        case "sub" -> SharedValueSemantics.numberSub(b.a(), b.b());
                        case "mul" -> SharedValueSemantics.numberMul(b.a(), b.b());
                        case "div" -> SharedValueSemantics.numberDiv(b.a(), b.b());
                        case "mod" -> SharedValueSemantics.numberModFloor(b.a(), b.b());
                        default -> throw new IllegalArgumentException("unknown number op " + b.op());
                    };
                    return SemRowOutcome.value(numberText(v));
                }
                case SignedInt32Corpus.SemNumberUnary u -> {
                    double v = switch (u.op()) {
                        case "neg" -> SharedValueSemantics.numberNeg(u.a());
                        default -> throw new IllegalArgumentException("unknown number unary " + u.op());
                    };
                    return SemRowOutcome.value(numberText(v));
                }
                case SignedInt32Corpus.SemNumberCompare cmp -> {
                    boolean v = switch (cmp.op()) {
                        case "eq" -> SharedValueSemantics.numberEq(cmp.a(), cmp.b());
                        case "ne" -> SharedValueSemantics.numberNe(cmp.a(), cmp.b());
                        case "lt" -> SharedValueSemantics.numberLt(cmp.a(), cmp.b());
                        case "le" -> SharedValueSemantics.numberLe(cmp.a(), cmp.b());
                        case "gt" -> SharedValueSemantics.numberGt(cmp.a(), cmp.b());
                        case "ge" -> SharedValueSemantics.numberGe(cmp.a(), cmp.b());
                        default -> throw new IllegalArgumentException("unknown compare op " + cmp.op());
                    };
                    return SemRowOutcome.value(Boolean.toString(v));
                }
                case SignedInt32Corpus.SemNumberPow p -> {
                    return SemRowOutcome.value(
                        numberText(SharedValueSemantics.numberPow(p.a(), p.b())));
                }
            }
        }

        private static SemRowOutcome int32Text(SharedValueSemantics.Int32Result result) {
            if (result instanceof SharedValueSemantics.Int32Result.Value v) {
                return SemRowOutcome.value(Integer.toString(v.value()));
            }
            return SemRowOutcome.failure(
                (SharedValueSemantics.Int32Result.Fail) result);
        }

        // =====================================================================
        // Retained LuaJIT subprocess driver (T4)
        // =====================================================================

        private static boolean luajitAvailable;

        static {
            luajitAvailable = false;
            try {
                Process probe = new ProcessBuilder("luajit", "-v").start();
                probe.waitFor();
                luajitAvailable = probe.exitValue() == 0;
            } catch (Exception ignored) {
                luajitAvailable = false;
            }
        }

        private static final String LUA_RUNNER = """
            package.path = './?.lua;./std/?.lua;' .. package.path
            local ok, err = xpcall(function()
              local m = require(arg[1])
              m.main.f()
            end, function(e) return e end)
            if ok then
              print("RUNTIME_OK")
            else
              if type(err) == "table" and err.code ~= nil then
                print("CODE: " .. tostring(err.code))
                print("MESSAGE: " .. tostring(err.message))
                print("FILE: " .. tostring(err.file))
                print("LINE: " .. tostring(err.line))
                print("COLUMN: " .. tostring(err.column))
              else
                print("RAW: " .. tostring(err))
              end
            end
            """;

        private static LuaCaseRun runLuaCase(Path outDir, String caseName) {
            if (!luajitAvailable) {
                return null; // environmental: the lane cannot execute
            }
            try {
                Path runner = outDir.resolve("runner.lua");
                Files.writeString(runner, LUA_RUNNER);
                ProcessBuilder pb = new ProcessBuilder("luajit", "runner.lua", caseName);
                pb.directory(outDir.toFile());
                pb.redirectErrorStream(true);
                Process p = pb.start();
                String output = new String(p.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                p.waitFor();
                Map<String, String> fields = parseFieldOutput(output);
                if (output.contains("RUNTIME_OK")) {
                    return new LuaCaseRun(true, null, null, null, null, null);
                }
                String code = fields.get("CODE");
                if (code == null) {
                    return new LuaCaseRun(false, null, null, "raw: " + output, null, null);
                }
                return new LuaCaseRun(false, code, fields.get("MESSAGE"),
                    fields.get("FILE"), intOrNull(fields.get("LINE")),
                    intOrNull(fields.get("COLUMN")));
            } catch (Exception e) {
                return new LuaCaseRun(false, null, null, "exception: " + e, null, null);
            }
        }

        /** The pinned LuaJIT gate check — the host-boundary replacement. */
        private static LuaCaseRun runLuaGateScript(Path outDir, String script,
                String caseName) {
            if (!luajitAvailable) {
                return null;
            }
            try {
                Path file = outDir.resolve("gate_" + caseName + ".lua");
                Files.writeString(file, script);
                ProcessBuilder pb = new ProcessBuilder("luajit", file.getFileName().toString());
                pb.directory(outDir.toFile());
                pb.redirectErrorStream(true);
                Process p = pb.start();
                String output = new String(p.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                p.waitFor();
                Map<String, String> fields = parseFieldOutput(output);
                String code = fields.get("CODE");
                if (code == null) {
                    return new LuaCaseRun(false, null, null, "raw: " + output, null, null);
                }
                return new LuaCaseRun(false, code, fields.get("MESSAGE"),
                    fields.get("FILE"), intOrNull(fields.get("LINE")),
                    intOrNull(fields.get("COLUMN")));
            } catch (Exception e) {
                return new LuaCaseRun(false, null, null, "exception: " + e, null, null);
            }
        }

        private static Map<String, String> parseFieldOutput(String output) {
            Map<String, String> fields = new LinkedHashMap<>();
            for (String line : output.split("\n")) {
                int colon = line.indexOf(": ");
                if (colon > 0) {
                    fields.put(line.substring(0, colon), line.substring(colon + 2).trim());
                }
            }
            return fields;
        }

        private static Integer intOrNull(String text) {
            if (text == null || "nil".equals(text)) {
                return null;
            }
            try {
                return Integer.valueOf(text);
            } catch (NumberFormatException e) {
                return null;
            }
        }

        // =====================================================================
        // Retained JVM subprocess driver (T5)
        // =====================================================================

        private static final String JVM_RUNNER = """
            public final class CorpusJvmRunner {
                public static void main(String[] args) {
                    for (String cn : args) {
                        try {
                            Class<?> c = Class.forName(cn);
                            c.getMethod("main").invoke(null);
                            System.out.println("CASE " + cn + " RUNTIME_OK");
                        } catch (Throwable e) {
                            Throwable t = e;
                            while (t instanceof ExceptionInInitializerError && t.getCause() != null) {
                                t = t.getCause();
                            }
                            if (t instanceof java.lang.reflect.InvocationTargetException
                                    && t.getCause() != null) {
                                t = t.getCause();
                            }
                            String code = null;
                            if ("DealError".equals(t.getClass().getSimpleName())) {
                                try {
                                    java.lang.reflect.Field f =
                                        t.getClass().getDeclaredField("code");
                                    f.setAccessible(true);
                                    code = String.valueOf(f.get(t));
                                } catch (ReflectiveOperationException ignored) { }
                            }
                            if (code != null) {
                                System.out.println("CASE " + cn + " CODE: " + code);
                                System.out.println("CASE " + cn + " MESSAGE: " + t.getMessage());
                            } else {
                                System.out.println("CASE " + cn + " RAW: " + t);
                            }
                        }
                    }
                }
            }
            """;

        private static JvmCaseRun runJvmCase(Path outDir, String caseName) {
            try {
                ProcessBuilder pb = new ProcessBuilder("java", "-cp",
                    outDir.toString(), "CorpusJvmRunner", jvmClassName(caseName));
                pb.directory(outDir.toFile());
                pb.redirectErrorStream(true);
                Process p = pb.start();
                String output = new String(p.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8).trim();
                int exitCode = p.waitFor();
                String okLine = "CASE " + jvmClassName(caseName) + " RUNTIME_OK";
                if (output.contains(okLine)) {
                    return new JvmCaseRun(true, null, null);
                }
                Map<String, String> fields = new LinkedHashMap<>();
                String prefix = "CASE " + jvmClassName(caseName) + " ";
                for (String line : output.split("\n")) {
                    if (line.startsWith(prefix)) {
                        int colon = line.indexOf(": ");
                        if (colon > 0) {
                            fields.put(line.substring(prefix.length(), colon),
                                line.substring(colon + 2).trim());
                        }
                    }
                }
                String code = fields.get("CODE");
                if (code == null) {
                    return new JvmCaseRun(false, null,
                        "jvm exit " + exitCode + ": " + output);
                }
                return new JvmCaseRun(false, code, fields.get("MESSAGE"));
            } catch (Exception e) {
                return new JvmCaseRun(false, null, "exception: " + e);
            }
        }

        // =====================================================================
        // The batch project: one compile per retained backend for every case
        // =====================================================================

        /**
         * Writes every corpus module of the run into {@code src}, plus the
         * synthetic entry module that imports and calls each case's
         * {@code test()} (compile-time closure only — the runners never
         * execute the entry), plus the host declaration and deal.json for
         * the host-boundary case. Returns the entry file.
         */
        private static Path writeBatchProject(Path src,
                List<SignedInt32Corpus.Case> moduleCases) throws IOException {
            Files.createDirectories(src);
            StringBuilder entry = new StringBuilder();
            List<String> aliases = new ArrayList<>();
            int index = 0;
            for (SignedInt32Corpus.Case c : moduleCases) {
                Files.writeString(src.resolve(c.name() + ".deal"), c.source());
                String alias = "c" + index;
                aliases.add(alias);
                entry.append("import * as ").append(alias)
                    .append(" from \"./").append(c.name()).append("\"\n");
                index++;
            }
            entry.append("\nexport function main(): null {\n");
            for (String alias : aliases) {
                entry.append("  ").append(alias).append(".test();\n");
            }
            entry.append("  return null;\n}\n");
            Files.writeString(src.resolve("all.deal"), entry.toString());

            for (SignedInt32Corpus.Case c : moduleCases) {
                if (c.host() == null) {
                    continue;
                }
                Path declaration = src.resolve(c.host().declarationPath());
                Files.createDirectories(declaration.getParent());
                Files.writeString(declaration, c.host().declarationSource());
                Files.writeString(src.resolve("deal.json"), """
                    {
                      "languageVersion": "1.2",
                      "externals": {
                        "%s": { "declaration": "%s" }
                      }
                    }
                    """.formatted(c.host().importPath(),
                    c.host().declarationPath().replace('\\', '/')));
            }
            return src.resolve("all.deal");
        }

        /**
         * The externals map of the batch project's injected
         * {@code deal.json}, parsed by the strict parser (ISSUE-0269:
         * the retired tolerant DealConfig reader is gone); null when the
         * project carries no manifest. Declaration texts stay exactly as
         * written (entry-directory-relative in the isolated-phase
         * synthesis — the batch manifest sits next to the entry).
         */
        private static Map<String, String> loadExternals(Path src)
                throws IOException {
            if (!Files.exists(src.resolve("deal.json"))) {
                return null;
            }
            StrictManifestParser.StrictManifestParseResult parsed =
                StrictManifestParser.parse(
                    src.resolve("deal.json").toString(),
                    Files.readString(src.resolve("deal.json")));
            if (parsed.manifest() == null) {
                return null;
            }
            Map<String, String> externals = new LinkedHashMap<>();
            parsed.manifest().externals().forEach((specifier, spec) ->
                externals.put(specifier, spec.declaration().value()));
            return externals;
        }

        /** Returns the output dir when the batch compiled; null on failure. */
        private static String compileBatch(Path tmp,
                List<SignedInt32Corpus.Case> moduleCases, CorpusConfig config,
                String suffix, Backend backend, boolean legacy) throws IOException {
            Path src = tmp.resolve("src");
            Path entry = writeBatchProject(src, moduleCases);
            Path out = tmp.resolve("out-" + suffix);
            CompilerInvocation invocation;
            try {
                invocation = config.flipProviderMatrix
                    ? CompilerProfileProvider.resolveCommonShadow(
                        SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
                        CapabilityRegistry.releaseRegistry())
                    : legacy ? legacyRegressionInvocation() : v12Invocation();
            } catch (IllegalArgumentException flipped) {
                return null; // the flipped provider matrix rejects at resolution
            }
            CompilationOrchestrator orchestrator = compile(entry, out, backend,
                List.of(src.toAbsolutePath()), invocation, loadExternals(src));
            if (orchestrator == null || orchestrator.checkedProject() == null
                    || orchestrator.checkedProject().hasErrors()
                    || !Files.exists(out)) {
                return null;
            }
            if (backend == Backend.LUAJIT && config.tamperLuaInt32Flag) {
                try (Stream<Path> stream = Files.walk(out)) {
                    for (Path file : stream.filter(Files::isRegularFile)
                            .filter(p -> p.toString().endsWith(".lua")).toList()) {
                        Files.writeString(file,
                            Files.readString(file)
                                .replace("__rt.__INT32 = true", "__rt.__INT32 = false"));
                    }
                }
            }
            return out.toString();
        }

        private static boolean javacBatch(Path outDir) {
            List<String> javaFiles = new ArrayList<>();
            try (Stream<Path> stream = Files.list(outDir)) {
                stream.filter(p -> p.toString().endsWith(".java"))
                      .sorted()
                      .forEach(p -> javaFiles.add(p.getFileName().toString()));
            } catch (IOException e) {
                return false;
            }
            if (javaFiles.isEmpty()) {
                return false;
            }
            StringBuilder err = new StringBuilder();
            return StubModuleResolver.compileWithJavac(outDir, javaFiles, err);
        }

        // =====================================================================
        // The corpus verification core
        // =====================================================================

        private static AgreementReport verifyCorpus(CorpusConfig config,
                List<SignedInt32Corpus.Case> cases, boolean report, Path tmp)
                throws IOException {
            List<SignedInt32Corpus.Case> moduleCases = new ArrayList<>();
            for (SignedInt32Corpus.Case c : cases) {
                if (c.expected() instanceof SignedInt32Corpus.RuntimeOutcome) {
                    moduleCases.add(c);
                }
            }

            // Parser driver runs per case in-process.
            Map<String, ParserOutcome> parserOutcomes = new LinkedHashMap<>();
            for (SignedInt32Corpus.Case c : cases) {
                parserOutcomes.put(c.name(), runParserDriver(c, config));
            }

            // Retained LuaJIT lane: one batched compile + one subprocess.
            Map<String, LuaCaseRun> luaOutcomes = new LinkedHashMap<>();
            String luaOutDir = compileBatch(tmp, moduleCases, config, "lua",
                Backend.LUAJIT, config.legacyLuaInvocation);
            if (luaOutDir != null) {
                for (SignedInt32Corpus.Case c : moduleCases) {
                    if (c.luaGateScript() != null) {
                        continue; // the gate-script case runs its script instead
                    }
                    luaOutcomes.put(c.name(), runLuaCase(Path.of(luaOutDir), c.name()));
                }
                for (SignedInt32Corpus.Case c : moduleCases) {
                    if (c.luaGateScript() == null) {
                        continue;
                    }
                    luaOutcomes.put(c.name(),
                        runLuaGateScript(Path.of(luaOutDir), c.luaGateScript(), c.name()));
                }
            }

            // Retained JVM lane: one batched compile + javac + one subprocess.
            Map<String, JvmCaseRun> jvmOutcomes = new LinkedHashMap<>();
            String jvmOutDir = compileBatch(tmp, moduleCases, config, "jvm",
                Backend.JVM, config.legacyJvmInvocation);
            if (jvmOutDir != null) {
                Path jvmDir = Path.of(jvmOutDir);
                for (SignedInt32Corpus.Case c : moduleCases) {
                    if (c.host() != null) {
                        Files.writeString(jvmDir.resolve(hostClassName(c) + ".java"),
                            c.host().javaSource());
                    }
                }
                Files.writeString(jvmDir.resolve("CorpusJvmRunner.java"), JVM_RUNNER);
                if (javacBatch(jvmDir)) {
                    for (SignedInt32Corpus.Case c : moduleCases) {
                        jvmOutcomes.put(c.name(), runJvmCase(jvmDir, c.name()));
                    }
                }
            }

            int disagreements = 0;
            for (SignedInt32Corpus.Case c : cases) {
                int before = disagreements;
                disagreements += agreeOnCase(c, config, parserOutcomes.get(c.name()),
                    luaOutcomes.get(c.name()), jvmOutcomes.get(c.name()), report);
                if (report) {
                    System.out.println("  corpus " + c.name() + ": "
                        + (disagreements == before ? "AGREES" : "DISAGREES"));
                }
            }
            return new AgreementReport(cases.size(), disagreements);
        }

        private static String hostClassName(SignedInt32Corpus.Case c) {
            String javaSource = c.host().javaSource();
            java.util.regex.Matcher m = java.util.regex.Pattern.compile(
                "(?:^|\\s)class\\s+([A-Za-z_$][A-Za-z0-9_$]*)").matcher(javaSource);
            return m.find() ? m.group(1) : "HostImpl";
        }

        /**
         * Asserts one corpus case's agreement across the constituents that
         * run it; returns the number of detected deviations (also reported
         * through the global counters when {@code report} is set).
         */
        private static int agreeOnCase(SignedInt32Corpus.Case c, CorpusConfig config,
                ParserOutcome parser, LuaCaseRun lua, JvmCaseRun jvm, boolean report) {
            int disagreements = 0;
            String name = c.name();
            if (c.expected() instanceof SignedInt32Corpus.CompileError expected) {
                // Parser-only case: the profile-aware parser must reject the
                // module with exactly the pinned E1036 at the pinned token.
                boolean ok = parser != null && !parser.parsed()
                    && parser.diagnostics().stream()
                        .anyMatch(d -> matchDiagnostic(d, expected));
                if (report) {
                    check(ok, "corpus " + name + ": the parser produces exactly the pinned "
                        + "E1036 '" + expected.message() + "' at " + expected.line() + ":"
                        + expected.column() + (parser == null ? " (no parser run)"
                            : "; got " + parser.diagnostics()));
                }
                if (!ok) {
                    disagreement(name, "parser produced no pinned E1036: "
                        + (parser == null ? "no run" : parser.diagnostics().toString()));
                    disagreements++;
                }
                return disagreements;
            }

            SignedInt32Corpus.RuntimeOutcome expected =
                (SignedInt32Corpus.RuntimeOutcome) c.expected();
            boolean okCase = expected.code() == null;

            // Parser: a runtime case must parse cleanly; for error cases the
            // pinned operation node's span must equal the pinned origin —
            // the very span both retained emitters forward to their helper
            // call sites.
            if (parser == null || !parser.parsed()) {
                if (report) {
                    check(false, "corpus " + name + ": the parser accepts the case source; got "
                        + (parser == null ? "no run" : parser.diagnostics().toString()));
                }
                disagreement(name, "parser did not accept the case source");
                disagreements++;
            } else if (expected.opKind() != SignedInt32Corpus.OpKind.NONE) {
                boolean located = parser.locatedLine() != null
                    && parser.locatedLine().equals(expected.originLine())
                    && parser.locatedColumn() != null
                    && parser.locatedColumn().equals(expected.originColumn());
                if (report) {
                    check(located, "corpus " + name + ": the pinned operation node spans "
                        + expected.originLine() + ":" + expected.originColumn() + "; got "
                        + (parser.locatedLine() == null ? "no node"
                            : parser.locatedLine() + ":" + parser.locatedColumn()));
                }
                if (!located) {
                    disagreement(name, "operation node span deviates from the pinned origin");
                    disagreements++;
                }
            }

            // Shared semantics: every pinned row must produce the pinned
            // outcome (value for ok cases; code + canonical template for
            // error cases), each failure carrying the caller-supplied origin.
            SourceOrigin origin = pinnedOrigin(c);
            for (SignedInt32Corpus.SemRow row : expected.semantics()) {
                SemRowOutcome outcome = runSemRow(row, origin, config.tamperConversionRow);
                if (okCase) {
                    boolean matched = outcome.value() != null
                        && ("v:" + outcome.value()).equals(rowExpectValue(row));
                    if (report) {
                        check(matched, "corpus " + name + ": semantics row " + row
                            + " yields " + outcome.value() + " (expected "
                            + rowExpectValue(row) + ")");
                    }
                    if (!matched) {
                        disagreement(name, "semantics row " + row + " yielded "
                            + outcome.value() + " instead of " + rowExpectValue(row));
                        disagreements++;
                    }
                } else {
                    // The shared primitive must fail with the pinned code,
                    // the pinned canonical template, and the failure origin
                    // the driver handed in — the origin comparison mirrors
                    // the LuaJIT-lane check (span line/column plus the
                    // case's source file name). All error cases pin an
                    // origin, so a primitive that fabricates or loses the
                    // caller-supplied origin fails the agreement.
                    boolean originOk = outcome.originLine() != null
                        && outcome.originLine().equals(expected.originLine())
                        && outcome.originColumn() != null
                        && outcome.originColumn().equals(expected.originColumn());
                    boolean fileOk = outcome.originFile() != null
                        && outcome.originFile()
                            .replace(java.io.File.separatorChar, '/')
                            .endsWith(name + ".deal");
                    boolean matched = expected.code().equals(outcome.failCode())
                        && expected.canonicalTemplate().equals(outcome.failTemplate())
                        && originOk && fileOk;
                    if (report) {
                        check(matched, "corpus " + name + ": semantics row " + row
                            + " fails " + outcome.failCode() + " \""
                            + outcome.failTemplate() + "\" at "
                            + outcome.originLine() + ":" + outcome.originColumn()
                            + " " + outcome.originFile() + " (expected "
                            + expected.code() + " \""
                            + expected.canonicalTemplate() + "\" at "
                            + expected.originLine() + ":" + expected.originColumn()
                            + " " + name + ".deal)");
                    }
                    if (!matched) {
                        String actual = outcome.failCode() == null
                            ? "value " + outcome.value()
                            : outcome.failCode() + " \"" + outcome.failTemplate()
                                + "\" at " + outcome.originLine() + ":"
                                + outcome.originColumn() + " "
                                + outcome.originFile();
                        disagreement(name, "semantics row " + row + " yielded " + actual
                            + " instead of " + expected.code() + " \""
                            + expected.canonicalTemplate() + "\" at "
                            + expected.originLine() + ":" + expected.originColumn()
                            + " " + name + ".deal");
                        disagreements++;
                    }
                }
            }

            // Retained LuaJIT lane (module run or the pinned gate script).
            if (expected.originLine() != null || okCase) {
                if (lua == null) {
                    if (!luajitAvailable) {
                        System.out.println("  corpus " + name
                            + ": LuaJIT lane SKIP (luajit not available)");
                    } else {
                        if (report) {
                            check(false, "corpus " + name
                                + ": the LuaJIT lane produced no run");
                        }
                        disagreement(name, "LuaJIT lane produced no run");
                        disagreements++;
                    }
                } else if (okCase) {
                    boolean matched = lua.ok();
                    if (report) {
                        check(matched, "corpus " + name + ": the LuaJIT route runs the case "
                            + "to completion (runtime-ok); got code=" + lua.code()
                            + " message=" + lua.message());
                    }
                    if (!matched) {
                        disagreement(name, "LuaJIT route failed a runtime-ok case: "
                            + lua.code() + " " + lua.message());
                        disagreements++;
                    }
                } else {
                    boolean codeOk = expected.code().equals(lua.code());
                    boolean messageOk = expected.retainedTemplate().equals(lua.message());
                    boolean originOk = expected.originLine() == null
                        || (lua.line() != null && lua.line().equals(expected.originLine())
                            && lua.column() != null
                            && lua.column().equals(expected.originColumn()));
                    boolean fileOk = expected.originLine() == null
                        || (lua.file() != null
                            && lua.file().replace(java.io.File.separatorChar, '/')
                                .endsWith(name + ".deal"));
                    boolean matched = codeOk && messageOk && originOk && fileOk;
                    if (report) {
                        check(matched, "corpus " + name + ": the LuaJIT route raises "
                            + lua.code() + " \"" + lua.message() + "\" at "
                            + lua.line() + ":" + lua.column() + " (expected "
                            + expected.code() + " \"" + expected.retainedTemplate()
                            + "\" at " + expected.originLine() + ":"
                            + expected.originColumn() + ")");
                    }
                    if (!matched) {
                        disagreement(name, "LuaJIT route deviation: got " + lua.code()
                            + " \"" + lua.message() + "\" at " + lua.line() + ":"
                            + lua.column() + "; expected " + expected.code() + " \""
                            + expected.retainedTemplate() + "\" at "
                            + expected.originLine() + ":" + expected.originColumn());
                        disagreements++;
                    }
                }
            }

            // Retained JVM lane.
            if (jvm == null) {
                if (report) {
                    check(false, "corpus " + name + ": the JVM lane produced no run");
                }
                disagreement(name, "JVM lane produced no run");
                disagreements++;
            } else if (okCase) {
                boolean matched = jvm.ok();
                if (report) {
                    check(matched, "corpus " + name + ": the JVM route runs the case to "
                        + "completion (runtime-ok); got code=" + jvm.code()
                        + " message=" + jvm.message());
                }
                if (!matched) {
                    disagreement(name, "JVM route failed a runtime-ok case: " + jvm.code()
                        + " " + jvm.message());
                    disagreements++;
                }
            } else {
                boolean matched = expected.code().equals(jvm.code())
                    && expected.retainedTemplate().equals(jvm.message());
                if (report) {
                    check(matched, "corpus " + name + ": the JVM route raises " + jvm.code()
                        + " \"" + jvm.message() + "\" (expected " + expected.code()
                        + " \"" + expected.retainedTemplate() + "\")");
                }
                if (!matched) {
                    disagreement(name, "JVM route deviation: got " + jvm.code() + " \""
                        + jvm.message() + "\"; expected " + expected.code() + " \""
                        + expected.retainedTemplate() + "\"");
                    disagreements++;
                }
            }
            return disagreements;
        }

        /** Local disagreement accounting (never the global counters). */
        private static void disagreement(String caseName, String detail) {
            System.err.println("CORPUS-DISAGREEMENT " + caseName + ": " + detail);
        }

        private static boolean matchDiagnostic(CompilerDiagnostic d,
                SignedInt32Corpus.CompileError expected) {
            return expected.code().equals(d.code())
                && expected.message().equals(d.message())
                && d.line() == expected.line()
                && d.column() == expected.column()
                && "error".equals(d.severity());
        }

        private static String rowExpectValue(SignedInt32Corpus.SemRow row) {
            return switch (row) {
                case SignedInt32Corpus.SemInt32Binary b -> b.expect();
                case SignedInt32Corpus.SemInt32Unary u -> u.expect();
                case SignedInt32Corpus.SemIntFromNumber n -> n.expect();
                case SignedInt32Corpus.SemNumberBinary b -> b.expect();
                case SignedInt32Corpus.SemNumberUnary u -> u.expect();
                case SignedInt32Corpus.SemNumberCompare cmp -> "v:" + Boolean.toString(cmp.expect());
                case SignedInt32Corpus.SemNumberPow p -> p.expect();
                case SignedInt32Corpus.SemInt32Integral i -> i.expect();
            };
        }

        // =====================================================================
        // 10.1 Four-way corpus agreement
        // =====================================================================

        static void testCorpusFourWayAgreement() throws Exception {
            System.out.println("-- SignedInt32 corpus: four-way agreement (parser / shared "
                + "semantics / retained LuaJIT / retained JVM) --");
            Path tmp = Files.createTempDirectory("deal-int32-corpus");
            try {
                AgreementReport report = verifyCorpus(new CorpusConfig(),
                    SignedInt32Corpus.CASES, true, tmp);
                check(report.casesRun() == SignedInt32Corpus.CASES.size(),
                    "every corpus case ran exactly once (" + report.casesRun() + " of "
                        + SignedInt32Corpus.CASES.size() + ")");
                check(report.disagreements() == 0,
                    "the four constituents agree on every corpus case; disagreements="
                        + report.disagreements());
            } finally {
                deleteRecursively(tmp);
            }
        }

        // =====================================================================
        // 10.2 Activated-state gate facts (A2, post-flip)
        // =====================================================================

        static void testActivatedStateGateFacts() throws Exception {
            System.out.println("-- SignedInt32 activated-state gate facts (A2, post-flip) --");
            check(activatedStateFactsHold(ReleaseState.V1_2_ACTIVE),
                "the activated-state gate facts hold (release state V1_2_ACTIVE)");
            check(!activatedStateFactsHold(ReleaseState.PRE_ACTIVATION),
                "a re-armed release constant (PRE_ACTIVATION) fails the "
                    + "activated-state verification (the flip is committed and "
                    + "irreversible)");
        }

        /**
         * Every activated-state gate fact as one predicate, evaluated end
         * to end under the asserted release state. Returns true iff all
         * hold: the public build of an int-using module under
         * {@code V1_2_ACTIVE} derives {@code DEAL_V1_2_INT32} and runs
         * the production arm (no route plan, one project emission, zero
         * retained emissions; ISSUE-0643 P4), the pre-activation matrix
         * row still derives {@code LEGACY_SAFE_INT} internally (never a
         * production rollback target), the release constant is committed
         * at {@code V1_2_ACTIVE} (a PRE_ACTIVATION probe fails), the flip
         * stays exactly the one ReleaseConfiguration constant edit plus
         * the promotion list, and no CLI/source profile selection path
         * exists.
         *
         * <p>The asserted state drives the derivation, the public-build
         * compile, and the plan checks — not only the entry guard — so
         * the {@code PRE_ACTIVATION} probe executes a genuinely re-armed
         * configuration through the real orchestrator and must fail the
         * DEAL_V1_2_INT32/SHARED gate facts. The release-constant guard
         * runs after the parameterized facts, so a re-armed probe reaches
         * and fails them instead of short-circuiting.</p>
         */
        private static boolean activatedStateFactsHold(ReleaseState assertedState)
                throws Exception {
            // State-independent provider facts: the closed public
            // derivation in both release states.
            if (CompilerProfileProvider.publicProfile(ReleaseState.PRE_ACTIVATION)
                    != SemanticProfile.LEGACY_SAFE_INT) {
                return false;
            }
            if (CompilerProfileProvider.publicProfile(ReleaseState.V1_2_ACTIVE)
                    != SemanticProfile.DEAL_V1_2_INT32) {
                return false;
            }
            CompilerInvocation active = publicBuildInvocation(ReleaseState.V1_2_ACTIVE);
            if (active.semanticProfile() != SemanticProfile.DEAL_V1_2_INT32
                    || active.releaseState() != ReleaseState.V1_2_ACTIVE) {
                return false;
            }

            // The asserted state drives the public-build invocation and
            // the real orchestrator compile end to end: the PRE_ACTIVATION
            // probe executes a genuinely re-armed configuration (a legacy
            // public build) and only then fails the DEAL_V1_2_INT32 gate
            // facts.
            CompilerInvocation publicInvocation = publicBuildInvocation(assertedState);
            // The post-flip gate fixture is an import-free single-shape
            // int-using module (the ISSUE-0239 E10 plan-time arms reroute
            // dual-shape modules — an exported function called from
            // source — and importers LEGACY while CALLS/MODULES stay
            // SHADOW; the single-shape shape keeps the SHARED pin exact).
            Path tmp = Files.createTempDirectory("deal-int32-activated");
            try {
                Path src = tmp.resolve("src");
                Files.createDirectories(src);
                Files.writeString(src.resolve("main.deal"), """
                    export function main(): null {
                      let x: int = 2147483647 + 1
                      return null
                    }
                    """);
                CompilationOrchestrator orchestrator = compile(
                    src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"),
                    Backend.LUAJIT, List.of(src.toAbsolutePath()),
                    publicInvocation, null);
                if (orchestrator == null || orchestrator.checkedProject() == null
                        || orchestrator.checkedProject().hasErrors()) {
                    return false;
                }
                // ISSUE-0643 P4: the release-owned production invocation
                // skips phase 3.7 (no route plan, one project emission,
                // zero retained emissions); the re-armed PRE_ACTIVATION
                // probe keeps the harness arm and computes one.
                RoutePlanResult plan = orchestrator.routePlan();
                boolean productionArm =
                    assertedState == ReleaseState.V1_2_ACTIVE;
                if (productionArm) {
                    if (plan != null
                            || orchestrator.semanticEmissionCount() != 1
                            || orchestrator.retainedEmissionCount() != 0) {
                        return false;
                    }
                } else if (plan == null || plan.hasErrors()
                        || plan.plan() == null) {
                    return false;
                }

                // The activated-state gate facts over the executed
                // configuration: under V1_2_ACTIVE the public build
                // derives DEAL_V1_2_INT32, runs the production arm (no
                // route plan, one project emission, zero retained
                // emissions — ISSUE-0643 P4), and keeps the promoted
                // release registry hash; the re-armed PRE_ACTIVATION run
                // fails the DEAL_V1_2_INT32 derivation facts here.
                if (CompilerProfileProvider.publicProfile(assertedState)
                        != SemanticProfile.DEAL_V1_2_INT32) {
                    return false;
                }
                if (publicInvocation.semanticProfile()
                        != SemanticProfile.DEAL_V1_2_INT32
                        || publicInvocation.releaseState() != assertedState) {
                    return false;
                }
                if (publicInvocation.capabilityRegistryHash().equals(
                        CapabilityRegistry.releaseRegistry()
                            .capabilityRegistryHash())) {
                    return false; // the promoted release registry hash, never stale
                }
                if (orchestrator.invocation().semanticProfile()
                        != SemanticProfile.DEAL_V1_2_INT32) {
                    return false;
                }
                if (!productionArm
                        && !plan.plan().entries().values().stream()
                            .allMatch(route -> route == ModuleRoute.LEGACY)) {
                    return false;
                }
            } finally {
                deleteRecursively(tmp);
            }

            // The release-constant facts: the committed constant stays
            // V1_2_ACTIVE; a re-armed probe fails here.
            if (ReleaseConfiguration.CURRENT_RELEASE_STATE != ReleaseState.V1_2_ACTIVE) {
                return false;
            }
            if (ReleaseConfiguration.CURRENT_RELEASE_STATE != assertedState) {
                return false; // only the V1_2_ACTIVE probe can hold
            }

            // The flip stays exactly the one ReleaseConfiguration
            // constant edit plus the promotion list: both former
            // hardcoded sites consume the constant and carry no
            // release-state selection literal; no CLI/source profile
            // surface; the promotion list is the committed registry half.
            String mainSource = Files.readString(Path.of("deal/Main.java"));
            String orchestratorSource =
                Files.readString(Path.of("deal/module/CompilationOrchestrator.java"));
            if (!mainSource.contains("ReleaseConfiguration.CURRENT_RELEASE_STATE")
                    || mainSource.contains("ReleaseState.PRE_ACTIVATION")
                    || mainSource.contains("--profile")) {
                return false;
            }
            if (!orchestratorSource.contains("ReleaseConfiguration.CURRENT_RELEASE_STATE")
                    || orchestratorSource.contains("ReleaseState.PRE_ACTIVATION")) {
                return false;
            }
            if (!ReleaseConfiguration.releaseCapabilityRegistry()
                    .capabilityRegistryHash().equals(
                        publicInvocation.capabilityRegistryHash())) {
                return false;
            }
            return true;
        }

        // =====================================================================
        // 10.3 Fault-injection matrix (each named constituent faulted in turn)
        // =====================================================================

        static void testFaultMatrix() throws Exception {
            System.out.println("-- SignedInt32 fault matrix: each named constituent faulted "
                + "in turn --");
            Path tmp = Files.createTempDirectory("deal-int32-faults");
            try {
                CorpusConfig parserFault = new CorpusConfig();
                parserFault.legacyParserConstructor = true;
                check(faultedRunFails("parser", parserFault,
                        List.of(caseNamed("lit_overflow")), tmp),
                    "faulted parser (the legacy parse contract — no E1036 int32 gate) "
                        + "fails the verification");

                CorpusConfig semanticsFault = new CorpusConfig();
                semanticsFault.tamperConversionRow = true;
                check(faultedRunFails("shared-semantics", semanticsFault,
                        List.of(caseNamed("conv_overflow_pos")), tmp),
                    "faulted shared semantics (a wrong int-conversion range row) fails "
                        + "the verification");

                CorpusConfig luaFault = new CorpusConfig();
                luaFault.tamperLuaInt32Flag = true;
                check(faultedRunFails("luajit-route", luaFault,
                        List.of(caseNamed("add_overflow_max"), caseNamed("mod_min_neg_one")),
                        tmp),
                    "faulted LuaJIT route (the emitted int32 gate flipped back to "
                        + "legacy) fails the verification");

                CorpusConfig jvmFault = new CorpusConfig();
                jvmFault.legacyJvmInvocation = true;
                check(faultedRunFails("jvm-route", jvmFault,
                        List.of(caseNamed("add_overflow_max"), caseNamed("num_pow_ieee")),
                        tmp),
                    "faulted JVM route (legacy helpers + raw Math.pow) fails the "
                        + "verification");

                CorpusConfig providerFault = new CorpusConfig();
                providerFault.flipProviderMatrix = true;
                check(faultedRunFails("provider-matrix", providerFault,
                        List.of(caseNamed("add_overflow_max")), tmp),
                    "faulted provider matrix (COMMON_SHADOW + LEGACY_SAFE_INT — the "
                        + "rejected combination) fails the verification");

                check(!activatedStateFactsHold(ReleaseState.PRE_ACTIVATION),
                    "faulted release configuration (a re-armed PRE_ACTIVATION release constant) fails "
                        + "the activated-state verification");

                check(catalogAuthorityProbe(tmp, true),
                    "the intact catalog resolves the fixture's declared "
                        + "production profile and the pinned production "
                        + "authority holds (E8004 'int out of safe range' — "
                        + "the fixture's re-pinned transcript)");
                check(catalogAuthorityProbe(tmp, false),
                    "faulted catalog (a wrong int-convert-range profile row "
                        + "selecting the legacy regression seam runs the "
                        + "fixture and its outcome diverges from the pinned "
                        + "production authority) fails the verification");

                CorpusConfig seamFault = new CorpusConfig();
                seamFault.legacyLuaInvocation = true;
                check(faultedRunFails("harness-seam", seamFault,
                        List.of(caseNamed("add_overflow_max"), caseNamed("mod_min_neg_one")),
                        tmp),
                    "faulted harness seam (a v1.2-positive corpus case routed through "
                        + "the legacy-regression invocation) fails the verification");
            } finally {
                deleteRecursively(tmp);
            }
        }

        private static SignedInt32Corpus.Case caseNamed(String name) {
            return SignedInt32Corpus.CASES.stream()
                .filter(c -> c.name().equals(name))
                .findFirst()
                .orElseThrow(() -> new IllegalArgumentException("unknown corpus case " + name));
        }

        /**
         * Runs the corpus verification with exactly one faulted seam and
         * returns true when the faulted run fails (at least one
         * disagreement) — the anti-hollow proof that the verification
         * detects a broken constituent.
         */
        private static boolean faultedRunFails(String constituent, CorpusConfig config,
                List<SignedInt32Corpus.Case> probeCases, Path tmp) {
            try {
                Path runDir = tmp.resolve("fault-" + constituent);
                AgreementReport report = verifyCorpus(config, probeCases, false, runDir);
                return report.disagreements() >= 1;
            } catch (Throwable e) {
                return false;
            }
        }

        /**
         * The catalog authority probe: for the catalogued backend-runtime
         * fixture {@code runtime/int-convert-range.deal} the intact harness
         * seam resolves the fixture's declared profile (the production
         * profile after the re-pin, with no {@code @profile} header) and
         * the LuaJIT lane produces the pinned production authority outcome
         * (E8004 with the production template the fixture's transcript
         * pins). The intact probe returns true iff the catalog still
         * carries the row and the observed outcome equals that pinned
         * authority.
         *
         * <p>The faulted probe ({@code rowPresent == false}) never
         * consults the catalog guard: it simulates a wrong row by
         * selecting the legacy-regression seam
         * ({@code LEGACY_REGRESSION + LEGACY_SAFE_INT}), executes the real
         * compile + LuaJIT run, and returns true iff the observed outcome
         * diverges from the pinned production authority outcome. The
         * faulted run therefore proves the anti-hollow requirement for the
         * catalog constituent: a wrong profile row makes the verification
         * fail observably (E8004 with the legacy retained template instead
         * of the pinned production template).</p>
         */
        private static boolean catalogAuthorityProbe(Path tmp, boolean rowPresent)
                throws Exception {
            String locator = "backend-runtime/runtime/int-convert-range.deal";
            Path fixture = Path.of("test", "conformance", locator);
            String source = Files.readString(fixture);
            // ISSUE-0273: the production orchestrator lexes header-free
            // sources — classification headers are stripped at this
            // materialization (the shared harness metadata seam), never
            // in production.
            String stripped = ConformanceHarnessMetadata
                .stripClassificationHeaders(source);
            CompilerInvocation invocation = rowPresent
                ? ConformanceHarnessMetadata.invocation(
                    ConformanceHarnessMetadata.profileFromMetadata(source,
                        locator))
                : ConformanceHarnessMetadata.invocation(
                    SemanticProfile.LEGACY_SAFE_INT);
            Path runDir = tmp.resolve("catalog-" + rowPresent);
            Path src = runDir.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("int_convert_range.deal"), stripped);
            CompilationOrchestrator orchestrator = compile(
                src.resolve("int_convert_range.deal").toAbsolutePath(),
                runDir.resolve("out"), Backend.LUAJIT, List.of(src.toAbsolutePath()),
                invocation, null);
            if (orchestrator == null || orchestrator.checkedProject() == null
                    || orchestrator.checkedProject().hasErrors()) {
                return false;
            }
            // The fixture's main does not call the test export: run every
            // zero-arity export (the conformance runtime-ok runner rule).
            Path outDir = runDir.resolve("out");
            Path runner = outDir.resolve("exports_runner.lua");
            Files.writeString(runner, """
                package.path = './?.lua;./std/?.lua;' .. package.path
                local ok, err = xpcall(function()
                  local m = require(arg[1])
                  for k, v in pairs(m) do
                    if type(v) == "table" and v.__kind == "function"
                        and tostring(v.sig):match("^%(%)") then
                      v.f()
                    end
                  end
                end, function(e) return e end)
                if ok then
                  print("RUNTIME_OK")
                else
                  if type(err) == "table" and err.code ~= nil then
                    print("CODE: " .. tostring(err.code))
                    print("MESSAGE: " .. tostring(err.message))
                  else
                    print("RAW: " .. tostring(err))
                  end
                end
                """);
            ProcessBuilder pb = new ProcessBuilder("luajit", "exports_runner.lua",
                "int_convert_range");
            pb.directory(outDir.toFile());
            pb.redirectErrorStream(true);
            Process p = pb.start();
            String output = new String(p.getInputStream().readAllBytes(),
                StandardCharsets.UTF_8).trim();
            p.waitFor();
            Map<String, String> fields = parseFieldOutput(output);
            // The pinned production authority outcome: E8004 with the
            // production template of the shared v1.2 int32 gate.
            boolean productionAuthority = "E8004".equals(fields.get("CODE"))
                && "int out of safe range".equals(fields.get("MESSAGE"));
            // Intact: the observed outcome must equal the pinned production
            // authority. Faulted (a wrong profile row): the legacy seam run
            // must diverge from the pinned production authority — that
            // divergence is the verification failure the fault matrix
            // asserts.
            return rowPresent ? productionAuthority : !productionAuthority;
        }
    }
}

/**
 * The fixed signed32/IEEE corpus (signed-int32 foundation I6 part 4): one
 * entry per area — literal boundaries, arithmetic, conversion, boundaries,
 * and the IEEE number operations — with per-case source text plus the
 * pinned expected outcome (result, code, per-side template, origin). For
 * E8004 cases the expected outcome records the pinned template
 * {@code int out of safe range} for the shared primitive and for the
 * retained routes alike (ISSUE-0618 retired the former two-template
 * split: the shared {@code INT32_RESULT} row now renders the retained
 * text; {@code LegacyErrorNormalization} still compares code + origin and
 * never compares raw messages across sides); the E8001 variants are
 * canonical-equivalent on all four constituents. The corpus is consumed
 * by the four drivers of {@code SignedInt32IntegrationTest}: the
 * profile-aware parser, the {@code SharedValueSemantics} unit rows, the
 * retained LuaJIT subprocess, and the retained JVM subprocess.
 */
final class SignedInt32Corpus {

    /** The pinned E8004 template of the shared primitive. */
    static final String SHARED_INT32_TEMPLATE = "int out of safe range";

    /** The pinned E8004 template of both retained routes. */
    static final String RETAINED_INT32_TEMPLATE = "int out of safe range";

    /** The E8001 infinity variant (canonical-equivalent on all four). */
    static final String E8001_INFINITY = "expected int, got infinity";

    /** The E8001 NaN variant (canonical-equivalent on all four). */
    static final String E8001_NAN = "expected int, got NaN";

    /** The E8001 fractional variant (canonical-equivalent on all four). */
    static final String E8001_FRACTIONAL = "expected int, got non-integer number";

    /** The E8005 divisor template (canonical-equivalent on all four). */
    static final String E8005_DIV_ZERO = "integer division by zero";

    /** The E8006 exponent template (canonical-equivalent on all four). */
    static final String E8006_NEG_EXP = "integer exponent must be non-negative";

    sealed interface Expected permits CompileError, RuntimeOutcome {}

    /** Parser-only outcome: the pinned E1036 at the offending token. */
    record CompileError(String code, String message, int line, int column)
        implements Expected {}

    /**
     * The four-constituent runtime outcome. {@code code == null} means
     * runtime-ok (every in-module assertion holds); otherwise the pinned
     * DEAL code with the canonical template (shared primitive) and the
     * retained template (both retained routes). The pinned origin is the
     * operation's AST span start, which the LuaJIT runtime error must
     * reproduce exactly; the one gate-script case pins the explicit
     * checker origin instead.
     */
    record RuntimeOutcome(String code, String canonicalTemplate, String retainedTemplate,
                          Integer originLine, Integer originColumn, OpKind opKind,
                          List<SemRow> semantics) implements Expected {
        RuntimeOutcome {
            semantics = List.copyOf(semantics);
        }

        static RuntimeOutcome ok(List<SemRow> semantics) {
            return new RuntimeOutcome(null, null, null, null, null, OpKind.NONE, semantics);
        }

        static RuntimeOutcome error(String code, String canonicalTemplate,
                String retainedTemplate, int originLine, int originColumn,
                OpKind opKind, List<SemRow> semantics) {
            return new RuntimeOutcome(code, canonicalTemplate, retainedTemplate,
                originLine, originColumn, opKind, semantics);
        }
    }

    /**
     * The operation node kind the parser driver locates for the origin pin;
     * {@code DECL_TYPE} is the declared-type span the emitters forward for
     * the descriptor-tail boundary.
     */
    enum OpKind { BINARY, UNARY, CALL, MEMBER, DECL_TYPE, NONE }

    /** One shared-semantics operation row mirroring the case's DEAL source. */
    sealed interface SemRow permits SemInt32Binary, SemInt32Unary, SemIntFromNumber,
        SemNumberBinary, SemNumberUnary, SemNumberCompare, SemNumberPow, SemInt32Integral {}

    record SemInt32Binary(String op, int a, int b, String expect) implements SemRow {}
    record SemInt32Unary(String op, int a, String expect) implements SemRow {}
    record SemIntFromNumber(double value, String expect) implements SemRow {}
    record SemNumberBinary(String op, double a, double b, String expect) implements SemRow {}
    record SemNumberUnary(String op, double a, String expect) implements SemRow {}
    record SemNumberCompare(String op, double a, double b, boolean expect) implements SemRow {}
    record SemNumberPow(double a, double b, String expect) implements SemRow {}
    record SemInt32Integral(long value, String expect) implements SemRow {}

    /** The JVM lane's declared host fixture for the host-int-return case. */
    record HostDef(String importPath, String declarationPath, String declarationSource,
                   String javaSource) {}

    /**
     * One fixed corpus case. {@code host} carries the JVM lane's declared
     * host fixture; {@code luaGateScript} carries the pinned LuaJIT
     * gate-check script (the host-boundary replacement of the retained
     * LuaJIT route).
     */
    record Case(String name, String source, Expected expected, HostDef host,
                String luaGateScript) {
        Case {
            source = source.stripTrailing() + "\n";
        }

        static Case compileError(String name, String source, String message,
                int line, int column) {
            return new Case(name, source,
                new CompileError("E1036", message, line, column), null, null);
        }

        static Case runtime(String name, String source, Expected expected) {
            return new Case(name, source, expected, null, null);
        }

        static Case runtimeHost(String name, String source, Expected expected,
                HostDef host, String luaGateScript) {
            return new Case(name, source, expected, host, luaGateScript);
        }
    }

    // =========================================================================
    // Semantics row factories
    // =========================================================================

    private static SemInt32Binary ib(String op, int a, int b, String expect) {
        return new SemInt32Binary(op, a, b, expect);
    }

    private static SemInt32Unary iu(String op, int a, String expect) {
        return new SemInt32Unary(op, a, expect);
    }

    private static SemIntFromNumber in(double value, String expect) {
        return new SemIntFromNumber(value, expect);
    }

    private static SemNumberBinary nb(String op, double a, double b, String expect) {
        return new SemNumberBinary(op, a, b, expect);
    }

    private static SemNumberUnary nu(String op, double a, String expect) {
        return new SemNumberUnary(op, a, expect);
    }

    private static SemNumberCompare nc(String op, double a, double b, boolean expect) {
        return new SemNumberCompare(op, a, b, expect);
    }

    private static SemNumberPow np(double a, double b, String expect) {
        return new SemNumberPow(a, b, expect);
    }

    private static SemInt32Integral ii(long value, String expect) {
        return new SemInt32Integral(value, expect);
    }

    // =========================================================================
    // Module templates (uniform layout: test first, main invokes test)
    // =========================================================================

    private static String moduleReturn(String expression) {
        return """
            export function test(): int {
              return %s
            }

            export function main(): null {
              test()
              return null
            }
            """.formatted(expression);
    }

    private static String moduleAsserts(String... asserts) {
        StringBuilder body = new StringBuilder();
        for (String assertion : asserts) {
            body.append(assertion).append('\n');
        }
        return """
            export function test(): int {
            %s  return 0
            }

            export function main(): null {
              test()
              return null
            }
            """.formatted(body);
    }

    private static String assertFail(String label, String expression, String message) {
        return "  if (" + expression + ") { throw { code: \"TEST_FAIL\", message: \""
            + label + ": " + message + "\" }; }";
    }

    // =========================================================================
    // The closed corpus
    // =========================================================================

    static final List<Case> CASES = List.of(
        // ---- Literal boundaries (I1 + runtime agreement) ----
        Case.runtime("lit_max", moduleReturn("2147483647"),
            RuntimeOutcome.ok(List.of(ii(2147483647L, "v:2147483647")))),
        Case.runtime("lit_min_immediate", moduleReturn("-2147483648"),
            RuntimeOutcome.ok(List.of(ii(-2147483648L, "v:-2147483648")))),
        Case.runtime("lit_double_neg_min", moduleReturn("--2147483648"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.UNARY,
                List.of(iu("neg", -2147483648, "E8004")))),
        Case.compileError("lit_overflow", moduleReturn("2147483648"),
            "Integer literal out of range: 2147483648", 2, 10),
        Case.compileError("lit_parenthesized_min", moduleReturn("-(2147483648)"),
            "Integer literal out of range: 2147483648", 2, 12),
        Case.compileError("lit_neg_overflow", moduleReturn("-2147483649"),
            "Integer literal out of range: 2147483649", 2, 11),

        // ---- Arithmetic: add/sub/mul/neg overflow, both signs ----
        Case.runtime("add_overflow_max", moduleReturn("2147483647 + 1"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("add", 2147483647, 1, "E8004")))),
        Case.runtime("add_overflow_min", moduleReturn("-2147483648 + -1"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("add", -2147483648, -1, "E8004")))),
        Case.runtime("sub_overflow_min", moduleReturn("-2147483648 - 1"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("sub", -2147483648, 1, "E8004")))),
        Case.runtime("sub_overflow_max", moduleReturn("2147483647 - -1"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("sub", 2147483647, -1, "E8004")))),
        Case.runtime("mul_overflow_max", moduleReturn("2147483647 * 2"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("mul", 2147483647, 2, "E8004")))),
        Case.runtime("mul_overflow_min", moduleReturn("-2147483648 * 2"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("mul", -2147483648, 2, "E8004")))),
        Case.runtime("neg_min", moduleReturn("-(-2147483648)"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.UNARY,
                List.of(iu("neg", -2147483648, "E8004")))),

        // ---- Arithmetic: truncating division/remainder, MIN edge ----
        Case.runtime("div_trunc", moduleAsserts(
                assertFail("div_trunc", "5 / -2 !== -2", "5 / -2 must truncate to -2"),
                assertFail("div_trunc", "-5 / 2 !== -2", "-5 / 2 must truncate to -2")),
            RuntimeOutcome.ok(List.of(ib("div", 5, -2, "v:-2"),
                ib("div", -5, 2, "v:-2")))),
        Case.runtime("div_min_neg_one", moduleReturn("-2147483648 / -1"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("div", -2147483648, -1, "E8004")))),
        Case.runtime("mod_min_neg_one", moduleAsserts(
                assertFail("mod_min_neg_one", "-2147483648 % -1 !== 0",
                    "MIN % -1 must be 0")),
            RuntimeOutcome.ok(List.of(ib("mod", -2147483648, -1, "v:0")))),
        Case.runtime("mod_trunc_signs", moduleAsserts(
                assertFail("mod_trunc_signs", "5 % -2 !== 1", "5 % -2 must be 1"),
                assertFail("mod_trunc_signs", "-5 % 2 !== -1", "-5 % 2 must be -1"),
                assertFail("mod_trunc_signs", "-5 % -2 !== -1", "-5 % -2 must be -1")),
            RuntimeOutcome.ok(List.of(ib("mod", 5, -2, "v:1"),
                ib("mod", -5, 2, "v:-1"), ib("mod", -5, -2, "v:-1")))),

        // ---- Arithmetic: divisor / exponent failures ----
        Case.runtime("div_zero", moduleReturn("1 / 0"),
            RuntimeOutcome.error("E8005", E8005_DIV_ZERO, E8005_DIV_ZERO,
                2, 10, OpKind.BINARY, List.of(ib("div", 1, 0, "E8005")))),
        Case.runtime("mod_zero", moduleReturn("1 % 0"),
            RuntimeOutcome.error("E8005", E8005_DIV_ZERO, E8005_DIV_ZERO,
                2, 10, OpKind.BINARY, List.of(ib("mod", 1, 0, "E8005")))),
        Case.runtime("pow_neg_exponent", moduleReturn("2 ** -1"),
            RuntimeOutcome.error("E8006", E8006_NEG_EXP, E8006_NEG_EXP,
                2, 10, OpKind.BINARY, List.of(ib("pow", 2, -1, "E8006")))),

        // ---- Arithmetic: the pow band (finite 2 ** 62, infinity 2 ** 1024) ----
        Case.runtime("pow_finite_band", moduleReturn("2 ** 62"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.BINARY,
                List.of(ib("pow", 2, 62, "E8004")))),
        Case.runtime("pow_infinity_band", moduleReturn("2 ** 1024"),
            RuntimeOutcome.error("E8001", E8001_INFINITY, E8001_INFINITY,
                2, 10, OpKind.BINARY, List.of(ib("pow", 2, 1024, "E8001")))),
        Case.runtime("pow_in_range", moduleAsserts(
                assertFail("pow_in_range", "0 ** 0 !== 1", "0 ** 0 must be 1"),
                assertFail("pow_in_range", "(-2) ** 31 !== -2147483648",
                    "(-2) ** 31 must be -2147483648"),
                assertFail("pow_in_range", "2 ** 30 !== 1073741824",
                    "2 ** 30 must be 1073741824")),
            RuntimeOutcome.ok(List.of(ib("pow", 0, 0, "v:1"),
                ib("pow", -2, 31, "v:-2147483648"),
                ib("pow", 2, 30, "v:1073741824")))),

        // ---- Conversion: NaN / infinity / fractional / boundaries / 2^31 ----
        Case.runtime("conv_nan", moduleReturn("int(0.0 / 0.0)"),
            RuntimeOutcome.error("E8001", E8001_NAN, E8001_NAN,
                2, 10, OpKind.CALL, List.of(in(Double.NaN, "E8001")))),
        Case.runtime("conv_infinity", moduleReturn("int(1.0 / 0.0)"),
            RuntimeOutcome.error("E8001", E8001_INFINITY, E8001_INFINITY,
                2, 10, OpKind.CALL,
                List.of(in(Double.POSITIVE_INFINITY, "E8001")))),
        Case.runtime("conv_fractional", moduleReturn("int(1.5)"),
            RuntimeOutcome.error("E8001", E8001_FRACTIONAL, E8001_FRACTIONAL,
                2, 10, OpKind.CALL, List.of(in(1.5, "E8001")))),
        Case.runtime("conv_boundaries", moduleAsserts(
                assertFail("conv_boundaries", "int(2147483647.0) !== 2147483647",
                    "int(2147483647.0) must be 2147483647"),
                assertFail("conv_boundaries", "int(-2147483648.0) !== -2147483648",
                    "int(-2147483648.0) must be -2147483648"),
                assertFail("conv_boundaries",
                    "1.0 / number(int(-0.0)) !== 1.0 / 0.0",
                    "int(-0.0) must normalize to +0 (the reciprocal pins the sign)")),
            RuntimeOutcome.ok(List.of(in(2147483647.0, "v:2147483647"),
                in(-2147483648.0, "v:-2147483648"), in(-0.0, "v:0")))),
        Case.runtime("conv_overflow_pos", moduleReturn("int(2147483648.0)"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.CALL,
                List.of(in(2147483648.0, "E8004")))),
        Case.runtime("conv_overflow_neg", moduleReturn("int(-2147483649.0)"),
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 10, OpKind.CALL,
                List.of(in(-2147483649.0, "E8004")))),

        // ---- Boundaries: array element, class int field, table read ----
        Case.runtime("boundary_array_element", """
                export function test(): int {
                  let xs: int[] = [2147483647 + 1];
                  return 0;
                }

                export function main(): null {
                  test()
                  return null
                }
                """,
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 2, 20, OpKind.BINARY,
                List.of(ib("add", 2147483647, 1, "E8004")))),
        Case.runtime("boundary_class_field", """
                class Box { f: int = 0; }

                export function test(): int {
                  let b: Box = {};
                  b.f = 2147483647 + 1;
                  return b.f;
                }

                export function main(): null {
                  test()
                  return null
                }
                """,
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 5, 9, OpKind.BINARY,
                List.of(ib("add", 2147483647, 1, "E8004")))),
        Case.runtime("boundary_table_read", """
                export function test(): int {
                  let t: table = { v: 2147483648.0 };
                  let n: int | null = t.v;
                  if (n === null) { return 1; }
                  return 0;
                }

                export function main(): null {
                  test()
                  return null
                }
                """,
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 3, 10, OpKind.DECL_TYPE,
                List.of(ii(2147483648L, "E8004")))),

        // ---- Boundary: declared host int return (JVM lane with the real
        // declared host fixture; the LuaJIT lane runs the pinned gate check
        // — the host-boundary replacement) ----
        Case.runtimeHost("boundary_host_int_return", """
                import * as log from "host/log"

                export function test(): int {
                  return log.value()
                }

                export function main(): null {
                  test()
                  return null
                }
                """,
            RuntimeOutcome.error("E8004", SHARED_INT32_TEMPLATE,
                RETAINED_INT32_TEMPLATE, 4, 10, OpKind.CALL,
                List.of(ii(2147483648L, "E8004"))),
            new HostDef("host/log", "bindings/log.d.deal",
                "export function value(): int;\n",
                "public final class HostLog {\n"
                    + "    public static Object value() { return Long.valueOf(2147483648L); }\n"
                    + "}\n"),
            """
                package.path = './?.lua;' .. package.path
                local __rt = require("deal.runtime")
                __rt.__INT32 = true
                local ok, err = pcall(function()
                  return __rt.check_int(2147483648,
                    "boundary_host_int_return.deal", 4, 10)
                end)
                if ok then
                  print("GATE_OK")
                else
                  print("CODE: " .. tostring(err.code))
                  print("MESSAGE: " .. tostring(err.message))
                  print("FILE: " .. tostring(err.file))
                  print("LINE: " .. tostring(err.line))
                  print("COLUMN: " .. tostring(err.column))
                end
                """),

        // ---- IEEE number operations: NaN equality/relational ----
        Case.runtime("num_nan_eq_rel", moduleAsserts(
                assertFail("num_nan_eq_rel", "0.0 / 0.0 === 0.0 / 0.0",
                    "NaN must not equal NaN"),
                assertFail("num_nan_eq_rel", "!(0.0 / 0.0 !== 1.0)",
                    "NaN !== 1.0 must be true"),
                assertFail("num_nan_eq_rel", "0.0 / 0.0 < 1.0",
                    "NaN < 1.0 must be false"),
                assertFail("num_nan_eq_rel", "0.0 / 0.0 <= 1.0",
                    "NaN <= 1.0 must be false"),
                assertFail("num_nan_eq_rel", "0.0 / 0.0 > 1.0",
                    "NaN > 1.0 must be false"),
                assertFail("num_nan_eq_rel", "0.0 / 0.0 >= 1.0",
                    "NaN >= 1.0 must be false")),
            RuntimeOutcome.ok(List.of(
                nc("eq", Double.NaN, Double.NaN, false),
                nc("ne", Double.NaN, Double.NaN, true),
                nc("lt", Double.NaN, 1.0, false),
                nc("le", Double.NaN, 1.0, false),
                nc("gt", Double.NaN, 1.0, false),
                nc("ge", Double.NaN, 1.0, false)))),

        // ---- IEEE number operations: ±0 and division by zero ----
        Case.runtime("num_zeros", moduleAsserts(
                assertFail("num_zeros", "-0.0 !== 0.0", "-0.0 must equal 0.0"),
                assertFail("num_zeros", "0.0 !== -0.0", "0.0 must equal -0.0"),
                assertFail("num_zeros", "!(1.0 / -0.0 < 0.0)",
                    "1.0 / -0.0 must be -Infinity"),
                assertFail("num_zeros",
                    "1.0 / (-(-0.0)) !== 1.0 / 0.0",
                    "-(-0.0) must be +0.0 (the reciprocal pins the sign)")),
            RuntimeOutcome.ok(List.of(
                nc("eq", -0.0, 0.0, true),
                nb("div", 1.0, -0.0, "v:-Infinity"),
                nu("neg", -0.0, "v:0.0")))),
        Case.runtime("num_div_zero", moduleAsserts(
                assertFail("num_div_zero", "!(1.0 / 0.0 > 0.0)",
                    "1.0 / 0.0 must be +Infinity"),
                assertFail("num_div_zero", "!(-1.0 / 0.0 < 0.0)",
                    "-1.0 / 0.0 must be -Infinity"),
                assertFail("num_div_zero", "0.0 / 0.0 === 0.0 / 0.0",
                    "0.0 / 0.0 must be NaN")),
            RuntimeOutcome.ok(List.of(
                nb("div", 1.0, 0.0, "v:Infinity"),
                nb("div", -1.0, 0.0, "v:-Infinity"),
                nb("div", 0.0, 0.0, "v:NaN")))),

        // ---- IEEE number operations: floor modulo ----
        Case.runtime("num_mod_floor", moduleAsserts(
                assertFail("num_mod_floor", "5.0 % -2.0 !== -1.0",
                    "5.0 % -2.0 must be -1.0"),
                assertFail("num_mod_floor", "-5.0 % 2.0 !== 1.0",
                    "-5.0 % 2.0 must be 1.0"),
                assertFail("num_mod_floor", "-5.0 % -2.0 !== -1.0",
                    "-5.0 % -2.0 must be -1.0")),
            RuntimeOutcome.ok(List.of(
                nb("mod", 5.0, -2.0, "v:-1.0"),
                nb("mod", -5.0, 2.0, "v:1.0"),
                nb("mod", -5.0, -2.0, "v:-1.0")))),

        // ---- IEEE number operations: the pinned numberPow special-case table ----
        Case.runtime("num_pow_ieee", moduleAsserts(
                assertFail("num_pow_ieee", "2.0 ** 10.0 !== 1024.0",
                    "2.0 ** 10.0 must be 1024.0"),
                assertFail("num_pow_ieee", "(-2.0) ** 3.0 !== -8.0",
                    "(-2.0) ** 3.0 must be -8.0"),
                assertFail("num_pow_ieee", "0.0 ** 0.0 !== 1.0",
                    "0.0 ** 0.0 must be 1.0"),
                assertFail("num_pow_ieee", "2.0 ** -0.0 !== 1.0",
                    "pow(finite, -0.0) must be 1.0"),
                assertFail("num_pow_ieee", "0.0 ** -1.0 !== (1.0 / 0.0)",
                    "0.0 ** -1.0 must be +Infinity"),
                assertFail("num_pow_ieee", "0.0 ** 3.0 !== 0.0",
                    "0.0 ** 3.0 must be +0.0"),
                assertFail("num_pow_ieee", "!(1.0 / (0.0 ** 3.0) > 0.0)",
                    "0.0 ** 3.0 must be +0.0 (the reciprocal pins the sign)"),
                assertFail("num_pow_ieee", "(-2.0) ** 0.5 === (-2.0) ** 0.5",
                    "negative-base fractional pow must be NaN"),
                assertFail("num_pow_ieee", "1.0 ** (0.0 / 0.0) !== 1.0",
                    "1.0 ** NaN must be 1.0"),
                assertFail("num_pow_ieee",
                    "2.0 ** (0.0 / 0.0) === 2.0 ** (0.0 / 0.0)",
                    "pow(x != 1, NaN) must be NaN (self-unequal)"),
                assertFail("num_pow_ieee", "(0.0 / 0.0) ** 0.0 !== 1.0",
                    "NaN ** 0.0 must be 1.0"),
                assertFail("num_pow_ieee", "(-1.0) ** (1.0 / 0.0) !== 1.0",
                    "(-1.0) ** Infinity must be 1.0"),
                assertFail("num_pow_ieee", "1.0 ** (1.0 / 0.0) !== 1.0",
                    "1.0 ** Infinity must be 1.0"),
                assertFail("num_pow_ieee", "1.0 ** (-1.0 / 0.0) !== 1.0",
                    "1.0 ** -Infinity must be 1.0"),
                assertFail("num_pow_ieee", "(-1.0) ** (-1.0 / 0.0) !== 1.0",
                    "(-1.0) ** -Infinity must be 1.0"),
                assertFail("num_pow_ieee", "2.0 ** 1024.0 !== (1.0 / 0.0)",
                    "2.0 ** 1024.0 must overflow to +Infinity"),
                assertFail("num_pow_ieee", "(-2.0) ** 1025.0 !== (-1.0 / 0.0)",
                    "(-2.0) ** 1025.0 must overflow to -Infinity (negative base, "
                        + "odd exponent)"),
                assertFail("num_pow_ieee", "2.0 ** -1075.0 !== 0.0",
                    "2.0 ** -1075.0 must underflow to +0"),
                assertFail("num_pow_ieee", "(-2.0) ** -1075.0 !== 0.0",
                    "(-2.0) ** -1075.0 must underflow to 0"),
                assertFail("num_pow_ieee", "!(1.0 / ((-2.0) ** -1075.0) < 0.0)",
                    "(-2.0) ** -1075.0 must be -0.0 (the reciprocal pins the sign)"),
                assertFail("num_pow_ieee", "(-0.0) ** -2.0 !== (1.0 / 0.0)",
                    "(-0.0) ** -2.0 must be +Infinity (even exponent)"),
                assertFail("num_pow_ieee", "!((-0.0) ** -3.0 < 0.0)",
                    "(-0.0) ** -3.0 must be -Infinity (negative odd exponent)"),
                assertFail("num_pow_ieee", "!(1.0 / ((-0.0) ** 3.0) < 0.0)",
                    "(-0.0) ** 3.0 must be -0.0 (sign preserved; the reciprocal "
                        + "pins the sign)"),
                assertFail("num_pow_ieee", "(1.0 / 0.0) ** 2.0 !== (1.0 / 0.0)",
                    "+Infinity ** 2.0 must be +Infinity"),
                assertFail("num_pow_ieee", "(1.0 / 0.0) ** -2.0 !== 0.0",
                    "+Infinity ** -2.0 must be +0.0"),
                assertFail("num_pow_ieee", "!(1.0 / ((1.0 / 0.0) ** -2.0) > 0.0)",
                    "+Infinity ** -2.0 must be +0.0 (the reciprocal pins the sign)"),
                assertFail("num_pow_ieee", "(-1.0 / 0.0) ** 2.0 !== (1.0 / 0.0)",
                    "(-Infinity) ** 2.0 must be +Infinity (even exponent)"),
                assertFail("num_pow_ieee", "!((-1.0 / 0.0) ** 3.0 < 0.0)",
                    "(-Infinity) ** 3.0 must be -Infinity (odd exponent)"),
                assertFail("num_pow_ieee", "(-1.0 / 0.0) ** -2.0 !== 0.0",
                    "-Infinity ** -2.0 must be +0.0 (even exponent)"),
                assertFail("num_pow_ieee", "!(1.0 / ((-1.0 / 0.0) ** -2.0) > 0.0)",
                    "-Infinity ** -2.0 must be +0.0 (the reciprocal pins the sign)"),
                assertFail("num_pow_ieee", "(-1.0 / 0.0) ** -3.0 !== 0.0",
                    "-Infinity ** -3.0 must be 0"),
                assertFail("num_pow_ieee", "!(1.0 / ((-1.0 / 0.0) ** -3.0) < 0.0)",
                    "-Infinity ** -3.0 must be -0.0 (odd exponent; the reciprocal "
                        + "pins the sign)")),
            RuntimeOutcome.ok(List.of(
                np(2.0, 10.0, "v:1024.0"),
                np(-2.0, 3.0, "v:-8.0"),
                np(0.0, 0.0, "v:1.0"),
                np(2.0, -0.0, "v:1.0"),
                np(0.0, -1.0, "v:Infinity"),
                np(0.0, 3.0, "v:0.0"),
                np(-2.0, 0.5, "v:NaN"),
                np(1.0, Double.NaN, "v:1.0"),
                np(2.0, Double.NaN, "v:NaN"),
                np(Double.NaN, 0.0, "v:1.0"),
                np(-1.0, Double.POSITIVE_INFINITY, "v:1.0"),
                np(1.0, Double.POSITIVE_INFINITY, "v:1.0"),
                np(1.0, Double.NEGATIVE_INFINITY, "v:1.0"),
                np(-1.0, Double.NEGATIVE_INFINITY, "v:1.0"),
                np(2.0, 1024.0, "v:Infinity"),
                np(-2.0, 1025.0, "v:-Infinity"),
                np(2.0, -1075.0, "v:0.0"),
                np(-2.0, -1075.0, "v:-0.0"),
                np(-0.0, -2.0, "v:Infinity"),
                np(-0.0, -3.0, "v:-Infinity"),
                np(-0.0, 3.0, "v:-0.0"),
                np(Double.POSITIVE_INFINITY, 2.0, "v:Infinity"),
                np(Double.POSITIVE_INFINITY, -2.0, "v:0.0"),
                np(Double.NEGATIVE_INFINITY, 2.0, "v:Infinity"),
                np(Double.NEGATIVE_INFINITY, 3.0, "v:-Infinity"),
                np(Double.NEGATIVE_INFINITY, -2.0, "v:0.0"),
                np(Double.NEGATIVE_INFINITY, -3.0, "v:-0.0"))))
    );

    private SignedInt32Corpus() {
        // Fixed test data only; no instances.
    }
}
